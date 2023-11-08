#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lif.rkt")
(require "priority_queue.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;; uniquify : R1 -> R1

(define (shrink-helper e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body) 
     (define mod_e (shrink-helper e))
     (define mod_body (shrink-helper body))
     (Let x mod_e mod_body)]
    [(Prim 'or es) (define e1 (car es)) (define e2 (car (cdr es))) (If (shrink-helper e1) (Bool #t) (shrink-helper e2))]
    [(Prim 'and es) (define e1 (car es)) (define e2 (car (cdr es))) (If (shrink-helper e1) (shrink-helper e2) (Bool #f))]
    [(Prim op es) (Prim op (for/list ([e es]) (shrink-helper e)))]
    [(If cnd thn els) (If (shrink-helper cnd) (shrink-helper thn) (shrink-helper els))]
    [else (error "Some error in shrink" e)]
  ))


(define (shrink p)
  (match p
  [(Program info e)
    (Program info (shrink-helper e))]))
;; 

;; uniquify : R1 -> R1

(define (uniquify_exp env)
  (lambda (e)
    (match e
    [(Var x) (Var (dict-ref env x))]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body) 
     (define mod_e ((uniquify_exp env) e))
     (define mod_env (dict-set env x (gensym x)))
     (define mod_x (dict-ref mod_env x))
     (define mod_body ((uniquify_exp mod_env) body))
     (Let mod_x mod_e mod_body)]
    [(Prim op es)
    (Prim op (for/list ([e es]) ((uniquify_exp env) e)))]
    [(If cnd thn els) (If ((uniquify_exp env) cnd) ((uniquify_exp env) thn) ((uniquify_exp env) els))]
    [else (error "Some Error in uniquify-exp" e)]
    )))

(define (uniquify p)
  (match p
    [(Program info body) (Program info ((uniquify_exp '()) body))]))

(define (rco-atm atm) ;; returns dict, atomic-expression
  (match atm
  [(Int a) (values '() atm)]
  [(Var a) (values '() atm)]
  [(Bool a) (values '() atm)]
  [(Prim 'read '()) 
    (define t1 (gensym 'x)) 
    (define mod_env (dict-set '() t1 (rco-exp (Prim 'read '()))))
    (values mod_env (Var t1))
  ]
  [(Prim op es) 
    (define t1 (gensym 'x))
    (define-values (sss mod_es) (for/lists (l1 l2) ([e es]) (rco-atm e)))
    (values (dict-set (append* sss) t1 (Prim op mod_es)) (Var t1)) 
    ;; the above line takes an already set dictionary (sss with all previous stuff set) and adds t1->(Prim op es) to it
  ] ;; sub each es with var 
  [(If cnd thn els) 
    (define t1 (gensym 'x))
    (define new-es (for/list ([e (list cnd thn els)]) (rco-exp e)))
    (match new-es
      [(list e1 e2 e3) (values (dict-set '() t1 (If e1 e2 e3)) (Var t1))]
      )]
  [(Let x e body) 
    (define mod_e (rco-exp e))
    (define-values (bodyenv bodyvar) (rco-atm body))
    (define modenv (append bodyenv (dict-set '() x mod_e)))
    (values modenv bodyvar)]
  [_ (error "Unhandled case in rco-atm")]
))

(define (make-let-expression env propes)
  (match env
      ['() propes]
      [_ 
        (define repKey (dict-iterate-key env (dict-iterate-first env)))
        (define repVal (dict-iterate-value env (dict-iterate-first env)))
        (define modenv (dict-remove env repKey))
        (Let repKey repVal (make-let-expression modenv propes))
      ]
    )
  )

(define (rco-exp exp)
(match exp
  [(Int a) (Int a)];;(define-values (a1 b1) (rco-atm exp)) (b1)]
  [(Var a) (Var a)];;(define-values (a1 b1) (rco-atm exp)) (b1)]
  [(Bool a) (Bool a)]
  [(Prim 'read '()) (Prim 'read '())]
  [(Let x e body) 
    (Let x (rco-exp e) (rco-exp body))
  ]
  [(If cnd thn els) (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
  [(Prim op es) 
    (define-values (modenv modes) (for/lists (l1 l2) ([e es]) (rco-atm e)))
    (make-let-expression (append* modenv) (Prim op modes))
  ]
  [_ (error "Unhandled case in rco-exp")]
))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]
    [_ (error "Error: remove-complex-opera* mein")]
  ))


;; explicate-control : R1 -> C0
(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) 
      (define mod_body (explicate_tail body)) 
      (explicate_assign rhs x mod_body)]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [(Var k) (Seq (Assign (Var x) (Var k)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) 
      (define mod_cont (explicate_assign body x cont))        ;Adding from bottom
      (explicate_assign rhs y mod_cont)] 
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (dict-set '() 'start (explicate_tail body)))]))

;;select instructions
(define (select_instructions_atm e)
  (match e
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
  ))
(define (select_instructions_stmt var_exp e)
  (match e
    [(Int n) (list (Instr 'movq (list (Imm n) var_exp)))]
    [(Var x) (list (Instr 'movq (list (Var x) var_exp)))]
    [(Prim 'read '()) (append (list (Callq 'read_int 0)) (list (Instr 'movq (list (Reg 'rax) var_exp))))]
    [(Prim '- (list exp)) (append (list (Instr 'movq (list (select_instructions_atm exp) var_exp)))
                                  (list (Instr 'negq (list var_exp))))]
    [(Prim '+ (list exp1 exp2)) (append (list (Instr 'movq (list (select_instructions_atm exp1) var_exp)))
                                    (list (Instr 'addq (list (select_instructions_atm exp2) var_exp))))]
    [(Prim '- (list exp1 exp2)) (append (list (Instr 'movq (list (select_instructions_atm exp1) var_exp)))
                                    (list (Instr 'subq (list (select_instructions_atm exp2) var_exp))))]
                                  
  ))

(define (select_instructions_assign e)
  (match e
    [(Assign var_exp exp) (select_instructions_stmt var_exp exp)]))

(define (select_instructions_tail e)
  (match e
    [(Return exp) (append (select_instructions_assign (Assign (Reg 'rax) exp)) (list (Jmp 'conclusion)))]
    [(Seq stmt tail) (append (select_instructions_assign stmt) (select_instructions_tail tail))]
    [else (error "select_instructions_tail unhandled case" e)]))

(define (select_instructions p)
  (match p
    [(CProgram info body) (X86Program info (dict-set '() 'start (Block '() (select_instructions_tail (dict-ref body 'start)))))]
  ))

;; assign homes

(define (assign-stack-locations variables)
  (define (create-stack-locations temp_vars offset ret)
    (cond
      [(equal? '() temp_vars) ret]
      [else (create-stack-locations (cdr temp_vars) (+ offset -8) (dict-set ret (car (car temp_vars)) (Deref 'rbp offset)))]
    )
  )
  (create-stack-locations variables -8 '())
  )

(define (assign-homes-stack variables instructions)
  (define (set-memory-location e)
    (match e
      [(Var x) (dict-ref variables x)]
      [else e]
    ))
  (define (modify-instructions instr ret)
    (cond
      [(equal? '() instr) ret]
      [else (match (car instr)
        [(Instr op (list arg1)) (modify-instructions (cdr instr) (append ret (list (Instr op (list (set-memory-location arg1))))))]
        [(Instr op (list arg1 arg2)) (modify-instructions (cdr instr) (append ret (list (Instr op (list (set-memory-location arg1) (set-memory-location arg2))))))]
        [else (modify-instructions (cdr instr) (append ret (list (car instr))))]
      )]
    )
  )
  (modify-instructions instructions '())
)

(define (get-stack-space variables)
  (define (find-stack-space temp_vars ret)
    (cond
      [(equal? '() temp_vars) ret]
      [else (find-stack-space (cdr temp_vars) (+ ret 8) )]
    )
  )
  (* (ceiling (/ (find-stack-space variables 0) 16)) 16)
  )

(define (assign-homes p)
  (match p
    [(X86Program info body) (define start-block-ele (dict-ref body 'start)) 
                            (define memory-map (assign-stack-locations (dict-ref info 'locals-types)))
                            (X86Program (dict-set info 'stack-space (get-stack-space (dict-ref info 'locals-types))) (dict-set '() 'start (Block '() (assign-homes-stack memory-map (Block-instr* start-block-ele)))))]
  ))

;; patch instructions

(define (patch_with_rax instructions)
  (define (include_rax instr ret)
    (cond
      [(equal? '() instr) ret]
      [else (match (car instr)
              [(Instr op (list exp1 exp2)) (if (and (Deref? exp1) (Deref? exp2))
                                              (include_rax (cdr instr) (append ret (list (Instr 'movq (list exp1 (Reg 'rax))) (Instr op (list (Reg 'rax) exp2)))))
                                              (include_rax (cdr instr) (append ret (list (car instr)))))]
              [else (include_rax (cdr instr) (append ret (list (car instr))))]
      )]
    ))
  (include_rax instructions '())
  )

(define (patch_trivial instructions)
  (define (delete_trivial instr ret)
    (cond
      [(equal? '() instr) ret]
      [else (match (car instr)
              [(Instr op (list exp1 exp2)) (if (equal? exp1 exp2)
                                              (delete_trivial (cdr instr) ret)
                                              (delete_trivial (cdr instr) (append ret (list (car instr)))))]
              [else (delete_trivial (cdr instr) (append ret (list (car instr))))]
      )]
    ))
  (delete_trivial instructions '())
  )

(define (patch_instructions p)
  (match p
    [(X86Program info body) (define start-block-ele (dict-ref body 'start)) 
                            (X86Program info (dict-set '() 'start (Block '() (patch_trivial (patch_with_rax (Block-instr* start-block-ele))))))]
  ))

;; prelude and conclude

(define (generate_main_block var-space callee_regs)
  (define stack-space (- (* (ceiling (/ (* (+ var-space (length callee_regs)) 8) 16)) 16) (* 8 (length callee_regs))))
  (Block '() (append (list (Instr 'pushq (list (Reg 'rbp))))
                      (list (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                      (for/list ([e callee_regs]) (Instr 'pushq (list e)))
                      (list (Instr 'subq (list (Imm stack-space) (Reg 'rsp))))
                      (list (Jmp 'start)))))

(define (generate_conclude_block var-space callee_regs)
  (define stack-space (- (* (ceiling (/ (* (+ var-space (length callee_regs)) 8) 16)) 16) (* 8 (length callee_regs))))
  (Block '() (append (list (Instr 'addq (list (Imm stack-space) (Reg 'rsp))))
                      (for/list ([e (my-reverse callee_regs)]) (Instr 'popq (list e)))
                      (list (Instr 'popq (list (Reg 'rbp))))
                      (list (Retq)))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info body) (define main_block (generate_main_block (dict-ref info 'S) (dict-ref info 'callee_regs)))
                            (define conclude_block (generate_conclude_block (dict-ref info 'S) (dict-ref info 'callee_regs)))
                            (define p_with_main (dict-set body 'main main_block))
                            (X86Program info (dict-set p_with_main 'conclusion conclude_block))]
  ))

;; uncover live

(define (my-reverse lis)
    (define (get-reverse orig ret) 
        (
            cond
            [(equal? '() orig) ret]
            [else (get-reverse (cdr orig) (cons (car orig) ret))]
        )
    )
    (get-reverse lis '())
)

(define (append_live_set temp_live_set lset)
  (let ([temp_label_live (dict-ref temp_live_set 'instr-live-after)]) 
    (dict-set temp_live_set 'instr-live-after (append (list lset) temp_label_live)))
)

(define (write_locations instr)
  (match instr
    [(Instr 'movq (list a b)) (set b)]
    [(Instr 'addq (list a b)) (set b)]
    [(Instr 'subq (list a b)) (set b)]
    [(Instr 'negq (list a)) (set a)]
    [(Callq label val) (set (Reg 'rax))]
    [else (set)]
  )
)

(define (read_locations instr)
  (match instr
    [(Instr 'movq (list a b)) (match a
                                [(Var val) (set a)]
                                [else (set)])]
    [(Instr 'addq (list a b)) (match a
                                [(Var val) (set a b)]
                                [else (set b)])]
    [(Instr 'subq (list a b)) (match a
                                [(Var val) (set a b)]
                                [else (set b)])]
    [(Instr 'negq (list a)) (set a)]
    [else (set)]
  )
)

(define (examine_live_vars instr live_set)
  (match instr
    [(Jmp label) (define temp_label_set (dict-set (dict-ref live_set 'label->live) label (list (Reg 'rax) (Reg 'rsp))))
                  (define temp_live_set (dict-set live_set 'label->live temp_label_set))
                  (append_live_set temp_live_set (set (Reg 'rax) (Reg 'rsp)))]
    [else (define prev_lset (car (dict-ref live_set 'instr-live-after)))
          (define set_diff (set-subtract prev_lset (write_locations instr)))
          (append_live_set live_set (set-union set_diff (read_locations instr)))]
  )
)

(define (uncover_live_instr instr_list live_set)
  (cond
    [(equal? '() instr_list) live_set]
    [else (uncover_live_instr (cdr instr_list) (examine_live_vars (car instr_list) live_set))]
  )
)

(define (uncover_live p)
  (match p
    [(X86Program info body) (define start-block-ele (dict-ref body 'start)) 
                            (define live_set (dict-set '() 'label->live '()))
                            (define live_set_ex (dict-set live_set 'instr-live-after '()))
                            (X86Program info (dict-set '() 'start (Block (dict-set '() 'live-set (uncover_live_instr (my-reverse (Block-instr* start-block-ele)) live_set_ex)) (Block-instr* start-block-ele))))]
  ))


; build interference graph
(define (create_edges src_list des_list edge_list)
  (define (create_vertex_edge src_node temp_des temp_edges)
    (cond
      [(equal? '() temp_des) temp_edges]
      [else (create_vertex_edge src_node (cdr temp_des) (append temp_edges (list (list src_node (car temp_des)))))]
    )
  )
  (cond
    [(equal? '() src_list) edge_list]
    [else (create_edges (cdr src_list) des_list (create_vertex_edge (car src_list) des_list edge_list))]
  )
)

(define (add_edges lset instr edge_list)
  (match instr
    [(Instr 'movq (list a b)) (create_edges (set->list (set b)) (set->list (set-subtract lset (set-union (read_locations instr) (write_locations instr)))) edge_list)]
    [else (create_edges (set->list (write_locations instr)) (set->list (set-subtract lset (write_locations instr))) edge_list)]
  )
)

(define (get_edges live_set instr_list edge_list)
  (cond
    [(equal? '() live_set) edge_list]
    [else (get_edges (cdr live_set) (cdr instr_list) (add_edges (car live_set) (car instr_list) edge_list))])
)

(define (add_vertices graph vars)
  (for/list ([e vars]) (add-vertex! graph (Var (car e))))
  graph
)

(define (build_interference p)
  (match p
    [(X86Program info body) (define start-block-ele (dict-ref body 'start))
                            (define live_set (dict-ref (Block-info start-block-ele) 'live-set))
                            (define inter_graph (undirected-graph (get_edges (dict-ref live_set 'instr-live-after) (Block-instr* start-block-ele) '())))
                            (define inter_graph_all (add_vertices inter_graph (dict-ref info 'locals-types)))
                            (X86Program info (dict-set '() 'start (Block (dict-set '() 'conflicts inter_graph_all) (Block-instr* start-block-ele))))]
  ))


; ; color the graph 
; (define (color-graph grph status pqueue)
;   (let tvar (pop pqueue) ;; get highest priority variable and put it in tvar
;     (
;       cond
;       [(priority-queue-empty? pqueue) status] ;; return dict. which stores the allocation of all the colors.
;       [(dict-has-key? status tvar) 
;         (color-graph graph status (mod-pqueue));; already colored this, move on (mod-pqueue = modified pqueue by removing top elt)
;       ]  
;       [else   ;; color the node 
;         ;; step 1: get colors of all nbrs in a set  ;; using tvar which also stores the number of colors used by nbrs.
;         ;; step 2: get smallest number > 0 which is not in the set
;         ;; step 3: allocate that number to this node
;         ;; step 4: push all the neighbors with the updated values of constraints.
;         ;; step 5: call color-graph
;       ]
;     )
;   )

; )


; (define (allocate-registers status rallocs) ;; stores allocated register for each variable using colored allocated to them 

; )

; (define (remove-same-line instructions newinstructions rallocs)
;   cond
;   [(equal? '() instructions) newinstructions]
;   [else (match (car instructions)
;       [(Instr op (list a b))
;           ;; append two instructions movq a raz and op rax b and replace a and b
;       ]
;       [(Instr op (list a))
;           ;; just replace 'a with a correct register allocation 
;       ]
;       [_
;           ;; just append the instruction to newinstruction and call the function again 
;       ]
;     )]
; )
(struct pq_node (var priority))
(define (cmp->= a b)
    (>= (pq_node-priority a) (pq_node-priority b)))
(define var_pq (make-pqueue cmp->=))

(define (get_saturation vert graph colors)
  (define sat_list (for/list ([e (sequence->list (in-neighbors graph vert))]) (dict-ref colors e)))
  (set-count (set-subtract (list->set sat_list) (set 'none)))
)


(define (init_saturation graph v_set colors)
  (define (init_saturation_temp vertices ret)
    (cond
      [(equal? '() vertices) ret]
      [else (define e (car vertices)) (init_saturation_temp (cdr vertices) (dict-set ret e (pqueue-push! var_pq (pq_node e (get_saturation e graph colors)))))]
    )
  )
  (init_saturation_temp v_set '())
)

(define (init_colors vert_set ret)
  (cond
    [(equal? '() vert_set) ret]
    [else (init_colors (cdr vert_set) (dict-set ret (car vert_set) 'none))]
  )
)

(define (get_color var graph colors)
  (define unavail_cols (for/list ([e (sequence->list (in-neighbors graph var))]) (dict-ref colors e)))
  (define unavail_cols_compr (set->list (set-subtract (list->set unavail_cols) (set -1 -2 'none))))
  (define (get_color_temp ind temp_colors)
    (cond
      [(equal? temp_colors '()) ind]
      [(equal? ind (car temp_colors)) (get_color_temp (+ 1 ind) (cdr temp_colors))]
      [else ind]
    )
  )
  (get_color_temp 0 (sort unavail_cols_compr <))
)
(define (update_handles var temp_colors graph handle_map)
  (define (update_handles_temp vert_set)
    (cond
      [(equal? '() vert_set) handle_map]
      [else (cond
            [(equal? (dict-ref temp_colors (car vert_set)) 'none) (set-node-key! (dict-ref handle_map (car vert_set)) (pq_node (car vert_set) (get_saturation (car vert_set) graph temp_colors)))
            (pqueue-decrease-key! var_pq (dict-ref handle_map (car vert_set))) (update_handles_temp (cdr vert_set))]
            [else (update_handles_temp (cdr vert_set))])]
    )
  )
  (update_handles_temp (sequence->list (in-neighbors graph var)))
)

(define (color_graph graph locals-types)
  (let ([vertex-set (list->set (sequence->list (in-vertices graph)))] [colors (init_colors (sequence->list (in-vertices graph)) '())])
    (let* ([vertex-set (set-subtract vertex-set (set (Reg 'rax) (Reg 'rsp)))]  
                                          [colors (dict-set colors (Reg 'rax) -1)] [colors (dict-set colors (Reg 'rsp) -2)])
      (define handle_map (init_saturation graph (set->list vertex-set) colors))
      (define (dsatur_algo v_set temp_colors temp_handle_map)
        (cond
          [(equal? (set-count v_set) 0) temp_colors]
          [else (define hs_vert_struct (pqueue-pop! var_pq))
                (define cur_var (pq_node-var hs_vert_struct))
                (define cur_col (get_color cur_var graph temp_colors))
                (dsatur_algo (set-subtract v_set (set cur_var)) (dict-set temp_colors cur_var cur_col) 
                                                (update_handles cur_var (dict-set temp_colors cur_var cur_col) graph handle_map))]
        )
      )
      (dsatur_algo vertex-set colors handle_map)
    )))  

(define stack_index_init 10)
(define (get_register_map)
  (list (cons -1  (Reg 'rax))
          (cons -2 (Reg 'rsp))
          (cons 0 (Reg 'rcx))
          (cons 1 (Reg 'rdx))
          (cons 2 (Reg 'rsi))
          (cons 3 (Reg 'rdi))
          (cons 4 (Reg 'r8))
          (cons 5 (Reg 'r9))
          (cons 6 (Reg 'r10))
          (cons 7 (Reg 'rbx))
          (cons 8 (Reg 'r12))
          (cons 9 (Reg 'r13))
          (cons 10 (Reg 'r14)))
)

(define (get_register arg color_map)
  (define register_map (get_register_map))
  (if (dict-has-key? color_map arg)
                (if (dict-has-key? register_map (dict-ref color_map arg))
                    (dict-ref register_map (dict-ref color_map arg))
                    (Deref 'rbp (* (- (dict-ref color_map arg) stack_index_init) -8)))
                arg)
)

(define (modify-vars instructions color_map)
  (for/list ([instr instructions]) (match instr
                                      [(Instr op (list arg1)) (Instr op (list (get_register arg1 color_map)))]
                                      [(Instr op (list arg1 arg2)) (Instr op (list (get_register arg1 color_map) (get_register arg2 color_map)))]
                                      [else instr]))
)

(define (used_callee color_map)
  (define register_map (get_register_map))
  (define used_colors (for/list ([e color_map]) (cdr e)))
  (define used_callee (for/list ([e used_colors]) (if (and (>= e 7) (<= e 10))
                                                (dict-ref register_map e)
                                                'none)))
  (set->list (set-subtract (list->set used_callee) (set 'none)))
)

(define (get_max_+ve lis)
  (define (get_max_temp temp_lis ret)
    (cond
      [(equal? '() temp_lis) ret]
      [(< ret (car temp_lis)) (get_max_temp (cdr temp_lis) (car temp_lis))]
      [else (get_max_temp (cdr temp_lis) ret)]
    )
  )
  (get_max_temp lis 0)
)

(define (get_stack_usage color_map)
  (define avail_cols (for/list ([e color_map]) (dict-ref color_map (car e))))
  (define max_ele (get_max_+ve avail_cols))
  (if (> max_ele stack_index_init) 
      (- max_ele stack_index_init)
      0)
)

(define (allocate_registers p)
  (match p
    [(X86Program info body) (define start-block-ele (dict-ref body 'start)) 
                          (define undirected_graph (dict-ref (Block-info start-block-ele) 'conflicts))
                          (define color_map (color_graph undirected_graph (dict-ref info 'locals-types)))
                          (define info_block (dict-set info 'S (get_stack_usage color_map)))
                          (X86Program (dict-set info_block 'callee_regs (used_callee color_map)) (dict-set '() 'start (Block '() (modify-vars (Block-instr* start-block-ele) color_map))))]
  ))

; test programme
(define (allocate_registers1 p)
  (match p
    [(X86Program info body) (define start-block-ele (dict-ref body 'start)) 
                          ; (define undirected_graph (dict-ref (Block-info start-block-ele) 'conflicts))
                          (printf "~a ~n" (Block-instr* start-block-ele))
                          (X86Program info body)]
  ))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
     ("shrink", shrink, interp-Lif, type-check-Lif)
     ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select_instructions ,interp-pseudo-x86-0)
     ("uncover live", uncover_live, interp-x86-0)
     ("build interference", build_interference, interp-x86-0)
     ("allocate registers", allocate_registers, interp-x86-0)
    ;  ("assign homes", assign-homes, interp-x86-0)
     ("patch instructions", patch_instructions, interp-x86-0)
    ;  ("allocate registers", allocate_registers1, interp-x86-0)
     ("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
     ))