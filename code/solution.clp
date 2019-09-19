(deftemplate add
        (multislot op1)
        (multislot op2)
        (multislot res)
        (multislot count))
        
(deffacts init
        (digit 0 1 2 3 4 5 6 7 8 9)
        (count-sol 0))

(defrule enumerate_op1
        (not (stop-enum))
        (add (op1 $? ?x $?)
                 (op2 $?)
                 (res $?)
                 (count $?))
        (digit $? ?d $?)
        (not (enum ?x ?d))
        => 
        (assert (enum ?x ?d)))

(defrule enumerate_op2
        (not (stop-enum))
        (add (op1 $?)
                 (op2 $? ?x $?)
                 (res $?)
                 (count $?))
        (digit $? ?d $?)
        (not (enum ?x ?d))
        => 
        (assert (enum ?x ?d)))

(defrule enumerate_res
        (not (stop-enum))
        (add (op1 $?)
                 (op2 $?)
                 (res $? ?x $?)
                 (count $?))
        (digit $? ?d $?)
        (not (enum ?x ?d))
        => 
        (assert (enum ?x ?d)))

(defrule end_first
        (not(end))
        (add (op1 ?x)
                 (op2 ?y)
                 (res ?z)
                 (count 1))
        =>
        (assert (process ?x ?y ?z 1))
        (assert (end))
        (assert (stop-enum))
        (assert (tlen 1))
        (assert (len 1))
        (assert (non-zero ?x))
        (assert (non-zero ?y))
        (assert (non-zero ?z)))

(defrule end 
        (not(end))
        (add (op1 ?x)
                 (op2 ?y)
                 (res ?z)
                 (count ?l))
        (pre-process ?p ?o ?i ?k)
        (test(eq ?l (+ ?k 1)))  
        =>
        (assert (process ?x ?y ?z (+ ?k 1)))
        (assert (end))
        (assert (stop-enum))
        (assert (tlen (+ ?k 1)))
        (assert (len (+ ?k 1)))
        (assert (non-zero ?x))
        (assert (non-zero ?y))
        (assert (non-zero ?z)))

(defrule end_a
        (not(end))
        (add (op1 )
                 (op2 )
                 (res ?n)
                 (count ?l))
        (pre-process ?x ?y ?z ?k)
        (test(eq ?l (+ ?k 1)))
        =>
        (assert (end))
        (assert (stop-enum))
        (assert (tlen (+ ?k 1)))
        (assert (len (+ ?k 1)))
        (assert (one ?n (+ ?k 1))))

(defrule calculate
        (not (end))
        ?f1 <- (add (op1 $?a ?x)
                (op2 $?b ?y)
                (res $?c ?z)
                (count 1))
        =>
        (assert (pre-process ?x ?y ?z 1))
        (retract ?f1)
        (assert (add (op1 $?a)
                (op2 $?b)
                (res $?c)
                (count 2))))

(defrule iterate
        (not(end))
        ?f1 <- (add (op1 $?a ?p)
                 (op2 $?b ?o)
                 (res $?c ?i)
                 (count ?l))
        (pre-process ?x ?y ?z ?k)
        (test(eq ?l (+ ?k 1)))
        =>
        (retract ?f1)
        (assert (pre-process ?p ?o ?i ?l))
        (assert (add (op1 $?a)
                 (op2 $?b)
                 (res $?c)
                 (count (+ ?l 1)))))

(defrule assure_one
        (one ?n)
        ?f1 <- (enum ?n ?d1) 
        (test (not (eq ?d1 1))) 
        =>
        (retract ?f1))

(defrule is_one
        (one ?n ?k)
        ?f1 <- (len ?k)
        =>
        (assert (len (- ?k 1)))
        (retract ?f1)
        (assert(crypto ?k ?n 1 1))) ;with value 1 and carry carry 1

(defrule assure_non_zero
        (non-zero ?n)
        ?f1 <- (enum ?n ?d1)
        (test (eq ?d1 0)) 
        =>
        (retract ?f1))

(defrule trigger
        (or (process $? ?l) (crypto ?l $?))
        (pre-process ?x ?y ?z ?k)
        (test(eq ?l (+ ?k 1)))
        =>
        (assert (process ?x ?y ?z ?k)))

(defrule first_round_get_process 
        (tlen ?k)
        (process ?op1 ?op2 ?res ?k)
        (enum ?op1 ?d1) 
        (enum ?op2 ?d2)
        (enum ?res ?d3)
        (test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))
        (test (or (and (eq ?op1 ?res) (eq ?d1 ?d3)) (and (neq ?op1 ?res) (neq ?d1 ?d3))))
        (test (or (and (eq ?op2 ?res) (eq ?d2 ?d3)) (and (neq ?op2 ?res) (neq ?d2 ?d3))))
        (test (eq (+ ?d1 ?d2) ?d3))
        =>
        (assert (crypto ?k ?op1 ?d1 ?op2 ?d2 ?res ?d3 0)))

(defrule first_round_get_process_with_carry
        (tlen ?k)
        (process ?op1 ?op2 ?res ?k)
        (enum ?op1 ?d1) 
        (enum ?op2 ?d2)
        (enum ?res ?d3)
        (test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))
        (test (or (and (eq ?op1 ?res) (eq ?d1 ?d3)) (and (neq ?op1 ?res) (neq ?d1 ?d3))))
        (test (or (and (eq ?op2 ?res) (eq ?d2 ?d3)) (and (neq ?op2 ?res) (neq ?d2 ?d3))))
        (test (eq (+ ?d1 ?d2 1) ?d3))
        =>
        (assert (crypto ?k ?op1 ?d1 ?op2 ?d2 ?res ?d3 1)))

(defrule get_process
        (tlen ?l)
        (process ?op1 ?op2 ?res ?k)
        (test(not (eq ?l ?k)))
        (enum ?op1 ?d1) 
        (enum ?op2 ?d2)
        (enum ?res ?d3)
        (test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))
        (test (or (and (eq ?op1 ?res) (eq ?d1 ?d3)) (and (neq ?op1 ?res) (neq ?d1 ?d3))))
        (test (or (and (eq ?op2 ?res) (eq ?d2 ?d3)) (and (neq ?op2 ?res) (neq ?d2 ?d3))))
        (test (eq (mod (+ ?d1 ?d2) 10) ?d3))
        =>
        (assert (pre-crypto ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?k (div (+ ?d1 ?d2) 10) 0))) ;k is len, i is carryover generated, 0 is carryover required

(defrule get_process_with_carry
        (tlen ?l)
        (process ?op1 ?op2 ?res ?k)
        (test(not (eq ?k 1)))
        (test(not (eq ?l ?k)))
        (enum ?op1 ?d1) 
        (enum ?op2 ?d2)
        (enum ?res ?d3)
        (test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))
        (test (or (and (eq ?op1 ?res) (eq ?d1 ?d3)) (and (neq ?op1 ?res) (neq ?d1 ?d3))))
        (test (or (and (eq ?op2 ?res) (eq ?d2 ?d3)) (and (neq ?op2 ?res) (neq ?d2 ?d3))))
        (test (eq (mod (+ ?d1 (+ ?d2 1)) 10) ?d3))
        =>
        (assert (pre-crypto ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?k (div (+ ?d1 ?d2 1) 10) 1))) ;k is len, i is carryover generated, 1 is carryover required

(defrule compact_crypto
    ?f1 <- (crypto $?stha ?op1 ?d1 $?sthb ?op1 ?d1 $?sthc)
    (digit $?digits)
    (test (not (subsetp (create$ ?op1) (create$ $?digits))))
    (test (subsetp (create$ ?d1) (create$ $?digits)))
    =>
    (retract ?f1)
    (assert (crypto $?stha ?op1 ?d1 $?sthb $?sthc)))

(defrule get_pre_crypto_already_found
        (crypto ?l $?stha ?opi ?di $?sthb ?opj ?dj $?sthc ?opk ?dk $?sthd ?i) 
        (pre-crypto ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?k ?i ?j)
        (digit $?digits)
        ; test that every op1 has not been already assigned
        ; and test that digit has not been assigned to other letter 
        (test (eq ?l (+ ?k 1)))  
        (test (not (subsetp (create$ ?opi) (create$ $?digits))))
        (test (not (subsetp (create$ ?opj) (create$ $?digits))))
        (test (not (subsetp (create$ ?opk) (create$ $?digits))))
        (test (or
                (and (eq ?op1 ?opi) (eq ?d1 ?di) (eq ?op2 ?opj) (eq ?d2 ?dj) (eq ?res ?opk) (eq ?d3 ?dk))
                (and (eq ?op1 ?opi) (eq ?d1 ?di) (eq ?res ?opj) (eq ?d3 ?dj) (eq ?op2 ?opk) (eq ?d2 ?dk))
                (and (eq ?op2 ?opi) (eq ?d2 ?di) (eq ?op1 ?opj) (eq ?d1 ?dj) (eq ?res ?opk) (eq ?d3 ?dk))
                (and (eq ?op2 ?opi) (eq ?d2 ?di) (eq ?res ?opj) (eq ?d3 ?dj) (eq ?op1 ?opk) (eq ?d1 ?dk))
                (and (eq ?res ?opi) (eq ?d3 ?di) (eq ?op1 ?opj) (eq ?d1 ?dj) (eq ?op2 ?opk) (eq ?d2 ?dk))
                (and (eq ?res ?opi) (eq ?d3 ?di) (eq ?op2 ?opj) (eq ?d2 ?dj) (eq ?op1 ?opk) (eq ?d1 ?dk))))
        =>
        (assert (crypto ?k $?stha ?opi ?di $?sthb ?opj ?dj $?sthc ?opk ?dk $?sthd ?j)))

(defrule get_pre_crypto_completely_new
        (crypto ?l $?stha ?i) 
        (pre-crypto ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?k ?i ?j)
        ; test that every op1 has not been already assigned
        ; and test that digit has not been assigned to other letter   
        (test (not (subsetp (create$ ?op1) (create$ $?stha))))
        (test (not (subsetp (create$ ?d1) (create$ $?stha))))
        (test (not (subsetp (create$ ?op2) (create$ $?stha))))
        (test (not (subsetp (create$ ?d2) (create$ $?stha))))
        (test (not (subsetp (create$ ?res) (create$ $?stha))))
        (test (not (subsetp (create$ ?d3) (create$ $?stha))))
        (test (eq ?l (+ ?k 1)))
        =>
        (assert (crypto ?k $?stha ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?j)))

(defrule get_pre_crypto_two_new
        (crypto ?l $?stha ?opi ?di $?sthb ?i)
        (pre-crypto ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?k ?i ?j)
        (digit $?digits)
        (test (eq ?l (+ ?k 1)))
        (test (not (subsetp (create$ ?opi) (create$ $?digits))))
        (test (or 
                (and 
                    (eq ?op1 ?opi) (eq ?d1 ?di)
                    (not (subsetp (create$ ?op2) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?d2) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?res) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?d3) (create$ $?stha $?sthb))))
                (and 
                    (eq ?op2 ?opi) (eq ?d2 ?di)
                    (not (subsetp (create$ ?op1) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?d1) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?res) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?d3) (create$ $?stha $?sthb))))
                (and 
                    (eq ?res ?opi) (eq ?d3 ?di)
                    (not (subsetp (create$ ?op2) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?d2) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?op1) (create$ $?stha $?sthb)))
                    (not (subsetp (create$ ?d1) (create$ $?stha $?sthb))))))
        =>
        (assert (crypto ?k $?stha $?sthb ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?j)))

(defrule get_pre_crypto_one_new
        (crypto ?l $?stha ?opi ?di $?sthb ?opj ?dj $?sthc ?i) 
        (pre-crypto ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?k ?i ?j)
        (digit $?digits)
        (test (eq ?l (+ ?k 1)))
        (test (not (subsetp (create$ ?opi) (create$ $?digits))))
        (test (not (subsetp (create$ ?opj) (create$ $?digits))))
        (test (or
                (and
                    (not (subsetp (create$ ?res) (create$ $?stha $?sthb $?sthc)))
                    (not (subsetp (create$ ?d3) (create$ $?stha $?sthb $?sthc)))
                    (or
                        (and (eq ?op1 ?opi) (eq ?d1 ?di) (eq ?op2 ?opj) (eq ?d2 ?dj)) 
                        (and (eq ?op2 ?opi) (eq ?d2 ?di) (eq ?op1 ?opj) (eq ?d1 ?dj))))
                (and
                    (not (subsetp (create$ ?op1) (create$ $?stha $?sthb $?sthc)))
                    (not (subsetp (create$ ?d1) (create$ $?stha $?sthb $?sthc)))
                    (or
                        (and (eq ?res ?opi) (eq ?d3 ?di) (eq ?op2 ?opj) (eq ?d2 ?dj)) 
                        (and (eq ?op2 ?opi) (eq ?d2 ?di) (eq ?res ?opj) (eq ?d3 ?dj))))
                (and
                    (not (subsetp (create$ ?op2) (create$ $?stha $?sthb $?sthc)))
                    (not (subsetp (create$ ?d2) (create$ $?stha $?sthb $?sthc)))
                    (or
                        (and (eq ?res ?opi) (eq ?d3 ?di) (eq ?op1 ?opj) (eq ?d1 ?dj)) 
                        (and (eq ?op1 ?opi) (eq ?d1 ?di) (eq ?res ?opj) (eq ?d3 ?dj))))))   
        =>
        (assert (crypto ?k $?stha $?sthb $?sthc ?op1 ?d1 ?op2 ?d2 ?res ?d3 ?j)))

(defrule sol_found
        ?f1 <- (crypto 1 $?sol 0)
        ?f2 <- (count-sol ?k)
        =>
        (assert (count-sol (+ ?k 1)))
        (retract ?f1 ?f2)
        (assert (sol n (+ ?k 1) $?sol))
        (printout t " Solution(s): " (+ ?k 1) $?sol crlf))
        
(defrule input
        =>
        (printout t "op1:")
        (bind ?op1 (readline))
        (printout t "op2:")
        (bind ?op2 (readline))
        (printout t "res:")
        (bind ?res (readline))
        (assert (add (op1 (explode$ ?op1))
                                (op2 (explode$ ?op2))
                                (res (explode$ ?res))
                                (count 1)))
        (printout t "count-sol: 0" crlf)
        (assert(enum EMPTY 0)))
