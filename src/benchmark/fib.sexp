((col w) (k 10) (selectors (q0 q1))
 (polynomial_gates
  ((Binop Mul (Selector q0) (Binop Sub (Ref -3) (Ref -1)))
   (Binop Mul (Selector q1)
    (Binop Sub (Ref 0) (Binop Add (Ref -2) (Ref -1))))))
 (copy_gates ((8 0))) (selector_values ((q0 (9)) (q1 (3 4 5 6 7))))
 (witness_values ((0 5) (1 0) (2 1) (3 1) (4 2) (5 3) (6 5) (7 8) (8 5))))