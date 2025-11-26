; SIGNATURE
(declare-fun subocc (Ind Ind) Bool)
(declare-fun occ_precedes (Ind Ind) Bool)
(declare-fun occ_covers (Ind Ind) Bool)
(declare-fun comp_occ_precedes (Ind Ind Ind) Bool)
(declare-fun hand_off (Ind Ind Ind) Bool)
(declare-fun ping_pong (Ind) Bool)

; AXIOMS
(assert (! 
  (forall ((x Ind) (y Ind)) 
    (=> (occ_precedes x y) (and (activity_occurrence x) (activity_occurrence y)))
  )

:named occ_precedes_sort
:description "If an occurrence precedes another in the activity tree, both are activity occurrences."
))

(assert (! 
  (forall ((x Ind) (y Ind) (z Ind)) 
    (=> (and (occ_precedes x y) (occ_precedes y z)) (occ_precedes x z))
  )
  :named occ_precedes_transitive
  :description "The occurrence precedence relation is transitive."
))

(assert (! 
  (forall ((o Ind))
    (=> (activity_occurrence o)
    (not (occ_precedes o o))))
  :named occ_precedes_irreflexive
  :description "The occurrence precedence relation is irreflexive."
)) 

(assert (! 
  (forall ((x Ind) (y Ind)) 
    (=> (occ_precedes x y) 
        (not (exists ((z Ind)) (and (subocc z x) (distinct z x))))) 
  )
  :named occ_precedes_atomic_1
  :description "The occurrence precedence relation is between atomic occurrences."
))

(assert (! 
  (forall ((x Ind) (y Ind)) 
    (=> (occ_precedes x y) 
        (not (exists ((z Ind)) (and (subocc z y) (distinct z y))))) 
  )
  :named occ_precedes_atomic_2
  :description "The occurrence precedence relation is between atomic occurrences."
))

(assert (! 
  (forall ((o1 Ind) (o2 Ind)) 
    (=> (occ_precedes o1 o2) 
        (exists ((o Ind)) (and (subocc o1 o) (subocc o2 o)))) 
  )
  :named occ_precedes_super_occ
  :description "The occurrence precedence relation is a relation that holds for some atomic occurrences in a shared complex activity occurrence."
))

(assert (! 
  (forall ((o1 Ind) (o2 Ind)) 
    (= (occ_covers o1 o2) 
    (and (occ_precedes o1 o2)
            (not (exists ((o3 Ind)) (and (occ_precedes o1 o3) (occ_precedes o3 o2)))))
    )
    )
  :named occ_covers_def
  :description "Occurrence coverage definition"
))

(assert (! 
  (forall ((o1 Ind) (o2 Ind)) 
    (=> (occ_precedes o1 o2) 
        (exists ((o3 Ind)) (and (occ_covers o1 o3) (or (occ_precedes o3 o2) (= o2 o3))))) 
  )
  :named occ_precedes_covers
  :description "A Preceding occurrence discretely covers another occurrence."
))

(assert (! 
  (forall ((o1 Ind) (o2 Ind)) 
    (=> (occ_precedes o1 o2) 
        (exists ((o3 Ind)) (and (occ_covers o3 o2) (or (occ_precedes o1 o3) (= o1 o3))))) 
  )
  :named occ_precedes_covered
  :description "A preceded occurrence is discretely covered by another occurrence."))

(assert (! 
  (forall ((o1 Ind) (o2 Ind) (o Ind))
  (= (comp_occ_precedes o1 o2 o)
    (and (subocc o1 o)
         (subocc o2 o)
         (occ_precedes o1 o2))) 
  )
  :named comp_occ_precedes_def
  :description "Complex occurrence precedence definition"
))

(assert (! 
  (forall ((o1 Ind) (o2 Ind) (o Ind) (r1 Ind) (r2 Ind))
  (=> (and 
  (comp_occ_precedes o1 o2 o)
  (participates r1 o1)
  (participates r2 o2)
  (distinct r1 r2))
  (hand_off o1 o2 o)
  ))
  :named hand_off_def
  :description "Definition of hand-off in an activity tree"
))

(assert (! 
  (forall ((o11 Ind) (o12 Ind) (o21 Ind) (o22 Ind) (o Ind))
  (=> (and 
  (hand_off o11 o12 o)
  (hand_off o21 o22 o)
  (distinct o11 o21)
  (distinct o12 o22))
  (ping_pong o)))
  :named ping_pong_def
  :description "Ping-pong/multi-hop definition in an activity tree"
))



