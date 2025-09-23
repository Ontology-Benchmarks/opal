; SIGNATURE
(declare-fun subactivity (Ind Ind) Bool)
(declare-fun primitive (Ind) Bool)

; AXIOMS
; subactivity is a relation over activities.
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (=> (subactivity a1 a2)
        (and (activity a1) (activity a2))))
  :named subactivity_relation
  :description "subactivity is a relation over activities."
))

; The subactivity relation is reflexive.
(assert (!
  (forall ((a Ind))
    (=> (activity a)
        (subactivity a a)))
  :named subactivity_reflexive
  :description "The subactivity relation is reflexive."
))

; The subactivity relation is antisymmetric.
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (=> (and (subactivity a1 a2) (subactivity a2 a1))
        (= a1 a2)))
  :named subactivity_antisymmetric
  :description "The subactivity relation is antisymmetric."
))

; The subactivity relation is transitive.
(assert (!
  (forall ((a1 Ind) (a2 Ind) (a3 Ind))
    (=> (and (subactivity a1 a2) (subactivity a2 a3))
        (subactivity a1 a3)))
  :named subactivity_transitive
  :description "The subactivity relation is transitive."
))

; The subactivity relation is a discrete ordering (upwards successor).
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (=> (and (subactivity a1 a2) (not (= a1 a2)))
        (exists ((a3 Ind))
          (and (subactivity a1 a3)
               (subactivity a3 a2)
               (not (= a3 a1))
               (forall ((a4 Ind))
                 (=> (and (subactivity a1 a4) (subactivity a4 a3))
                     (or (= a4 a1) (= a4 a3)))))))))
  :named subactivity_discrete_up
  :description "The subactivity relation is a discrete ordering, so every activity has an upwards successor."
)

; The subactivity relation is a discrete ordering (downwards successor).
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (=> (and (subactivity a1 a2) (not (= a1 a2)))
        (exists ((a3 Ind))
          (and (subactivity a1 a3)
               (subactivity a3 a2)
               (not (= a3 a2))
               (forall ((a4 Ind))
                 (=> (and (subactivity a3 a4) (subactivity a4 a2))
                     (or (= a4 a2) (= a4 a3)))))))))
  :named subactivity_discrete_down
  :description "The subactivity relation is a discrete ordering, so every activity has a downwards successor."
)

; An activity is primitive iff it has no proper subactivities.
(assert (!
  (forall ((a Ind))
    (iff (primitive a)
         (and (activity a)
              (forall ((a1 Ind))
                (=> (subactivity a1 a) (= a1 a))))))
  :named primitive_definition
  :description "An activity is primitive iff it has no proper subactivities."
))
