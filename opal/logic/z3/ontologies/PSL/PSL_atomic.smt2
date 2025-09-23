; SIGNATURE
(declare-fun atomic (Ind) Bool)
(declare-fun conc (Ind Ind) Ind)

; AXIOMS
; Primitive activities are atomic.
(assert (!
  (forall ((a Ind))
    (=> (primitive a) (atomic a)))
  :named primitive_atomic
  :description "Primitive activities are atomic."
))

; The function conc is idempotent.
(assert (!
  (forall ((a Ind))
    (= a (conc a a)))
  :named conc_idempotent
  :description "The function conc is idempotent."
))

; The function conc is commutative.
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (= (conc a1 a2) (conc a2 a1)))
  :named conc_commutative
  :description "The function conc is commutative."
))

; The function conc is associative.
(assert (!
  (forall ((a1 Ind) (a2 Ind) (a3 Ind))
    (= (conc a1 (conc a2 a3)) (conc (conc a1 a2) a3)))
  :named conc_associative
  :description "The function conc is associative."
))

; The concurrent aggregation of atomic actions is atomic.
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (iff (atomic (conc a1 a2))
         (and (atomic a1) (atomic a2))))
  :named conc_atomic_closure
  :description "The concurrent aggregation of atomic actions is atomic."
))

; An atomic activity a1 is a subactivity of atomic activity a2 iff a2 is an idempotent for a1.
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (=> (and (atomic a1) (atomic a2))
        (iff (subactivity a1 a2)
             (= a2 (conc a1 a2)))))
  :named atomic_subactivity_idempotent
  :description "Atomic a1 is subactivity of atomic a2 iff a2 is an idempotent for a1."
))

; An atomic action has a proper subactivity iff there exists another atomic that can be concurrently aggregated.
(assert (!
  (forall ((a1 Ind) (a2 Ind))
    (=> (and (atomic a2) (subactivity a1 a2) (not (= a1 a2)))
        (exists ((a3 Ind))
          (and (atomic a3)
               (= a2 (conc a1 a3))
               (not (exists ((a4 Ind))
                      (and (atomic a4)
                           (subactivity a4 a1)
                           (subactivity a4 a3)))))))))
  :named atomic_proper_subactivity
  :description "An atomic action has a proper subactivity iff another atomic can be concurrently aggregated."
)

; The semilattice of atomic activities is distributive.
(assert (!
  (forall ((a Ind) (b0 Ind) (b1 Ind))
    (=> (and (atomic a) (atomic b0) (atomic b1)
             (subactivity a (conc b0 b1))
             (not (primitive a)))
        (exists ((a0 Ind) (a1 Ind))
          (and (subactivity a0 b0)
               (subactivity a1 b1)
               (= a (conc a0 a1))))))
  :named atomic_semilattice_distributive
  :description "The semilattice of atomic activities is distributive."
))

; Only atomic activities can be generator activities.
(assert (!
  (forall ((a Ind))
    (=> (generator a) (atomic a)))
  :named generator_atomic
  :description "Only atomic activities can be generator activities."
))

; Atomic activities are activities.
(assert (!
  (forall ((a Ind))
    (=> (atomic a) (activity a)))
  :named atomic_are_activities
  :description "Atomic activities are activities."
))