; SIGNATURE
(declare-fun arboreal (Ind) Bool)
(declare-fun earlier (Ind Ind) Bool)
(declare-fun earlierEq (Ind Ind) Bool)
(declare-fun initial (Ind) Bool)
(declare-fun generator (Ind) Bool)
(declare-fun legal (Ind) Bool)
(declare-fun precedes (Ind Ind) Bool)
(declare-fun poss (Ind Ind) Bool)

(declare-fun successor (Ind Ind) Ind)

; AXIOMS
; Arboreal restriction
(assert (!
  (forall ((s Ind))
    (=> (arboreal s) (activity_occurrence s))
  )
  :named arboreal_occurrence_restriction
  :description "The earlier relation is restricted to arboreal activity occurrences (that is, activity occurrences that are elements of the occurrence tree)."
))

; Earlier requires arboreal
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (=> (earlier s1 s2) (and (arboreal s1) (arboreal s2)))
  )
  :named earlier_requires_arboreal
  :description "The earlier relation is restricted to arboreal activity occurrences."
))

; Earlier irreflexive
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (=> (earlier s1 s2) (not (earlier s2 s1)))
  )
  :named earlier_irreflexive
  :description "The ordering relation over occurrences is irreflexive."
))

; Earlier transitive
(assert (!
  (forall ((s1 Ind) (s2 Ind) (s3 Ind))
    (=> (and (earlier s1 s2) (earlier s2 s3)) (earlier s1 s3))
  )
  :named earlier_transitive
  :description "The ordering relation over occurrences is transitive."
))

; Branch totally ordered
(assert (!
  (forall ((s1 Ind) (s2 Ind) (s3 Ind))
    (=> (and (earlier s1 s2) (earlier s3 s2))
        (or (earlier s1 s3) (earlier s3 s1) (= s3 s1)))
  )
  :named branch_total_order
  :description "A branch in the occurrence tree is totally ordered."
))

; Branch has initial occurrence
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (=> (earlier s1 s2)
        (exists ((sp Ind)) (and (initial sp) (earlierEq sp s1))))
  )
  :named branch_initial_occurrence
  :description "Every branch of the occurrence tree has an initial occurrence."
))

; No two initials of same activity
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (=> (and (initial s1) (initial s2) (occurrence_of s1 a) (occurrence_of s2 a))
        (= s1 s2))
  )
  :named initial_unique_per_activity
  :description "No two initial activity occurrences in the occurrence tree are occurrences of the same activity."
))

; Generator iff initial occurrence
(assert (!
  (forall ((a Ind))
    (=> (generator a)
        (exists ((s Ind)) (and (initial s) (occurrence_of s a))))
  )
  :named generator_initial_occurrence
  :description "An activity is a generator iff it has an initial occurrence in the occurrence tree."
))

; Activity has initial occurrence
(assert (!
  (forall ((s Ind) (a Ind))
    (=> (occurrence_of s a) (= (arboreal s) (generator a)))
  )
  :named activity_initial_occurrence
  :description "There is an initial occurrence of each activity."
))

; Successor of arboreal occurrence
(assert (!
  (forall ((a Ind) (o Ind))
    (= (occurrence_of (successor a o) a)
       (and (generator a) (arboreal o)))
  )
  :named successor_generator_relation
  :description "The successor of an arboreal activity occurrence is an occurrence of a generator activity."
))

; Every non-initial has predecessor
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (=> (earlier s1 s2)
        (exists ((a Ind) (s3 Ind))
          (and (generator a) (= s2 (successor a s3)))))
  )
  :named noninitial_has_predecessor
  :description "Every non-initial activity occurrence is the successor of another activity occurrence."
))

; Earlier <-> successor relation
(assert (!
  (forall ((a Ind) (s1 Ind) (s2 Ind))
    (=> (generator a)
        (= (earlier s1 (successor a s2)) (earlierEq s1 s2)))
  )
  :named successor_earlier_relation
  :description "An occurrence s1 is earlier than the successor occurrence of s2 iff the occurrence s2 is later than s1."
))

; Legal implies arboreal
(assert (!
  (forall ((s Ind))
    (=> (legal s) (arboreal s))
  )
  :named legal_implies_arboreal
  :description "The legal relation restricts arboreal activity occurrences."
))

; Legal closed under earlier
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (=> (and (legal s1) (earlier s2 s1)) (legal s2))
  )
  :named legal_closed_under_earlier
  :description "If an activity occurrence is legal, all earlier activity occurrences in the occurrence tree are also legal."
))

; End before successor begin
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (=> (earlier s1 s2) (< (end_of s1) (begin_of s2)))
  )
  :named end_before_successor_begin
  :description "The end of an activity occurrence is before the begin_of the successor of the activity occurrence."
))

; Precedes definition
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (= (precedes s1 s2) (and (earlier s1 s2) (legal s2)))
  )
  :named precedes_definition
  :description "An activity occurrence s1 precedes another activity occurrence s2 iff s1 is earlier than s2 and s2 is legal."
))

; EarlierEq definition
(assert (!
  (forall ((s1 Ind) (s2 Ind))
    (= (earlierEq s1 s2)
       (and (arboreal s1) (arboreal s2)
            (or (earlier s1 s2) (= s1 s2))))
  )
  :named earlierEq_definition
  :description "An activity occurrence s1 is EarlierEq than an activity occurrence s2 iff it is either earlier than s2 or equal to s2."
))

; Poss definition
(assert (!
  (forall ((a Ind) (s Ind))
    (= (poss a s) (legal (successor a s)))
  )
  :named poss_definition
  :description "An activity is poss at some occurrence iff the successor occurrence of the activity is legal."
))

; Initial iff no earlier
(assert (!
  (forall ((s Ind))
    (= (initial s)
       (and (arboreal s) (not (exists ((sp Ind)) (earlier sp s)))))
  )
  :named initial_definition
  :description "No occurrence in the occurrence tree is earlier than an initial occurrence."
))




