; SIGNATURE
(declare-fun activity (Ind) Bool)
(declare-fun activity_occurrence (Ind) Bool)
(declare-fun object_ (Ind) Bool)
(declare-fun timepoint (Real) Bool)

(declare-fun occurrence_of (Ind Ind) Bool)
(declare-fun participates_in (Ind Ind Real) Bool)
(declare-fun exists_at (Ind Real) Bool)
(declare-fun is_occurring_at (Ind Real) Bool)

(declare-fun begin_of (Ind) Real)
(declare-fun end_of (Ind) Real)

; AXIOMS
(assert (! 
  (forall ((x Ind)) 
    (and
      (=> (activity x) (not (or (activity_occurrence x) (object_ x))))
      (=> (activity_occurrence x) (not (or (object_ x) (activity x))))
      (=> (object_ x) (not (or (activity_occurrence x) (activity x))))
    )
  )
  :named type_disjointness
  :description "Activities, occurrences, and objects are different things."
))

(assert (! 
  (forall ((x Ind) (t1 Real) (t2 Real)) 
    (=> (and (= (begin_of x) t1) (= (begin_of x) t2)) (= t1 t2))
  )
  :named begin_unique
  :description "Start points are unique."
))

(assert (! 
  (forall ((x Ind) (t1 Real) (t2 Real)) 
    (=> (and (= (end_of x) t1) (= (end_of x) t2)) (= t1 t2))
  )
  :named ends_unique
  :description "End points are unique."
))

(assert (! 
  (forall ((o Ind)) 
    (=> (activity_occurrence o)
      (exists ((t1 Real) (t2 Real)) 
        (and 
          (= (begin_of o) t1)
          (= (end_of o) t2)
          (<= t1 t2)
        )
      )
    )
  )
  :named occurrence_bounds
  :description "Activity occurrence start points are before or equal to their end points."
))

(assert (! 
  (forall ((a Ind) (o Ind)) 
    (=> (occurrence_of o a) (and (activity_occurrence o) (activity a)))
  )
  :named occurrence_sort_constraints
  :description "Occurrences are the occurrences of activities."
))

(assert (! 
  (forall ((o Ind) (a1 Ind) (a2 Ind)) 
    (=> (and (occurrence_of o a1) (occurrence_of o a2)) (= a1 a2))
  )
  :named unique_activity_occurrence
  :description "Activity occurrences are an occurrence of a single unique activity."
))

(assert (! 
  (forall ((occ Ind)) 
    (=> (activity_occurrence occ) 
      (exists ((a Ind)) 
        (and (activity a) (occurrence_of occ a))
      )
    )
  )
  :named occurrence_has_activity
  :description "Every activity occurrence is the occurrence of some activity."
))

(assert (! 
  (forall ((x Ind) (occ Ind) (t Real)) 
    (=> (participates_in x occ t) 
      (and (object_ x) (activity_occurrence occ) (timepoint t))
    )
  )
  :named participation_sort_constraints
  :description "The participates_in relation only holds between objects, activity occurrences, and timepoints, respectively."
))

(assert (! 
  (forall ((x Ind) (occ Ind) (t Real)) 
    (=> (participates_in x occ t) 
      (and (exists_at x t) (is_occurring_at occ t))
    )
  )
  :named participation_temporal_constraint
  :description "An object can participate in an activity occurrence only at those timepoints at which both the object exists and the activity is occurring."
))

(assert (! 
  (forall ((x Ind) (t Real)) 
    (= (exists_at x t) 
      (and (object_ x) (<= (begin_of x) t) (<= t (end_of x)))
    )
  )
  :named object_temporal_existence
  :description "An object exists at a timepoint t if and only if t is between or equal to its begin and end points."
))

(assert (! 
  (forall ((occ Ind) (t Real)) 
    (= (is_occurring_at occ t) 
      (and (activity_occurrence occ) (<= (begin_of occ) t) (<= t (end_of occ)))
    )
  )
  :named occurrence_temporal_extent
  :description "An activity is occurring at a timepoint t if and only if t is between or equal to the begin and end points of the activity occurrence."
))