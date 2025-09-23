(assert (! 
  (forall ((e1 Ind) (e2 Ind) (t1 Real) (t2 Real) (c Ind) (a Ind))
    (=> (and
      (hasCase e1 c)
      (hasCase e2 c)
      (hasActivity e1 a)
      (hasActivity e2 a)
      (hasLifecycleTransition e1 T_start)
      (hasLifecycleTransition e2 T_complete)
      (hasRecordedTime e1 t1)
      (hasRecordedTime e2 t2)
    )
    (exists ((o Ind))
      (and
        (occurrence_of o a)
        (= (begin_of o) t1)
        (= (end_of o) t2)
      )
    )
  ))
  :named occurrence_start_end_event_mapping
  :description "Maps start and complete events to activity occurrences."))

  (assert (! 
  (forall ((e1 Ind) (e2 Ind) (t1 Real) (t2 Real) (c Ind) (a Ind) (r1 Ind) (r2 Ind))
    (=> (and
      (hasCase e1 c)
      (hasCase e2 c)
      (hasActivity e1 a)
      (hasActivity e2 a)
      (hasLifecycleTransition e1 T_start)
      (hasLifecycleTransition e2 T_complete)
      (hasRecordedTime e1 t1)
      (hasRecordedTime e2 t2)
      (hasResource e1 r1)
      (hasResource e2 r2)
    )
    (exists ((o Ind))
      (and
        (participates_in r1 o t1)
        (participates_in r2 o t2)
      )
    )
  ))
  :named occurrence_participation_mapping
  :description "Maps start and complete events resources to participation in the occurrence."))