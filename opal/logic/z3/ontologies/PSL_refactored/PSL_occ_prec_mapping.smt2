(assert (! 
  (forall ((e1 Ind) (e2 Ind) (t1 Real) (t2 Real) (c Ind) (a Ind) (p Ind))
    (=> (and
      (hasCase e1 c)
      (hasCase e2 c)
      (not (= e1 e2))
      (hasActivity e1 a)
      (hasActivity e2 a)
      (hasLifecycleTransition e1 T_start)
      (hasLifecycleTransition e2 T_complete)
      (= (hasRecordedTime e1) t1)
      (= (hasRecordedTime e2) t2)
      (hasProcess c p)
    )
    (subocc (ev_occ e1 e2) c)
    )
  )
  :named subocc_ev_occ
  :description "Maps start and complete events to subactivity occurrences of the case."
  ))

  (assert (! 
  (forall ((e11 Ind) (e12 Ind) (e21 Ind) (e22 Ind) (c Ind))
    (=> (and
      (subocc (ev_occ e11 e12) c)
      (subocc (ev_occ e21 e22) c)
      (distinct (ev_occ e11 e12) (ev_occ e21 e22))
      (event_earlier e12 e21 c)
    )
    (comp_occ_precedes (ev_occ e11 e12) (ev_occ e21 e22) c)
    )
  )
  :named comp_occ_precedes_mapping
  :description "Maps subactivity occurrences precedence based on event order."
  ))

