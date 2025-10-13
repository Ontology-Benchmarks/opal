(declare-sort Ind 0)

(declare-fun Event (Ind) Bool)
(declare-fun Transition (Ind) Bool)
(declare-fun Activity (Ind) Bool)
(declare-fun Case (Ind) Bool)
(declare-fun Resource (Ind) Bool)
(declare-fun hasResource (Ind Ind) Bool)
(declare-fun hasRecordedTime (Ind) Real)
(declare-fun hasLifecycleTransition (Ind Ind) Bool)
(declare-fun hasCase (Ind Ind) Bool)
(declare-fun hasActivity (Ind Ind) Bool)
(declare-fun next_event (Ind Ind) Bool)
(declare-fun earlier (Ind Ind) Bool)


; Declare individual constants for start and complete transitions
(declare-const T_start Ind)
(declare-const T_complete Ind)

(assert (! (transition T_start)
:named transition_start
:description "declaration of the start transition"))

(assert (! (transition T_complete)
:named transition_complete
:description "declaration of the complete transition"))

; SIMPLE INFERENCE RULES

; events, transitions, activities, cases, and resources are disjoint classes
(assert (!
    (forall ((x Ind))
        (and
            ; Assert that no 'x' can be in any two of these categories.
            (=> (Event x) (not (or (Transition x) (Activity x) (Case x) (Resource x))))
            (=> (Transition x) (not (or (Activity x) (Case x) (Resource x))))
            (=> (Activity x) (not (or (Case x) (Resource x))))
            (=> (Case x) (not (Resource x)))
        )
    )
    :named disjoint_classes
    :description "Events, transitions, activities, cases, and resources are disjoint."
))

(assert (!
    (forall ((e1 Ind) (e2 Ind))
        (=>
            (exists ((c Ind) (t1 Real) (t2 Real))
                (and
                    (hasCase e1 c)
                    (hasCase e2 c)
                    (= (hasRecordedTime e1) t1)
                    (= (hasRecordedTime e2) t2)
                    (< t1 t2)
                )
            )
            (earlier e1 e2)
        )
    )
    :named event_order_SIMPLE
))

(assert (!
    (forall ((e1 Ind) (e2 Ind))
        (=>
            (exists ((c Ind) (t1 Real) (t2 Real))
                (and
                    (hasCase e1 c)
                    (hasCase e2 c)
                    (= (hasRecordedTime e1) t1)
                    (= (hasRecordedTime e2) t2)
                    (< t1 t2)
                    (not (exists ((e3 Ind) (t3 Real))
                        (and
                            (Event e3)
                            (not (= e3 e1))
                            (not (= e3 e2))
                            (hasCase e3 c)
                            (= (hasRecordedTime e3) t3)
                            (< t1 t3)
                            (< t3 t2)
                        )
                    ))
                )
            )
            (next_event e1 e2)
        )
    )
    :named infer_next_event
    :description "Infers that e2 is the next event after e1 if they are in the same case, ordered by time, and no other event occurs between them."
))
