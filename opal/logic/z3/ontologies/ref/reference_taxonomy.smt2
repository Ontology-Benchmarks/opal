(declare-sort Ind 0)

(declare-fun Event (Ind) Bool)
(declare-fun Transition (Ind) Bool)
(declare-fun Activity (Ind) Bool)
(declare-fun Case (Ind) Bool)
(declare-fun Resource (Ind) Bool)
(declare-fun hasResource (Ind Ind) Bool)
(declare-fun hasRecordedTime (Ind Real) Bool)
(declare-fun hasLifecycleTransition (Ind Ind) Bool)
(declare-fun hasCase (Ind Ind) Bool)
(declare-fun hasActivity (Ind Ind) Bool)


; Declare individual constants for start and complete transitions
(declare-const T_start Ind)
(declare-const T_complete Ind)

(assert (! (transition T_start)
:named transition_start
:description "declaration of the start transition"))

(assert (! (transition T_complete)
:named transition_complete
:description "declaration of the complete transition"))