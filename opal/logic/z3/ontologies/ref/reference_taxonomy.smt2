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
(declare-const Ind T_start)
(declare-const Ind T_complete)