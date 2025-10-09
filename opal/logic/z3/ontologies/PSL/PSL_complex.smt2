; SIGNATURE
(declare-fun legal (Ind) Bool)
(declare-fun successor (Ind Ind) Ind)
(declare-fun hand_off (Ind Ind Ind Ind Ind) Bool)
(declare-fun ping_pong (Ind) Bool)

(declare-fun min_precedes (Ind Ind Ind) Bool)
(declare-fun root (Ind Ind) Bool)
(declare-fun subtree (Ind Ind Ind Ind) Bool)
(declare-fun next_subocc (Ind Ind Ind) Bool)
(declare-fun leaf (Ind Ind) Bool)
(declare-fun do (Ind Ind Ind) Bool)
(declare-fun sibling (Ind Ind Ind) Bool)

; AXIOMS
; Occurrences in the activity tree for an activity correspond to atomic subactivity occurrences.
(assert (!
  (forall ((a Ind) (s1 Ind) (s2 Ind))
    (=> (min_precedes s1 s2 a)
        (exists ((a1 Ind) (a2 Ind))
          (and (subactivity a1 a)
               (subactivity a2 a)
               (atocc s1 a1)
               (atocc s2 a2)))))
  :named act_tree_occ_atomic
  :description "Occurrences in the activity tree for an activity correspond to atomic subactivity occurrences."
))

; Root occurrences in the activity tree correspond to atomic subactivity occurrences.
(assert (!
  (forall ((a Ind) (s Ind))
    (=> (root s a)
        (exists ((a1 Ind))
          (and (subactivity a1 a) (atocc s a1)))))
  :named act_tree_root_atomic
  :description "Root occurrences in the activity tree correspond to atomic subactivity occurrences."
))

; All activity trees have a root subactivity occurrence.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (=> (min_precedes s1 s2 a)
        (exists ((s3 Ind))
          (and (root s3 a) (min_precedes s3 s2 a)))))
  :named act_tree_has_root
  :description "All activity trees have a root subactivity occurrence."
))

; No subactivity occurrences occur earlier than the root.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (=> (min_precedes s1 s2 a)
        (not (root s2 a))))
  :named act_tree_root_no_earlier
  :description "No subactivity occurrences in an activity tree occur earlier than the root."
))

; Activity trees are subtrees of the occurrence tree.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (=> (min_precedes s1 s2 a) (precedes s1 s2)))
  :named act_tree_sub_occ_tree
  :description "Activity trees are subtrees of the occurrence tree."
))

; Root occurrences are legal.
(assert (!
  (forall ((s Ind) (a Ind))
    (=> (root s a) (legal s)))
  :named root_legal
  :description "Root occurrences are elements of the occurrence tree."
))

; Every legal atomic activity occurrence is a single-node activity tree.
(assert (!
  (forall ((s Ind) (a Ind))
    (=> (and (atocc s a) (legal s)) (root s a)))
  :named legal_atomic_is_tree
  :description "Every legal atomic activity occurrence is an activity tree with only one occurrence."
))

; Activity trees are discrete.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (=> (min_precedes s1 s2 a)
        (exists ((s3 Ind))
          (and (next_subocc s1 s3 a)
               (or (min_precedes s3 s2 a) (= s3 s2))))))
  :named act_tree_discrete
  :description "Activity trees are discrete."
))

; Subactivity occurrences on the same branch of the occurrence tree are on the same branch of the activity tree.
(assert (!
  (forall ((a Ind) (s1 Ind) (s2 Ind) (s3 Ind))
    (=> (and (min_precedes s1 s2 a)
             (min_precedes s1 s3 a)
             (precedes s2 s3))
        (min_precedes s2 s3 a)))
  :named act_tree_branch_consistency
  :description "Subactivity occurrences on the same branch of the occurrence tree are on the same branch of the activity tree."
))

; The activity tree for a complex subactivity occurrence is a subtree of the activity tree for the activity occurrence.
(assert (!
  (forall ((a1 Ind) (a2 Ind) (s1 Ind) (s2 Ind) (s3 Ind))
    (=> (and (subactivity a1 a2)
             (subtree s1 a1 s2 a2)
             (min_precedes s1 s3 a1))
        (min_precedes s1 s3 a2)))
  :named complex_subtree_property
  :description "The activity tree for a complex subactivity occurrence is a subtree of the activity tree for the activity occurrence."
))

; Only complex activities can be arguments to min_precedes.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (=> (min_precedes s1 s2 a) (not (atomic a))))
  :named min_precedes_complex_only
  :description "Only complex activities can be arguments to min_precedes."
))

; Subactivity occurrences on the same branch of the activity tree are linearly ordered.
(assert (!
  (forall ((a Ind) (s1 Ind) (s2 Ind) (s3 Ind))
    (=> (and (min_precedes s2 s1 a)
             (min_precedes s3 s1 a)
             (precedes s2 s3))
        (min_precedes s2 s3 a)))
  :named act_tree_linear_order
  :description "Subactivity occurrences on the same branch of the activity tree are linearly ordered."
))

; Definition of leaf in the activity tree.
(assert (!
  (forall ((s Ind) (a Ind))
    (iff (leaf s a)
         (and (or (root s a) (exists ((s1 Ind)) (min_precedes s1 s a)))
              (not (exists ((s2 Ind)) (min_precedes s s2 a))))))
  :named leaf_def
  :description "An occurrence is the leaf of an activity tree iff it has an earlier but no later subactivity occurrence."
))

; The do relation specifies the initial and final atomic subactivity occurrences.
(assert (!
  (forall ((a Ind) (s1 Ind) (s2 Ind))
    (iff (do a s1 s2)
         (and (root s1 a)
              (leaf s2 a)
              (or (min_precedes s1 s2 a) (= s1 s2)))))
  :named do_relation
  :description "The do relation specifies the initial and final atomic subactivity occurrences of an activity."
))

; Next suboccurrence definition.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (iff (next_subocc s1 s2 a)
         (and (min_precedes s1 s2 a)
              (not (exists ((s3 Ind))
                     (and (activity_occurrence s3)
                          (min_precedes s1 s3 a)
                          (min_precedes s3 s2 a)))))))
  :named next_subocc_def
  :description "An activity occurrence s2 is the next suboccurrence after s1 iff s1 precedes s2 and no intermediate occurrence exists."
))

; Subtree definition.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a1 Ind) (a2 Ind))
    (iff (subtree s1 a1 s2 a2)
         (and (root s1 a1)
              (root s2 a2)
              (or (min_precedes s1 s2 a1) (= s1 s2))
              (forall ((s3 Ind))
                (=> (min_precedes s1 s3 a1) (min_precedes s2 s3 a2))))))
  :named subtree_def
  :description "Tree for a1 with root s1 contains tree for a2 with root s2 iff every atomic occurrence of a2 is in a1 and a1 has something extra."
))

; Sibling definition.
(assert (!
  (forall ((s1 Ind) (s2 Ind) (a Ind))
    (iff (sibling s1 s2 a)
         (or (exists ((s3 Ind))
               (and (next_subocc s3 s1 a)
                    (next_subocc s3 s2 a)))
             (and (root s1 a)
                  (root s2 a)
                  (or (and (initial s1) (initial s2))
                      (exists ((s4 Ind) (a1 Ind) (a2 Ind))
                        (and (= s1 (successor a1 s4))
                             (= s2 (successor a2 s4)))))))))
  :named sibling_def
  :description "Two subactivity occurrences are siblings if they have a common predecessor in the activity tree or share a predecessor in the occurrence tree."
))


