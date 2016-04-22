#lang racket

(provide (struct-out complete-proof)
         (rename-out [complete-proof? completed?]))

;;; We have one kind of complete proof. Note that all sub-proofs must
;;; be complete here.

(struct complete-proof (type rule extract sub-proofs) #:transparent)

;;;; Incomplete proofs come in a few kinds of node

;;; Nodes that are ready to be refined have a flag indicating whether
;;; their result is computationally relevant as well as a goal
(struct ready (relevant? goal) #:transparent)

;;; Nodes that are blocked on a metavariable identify the variable and
;;; provide a means of constructing a new incomplete proof based on
;;; that. todo should be a Racket procedure for constructing either a
;;; ready or a blocked, given the extract of the named variable.
(struct blocked (name todo) #:transparent)

;;; When a ready node is refined, we store the original relevance flag
;;; and goal, the tactic used to refine it, the extraction procedure,
;;; and the subgoals as either complete or partial proofs.
(struct refined (relevant? goal tactic extraction subgoals))




