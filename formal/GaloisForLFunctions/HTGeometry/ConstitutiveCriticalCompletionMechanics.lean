import Mathlib.Data.List.Infix
import Mathlib.Order.WellFounded

/-!
# Constitutive critical-completion mechanics

This module certifies a route-independent law-generation mechanism.  Every word execution is
well-founded, but each finite executable rulebook is nonconfluent.  Its missing joining rule is
already valid in the old generated equivalence, so adjoining it is semantically conservative;
nevertheless the new executable rule produces the next marked failure.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-completion-mechanics/
terminating-execution-open-conservative-completion-and-critical-heredity-law.md`.
-/

namespace ConstitutiveCriticalCompletionMechanics

/-- Two-letter alphabet for the completion laboratory. -/
inductive Letter
  | a
  | b
  deriving DecidableEq, Repr

/-- Finite words in the two-letter alphabet. -/
abbrev Word := List Letter

/-- Left side `a b^n a` of rule `n`. -/
def left (n : ℕ) : Word := .a :: List.replicate n .b ++ [.a]

/-- Right side `b^n a` of rule `n`. -/
def right (n : ℕ) : Word := List.replicate n .b ++ [.a]

/-- Marked overlap word for rules `m` and `n`. -/
def critical (m n : ℕ) : Word := left m ++ List.replicate n .b ++ [.a]

/-- One contextual rewrite using an indexed rule admitted by finite stage `N`. -/
def Step (N : ℕ) (u v : Word) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ N ∧ ∃ p s,
    u = p ++ left n ++ s ∧ v = p ++ right n ++ s

theorem critical_eq_suffix (m n : ℕ) :
    critical m n = (.a :: List.replicate m .b) ++ left n := by
  simp [critical, left, List.append_assoc]

/-- The persistent seed rule is the first branch of the marked peak. -/
theorem critical_seed_step (n : ℕ) (hn : 1 ≤ n) :
    Step n (critical 1 n) (.b :: left n) := by
  refine ⟨1, by omega, hn, [], List.replicate n .b ++ [.a], ?_, ?_⟩
  · simp [critical, left]
  · simp [right, left]

/-- The newest admitted rule is the second branch of the marked peak. -/
theorem critical_newest_step (n : ℕ) (hn : 1 ≤ n) :
    Step n (critical 1 n) (left (n + 1)) := by
  refine ⟨n, hn, le_rfl, [.a, .b], [], ?_, ?_⟩
  · simp [critical_eq_suffix, left]
  · simp [left, right, List.replicate_succ]

/-- After the seed step, the newest rule reaches the other marked endpoint. -/
theorem intermediate_step (n : ℕ) (hn : 1 ≤ n) :
    Step n (.b :: left n) (right (n + 1)) := by
  refine ⟨n, hn, le_rfl, [.b], [], ?_, ?_⟩
  · simp
  · simp [right, List.replicate_succ]

theorem count_a_replicate_b (n : ℕ) :
    (List.replicate n Letter.b).count .a = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem count_a_left (n : ℕ) : (left n).count .a = 2 := by
  simp [left, count_a_replicate_b]

theorem count_a_right (n : ℕ) : (right n).count .a = 1 := by
  simp [right, count_a_replicate_b]

/-- Every executable rule decreases the number of `a` letters by exactly one. -/
theorem step_count_a (h : Step N u v) : v.count .a + 1 = u.count .a := by
  rcases h with ⟨n, hn, hN, p, s, rfl, rfl⟩
  rw [List.count_append, List.count_append, List.count_append, List.count_append,
    count_a_left, count_a_right]
  omega

theorem step_count_a_lt (h : Step N u v) : v.count .a < u.count .a := by
  have hcount := step_count_a h
  omega

/-- Object-level execution terminates at every finite completion stage. -/
theorem step_wellFounded (N : ℕ) :
    WellFounded (fun v u => Step N u v) := by
  apply (InvImage.wf (fun w : Word => w.count .a) (Nat.lt_wfRel.2)).mono
  intro v u h
  exact step_count_a_lt h

/-- A word is normal when it has no outgoing executable rewrite. -/
def Normal (N : ℕ) (w : Word) : Prop := ∀ v, ¬ Step N w v

theorem prefix_empty_of_left_eq (M n : ℕ) (p s : Word)
    (hp : p.count .a = 0) (h : left M = p ++ left n ++ s) : p = [] := by
  cases p with
  | nil => rfl
  | cons x xs =>
      have hx : x = .a := by
        have hh := congrArg List.head? h
        symm
        simpa [left] using hh
      subst x
      simp at hp

theorem reverse_left (n : ℕ) : (left n).reverse = left n := by
  simp [left, List.reverse_append]

/-- The right endpoint of the next missing rule is normal at stage `N`. -/
theorem normal_right_succ (N : ℕ) : Normal N (right (N + 1)) := by
  intro v h
  rcases h with ⟨n, hn, hN, p, s, hu, hv⟩
  have hc := congrArg (fun w : Word => w.count .a) hu
  simp [count_a_left, count_a_right, List.count_append] at hc
  omega

/-- The left endpoint of the next missing rule is normal at stage `N`. -/
theorem normal_left_succ (N : ℕ) : Normal N (left (N + 1)) := by
  intro v h
  rcases h with ⟨n, hn, hN, p, s, hu, hv⟩
  have hc := congrArg (fun w : Word => w.count .a) hu
  simp [count_a_left, List.count_append] at hc
  have hp : p.count .a = 0 := by omega
  have hs : s.count .a = 0 := by omega
  have hpnil : p = [] := prefix_empty_of_left_eq (N + 1) n p s hp hu
  subst p
  simp only [List.nil_append] at hu
  have hrev := congrArg List.reverse hu
  rw [reverse_left, List.reverse_append, reverse_left] at hrev
  have hsnilRev : s.reverse = [] :=
    prefix_empty_of_left_eq (N + 1) n s.reverse [] (by simpa using hs) (by simpa using hrev)
  have hsnil : s = [] := by simpa using congrArg List.reverse hsnilRev
  subst s
  simp only [List.append_nil] at hu
  have hlen := congrArg List.length hu
  simp [left] at hlen
  omega

/-- Reflexive transitive execution at finite stage `N`. -/
abbrev Reach (N : ℕ) := Relation.ReflTransGen (Step N)

theorem critical_to_right (N : ℕ) (hN : 1 ≤ N) :
    Reach N (critical 1 N) (right (N + 1)) := by
  exact (Relation.ReflTransGen.single (critical_seed_step N hN)).trans
    (Relation.ReflTransGen.single (intermediate_step N hN))

theorem critical_to_left (N : ℕ) (hN : 1 ≤ N) :
    Reach N (critical 1 N) (left (N + 1)) :=
  Relation.ReflTransGen.single (critical_newest_step N hN)

theorem left_ne_right (n : ℕ) : left n ≠ right n := by
  intro h
  have hc := congrArg (fun w : Word => w.count .a) h
  simp [count_a_left, count_a_right] at hc

theorem reach_from_normal_eq (h : Normal N w) (hz : Reach N w z) : z = w := by
  exact (Relation.reflTransGen_iff_eq h).mp hz

/-- Global confluence of finite-stage execution. -/
def Confluent (N : ℕ) : Prop :=
  ∀ w u v, Reach N w u → Reach N w v → ∃ z, Reach N u z ∧ Reach N v z

/-- Every nonempty finite completion stage is nonconfluent. -/
theorem finite_stage_not_confluent (N : ℕ) (hN : 1 ≤ N) : ¬ Confluent N := by
  intro hconf
  rcases hconf (critical 1 N) (left (N + 1)) (right (N + 1))
      (critical_to_left N hN) (critical_to_right N hN) with ⟨z, hl, hr⟩
  have hzl : z = left (N + 1) := reach_from_normal_eq (normal_left_succ N) hl
  have hzr : z = right (N + 1) := reach_from_normal_eq (normal_right_succ N) hr
  exact left_ne_right (N + 1) (hzl.symm.trans hzr)

/-- Unoriented semantic equivalence generated by finite-stage execution. -/
abbrev Semantic (N : ℕ) := Relation.EqvGen (Step N)

/-- The missing next rule is already an equality in the old semantic theory. -/
theorem semantic_new_rule (N : ℕ) (hN : 1 ≤ N) :
    Semantic N (left (N + 1)) (right (N + 1)) := by
  exact Relation.EqvGen.trans _ (critical 1 N) _
    (Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ (critical_newest_step N hN)))
    (Relation.EqvGen.trans _ (.b :: left N) _
      (Relation.EqvGen.rel _ _ (critical_seed_step N hN))
      (Relation.EqvGen.rel _ _ (intermediate_step N hN)))

/-- Contextual closure of one executable step. -/
theorem step_in_context (h : Step N u v) (p s : Word) :
    Step N (p ++ u ++ s) (p ++ v ++ s) := by
  rcases h with ⟨n, hn, hN, p₀, s₀, hu, hv⟩
  refine ⟨n, hn, hN, p ++ p₀, s₀ ++ s, ?_, ?_⟩
  · simp [hu, List.append_assoc]
  · simp [hv, List.append_assoc]

/-- Contextual closure of generated semantic equivalence. -/
theorem semantic_in_context (h : Semantic N u v) (p s : Word) :
    Semantic N (p ++ u ++ s) (p ++ v ++ s) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (step_in_context hxy p s)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

theorem step_mono {N M : ℕ} (hNM : N ≤ M) : Step N ≤ Step M := by
  intro u v h
  rcases h with ⟨n, hn, hnN, p, s, hu, hv⟩
  exact ⟨n, hn, hnN.trans hNM, p, s, hu, hv⟩

/-- Every new-stage step was already valid in old-stage semantics. -/
theorem next_step_semantic_old (N : ℕ) (hN : 1 ≤ N) (h : Step (N + 1) u v) :
    Semantic N u v := by
  rcases h with ⟨n, hn, hnNext, p, s, hu, hv⟩
  rcases Nat.lt_or_eq_of_le hnNext with hnOld | hnEq
  · exact Relation.EqvGen.rel _ _ ⟨n, hn, Nat.lt_succ_iff.mp hnOld, p, s, hu, hv⟩
  · subst n
    rw [hu, hv]
    exact semantic_in_context (semantic_new_rule N hN) p s

theorem semantic_next_to_old (N : ℕ) (hN : 1 ≤ N) :
    Semantic (N + 1) ≤ Semantic N := by
  intro u v h
  induction h with
  | rel x y hxy => exact next_step_semantic_old N hN hxy
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

theorem semantic_old_to_next (N : ℕ) : Semantic N ≤ Semantic (N + 1) := by
  exact Relation.EqvGen.mono (step_mono (Nat.le_succ N))

/-- The generated semantic theory is stationary under the executable repair. -/
theorem semantic_succ_eq (N : ℕ) (hN : 1 ≤ N) : Semantic (N + 1) = Semantic N := by
  funext u v
  apply propext
  exact ⟨fun h => semantic_next_to_old N hN u v h,
    fun h => semantic_old_to_next N u v h⟩

/-- The next joining rule is not executable before repair. -/
theorem new_rule_absent (N : ℕ) : ¬ Step N (left (N + 1)) (right (N + 1)) :=
  normal_left_succ N _

/-- The next joining rule is executable after repair. -/
theorem new_rule_present (N : ℕ) : Step (N + 1) (left (N + 1)) (right (N + 1)) := by
  exact ⟨N + 1, by omega, le_rfl, [], [], by simp, by simp⟩

/--
Capstone: terminating execution, nonconfluent finite rulebooks, stationary generated semantics,
strict repair admission, and inherited next-stage failure coexist for every nonempty stage.
-/
theorem endogenous_completion_mechanism (N : ℕ) (hN : 1 ≤ N) :
    WellFounded (fun v u => Step N u v) ∧
    ¬ Confluent N ∧
    Semantic (N + 1) = Semantic N ∧
    ¬ Step N (left (N + 1)) (right (N + 1)) ∧
    Step (N + 1) (left (N + 1)) (right (N + 1)) ∧
    ¬ Confluent (N + 1) := by
  exact ⟨step_wellFounded N, finite_stage_not_confluent N hN,
    semantic_succ_eq N hN, new_rule_absent N, new_rule_present N,
    finite_stage_not_confluent (N + 1) (by omega)⟩

end ConstitutiveCriticalCompletionMechanics
