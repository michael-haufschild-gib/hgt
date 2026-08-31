import Mathlib

/-!
# Topologically admitted Hahn-label mechanics

Finite unconditional core of ULF-TAFM-6. A binary source carries a canonical Hahn sign label.
Decision-current deficit is exactly half its weighted `L¹` label error. Finite observers and
stochastic formation channels preserve current under pullback; canonical target labels realize
exact total-variation loss, and observer deficits telescope without sections.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/hahn-label-approximation-spectrum-observer-deficit-and-tensor-convergence-law.md`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A soft binary label, with its range enforced by the type. -/
abbrev SoftLabel (X : Type*) := X → Set.Icc (-1 : ℝ) 1

/-- Canonical Hahn sign, with the zero value fixed to the positive side. -/
def hahnSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

@[simp] theorem hahnSign_of_nonneg {r : ℝ} (hr : 0 ≤ r) : hahnSign r = 1 := by
  simp [hahnSign, hr]

@[simp] theorem hahnSign_of_neg {r : ℝ} (hr : r < 0) : hahnSign r = -1 := by
  simp [hahnSign, not_le.mpr hr]

theorem hahnSign_mem_Icc (r : ℝ) : hahnSign r ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases hr : 0 ≤ r
  · simp [hahnSign, hr]
  · simp [hahnSign, hr]

/-- Pointwise binary Bayes-regret/Hahn-label identity. -/
theorem hahn_regret_pointwise (r : ℝ) (g : Set.Icc (-1 : ℝ) 1) :
    |r| - (g : ℝ) * r = |(g : ℝ) - hahnSign r| * |r| := by
  by_cases hr : 0 ≤ r
  · rw [hahnSign_of_nonneg hr, abs_of_nonneg hr]
    have hg : (g : ℝ) - 1 ≤ 0 := sub_nonpos.mpr g.2.2
    rw [abs_of_nonpos hg]
    ring
  · have hr' : r < 0 := lt_of_not_ge hr
    rw [hahnSign_of_neg hr', abs_of_neg hr']
    have hg : 0 ≤ (g : ℝ) - -1 := by linarith [g.2.1]
    rw [abs_of_nonneg hg]
    ring

/-- Finite binary source experiment. Probability normalization is stored in the object. -/
structure FiniteBinaryExperiment (X : Type*) [Fintype X] where
  law₀ : X → ℝ
  law₁ : X → ℝ
  law₀_nonneg : ∀ x, 0 ≤ law₀ x
  law₁_nonneg : ∀ x, 0 ≤ law₁ x
  law₀_sum : ∑ x, law₀ x = 1
  law₁_sum : ∑ x, law₁ x = 1

namespace FiniteBinaryExperiment

variable {X : Type*} [Fintype X]

/-- Signed decision current. -/
def current (E : FiniteBinaryExperiment X) (x : X) : ℝ := E.law₁ x - E.law₀ x

theorem sum_current (E : FiniteBinaryExperiment X) : ∑ x, E.current x = 0 := by
  simp only [current, Finset.sum_sub_distrib, E.law₁_sum, E.law₀_sum, sub_self]

/-- Probability-normalized total variation. -/
def tv (E : FiniteBinaryExperiment X) : ℝ := (1 / 2 : ℝ) * ∑ x, |E.current x|

/-- Current extracted by a soft label. -/
def decisionCurrent (E : FiniteBinaryExperiment X) (g : SoftLabel X) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, (g x : ℝ) * E.current x

/-- Weighted approximation error to the canonical Hahn label. -/
def labelError (E : FiniteBinaryExperiment X) (g : SoftLabel X) : ℝ :=
  ∑ x, |(g x : ℝ) - hahnSign (E.current x)| * |E.current x|

/-- Exact source-native conservation law: decision deficit equals half Hahn-label error. -/
theorem tv_sub_decisionCurrent_eq_half_labelError
    (E : FiniteBinaryExperiment X) (g : SoftLabel X) :
    E.tv - E.decisionCurrent g = (1 / 2 : ℝ) * E.labelError g := by
  rw [tv, decisionCurrent, labelError, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact hahn_regret_pointwise (E.current x) (g x)

theorem hahnSign_mul_self (r : ℝ) : hahnSign r * r = |r| := by
  by_cases hr : 0 ≤ r
  · rw [hahnSign_of_nonneg hr, one_mul, abs_of_nonneg hr]
  · have hr' : r < 0 := lt_of_not_ge hr
    rw [hahnSign_of_neg hr', neg_one_mul, abs_of_neg hr']

/-- The canonical soft label of a finite experiment. -/
def canonicalLabel (E : FiniteBinaryExperiment X) : SoftLabel X :=
  fun x => ⟨hahnSign (E.current x), hahnSign_mem_Icc _⟩

theorem decisionCurrent_canonicalLabel (E : FiniteBinaryExperiment X) :
    E.decisionCurrent E.canonicalLabel = E.tv := by
  rw [decisionCurrent, tv]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact hahnSign_mul_self (E.current x)

theorem decisionCurrent_le_tv (E : FiniteBinaryExperiment X) (g : SoftLabel X) :
    E.decisionCurrent g ≤ E.tv := by
  rw [← sub_nonneg]
  rw [tv_sub_decisionCurrent_eq_half_labelError]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Push a finite binary experiment through a finite observer. -/
def observe {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X) (π : X → Q) :
    FiniteBinaryExperiment Q := by
  refine
    { law₀ := fun q => ∑ x ∈ Finset.univ with π x = q, E.law₀ x
      law₁ := fun q => ∑ x ∈ Finset.univ with π x = q, E.law₁ x
      law₀_nonneg := ?_
      law₁_nonneg := ?_
      law₀_sum := ?_
      law₁_sum := ?_ }
  · intro q
    exact Finset.sum_nonneg fun x _ => E.law₀_nonneg x
  · intro q
    exact Finset.sum_nonneg fun x _ => E.law₁_nonneg x
  · rw [Finset.sum_fiberwise Finset.univ π E.law₀, E.law₀_sum]
  · rw [Finset.sum_fiberwise Finset.univ π E.law₁, E.law₁_sum]

theorem observe_current {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X)
    (π : X → Q) (q : Q) :
    (E.observe π).current q = ∑ x ∈ Finset.univ with π x = q, E.current x := by
  simp only [current, observe, Finset.sum_sub_distrib]

/-- Pull a target soft label back through an observer. -/
def pullLabel {Q : Type*} (π : X → Q) (g : SoftLabel Q) : SoftLabel X :=
  fun x => g (π x)

/-- Exact current conservation through an arbitrary finite observer. -/
theorem decisionCurrent_pullLabel {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X) (π : X → Q) (g : SoftLabel Q) :
    E.decisionCurrent (pullLabel π g) = (E.observe π).decisionCurrent g := by
  rw [decisionCurrent, decisionCurrent]
  congr 1
  calc
    ∑ x, ((pullLabel π g) x : ℝ) * E.current x =
        ∑ q, ∑ x ∈ Finset.univ with π x = q,
          ((pullLabel π g) x : ℝ) * E.current x := by
            rw [Finset.sum_fiberwise Finset.univ π]
    _ = ∑ q, (g q : ℝ) * ∑ x ∈ Finset.univ with π x = q, E.current x := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hπ : π x = q := (Finset.mem_filter.mp hx).2
      simp only [pullLabel, hπ]
    _ = ∑ q, (g q : ℝ) * (E.observe π).current q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [observe_current]

/-- Canonical observer label realizes exactly the total-variation visible to that observer. -/
theorem decisionCurrent_pull_observerCanonicalLabel {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X) (π : X → Q) :
    E.decisionCurrent (pullLabel π (E.observe π).canonicalLabel) = (E.observe π).tv := by
  rw [decisionCurrent_pullLabel, decisionCurrent_canonicalLabel]

/-- Exact observer deficit: canonical lifted label error equals twice lost total variation. -/
theorem half_labelError_pull_observerCanonicalLabel {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X) (π : X → Q) :
    (1 / 2 : ℝ) * E.labelError (pullLabel π (E.observe π).canonicalLabel) =
      E.tv - (E.observe π).tv := by
  rw [← tv_sub_decisionCurrent_eq_half_labelError,
    decisionCurrent_pull_observerCanonicalLabel]

/-- Every observer-measurable label pays at least the intrinsic observer deficit. -/
theorem observerDeficit_le_half_labelError_pull {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X) (π : X → Q) (g : SoftLabel Q) :
    E.tv - (E.observe π).tv ≤ (1 / 2 : ℝ) * E.labelError (pullLabel π g) := by
  rw [← tv_sub_decisionCurrent_eq_half_labelError, decisionCurrent_pullLabel]
  linarith [decisionCurrent_le_tv (E.observe π) g]

/-- Intrinsic information deficit of a finite observer. -/
def observerDeficit {Q : Type*} [Fintype Q] [DecidableEq Q]
    (E : FiniteBinaryExperiment X) (π : X → Q) : ℝ :=
  E.tv - (E.observe π).tv

/-- Section-free serial observer conservation. -/
theorem observerDeficit_serial {Q R : Type*} [Fintype Q] [Fintype R]
    [DecidableEq Q] [DecidableEq R]
    (E : FiniteBinaryExperiment X) (π : X → Q) (ρ : Q → R) :
    E.tv - ((E.observe π).observe ρ).tv =
      E.observerDeficit π + (E.observe π).observerDeficit ρ := by
  simp only [observerDeficit]
  ring

end FiniteBinaryExperiment

/-- Finite stochastic formation channel. -/
structure FiniteChannel (X Y : Type*) [Fintype Y] where
  weight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ weight x y
  row_sum : ∀ x, ∑ y, weight x y = 1

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Push a finite binary experiment through a stochastic channel. -/
def push (K : FiniteChannel X Y) (E : FiniteBinaryExperiment X) :
    FiniteBinaryExperiment Y := by
  refine
    { law₀ := fun y => ∑ x, E.law₀ x * K.weight x y
      law₁ := fun y => ∑ x, E.law₁ x * K.weight x y
      law₀_nonneg := ?_
      law₁_nonneg := ?_
      law₀_sum := ?_
      law₁_sum := ?_ }
  · intro y
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (E.law₀_nonneg x) (K.weight_nonneg x y)
  · intro y
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (E.law₁_nonneg x) (K.weight_nonneg x y)
  · calc
      ∑ y, ∑ x, E.law₀ x * K.weight x y =
          ∑ x, ∑ y, E.law₀ x * K.weight x y := Finset.sum_comm
      _ = ∑ x, E.law₀ x * ∑ y, K.weight x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = 1 := by simp only [K.row_sum, mul_one, E.law₀_sum]
  · calc
      ∑ y, ∑ x, E.law₁ x * K.weight x y =
          ∑ x, ∑ y, E.law₁ x * K.weight x y := Finset.sum_comm
      _ = ∑ x, E.law₁ x * ∑ y, K.weight x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = 1 := by simp only [K.row_sum, mul_one, E.law₁_sum]

theorem push_current (K : FiniteChannel X Y) (E : FiniteBinaryExperiment X) (y : Y) :
    (K.push E).current y = ∑ x, E.current x * K.weight x y := by
  simp only [FiniteBinaryExperiment.current, push, Finset.sum_sub_distrib, sub_mul]

/-- Pull a bounded soft detector through a stochastic channel. -/
def pullSoftLabel (K : FiniteChannel X Y) (g : SoftLabel Y) : SoftLabel X := fun x => by
  refine ⟨∑ y, K.weight x y * (g y : ℝ), ?_⟩
  constructor
  · calc
      (-1 : ℝ) = ∑ y, K.weight x y * (-1 : ℝ) := by
        rw [← Finset.sum_mul, K.row_sum]
        norm_num
      _ ≤ ∑ y, K.weight x y * (g y : ℝ) := by
        exact Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (g y).2.1 (K.weight_nonneg x y)
  · calc
      ∑ y, K.weight x y * (g y : ℝ) ≤ ∑ y, K.weight x y * (1 : ℝ) := by
        exact Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (g y).2.2 (K.weight_nonneg x y)
      _ = 1 := by
        rw [← Finset.sum_mul, K.row_sum]
        norm_num

/-- Common recovery kernel is information-neutral: pulled detector current equals target current. -/
theorem decisionCurrent_pullSoftLabel (K : FiniteChannel X Y)
    (E : FiniteBinaryExperiment X) (g : SoftLabel Y) :
    E.decisionCurrent (K.pullSoftLabel g) = (K.push E).decisionCurrent g := by
  rw [FiniteBinaryExperiment.decisionCurrent, FiniteBinaryExperiment.decisionCurrent]
  congr 1
  simp only [pullSoftLabel, push_current]
  calc
    ∑ x, (∑ y, K.weight x y * (g y : ℝ)) * E.current x =
        ∑ x, ∑ y, (g y : ℝ) * (E.current x * K.weight x y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ y, ∑ x, (g y : ℝ) * (E.current x * K.weight x y) := Finset.sum_comm
    _ = ∑ y, (g y : ℝ) * ∑ x, E.current x * K.weight x y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]

/-- Exact formation-to-label law for the target's canonical Neyman--Pearson detector. -/
theorem half_labelError_pull_targetCanonicalLabel (K : FiniteChannel X Y)
    (E : FiniteBinaryExperiment X) :
    (1 / 2 : ℝ) * E.labelError (K.pullSoftLabel (K.push E).canonicalLabel) =
      E.tv - (K.push E).tv := by
  rw [← FiniteBinaryExperiment.tv_sub_decisionCurrent_eq_half_labelError,
    decisionCurrent_pullSoftLabel, FiniteBinaryExperiment.decisionCurrent_canonicalLabel]

end FiniteChannel

end

end GaloisForLFunctions.HTGeometry
