import Mathlib

/-!
# The discounted first-entrance potential of a finite chain

For a stochastic matrix, a target set and a discount `0 < a < 1`, the map that fixes the value one
on the target and averages the discounted values elsewhere is an `a`-contraction of the sup norm.
Its unique fixed point is the discounted first-entrance potential: it is one on the target, lies
between zero and one everywhere, and its discounted charge `q = h - aPh` vanishes off the target
and lies between `1-a` and `1` on it.

Those four properties are exactly what a capacitary estimate consumes; no path space, hitting time
or strong Markov property is needed to produce them.
-/

open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Potential

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The discounted first-entrance operator of a target set. -/
def hittingMap (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (f : X → ℝ) : X → ℝ :=
  fun x => if x ∈ A then 1 else a * ∑ y, P x y * f y

theorem hittingMap_apply_mem {P : Matrix X X ℝ} {A : Finset X} {a : ℝ} (f : X → ℝ) {x : X}
    (hx : x ∈ A) : hittingMap P A a f x = 1 := by
  rw [hittingMap, if_pos hx]

theorem hittingMap_apply_notMem {P : Matrix X X ℝ} {A : Finset X} {a : ℝ} (f : X → ℝ) {x : X}
    (hx : x ∉ A) : hittingMap P A a f x = a * ∑ y, P x y * f y := by
  rw [hittingMap, if_neg hx]

/-- **The discounted operator is an `a`-contraction of the sup norm.** -/
theorem lipschitzWith_hittingMap {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 ≤ a) :
    LipschitzWith ⟨a, ha⟩ (hittingMap P A a) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro x
  by_cases hx : x ∈ A
  · rw [hittingMap_apply_mem f hx, hittingMap_apply_mem g hx]
    simp only [dist_self]
    positivity
  · rw [hittingMap_apply_notMem f hx, hittingMap_apply_notMem g hx, Real.dist_eq, ← mul_sub,
      abs_mul, abs_of_nonneg ha, ← Finset.sum_sub_distrib]
    have hterm : ∀ y, |P x y * f y - P x y * g y| ≤ P x y * dist f g := by
      intro y
      rw [← mul_sub, abs_mul, abs_of_nonneg (hP x y)]
      exact mul_le_mul_of_nonneg_left (by
        rw [← Real.dist_eq]
        exact dist_le_pi_dist f g y) (hP x y)
    have hbound : |∑ y, (P x y * f y - P x y * g y)| ≤ dist f g := by
      calc |∑ y, (P x y * f y - P x y * g y)| ≤ ∑ y, |P x y * f y - P x y * g y| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, P x y * dist f g := Finset.sum_le_sum fun y _ => hterm y
        _ = dist f g := by rw [← Finset.sum_mul, hrow x, one_mul]
    calc a * |∑ y, (P x y * f y - P x y * g y)| ≤ a * dist f g :=
          mul_le_mul_of_nonneg_left hbound ha
      _ = ↑(⟨a, ha⟩ : ℝ≥0) * dist f g := by norm_num

/-- The discounted operator contracts. -/
theorem hittingContracting (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) :
    ContractingWith ⟨a, ha⟩ (hittingMap P A a) :=
  ⟨by exact_mod_cast ha1, lipschitzWith_hittingMap hP hrow ha⟩

/-- The discounted first-entrance potential: the unique fixed point of the discounted operator. -/
def hittingPotential (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) : X → ℝ :=
  ContractingWith.fixedPoint (hittingMap P A a) (hittingContracting P A a hP hrow ha ha1)

theorem hittingPotential_fixed (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) :
    hittingMap P A a (hittingPotential P A a hP hrow ha ha1)
      = hittingPotential P A a hP hrow ha ha1 :=
  ContractingWith.fixedPoint_isFixedPt (hittingContracting P A a hP hrow ha ha1)

theorem hittingPotential_eq_one {P : Matrix X X ℝ} {A : Finset X} {a : ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) {x : X} (hx : x ∈ A) :
    hittingPotential P A a hP hrow ha ha1 x = 1 := by
  conv_lhs => rw [← hittingPotential_fixed P A a hP hrow ha ha1]
  exact hittingMap_apply_mem _ hx

/-- The potential takes values in the unit interval. -/
theorem hittingPotential_mem_unitInterval {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) (x : X) :
    0 ≤ hittingPotential P A a hP hrow ha ha1 x ∧ hittingPotential P A a hP hrow ha ha1 x ≤ 1 := by
  classical
  have C : ContractingWith ⟨a, ha⟩ (hittingMap P A a) := hittingContracting P A a hP hrow ha ha1
  set S : Set (X → ℝ) := {f | ∀ y, 0 ≤ f y ∧ f y ≤ 1} with hS
  have hclosed : IsClosed S := by
    have : S = ⋂ y : X, {f : X → ℝ | 0 ≤ f y} ∩ {f : X → ℝ | f y ≤ 1} := by
      ext f
      simp [hS, Set.mem_iInter]
    rw [this]
    refine isClosed_iInter fun y => IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const (continuous_apply y)
    · exact isClosed_le (continuous_apply y) continuous_const
  have hinv : ∀ f ∈ S, hittingMap P A a f ∈ S := by
    intro f hf y
    by_cases hy : y ∈ A
    · rw [hittingMap_apply_mem f hy]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [hittingMap_apply_notMem f hy]
      have hnn : 0 ≤ ∑ z, P y z * f z :=
        Finset.sum_nonneg fun z _ => mul_nonneg (hP y z) (hf z).1
      have hle : ∑ z, P y z * f z ≤ 1 := by
        calc ∑ z, P y z * f z ≤ ∑ z, P y z * 1 :=
              Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hf z).2 (hP y z)
          _ = 1 := by rw [← Finset.sum_mul, hrow y, one_mul]
      constructor
      · positivity
      · nlinarith [ha, ha1, hnn, hle]
  have hzero : (fun _ : X => (0 : ℝ)) ∈ S := fun y => ⟨le_rfl, zero_le_one⟩
  have hiter : ∀ n : ℕ, (hittingMap P A a)^[n] (fun _ : X => (0 : ℝ)) ∈ S := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hinv _ ih
  have htend := ContractingWith.tendsto_iterate_fixedPoint
    (hittingContracting P A a hP hrow ha ha1) (fun _ : X => (0 : ℝ))
  have hmem : hittingPotential P A a hP hrow ha ha1 ∈ S :=
    hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hiter)
  exact hmem x

/-- **The discounted charge vanishes off the target.** -/
theorem charge_eq_zero_of_notMem {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) {x : X}
    (hx : x ∉ A) :
    hittingPotential P A a hP hrow ha ha1 x
        - a * ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y = 0 := by
  conv_lhs => rw [← hittingPotential_fixed P A a hP hrow ha ha1]
  rw [hittingMap_apply_notMem _ hx, hittingPotential_fixed P A a hP hrow ha ha1, sub_self]

/-- **The discounted charge is between `1-a` and `1` on the target.** -/
theorem charge_bounds_of_mem {P : Matrix X X ℝ} {A : Finset X} {a : ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) {x : X} (hx : x ∈ A) :
    1 - a ≤ hittingPotential P A a hP hrow ha ha1 x
        - a * ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ∧
      hittingPotential P A a hP hrow ha ha1 x
        - a * ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤ 1 := by
  have hone := hittingPotential_eq_one hP hrow ha ha1 hx
  have hnn : 0 ≤ ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y :=
    Finset.sum_nonneg fun y _ =>
      mul_nonneg (hP x y) (hittingPotential_mem_unitInterval hP hrow ha ha1 y).1
  have hle : ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤ 1 := by
    calc ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤ ∑ y, P x y * 1 :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hittingPotential_mem_unitInterval hP hrow ha ha1 y).2
              (hP x y)
      _ = 1 := by rw [← Finset.sum_mul, hrow x, one_mul]
  rw [hone]
  constructor
  · nlinarith
  · nlinarith

end Potential

end

end GaloisForLFunctions.HTGeometry
