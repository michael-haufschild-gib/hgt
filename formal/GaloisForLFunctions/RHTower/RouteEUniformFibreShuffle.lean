import GaloisForLFunctions.RHTower.RouteEPhysicalFibreCoarea

/-!
# Route E uniform fibre shuffle and admission defect

Every finite equivalence-class shuffle is an exact symmetric bistochastic projection.  Restricting
the state space to an arbitrary nonempty aperture changes the fibres but not these laws.  The file
also isolates the exact scalar cost of comparing a restricted sign mean with its unrestricted
mean.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

section UniformShuffle

variable {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Λ]

/-- Fibre through `x` for a finite label map. -/
def routeEUniformFibre (label : Ω → Λ) (x : Ω) : Finset Ω :=
  Finset.univ.filter fun y => label y = label x

theorem self_mem_routeEUniformFibre (label : Ω → Λ) (x : Ω) :
    x ∈ routeEUniformFibre label x := by
  simp [routeEUniformFibre]

theorem routeEUniformFibre_card_pos (label : Ω → Λ) (x : Ω) :
    0 < (routeEUniformFibre label x).card :=
  Finset.card_pos.mpr ⟨x, self_mem_routeEUniformFibre label x⟩

theorem routeEUniformFibre_eq_of_label_eq (label : Ω → Λ) {x y : Ω}
    (h : label x = label y) :
    routeEUniformFibre label x = routeEUniformFibre label y := by
  unfold routeEUniformFibre
  rw [h]

/-- Uniform resampling inside the finite label fibre. -/
def routeEUniformFibreKernel (label : Ω → Λ) (x y : Ω) : ℝ :=
  if label x = label y then 1 / (routeEUniformFibre label x).card else 0

theorem routeEUniformFibreKernel_nonneg (label : Ω → Λ) (x y : Ω) :
    0 ≤ routeEUniformFibreKernel label x y := by
  unfold routeEUniformFibreKernel
  split_ifs
  · positivity
  · exact le_rfl

theorem routeEUniformFibreKernel_symm (label : Ω → Λ) (x y : Ω) :
    routeEUniformFibreKernel label x y = routeEUniformFibreKernel label y x := by
  classical
  by_cases h : label x = label y
  · unfold routeEUniformFibreKernel
    rw [if_pos h, if_pos h.symm, routeEUniformFibre_eq_of_label_eq label h]
  · unfold routeEUniformFibreKernel
    rw [if_neg h, if_neg (Ne.symm h)]

/-- Exact row stochasticity of uniform class averaging. -/
theorem routeEUniformFibreKernel_row_sum (label : Ω → Λ) (x : Ω) :
    ∑ y, routeEUniformFibreKernel label x y = 1 := by
  classical
  let fibre := routeEUniformFibre label x
  have hcard : ((fibre.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (routeEUniformFibre_card_pos label x)
  calc
    (∑ y, routeEUniformFibreKernel label x y) =
        ∑ y ∈ fibre, (1 : ℝ) / fibre.card := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      unfold routeEUniformFibreKernel fibre routeEUniformFibre
      by_cases h : label x = label y
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    _ = (fibre.card : ℝ) * (1 / fibre.card) := by simp
    _ = 1 := by field_simp

/-- Symmetry upgrades row stochasticity to column stochasticity. -/
theorem routeEUniformFibreKernel_column_sum (label : Ω → Λ) (y : Ω) :
    ∑ x, routeEUniformFibreKernel label x y = 1 := by
  calc
    (∑ x, routeEUniformFibreKernel label x y) =
        ∑ x, routeEUniformFibreKernel label y x := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact routeEUniformFibreKernel_symm label x y
    _ = 1 := routeEUniformFibreKernel_row_sum label y

theorem routeEUniformFibreKernel_eq_of_same_source_label
    (label : Ω → Λ) {x z : Ω} (h : label x = label z) (y : Ω) :
    routeEUniformFibreKernel label z y = routeEUniformFibreKernel label x y := by
  classical
  unfold routeEUniformFibreKernel
  rw [← h, routeEUniformFibre_eq_of_label_eq label h]

/-- Uniform class averaging is an exact projection kernel. -/
theorem routeEUniformFibreKernel_idempotent (label : Ω → Λ) (x y : Ω) :
    ∑ z, routeEUniformFibreKernel label x z * routeEUniformFibreKernel label z y =
      routeEUniformFibreKernel label x y := by
  classical
  calc
    (∑ z, routeEUniformFibreKernel label x z * routeEUniformFibreKernel label z y) =
        ∑ z, routeEUniformFibreKernel label x z * routeEUniformFibreKernel label x y := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases h : label x = label z
      · rw [routeEUniformFibreKernel_eq_of_same_source_label label h y]
      · simp [routeEUniformFibreKernel, h]
    _ = (∑ z, routeEUniformFibreKernel label x z) *
        routeEUniformFibreKernel label x y := by rw [Finset.sum_mul]
    _ = routeEUniformFibreKernel label x y := by
      rw [routeEUniformFibreKernel_row_sum, one_mul]

/-- Column load of a uniform fibre projection is exactly one. -/
theorem routeEUniformFibreKernel_columnLoad_eq_one (label : Ω → Λ) (y : Ω) :
    (∑ x, routeEUniformFibreKernel label x y) = 1 :=
  routeEUniformFibreKernel_column_sum label y

/-- Any weighted edge-gradient energy of the column load vanishes identically. -/
theorem routeEUniformFibreKernel_columnLoadGradient_eq_zero
    (label : Ω → Λ) (edgeWeight : Ω → Ω → ℝ) :
    (∑ x, ∑ y, edgeWeight x y *
      ((∑ z, routeEUniformFibreKernel label z x) -
        ∑ z, routeEUniformFibreKernel label z y) ^ 2) = 0 := by
  simp_rw [routeEUniformFibreKernel_column_sum, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, Finset.sum_const_zero]

/-- Restricting to an arbitrary nonempty aperture simply restricts the label map; the resulting
conditional orbit kernel remains a symmetric bistochastic projection. -/
theorem routeERestrictedUniformFibreKernel_projection
    (label : Ω → Λ) (A : Set Ω) [Nonempty A] :
    (∀ x y : A,
      routeEUniformFibreKernel (fun z : A => label z) x y =
        routeEUniformFibreKernel (fun z : A => label z) y x) ∧
    (∀ x : A, ∑ y, routeEUniformFibreKernel (fun z : A => label z) x y = 1) ∧
    (∀ y : A, ∑ x, routeEUniformFibreKernel (fun z : A => label z) x y = 1) ∧
    (∀ x y : A,
      ∑ z, routeEUniformFibreKernel (fun w : A => label w) x z *
          routeEUniformFibreKernel (fun w : A => label w) z y =
        routeEUniformFibreKernel (fun w : A => label w) x y) := by
  classical
  exact ⟨routeEUniformFibreKernel_symm _, routeEUniformFibreKernel_row_sum _,
    routeEUniformFibreKernel_column_sum _, routeEUniformFibreKernel_idempotent _⟩

end UniformShuffle

/-! ## Exact shell-admission comparison -/

/-- Scalar form of the shell-admission defect. -/
theorem routeE_abs_conditionedMean_sub_totalMean_le_two_rejection
    (thetaGood thetaBad thetaTotal epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hgood : |thetaGood| ≤ 1) (hbad : |thetaBad| ≤ 1)
    (hdecomp : thetaTotal = (1 - epsilon) * thetaGood + epsilon * thetaBad) :
    |thetaGood - thetaTotal| ≤ 2 * epsilon := by
  have hdiff : thetaGood - thetaTotal = epsilon * (thetaGood - thetaBad) := by
    rw [hdecomp]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hepsilon]
  have htriangle : |thetaGood - thetaBad| ≤ |thetaGood| + |thetaBad| := abs_sub _ _
  have : |thetaGood - thetaBad| ≤ 2 := by linarith
  exact mul_le_mul_of_nonneg_left this hepsilon

/-- Squared admission comparison used cellwise in conditional parity ANOVA. -/
theorem routeE_conditionedMean_sq_le_totalMean_sq_add_rejection_sq
    (thetaGood thetaTotal epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hdefect : |thetaGood - thetaTotal| ≤ 2 * epsilon) :
    thetaGood ^ 2 ≤ 2 * thetaTotal ^ 2 + 8 * epsilon ^ 2 := by
  have hlower := (abs_le.mp hdefect).1
  have hupper := (abs_le.mp hdefect).2
  nlinarith [sq_nonneg (thetaGood - 2 * thetaTotal),
    sq_nonneg (thetaGood + 2 * thetaTotal)]

/-- Weighted finite shell-admission comparison, exactly summable over orbit cells. -/
theorem routeE_weightedConditionalParityEnergy_le_admission
    {O : Type*} [Fintype O]
    (mass thetaGood thetaTotal epsilon : O → ℝ)
    (hmass : ∀ o, 0 ≤ mass o) (hepsilon : ∀ o, 0 ≤ epsilon o)
    (hdefect : ∀ o, |thetaGood o - thetaTotal o| ≤ 2 * epsilon o) :
    (∑ o, mass o * thetaGood o ^ 2) ≤
      2 * ∑ o, mass o * thetaTotal o ^ 2 +
        8 * ∑ o, mass o * epsilon o ^ 2 := by
  calc
    (∑ o, mass o * thetaGood o ^ 2) ≤
        ∑ o, mass o * (2 * thetaTotal o ^ 2 + 8 * epsilon o ^ 2) := by
      apply Finset.sum_le_sum
      intro o _ho
      exact mul_le_mul_of_nonneg_left
        (routeE_conditionedMean_sq_le_totalMean_sq_add_rejection_sq
          (thetaGood o) (thetaTotal o) (epsilon o) (hepsilon o) (hdefect o)) (hmass o)
    _ = 2 * ∑ o, mass o * thetaTotal o ^ 2 +
        8 * ∑ o, mass o * epsilon o ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

end

end RHTower
