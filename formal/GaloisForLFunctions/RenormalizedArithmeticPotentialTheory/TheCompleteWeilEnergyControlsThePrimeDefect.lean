import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionRetainsThePrimeDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossReplacementHasUniformErrors

/-!
# Coercivity of the complete Weil energy throughout strict separation

The exact matrix decomposition retains the prime form, archimedean integral,
and both pole moments. The cross and pole replacements have bounded form
errors. A tunable center estimate leaves a positive prime-defect coefficient
for every width ratio strictly between zero and one.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticLorentzianGeometry ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The literal complete matrix energy in unit atom-mass normalization. -/
def completeWeilEnergy (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, x⟫

private theorem identity_matrix_action {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

/-- Exact complete energy decomposition, including the two signed replacement errors. -/
theorem completeWeilEnergy_eq_decomposition {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hsep : c / N < atomSpacing N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N x = renormalizedPrimeEnergy N x +
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ‖x‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) x, x⟫ -
      ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) x, x⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, x⟫ := by
  rw [completeWeilEnergy, completeWeilMatrix_eq_decomposition hφ hsupp hM hc hN hsep]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_matrix_action, inner_add_left, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, renormalizedPrimeEnergy]
  ring

/-- The actual cross-integral error is uniformly bounded on every horizon vector. -/
theorem abs_fullWeilCrossErrorMatrix_inner_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) x, x⟫| ≤
      (4 * atomCrossErrorConstant φ c * c ^ 2) * ‖x‖ ^ 2 := by
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (atomCrossErrorKernel (atomDilate φ (c / N))) N) x, x⟫| ≤ _
  rw [horizonKernelMatrix_inner, ← sum_primeHorizonExtension_sq]
  exact abs_atomCrossError_quadratic_at_spacing_le hφ hsupp hM hc0 hc1 hN _

/-- Both actual pole moments have a uniformly bounded replacement cost. -/
theorem abs_fullWeilPoleErrorMatrix_inner_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, x⟫| ≤
      (2 * atomPoleMomentErrorConstant φ * c ^ 2) * ‖x‖ ^ 2 := by
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N) x, x⟫| ≤ _
  rw [horizonKernelMatrix_inner, ← sum_primeHorizonExtension_sq]
  exact abs_atomPoleError_quadratic_le hφ hsupp hM hc0 hc1 hN _

/-- Every strictly separated ratio retains a positive fraction of the literal prime defect. -/
theorem eventually_completeWeilEnergy_ge_primeDefect {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ a : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + ((1 - c) / 4) * poleDefect N (primeHorizonExtension x) ≤
        completeWeilEnergy φ c N x := by
  let α := completeWeilPoleShift φ c
  -- This Young parameter leaves a definite part of the defect when the charge is at most c.
  let lam := 2 * c / (1 - c)
  let ε := (1 - c) / 4
  have hε : 0 < ε := div_pos (sub_pos.mpr hc1) (by norm_num)
  have hlam : 0 < lam := div_pos (mul_pos (by norm_num) hc0) (sub_pos.mpr hc1)
  have hα : 0 ≤ α := completeWeilPoleShift_nonneg φ hc0.le
  have hαc : α ≤ c := completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
  have hcoef : α * (1 + 1 / lam) ≤ (1 + c) / 2 := by
    calc
      _ ≤ c * (1 + 1 / lam) := mul_le_mul_of_nonneg_right hαc (by positivity)
      _ = _ := by
        dsimp only [lam]
        field_simp [hc0.ne', (sub_pos.mpr hc1).ne']
        ring
  let a := completeWeilSelfFinitePart φ c - ε - Real.exp (1 / 2) / 2 -
    α * ((1 + lam) * psiConstant + 15) -
    4 * atomCrossErrorConstant φ c * c ^ 2 - 2 * atomPoleMomentErrorConstant φ * c ^ 2
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨a, ?_⟩
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1,
    eventually_div_horizon_lt_atomSpacing hc0 hc1] with N hN hN1 hsep x
  have hp := hN₀ N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hp
  have hcenter := fullWeilCenterMatrix_inner_ge hα hlam hN1 x
  have hcross := (abs_le.mp (abs_fullWeilCrossErrorMatrix_inner_le hφ hsupp hM hc0 hc1 hN1 x)).2
  have hpole := (abs_le.mp (abs_fullWeilPoleErrorMatrix_inner_le hφ hsupp hM hc0 hc1 hN1 x)).1
  have hself := abs_completeWeilSelfError_le hφ hsupp hM hc0 hc1 hN1
  have hself1 : -Real.exp (1 / 2) / 2 ≤ completeWeilSelfError φ c N := by
    have hlarge := mul_le_mul_of_nonneg_left hsep.2.1
      (show 0 ≤ Real.exp (1 / 2) / 2 by positivity)
    have hsmall := (abs_le.mp hself).1
    linarith only [hlarge, hsmall]
  have hselfmass := mul_le_mul_of_nonneg_right hself1 (sq_nonneg ‖x‖)
  have hdefect := mul_le_mul_of_nonneg_right hcoef
    (poleDefect_nonneg N (primeHorizonExtension x))
  rw [completeWeilEnergy_eq_decomposition hφ hsupp hM hc0 hN1 hsep.2.2]
  dsimp only [a, ε] at *
  unfold renormalizedPrimeEnergy
  linarith only [hp, hcenter, hcross, hpole, hselfmass, hdefect]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
