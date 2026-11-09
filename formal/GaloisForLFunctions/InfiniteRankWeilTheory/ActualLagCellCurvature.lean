import GaloisForLFunctions.InfiniteRankWeilTheory.TrivialZeroSeriesCurvature
import GaloisForLFunctions.InfiniteRankWeilTheory.FiniteJetSublevelCover
import Mathlib.Analysis.Convex.Deriv

/-!+# Arithmetic-cell curvature of the actual Weil lag

Within each integer cell, the scaled lag has an affine arithmetic part. The logarithmic
curvature dominates the complete trivial-zero correction, giving a uniform two-ball sublevel
cover independent of the affine coefficients.
-/

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

open HTGeometry.KleinbockMargulis

/-- The common cell profile, with the affine arithmetic coefficients exposed. -/
def lagCellModel (A B x : ℝ) : ℝ :=
  A * x + B - x * Real.log x + RHTower.trivialZeroSeriesReal x

private def lagCellSlope (A x : ℝ) : ℝ := A - (Real.log x + 1) + trivialZeroSlope x

private def lagCellCurvature (x : ℝ) : ℝ := -x⁻¹ + 1 / (x ^ 2 * (x ^ 2 - 1))

private theorem hasDerivAt_lagCellModel (A B : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (lagCellModel A B) (lagCellSlope A x) x := by
  have h := ((((hasDerivAt_id x).const_mul A).add_const B).sub
    (Real.hasDerivAt_mul_log (zero_lt_one.trans hx).ne')).add (hasDerivAt_trivialZeroSeriesReal hx)
  simpa only [lagCellModel, lagCellSlope, mul_one] using h

private theorem hasDerivAt_lagCellSlope (A : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (lagCellSlope A) (lagCellCurvature x) x := by
  have h := ((hasDerivAt_const x A).sub
    ((Real.hasDerivAt_log (zero_lt_one.trans hx).ne').add_const 1)).add
      (hasDerivAt_trivialZeroSlope hx)
  simpa only [lagCellSlope, lagCellCurvature, zero_sub] using h

private theorem lagCellCurvature_neg {x : ℝ} (hx : 2 ≤ x) : lagCellCurvature x < 0 := by
  have h := half_reciprocal_le_log_sub_trivialZero_curvature hx
  have hpos : 0 < 1 / (2 * x) := by positivity
  dsimp [lagCellCurvature]
  linarith only [h, hpos]

/-- Every arithmetic cell model is strictly concave beyond two, independent of its affine part. -/
theorem strictConcaveOn_lagCellModel (A B : ℝ) :
    StrictConcaveOn ℝ (Ici 2) (lagCellModel A B) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 2)
    (fun x hx => (hasDerivAt_lagCellModel A B (by linarith only [hx])).continuousAt.continuousWithinAt)
  intro x hx
  have hx2 : 2 ≤ x := interior_subset hx
  have hx1 : 1 < x := by linarith only [hx2]
  have heq : deriv (lagCellModel A B) =ᶠ[𝓝 x] lagCellSlope A := by
    filter_upwards [isOpen_Ioi.mem_nhds hx1] with y hy
    exact (hasDerivAt_lagCellModel A B hy).deriv
  have hd := (hasDerivAt_lagCellSlope A hx1).congr_of_eventuallyEq heq
  change deriv (deriv (lagCellModel A B)) x < 0
  rw [hd.deriv]
  exact lagCellCurvature_neg hx2

private def lagCellJet (A B : ℝ) : ℕ → ℝ → ℝ
  | 0 => lagCellModel A B
  | 1 => lagCellSlope A
  | _ + 2 => lagCellCurvature

private theorem isDerivChain_lagCellJet (A B R : ℝ) :
    IsDerivChain 2 (lagCellJet A B) (Icc 2 R) := by
  intro j hj x hx
  have hx1 : 1 < x := by linarith only [hx.1]
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with rfl | rfl
  · exact hasDerivAt_lagCellModel A B hx1
  · exact hasDerivAt_lagCellSlope A hx1

/-- The sublevel set of every cell model has a two-ball cover on `[2,R]`, with a radius
controlled only by `R` and the sublevel threshold. -/
theorem exists_lagCellModel_sublevel_cover (A B : ℝ) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ T : Finset ℝ, T.card ≤ 2 ∧ ∀ x ∈ Icc 2 R, |lagCellModel A B x| < ε →
      ∃ z ∈ T, |x - z| ≤ derivativeCoverConstant 2 (1 / (2 * R)) * ε ^ ((2 : ℝ)⁻¹) := by
  apply exists_sublevel_cover_of_derivative_lower ordConnected_Icc
    (isDerivChain_lagCellJet A B R) (by omega) (by positivity) hε
  intro x hx
  have hx0 : 0 < x := by linarith only [hx.1]
  have hhalf := half_reciprocal_le_log_sub_trivialZero_curvature hx.1
  have hRhalf : 1 / (2 * R) ≤ 1 / (2 * x) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) hx0) (by linarith only [hx.2])
  change 1 / (2 * R) ≤ |lagCellCurvature x|
  rw [abs_of_neg (lagCellCurvature_neg hx.1)]
  dsimp [lagCellCurvature]
  linarith only [hhalf, hRhalf]

/-- The actual lag with its positive square-root factor restored at the arithmetic argument. -/
def scaledActualLag (x : ℝ) : ℝ :=
  Real.exp (Real.log x / 2) * RHTower.weilLagFunctionReal (Real.log x)

/-- On each half-open integer cell, the scaled actual lag equals one affine cell model. -/
theorem scaledActualLag_eq_cellModel {j : ℕ} (hj : 2 ≤ j) {x : ℝ}
    (hx : x ∈ Ico (j : ℝ) ((j : ℝ) + 1)) :
    scaledActualLag x = lagCellModel
      (1 + Real.eulerMascheroniConstant + RHTower.mertensSum j)
      (-Chebyshev.psi (j : ℝ) - Real.log (2 * Real.pi)) x := by
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hx1 : 1 < x := by linarith only [hj2, hx.1]
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hfloor : ⌊x⌋₊ = j := (Nat.floor_eq_iff hx0.le).mpr hx
  have hpsi : Chebyshev.psi x = Chebyshev.psi (j : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, hfloor, Nat.floor_natCast]
  rw [scaledActualLag, RHTower.weilLagFunctionReal_eq_prime_side (Real.log_pos hx1),
    Real.exp_log hx0, hfloor, hpsi, ← mul_assoc, ← Real.exp_add,
    show Real.log x / 2 + -(Real.log x) / 2 = 0 by ring, Real.exp_zero, one_mul]
  dsimp [lagCellModel]
  ring

/-- The scaled actual lag is strictly concave inside every integer cell beyond two. -/
theorem strictConcaveOn_scaledActualLag_cell {j : ℕ} (hj : 2 ≤ j) :
    StrictConcaveOn ℝ (Ico (j : ℝ) ((j : ℝ) + 1)) scaledActualLag := by
  refine ⟨convex_Ico _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have h := (strictConcaveOn_lagCellModel
    (1 + Real.eulerMascheroniConstant + RHTower.mertensSum j)
    (-Chebyshev.psi (j : ℝ) - Real.log (2 * Real.pi))).2
      (hj2.trans hx.1) (hj2.trans hy.1) hxy ha hb hab
  have hmem := (convex_Ico (j : ℝ) ((j : ℝ) + 1)) hx hy ha.le hb.le hab
  rw [scaledActualLag_eq_cellModel hj hx, scaledActualLag_eq_cellModel hj hy,
    scaledActualLag_eq_cellModel hj hmem]
  exact h

/-- No integer cell beyond two contains three distinct zeros of the actual lag. -/
theorem not_three_actualLag_zeros_in_cell {j : ℕ} (hj : 2 ≤ j) {x y z : ℝ}
    (hx : x ∈ Ico (j : ℝ) ((j : ℝ) + 1)) (hz : z ∈ Ico (j : ℝ) ((j : ℝ) + 1))
    (hxy : x < y) (hyz : y < z)
    (hfx : RHTower.weilLagFunctionReal (Real.log x) = 0)
    (hfy : RHTower.weilLagFunctionReal (Real.log y) = 0)
    (hfz : RHTower.weilLagFunctionReal (Real.log z) = 0) : False := by
  let a : ℝ := (z - y) / (z - x)
  let b : ℝ := (y - x) / (z - x)
  have hzx : 0 < z - x := sub_pos.mpr (hxy.trans hyz)
  have ha : 0 < a := div_pos (sub_pos.mpr hyz) hzx
  have hb : 0 < b := div_pos (sub_pos.mpr hxy) hzx
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hmean : a * x + b * z = y := by dsimp [a, b]; field_simp; ring
  have h := (strictConcaveOn_scaledActualLag_cell hj).2 hx hz
    (ne_of_lt (hxy.trans hyz)) ha hb hab
  simp only [smul_eq_mul] at h
  rw [hmean] at h
  simp only [scaledActualLag, hfx, hfy, hfz, mul_zero, add_zero] at h
  exact (lt_irrefl (0 : ℝ)) h

#print axioms exists_lagCellModel_sublevel_cover
#print axioms strictConcaveOn_scaledActualLag_cell
#print axioms not_three_actualLag_zeros_in_cell

end GaloisForLFunctions.InfiniteRankWeilTheory
