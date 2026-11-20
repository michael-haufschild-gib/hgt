import GaloisForLFunctions.goldbach.LiLiu.Mellin.CharacterMoment
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DiagonalInversion
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DoubleModel
import GaloisForLFunctions.goldbach.LiLiu.Boundary.KernelDecay

/-! # The exact signed arithmetic residual on a Mellin product contour -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

private def diagonalTestKernel (N : ℕ) (φ : TestWeight) (a : ℝ) (p : ℝ × ℝ) : ℂ :=
  let s := mellinLine a p.1
  let z := mellinLine a p.2
  (mellinMultiplier N φ s * conj (mellinMultiplier N φ z)) * diagonalSeries N (s+conj z)

private theorem diagonalTestKernel_integrable {N : ℕ} (hN : 0 < N) (φ : TestWeight) {a : ℝ} (ha : 0 < a) :
    Integrable (diagonalTestKernel N φ a) := by
  obtain ⟨D,hD,hd⟩ := diagonalSeries_halfPlane_bound N (a := 2*a) (by positivity)
  let s := mellinLine a
  let V := fun t => mellinMultiplier N φ (s t)
  let w := fun p : ℝ × ℝ => s p.1 + conj (s p.2)
  have hline : Continuous (mellinLine a) := by unfold mellinLine; fun_prop
  have hw : Continuous w := (hline.comp continuous_fst).add (continuous_conj.comp (hline.comp continuous_snd))
  have hre (p : ℝ × ℝ) : (w p).re=2*a := by simp [w,s,mellinLine,two_mul]
  have hD' : Continuous (fun p => diagonalSeries N (w p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : 0 < (w p).re := by rw [hre]; positivity
    exact (diagonalSeries_differentiableAt N hp).continuousAt.comp (f := w) hw.continuousAt
  have hv : Continuous V := (mellinMultiplier_continuous N hN φ).comp hline
  have hv' := (mellinMultiplier_integrable N hN φ a).norm
  apply ((hv'.mul_prod hv').const_mul D).mono'
    (((hv.comp continuous_fst).mul (continuous_conj.comp (hv.comp continuous_snd))).mul hD').aestronglyMeasurable
  filter_upwards with p
  change ‖(V p.1 * conj (V p.2))* diagonalSeries N (w p)‖ ≤ D * (‖V p.1‖ * ‖V p.2‖)
  rw [norm_mul,norm_mul,RCLike.norm_conj,mul_comm D]
  exact mul_le_mul_of_nonneg_left (hd _ (hre p).ge) (by positivity)

/-- Exact signed contour identity. Each of the three product integrals converges absolutely. -/
theorem residual_contour_integral {k : ℕ} (hN : 4 ≤ k+2) (φ : TestWeight) (hg : modulusGRH (k+2))
    {a : ℝ} (ha : 0 < a) (ht : a ≤ 1/8) :
    (1/(2*Real.pi):ℂ)^2 * (∫ x : ℝ, ∫ y : ℝ, (mellinMultiplier (k+2) φ (mellinLine a x) *
        conj (mellinMultiplier (k+2) φ (mellinLine a y))) *
        residualKernel (k+2) (mellinLine a x) (mellinLine a y)) =
      ((φ.mass * singularSeries (k+2) - correlation φ (k+2) : ℝ) : ℂ) := by
  let N := k+2
  let C := characterTestKernel N φ a
  let D := diagonalTestKernel N φ a
  let B := modelTestKernel N φ a
  let c := (1/(2*Real.pi):ℂ)
  obtain ⟨hC,hCE⟩ := characterMoment_integral (n := k+1) φ hg ha (by linarith only [ht])
  have hD := diagonalTestKernel_integrable (N := N) (by dsimp [N]; omega) φ ha
  have hB := modelTestKernel_integrable hN φ ha ht
  have hDE : c^2 * (∫ p, D p) = (diagonal φ N : ℂ) := by
    simpa only [c,D,diagonalTestKernel,mul_comm (diagonalSeries _ _)] using diagonal_mellin_evaluation N φ ha
  have hBE := doubleModel_integral hN φ ha ht
  have hrs (x y : ℝ) : (mellinMultiplier N φ (mellinLine a x) *
      conj (mellinMultiplier N φ (mellinLine a y))) * residualKernel N (mellinLine a x) (mellinLine a y) =
      C (x,y)-D (x,y)-B (x,y) := by
    dsimp [residualKernel,C,D,B,characterTestKernel,diagonalTestKernel,modelTestKernel]
    ring
  change Integrable C at hC
  change Integrable D at hD
  change Integrable B at hB
  change c^2 * (∫ p, C p) = _ at hCE
  change c^2 * (∫ p, B p) = _ at hBE
  have hCD : Integrable (fun p => C p-D p) := hC.sub hD
  have hCDB : Integrable (fun p => C p-D p-B p) := hCD.sub hB
  have hpair : (∫ p : ℝ × ℝ, C p-D p-B p) = ∫ x : ℝ, ∫ y : ℝ, C (x,y)-D (x,y)-B (x,y) :=
    integral_prod _ hCDB
  change c^2 * (∫ x : ℝ, ∫ y : ℝ, (mellinMultiplier N φ (mellinLine a x) *
    conj (mellinMultiplier N φ (mellinLine a y))) * residualKernel N (mellinLine a x) (mellinLine a y)) = _
  simp_rw [hrs]
  rw [← hpair,integral_sub hCD hB,integral_sub hC hD,mul_sub,mul_sub,hCE,hDE,hBE]
  dsimp only [N]
  rw [correlation_eq_diagonal_sub_oddMoment]
  push_cast
  ring

#print axioms residual_contour_integral
end
end GaloisForLFunctions.Goldbach.LiLiu
