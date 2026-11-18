import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SplineSampling
import GaloisForLFunctions.SignedWindowCriticality.TheContinuumCanonicalSystemIsTheJetHankelSystem

/-!
# Higher differences of the ordinary-prime spline

The third forward difference of the full dyadic spline on square mesh
is O(n⁻⁷). The mean value formula samples its bounded third derivative
between the two mesh endpoints.
-/

noncomputable section
open Filter Topology
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.ArithmeticWeightTheory GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge RHTower.WeilDeletion
open GaloisForLFunctions.SignedWindowCriticality
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem profile_zero {x : ℝ}
    (hx : x ∉ Set.Icc (Real.exp (-8)) (Real.exp (8+Real.log 4))) : dyadicSpline x=0 := by
  by_cases hp : 0<x
  · simp only [dyadicSpline,if_pos hp,squarePrimeWeight_zero_outside hp hx,Complex.zero_re,mul_zero]
  · exact if_neg hp

private theorem profile_cubic : ContDiff ℝ 3 dyadicSpline := by
  have hA : ContDiff ℝ 3 splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact (contDiff_upow one_pos 6).of_le (by norm_num)
  have hF : ContDiff ℝ 3 squareLogProfile :=
    (contDiff_const.mul hA).sub (hA.comp (contDiff_id.sub contDiff_const))
  apply contDiff_iff_contDiffAt.mpr; intro x
  by_cases hx : 0<x
  · have hl := (Real.contDiffAt_log (n := 3)).mpr hx.ne'
    have he : ContDiffAt ℝ 3 (fun v : ℝ =>
        2*(Real.exp (-Real.log v/2)*squareLogProfile (Real.log v))) x := by fun_prop
    apply he.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with v hv
    simp only [dyadicSpline,if_pos hv,squarePrimeWeight,Complex.ofReal_re]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with v hv
    exact profile_zero (fun h => hv.not_ge h.1)

/-- Forward decrease on the integer horizon. -/
def horizonDifference (f : ℕ → ℝ) (k : ℕ) := f k-f (k+1)

/-- The third signed horizon difference costs seven powers of the square
conductor parameter. -/
theorem sampledSpline_third_difference :
    ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n → ∀ k : ℕ,
      |horizonDifference (horizonDifference (horizonDifference (sampledSpline n))) k| ≤ C/(n:ℝ)^7 := by
  have hs : HasCompactSupport dyadicSpline := HasCompactSupport.intro isCompact_Icc (fun _ h => profile_zero h)
  have hs₃ : HasCompactSupport (iteratedDeriv 3 dyadicSpline) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hs.deriv.deriv.deriv
  obtain ⟨C,hC⟩ := hs₃.exists_bound_of_continuous (profile_cubic.continuous_iteratedDeriv 3 le_rfl)
  refine ⟨C,(norm_nonneg _).trans (hC 0),fun {n} hn k => ?_⟩
  let h := ((n:ℝ)^2)⁻¹
  let x := (k:ℝ)/(n:ℝ)^2
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hh : 0<h := inv_pos.mpr (sq_pos_of_pos hn')
  obtain ⟨ξ,_,he⟩ := exists_fwdDiff_iter_eq 3 profile_cubic hh x
  have hb : |(fwdDiff h)^[3] dyadicSpline x| ≤ h^3*C := by
    rw [he,abs_mul,abs_of_nonneg (pow_nonneg hh.le 3)]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hC ξ) (pow_nonneg hh.le 3)
  have e₁ : ((k+1:ℕ):ℝ)/(n:ℝ)^2=x+h := by dsimp [x,h]; push_cast; ring
  have e₂ : ((k+1+1:ℕ):ℝ)/(n:ℝ)^2=x+h+h := by dsimp [x,h]; push_cast; ring
  have e₃ : ((k+1+1+1:ℕ):ℝ)/(n:ℝ)^2=x+h+h+h := by dsimp [x,h]; push_cast; ring
  have hid : horizonDifference (horizonDifference (horizonDifference (sampledSpline n))) k =
      -((fwdDiff h)^[3] dyadicSpline x)/n := by
    simp only [horizonDifference,sampledSpline,e₁,e₂,e₃]
    change _ = -(((dyadicSpline (x+h+h+h)-dyadicSpline (x+h+h))-
      (dyadicSpline (x+h+h)-dyadicSpline (x+h)))-
      ((dyadicSpline (x+h+h)-dyadicSpline (x+h))-(dyadicSpline (x+h)-dyadicSpline x)))/n
    dsimp only [x]
    ring
  rw [hid,abs_div,abs_neg,abs_of_pos hn']
  exact (div_le_div_of_nonneg_right hb hn'.le).trans_eq (by dsimp [h]; ring)

#print axioms sampledSpline_third_difference
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
