import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DoublyLogarithmicVisibilityAndExcludedDepthLaw
import GaloisForLFunctions.DilutionCrystallizationPincer.ArchimedeanDominationOfDilutedVisibility

/-!
# Archimedean domination is blind at every depth

At height `ξ`, archimedean domination (`zetaZeroConfig_re_W_heightShift_pos_of_dominance`) proves Weil
positivity of tests of aperture `a` once

  `horizonExponent(e^{2a}) + 2 S_{½}(a) < log(1 + π|ξ|/4)`,  `S_δ(a) = sinh(2δa)/(2δ) − a`,

that is `10 + 68e^a + 2(sinh a − a) < log(1 + π|ξ|/4)`.  The pair energy `S_{½}` is the energy of an
off-line pair at the boundary depth `½`.

**Theorem** (`hodgeDefectAt_isolatedPair_eq_zero_of_dominance`).  For `ξ ≥ e^{100}`, every aperture `a`
in this range and every depth `δ ∈ (0, ½]`, the isolated off-line pair at depth `δ` and height `ξ`
in an on-line background of Riemann–von Mangoldt density `L = (1/2π) log(ξ/2π)`
(`isolatedPairConfig`) has Hodge defect `0` at aperture `a`: it passes every test of aperture `a`.

So the tests that domination certifies at height `ξ` cannot tell `ζ` from a configuration carrying
an off-line pair of any depth at that height.  The isolated pair is visible exactly when
`S_δ(a) > L` (`hodgeDefectAt_isolatedPair`); `S_δ(a) ≤ S_{½}(a)` because `sinh(θx) ≤ θ sinh x` for
`θ ∈ [0, 1]` (`sinh_mul_le_mul_sinh`), and domination forces `S_{½}(a) < e^a/2 < log(1 + π|ξ|/4)/136 ≤ L`.
-/

open Real

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

/-- `sinh(θx) ≤ θ sinh x` for `θ ∈ [0, 1]` and `x ≥ 0`: term by term in the odd power series. -/
theorem sinh_mul_le_mul_sinh {θ x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) :
    Real.sinh (θ * x) ≤ θ * Real.sinh x := by
  have h1 := Real.hasSum_sinh (θ * x)
  have h2 := (Real.hasSum_sinh x).mul_left θ
  refine hasSum_le (fun n => ?_) h1 h2
  rw [mul_pow, mul_div_assoc]
  have hθn : θ ^ (2 * n + 1) ≤ θ := by
    calc θ ^ (2 * n + 1) ≤ θ ^ 1 := pow_le_pow_of_le_one hθ0 hθ1 (by omega)
      _ = θ := pow_one θ
  exact mul_le_mul_of_nonneg_right hθn (by positivity)

/-- **Domination is blind at every depth.**  Let `ξ ≥ e^{100}`, `a > 0` with
`horizonExponent(e^{2a}) + 2 S_{½}(a) < log(1 + πξ/4)`, and `0 < δ ≤ ½`.  Then the isolated off-line
pair of depth `δ` at height `ξ`, in an on-line background of density `rvmLocalDensity ξ`, has Hodge
defect `0` at aperture `a`. -/
theorem hodgeDefectAt_isolatedPair_eq_zero_of_dominance {ξ a δ : ℝ} (hξ : Real.exp 100 ≤ ξ)
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hdom : _root_.RHTower.horizonExponent (Real.exp (2 * a))
        + 2 * SquareRootThreshold.pairEnergy (1 / 2) a < Real.log (1 + π * ξ / 4)) :
    hodgeDefectAt (SquareRootThreshold.isolatedPairConfig (rvmLocalDensity_pos (lt_of_lt_of_le (by
      have := Real.add_one_le_exp (100 : ℝ); have := Real.pi_lt_four; linarith) hξ))
        hδ hδ1 ξ) a = 0 := by
  have hξ0 : 0 < ξ := lt_of_lt_of_le (Real.exp_pos _) hξ
  set x := Real.log ξ with hx
  have hx100 : 100 ≤ x := by rw [hx, ← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hξ
  set L := rvmLocalDensity ξ with hL
  -- the archimedean logarithm is at most `log ξ`
  have hlog1 : Real.log (1 + π * ξ / 4) ≤ x := by
    rw [hx]
    refine Real.log_le_log (by positivity) ?_
    have h1 : (5 : ℝ) ≤ ξ := le_trans (by have := Real.add_one_le_exp (100 : ℝ); linarith) hξ
    have hπ := Real.pi_lt_d2
    have h2 : π * ξ ≤ 3.15 * ξ := mul_le_mul_of_nonneg_right hπ.le hξ0.le
    linarith
  -- the density is at least `log ξ/(4π)`
  have hLx : x / (4 * π) ≤ L := by
    rw [hL, rvmLocalDensity, Real.log_div hξ0.ne' (by positivity), ← hx]
    have h2π : Real.log (2 * π) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have := Real.pi_lt_d2
      have h7 : (7 : ℝ) ≤ Real.exp 2 := by
        have h1 := Real.exp_one_gt_d9
        have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      linarith
    have hπ := Real.pi_pos
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 * π) * (x - Real.log (2 * π)) * (4 * π) = 2 * (x - Real.log (2 * π)) := by
      field_simp; ring
    rw [this]; linarith
  -- domination bounds `e^a`
  have hsinh0 : 0 ≤ SquareRootThreshold.pairEnergy (1 / 2) a := by
    unfold SquareRootThreshold.pairEnergy
    have := Real.self_le_sinh_iff.mpr ha.le
    norm_num; linarith
  have hea : 68 * Real.exp a ≤ x := by
    have e : _root_.RHTower.horizonExponent (Real.exp (2 * a)) = 10 + 68 * Real.exp a := by
      unfold _root_.RHTower.horizonExponent
      rw [show 2 * a = a + a by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a).le]
    rw [e] at hdom
    linarith
  -- the pair energy at every depth is below the density
  have hδa : 2 * δ * a ≤ a := by nlinarith
  have hS : Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a := by
    have h1 := sinh_mul_le_mul_sinh (θ := 2 * δ) (x := a) (by positivity) (by linarith) ha.le
    have h2 : Real.sinh (2 * δ * a) / δ ≤ 2 * Real.sinh a := by
      rw [div_le_iff₀ hδ]; linarith
    have h3 : Real.sinh a ≤ Real.exp a / 2 := by
      rw [Real.sinh_eq]; have := Real.exp_pos (-a); linarith
    have hπ4 := Real.pi_lt_four
    have hπ0 := Real.pi_pos
    have h4 : Real.exp a / 2 ≤ L := by
      have : x / 136 ≤ x / (4 * π) := div_le_div_of_nonneg_left (by linarith) (by positivity)
        (by linarith)
      linarith
    linarith
  -- the aperture is below the Nyquist bound `L/2`
  have haL : a ≤ L / 2 := by
    have h1 : a ≤ Real.exp a - 1 := by linarith [Real.add_one_le_exp a]
    have hπ4 := Real.pi_lt_four
    have h2 : x / 68 ≤ L / 2 := by
      have : x / 68 ≤ x / (8 * π) := div_le_div_of_nonneg_left (by linarith) (by positivity)
        (by nlinarith)
      have e : x / (8 * π) = x / (4 * π) / 2 := by field_simp; ring
      linarith
    linarith
  rw [hodgeDefectAt_isolatedPair _ hδ hδ1 ξ ha haL, if_pos hS]

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

