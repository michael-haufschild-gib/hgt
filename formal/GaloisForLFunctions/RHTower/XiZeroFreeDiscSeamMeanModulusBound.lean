import GaloisForLFunctions.RHTower.XiZeroFreeDiscSeamModulusMargin
import GaloisForLFunctions.RHTower.XiRightDiscAdjointSeamSupremum

/-!
# Upper bound for the seam margin: centre value against boundary mean

On a closed disc `D = closedBall c t` on which `xi` has no zero,

`1 − ‖(1 − P) U† P‖² ≤ |xi(c)| / ∫₀¹ |xi(c + t e^{2πix})| dx`   (`xiDisc_one_sub_seam_sq_le`).

With the lower bound `xiDisc_one_sub_seam_sq_ge`, the margin is squeezed between
`min_{∂D}|xi| / max_{∂D}|xi|` and `|xi(c)| / mean_{∂D}|xi|`.

Proof: write `xi(c + t w) = κ exp Ψ(w)` on a slightly larger disc and take the Hardy test vector
`h = exp(Ψ/2)`.  The phase satisfies `U† h = conj(h)`, whose Hardy part is the constant
`conj(h(0))` (Cauchy's mean value), of norm `|h(0)|² = |xi(c)|/κ`.  Meanwhile
`‖h‖² = ∫ |xi(c + t e)|/κ`.  Apply the seam inequality `‖h‖² − ‖P U† h‖² ≤ ‖seam‖² ‖h‖²`.

Consequence (paper): on a disc of fixed radius `t` at height `T`, `|xi|` on the circle is dominated
by the archimedean factor, `log|xi(c + t e^{iθ})| ≈ log|xi(c)| + (t/2) log(T/2π) cos θ`.  So the
bound is about `1/I₀((t/2) log(T/2π)) ≍ (t log T)^{1/2} (T/2π)^{−t/2}`: the seam margin of
fixed-radius discs tends to zero with height even far from every zero, and only discs of radius
`≍ 1/log T` can carry a height-uniform margin.
-/

noncomputable section

open Complex Metric Filter Topology MeasureTheory

namespace RHTower

namespace XiSeamMeanModulus

open LinearPhaseSeam hiding e

local notation "𝕖" => LinearPhaseSeam.e

/-- The logarithm of `xi` on a disc slightly larger than a zero-free closed disc, in disc
coordinates. -/
theorem exists_disc_log (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hzero : ∀ z ∈ closedBall c t, xi z ≠ 0) :
    ∃ R : ℝ, 1 < R ∧ ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (ball (0 : ℂ) R) ∧
      ∀ w : ℂ, ‖w‖ < R → xi (c + (t : ℂ) * w) = ((‖xi c‖ : ℝ) : ℂ) * Complex.exp (Ψ w) := by
  have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous
    continuous_const
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c t).exists_thickening_subset_open hopen
    (fun z hz => hzero z hz)
  rw [thickening_closedBall hδ ht.le] at hsub
  have hball : ∀ z ∈ ball c (δ + t), xi z ≠ 0 := fun z hz => hsub hz
  obtain ⟨L, hLd, -, hLeq⟩ := GaloisForLFunctions.HTGeometry.exists_log_on_ball
    (by positivity : (0 : ℝ) < δ + t) xi_differentiable.differentiableOn hball
  set R : ℝ := 1 + δ / t with hR
  have hδt : 0 < δ / t := by positivity
  have hR1 : 1 < R := by rw [hR]; linarith
  have hmap : ∀ w : ℂ, ‖w‖ < R → c + (t : ℂ) * w ∈ ball c (δ + t) := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    calc t * ‖w‖ < t * R := mul_lt_mul_of_pos_left hw ht
      _ = δ + t := by rw [hR]; field_simp; ring
  refine ⟨R, hR1, fun w => ((Complex.arg (xi c) : ℝ) : ℂ) * I + L (c + (t : ℂ) * w), ?_, ?_⟩
  · intro w hw
    rw [mem_ball, dist_zero_right] at hw
    have hmem := hmap w hw
    exact ((differentiableAt_const _).add ((hLd.differentiableAt (isOpen_ball.mem_nhds hmem)).comp
      w ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)))
      ).differentiableWithinAt
  · intro w hw
    rw [hLeq _ (hmap w hw), Complex.exp_add, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I]

/-- **Seam margin is at most centre value over boundary mean.** -/
theorem xiDisc_one_sub_seam_sq_le (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (hzero : ∀ z ∈ closedBall c t, xi z ≠ 0) :
    1 - ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ ^ 2 ≤
      ‖xi c‖ / ∫ x in (0 : ℝ)..1, ‖xi (c + (t : ℂ) * 𝕖 x)‖ := by
  obtain ⟨R, hR1, Ψ, hΨd, hxiΨ⟩ := exists_disc_log c t ht hzero
  set κ : ℝ := ‖xi c‖ with hκ
  have hκpos : 0 < κ := norm_pos_iff.mpr (hzero c (mem_closedBall_self ht.le))
  set H : ℂ → ℂ := fun w => Complex.exp (Ψ w / 2) with hH
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) R) := fun w hw =>
    ((hΨd w hw).div_const 2).cexp
  set DH := XiSeamModulusMargin.unitDatum hR1 H hHd (fun w => Complex.exp_ne_zero _) with hDH
  have hvH : ∀ x, DH.value x = H (𝕖 x) := XiSeamModulusMargin.unitDatum_value hR1 H hHd _
  have he_lt : ∀ x, ‖𝕖 x‖ < R := fun x => by rw [norm_e]; exact hR1
  have hnormH : ∀ w : ℂ, ‖w‖ < R → ‖H w‖ ^ 2 = ‖xi (c + (t : ℂ) * w)‖ / κ := by
    intro w hw
    rw [hxiΨ w hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
    have : ‖H w‖ ^ 2 = ‖Complex.exp (Ψ w)‖ := by
      rw [hH, pow_two, ← norm_mul, ← Complex.exp_add]; congr 2; ring
    rw [this]; field_simp
  -- the test vector
  set f := circleLiftLp DH.periodic_value DH.contDiff_value.continuous with hf
  set D := (xiDiscDatum c t ht hne) with hD
  have hPf : D.circlePhase.datum.projection f = f := by
    apply hardy_eq_self_of_fourierCoeff_neg
    intro n hn
    rw [hf, fourierCoeff_circleLiftLp]
    exact DH.fourierCoeff_circleLift_value_of_neg hn
  -- the phase: conj(u) · h = conj(h)
  have hval : ∀ x, D.value x = (κ : ℂ) * (H (𝕖 x) * H (𝕖 x)) := by
    intro x
    have hbd : D.boundary x = c + (t : ℂ) * 𝕖 x := by
      simp [hD, DiscArgumentDatum.boundary, xiDiscDatum, LinearPhaseSeam.e, circleMap]
    rw [DiscArgumentDatum.value, hbd, show D.F = xi from rfl, hxiΨ _ (he_lt x), hH,
      ← Complex.exp_add]
    congr 2; ring
  have hphase : ∀ x, starRingEnd ℂ (D.phase x) * H (𝕖 x) = starRingEnd ℂ (H (𝕖 x)) := by
    intro x
    set Hx := H (𝕖 x)
    have hHx : Hx ≠ 0 := Complex.exp_ne_zero _
    have hcHx : starRingEnd ℂ Hx ≠ 0 := (map_ne_zero _).mpr hHx
    have hmod : ((D.modulus x : ℝ) : ℂ) = (κ : ℂ) * (Hx * starRingEnd ℂ Hx) := by
      rw [DiscArgumentDatum.modulus, hval, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hκpos, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκpos.ne'
    rw [DiscArgumentDatum.phase, hmod, hval]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    rfl
  have hper_c : Function.Periodic (fun x => starRingEnd ℂ (DH.value x)) 1 :=
    fun x => by simp only [DH.periodic_value x]
  have hcoef : fourierCoeff ((D.circlePhase.conjMultiplier f : CCMCircleL2) :
      AddCircle (1 : ℝ) → ℂ) = fourierCoeff (circleLift (fun x => starRingEnd ℂ (DH.value x))) := by
    apply fourierCoeff_congr_ae
    filter_upwards [D.circlePhase.conjMultiplier_coeFn f,
      circleLiftLp_coeFn DH.periodic_value DH.contDiff_value.continuous] with z h1 h2
    rw [h1, show ((f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) z = circleLift DH.value z from h2]
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [DiscArgumentDatum.circlePhase_toFun, circleLift_coe D.periodic_phase,
      circleLift_coe DH.periodic_value, circleLift_coe hper_c, hvH]
    exact hphase x
  -- Fourier coefficients of `conj h`
  have hconjcoef : ∀ n : ℤ, fourierCoeff (circleLift (fun x => starRingEnd ℂ (DH.value x))) n =
      starRingEnd ℂ (fourierCoeff (circleLift DH.value) (-n)) := by
    intro n
    rw [fourierCoeff_circleLift, fourierCoeff_circleLift, ← interval_integral_conj]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [map_mul, fourier_neg, neg_neg]
  have hmean : fourierCoeff (circleLift DH.value) 0 = H 0 := by
    rw [fourierCoeff_circleLift]
    have hc := XiSeamSupremum.integral_e_cauchy_of_differentiable hR1
      (fun z hz => hHd.differentiableAt (isOpen_ball.mem_nhds (by
        rw [mem_ball, dist_zero_right]; exact hz))) (w := 0) (by simp) 0
    simp only [pow_zero, one_mul, zero_add, pow_one, sub_zero] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [neg_zero, fourier_zero, one_mul, hvH]
    field_simp [e_ne_zero x]
  have hPnorm : ‖ccmCircleHardyProjection (D.circlePhase.conjMultiplier f)‖ ^ 2 = ‖H 0‖ ^ 2 := by
    rw [norm_sq_hardy_eq_tsum, hcoef]
    rw [tsum_eq_single 0]
    · rw [Nat.cast_zero, hconjcoef, neg_zero, hmean, Complex.norm_conj]
    · intro n hn
      rw [hconjcoef, DH.fourierCoeff_circleLift_value_of_neg (by omega), map_zero, norm_zero]
      norm_num
  have hH0 : ‖H 0‖ ^ 2 = 1 := by
    rw [hnormH 0 (by rw [norm_zero]; linarith), mul_zero, add_zero, ← hκ]
    exact div_self hκpos.ne'
  have hfnorm : ‖f‖ ^ 2 = (∫ x in (0 : ℝ)..1, ‖xi (c + (t : ℂ) * 𝕖 x)‖) / κ := by
    rw [hf, norm_sq_circleLiftLp]
    simp_rw [hvH, fun x => hnormH _ (he_lt x)]
    rw [intervalIntegral.integral_div]
  -- the seam inequality
  have hU : ContinuousLinearMap.adjoint D.circlePhase.datum.unitary =
      D.circlePhase.conjMultiplier := D.circlePhase.adjoint_multiplier
  have hineq := seam_sq_mul_ge D.circlePhase.datum f hPf
  rw [hU] at hineq
  change ‖f‖ ^ 2 - ‖ccmCircleHardyProjection (D.circlePhase.conjMultiplier f)‖ ^ 2 ≤ _ at hineq
  rw [hPnorm, hH0] at hineq
  have hint_pos : 0 < ∫ x in (0 : ℝ)..1, ‖xi (c + (t : ℂ) * 𝕖 x)‖ := by
    have hcont : Continuous (fun x : ℝ => ‖xi (c + (t : ℂ) * 𝕖 x)‖) :=
      (xi_differentiable.continuous.comp (continuous_const.add
        (continuous_const.mul XiSeamModulusMargin.continuous_e))).norm
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
      _ (by norm_num)
    intro x _
    apply norm_pos_iff.mpr
    apply hzero
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, norm_e, mul_one]
  have hfpos : 0 < ‖f‖ ^ 2 := by rw [hfnorm]; positivity
  set I₀ := ∫ x in (0 : ℝ)..1, ‖xi (c + (t : ℂ) * 𝕖 x)‖
  set s := ‖D.circlePhase.datum.adjointHankelSeam‖
  have key : (1 - s ^ 2) * ‖f‖ ^ 2 ≤ 1 := by nlinarith
  rw [hfnorm] at key
  rw [le_div_iff₀ hint_pos]
  have : (1 - s ^ 2) * (I₀ / κ) * κ = (1 - s ^ 2) * I₀ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right key hκpos.le]

end XiSeamMeanModulus

end RHTower
