import GaloisForLFunctions.RHTower.BalazardSaiasYorMollifierClass

/-!
# The Balazard–Saias–Yor criterion as an equivalence

Let `I = (1/2π) ∫ log|ζ(½ + it)| dt/(¼ + t²)`.  Unconditionally
`I ≥ Σ_{Re ρ > ½} log|ρ/(1 − ρ)| ≥ 0`, and `I ≤ 0` forces RH.  Here the converse is proved:

`RH ⟺ I = 0`   (`riemannHypothesis_iff_integral_log_norm_zeta_criticalLine_eq_zero`).

**Mechanism.**  For a real Báez-Duarte combination with residual `d < 1` take the mollifier
`M = −sP(s)/(s − 1)` (`bdMollifier`).  Then

`I = (1/2π)∫ log|ζM| − (1/2π)∫ log|M| ≤ ½ log((1/2π)∫|ζM|²) − log|M(1)| ≤ log((1 + d)/(1 − d))`

(`integral_log_norm_zeta_le_of_residual`): Jensen's inequality for `log` on the probability measure
`dt/(2π(¼ + t²))`, the sub-mean-value inequality for the bounded mollifier
(`integrable_and_log_le_integral_log_norm_mollifier`), `|ζM| = |ζP|` on the line with
`(1/2π)∫|ζP|² ≤ (1 + d)²`, and `|M(1)| ≥ 1 − d`.  Under RH the residuals tend to `0`.

Unconditionally this links the two criteria: `tanh(I/2) ≤ d` for every real combination
(`tanh_half_integral_log_norm_zeta_le_residual`).
-/

open MeasureTheory Set Filter Complex Topology

namespace RHTower

noncomputable section

/-- **Jensen's inequality for a bounded mollifier.**  For `M` entire, bounded on `Re s ≥ ½`, with
`M(1) ≠ 0`: `log|M(1)| ≤ (1/2π) ∫ log|M(½ + it)| dt/(¼ + t²)`, and the integrand is integrable. -/
theorem integrable_and_log_le_integral_log_norm_mollifier {M : ℂ → ℂ} (hM : Differentiable ℂ M)
    (hMb : ∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B) (hM1 : M 1 ≠ 0) :
    Integrable (fun t : ℝ => Real.log ‖M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) ∧
      Real.log ‖M 1‖ ≤
        (2 * Real.pi)⁻¹ * ∫ t : ℝ, Real.log ‖M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  set Φ : ℂ → ℂ := fun w => M (halfPlaneOfDisc w) with hΦ
  have hdiff : DifferentiableOn ℂ Φ {1}ᶜ := by
    intro w hw
    have hw1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    have hh : DifferentiableAt ℂ halfPlaneOfDisc w := by
      unfold halfPlaneOfDisc
      exact ((differentiableAt_const _).sub differentiableAt_id).inv hw1
    exact ((hM _).comp w hh).differentiableWithinAt
  have hmeas : Measurable Φ :=
    hM.continuous.measurable.comp ((measurable_const.sub measurable_id).inv)
  have h0 : Φ 0 = M 1 := by simp [hΦ, halfPlaneOfDisc]
  obtain ⟨B, hB⟩ := hMb
  have hB0 : 0 < B := lt_of_lt_of_le (norm_pos_iff.mpr hM1) (hB 1 (by norm_num))
  have hgrowth : ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 →
      Real.log ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖ := by
    refine ⟨|Real.log B| + 2 * Real.log 2, fun w hw hw1 => ?_⟩
    have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    have hn0 : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
    have hn2 : ‖1 - w‖ ≤ 2 := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hlog2 : Real.log ‖1 - w‖ ≤ Real.log 2 := Real.log_le_log hn0 hn2
    have habs := le_abs_self (Real.log B)
    have habs0 := abs_nonneg (Real.log B)
    rcases eq_or_ne (Φ w) 0 with h | h
    · rw [h, norm_zero, Real.log_zero]; linarith
    · have := Real.log_le_log (norm_pos_iff.mpr h) (hB _ (re_halfPlaneOfDisc_ge hw hw1))
      linarith
  obtain ⟨hci, hle⟩ := circleIntegrable_and_sum_log_add_le_circleAverage hdiff hmeas
    (by rw [h0]; exact hM1) hgrowth (U := ∅) (by simp)
  rw [Finset.sum_empty, zero_add, h0] at hle
  have heq : (fun t : ℝ => Real.log ‖Φ (circleMap 0 1 (criticalLineAngle t))‖ / (1 / 4 + t ^ 2)) =
      fun t : ℝ => Real.log ‖M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
    funext t; simp only [hΦ, halfPlaneOfDisc_circleMap_criticalLineAngle]
  refine ⟨?_, ?_⟩
  · have := (circleIntegrable_iff_integrable_criticalLine _).mp hci
    rwa [heq] at this
  · rw [circleAverage_eq_integral_criticalLine, heq] at hle
    exact hle

/-- **The Balazard–Saias–Yor integral is bounded by any Báez-Duarte residual.**  If a real
combination of the generators lies within `d < 1` of the target, then
`(1/2π) ∫ log|ζ(½ + it)| dt/(¼ + t²) ≤ log((1 + d)/(1 − d))`. -/
theorem integral_log_norm_zeta_le_of_residual {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ)
    (hd1 : ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ < 1) :
    (2 * Real.pi)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) ≤
      Real.log ((1 + ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖) /
        (1 - ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖)) := by
  set d := ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  set M := bdMollifier S c with hMdef
  have hMd := differentiable_bdMollifier hS c
  have hMb := exists_bound_bdMollifier hS c
  -- `M(1)`
  have hM1d : ‖1 - M 1‖ ≤ d := by
    rw [hMdef, ← inner_bdTarget_residual hS c]
    refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    rw [norm_bdTarget, one_mul]
  have hM1low : 1 - d ≤ ‖M 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (M 1)
    rw [norm_one] at this
    linarith
  have hM1 : M 1 ≠ 0 := fun h => by rw [h, norm_zero] at hM1low; linarith
  -- the pieces
  obtain ⟨hint, heq⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS c
  obtain ⟨hwint, hwval⟩ := integrable_and_integral_criticalLine_weight
  obtain ⟨hlogM, hJM⟩ := integrable_and_log_le_integral_log_norm_mollifier hMd hMb hM1
  obtain ⟨hlogZM, -⟩ := integrable_and_sum_log_add_le_integral_log_norm_zeta_mul hMd hMb hM1
    (Z := ∅) (by simp)
  obtain ⟨hlogZ, -⟩ := integrable_and_sum_log_le_integral_log_norm_zeta (Z := ∅) (by simp)
  have hae := ae_riemannZeta_mul_ne_zero hMd hM1
  -- `log|ζ| = log|ζM| − log|M|`
  have hsplit : ∀ᵐ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) =
      Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) -
        Real.log ‖M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
    filter_upwards [hae] with t ht
    have hz : riemannZeta (1 / 2 + t * I) ≠ 0 := left_ne_zero_of_mul ht
    have hm : M (1 / 2 + t * I) ≠ 0 := right_ne_zero_of_mul ht
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hm)]
    ring
  have hIeq : ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) =
      (∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) -
        ∫ t : ℝ, Real.log ‖M (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
    rw [integral_congr_ae hsplit, integral_sub hlogZM hlogM]
  -- the mean square of `ζM`
  set F : ℝ → ℝ := fun t => ‖1 + riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)‖
    with hF
  have hpt : ∀ lam : ℝ, 0 < lam → ∀ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) ≤
        (1 + lam) * (1 / (1 / 4 + t ^ 2)) + (1 / lam + 1) * (F t ^ 2 / (1 / 4 + t ^ 2)) := by
    intro lam hlam t
    rw [hMdef, norm_riemannZeta_mul_bdMollifier_line]
    set z := riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)
    have hz : ‖z‖ ≤ 1 + F t := by
      have h1 : z = (1 + z) - 1 := by ring
      calc ‖z‖ = ‖(1 + z) - 1‖ := by rw [← h1]
        _ ≤ ‖1 + z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + F t := by rw [norm_one]; simp only [hF, z]; ring
    have hF0 : 0 ≤ F t := norm_nonneg _
    have hsq : ‖z‖ ^ 2 ≤ (1 + lam) + (1 / lam + 1) * F t ^ 2 := by
      have h1 : ‖z‖ ^ 2 ≤ (1 + F t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have h2 : 2 * F t ≤ F t ^ 2 / lam + lam := by
        rw [div_add' _ _ _ hlam.ne', le_div_iff₀ hlam]; nlinarith [sq_nonneg (F t - lam)]
      have h3 : F t ^ 2 / lam = (1 / lam) * F t ^ 2 := by ring
      nlinarith
    have hq : 0 < 1 / 4 + t ^ 2 := by positivity
    rw [div_le_iff₀ hq]
    have : ((1 + lam) * (1 / (1 / 4 + t ^ 2)) + (1 / lam + 1) * (F t ^ 2 / (1 / 4 + t ^ 2))) *
        (1 / 4 + t ^ 2) = (1 + lam) + (1 / lam + 1) * F t ^ 2 := by field_simp
    rw [this]; exact hsq
  have hmeasZM : AEStronglyMeasurable (fun t : ℝ =>
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) volume := by
    have hcz : Continuous fun t : ℝ => riemannZeta (1 / 2 + t * I) := by
      have := continuous_riemannZeta_vertical (σ := 1 / 2) (by norm_num)
      simpa using this
    have hcm : Continuous fun t : ℝ => M (1 / 2 + t * I) := hMd.continuous.comp (by fun_prop)
    exact (((hcz.mul hcm).norm.pow 2).div (by fun_prop)
      (fun t => by positivity)).aestronglyMeasurable
  have hdom : Integrable (fun t : ℝ =>
      (1 + 1) * (1 / (1 / 4 + t ^ 2)) + (1 / 1 + 1) * (F t ^ 2 / (1 / 4 + t ^ 2))) :=
    (hwint.const_mul _).add (hint.const_mul _)
  have hsqint : Integrable (fun t : ℝ =>
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) :=
    hdom.mono' hmeasZM (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt 1 one_pos t)
  set I2 : ℝ := ∫ t : ℝ, F t ^ 2 / (1 / 4 + t ^ 2) with hI2
  have hd2 : (2 * Real.pi)⁻¹ * I2 = d ^ 2 := by rw [hd, heq]
  have hmean : ∀ lam : ℝ, 0 < lam → (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) ≤
        (1 + lam) + (1 / lam + 1) * d ^ 2 := by
    intro lam hlam
    have hdomlam : Integrable (fun t : ℝ =>
        (1 + lam) * (1 / (1 / 4 + t ^ 2)) + (1 / lam + 1) * (F t ^ 2 / (1 / 4 + t ^ 2))) :=
      (hwint.const_mul _).add (hint.const_mul _)
    have hi := integral_mono hsqint hdomlam (hpt lam hlam)
    rw [integral_add (hwint.const_mul _) (hint.const_mul _), integral_const_mul,
      integral_const_mul, hwval] at hi
    have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
    have hc1 : (2 * Real.pi)⁻¹ * ((1 + lam) * (2 * Real.pi)) = 1 + lam := by field_simp
    calc (2 * Real.pi)⁻¹ * ∫ t : ℝ, _ ≤ (2 * Real.pi)⁻¹ *
          ((1 + lam) * (2 * Real.pi) + (1 / lam + 1) * I2) := mul_le_mul_of_nonneg_left hi hπ.le
      _ = (2 * Real.pi)⁻¹ * ((1 + lam) * (2 * Real.pi)) +
            (1 / lam + 1) * ((2 * Real.pi)⁻¹ * I2) := by ring
      _ = (1 + lam) + (1 / lam + 1) * d ^ 2 := by rw [hc1, hd2]
  have hmean' : (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) ≤ (1 + d) ^ 2 := by
    rcases hd0.lt_or_eq with hdp | hd00
    · have := hmean d hdp
      calc _ ≤ (1 + d) + (1 / d + 1) * d ^ 2 := this
        _ = (1 + d) ^ 2 := by field_simp
    · rw [← hd00]
      refine le_of_forall_pos_lt_add fun e he => ?_
      have := hmean (e / 2) (by positivity)
      rw [← hd00] at this
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero] at this
      norm_num at this ⊢
      linarith
  -- Jensen's inequality for `ζM`
  have hjen := integral_log_norm_le_half_log_integral_sq
    (F := fun t : ℝ => riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)) hae hlogZM hsqint
  have hpos1 : 0 < 1 - d := by linarith
  have hmeanpos : 0 < (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) :=
    mul_pos (by positivity) (integral_sq_criticalLine_pos hae hsqint)
  have hlogmean : 1 / 2 * Real.log ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ≤
      Real.log (1 + d) := by
    have := Real.log_le_log hmeanpos hmean'
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogM1 : Real.log (1 - d) ≤ Real.log ‖M 1‖ := Real.log_le_log hpos1 hM1low
  rw [hIeq, mul_sub, Real.log_div (by linarith) hpos1.ne']
  linarith

/-- **The Balazard–Saias–Yor criterion as an equivalence.**
RH ⟺ `∫ log|ζ(½ + it)| dt/(¼ + t²) = 0`.  The forward direction uses the Báez-Duarte approximants:
under RH the residuals tend to `0`, so the integral is `≤ log((1 + d)/(1 − d)) → 0`. -/
theorem riemannHypothesis_iff_integral_log_norm_zeta_criticalLine_eq_zero :
    RiemannHypothesis ↔
      ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) = 0 := by
  constructor
  · intro hRH
    set J := ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) with hJ
    have hJ0 : 0 ≤ J := integral_log_norm_zeta_criticalLine_nonneg
    have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
    have hle : ∀ η : ℝ, 0 < η → η < 1 → (2 * Real.pi)⁻¹ * J ≤ Real.log ((1 + η) / (1 - η)) := by
      intro η hη hη1
      obtain ⟨N, δ, -, -, hlt⟩ := exists_bdRiesz_norm_lt_of_rh hRH hη
      have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
      refine (integral_log_norm_zeta_le_of_residual hS (bdRieszCoeff N δ)
        (hlt.trans hη1)).trans ?_
      refine Real.log_le_log (by
        have := norm_nonneg (bdTarget - ∑ n ∈ Finset.Icc 1 N,
          (bdRieszCoeff N δ n : ℂ) • bdGen ((n : ℝ)⁻¹))
        exact div_pos (by linarith) (by linarith)) ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hlim : Tendsto (fun η : ℝ => Real.log ((1 + η) / (1 - η))) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun η : ℝ => Real.log ((1 + η) / (1 - η))) 0 := by
        refine ContinuousAt.log ?_ (by norm_num)
        exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    have hJle : (2 * Real.pi)⁻¹ * J ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
      exact hle η hη.1 hη.2
    nlinarith
  · intro h
    exact riemannHypothesis_of_integral_log_norm_zeta_criticalLine_le_zero h.le

/-- **The Báez-Duarte residuals see the BSY integral.**  For every real combination of the
generators, `tanh(I/2) ≤ ‖target − combination‖`, where
`I = (1/2π) ∫ log|ζ(½ + it)| dt/(¼ + t²)`. -/
theorem tanh_half_integral_log_norm_zeta_le_residual {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℕ → ℝ) :
    Real.tanh ((2 * Real.pi)⁻¹ *
        (∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) / 2) ≤
      ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ := by
  set d := ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ with hd
  set I := (2 * Real.pi)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)
    with hI
  rcases lt_or_ge d 1 with hd1 | hd1
  · have h := integral_log_norm_zeta_le_of_residual hS c hd1
    rw [← hd, ← hI] at h
    have hd0 : 0 ≤ d := norm_nonneg _
    have hpos : 0 < (1 + d) / (1 - d) := div_pos (by linarith) (by linarith)
    have hexp : Real.exp I ≤ (1 + d) / (1 - d) := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr h
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have he := Real.exp_pos (I / 2)
    have he' := Real.exp_pos (-(I / 2))
    rw [div_le_iff₀ (by positivity)]
    have hsq : Real.exp (I / 2) * Real.exp (I / 2) = Real.exp I := by
      rw [← Real.exp_add]; ring_nf
    have hinv : Real.exp (-(I / 2)) * Real.exp (I / 2) = 1 := by
      rw [← Real.exp_add]; simp
    rw [le_div_iff₀ (by linarith)] at hexp
    nlinarith [mul_pos he he']
  · refine le_trans ?_ hd1
    exact (Real.tanh_lt_one _).le

end

end RHTower
