import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceSimpleJet
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Signed physical escape of the actual prime head

The positive first logarithmic Mellin coefficient forces the actual finite
prime head below every negative linear bound. The transfer uses monotonicity
of the transform of a putatively nonnegative compensated source; it does not
assume a pointwise Tauberian converse.
-/

noncomputable section
open Filter Topology MeasureTheory Set
namespace RHTower

private theorem head_real (x : ℝ) :
    criticalPrimeAbelHead x = ((criticalPrimeAbelHead x).re : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge x
  apply Complex.ext
  · simp
  · rw [criticalPrimeAbelHead_eq_finite x N hN]
    simp

private theorem head_zero {x : ℝ} (hx : x ≤ 1) :
    criticalPrimeAbelHead x = 0 := by
  rw [criticalPrimeAbelHead_eq_finite x 1 (by simpa using hx)]
  apply Finset.sum_eq_zero
  intro p hp
  have hp1 : (p : ℕ) < 1 := by simpa using hp
  have hp2 := p.2.two_le
  omega

private def primeHeadMellin (δ : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re

private theorem primeHeadMellin_eq (δ : ℝ) :
    mellin criticalPrimeAbelHead (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) =
      (primeHeadMellin δ : ℂ) := by
  unfold mellin primeHeadMellin
  rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 1 < x
  · have hx0 : 0 < x := by linarith
    simp only [Set.indicator_apply, Set.mem_Ioi, hx, hx0, ite_true, smul_eq_mul]
    rw [head_real]
    have hp : (x : ℂ) ^ (-((1 : ℂ) + (δ : ℂ) + 1 / 2) - 1) =
        ((x ^ (-(5 / 2 : ℝ) - δ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]
      congr 1
      push_cast
      ring
    rw [hp, ← Complex.ofReal_mul]
    simp only [Complex.ofReal_re]
  · have hz := head_zero (le_of_not_gt hx)
    by_cases hx0 : 0 < x <;> simp [hx, hx0, hz]

private theorem primeHeadMellin_logJet :
    Tendsto (fun δ : ℝ => primeHeadMellin δ / δ / (-Real.log δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorHarmonicBoundary / 3)) := by
  have h := (Complex.continuous_re.tendsto
    ((divisorHarmonicBoundary : ℂ) / 3)).comp criticalPrimeAbelHead_simpleLogJet
  simp only [Function.comp_def, primeHeadMellin_eq] at h
  simp only [Complex.div_ofReal_re, Complex.ofReal_re] at h
  simpa [abscissaLog] using h

private theorem primeHeadMellin_zero :
    Tendsto primeHeadMellin (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscale : Tendsto (fun δ : ℝ => δ * (-Real.log δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_one, neg_mul, mul_neg, mul_comm, neg_zero] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one).neg
  have h := primeHeadMellin_logJet.mul hscale
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ hδ1
  change 0 < δ at hδ
  have hl : -Real.log δ ≠ 0 := neg_ne_zero.mpr (ne_of_lt (Real.log_neg hδ hδ1))
  field_simp [ne_of_gt hδ, hl, ne_of_lt (Real.log_neg hδ hδ1)]

private theorem primeHeadMellin_div_atTop :
    Tendsto (fun δ : ℝ => primeHeadMellin δ / δ) (𝓝[>] (0 : ℝ)) atTop := by
  have hc : 0 < divisorHarmonicBoundary / 3 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 90)
      criticalPrimeAbelHead_simpleLogJet_coefficient_lower
  have hlog : Tendsto (fun δ : ℝ => -Real.log δ) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := primeHeadMellin_logJet.pos_mul_atTop hc hlog
  refine h.congr' ?_
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with δ hδ
  exact div_mul_cancel₀ _ (ne_of_gt hδ)

private theorem primeHeadMellin_eventually_integrable :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      IntegrableOn
        (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re)
        (Ioi (1 : ℝ)) := by
  filter_upwards [primeHeadMellin_div_atTop.eventually (eventually_gt_atTop 0)] with δ hδ
  apply Integrable.of_integral_ne_zero
  change primeHeadMellin δ ≠ 0
  intro hz
  simp [hz] at hδ

private theorem compensated_integral (C δ : ℝ) (hδ : 0 < δ)
    (hi : IntegrableOn
      (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re)
      (Ioi (1 : ℝ))) :
    IntegrableOn
      (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) *
        ((criticalPrimeAbelHead x).re + C * x)) (Ioi (1 : ℝ)) ∧
    (∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ) - δ) *
      ((criticalPrimeAbelHead x).re + C * x)) =
        primeHeadMellin δ + C / (1 / 2 + δ) := by
  have hp := (integrableOn_Ioi_rpow_of_lt
    (a := -(3 / 2 : ℝ) - δ) (by linarith) zero_lt_one).const_mul C
  have heq : ∀ x ∈ Ioi (1 : ℝ),
      x ^ (-(5 / 2 : ℝ) - δ) * ((criticalPrimeAbelHead x).re + C * x) =
        x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re +
          C * x ^ (-(3 / 2 : ℝ) - δ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hr : x ^ (-(5 / 2 : ℝ) - δ) * x = x ^ (-(3 / 2 : ℝ) - δ) := by
      calc
        _ = x ^ (-(5 / 2 : ℝ) - δ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    linear_combination C * hr
  constructor
  · exact (hi.add hp).congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_add hi hp,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    change primeHeadMellin δ + C * (-1 / (-(3 / 2 : ℝ) - δ + 1)) = _
    congr 1
    rw [show -(3 / 2 : ℝ) - δ + 1 = -(1 / 2 + δ) by ring]
    rw [div_neg, neg_div, neg_neg]
    ring

/-- The full finite prime head admits no global linear lower bound. The
conclusion concerns the actual signed source, with no RH or positivity premise. -/
theorem criticalPrimeAbelHead_negative_linear_escape (C : ℝ) :
    ∃ x : ℝ, 1 < x ∧ (criticalPrimeAbelHead x).re < -C * x := by
  suffices h : ∀ K : ℝ, 0 ≤ K →
      ∃ x : ℝ, 1 < x ∧ (criticalPrimeAbelHead x).re < -K * x by
    obtain ⟨x, hx, hb⟩ := h (max C 0) (le_max_right _ _)
    refine ⟨x, hx, hb.trans_le ?_⟩
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) (by linarith)
  intro K hK
  by_contra! hbound
  have hlim : Tendsto (fun δ : ℝ => primeHeadMellin δ + K / (1 / 2 + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * K)) := by
    have hd : Tendsto (fun δ : ℝ => (1 / 2 : ℝ) + δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0)))
    convert primeHeadMellin_zero.add (tendsto_const_nhds.div hd (by norm_num)) using 1 <;>
      first | rfl | ring
  have hevent := (primeHeadMellin_eventually_integrable.and
    (primeHeadMellin_div_atTop.eventually (eventually_gt_atTop (4 * K)))).and
      self_mem_nhdsWithin
  obtain ⟨ε, ⟨hiε, hlarge⟩, hε⟩ := hevent.exists
  change 0 < ε at hε
  have hle : primeHeadMellin ε + K / (1 / 2 + ε) ≤ 2 * K := by
    apply ge_of_tendsto hlim
    filter_upwards [primeHeadMellin_eventually_integrable, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hε)] with δ hiδ hδ hδε
    change 0 < δ at hδ
    change δ < ε at hδε
    obtain ⟨hie, he⟩ := compensated_integral K ε hε hiε
    obtain ⟨hid, hd⟩ := compensated_integral K δ hδ hiδ
    rw [← he, ← hd]
    apply integral_mono_ae hie hid
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
    have hb := hbound x hx
    linarith
  have hbig : 4 * K * ε < primeHeadMellin ε := (lt_div_iff₀ hε).mp hlarge
  have hden : 0 < (1 / 2 : ℝ) + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_right hle hden.le
  have hquot : K / (1 / 2 + ε) * (1 / 2 + ε) = K := div_mul_cancel₀ _ hden.ne'
  have hstrict := mul_lt_mul_of_pos_right hbig hden
  nlinarith [mul_nonneg hK (sq_nonneg ε)]

private theorem criticalAbel_locally_bounded (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ R → |criticalContinuousAbel x| ≤ B := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 1)
  let b : ℕ → ℝ := fun k => |criticalContinuousAbel k| +
    (Real.sqrt N + Real.sqrt k) * |psiDefect k|
  have hb : ∀ k, 0 ≤ b k := fun k => by dsimp [b]; positivity
  refine ⟨∑ k ∈ Finset.range (N + 1), b k, Finset.sum_nonneg (fun k _ => hb k), ?_⟩
  intro x hx
  by_cases hx1 : x ≤ 1
  · rw [criticalContinuousAbel_eq_zero_le_one hx1, abs_zero]
    exact Finset.sum_nonneg (fun k _ => hb k)
  have hx0 : 0 < x := by linarith
  have hxN : x ≤ N := hx.trans ((le_max_left _ _).trans hN)
  have hk : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by simpa using (lt_of_not_ge hx1).le)
  have hkx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxk : x ≤ (⌊x⌋₊ + 1 : ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  have hkN : ⌊x⌋₊ ≤ N := by exact_mod_cast hkx.trans hxN
  have he := congrArg Complex.re
    (squareRootSummatoryPrimitive_between criticalSourceCoeff hk hkx hxk)
  rw [criticalSourceCoeff_cumulative _ hk] at he
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at he
  change criticalContinuousAbel x = criticalContinuousAbel ⌊x⌋₊ +
    (Real.sqrt x - Real.sqrt ⌊x⌋₊) * psiDefect ⌊x⌋₊ at he
  have hs : |Real.sqrt x - Real.sqrt ⌊x⌋₊| ≤ Real.sqrt N + Real.sqrt ⌊x⌋₊ :=
    (abs_sub _ _).trans (by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
      gcongr)
  calc
    |criticalContinuousAbel x| ≤ b ⌊x⌋₊ := by
      rw [he]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (abs_nonneg _)))
    _ ≤ ∑ k ∈ Finset.range (N + 1), b k :=
      Finset.single_le_sum (fun k _ => hb k) (Finset.mem_range.mpr (by omega))

private theorem primeHead_locally_bounded (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ R → |(criticalPrimeAbelHead x).re| ≤ B := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 1)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨B, hB, hb⟩ := criticalAbel_locally_bounded N
  let S := (Finset.range N).subtype Nat.Prime
  refine ⟨∑ p ∈ S, Real.sqrt (p : ℝ) * B,
    Finset.sum_nonneg (fun p _ => mul_nonneg (Real.sqrt_nonneg _) hB), ?_⟩
  intro x hx
  have hxN : x ≤ N := hx.trans ((le_max_left _ _).trans hN)
  rw [criticalPrimeAbelHead_eq_finite x N hxN, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left (hb _ ?_) (Real.sqrt_nonneg _)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  apply (div_le_iff₀ hp0).mpr
  exact hxN.trans (le_mul_of_one_le_right hN0 hp1)

/-- Negative linear excursions occur beyond every physical cutoff, for the
literal finite all-prime source. -/
theorem criticalPrimeAbelHead_cofinal_negative_linear_escape (C X : ℝ) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ (criticalPrimeAbelHead x).re < -C * x := by
  obtain ⟨B, hB, hb⟩ := primeHead_locally_bounded X
  obtain ⟨x, hx1, hxneg⟩ := criticalPrimeAbelHead_negative_linear_escape (max C B)
  have hxX : X < x := by
    by_contra! hle
    have hlow := (abs_le.mp (hb x hle)).1
    have hKB : B ≤ max C B := le_max_right _ _
    have hK0 : 0 ≤ max C B := hB.trans hKB
    have hmul : B ≤ max C B * x := hKB.trans (le_mul_of_one_le_right hK0 hx1.le)
    nlinarith
  refine ⟨x, hxX, hx1, hxneg.trans_le ?_⟩
  exact mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) (by linarith)

end RHTower
