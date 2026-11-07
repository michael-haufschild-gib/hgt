import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentCore

/-!
# A parabolic core for the theta current

The positive cosine source retains the lower profile
`Ξ(b) ≥ (49/100) (1 - b²/36)` on `|b| ≤ 6`.
The verified low-zero region then gives a squared parabolic current floor.
Keeping this weight permits polynomial estimates on the larger symmetric interval.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

/-- The second source moment pays a quadratic minorant of the complete cosine transform. -/
theorem Xi_ge_center_parabola (b : ℝ) :
    Xi 0 * (1 - b ^ 2 / 36) ≤ Xi b := by
  have hsrc : IntegrableOn thetaCuspFullSource (Ioi 0) :=
    integrable_thetaCuspFullSource'.integrableOn
  have hsec : IntegrableOn (fun x : ℝ => x ^ 2 * thetaCuspFullSource x) (Ioi 0) :=
    integrable_thetaCuspSecondMoment.integrableOn
  have hcos : IntegrableOn (fun x : ℝ => thetaCuspFullSource x * Real.cos (b * x)) (Ioi 0) := by
    refine Integrable.mul_bdd (c := 1) hsrc (by fun_prop) (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (b * x)
  have hmono : ∫ x in Ioi (0 : ℝ), (thetaCuspFullSource x - b ^ 2 / 2 *
      (x ^ 2 * thetaCuspFullSource x)) ≤
      ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.cos (b * x) := by
    refine setIntegral_mono_on (hsrc.sub (hsec.const_mul _)) hcos measurableSet_Ioi fun x _ => ?_
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := b * x))
      (thetaCuspFullSource_pos x).le
    nlinarith only [h]
  rw [integral_sub hsrc (hsec.const_mul _), integral_const_mul] at hmono
  have hS : (∫ x in Ioi (0 : ℝ), x ^ 2 * thetaCuspFullSource x) ≤ Xi 0 / 36 := by
    have hp := mul_le_mul_of_nonneg_left poleSharpConstant_le Xi_zero_pos.le
    have hs := second_moment_le
    nlinarith only [hp, hs, Xi_zero_pos.le]
  have hpaid := mul_le_mul_of_nonneg_left hS (sq_nonneg b)
  have hmass := Xi_zero_eq_two_mul_integral_thetaCuspFullSource
  rw [Xi_eq_thetaCuspCosineRepresentation b, thetaCuspCosineRepresentation]
  nlinarith only [hmono, hpaid, hmass]

/-- A nonnegative parabolic minorant on the symmetric interval of radius six. -/
theorem Xi_ge_parabolic {b : ℝ} (hb : |b| ≤ 6) :
    (49 / 100 : ℝ) * (1 - b ^ 2 / 36) ≤ Xi b := by
  have hb2 : b ^ 2 ≤ 36 := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    norm_num only [sq_abs, show (6 : ℝ) ^ 2 = 36 by norm_num] at h
    exact h
  have hw : 0 ≤ 1 - b ^ 2 / 36 := by linarith only [hb2]
  have hz : (49 / 100 : ℝ) ≤ Xi 0 := by
    have hh := Xi_zero_ge
    norm_num at hh ⊢
    exact hh
  exact (mul_le_mul_of_nonneg_right hz hw).trans (Xi_ge_center_parabola b)

/-- Every zero contributes to the pair sum at least its share of `2 + γ − log 4π`. -/
theorem pair_floor_thirteen_halves {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hb : |b| ≤ 13 / 2) (q : XiZeroCopy) :
    1 / 3 * a * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re ≤
      xiLinePairRe a ((q.1 : ℂ).re - 1 / 2) (b - (q.1 : ℂ).im) := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (q.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (q.1 : ℂ).im := ⟨_, rfl⟩
  rw [← hδ, ← hγ]
  have hδ1 : δ ^ 2 < 1 / 4 := by
    rw [hδ]
    exact xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hγ2 : 41 / 2 < γ ^ 2 := by
    rw [hγ]
    exact xiZeroCopy_fortyOne_div_two_lt_im_sq q
  -- The zero sum term.
  have hρ : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = ((1 / 4 - δ ^ 2 + γ ^ 2 : ℝ) : ℂ) +
      ((-(2 * δ * γ) : ℝ) : ℂ) * I := by
    have hq : (q.1 : ℂ) = ((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I := by
      apply Complex.ext
      · simp [hδ]
      · simp [hγ]
    rw [hq]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  obtain ⟨A, hA⟩ : ∃ A, A = 1 / 4 - δ ^ 2 + γ ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; nlinarith only [hδ1, hγ2]
  have hr : ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re ≤ 1 / A := by
    rw [hρ, one_div, Complex.inv_re, Complex.normSq_apply, ← hA]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    rw [div_le_div_iff₀ (by nlinarith only [hA0, mul_self_nonneg (2 * δ * γ)]) hA0]
    nlinarith only [mul_self_nonneg (2 * δ * γ)]
  -- The pair.
  obtain ⟨u, hu⟩ : ∃ u, u = b - γ := ⟨_, rfl⟩
  rw [← hu]
  have habsu : |u| ≤ |γ| + 13 / 2 := by
    rw [hu]
    have := abs_sub b γ
    linarith only [this, hb]
  have hu2 : u ^ 2 ≤ γ ^ 2 + 13 * |γ| + 169 / 4 := by
    rw [← sq_abs u]
    have h1 := pow_le_pow_left₀ (abs_nonneg u) habsu 2
    have h2 := sq_abs γ
    nlinarith only [h1, h2]
  have hgabs : (4.5 : ℝ) < |γ| := by
    have h2 := sq_abs γ
    have h3 := abs_nonneg γ
    by_contra hc
    nlinarith only [not_lt.1 hc, h2, h3, hγ2]
  have hgoal : 1 / 3 * a * (1 / A) ≤ xiLinePairRe a δ u := by
    unfold xiLinePairRe
    by_cases hoff : δ = 0
    · subst hoff
      simp only [sub_zero, add_zero]
      have hD : 0 < a ^ 2 + u ^ 2 := by positivity
      have hA' : A = 1 / 4 + γ ^ 2 := by rw [hA]; ring
      have e : a / (a ^ 2 + u ^ 2) + a / (a ^ 2 + u ^ 2) = 2 * a / (a ^ 2 + u ^ 2) := by ring
      rw [e, show 1 / 3 * a * (1 / A) = 1 / 3 * a / A by ring,
        div_le_div_iff₀ hA0 hD]
      have hkey : 1 / 3 * (a ^ 2 + u ^ 2) ≤ 2 * A := by
        rw [hA']
        nlinarith only [hu2, hgabs, ha2, ha, sq_abs γ, abs_nonneg γ]
      nlinarith only [mul_le_mul_of_nonneg_left hkey ha.le]
    · -- Off the line the zero is far above the window.
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro h
        apply hoff
        rw [hδ, h]
        ring
      have hfar : (67 : ℝ) < |γ| := by
        have hzero : xi (q.1 : ℂ) = 0 := xi_xiZeroCopy_eq_zero q
        rw [hγ]
        exact lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven hzero
          (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q) hqoff
      have habslow : |γ| - 13 / 2 ≤ |u| := by
        rw [hu]
        have := abs_sub_abs_le_abs_sub γ b
        rw [abs_sub_comm γ b] at this
        linarith only [this, hb]
      have hX : (60 : ℝ) ^ 2 ≤ u ^ 2 := by
        rw [← sq_abs u]
        exact pow_le_pow_left₀ (by norm_num) (by linarith only [habslow, hfar]) 2
      have hδabs : |δ| ≤ 1 / 2 := by
        rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
        linarith only [hδ1]
      obtain ⟨hδa, hδb⟩ := abs_le.mp hδabs
      have h1 : (a - δ) ^ 2 ≤ 1 := by nlinarith only [ha, ha2, hδa, hδb]
      have h2 : (a + δ) ^ 2 ≤ 1 := by nlinarith only [ha, ha2, hδa, hδb]
      obtain ⟨X, hXdef⟩ : ∃ X, X = u ^ 2 := ⟨_, rfl⟩
      rw [← hXdef] at hX hu2 ⊢
      norm_num at hX
      have hD1 : 0 < (a - δ) ^ 2 + X := by positivity
      have hD2 : 0 < (a + δ) ^ 2 + X := by positivity
      rw [div_add_div _ _ hD1.ne' hD2.ne', show 1 / 3 * a * (1 / A) = 1 / 3 * a / A by ring,
        div_le_div_iff₀ hA0 (mul_pos hD1 hD2)]
      have hnum : (a - δ) * ((a + δ) ^ 2 + X) + ((a - δ) ^ 2 + X) * (a + δ) =
          2 * a * (a ^ 2 - δ ^ 2 + X) := by ring
      rw [hnum]
      have hprod : ((a - δ) ^ 2 + X) * ((a + δ) ^ 2 + X) ≤ (1 + X) ^ 2 := by
        nlinarith only [h1, h2, hD1, hD2]
      have hA2 : γ ^ 2 ≤ A := by rw [hA]; linarith only [hδ1]
      have hnum2 : X - 1 / 4 ≤ a ^ 2 - δ ^ 2 + X := by nlinarith only [hδ1, sq_nonneg a]
      have hgX : X ≤ 2 * γ ^ 2 := by
        have h3 := sq_abs γ
        nlinarith only [hu2, hfar, h3]
      have hmain : 1 / 3 * (1 + X) ^ 2 ≤ 2 * (X - 1 / 4) * γ ^ 2 := by
        nlinarith only [hgX, hX, mul_nonneg (by linarith only [hX] : (0 : ℝ) ≤ X)
          (by linarith only [hgX] : (0 : ℝ) ≤ 2 * γ ^ 2 - X)]
      have hX4 : 0 ≤ X - 1 / 4 := by linarith only [hX]
      calc 1 / 3 * a * (((a - δ) ^ 2 + X) * ((a + δ) ^ 2 + X))
          ≤ 1 / 3 * a * (1 + X) ^ 2 := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = a * (1 / 3 * (1 + X) ^ 2) := by ring
        _ ≤ a * (2 * (X - 1 / 4) * γ ^ 2) := mul_le_mul_of_nonneg_left hmain ha.le
        _ ≤ a * (2 * (a ^ 2 - δ ^ 2 + X) * A) := by
            refine mul_le_mul_of_nonneg_left ?_ ha.le
            exact mul_le_mul (by linarith only [hnum2]) hA2 (sq_nonneg _)
              (by linarith only [hnum2, hX4])
        _ = _ := by ring
  refine le_trans ?_ hgoal
  exact mul_le_mul_of_nonneg_left hr (by positivity)

/-- The radius-six pair floor is a restriction of the wider window estimate. -/
theorem pair_floor_six {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hb : |b| ≤ 6) (q : XiZeroCopy) :
    1 / 3 * a * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re ≤
      xiLinePairRe a ((q.1 : ℂ).re - 1 / 2) (b - (q.1 : ℂ).im) :=
  pair_floor_thirteen_halves ha ha2 (hb.trans (by norm_num)) q

/-- The logarithmic derivative retains its floor throughout radius `13/2`. -/
theorem re_logDeriv_xi_ge_thirteen_halves {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hb : |b| ≤ 13 / 2) :
    0.0076 * a ≤ (logDeriv xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I)).re ∧
      xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I) ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I := ⟨_, rfl⟩
  rw [← hs]
  have hre : s.re = 1 / 2 + a := by
    rw [hs]
    norm_num [Complex.mul_re, Complex.mul_im]
  have him : s.im = b := by
    rw [hs]
    norm_num [Complex.mul_re, Complex.mul_im]
  have hxi : xi s ≠ 0 := by
    intro h0
    rcases eq_or_lt_of_le ha2 with rfl | hlt
    · exact xi_ne_zero_of_one_le_re (by rw [hre]; norm_num) h0
    · have h := lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven h0
        (by rw [hre]; linarith only [ha]) (by rw [hre]; linarith only [hlt])
        (by rw [hre]; linarith only [ha])
      rw [him] at h
      linarith only [h, hb]
  refine ⟨?_, hxi⟩
  have hsa : s.re - 1 / 2 = a := by rw [hre]; ring
  have hfloor (q : XiZeroCopy) := pair_floor_thirteen_halves ha ha2 hb q
  have hpair (q : XiZeroCopy) :
      0 ≤ xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2) (s.im - (q.1 : ℂ).im) := by
    rw [hsa, him]
    by_cases hoff : (q.1 : ℂ).re = 1 / 2
    · rw [hoff, sub_self]
      unfold xiLinePairRe
      simp only [sub_zero, add_zero]
      positivity
    · refine le_trans ?_ (hfloor q)
      have hr : 0 ≤ ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
        have := WeilDeletion.inv_normSq_spectralPoint_le q
        have hp : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
        linarith only [this, hp]
      positivity
  have hsumRe : Summable fun q : XiZeroCopy => ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
    summable_inv_mul_one_sub.mapL Complex.reCLM
  have hval : ∑' q : XiZeroCopy, ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re =
      poleSharpConstant := by
    rw [← Complex.re_tsum summable_inv_mul_one_sub, tsum_inv_zero_mul_one_sub_zero_re]
  have hmain : 1 / 3 * a * poleSharpConstant ≤ 2 * (logDeriv xi s).re := by
    rw [← hval, ← tsum_mul_left]
    refine (hsumRe.mul_left _).tsum_le_of_sum_le fun F => ?_
    refine le_trans (Finset.sum_le_sum fun q _ => ?_)
      (sum_pair_le_two_mul_re_logDeriv_xi hxi hpair F)
    rw [hsa, him]
    exact hfloor q
  have hP := le_poleSharpConstant
  have h1 := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 1 / 3 * a)
  norm_num at h1 ⊢
  linarith only [h1, hmain, ha]

/-- The logarithmic derivative floor on the radius-six window. -/
theorem re_logDeriv_xi_ge_six {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hb : |b| ≤ 6) :
    0.0076 * a ≤ (logDeriv xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I)).re ∧
      xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I) ≠ 0 :=
  re_logDeriv_xi_ge_thirteen_halves ha ha2 (hb.trans (by norm_num))

/-- The complete current retains a squared parabolic core at every critical aperture. -/
theorem current_ge_parabolic {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hb : |b| ≤ 6) :
    a / 300 * (1 - b ^ 2 / 36) ^ 2 ≤ current a b := by
  obtain ⟨hlog, hxi⟩ := re_logDeriv_xi_ge_six ha ha2 hb
  have him : 0.0076 * a ≤ (logDeriv XiC ((b : ℂ) - (a : ℂ) * I)).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using hlog
  have hnn : ∀ a' ∈ Ioo 0 a, 0 ≤ current a' b := fun a' ha' =>
    current_nonneg_of_rhVerifiedThrough (T := 66) ha'.1 (by
      norm_num
      exact rhVerifiedThrough_sixtySeven) (hb.trans (by norm_num))
  have hN := sq_Xi_le_normSq ha.le hnn
  have hb2 : b ^ 2 ≤ 36 := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    norm_num only [sq_abs, show (6 : ℝ) ^ 2 = 36 by norm_num] at h
    exact h
  have hw : 0 ≤ (49 / 100 : ℝ) * (1 - b ^ 2 / 36) := by
    have : 0 ≤ 1 - b ^ 2 / 36 := by linarith only [hb2]
    positivity
  have hsq := pow_le_pow_left₀ hw (Xi_ge_parabolic hb) 2
  have hne : XiC ((b : ℂ) - (a : ℂ) * I) ≠ 0 := hxi
  change _ ≤ 2 * ((starRingEnd ℂ) (XiC ((b : ℂ) - (a : ℂ) * I)) *
    (-I * deriv XiC ((b : ℂ) - (a : ℂ) * I))).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hne, ← logDeriv_apply]
  have h1 := mul_le_mul (hsq.trans hN) him (by positivity : 0 ≤ 0.0076 * a)
    (Complex.normSq_nonneg (XiC ((b : ℂ) - (a : ℂ) * I)))
  have hp := mul_nonneg ha.le (sq_nonneg (1 - b ^ 2 / 36))
  nlinarith only [h1, hp]

#print axioms Xi_ge_center_parabola
#print axioms current_ge_parabolic

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
