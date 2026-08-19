import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule
import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyRealKrylovPrimeSeamWeld
import GaloisForLFunctions.RHTower.GaussHodgeSeamEnergyBridge
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion

/-!
# The prime seam is the norm-growth defect of one reciprocal Cauchy orbit

Spectral translation by a real time multiplies each reciprocal divisor coordinate by
`exp (-i L α)`, whose modulus is `exp (L · Im α)`.  Because every centered divisor copy lies in the
open horizontal half-strip, the resulting squared norm converges for every real time, is even, and
increases away from zero.

Its increment at the time `log p` is exactly the divisor-weighted seam coefficient of the prime
`p`, up to the fixed positive scale `2 (log p)² / p`.  Hence a single time of norm preservation is
the Riemann hypothesis.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- The translated reciprocal coordinate: the modulus square of `exp(-i L α) / α`. -/
def xiTranslatedReciprocalTerm (L : ℝ) (q : XiZeroCopy) : ℝ :=
  Real.exp (2 * L * (xiSpectralPoint q).im) / ‖xiSpectralPoint q‖ ^ 2

theorem xiTranslatedReciprocalTerm_nonneg (L : ℝ) (q : XiZeroCopy) :
    0 ≤ xiTranslatedReciprocalTerm L q := by
  rw [xiTranslatedReciprocalTerm]
  positivity

theorem summable_inv_norm_xiSpectralPoint_sq :
    Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have h := summable_norm_xiSpectralPoint_inv_sq
  apply h.congr
  intro q
  rw [norm_inv, inv_pow, one_div]

theorem summable_xiTranslatedReciprocalTerm (L : ℝ) :
    Summable (xiTranslatedReciprocalTerm L) := by
  refine Summable.of_nonneg_of_le (fun q => xiTranslatedReciprocalTerm_nonneg L q)
    (fun q => ?_) ((summable_inv_norm_xiSpectralPoint_sq).mul_left (Real.exp |L|))
  have hy := abs_im_xiSpectralPoint_lt_half q
  have hbound : 2 * L * (xiSpectralPoint q).im ≤ |L| := by
    have h1 : |2 * L * (xiSpectralPoint q).im| ≤ |L| := by
      rw [abs_mul, abs_mul]
      have : |(xiSpectralPoint q).im| ≤ 1 / 2 := hy.le
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      nlinarith [abs_nonneg L, abs_nonneg (xiSpectralPoint q).im]
    exact le_trans (le_abs_self _) h1
  have hnum : Real.exp (2 * L * (xiSpectralPoint q).im) ≤ Real.exp |L| :=
    Real.exp_le_exp.mpr hbound
  have hden : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by
    have := xiSpectralPoint_ne_zero q
    positivity
  have hnorm : ‖xiSpectralPoint q‖ ≠ 0 := norm_ne_zero_iff.mpr (xiSpectralPoint_ne_zero q)
  rw [xiTranslatedReciprocalTerm, div_le_iff₀ hden]
  have hcancel : Real.exp |L| * (1 / ‖xiSpectralPoint q‖ ^ 2) * ‖xiSpectralPoint q‖ ^ 2 =
      Real.exp |L| := by field_simp
  rw [hcancel]
  exact hnum

/-- The squared norm of the reciprocal Cauchy vector after spectral translation by `L`. -/
def xiTranslatedReciprocalNormSq (L : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiTranslatedReciprocalTerm L q

/-- **Reflection evenness.**  Functional-equation reflection negates the transverse coordinate and
preserves the modulus, so the norm orbit is even. -/
theorem xiTranslatedReciprocalNormSq_neg (L : ℝ) :
    xiTranslatedReciprocalNormSq (-L) = xiTranslatedReciprocalNormSq L := by
  rw [xiTranslatedReciprocalNormSq, xiTranslatedReciprocalNormSq,
    ← xiZeroCopyReflectEquiv.tsum_eq (xiTranslatedReciprocalTerm L)]
  apply tsum_congr
  intro q
  rw [xiTranslatedReciprocalTerm, xiTranslatedReciprocalTerm, xiSpectralPoint_reflect]
  congr 2
  · simp only [Complex.neg_im]
    ring
  · rw [norm_neg]

theorem xiTranslatedReciprocalNormSq_zero :
    xiTranslatedReciprocalNormSq 0 = xiReciprocalHermitianMass := by
  rw [xiTranslatedReciprocalNormSq, xiReciprocalHermitianMass]
  apply tsum_congr
  intro q
  rw [xiTranslatedReciprocalTerm, xiReciprocalCoordinate, norm_inv, inv_pow]
  norm_num

/-- The cosh-defect term of the norm orbit. -/
def xiTranslatedCoshDefectTerm (L : ℝ) (q : XiZeroCopy) : ℝ :=
  (Real.cosh (2 * L * (xiSpectralPoint q).im) - 1) / ‖xiSpectralPoint q‖ ^ 2

theorem xiTranslatedCoshDefectTerm_nonneg (L : ℝ) (q : XiZeroCopy) :
    0 ≤ xiTranslatedCoshDefectTerm L q := by
  rw [xiTranslatedCoshDefectTerm]
  have h1 : 1 ≤ Real.cosh (2 * L * (xiSpectralPoint q).im) :=
    Real.one_le_cosh _
  have hden : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by
    have := xiSpectralPoint_ne_zero q
    positivity
  positivity

theorem summable_xiTranslatedCoshDefectTerm (L : ℝ) :
    Summable (xiTranslatedCoshDefectTerm L) := by
  have hsum := ((summable_xiTranslatedReciprocalTerm L).add
    (summable_xiTranslatedReciprocalTerm (-L))).sub
      (summable_inv_norm_xiSpectralPoint_sq.mul_left 2)
  have hhalf := hsum.mul_left (1 / 2)
  apply hhalf.congr
  intro q
  rw [xiTranslatedCoshDefectTerm, xiTranslatedReciprocalTerm, xiTranslatedReciprocalTerm,
    Real.cosh_eq]
  have hden : (‖xiSpectralPoint q‖ ^ 2 : ℝ) ≠ 0 := by
    have := xiSpectralPoint_ne_zero q
    positivity
  have hneg : 2 * -L * (xiSpectralPoint q).im = -(2 * L * (xiSpectralPoint q).im) := by ring
  rw [hneg]
  field_simp

/-- **Exact norm growth.**  The norm orbit exceeds its central value by the summed cosh defect. -/
theorem xiTranslatedReciprocalNormSq_sub_zero (L : ℝ) :
    xiTranslatedReciprocalNormSq L - xiTranslatedReciprocalNormSq 0 =
      ∑' q : XiZeroCopy, xiTranslatedCoshDefectTerm L q := by
  have h0 := summable_xiTranslatedReciprocalTerm 0
  have hA : Summable (fun q : XiZeroCopy => (1 / 2 : ℝ) *
      (xiTranslatedReciprocalTerm L q + xiTranslatedReciprocalTerm (-L) q)) :=
    ((summable_xiTranslatedReciprocalTerm L).add
      (summable_xiTranslatedReciprocalTerm (-L))).mul_left _
  have hkey : ∀ q : XiZeroCopy, (1 / 2 : ℝ) *
      (xiTranslatedReciprocalTerm L q + xiTranslatedReciprocalTerm (-L) q) -
        xiTranslatedReciprocalTerm 0 q = xiTranslatedCoshDefectTerm L q := by
    intro q
    have hden : (‖xiSpectralPoint q‖ ^ 2 : ℝ) ≠ 0 := by
      have := xiSpectralPoint_ne_zero q
      positivity
    have hneg : 2 * -L * (xiSpectralPoint q).im = -(2 * L * (xiSpectralPoint q).im) := by ring
    rw [xiTranslatedReciprocalTerm, xiTranslatedReciprocalTerm, xiTranslatedReciprocalTerm,
      xiTranslatedCoshDefectTerm, hneg, Real.cosh_eq]
    simp only [mul_zero, zero_mul, Real.exp_zero]
    field_simp
  have hsplit : xiTranslatedReciprocalNormSq L =
      ∑' q : XiZeroCopy, (1 / 2 : ℝ) *
        (xiTranslatedReciprocalTerm L q + xiTranslatedReciprocalTerm (-L) q) := by
    rw [tsum_mul_left, (summable_xiTranslatedReciprocalTerm L).tsum_add
      (summable_xiTranslatedReciprocalTerm (-L))]
    change _ = 1 / 2 * (xiTranslatedReciprocalNormSq L + xiTranslatedReciprocalNormSq (-L))
    rw [xiTranslatedReciprocalNormSq_neg]
    ring
  rw [hsplit]
  change _ - ∑' q : XiZeroCopy, xiTranslatedReciprocalTerm 0 q = _
  rw [← hA.tsum_sub h0]
  exact tsum_congr hkey

/-- The norm orbit never drops below its central value. -/
theorem xiTranslatedReciprocalNormSq_zero_le (L : ℝ) :
    xiTranslatedReciprocalNormSq 0 ≤ xiTranslatedReciprocalNormSq L := by
  have h := xiTranslatedReciprocalNormSq_sub_zero L
  have hnn : 0 ≤ ∑' q : XiZeroCopy, xiTranslatedCoshDefectTerm L q :=
    tsum_nonneg (fun q => xiTranslatedCoshDefectTerm_nonneg L q)
  linarith

/-! ## One time of norm preservation is the Riemann hypothesis -/

theorem xiSpectralPoint_im_eq_zero_iff_rh :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
  rw [riemannHypothesis_iff_forall_seamCharge_eq_zero]
  constructor
  · intro h q
    rw [xiSpectralPoint_im_eq_zero_iff_orbitwiseFirstPrimeSeamCharge_eq_zero,
      ← orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
    exact h q
  · intro h q
    rw [orbitwiseNatPrimeSeamCharge_two_eq_firstPrime,
      ← xiSpectralPoint_im_eq_zero_iff_orbitwiseFirstPrimeSeamCharge_eq_zero]
    exact h q

/-- **One-time norm preservation.**  For a nonzero translation time, preservation of the reciprocal
Cauchy norm is exactly the Riemann hypothesis. -/
theorem xiTranslatedReciprocalNormSq_eq_zero_iff_rh {L : ℝ} (hL : L ≠ 0) :
    xiTranslatedReciprocalNormSq L = xiTranslatedReciprocalNormSq 0 ↔ RiemannHypothesis := by
  rw [xiSpectralPoint_im_eq_zero_iff_rh]
  constructor
  · intro heq q
    have hsum : ∑' r : XiZeroCopy, xiTranslatedCoshDefectTerm L r = 0 := by
      have h := xiTranslatedReciprocalNormSq_sub_zero L
      rw [heq] at h
      linarith [h]
    have hle := (summable_xiTranslatedCoshDefectTerm L).le_tsum q
      (fun j _ => xiTranslatedCoshDefectTerm_nonneg L j)
    rw [hsum] at hle
    have hterm : xiTranslatedCoshDefectTerm L q = 0 :=
      le_antisymm hle (xiTranslatedCoshDefectTerm_nonneg L q)
    have hden : (‖xiSpectralPoint q‖ ^ 2 : ℝ) ≠ 0 := by
      have := xiSpectralPoint_ne_zero q
      positivity
    rw [xiTranslatedCoshDefectTerm, div_eq_zero_iff] at hterm
    have hcosh : Real.cosh (2 * L * (xiSpectralPoint q).im) = 1 := by
      rcases hterm with h | h
      · linarith
      · exact absurd h hden
    by_contra hne
    have hpos : 1 < Real.cosh (2 * L * (xiSpectralPoint q).im) :=
      Real.one_lt_cosh.mpr (by
        intro hz
        rcases mul_eq_zero.mp hz with h2 | h3
        · rcases mul_eq_zero.mp h2 with h4 | h5
          · norm_num at h4
          · exact hL h5
        · exact hne h3)
    linarith
  · intro h
    have hzero : ∀ q : XiZeroCopy, xiTranslatedCoshDefectTerm L q = 0 := by
      intro q
      rw [xiTranslatedCoshDefectTerm, h q]
      norm_num
    have hsub := xiTranslatedReciprocalNormSq_sub_zero L
    rw [tsum_congr hzero, tsum_zero] at hsub
    linarith

/-! ## The frozen reflected value and the constraint--orientation split -/

/-- **The Weil value is frozen along the orbit.**  Pairing a translated reciprocal coordinate with
the Schwarz-reflected one cancels the translation phase exactly. -/
theorem translated_reciprocal_schwarz_pairing (alpha : ℂ) (L : ℝ) :
    (starRingEnd ℂ)
        (Complex.exp (-(Complex.I * (L : ℂ) * (starRingEnd ℂ) alpha)) /
          (starRingEnd ℂ) alpha) *
        (Complex.exp (-(Complex.I * (L : ℂ) * alpha)) / alpha) = 1 / alpha ^ 2 := by
  have hconj : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (L : ℂ) * (starRingEnd ℂ) alpha))) =
      Complex.exp (Complex.I * (L : ℂ) * alpha) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [map_div₀, hconj, Complex.conj_conj, div_mul_div_comm, ← Complex.exp_add]
  have hcancel : Complex.I * (L : ℂ) * alpha + -(Complex.I * (L : ℂ) * alpha) = 0 := by ring
  rw [hcancel, Complex.exp_zero]
  rw [pow_two]

/-- **Constraint--orientation split.**  The gap between the translated norm and the central
prime--Gamma curvature is the translation defect plus half the static reflection energy. -/
theorem xiTranslatedReciprocalNormSq_sub_curvature (L : ℝ) :
    xiTranslatedReciprocalNormSq L - primeArchCentralCurvature =
      (xiTranslatedReciprocalNormSq L - xiTranslatedReciprocalNormSq 0) +
        xiGlobalReflectionDefectEnergy / 2 := by
  have hdef := xiGlobalReflectionDefectEnergy_eq_mass_sub_source
  have h0 := xiTranslatedReciprocalNormSq_zero
  rw [h0]
  linarith

/-! ## The prime seam coefficient is the sampled norm defect -/

/-- The divisor-weighted seam coefficient at an integer scale. -/
def xiSeamDivisorCoefficient (n : ℕ) : ℝ :=
  ∑' q : XiZeroCopy,
    ‖orbitwiseNatPrimeSeamCharge n ((q.1 : ℂ))‖ ^ 2 / ‖xiSpectralPoint q‖ ^ 2

theorem seam_norm_sq_eq_cosh_defect {n : ℕ} (hn : 1 < n) (q : XiZeroCopy) :
    ‖orbitwiseNatPrimeSeamCharge n ((q.1 : ℂ))‖ ^ 2 =
      2 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) *
        (Real.cosh (2 * Real.log (n : ℝ) * (xiSpectralPoint q).im) - 1) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hbase := orbitwiseNatSeamCharge_weighted_norm_sq_eq_coshDefect ((q.1 : ℂ)) hn
  have hcosh : ((n : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
      (n : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2) =
      2 * (Real.cosh (2 * Real.log (n : ℝ) * (xiSpectralPoint q).im) - 1) := by
    rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR, Real.cosh_eq]
    have him : (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := xiSpectralPoint_im_eq q
    rw [him]
    have h1 : 2 * Real.log (n : ℝ) * (1 / 2 - ((q.1 : ℂ)).re) =
        -(Real.log (n : ℝ) * (2 * ((q.1 : ℂ)).re - 1)) := by ring
    have h2 : Real.log (n : ℝ) * (-(2 * ((q.1 : ℂ)).re - 1)) =
        -(Real.log (n : ℝ) * (2 * ((q.1 : ℂ)).re - 1)) := by ring
    rw [h1, h2, neg_neg]
    ring
  rw [hcosh] at hbase
  have hpow : (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 := by
    rw [Real.rpow_neg hnR.le, one_div]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow] at hbase
  field_simp at hbase ⊢
  linarith [hbase]

theorem summable_seamDivisorTerm {n : ℕ} (hn : 1 < n) :
    Summable (fun q : XiZeroCopy =>
      ‖orbitwiseNatPrimeSeamCharge n ((q.1 : ℂ))‖ ^ 2 / ‖xiSpectralPoint q‖ ^ 2) := by
  have h := (summable_xiTranslatedCoshDefectTerm (Real.log (n : ℝ))).mul_left
    (2 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ))
  apply h.congr
  intro q
  rw [xiTranslatedCoshDefectTerm, seam_norm_sq_eq_cosh_defect hn q]
  ring

/-- **The seam coefficient is the sampled norm defect.** -/
theorem xiSeamDivisorCoefficient_eq {n : ℕ} (hn : 1 < n) :
    xiSeamDivisorCoefficient n =
      2 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) *
        (xiTranslatedReciprocalNormSq (Real.log (n : ℝ)) -
          xiTranslatedReciprocalNormSq 0) := by
  rw [xiSeamDivisorCoefficient, xiTranslatedReciprocalNormSq_sub_zero, ← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [xiTranslatedCoshDefectTerm, seam_norm_sq_eq_cosh_defect hn q]
  ring

/-- **One scale decides.**  Vanishing of the divisor-weighted seam coefficient at any single
nontrivial integer scale is the Riemann hypothesis. -/
theorem xiSeamDivisorCoefficient_eq_zero_iff_rh {n : ℕ} (hn : 1 < n) :
    xiSeamDivisorCoefficient n = 0 ↔ RiemannHypothesis := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hnR).ne'
  have hscale : 2 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    positivity
  rw [xiSeamDivisorCoefficient_eq hn, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact absurd h hscale
    · exact (xiTranslatedReciprocalNormSq_eq_zero_iff_rh hlog).mp (by linarith)
  · intro h
    right
    have := (xiTranslatedReciprocalNormSq_eq_zero_iff_rh hlog).mpr h
    linarith

/-! ## Subexponential orbit growth -/

/-- **Bounded orbit forces the critical line.**  A uniform bound on the translated reciprocal norm
over nonnegative times is the Riemann hypothesis. -/
theorem riemannHypothesis_of_bddAbove_xiTranslatedReciprocalNormSq
    (h : ∃ C : ℝ, ∀ L : ℝ, 0 ≤ L → xiTranslatedReciprocalNormSq L ≤ C) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := h
  rw [xiSpectralPoint_im_eq_zero_iff_rh]
  by_contra hcon
  push Not at hcon
  obtain ⟨q₀, hq₀⟩ := hcon
  -- choose the copy with positive transverse coordinate
  obtain ⟨q, hy⟩ : ∃ q : XiZeroCopy, 0 < (xiSpectralPoint q).im := by
    rcases lt_or_gt_of_ne hq₀ with hlt | hgt
    · refine ⟨xiZeroCopyReflectEquiv q₀, ?_⟩
      rw [xiSpectralPoint_reflect]
      simpa using hlt
    · exact ⟨q₀, hgt⟩
  set r : ℝ := ‖xiSpectralPoint q‖ with hr
  have hrpos : 0 < r := by
    rw [hr]
    exact norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  set L : ℝ := (|C| * r ^ 2 + 1) / (2 * (xiSpectralPoint q).im) with hL
  have hLnonneg : 0 ≤ L := by
    rw [hL]
    positivity
  have hexp : 2 * L * (xiSpectralPoint q).im = |C| * r ^ 2 + 1 := by
    rw [hL]
    field_simp
  have hle : xiTranslatedReciprocalTerm L q ≤ xiTranslatedReciprocalNormSq L :=
    (summable_xiTranslatedReciprocalTerm L).le_tsum q
      (fun j _ => xiTranslatedReciprocalTerm_nonneg L j)
  have hbound := hC L hLnonneg
  have hchain : Real.exp (|C| * r ^ 2 + 1) / r ^ 2 ≤ C := by
    calc Real.exp (|C| * r ^ 2 + 1) / r ^ 2
        = xiTranslatedReciprocalTerm L q := by
          rw [xiTranslatedReciprocalTerm, hexp, hr]
      _ ≤ xiTranslatedReciprocalNormSq L := hle
      _ ≤ C := hbound
  have hgrow : |C| * r ^ 2 + 1 + 1 ≤ Real.exp (|C| * r ^ 2 + 1) := by
    simpa using Real.add_one_le_exp (|C| * r ^ 2 + 1)
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  rw [div_le_iff₀ hr2] at hchain
  nlinarith [le_abs_self C, abs_nonneg C]

/-- **Displacement as a window amplitude.**  The difference between the untranslated and the
translated reciprocal coordinate is the anchored sharp-window amplitude at that spectral point. -/
theorem translated_reciprocal_displacement (alpha : ℂ) (halpha : alpha ≠ 0) (L : ℝ) :
    1 / alpha - Complex.exp (-(Complex.I * (L : ℂ) * alpha)) / alpha =
      Complex.I * ((1 - Complex.exp (-(Complex.I * (L : ℂ) * alpha))) /
        (Complex.I * alpha)) := by
  field_simp

end

end RHTower
