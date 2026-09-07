import GaloisForLFunctions.RHTower.ArithmeticUnitFourierOrientation

/-!
# Finite stationary-frequency control of the literal remainder

The positive-frequency Bernoulli mass is exactly `1/24`. The reciprocal-clock sine identity
bounds each positive atom, while every negative atom outside the finite stationary sector
has negative imaginary part. Summation bounds the full scaled remainder by the finite
stationary contribution plus the positive ceiling minus the negative mean.

For `0 < Re(s) ≤ 1` and `1 ≤ Im(s)`, the mean strictly dominates that ceiling. Hence the full
remainder has negative imaginary part whenever `Im(s) < 2 * pi * N`. At larger heights its
scaled imaginary part lies strictly below the retained stationary budget. That budget is
strictly positive at every unit zero on or right of the critical line; discarding it or
assuming its nonpositivity would also exclude critical zeros. RH remains open.

No numerical certificate or unproved source-sign premise is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Literal Bernoulli Fourier atom with the exact positive-anchor normalization. -/
def scaledBernoulliFourierAtom (s : ℂ) (N : ℕ) (k : ℤ) : ℂ :=
  (N:ℂ)^(star s+1) * ∫ x in Ioi (N:ℝ), bernoulliFourierTerm k (star s) x

/-- The normalization splits into its positive amplitude and logarithmic phase. -/
theorem real_cpow_star_add_one (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (a:ℂ)^(star s+1) = (a^(s.re+1):ℝ) *
      Complex.exp (((-s.im*Real.log a:ℝ):ℂ)*Complex.I) := by
  have hn : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log ha.le,
    Real.rpow_def_of_pos ha, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- Integer anchoring removes the Fourier endpoint phase exactly. -/
theorem scaledBernoulliFourier_integrand_im (s : ℂ) {N : ℕ} (hN : 1 ≤ N)
    (k : ℤ) {x : ℝ} (hx : 0 < x) :
    ((N:ℂ)^(star s+1) * bernoulliFourierTerm k (star s) x).im =
      (N:ℝ)^(s.re+1) * bernoulliModeWeight k * x^(-(s.re+2)) *
        Real.sin (anchoredLogPhase N s.im (2*Real.pi*k) x) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpow := real_cpow_star_add_one s hNp
  simp only [Complex.ofReal_natCast] at hpow
  rw [bernoulliFourierTerm, fourier_mul_cpow_eq_mode k (star s) hx, hpow]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, neg_neg, logarithmicFourierMode]
  have he (A B : ℂ) (w v : ℝ) : (A*Complex.exp (((w:ℝ):ℂ)*Complex.I)) *
      ((bernoulliModeWeight k:ℂ)*(B*Complex.exp ((v:ℂ)*Complex.I))) =
      (A*(bernoulliModeWeight k:ℂ)*B) * Complex.exp (((w+v:ℝ):ℂ)*Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  rw [he]
  simp only [← Complex.ofReal_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
  congr 1
  have hp : -s.im*Real.log N+(2*Real.pi*(k:ℝ)*x+s.im*Real.log x) =
      anchoredLogPhase N s.im (2*Real.pi*k) x + ((k*(N:ℤ):ℤ):ℝ)*(2*Real.pi) := by
    unfold anchoredLogPhase
    push_cast
    ring
  rw [hp, Real.sin_add_int_mul_two_pi]

/-- The literal normalized atom is the anchored, power-weighted sine integral. -/
theorem scaledBernoulliFourierAtom_im_eq {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N)
    (k : ℤ) : (scaledBernoulliFourierAtom s N k).im =
      (N:ℝ)^(s.re+1) * bernoulliModeWeight k *
        ∫ x in Ioi (N:ℝ), x^(-(s.re+2))*Real.sin (anchoredLogPhase N s.im (2*Real.pi*k) x) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hi := (integrable_bernoulliFourierTerm hNp
    (show -1 < (star s).re by simpa using (show -1 < s.re by linarith)) k).const_mul ((N:ℂ)^(star s+1))
  have he : (∫ x in Ioi (N:ℝ), ((N:ℂ)^(star s+1)*bernoulliFourierTerm k (star s) x).im) =
      (∫ x in Ioi (N:ℝ), (N:ℂ)^(star s+1)*bernoulliFourierTerm k (star s) x).im := integral_im hi
  rw [scaledBernoulliFourierAtom, ← integral_const_mul, ← he, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [scaledBernoulliFourier_integrand_im s hN k (hNp.trans hx)]
  ring

/-- The positive-frequency ceiling retains the exact frequency and height. -/
theorem scaledBernoulliFourierAtom_pos_le {s : ℂ} (hs : 0 < s.re) (ht : 0 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : 0 < k) :
    (scaledBernoulliFourierAtom s N k).im ≤ 2*bernoulliModeWeight k/(2*Real.pi*k*N+s.im) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw : 0 < 2*Real.pi*(k:ℝ) := by positivity
  have hd : 0 < 2*Real.pi*(k:ℝ)*N+s.im := by positivity
  rw [scaledBernoulliFourierAtom_im_eq hs hN]
  have hb := integral_anchoredLogSine_le hNp (show 1 < s.re+2 by linarith) hw hd
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Real.rpow_nonneg hNp.le (s.re+1)) (bernoulliModeWeight_nonneg k))
  apply hm.trans_eq
  have hp : (N:ℝ)^(s.re+1)*(N:ℝ)^(1-(s.re+2))=1 := by
    rw [← Real.rpow_add hNp, show s.re+1+(1-(s.re+2))=0 by ring, Real.rpow_zero]
  unfold reciprocalLogWeight
  calc
    _ = 2*bernoulliModeWeight k*((N:ℝ)^(s.re+1)*(N:ℝ)^(1-(s.re+2)))/(2*Real.pi*k*N+s.im) := by ring
    _ = _ := by rw [hp, mul_one]

/-- Negative frequency is the negative of the opposite-height positive sine integral. -/
theorem anchoredLogSine_neg_frequency {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hw : 0 < ω) (hd : 0 < ω*a-γ) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ (-ω) x)) < 0 := by
  have he (x : ℝ) : anchoredLogPhase a γ (-ω) x = -anchoredLogPhase a (-γ) ω x := by
    unfold anchoredLogPhase
    ring
  simp_rw [he, Real.sin_neg, mul_neg, integral_neg]
  exact neg_neg_of_pos (integral_anchoredLogSine_pos ha hβ hw (by simpa using hd))

/-- Every strictly nonstationary negative-frequency atom has negative imaginary part. -/
theorem scaledBernoulliFourierAtom_neg_im_neg {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : 0 < k) (ht : s.im < 2*Real.pi*k*N) :
    (scaledBernoulliFourierAtom s N (-k)).im < 0 := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [scaledBernoulliFourierAtom_im_eq hs hN]
  apply mul_neg_of_pos_of_neg (mul_pos (Real.rpow_pos_of_pos hNp _) (bernoulliModeWeight_pos (neg_ne_zero.mpr hk.ne')))
  simp only [Int.cast_neg, mul_neg]
  exact anchoredLogSine_neg_frequency hNp (by linarith) (by positivity) (sub_pos.mpr ht)

/-- Reflection preserves the Bernoulli coefficient. -/
theorem bernoulliModeWeight_even : Function.Even bernoulliModeWeight := by
  intro k
  simp [bernoulliModeWeight]

/-- Complete source reconstruction at every positive integer anchor. -/
theorem hasSum_scaledBernoulliFourierAtom {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) : HasSum (scaledBernoulliFourierAtom s N)
      (normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ) + 1/(12*(star s+1))) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast hNp.ne'
  have hs' : -1 < (star s).re := by simpa using (show -1 < s.re by linarith)
  have h := (hasSum_integral_bernoulliFourierTerm hNp hs').mul_left ((N:ℂ)^(star s+1))
  rw [centeredBernoulliTail_eq_sub_mean hs' hN, mul_add] at h
  have hp : (N:ℂ)^(star s+1) * ((N:ℂ)^(-star s-1)/(12*(star s+1))) = 1/(12*(star s+1)) := by
    rw [← mul_div_assoc, ← Complex.cpow_add _ _ hn,
      show star s+1+(-star s-1)=0 by ring, Complex.cpow_zero]
  rw [hp, mul_comm ((N:ℂ)^(star s+1)), ← normalizedWeightedRemainder_scaled_eq_tail hs hs1 hN] at h
  exact h

/-- The exact imaginary part of the Bernoulli mean correction. -/
theorem reciprocalBernoulliMean_im (s : ℂ) :
    (1/(12*(star s+1))).im = s.im/(12*Complex.normSq (s+1)) := by
  rw [show (1:ℂ)/(12*(star s+1)) = (star s+1)⁻¹/12 by simp only [mul_inv_rev, div_eq_mul_inv, one_mul]]
  simp only [Complex.div_ofNat_im, Complex.inv_im, Complex.add_im, Complex.star_def,
    Complex.conj_im, Complex.one_im, add_zero, neg_neg]
  have he : Complex.normSq ((starRingEnd ℂ) s+1) = Complex.normSq (s+1) := by simp [Complex.normSq_apply]
  rw [he]
  ring

/-- Complete real source identity, including the normalization and mean. -/
theorem hasSum_scaledBernoulliFourierAtom_im {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) : HasSum (fun k => (scaledBernoulliFourierAtom s N k).im)
      ((N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im + s.im/(12*Complex.normSq (s+1))) := by
  have h := Complex.hasSum_im (hasSum_scaledBernoulliFourierAtom hs hs1 hN)
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    mul_zero, zero_mul, zero_add, add_zero, reciprocalBernoulliMean_im, mul_comm] using h

/-- The positive-frequency half of the actual coefficient sequence. -/
def positiveBernoulliWeight (k : ℤ) : ℝ := if 0 < k then bernoulliModeWeight k else 0

/-- The positive-frequency coefficient sequence remains summable. -/
theorem summable_positiveBernoulliWeight : Summable positiveBernoulliWeight := by
  apply Summable.of_nonneg_of_le (fun k => by unfold positiveBernoulliWeight; split_ifs; exact bernoulliModeWeight_nonneg k; exact le_rfl)
    (fun k => ?_) hasSum_bernoulliModeWeight.summable
  unfold positiveBernoulliWeight
  split_ifs
  · exact le_rfl
  · exact bernoulliModeWeight_nonneg k

/-- The positive-frequency coefficient mass is exactly one twenty-fourth. -/
theorem tsum_positiveBernoulliWeight : (∑' k : ℤ, positiveBernoulliWeight k) = 1/24 := by
  have he : Function.Even bernoulliModeWeight := bernoulliModeWeight_even
  have hsplit (k : ℤ) : bernoulliModeWeight k = positiveBernoulliWeight k + positiveBernoulliWeight (-k) := by
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · simp only [positiveBernoulliWeight, if_neg (not_lt.mpr hk.le), if_pos (neg_pos.mpr hk), he k, zero_add]
    · simp [positiveBernoulliWeight, bernoulliModeWeight_zero]
    · simp only [positiveBernoulliWeight, if_pos hk, if_neg (not_lt.mpr (neg_nonpos.mpr hk.le)), add_zero]
  have hn : Summable (fun k : ℤ => positiveBernoulliWeight (-k)) :=
    summable_positiveBernoulliWeight.comp_injective neg_injective
  have hh : (∑' k : ℤ, positiveBernoulliWeight (-k)) = ∑' k : ℤ, positiveBernoulliWeight k :=
    (Equiv.neg ℤ).tsum_eq positiveBernoulliWeight
  have h := hasSum_bernoulliModeWeight.tsum_eq
  simp_rw [hsplit] at h
  rw [summable_positiveBernoulliWeight.tsum_add hn, hh] at h
  linarith

/-- All negative integer frequencies stationary at or beyond the anchor, including equality. -/
def stationaryFourierIndices (t : ℝ) (N : ℕ) : Finset ℤ :=
  Finset.Icc (-⌊t/(2*Real.pi*N)⌋) (-1)

/-- The complete finite contribution of the stationary negative-frequency atoms. -/
def stationaryFourierBudget (s : ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ stationaryFourierIndices s.im N, (scaledBernoulliFourierAtom s N k).im

/-- The finite index interval is exactly the stationary-frequency condition. -/
theorem mem_stationaryFourierIndices {t : ℝ} {N : ℕ} (hN : 1 ≤ N) {k : ℤ} :
    k ∈ stationaryFourierIndices t N ↔ k < 0 ∧ 2*Real.pi*(-k)*N ≤ t := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd : 0 < 2*Real.pi*(N:ℝ) := by positivity
  simp only [stationaryFourierIndices, Finset.mem_Icc]
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨by omega, ?_⟩
    have hi : -k ≤ ⌊t/(2*Real.pi*N)⌋ := by omega
    have hj := Int.le_floor.mp hi
    have hl := (le_div_iff₀ hd).mp hj
    push_cast at hl ⊢
    nlinarith [hl]
  · rintro ⟨ha,hb⟩
    have hj : ((-k:ℤ):ℝ) ≤ t/(2*Real.pi*N) := by
      apply (le_div_iff₀ hd).mpr
      push_cast at hb ⊢
      nlinarith [hb]
    have hi := Int.le_floor.mpr hj
    constructor <;> omega

/-- Retain stationary atoms exactly and bound all remaining atoms by the positive ceiling. -/
theorem scaledBernoulliFourierAtom_pointwise_le {s : ℂ} (hs : 0 < s.re) (ht : 0 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) (k : ℤ) :
    (scaledBernoulliFourierAtom s N k).im ≤ positiveBernoulliWeight k * (2/(2*Real.pi*N+s.im)) +
      if k ∈ stationaryFourierIndices s.im N then (scaledBernoulliFourierAtom s N k).im else 0 := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd : 0 < 2*Real.pi*(N:ℝ)+s.im := by positivity
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [positiveBernoulliWeight, if_neg (not_lt.mpr hk.le), zero_mul, zero_add]
    by_cases hmem : k ∈ stationaryFourierIndices s.im N
    · simp only [if_pos hmem, le_refl]
    · rw [if_neg hmem]
      have hgt : s.im < 2*Real.pi*(-k)*N := by
        by_contra hh
        exact hmem ((mem_stationaryFourierIndices hN).mpr ⟨hk,not_lt.mp hh⟩)
      simpa only [neg_neg] using (scaledBernoulliFourierAtom_neg_im_neg hs hN (neg_pos.mpr hk) (by simpa only [Int.cast_neg] using hgt)).le
  · simp [scaledBernoulliFourierAtom, bernoulliFourierTerm, bernoulliModeWeight_zero, positiveBernoulliWeight]
  · have hmem : k ∉ stationaryFourierIndices s.im N := by
      intro hh
      exact (lt_asymm hk) ((mem_stationaryFourierIndices hN).mp hh).1
    rw [positiveBernoulliWeight, if_pos hk, if_neg hmem, add_zero]
    apply (scaledBernoulliFourierAtom_pos_le hs ht hN hk).trans
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
    have hden : 2*Real.pi*N+s.im ≤ 2*Real.pi*(k:ℝ)*N+s.im := by
      nlinarith [mul_nonneg (show 0 ≤ 2*Real.pi*(N:ℝ) by positivity) (sub_nonneg.mpr hkR)]
    have hb := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (bernoulliModeWeight_nonneg k)) hd hden
    convert! hb using 1
    ring

/-- The complete source is bounded by its finite stationary budget plus the explicit signed error. -/
theorem normalizedWeightedRemainder_scaled_im_le_stationary_budget {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (ht : 0 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im ≤ stationaryFourierBudget s N +
      1/(12*(2*Real.pi*N+s.im)) - s.im/(12*Complex.normSq (s+1)) := by
  classical
  let F : ℤ → ℝ := fun k => if k ∈ stationaryFourierIndices s.im N then
    (scaledBernoulliFourierAtom s N k).im else 0
  have hF : HasSum F (stationaryFourierBudget s N) := by
    have h : HasSum F (∑ k ∈ stationaryFourierIndices s.im N, F k) :=
      hasSum_sum_of_ne_finset_zero (s := stationaryFourierIndices s.im N)
      (f := F) (fun k hk => by simp [F,hk])
    convert! h using 1
    unfold stationaryFourierBudget
    apply Finset.sum_congr rfl
    intro k hk
    simp [F,hk]
  have hP := summable_positiveBernoulliWeight.hasSum.mul_right (2/(2*Real.pi*N+s.im))
  rw [tsum_positiveBernoulliWeight] at hP
  have h := hasSum_le (scaledBernoulliFourierAtom_pointwise_le hs ht hN)
    (hasSum_scaledBernoulliFourierAtom_im hs hs1 hN) (hP.add hF)
  have he : (1:ℝ)/24 * (2/(2*Real.pi*N+s.im)) = 1/(12*(2*Real.pi*N+s.im)) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  rw [he] at h
  linarith

/-- Throughout the strip at heights at least one, the negative mean exceeds the positive-frequency ceiling. -/
theorem positiveFourier_ceiling_lt_mean {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    1/(12*(2*Real.pi*N+s.im)) < s.im/(12*Complex.normSq (s+1)) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := zero_lt_one.trans_le hNr
  have ht0 : 0 < s.im := zero_lt_one.trans_le ht
  have he : Complex.normSq (s+1) = (s.re+1)^2+s.im^2 := by simp [Complex.normSq_apply,pow_two]
  have hd : 0 < Complex.normSq (s+1) := by rw [he]; positivity
  have hn : 1 ≤ (N:ℝ)*s.im := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*Real.pi by positivity)
  have hc : Complex.normSq (s+1) < s.im*(2*Real.pi*N+s.im) := by
    rw [he]
    nlinarith [Real.pi_gt_three, sq_nonneg (s.re-1)]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The scaled source lies strictly below its finite stationary-frequency budget. -/
theorem normalizedWeightedRemainder_scaled_im_lt_stationary_budget {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im < stationaryFourierBudget s N := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at ht; norm_num at ht
  have hb := normalizedWeightedRemainder_scaled_im_le_stationary_budget hs hs1 (by linarith) hN
  have hp := positiveFourier_ceiling_lt_mean hs hs' ht hN
  linarith

/-- Strictly below the first frequency threshold, the stationary sector is empty. -/
theorem stationaryFourierIndices_eq_empty_of_subresonant {t : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (ht : t < 2*Real.pi*N) : stationaryFourierIndices t N = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨hk0,hkt⟩ := (mem_stationaryFourierIndices hN).mp hk
  have hk1 : (1:ℝ) ≤ -(k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ -k by omega)
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp := mul_le_mul_of_nonneg_left hk1 (show 0 ≤ 2*Real.pi*(N:ℝ) by positivity)
  nlinarith

/-- The sharper remainder sign holds for every strip parameter with height at least one and t less than 2*pi*N. -/
theorem normalizedWeightedRemainder_im_neg_of_subresonant {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (hsub : s.im < 2*Real.pi*N) : (normalizedWeightedRemainder s N).im < 0 := by
  have h := normalizedWeightedRemainder_scaled_im_lt_stationary_budget hs hs' ht hN
  rw [stationaryFourierBudget, stationaryFourierIndices_eq_empty_of_subresonant hN hsub,
    Finset.sum_empty] at h
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  nlinarith [Real.rpow_pos_of_pos hNp (2*s.re+1)]

/-- A zero requires an explicit finite stationary contribution, including horizontal displacement. -/
theorem stationaryFourierBudget_lowerBound_at_zero {s : ℂ} (hs : 0 < s.re)
    (hs' : s.re < 1) (ht : 0 ≤ s.im) (hz : riemannZeta s = 0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s))) +
      s.im/(12*Complex.normSq (s+1)) - 1/(12*(2*Real.pi+s.im)) ≤ stationaryFourierBudget s 1 := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at hs'; norm_num at hs'
  have h := normalizedWeightedRemainder_scaled_im_le_stationary_budget hs hs1 ht (N := 1) (by rfl)
  rw [normalizedWeightedRemainder_one_eq_boundary hs hs', hz] at h
  simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one, zero_div, star_zero, sub_zero,
    minimumZeroBoundary_im] at h
  linarith

/-- Every zero on or right of the critical line requires strictly positive stationary unit budget. -/
theorem stationaryFourierBudget_pos_at_closed_right_zero {s : ℂ} (hs : 1/2 ≤ s.re)
    (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s = 0) :
    0 < stationaryFourierBudget s 1 := by
  have hs0 : 0 < s.re := by linarith
  have h := stationaryFourierBudget_lowerBound_at_zero hs0 hs' (by linarith) hz
  have hp := positiveFourier_ceiling_lt_mean hs0 hs'.le ht (N := 1) (by rfl)
  simp only [Nat.cast_one, mul_one] at hp
  have hb : 0 ≤ s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s))) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  linarith

end RHTower.DeletionMixedRefinement
