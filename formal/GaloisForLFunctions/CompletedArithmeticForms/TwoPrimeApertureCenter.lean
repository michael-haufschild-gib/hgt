import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureWeight
import GaloisForLFunctions.RHTower.ThetaRenewalFeedbackLoop

/-!
# The boundary of two-prime common-center aperture payment

Single-prime damped convexity remains positive before the second generator
enters. At the sum of the two prime shifts, an exact four-term angular
minimum can be negative. Primes two and three give a strict obstruction
for every sufficiently small positive aperture.
-/

set_option autoImplicit false
open Set Filter
open RHTower
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The four surviving pair contributions at center `log 6`, with both prime phases negative. -/
def twoPrimeCenterMinimum (a : ℝ) : ℝ :=
  thetaCuspCenterTailWeight a (Real.log 6) -
    Real.sqrt 2 * thetaCuspCenterTailWeight a (Real.log 3) -
    (2 / Real.sqrt 3) * thetaCuspCenterTailWeight a (Real.log 2) +
    (1 / 2) * thetaCuspCenterTailWeight a (Real.log (3 / 2))

private theorem twoPrimeCenter_linear_neg :
    Real.log 6 - Real.sqrt 2 * Real.log 3 -
      (2 / Real.sqrt 3) * Real.log 2 + (1 / 2) * Real.log (3 / 2) < 0 := by
  have hx : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [h, hn]
  have hy : (2 : ℝ) / Real.sqrt 3 ≥ 8 / 7 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    apply (le_div_iff₀ hp).mpr
    nlinarith only [h, hn]
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    exact ht
  have h32 : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at ht
    exact ht
  have h32n : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have he : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have he32 : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have hbound :
      (2 - Real.sqrt 2 - 2 / Real.sqrt 3) * Real.log 2 +
        (3 / 2 - Real.sqrt 2) * Real.log (3 / 2) ≤
      (-19 / 35 : ℝ) * (1 / 2) + (1 / 10) * (1 / 2) := by
    calc
      _ ≤ (-19 / 35 : ℝ) * Real.log 2 + (1 / 10) * Real.log (3 / 2) :=
        add_le_add (mul_le_mul_of_nonneg_right (by linarith only [hx, hy])
          (le_trans (by norm_num) h2))
          (mul_le_mul_of_nonneg_right (by linarith only [hx]) h32n)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonpos_left h2 (by norm_num))
        (mul_le_mul_of_nonneg_left h32 (by norm_num))
  rw [he32] at hbound
  rw [he, he32]
  nlinarith only [hbound]

private theorem hasDerivAt_apertureWeight_zero (r : ℝ) :
    HasDerivAt (fun a : ℝ => thetaCuspCenterTailWeight a r) (2 * r) 0 := by
  have hu := (hasDerivAt_id (0 : ℝ)).mul_const r
  have h := hu.sinh.add (hu.mul hu.cosh)
  change HasDerivAt (fun a : ℝ => Real.sinh (a * r) + a * r * Real.cosh (a * r)) (2 * r) 0
  apply h.congr_deriv
  simp only [id_eq, zero_mul, Real.cosh_zero, Real.sinh_zero, one_mul, mul_one, add_zero]
  ring

/-- Two independent prime directions already give a negative common-center aperture sum. -/
theorem twoPrimeCenterMinimum_eventually_neg :
    ∃ ε > 0, ε ≤ (1 / 2 : ℝ) ∧ ∀ a ∈ Ioo 0 ε, twoPrimeCenterMinimum a < 0 := by
  have hd := (((hasDerivAt_apertureWeight_zero (Real.log 6)).sub
    ((hasDerivAt_apertureWeight_zero (Real.log 3)).const_mul (Real.sqrt 2))).sub
      ((hasDerivAt_apertureWeight_zero (Real.log 2)).const_mul (2 / Real.sqrt 3))).add
        ((hasDerivAt_apertureWeight_zero (Real.log (3 / 2))).const_mul (1 / 2))
  have hn : 2 * Real.log 6 - Real.sqrt 2 * (2 * Real.log 3) -
      (2 / Real.sqrt 3) * (2 * Real.log 2) + (1 / 2) * (2 * Real.log (3 / 2)) < 0 := by
    nlinarith only [twoPrimeCenter_linear_neg]
  change HasDerivAt twoPrimeCenterMinimum _ 0 at hd
  obtain ⟨ε, hε, hneg⟩ := exists_Ioo_neg_of_hasDerivAt_neg hd
    (by simp [twoPrimeCenterMinimum, thetaCuspCenterTailWeight]) hn
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro a ha
  exact hneg a ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩



/-- The aperture weight extended by zero to negative centers. -/
def clippedApertureWeight (a s : ℝ) : ℝ :=
  thetaCuspCenterTailWeight a (max 0 s)

/-- A prime direction acts by a damped second difference at phase minus one. -/
def aperturePrimeDifference (p h : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  f s - 2 * p * f (s - h) + p ^ 2 * f (s - 2 * h)

private theorem clippedApertureWeight_of_nonpos (a : ℝ) {s : ℝ} (hs : s ≤ 0) :
    clippedApertureWeight a s = 0 := by
  simp only [clippedApertureWeight, max_eq_left hs, thetaCuspCenterTailWeight,
    mul_zero, Real.sinh_zero, Real.cosh_zero, zero_mul, add_zero]

private theorem clippedApertureWeight_of_nonneg (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    clippedApertureWeight a s = thetaCuspCenterTailWeight a s := by
  rw [clippedApertureWeight, max_eq_right hs]

/-- Before the second generator enters, the exact two-prime difference is the positive one-prime payment. -/
theorem aperturePrimeDifference_two_nonneg_before_second
    {a h k p q s : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) (hsk : s ≤ k) :
    0 ≤ aperturePrimeDifference p h
      (aperturePrimeDifference q k (clippedApertureWeight a)) s := by
  have hz (r : ℝ) (hr : r ≤ k) :
      aperturePrimeDifference q k (clippedApertureWeight a) r =
        clippedApertureWeight a r := by
    rw [aperturePrimeDifference,
      clippedApertureWeight_of_nonpos a (s := r - k) (by linarith only [hr]),
      clippedApertureWeight_of_nonpos a (s := r - 2 * k) (by linarith only [hr, hk])]
    ring
  rw [aperturePrimeDifference, hz s hsk,
    hz (s - h) (by linarith only [hsk, hh]),
    hz (s - 2 * h) (by linarith only [hsk, hh])]
  have hpay := thetaCenterTailWeight_two_atom_payment ha hh hs hp hp1
  rw [clippedApertureWeight_of_nonneg a hs]
  change 0 ≤ thetaCuspCenterTailWeight a s -
    2 * p * thetaCuspCenterTailWeight a (max 0 (s - h)) +
    p ^ 2 * thetaCuspCenterTailWeight a (max 0 (s - 2 * h))
  linarith only [hpay]

/-- At the sum of the two prime shifts, exactly four terms survive. -/
theorem aperturePrimeDifference_two_boundary (a p q : ℝ)
    {h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) :
    aperturePrimeDifference p h
      (aperturePrimeDifference q k (clippedApertureWeight a)) (h + k) =
    thetaCuspCenterTailWeight a (h + k) -
      2 * p * thetaCuspCenterTailWeight a k -
      2 * q * thetaCuspCenterTailWeight a h +
      p ^ 2 * thetaCuspCenterTailWeight a (k - h) := by
  have hk : 0 ≤ k := hh.trans hhk
  simp only [aperturePrimeDifference]
  rw [show h + k - k = h by ring,
    show h + k - 2 * k = h - k by ring,
    show h + k - h = k by ring,
    show k - k = 0 by ring,
    show k - 2 * k = -k by ring,
    show h + k - 2 * h = k - h by ring,
    show k - h - k = -h by ring,
    show k - h - 2 * k = -(h + k) by ring]
  rw [clippedApertureWeight_of_nonneg a (add_nonneg hh hk),
    clippedApertureWeight_of_nonneg a hh,
    clippedApertureWeight_of_nonneg a hk,
    clippedApertureWeight_of_nonneg a (sub_nonneg.mpr hhk),
    clippedApertureWeight_of_nonpos a (sub_nonpos.mpr hhk),
    clippedApertureWeight_of_nonpos a le_rfl,
    clippedApertureWeight_of_nonpos a (neg_nonpos.mpr hk),
    clippedApertureWeight_of_nonpos a (neg_nonpos.mpr hh),
    clippedApertureWeight_of_nonpos a (neg_nonpos.mpr (add_nonneg hh hk))]
  ring

/-- The two-prime angular minimum is attained by assigning minus one to both generators. -/
theorem twoPrimeCenter_boundary_minimum {a h k p q c d : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hhk : h ≤ k)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : -1 ≤ c) (hd : -1 ≤ d) :
    aperturePrimeDifference p h
      (aperturePrimeDifference q k (clippedApertureWeight a)) (h + k) ≤
      thetaCuspCenterTailWeight a (h + k) +
        2 * p * c * thetaCuspCenterTailWeight a k +
        2 * q * d * thetaCuspCenterTailWeight a h +
        p ^ 2 * thetaCuspCenterTailWeight a (k - h) := by
  rw [aperturePrimeDifference_two_boundary a p q hh hhk]
  have hk := thetaCuspCenterTailWeight_nonneg ha (hh.trans hhk)
  have hh0 := thetaCuspCenterTailWeight_nonneg ha hh
  have h1 := mul_nonneg (mul_nonneg hp (by linarith only [hc] : 0 ≤ c + 1)) hk
  have h2 := mul_nonneg (mul_nonneg hq (by linarith only [hd] : 0 ≤ d + 1)) hh0
  nlinarith only [h1, h2]

/-- The normalized shifts of primes two and three give the exact negative boundary polynomial. -/
theorem aperturePrimeDifference_two_log6 (a : ℝ) :
    aperturePrimeDifference (1 / Real.sqrt 2) (Real.log 2)
      (aperturePrimeDifference (1 / Real.sqrt 3) (Real.log 3)
        (clippedApertureWeight a)) (Real.log 6) = twoPrimeCenterMinimum a := by
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h23 : Real.log (2 : ℝ) ≤ Real.log 3 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h32 : Real.log (3 : ℝ) - Real.log 2 = Real.log (3 / 2) :=
    (Real.log_div (by norm_num) (by norm_num)).symm
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 2 * (1 / Real.sqrt (2 : ℝ)) = Real.sqrt 2 := by
    have hne : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp
    nlinarith only [hs2]
  have hp2 : (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [div_pow, hs2]
    norm_num
  rw [h6, aperturePrimeDifference_two_boundary a _ _ h2 h23, ← h6, h32, hp, hp2]
  unfold twoPrimeCenterMinimum
  ring

/-- Damped convex payment does not remain nonnegative under the two actual prime shifts. -/
theorem aperturePrimeDifference_two_eventually_neg :
    ∃ ε > 0, ε ≤ (1 / 2 : ℝ) ∧ ∀ a ∈ Ioo 0 ε,
      aperturePrimeDifference (1 / Real.sqrt 2) (Real.log 2)
        (aperturePrimeDifference (1 / Real.sqrt 3) (Real.log 3)
          (clippedApertureWeight a)) (Real.log 6) < 0 := by
  simpa only [aperturePrimeDifference_two_log6] using twoPrimeCenterMinimum_eventually_neg

end GaloisForLFunctions.CompletedArithmeticForms
