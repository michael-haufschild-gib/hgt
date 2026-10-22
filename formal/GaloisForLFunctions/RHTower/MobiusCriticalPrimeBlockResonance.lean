import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.CCM.CCMPrimeTransverseFrostmanProfile

/-!
# Critical prime-block resonance of the Möbius dilation cascade

The critical rough-prime recurrence has local translation factor
`I - p^(-1/2) U_(log p)`.  This file proves an exact finite-window obstruction to controlling
those factors by a positive multiplier norm.  In the prime window `(y/3,y]`, the common frequency
`pi/log y` puts every factor in the negative cosine chamber.  Both the forward block at that
frequency and the inverse block at frequency zero dominate the same explicit power

`(1 + 1/sqrt y)^(# window primes)`.

The existing Chebyshev window estimate supplies the matching explicit cardinality budget.  No zero
data, RH assumption, or numerical computation enters the result.
-/

open Complex Finset

noncomputable section
namespace RHTower

/-- Critical radius of the local Möbius translation factor. -/
def mobiusCriticalPrimeRadius (p : ℕ) : ℝ :=
  (Real.sqrt p)⁻¹

/-- Scalar Fourier multiplier of `I - p^(-1/2) U_(log p)`. -/
def mobiusCriticalPrimeFactor (p : ℕ) (t : ℝ) : ℂ :=
  1 - (mobiusCriticalPrimeRadius p : ℂ) *
    Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)

/-- The scalar factor is exactly the physical Hardy--Titchmarsh local Euler multiplier. -/
theorem mobiusCriticalPrimeFactor_eq_archimedeanLocalMultiplier
    (p : ℕ) (t : ℝ) :
    mobiusCriticalPrimeFactor p t =
      1 - ((Real.sqrt (p : ℝ) : ℂ)⁻¹) *
        (MellinL2.mellinCharacter (p : ℝ) t)⁻¹ := by
  have hr : (mobiusCriticalPrimeRadius p : ℂ) =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by
    simp [mobiusCriticalPrimeRadius]
  rw [mobiusCriticalPrimeFactor, hr, MellinL2.mellinCharacter, ← Complex.exp_neg]
  congr 3
  push_cast
  ring

/-- Exact local norm-square law in the prime-log clock phase. -/
theorem normSq_mobiusCriticalPrimeFactor {p : ℕ} (hp : 0 < p) (t : ℝ) :
    Complex.normSq (mobiusCriticalPrimeFactor p t) =
      1 + mobiusCriticalPrimeRadius p ^ 2 -
        2 * mobiusCriticalPrimeRadius p * Real.cos (t * Real.log p) := by
  have hsqrt0 : Real.sqrt (p : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp)
  have hfac : mobiusCriticalPrimeFactor p t =
      (mobiusCriticalPrimeRadius p : ℂ) * ((Real.sqrt p : ℂ) -
        Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)) := by
    rw [mobiusCriticalPrimeFactor, mobiusCriticalPrimeRadius]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hsqrt0]
  rw [hfac, Complex.normSq_mul, Complex.normSq_ofReal,
    normSq_real_sub_exp_I_mul, Real.cos_neg]
  rw [mobiusCriticalPrimeRadius]
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
  field_simp [hsqrt0]
  nlinarith

/-- Negative cosine chamber gives a linear critical-radius gain. -/
theorem one_add_radius_le_normSq_mobiusCriticalPrimeFactor
    {p : ℕ} {t : ℝ} (hp : 0 < p)
    (hcos : Real.cos (t * Real.log p) ≤ -(1 / 2 : ℝ)) :
    1 + mobiusCriticalPrimeRadius p ≤
      Complex.normSq (mobiusCriticalPrimeFactor p t) := by
  rw [normSq_mobiusCriticalPrimeFactor hp]
  have hr0 : 0 ≤ mobiusCriticalPrimeRadius p := by
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (mobiusCriticalPrimeRadius p)]

/-- Radius comparison for a prime bounded by the window endpoint. -/
theorem one_div_sqrt_le_mobiusCriticalPrimeRadius
    {p : ℕ} {y : ℝ} (hp : 1 < p) (hpy : (p : ℝ) ≤ y) :
    1 / Real.sqrt y ≤ mobiusCriticalPrimeRadius p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsqrtp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
  have hsqrtle : Real.sqrt (p : ℝ) ≤ Real.sqrt y := Real.sqrt_le_sqrt hpy
  simpa [mobiusCriticalPrimeRadius, one_div] using
    one_div_le_one_div_of_le hsqrtp hsqrtle

/-- Exact local lower bound at a synchronized window phase. -/
theorem one_add_one_div_sqrt_le_normSq_mobiusCriticalPrimeFactor
    {p : ℕ} {y t : ℝ} (hp : 1 < p) (hpy : (p : ℝ) ≤ y)
    (hcos : Real.cos (t * Real.log p) ≤ -(1 / 2 : ℝ)) :
    1 + 1 / Real.sqrt y ≤
      Complex.normSq (mobiusCriticalPrimeFactor p t) := by
  have hrad : 1 + 1 / Real.sqrt y ≤ 1 + mobiusCriticalPrimeRadius p := by
    linarith [one_div_sqrt_le_mobiusCriticalPrimeRadius hp hpy]
  exact hrad.trans
    (one_add_radius_le_normSq_mobiusCriticalPrimeFactor hp.pos hcos)

/-- Cofinal terminal prime window used by the synchronized block. -/
def mobiusCriticalPrimeWindow (y : ℝ) : Finset ℕ :=
  windowPrimes (y / 3) y

/-- Finite forward critical translation block. -/
def mobiusCriticalPrimeBlock (y t : ℝ) : ℂ :=
  ∏ p ∈ mobiusCriticalPrimeWindow y, mobiusCriticalPrimeFactor p t

/-- Zero-frequency inverse size of the same finite block. -/
def mobiusCriticalPrimeInverseBlock (y : ℝ) : ℝ :=
  ∏ p ∈ mobiusCriticalPrimeWindow y,
    (1 - mobiusCriticalPrimeRadius p)⁻¹

/-- At `t=pi/log y`, every prime in `(y/3,y]` lies in the cosine chamber `cos≤-1/2` once
`y≥27`. -/
theorem mobiusCriticalPrimeWindow_cos_le_neg_half
    {y : ℝ} (hy : 27 ≤ y) {p : ℕ}
    (hpmem : p ∈ mobiusCriticalPrimeWindow y) :
    Real.cos ((Real.pi / Real.log y) * Real.log p) ≤ -(1 / 2 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  have hx0 : 0 ≤ y / 3 := by positivity
  obtain ⟨hpprime, hplower, hpupper⟩ :=
    (mem_windowPrimes hx0 hy0.le).mp hpmem
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlog27 : Real.log (27 : ℝ) ≤ Real.log y :=
    Real.log_le_log (by norm_num) hy
  have hlog27eq : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog3budget : 3 * Real.log 3 ≤ Real.log y := by
    rw [← hlog27eq]
    exact hlog27
  have hloglower : Real.log (y / 3) < Real.log p :=
    Real.log_lt_log (div_pos hy0 (by norm_num)) hplower
  rw [Real.log_div hy0.ne' (by norm_num : (3 : ℝ) ≠ 0)] at hloglower
  have hlogpLower : (2 / 3 : ℝ) * Real.log y ≤ Real.log p := by
    nlinarith
  have hlogpUpper : Real.log p ≤ Real.log y :=
    Real.log_le_log hp0 hpupper
  have hthetaLower : 2 * Real.pi / 3 ≤
      (Real.pi / Real.log y) * Real.log p := by
    have h := mul_le_mul_of_nonneg_left hlogpLower Real.pi_pos.le
    rw [show (Real.pi / Real.log y) * Real.log p =
      (Real.pi * Real.log p) / Real.log y by field_simp]
    rw [le_div_iff₀ hlogy]
    nlinarith
  have hthetaUpper : (Real.pi / Real.log y) * Real.log p ≤ Real.pi := by
    rw [show (Real.pi / Real.log y) * Real.log p =
      (Real.pi * Real.log p) / Real.log y by field_simp]
    apply (div_le_iff₀ hlogy).2
    nlinarith [mul_le_mul_of_nonneg_left hlogpUpper Real.pi_pos.le]
  have htheta0 : 0 ≤ (Real.pi / Real.log y) * Real.log p := by
    positivity
  have htwoThird0 : 0 ≤ 2 * Real.pi / 3 := by positivity
  have htwoThirdPi : 2 * Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcos := Real.antitoneOn_cos
    ⟨htwoThird0, htwoThirdPi⟩ ⟨htheta0, hthetaUpper⟩ hthetaLower
  have hcosTwoThird : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  exact hcos.trans_eq hcosTwoThird

/-- **Synchronized forward block resonance.**  Its squared modulus dominates one copy of the
critical endpoint gain for every prime in the terminal window. -/
theorem mobiusCriticalPrimeBlock_norm_sq_lower
    {y : ℝ} (hy : 27 ≤ y) :
    (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ≤
      ‖mobiusCriticalPrimeBlock y (Real.pi / Real.log y)‖ ^ 2 := by
  rw [mobiusCriticalPrimeBlock, norm_prod, ← Finset.prod_pow,
    ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    rw [← Complex.normSq_eq_norm_sq]
    have hx0 : 0 ≤ y / 3 := by linarith
    have hy0 : 0 ≤ y := by linarith
    obtain ⟨hpprime, _hplower, hpupper⟩ :=
      (mem_windowPrimes hx0 hy0).mp hp
    exact one_add_one_div_sqrt_le_normSq_mobiusCriticalPrimeFactor
      hpprime.one_lt hpupper (mobiusCriticalPrimeWindow_cos_le_neg_half hy hp)

/-- A single local inverse factor dominates `1+p^(-1/2)`. -/
theorem one_add_radius_le_inv_one_sub_radius
    {p : ℕ} (hp : 1 < p) :
    1 + mobiusCriticalPrimeRadius p ≤
      (1 - mobiusCriticalPrimeRadius p)⁻¹ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ mobiusCriticalPrimeRadius p := by
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hrlt : mobiusCriticalPrimeRadius p < 1 := by
    have hsqrt1 : 1 < Real.sqrt (p : ℝ) := by
      nlinarith [Real.sq_sqrt (zero_lt_one.trans hpR).le,
        Real.sqrt_nonneg (p : ℝ)]
    exact inv_lt_one_of_one_lt₀ hsqrt1
  have hden : 0 < 1 - mobiusCriticalPrimeRadius p := sub_pos.mpr hrlt
  rw [inv_eq_one_div, le_div_iff₀ hden]
  nlinarith [sq_nonneg (mobiusCriticalPrimeRadius p)]

/-- **Zero-frequency inverse amplification.**  The inverse block has the same endpoint-power
lower bound as the forward resonant block. -/
theorem mobiusCriticalPrimeInverseBlock_lower
    {y : ℝ} (hy : 27 ≤ y) :
    (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ≤
      mobiusCriticalPrimeInverseBlock y := by
  rw [mobiusCriticalPrimeInverseBlock, ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hx0 : 0 ≤ y / 3 := by linarith
    have hy0 : 0 ≤ y := by linarith
    obtain ⟨hpprime, _hplower, hpupper⟩ :=
      (mem_windowPrimes hx0 hy0).mp hp
    have hrad : 1 + 1 / Real.sqrt y ≤ 1 + mobiusCriticalPrimeRadius p := by
      linarith [one_div_sqrt_le_mobiusCriticalPrimeRadius hpprime.one_lt hpupper]
    exact hrad.trans (one_add_radius_le_inv_one_sub_radius hpprime.one_lt)

/-- Existing Chebyshev supply specialized to the synchronized terminal window. -/
theorem mobiusCriticalPrimeWindow_card_budget
    {y : ℝ} (hy : 27 ≤ y) :
    (y - 1) * Real.log 2 - Real.log (y + 2) -
          2 * Real.sqrt y * Real.log y - Real.log 4 * (y / 3) ≤
      (mobiusCriticalPrimeWindow y).card * Real.log y := by
  exact windowPrimes_card_ge (x := y / 3) (y := y) (by linarith) (by linarith)

/-- Complete finite critical prime-block wall: forward resonance, inverse amplification, and the
explicit Chebyshev cardinality budget hold simultaneously. -/
theorem mobiusCriticalPrimeBlock_resonance_wall
    {y : ℝ} (hy : 27 ≤ y) :
    (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ≤
        ‖mobiusCriticalPrimeBlock y (Real.pi / Real.log y)‖ ^ 2 ∧
      (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ≤
        mobiusCriticalPrimeInverseBlock y ∧
      (y - 1) * Real.log 2 - Real.log (y + 2) -
            2 * Real.sqrt y * Real.log y - Real.log 4 * (y / 3) ≤
        (mobiusCriticalPrimeWindow y).card * Real.log y := by
  exact ⟨mobiusCriticalPrimeBlock_norm_sq_lower hy,
    mobiusCriticalPrimeInverseBlock_lower hy,
    mobiusCriticalPrimeWindow_card_budget hy⟩

end RHTower
