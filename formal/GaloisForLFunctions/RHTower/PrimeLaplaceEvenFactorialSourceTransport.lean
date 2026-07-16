import GaloisForLFunctions.RHTower.PrimeLaplaceEvenFactorialFockIncidence

/-!
# Source-generated transport and its uniform prime defect

The ambient even-factorial jet completion need not support bounded Taylor translation.  The actual
prime-exponential columns nevertheless form an invariant source subspace: translation by `a`
sends the raw jet at `log p` to exactly `p⁻ᵃ` times itself.  At the critical half-unit seam the
corresponding source-diagonal translation loses at least one half of the squared norm; at unit
translation it loses at least three quarters:

`(1/2) * energy ≤ halfUnitDefectEnergy`,

`(3/4) * energy ≤ unitDefectEnergy`.

Together with `PrimeLaplaceEvenFactorialFockIncidence`, this gives a complete all-prime
Hilbert--Schmidt incidence whose source-generated transport is a strict contraction at every
finite source scale.  It does not identify this positive defect with the normalized Xi/Weil form;
that completed source-value comparison remains the RH-bearing step.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The raw derivative jet of the prime exponential `x ↦ p⁻ˣ`. -/
def primeLaplaceRawJet (p : Nat.Primes) (j : ℕ) : ℝ :=
  (-primeLogSupport p) ^ j

/-- **Exact source-transport eigenlaw.**  Infinite Taylor translation by `a` acts on the complete
raw prime jet by the real eigenvalue `p⁻ᵃ`. -/
theorem hasSum_primeLaplaceRawJet_translate
    (p : Nat.Primes) (i : ℕ) (a : ℝ) :
    HasSum (fun h : ℕ ↦
      a ^ h * primeLaplaceRawJet p (i + h) / (h.factorial : ℝ))
      ((p : ℝ) ^ (-a) * primeLaplaceRawJet p i) := by
  have hsum :=
    (NormedSpace.expSeries_div_hasSum_exp (-a * primeLogSupport p)).mul_left
      ((-primeLogSupport p) ^ i)
  rw [← Real.exp_eq_exp_ℝ] at hsum
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hexp : Real.exp (-a * primeLogSupport p) = (p : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos hp0]
    congr 1
    rw [primeLogSupport]
    ring
  rw [hexp] at hsum
  convert hsum using 1
  · funext h
    unfold primeLaplaceRawJet
    rw [pow_add]
    rw [mul_pow]
    ring
  · unfold primeLaplaceRawJet
    ring

theorem hasSum_primeLaplaceRawJet_unitTranslate
    (p : Nat.Primes) (i : ℕ) :
    HasSum (fun h : ℕ ↦ primeLaplaceRawJet p (i + h) / (h.factorial : ℝ))
      ((p : ℝ)⁻¹ * primeLaplaceRawJet p i) := by
  simpa [Real.rpow_neg_one] using hasSum_primeLaplaceRawJet_translate p i 1

/-- The critical half-unit source transport has multiplier `p⁻¹˲²` on every prime column. -/
theorem hasSum_primeLaplaceRawJet_halfTranslate
    (p : Nat.Primes) (i : ℕ) :
    HasSum (fun h : ℕ ↦
      (1 / 2 : ℝ) ^ h * primeLaplaceRawJet p (i + h) / (h.factorial : ℝ))
      ((p : ℝ) ^ (-(1 / 2 : ℝ)) * primeLaplaceRawJet p i) := by
  exact hasSum_primeLaplaceRawJet_translate p i (1 / 2)

/-- Squared norm of a finite source coefficient packet. -/
def finitePrimeSourceEnergy
    {P : Type*} [Fintype P] (c : P → ℂ) : ℝ :=
  ∑ q, Complex.normSq (c q)

/-- Squared norm after applying the source-diagonal unit translation `c_q ↦ p_q⁻¹ c_q`. -/
def finitePrimeSourceUnitTranslationEnergy
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) : ℝ :=
  ∑ q, Complex.normSq (c q) * ((prime q : ℝ)⁻¹) ^ 2

/-- Energy of the source translation defect `I - T*T`. -/
def finitePrimeSourceUnitTranslationDefectEnergy
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) : ℝ :=
  finitePrimeSourceEnergy c - finitePrimeSourceUnitTranslationEnergy prime c

/-- Squared energy after critical half-unit translation.  The eigenvalue `p⁻¹˲²` contributes
the exact energy multiplier `p⁻¹`. -/
def finitePrimeSourceHalfTranslationEnergy
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) : ℝ :=
  ∑ q, Complex.normSq (c q) * (prime q : ℝ)⁻¹

/-- Energy of the critical half-unit source translation defect. -/
def finitePrimeSourceHalfTranslationDefectEnergy
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) : ℝ :=
  finitePrimeSourceEnergy c - finitePrimeSourceHalfTranslationEnergy prime c

/-- Squared source energy after translation by an arbitrary real displacement `a`. -/
def finitePrimeSourceTranslationEnergy
    {P : Type*} [Fintype P] (a : ℝ) (prime : P → Nat.Primes) (c : P → ℂ) : ℝ :=
  ∑ q, Complex.normSq (c q) * (prime q : ℝ) ^ (-2 * a)

/-- Source translation defect at displacement `a`. -/
def finitePrimeSourceTranslationDefectEnergy
    {P : Type*} [Fintype P] (a : ℝ) (prime : P → Nat.Primes) (c : P → ℂ) : ℝ :=
  finitePrimeSourceEnergy c - finitePrimeSourceTranslationEnergy a prime c

lemma prime_inv_sq_le_quarter (p : Nat.Primes) :
    ((p : ℝ)⁻¹) ^ 2 ≤ 1 / 4 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  have hsquare :=
    (sq_le_sq₀ (inv_nonneg.mpr hp0.le) (by norm_num : (0 : ℝ) ≤ 2⁻¹)).2 hinv
  norm_num at hsquare ⊢
  exact hsquare

/-- Source unit translation is uniformly contractive by a factor at most `1/2`, independently of
the number and choice of prime channels. -/
theorem finitePrimeSourceUnitTranslationEnergy_le_quarter
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) :
    finitePrimeSourceUnitTranslationEnergy prime c ≤
      (1 / 4 : ℝ) * finitePrimeSourceEnergy c := by
  unfold finitePrimeSourceUnitTranslationEnergy finitePrimeSourceEnergy
  calc
    ∑ q, Complex.normSq (c q) * ((prime q : ℝ)⁻¹) ^ 2 ≤
        ∑ q, Complex.normSq (c q) * (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (prime_inv_sq_le_quarter (prime q))
        (Complex.normSq_nonneg _)
    _ = (1 / 4 : ℝ) * ∑ q, Complex.normSq (c q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- **Uniform all-scale source coercivity.**  The defect of the source-generated unit translation
has the aperture-independent lower bound `3/4`. -/
theorem finitePrimeSourceUnitTranslationDefectEnergy_coercive
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) :
    (3 / 4 : ℝ) * finitePrimeSourceEnergy c ≤
      finitePrimeSourceUnitTranslationDefectEnergy prime c := by
  unfold finitePrimeSourceUnitTranslationDefectEnergy
  linarith [finitePrimeSourceUnitTranslationEnergy_le_quarter prime c]

/-- Critical half-unit translation loses at least one half of the source energy at every finite
aperture. -/
theorem finitePrimeSourceHalfTranslationEnergy_le_half
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) :
    finitePrimeSourceHalfTranslationEnergy prime c ≤
      (1 / 2 : ℝ) * finitePrimeSourceEnergy c := by
  unfold finitePrimeSourceHalfTranslationEnergy finitePrimeSourceEnergy
  calc
    ∑ q, Complex.normSq (c q) * (prime q : ℝ)⁻¹ ≤
        ∑ q, Complex.normSq (c q) * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hp2 : (2 : ℝ) ≤ (prime q : ℝ) := by
        exact_mod_cast (prime q).prop.two_le
      have hinv : (prime q : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      exact mul_le_mul_of_nonneg_left hinv (Complex.normSq_nonneg _)
    _ = (1 / 2 : ℝ) * ∑ q, Complex.normSq (c q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- **Critical all-scale source coercivity.**  The defect of the source-generated half-unit
translation has the aperture-independent lower bound `1/2`. -/
theorem finitePrimeSourceHalfTranslationDefectEnergy_coercive
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) (c : P → ℂ) :
    (1 / 2 : ℝ) * finitePrimeSourceEnergy c ≤
      finitePrimeSourceHalfTranslationDefectEnergy prime c := by
  unfold finitePrimeSourceHalfTranslationDefectEnergy
  linarith [finitePrimeSourceHalfTranslationEnergy_le_half prime c]

lemma prime_rpow_neg_two_mul_le_half
    (p : Nat.Primes) {a : ℝ} (ha : 1 / 2 ≤ a) :
    (p : ℝ) ^ (-2 * a) ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
  have hpow : (p : ℝ) ^ (-2 * a) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  exact hpow.trans hinv

/-- Every source translation at or beyond the critical half-unit seam has norm at most
`1 / sqrt 2`, uniformly in the aperture. -/
theorem finitePrimeSourceTranslationEnergy_le_half
    {P : Type*} [Fintype P] {a : ℝ} (ha : 1 / 2 ≤ a)
    (prime : P → Nat.Primes) (c : P → ℂ) :
    finitePrimeSourceTranslationEnergy a prime c ≤
      (1 / 2 : ℝ) * finitePrimeSourceEnergy c := by
  unfold finitePrimeSourceTranslationEnergy finitePrimeSourceEnergy
  calc
    ∑ q, Complex.normSq (c q) * (prime q : ℝ) ^ (-2 * a) ≤
        ∑ q, Complex.normSq (c q) * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (prime_rpow_neg_two_mul_le_half (prime q) ha)
        (Complex.normSq_nonneg _)
    _ = (1 / 2 : ℝ) * ∑ q, Complex.normSq (c q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- **All-transport-scale source coercivity.**  Every displacement at least `1/2` retains the
same aperture-independent defect floor. -/
theorem finitePrimeSourceTranslationDefectEnergy_coercive
    {P : Type*} [Fintype P] {a : ℝ} (ha : 1 / 2 ≤ a)
    (prime : P → Nat.Primes) (c : P → ℂ) :
    (1 / 2 : ℝ) * finitePrimeSourceEnergy c ≤
      finitePrimeSourceTranslationDefectEnergy a prime c := by
  unfold finitePrimeSourceTranslationDefectEnergy
  linarith [finitePrimeSourceTranslationEnergy_le_half ha prime c]

end

end RHTower
