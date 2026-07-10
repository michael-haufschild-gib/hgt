/-
The all-prime prime-power tail forced by Sonin principal-shell subtraction.

The raw one-prime Euler corner has squared coefficient p^-1, whose prime sum diverges.  Removing
that linear shell leaves the prime-power tail k >= 2. Its total square energy is finite, and hence
it defines a genuine countable Hilbert--Schmidt diagonal carrier for det_2 regularization.
-/
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal
import GaloisForLFunctions.FredholmDeterminantInfinite
import Mathlib.NumberTheory.SumPrimeReciprocals

noncomputable section

open scoped BigOperators

namespace RHTower

/-- The squared coefficient of the prime-power mode `(p,k+2)`. -/
def soninPrimePowerTailEnergy (pk : Nat.Primes × ℕ) : ℝ :=
  ((pk.1 : ℝ)⁻¹) ^ (pk.2 + 2)

theorem soninPrimePowerTailEnergy_nonneg (pk : Nat.Primes × ℕ) :
    0 ≤ soninPrimePowerTailEnergy pk :=
  pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _

/-- The regularized all-prime tail has finite square energy:
`sum_p sum_(k>=2) p^-k < infinity`. -/
theorem summable_soninPrimePowerTailEnergy :
    Summable soninPrimePowerTailEnergy := by
  have hp0 (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr p.prop.pos)
  have hp1 (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast p.prop.one_lt)
  have hsquare : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    apply h.congr
    intro p
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  change Summable (fun pk : Nat.Primes × ℕ =>
    ((pk.1 : ℝ)⁻¹) ^ (pk.2 + 2))
  rw [summable_prod_of_nonneg (fun pk =>
    pow_nonneg (le_of_lt (hp0 pk.1)) _)]
  refine ⟨(fun p => ?_), ?_⟩
  · change Summable (fun k : ℕ => ((p : ℝ)⁻¹) ^ (k + 2))
    have hgeo :=
      (summable_geometric_of_lt_one (hp0 p).le (hp1 p)).mul_left (((p : ℝ)⁻¹) ^ 2)
    apply hgeo.congr
    intro k
    rw [pow_add]
    ring
  · apply (hsquare.mul_left 2).of_nonneg_of_le
      (fun p => tsum_nonneg (fun k => pow_nonneg (hp0 p).le _))
    intro p
    change (∑' k : ℕ, ((p : ℝ)⁻¹) ^ (k + 2)) ≤ 2 * ((p : ℝ)⁻¹) ^ 2
    rw [show (fun k : ℕ => ((p : ℝ)⁻¹) ^ (k + 2)) =
        fun k => ((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ k by
      funext k
      rw [← pow_add]
      ring_nf]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (hp0 p).le (hp1 p)]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hden : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (hp1 p)
    have hinv : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hden zero_lt_two]
      have hhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
      linarith
    calc
      ((p : ℝ)⁻¹) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹
          ≤ ((p : ℝ)⁻¹) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = 2 * ((p : ℝ)⁻¹) ^ 2 := by ring

/-- The Hilbert--Schmidt amplitude whose square is the regularized prime-power energy. -/
def soninPrimePowerAmplitude (pk : Nat.Primes × ℕ) : ℂ :=
  (Real.sqrt (soninPrimePowerTailEnergy pk) : ℝ)

theorem norm_soninPrimePowerAmplitude_sq (pk : Nat.Primes × ℕ) :
    ‖soninPrimePowerAmplitude pk‖ ^ 2 = soninPrimePowerTailEnergy pk := by
  rw [soninPrimePowerAmplitude, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt
      (soninPrimePowerTailEnergy_nonneg pk)]

theorem summable_norm_soninPrimePowerAmplitude_sq :
    Summable (fun pk : Nat.Primes × ℕ => ‖soninPrimePowerAmplitude pk‖ ^ 2) := by
  apply summable_soninPrimePowerTailEnergy.congr
  intro pk
  exact (norm_soninPrimePowerAmplitude_sq pk).symm

/-- The regularized all-prime prime-power carrier is a genuine countable Hilbert--Schmidt
diagonal kernel. -/
theorem isHS_soninPrimePowerDiagonal :
    HilbertSchmidt.IsHS (HilbertSchmidt.diagMul soninPrimePowerAmplitude) :=
  HilbertSchmidt.isHS_diagMul_infinite soninPrimePowerAmplitude
    summable_norm_soninPrimePowerAmplitude_sq

/-- Its Hilbert--Schmidt norm square is exactly the regularized prime-power energy. -/
theorem hsNormSq_soninPrimePowerDiagonal :
    HilbertSchmidt.hsNormSq (HilbertSchmidt.diagMul soninPrimePowerAmplitude) =
      ∑' pk : Nat.Primes × ℕ, soninPrimePowerTailEnergy pk := by
  rw [HilbertSchmidt.hsNormSq_diagMul_infinite]
  exact tsum_congr norm_soninPrimePowerAmplitude_sq

/-- The actual dilation scale belonging to the prime-power mode `(p,k+2)`. -/
def soninPrimePowerScale (pk : Nat.Primes × ℕ) : ℝ :=
  (pk.1 : ℝ) ^ (pk.2 + 2)

theorem one_lt_soninPrimePowerScale (pk : Nat.Primes × ℕ) :
    1 < soninPrimePowerScale pk := by
  apply one_lt_pow₀ (by exact_mod_cast pk.1.prop.one_lt)
  omega

/-- The logarithmic Euler coefficient `p^(-(k+2)/2)/(k+2)`, expressed as the square root of the
square-energy carrier divided by the prime-power exponent. -/
def soninLogPrimePowerCoefficient (pk : Nat.Primes × ℕ) : ℂ :=
  ((Real.sqrt (soninPrimePowerTailEnergy pk) / (pk.2 + 2 : ℝ) : ℝ) : ℂ)

theorem norm_soninLogPrimePowerCoefficient_sq_le (pk : Nat.Primes × ℕ) :
    ‖soninLogPrimePowerCoefficient pk‖ ^ 2 ≤ soninPrimePowerTailEnergy pk := by
  have hn : (1 : ℝ) ≤ (pk.2 + 2 : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ pk.2 + 2)
  have hn0 : (0 : ℝ) < (pk.2 + 2 : ℝ) := lt_of_lt_of_le zero_lt_one hn
  rw [soninLogPrimePowerCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hn0.le), div_pow,
    Real.sq_sqrt (soninPrimePowerTailEnergy_nonneg pk)]
  exact div_le_self (soninPrimePowerTailEnergy_nonneg pk) (by nlinarith)

theorem summable_norm_soninLogPrimePowerCoefficient_sq :
    Summable (fun pk : Nat.Primes × ℕ => ‖soninLogPrimePowerCoefficient pk‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    norm_soninLogPrimePowerCoefficient_sq_le summable_soninPrimePowerTailEnergy

/-- The actual principal-subtracted Sonin block at prime-power scale `p^(k+2)`. -/
def centralSoninPrimePowerResidual
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[Complex] SoninL2 :=
  centralSoninDilationCornerResidual a (soninPrimePowerScale pk)
    (one_lt_soninPrimePowerScale pk)

/-- The logarithmically weighted actual Sonin residual block. -/
def centralSoninWeightedPrimePowerResidual
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[Complex] SoninL2 :=
  soninLogPrimePowerCoefficient pk • centralSoninPrimePowerResidual a pk

theorem centralSoninPrimePowerResidual_mem_timeBandIdeal
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsSoninTimeBandIdeal (centralSoninPrimePowerResidual a pk) := by
  exact centralSoninDilationCornerResidual_mem_timeBandIdeal a
    (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)

theorem centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsSoninTimeBandIdeal (centralSoninWeightedPrimePowerResidual a pk) := by
  exact IsSoninTimeBandIdeal.smul (soninLogPrimePowerCoefficient pk)
    (centralSoninPrimePowerResidual_mem_timeBandIdeal a ha pk)

/-- Every finite regularized prime-power section of the actual Sonin residual belongs to the
time-band ideal. The remaining infinite assembly is purely the quantitative Schatten-norm
passage. -/
theorem finite_centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    IsSoninTimeBandIdeal (∑ pk ∈ s, centralSoninWeightedPrimePowerResidual a pk) := by
  induction s using Finset.induction_on with
  | empty => simpa using (IsSoninTimeBandIdeal.zero :
      IsSoninTimeBandIdeal (0 : SoninL2 →L[Complex] SoninL2))
  | @insert pk s hpk ih =>
      rw [Finset.sum_insert hpk]
      exact (centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal a ha pk).add ih

/-- The deleted linear shell cannot itself be assembled in Hilbert--Schmidt energy: its square
energy is the divergent prime harmonic series. -/
theorem not_summable_soninLinearPrimeEnergy :
    ¬ Summable (fun p : Nat.Primes => (p : ℝ)⁻¹) := by
  simpa [one_div] using Nat.Primes.not_summable_one_div

end RHTower
