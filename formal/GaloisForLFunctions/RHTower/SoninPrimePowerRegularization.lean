/-
The all-prime prime-power tail forced by Sonin principal-shell subtraction.

The raw one-prime Euler corner has squared coefficient p^-1, whose prime sum diverges.  Removing
that linear shell leaves the prime-power tail k >= 2. Its total square energy is finite, and hence
it defines a genuine countable Hilbert--Schmidt diagonal carrier for det_2 regularization.
-/
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite
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

theorem soninPrimePowerTailEnergy_pos (pk : Nat.Primes × ℕ) :
    0 < soninPrimePowerTailEnergy pk := by
  exact pow_pos (inv_pos.mpr (Nat.cast_pos.mpr pk.1.prop.pos)) _

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

/-- Exact unsquared Euler form of the retained logarithmic coefficient. -/
theorem soninLogPrimePowerCoefficient_eq_sqrtInvPow_div (pk : Nat.Primes × ℕ) :
    soninLogPrimePowerCoefficient pk =
      (((Real.sqrt (pk.1 : ℝ))⁻¹ ^ (pk.2 + 2) /
        (pk.2 + 2 : ℝ) : ℝ) : ℂ) := by
  rw [soninLogPrimePowerCoefficient]
  congr 1
  congr 1
  let r : ℝ := (Real.sqrt (pk.1 : ℝ))⁻¹
  have hp : 0 < (pk.1 : ℝ) := by exact_mod_cast pk.1.prop.pos
  have hr : 0 ≤ r := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr2 : r ^ 2 = ((pk.1 : ℝ)⁻¹) := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hp.le]
  have henergy : soninPrimePowerTailEnergy pk = r ^ (2 * (pk.2 + 2)) := by
    rw [soninPrimePowerTailEnergy, ← hr2, pow_mul]
  rw [henergy, show 2 * (pk.2 + 2) = (pk.2 + 2) * 2 by omega, pow_mul]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hr _)]

/-- Every retained logarithmic prime-power coefficient is nonzero. -/
theorem soninLogPrimePowerCoefficient_ne_zero (pk : Nat.Primes × ℕ) :
    soninLogPrimePowerCoefficient pk ≠ 0 := by
  rw [soninLogPrimePowerCoefficient, Complex.ofReal_ne_zero]
  exact div_ne_zero (Real.sqrt_ne_zero'.mpr (soninPrimePowerTailEnergy_pos pk))
    (by positivity)

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

/-- The logarithmic coefficients are square-summable but not absolutely summable.  The
prime-square slice `(p, 0)` is exactly `1/(2p)`, so deleting only the linear `m = 1` shell does
not make the unsquared logarithmic Euler metric summable over all primes.  This excludes a naive
global sum of local operator logarithms; the logarithmic object must remain semilocal/relative or
undergo a further canonical subtraction. -/
theorem not_summable_norm_soninLogPrimePowerCoefficient :
    ¬ Summable (fun pk : Nat.Primes × ℕ => ‖soninLogPrimePowerCoefficient pk‖) := by
  intro h
  have hslice : Summable (fun p : Nat.Primes =>
      ‖soninLogPrimePowerCoefficient (p, 0)‖) :=
    h.comp_injective (fun p q hpq => by simpa using congrArg Prod.fst hpq)
  have hhalf : Summable (fun p : Nat.Primes => (1 / (2 * (p : ℝ)))) := by
    apply hslice.congr
    intro p
    rw [soninLogPrimePowerCoefficient, Complex.norm_real, Real.norm_eq_abs]
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    have henergy : soninPrimePowerTailEnergy (p, 0) = ((p : ℝ)⁻¹) ^ 2 := rfl
    rw [henergy, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    norm_num
    rw [abs_of_pos (div_pos (inv_pos.mpr hp) (by norm_num : (0 : ℝ) < 2))]
    field_simp
  have hone : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := by
    apply (hhalf.mul_left 2).congr
    intro p
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    field_simp
  exact Nat.Primes.not_summable_one_div hone

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
