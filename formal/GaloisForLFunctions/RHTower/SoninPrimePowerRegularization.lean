/-
The all-prime prime-power tail forced by Sonin principal-shell subtraction.

The raw one-prime Euler corner has squared coefficient p^-1, whose prime sum diverges.  Removing
that linear shell leaves the prime-power tail k >= 2. Its total square energy is finite, and hence
it defines a genuine countable Hilbert--Schmidt diagonal carrier for det_2 regularization.
-/
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite
import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk
import Mathlib.NumberTheory.SumPrimeReciprocals

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RHTower

/-- The normalized dilation representation sends the multiplicative identity to the identity
operator. -/
theorem dilationCLM_one :
    dilationCLM 1 zero_lt_one = (1 : SoninL2 →L[ℂ] SoninL2) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [dilation_ae 1 zero_lt_one f] with x hx
  simpa using hx

/-- Multiplicative scales compose exactly in the normalized unitary dilation representation. -/
theorem dilationCLM_mul_dilationCLM
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    dilationCLM r hr * dilationCLM s hs =
      dilationCLM (r * s) (mul_pos hr hs) := by
  apply ContinuousLinearMap.ext
  intro f
  exact dilation_comp_apply r s hr hs f

/-- Operator powers are exactly multiplicative scale powers.  This is the rapidity-addition law
for the quantum dilation representation, stated without introducing a generator or a flow. -/
theorem dilationCLM_pow_eq
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    dilationCLM r hr ^ n = dilationCLM (r ^ n) (pow_pos hr n) := by
  induction n with
  | zero => simpa using dilationCLM_one.symm
  | succ n ih =>
      calc
        dilationCLM r hr ^ (n + 1) =
            dilationCLM r hr ^ n * dilationCLM r hr := pow_succ _ n
        _ = dilationCLM (r ^ n) (pow_pos hr n) * dilationCLM r hr := by rw [ih]
        _ = dilationCLM (r ^ n * r) (mul_pos (pow_pos hr n) hr) :=
          dilationCLM_mul_dilationCLM (r ^ n) r (pow_pos hr n) hr
        _ = dilationCLM (r ^ (n + 1)) (pow_pos hr (n + 1)) := by
          congr 1

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

/-- Every retained prime-power scale is at least the prime square `2² = 4`. -/
theorem four_le_soninPrimePowerScale (pk : Nat.Primes × ℕ) :
    4 ≤ soninPrimePowerScale pk := by
  have hnat : 4 ≤ (pk.1 : ℕ) ^ (pk.2 + 2) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (pk.2 + 2) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      _ ≤ pk.1 ^ (pk.2 + 2) :=
        Nat.pow_le_pow_left pk.1.prop.two_le (pk.2 + 2)
  rw [soninPrimePowerScale]
  exact_mod_cast hnat

/-- The single Hermitian dilation signal attached to a prime.  All retained powers of that prime
will be recurrence polynomials in this one observable. -/
def soninPrimeDilationSignal (p : Nat.Primes) : SoninL2 →L[ℂ] SoninL2 :=
  dilationSum (p : ℝ) (by exact_mod_cast p.prop.one_lt)

/-- **Rapidity/Chebyshev dilation law.**  The symmetric observable at scale `pⁿ` is the
denominator-free cosine recurrence of the one-prime signal.  Thus a whole prime-power tower has
one operator generator. -/
theorem unitaryCosineRecurrence_soninPrimeDilationSignal
    (p : Nat.Primes) (n : ℕ) (hn : 0 < n) :
    HTGeometry.unitaryCosineRecurrence (soninPrimeDilationSignal p) n =
      dilationSum ((p : ℝ) ^ n)
        (one_lt_pow₀ (by exact_mod_cast p.prop.one_lt) (Nat.ne_of_gt hn)) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := zero_lt_one.trans hp
  let U : SoninL2 →L[ℂ] SoninL2 := dilationCLM (p : ℝ) hp0
  let V : SoninL2 →L[ℂ] SoninL2 :=
    dilationCLM ((p : ℝ)⁻¹) (inv_pos.mpr hp0)
  have hUV : U * V = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    change dilation (p : ℝ) hp0
      (dilation ((p : ℝ)⁻¹) (inv_pos.mpr hp0) f) = f
    exact dilation_dilation_inv (p : ℝ) hp0 f
  have hVU : V * U = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    change dilation ((p : ℝ)⁻¹) (inv_pos.mpr hp0)
      (dilation (p : ℝ) hp0 f) = f
    exact dilation_inv_dilation (p : ℝ) hp0 f
  have hsignal : soninPrimeDilationSignal p = U + V := by
    rw [soninPrimeDilationSignal, dilationSum, adjoint_dilationCLM]
  calc
    HTGeometry.unitaryCosineRecurrence (soninPrimeDilationSignal p) n =
        HTGeometry.unitaryCosineRecurrence (U + V) n := by rw [hsignal]
    _ = U ^ n + V ^ n :=
      HTGeometry.unitaryCosineRecurrence_add_inversePair U V hUV hVU n
    _ = dilationCLM ((p : ℝ) ^ n) (pow_pos hp0 n) +
        dilationCLM (((p : ℝ)⁻¹) ^ n) (pow_pos (inv_pos.mpr hp0) n) := by
      simp only [U, V, dilationCLM_pow_eq]
    _ = dilationSum ((p : ℝ) ^ n)
        (one_lt_pow₀ (by exact_mod_cast p.prop.one_lt) (Nat.ne_of_gt hn)) := by
      simp only [dilationSum, adjoint_dilationCLM, inv_pow]

/-- Every retained prime-power dilation observable is therefore a polynomial recurrence value of
the single signal belonging to its underlying prime. -/
theorem unitaryCosineRecurrence_soninPrimeDilationSignal_eq_primePower
    (pk : Nat.Primes × ℕ) :
    HTGeometry.unitaryCosineRecurrence
        (soninPrimeDilationSignal pk.1) (pk.2 + 2) =
      dilationSum (soninPrimePowerScale pk) (one_lt_soninPrimePowerScale pk) := by
  simpa [soninPrimePowerScale] using
    unitaryCosineRecurrence_soninPrimeDilationSignal pk.1 (pk.2 + 2) (by omega)

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

/-- **Prime-power response reduction.**  Each concrete residual is the correction response of a
Chebyshev value of one prime signal.  This is the exact quantum-signal-processing form of the
local nondegeneracy problem. -/
theorem centralSoninPrimePowerResidual_eq_cosineResponse
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    centralSoninPrimePowerResidual a pk =
      centralSoninCornerCorrectionResponse a
        (HTGeometry.unitaryCosineRecurrence
          (soninPrimeDilationSignal pk.1) (pk.2 + 2)) := by
  rw [centralSoninPrimePowerResidual,
    centralSoninDilationCornerResidual_eq_correctionResponse,
    unitaryCosineRecurrence_soninPrimeDilationSignal_eq_primePower]

/-- Every retained prime-power channel is unconditionally nonzero at every positive aperture. -/
theorem centralSoninPrimePowerResidual_ne_zero
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    centralSoninPrimePowerResidual a pk ≠ 0 := by
  exact centralSoninDilationCornerResidual_ne_zero a (soninPrimePowerScale pk) ha
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
