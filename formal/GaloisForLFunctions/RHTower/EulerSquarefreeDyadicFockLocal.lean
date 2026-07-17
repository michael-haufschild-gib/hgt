import GaloisForLFunctions.RHTower.MobiusFiniteSchurTransfer
import GaloisForLFunctions.HTGeometry.WeylCharacterGenerator

/-!
# Local dyadic Fock factorization of an Euler exponent

A geometric prime exponent decomposes uniquely into its parity bit and a residual exponent.
This file proves the exact probability, signed-amplitude, normalization, mean, and variance
identities.  They are the one-prime algebraic core of the canonical squarefree--Euler source
channel; no Xi-zero or RH hypothesis occurs.
-/

open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- The normalized geometric law of one Euler prime exponent. -/
def dyadicEulerGeometricProbability (q : ℝ) (k : ℕ) : ℝ :=
  (1 - q) * q ^ k

/-- The squarefree parity law obtained from a geometric Euler exponent. -/
def dyadicSquarefreeParityProbability (q : ℝ) (e : Fin 2) : ℝ :=
  q ^ (e : ℕ) / (1 + q)

/-- The residual geometric law after removing the parity bit. -/
def dyadicEulerResidualProbability (q : ℝ) (j : ℕ) : ℝ :=
  dyadicEulerGeometricProbability (q ^ 2) j

theorem dyadicEulerGeometricProbability_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    0 ≤ dyadicEulerGeometricProbability q k := by
  exact mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq0 k)

theorem dyadicSquarefreeParityProbability_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (e : Fin 2) :
    0 ≤ dyadicSquarefreeParityProbability q e := by
  exact div_nonneg (pow_nonneg hq0 _) (by linarith)

theorem dyadicEulerResidualProbability_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℕ) :
    0 ≤ dyadicEulerResidualProbability q j := by
  apply dyadicEulerGeometricProbability_nonneg (sq_nonneg q) ?_ j
  nlinarith [sq_nonneg q]

/-- Exact parity--residual factorization of the geometric Euler law. -/
theorem dyadicEulerGeometricProbability_parity_factor
    {q : ℝ} (hq0 : 0 ≤ q) (e : Fin 2) (j : ℕ) :
    dyadicEulerGeometricProbability q ((e : ℕ) + 2 * j) =
      dyadicSquarefreeParityProbability q e *
        dyadicEulerResidualProbability q j := by
  have hplus : 1 + q ≠ 0 := ne_of_gt (by linarith)
  unfold dyadicEulerResidualProbability dyadicEulerGeometricProbability
    dyadicSquarefreeParityProbability
  rw [pow_add, pow_mul]
  field_simp [hplus]
  ring

/-- The two parity probabilities have total mass one. -/
theorem sum_dyadicSquarefreeParityProbability
    {q : ℝ} (hq0 : 0 ≤ q) :
    ∑ e : Fin 2, dyadicSquarefreeParityProbability q e = 1 := by
  have hplus : 1 + q ≠ 0 := ne_of_gt (by linarith)
  rw [Fin.sum_univ_two]
  simp only [dyadicSquarefreeParityProbability, Fin.val_zero, pow_zero,
    Fin.val_one, pow_one]
  field_simp [hplus]

/-- The geometric Euler probabilities have total mass one. -/
theorem tsum_dyadicEulerGeometricProbability
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, dyadicEulerGeometricProbability q k = 1 := by
  rw [show (fun k : ℕ => dyadicEulerGeometricProbability q k) =
      fun k => (1 - q) * q ^ k by rfl,
    tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hminus : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  field_simp [hminus]

/-- The residual probabilities have total mass one. -/
theorem tsum_dyadicEulerResidualProbability
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' j : ℕ, dyadicEulerResidualProbability q j = 1 := by
  have hq2 : q ^ 2 < 1 := by nlinarith [sq_nonneg q]
  exact tsum_dyadicEulerGeometricProbability (sq_nonneg q) hq2

/-- Positive amplitude of the geometric Euler state. -/
def dyadicEulerGeometricAmplitude (q : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (dyadicEulerGeometricProbability q k)

/-- Signed squarefree parity amplitude; the sign is the local Moebius phase. -/
def dyadicSquarefreeSignedParityAmplitude (q : ℝ) (e : Fin 2) : ℝ :=
  (-1 : ℝ) ^ (e : ℕ) * Real.sqrt (dyadicSquarefreeParityProbability q e)

/-- Positive amplitude of the strict-right residual Euler state. -/
def dyadicEulerResidualAmplitude (q : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (dyadicEulerResidualProbability q j)

/-- Exact signed coefficient factorization under `k = e + 2j`. -/
theorem dyadicEulerGeometricAmplitude_parity_factor
    {q : ℝ} (hq0 : 0 ≤ q) (e : Fin 2) (j : ℕ) :
    (-1 : ℝ) ^ (e : ℕ) *
        dyadicEulerGeometricAmplitude q ((e : ℕ) + 2 * j) =
      dyadicSquarefreeSignedParityAmplitude q e *
        dyadicEulerResidualAmplitude q j := by
  rw [dyadicEulerGeometricAmplitude, dyadicSquarefreeSignedParityAmplitude,
    dyadicEulerResidualAmplitude,
    dyadicEulerGeometricProbability_parity_factor hq0 e j,
    Real.sqrt_mul (dyadicSquarefreeParityProbability_nonneg hq0 e)]
  ring

/-! ### Compatibility with the bounded Weyl orbit carrying the logarithmic generator -/

/-- Geometric Euler amplitude decorated by its logarithmic Weyl character. -/
def dyadicEulerWeylMode
    (q logScale : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (dyadicEulerGeometricAmplitude q k : ℂ) *
    HTGeometry.scalarWeylCharacter ((k : ℝ) * logScale) z

/-- Signed squarefree parity amplitude with its parity Weyl character. -/
def dyadicSquarefreeWeylMode
    (q logScale : ℝ) (e : Fin 2) (z : ℂ) : ℂ :=
  (dyadicSquarefreeSignedParityAmplitude q e : ℂ) *
    HTGeometry.scalarWeylCharacter ((e : ℕ) * logScale) z

/-- Strict-right residual amplitude with the even residual Weyl character. -/
def dyadicEulerResidualWeylMode
    (q logScale : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  (dyadicEulerResidualAmplitude q j : ℂ) *
    HTGeometry.scalarWeylCharacter ((2 * j : ℕ) * logScale) z

/-- The source unitary factors the complete bounded Weyl mode, not only its probability. -/
theorem dyadicEulerWeylMode_parity_factor
    {q : ℝ} (hq0 : 0 ≤ q) (logScale : ℝ)
    (e : Fin 2) (j : ℕ) (z : ℂ) :
    (((-1 : ℝ) ^ (e : ℕ) : ℝ) : ℂ) *
        dyadicEulerWeylMode q logScale ((e : ℕ) + 2 * j) z =
      dyadicSquarefreeWeylMode q logScale e z *
        dyadicEulerResidualWeylMode q logScale j z := by
  have hamp := congrArg (fun x : ℝ => (x : ℂ))
    (dyadicEulerGeometricAmplitude_parity_factor hq0 e j)
  push_cast at hamp
  have hcharge :
      ((((e : ℕ) + 2 * j : ℕ) : ℝ) * logScale) =
        ((e : ℕ) : ℝ) * logScale + ((2 * j : ℕ) : ℝ) * logScale := by
    push_cast
    ring
  rw [dyadicEulerWeylMode, dyadicSquarefreeWeylMode,
    dyadicEulerResidualWeylMode, hcharge,
    HTGeometry.scalarWeylCharacter_add_charge]
  calc
    ((((-1 : ℝ) ^ (e : ℕ) : ℝ) : ℂ) *
        (((dyadicEulerGeometricAmplitude q ((e : ℕ) + 2 * j) : ℝ) : ℂ) *
          (HTGeometry.scalarWeylCharacter (((e : ℕ) : ℝ) * logScale) z *
            HTGeometry.scalarWeylCharacter (((2 * j : ℕ) : ℝ) * logScale) z))) =
      ((((dyadicSquarefreeSignedParityAmplitude q e : ℝ) *
          dyadicEulerResidualAmplitude q j : ℝ)) : ℂ) *
        (HTGeometry.scalarWeylCharacter (((e : ℕ) : ℝ) * logScale) z *
          HTGeometry.scalarWeylCharacter (((2 * j : ℕ) : ℝ) * logScale) z) := by
            push_cast
            rw [← mul_assoc, hamp]
    _ = _ := by push_cast; ring

/-- Wigner--Smith charge of one exponent mode. -/
def dyadicEulerWignerSmithCharge
    (logScale : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  HTGeometry.scalarWeylWignerSmithValue ((k : ℝ) * logScale) t

theorem dyadicEulerWignerSmithCharge_eq
    (logScale : ℝ) (k : ℕ) (t : ℝ) :
    dyadicEulerWignerSmithCharge logScale k t =
      (((k : ℝ) * logScale : ℝ) : ℂ) := by
  exact HTGeometry.scalarWeylWignerSmithValue_eq ((k : ℝ) * logScale) t

/-- The unbounded logarithmic generator is additive across the dyadic source split. -/
theorem dyadicEulerWignerSmithCharge_parity_split
    (logScale : ℝ) (e : Fin 2) (j : ℕ) (t : ℝ) :
    dyadicEulerWignerSmithCharge logScale ((e : ℕ) + 2 * j) t =
      dyadicEulerWignerSmithCharge logScale (e : ℕ) t +
        dyadicEulerWignerSmithCharge logScale (2 * j) t := by
  simp only [dyadicEulerWignerSmithCharge_eq]
  push_cast
  ring

theorem dyadicEulerGeometricAmplitude_sq
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    dyadicEulerGeometricAmplitude q k ^ 2 =
      dyadicEulerGeometricProbability q k := by
  exact Real.sq_sqrt (dyadicEulerGeometricProbability_nonneg hq0 hq1 k)

theorem dyadicSquarefreeSignedParityAmplitude_sq
    {q : ℝ} (hq0 : 0 ≤ q) (e : Fin 2) :
    dyadicSquarefreeSignedParityAmplitude q e ^ 2 =
      dyadicSquarefreeParityProbability q e := by
  rw [dyadicSquarefreeSignedParityAmplitude, mul_pow,
    Real.sq_sqrt (dyadicSquarefreeParityProbability_nonneg hq0 e)]
  have hsign : ((-1 : ℝ) ^ (e : ℕ)) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign, one_mul]

theorem dyadicEulerResidualAmplitude_sq
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℕ) :
    dyadicEulerResidualAmplitude q j ^ 2 =
      dyadicEulerResidualProbability q j := by
  exact Real.sq_sqrt (dyadicEulerResidualProbability_nonneg hq0 hq1 j)

theorem sum_dyadicSquarefreeSignedParityAmplitude_sq
    {q : ℝ} (hq0 : 0 ≤ q) :
    ∑ e : Fin 2, dyadicSquarefreeSignedParityAmplitude q e ^ 2 = 1 := by
  simp_rw [dyadicSquarefreeSignedParityAmplitude_sq hq0]
  exact sum_dyadicSquarefreeParityProbability hq0

theorem tsum_dyadicEulerGeometricAmplitude_sq
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, dyadicEulerGeometricAmplitude q k ^ 2 = 1 := by
  simp_rw [dyadicEulerGeometricAmplitude_sq hq0 hq1.le]
  exact tsum_dyadicEulerGeometricProbability hq0 hq1

theorem tsum_dyadicEulerResidualAmplitude_sq
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' j : ℕ, dyadicEulerResidualAmplitude q j ^ 2 = 1 := by
  simp_rw [dyadicEulerResidualAmplitude_sq hq0 hq1.le]
  exact tsum_dyadicEulerResidualProbability hq0 hq1

/-- Closed form for the mean of one geometric Euler exponent. -/
def dyadicEulerGeometricMean (q : ℝ) : ℝ := q / (1 - q)

/-- Closed form for the mean of the squarefree parity bit. -/
def dyadicSquarefreeParityMean (q : ℝ) : ℝ := q / (1 + q)

/-- Closed form for the variance of one geometric Euler exponent. -/
def dyadicEulerGeometricVariance (q : ℝ) : ℝ := q / (1 - q) ^ 2

/-- Closed form for the variance of the squarefree parity bit. -/
def dyadicSquarefreeParityVariance (q : ℝ) : ℝ := q / (1 + q) ^ 2

/-- Exact logarithmic-mean reconstruction `K = epsilon + 2J`. -/
theorem dyadicEulerGeometricMean_split
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    dyadicEulerGeometricMean q =
      dyadicSquarefreeParityMean q +
        2 * dyadicEulerGeometricMean (q ^ 2) := by
  have hminus : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hplus : 1 + q ≠ 0 := ne_of_gt (by linarith)
  have hsq : 1 - q ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg q])
  unfold dyadicEulerGeometricMean dyadicSquarefreeParityMean
  field_simp [hminus, hplus, hsq]
  ring

/-- Exact centered Fisher-variance reconstruction under the dyadic source split. -/
theorem dyadicEulerGeometricVariance_split
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    dyadicEulerGeometricVariance q =
      dyadicSquarefreeParityVariance q +
        4 * dyadicEulerGeometricVariance (q ^ 2) := by
  have hminus : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hplus : 1 + q ≠ 0 := ne_of_gt (by linarith)
  have hsq : 1 - q ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg q])
  unfold dyadicEulerGeometricVariance dyadicSquarefreeParityVariance
  field_simp [hminus, hplus, hsq]
  ring

/-- The same variance split after applying an arbitrary tangent scale. -/
theorem dyadicEulerScaledVariance_split
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c : ℝ) :
    c ^ 2 * dyadicEulerGeometricVariance q =
      c ^ 2 * dyadicSquarefreeParityVariance q +
        (2 * c) ^ 2 * dyadicEulerGeometricVariance (q ^ 2) := by
  rw [dyadicEulerGeometricVariance_split hq0 hq1]
  ring

theorem primeSchurWeight_lt_one
    {sigma : ℝ} (hsigma : 0 < sigma) (p : Nat.Primes) :
    primeSchurWeight sigma p < 1 := by
  rw [primeSchurWeight, Real.exp_lt_one_iff]
  have hp : 1 < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  nlinarith

/-- Actual prime specialization of the exact local source factorization. -/
theorem primeEulerGeometricProbability_parity_factor
    (sigma : ℝ) (p : Nat.Primes)
    (e : Fin 2) (j : ℕ) :
    dyadicEulerGeometricProbability (primeSchurWeight sigma p)
        ((e : ℕ) + 2 * j) =
      dyadicSquarefreeParityProbability (primeSchurWeight sigma p) e *
        dyadicEulerResidualProbability (primeSchurWeight sigma p) j := by
  exact dyadicEulerGeometricProbability_parity_factor
    (primeSchurWeight_pos sigma p).le e j

/-- Actual-prime specialization of the complete amplitude--Weyl factorization. -/
theorem primeEulerWeylMode_parity_factor
    (sigma : ℝ) (p : Nat.Primes) (e : Fin 2) (j : ℕ) (z : ℂ) :
    (((-1 : ℝ) ^ (e : ℕ) : ℝ) : ℂ) *
        dyadicEulerWeylMode (primeSchurWeight sigma p) (Real.log (p : ℝ))
          ((e : ℕ) + 2 * j) z =
      dyadicSquarefreeWeylMode (primeSchurWeight sigma p) (Real.log (p : ℝ)) e z *
        dyadicEulerResidualWeylMode (primeSchurWeight sigma p)
          (Real.log (p : ℝ)) j z := by
  exact dyadicEulerWeylMode_parity_factor
    (primeSchurWeight_pos sigma p).le (Real.log (p : ℝ)) e j z

end RHTower
