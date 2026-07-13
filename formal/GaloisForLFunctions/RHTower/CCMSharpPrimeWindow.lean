import GaloisForLFunctions.RHTower.CCMCriticalMellinCompletedError

/-!
# A sharp moving-prime window as one completed-error increment

The rectangular tent is not needed to expose the local arithmetic obstruction.  A single sharp
multiplicative prime window is exactly one first difference of the completed critical-Mellin
error, up to an explicit decaying endpoint term.  Replacing the completed error by its Chebyshev
potential gives the same identity on the nonnegative logarithmic ray.

All sums below are finite and source-defined.  No Xi zero or divisor datum enters the definitions.
-/

open scoped BigOperators
open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- Weighted von Mangoldt mass up to logarithmic height `h`. -/
def criticalMellinPrimeMass (h : ℝ) : ℝ :=
  ∑ k ∈ Icc 0 ⌊Real.exp h⌋₊,
    ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k

/-- The completed critical-Mellin error is its polar profile minus the weighted prime mass. -/
theorem criticalMellinCompletedError_eq_polar_sub_primeMass (h : ℝ) :
    criticalMellinCompletedError h =
      4 * Real.sinh (h / 2) - criticalMellinPrimeMass h := rfl

/-- Prime mass in the sharp multiplicative window `exp(x-L) < k ≤ exp x`, expressed as the
difference of two finite cumulative masses.  This convention gives an exact endpoint identity. -/
def sharpMovingPrimeWindowMass (L x : ℝ) : ℝ :=
  criticalMellinPrimeMass x - criticalMellinPrimeMass (x - L)

/-- The cumulative difference is literally the finite prime-power sum in the sharp
multiplicative window. -/
theorem sharpMovingPrimeWindowMass_eq_sum_Ioc
    {L x : ℝ} (hL : 0 ≤ L) :
    sharpMovingPrimeWindowMass L x =
      ∑ k ∈ Ioc ⌊Real.exp (x - L)⌋₊ ⌊Real.exp x⌋₊,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k := by
  let f : ℕ → ℝ := fun k =>
    ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k
  let a : ℕ := ⌊Real.exp (x - L)⌋₊
  let b : ℕ := ⌊Real.exp x⌋₊
  have hab : a ≤ b := Nat.floor_mono ((Real.exp_le_exp).2 (by linarith))
  have hIcc : ∀ m : ℕ, Icc 0 m = range (m + 1) := by
    intro m
    ext k
    simp only [mem_Icc, zero_le, true_and, mem_range]
    omega
  have hIoc : Ioc a b = Ico (a + 1) (b + 1) := by
    ext k
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [sharpMovingPrimeWindowMass, criticalMellinPrimeMass,
    criticalMellinPrimeMass]
  change (∑ k ∈ Icc 0 b, f k) - ∑ k ∈ Icc 0 a, f k =
    ∑ k ∈ Ioc a b, f k
  rw [hIcc, hIcc, hIoc, Finset.sum_Ico_eq_sub f (Nat.succ_le_succ hab)]

/-- Arithmetic form of the sharp source: at `x = log n`, the finite window is exactly
`n * exp(-L) < k ≤ n`. -/
theorem sharpMovingPrimeWindowMass_logSample_eq_sum_Ioc
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n) :
    sharpMovingPrimeWindowMass L (Real.log n) =
      ∑ k ∈ Ioc ⌊(n : ℝ) * Real.exp (-L)⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k := by
  rw [sharpMovingPrimeWindowMass_eq_sum_Ioc hL]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper : ⌊Real.exp (Real.log n)⌋₊ = n := by
    rw [Real.exp_log hnreal, Nat.floor_natCast]
  have hlower : Real.exp (Real.log n - L) =
      (n : ℝ) * Real.exp (-L) := by
    rw [show Real.log n - L = Real.log n + -L by ring,
      Real.exp_add, Real.exp_log hnreal]
  rw [hupper, hlower]

/-- The source-defined sharp prime--polar coefficient at logarithmic scale `x`. -/
def sharpPrimePolarCoefficient (L x : ℝ) : ℝ :=
  4 * (Real.exp (x / 2) - Real.exp ((x - L) / 2)) -
    2 * sharpMovingPrimeWindowMass L x

/-- The decaying endpoint correction forced by replacing `sinh` with its growing exponential
channel. -/
def sharpPrimeWindowEndpointCorrection (L x : ℝ) : ℝ :=
  4 * Real.exp (-x / 2) * (Real.exp (L / 2) - 1)

/-- **Sharp-window completed-error law.**  The prime--polar coefficient is exactly twice one
completed-error increment, minus the explicit decaying endpoint correction. -/
theorem sharpPrimePolarCoefficient_eq_completedErrorIncrement (L x : ℝ) :
    sharpPrimePolarCoefficient L x =
      2 * (criticalMellinCompletedError x -
        criticalMellinCompletedError (x - L)) -
      sharpPrimeWindowEndpointCorrection L x := by
  rw [sharpPrimePolarCoefficient, sharpMovingPrimeWindowMass,
    criticalMellinCompletedError_eq_polar_sub_primeMass,
    criticalMellinCompletedError_eq_polar_sub_primeMass,
    sharpPrimeWindowEndpointCorrection, Real.sinh_eq, Real.sinh_eq]
  rw [show Real.exp (-((x - L) / 2)) = Real.exp (-x / 2) * Real.exp (L / 2) by
    rw [← Real.exp_add]
    congr 1
    ring]
  ring_nf

/-- The same sharp coefficient written through the source-defined Chebyshev potential. -/
def sharpPrimeChebyshevCoefficient (L x : ℝ) : ℝ :=
  2 * (criticalMellinChebyshevPotential x -
    criticalMellinChebyshevPotential (x - L)) -
  sharpPrimeWindowEndpointCorrection L x

/-- The sharp coefficient after complete removal of the polar values: a first difference of the
normalized Chebyshev error plus the matching causal-integral increment. -/
def sharpPrimeNormalizedChebyshevIncrement (L x : ℝ) : ℝ :=
  -2 * (criticalMellinNormalizedChebyshevError x -
      criticalMellinNormalizedChebyshevError (x - L)) -
    ((∫ u in Set.Ioc (0 : ℝ) x, criticalMellinNormalizedChebyshevError u) -
      ∫ u in Set.Ioc (0 : ℝ) (x - L),
        criticalMellinNormalizedChebyshevError u)

/-- Once the sharp window lies on the nonnegative logarithmic ray, its prime--polar coefficient
is exactly the corresponding first difference of the Chebyshev potential. -/
theorem sharpPrimePolarCoefficient_eq_chebyshevCoefficient
    {L x : ℝ} (hL : 0 ≤ L) (hx : L ≤ x) :
    sharpPrimePolarCoefficient L x = sharpPrimeChebyshevCoefficient L x := by
  rw [sharpPrimePolarCoefficient_eq_completedErrorIncrement,
    sharpPrimeChebyshevCoefficient,
    criticalMellinCompletedError_eq_chebyshevPotential (by linarith : 0 ≤ x),
    criticalMellinCompletedError_eq_chebyshevPotential (by linarith : 0 ≤ x - L)]

/-- **Polar-free sharp-window law.**  On the nonnegative logarithmic ray, the dyadic
prime--polar coefficient is exactly the local value relation carried by the normalized Chebyshev
error.  Both square-root polar values cancel identically; no asymptotic estimate is used. -/
theorem sharpPrimePolarCoefficient_eq_normalizedChebyshevIncrement
    {L x : ℝ} (hL : 0 ≤ L) (hx : L ≤ x) :
    sharpPrimePolarCoefficient L x =
      sharpPrimeNormalizedChebyshevIncrement L x := by
  rw [sharpPrimePolarCoefficient_eq_chebyshevCoefficient hL hx,
    sharpPrimeChebyshevCoefficient, sharpPrimeNormalizedChebyshevIncrement,
    criticalMellinChebyshevPotential_eq_volterraPotential
      (by linarith : 0 ≤ x),
    criticalMellinChebyshevPotential_eq_volterraPotential
      (by linarith : 0 ≤ x - L)]
  rw [criticalMellinChebyshevVolterraPotential,
    criticalMellinChebyshevVolterraPotential,
    sharpPrimeWindowEndpointCorrection]
  have hshift : Real.exp (-(x - L) / 2) =
      Real.exp (-x / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqrtInv : 1 / Real.sqrt (Real.exp x) = Real.exp (-x / 2) := by
    rw [← Real.exp_half, one_div, ← Real.exp_neg]
    congr 1
    ring
  have hsqrtShiftInv : 1 / Real.sqrt (Real.exp (x - L)) =
      Real.exp (-(x - L) / 2) := by
    rw [← Real.exp_half, one_div, ← Real.exp_neg]
    congr 1
    ring
  have htwo : 2 / Real.sqrt (Real.exp x) = 2 * Real.exp (-x / 2) := by
    rw [div_eq_mul_inv, ← one_div, hsqrtInv]
  have htwoShift : 2 / Real.sqrt (Real.exp (x - L)) =
      2 * Real.exp (-(x - L) / 2) := by
    rw [div_eq_mul_inv, ← one_div, hsqrtShiftInv]
  rw [htwo, htwoShift, hshift]
  ring

/-- At an integer logarithmic sample, the elementary polar part is the single square-root term
of the sharp moving-window criterion. -/
theorem sharpPrimePolarCoefficient_logSample
    {L : ℝ} {n : ℕ} (hn : 0 < n) :
    sharpPrimePolarCoefficient L (Real.log n) =
      4 * (1 - Real.exp (-L / 2)) * Real.sqrt n -
        2 * sharpMovingPrimeWindowMass L (Real.log n) := by
  rw [sharpPrimePolarCoefficient]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt hnreal.le, Real.exp_log (Real.sqrt_pos.mpr hnreal)]
  have hshift : Real.exp ((Real.log n - L) / 2) =
      Real.sqrt n * Real.exp (-L / 2) := by
    rw [show (Real.log n - L) / 2 = Real.log n / 2 + (-L / 2) by ring,
      Real.exp_add, hsqrt]
  rw [hsqrt, hshift]
  ring

/-- Fully explicit arithmetic sample: one square-root counterterm minus one finite sharp
von-Mangoldt window. -/
theorem sharpPrimePolarCoefficient_logSample_eq_sum_Ioc
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n) :
    sharpPrimePolarCoefficient L (Real.log n) =
      4 * (1 - Real.exp (-L / 2)) * Real.sqrt n -
        2 * ∑ k ∈ Ioc ⌊(n : ℝ) * Real.exp (-L)⌋₊ n,
          ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k := by
  rw [sharpPrimePolarCoefficient_logSample hn,
    sharpMovingPrimeWindowMass_logSample_eq_sum_Ioc hL hn]

/-- Fixed dyadic specialization.  The whole source coefficient is one weighted von-Mangoldt
interval `n/2 < k ≤ n` and one elementary square-root counterterm. -/
theorem sharpPrimePolarCoefficient_logTwo_logSample
    {n : ℕ} (hn : 0 < n) :
    sharpPrimePolarCoefficient (Real.log 2) (Real.log n) =
      4 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n -
        2 * ∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
          ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k := by
  rw [sharpPrimePolarCoefficient_logSample_eq_sum_Ioc
    (Real.log_nonneg (by norm_num)) hn]
  have hexpLogTwo : Real.exp (Real.log 2) = 2 :=
    Real.exp_log (by norm_num)
  have hexpNegLogTwo : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg, hexpLogTwo]
  have hexpHalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hexpNegHalf : Real.exp (-Real.log 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring,
      Real.exp_neg, hexpHalf]
  rw [hexpNegHalf, hexpNegLogTwo]
  congr 3

/-- The endpoint correction at the dyadic integer sample is an explicit positive decaying
value.  This is the only term separating the square-root main term from one completed-error
finite difference. -/
theorem sharpPrimeWindowEndpointCorrection_logTwo_logSample
    {n : ℕ} (hn : 0 < n) :
    sharpPrimeWindowEndpointCorrection (Real.log 2) (Real.log n) =
      4 * (Real.sqrt 2 - 1) / Real.sqrt n := by
  rw [sharpPrimeWindowEndpointCorrection]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt hnreal.le, Real.exp_log (Real.sqrt_pos.mpr hnreal)]
  have hexpNeg : Real.exp (-Real.log n / 2) = (Real.sqrt n)⁻¹ := by
    rw [show -Real.log n / 2 = -(Real.log n / 2) by ring,
      Real.exp_neg, hsqrt]
  have hhalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  rw [hexpNeg, hhalf, div_eq_mul_inv]
  ring

/-- **Completed-error finite-difference law.**  The excess of the dyadic weighted prime window
above its exact square-root main term is one backward `log 2` difference of the completed
critical-Mellin error, plus a completely explicit positive `O(n⁻¹ᐟ²)` endpoint value. -/
theorem dyadicWeightedPrimeWindow_eq_main_add_completedErrorDifference
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) =
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        (criticalMellinCompletedError (Real.log n - Real.log 2) -
          criticalMellinCompletedError (Real.log n)) +
        2 * (Real.sqrt 2 - 1) / Real.sqrt n := by
  have hnpos : 0 < n := by omega
  have hsource := sharpPrimePolarCoefficient_eq_completedErrorIncrement
    (Real.log 2) (Real.log n)
  rw [sharpPrimePolarCoefficient_logTwo_logSample hnpos,
    sharpPrimeWindowEndpointCorrection_logTwo_logSample hnpos] at hsource
  linear_combination (-1 / 2 : ℝ) * hsource

/-- The requested prime-window estimate is exactly the matching one-sided finite-difference
bound for the completed critical-Mellin error.  No averaging or loss of constants occurs. -/
theorem dyadicWeightedPrimeWindow_upper_iff_completedErrorDifference
    {n : ℕ} (hn : 2 ≤ n) (C epsilon : ℝ) :
    (∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n + C * (n : ℝ) ^ epsilon ↔
      criticalMellinCompletedError (Real.log n - Real.log 2) -
          criticalMellinCompletedError (Real.log n) +
          2 * (Real.sqrt 2 - 1) / Real.sqrt n ≤
        C * (n : ℝ) ^ epsilon := by
  rw [dyadicWeightedPrimeWindow_eq_main_add_completedErrorDifference hn]
  constructor <;> intro h <;> linarith

/-- **Exact value relation for the dyadic RH inequality.**  The desired one-sided upper bound for
the weighted von-Mangoldt window is equivalent, with the same exponent and twice the constant, to
a lower bound for one polar-free normalized-Chebyshev increment. -/
theorem dyadicWeightedPrimeWindow_upper_iff_normalizedChebyshevIncrement
    {n : ℕ} (hn : 2 ≤ n) (C epsilon : ℝ) :
    (∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n + C * (n : ℝ) ^ epsilon ↔
      0 ≤ sharpPrimeNormalizedChebyshevIncrement
          (Real.log 2) (Real.log n) + 2 * C * (n : ℝ) ^ epsilon := by
  have hnpos : 0 < n := by omega
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [← sharpPrimePolarCoefficient_eq_normalizedChebyshevIncrement
      (Real.log_nonneg (by norm_num)) hlog,
    sharpPrimePolarCoefficient_logTwo_logSample hnpos]
  constructor <;> intro h <;> linarith

/-- Endpoint-plus-primitive increment of the unnormalized Chebyshev error across `[n/2,n]`. -/
def dyadicCriticalMellinErrorIncrement (n : ℕ) : ℝ :=
  criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) n /
      Real.sqrt n -
    criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) ((n : ℝ) / 2) /
      Real.sqrt ((n : ℝ) / 2) +
    (1 / 2 : ℝ) *
      ((∫ t in Set.Ioc (1 : ℝ) n,
          criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
            t ^ (-3 / 2 : ℝ)) -
        ∫ t in Set.Ioc (1 : ℝ) ((n : ℝ) / 2),
          criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
            t ^ (-3 / 2 : ℝ))

/-- **Direct Abel value relation.**  The dyadic weighted prime mass is its exact square-root main
term plus one endpoint difference and one primitive difference of the Chebyshev error
`psi(X) - X`.  This is the source identity behind the normalized logarithmic relation above. -/
theorem dyadicWeightedPrimeWindow_eq_criticalMellinErrorIncrement
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) =
      2 * Real.sqrt n - 2 * Real.sqrt ((n : ℝ) / 2) +
        criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) n /
          Real.sqrt n -
        criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) ((n : ℝ) / 2) /
          Real.sqrt ((n : ℝ) / 2) +
        (1 / 2 : ℝ) *
          ((∫ t in Set.Ioc (1 : ℝ) n,
              criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
                t ^ (-3 / 2 : ℝ)) -
            ∫ t in Set.Ioc (1 : ℝ) ((n : ℝ) / 2),
              criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
                t ^ (-3 / 2 : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnrealTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
  have hfull := vonMangoldt_criticalMellinError_identity (n : ℝ)
    (by exact_mod_cast (show 1 ≤ n by omega))
  have hlow := vonMangoldt_criticalMellinError_identity ((n : ℝ) / 2) hhalf
  rw [Nat.floor_natCast] at hfull
  have hexpUpper : Real.exp (Real.log n) = (n : ℝ) :=
    Real.exp_log hnreal
  have hexpLower : Real.exp (Real.log n - Real.log 2) = (n : ℝ) / 2 := by
    rw [Real.exp_sub, Real.exp_log hnreal, Real.exp_log (by norm_num)]
  have hwindow := sharpMovingPrimeWindowMass_eq_sum_Ioc
    (x := Real.log n) (L := Real.log 2) (Real.log_nonneg (by norm_num))
  rw [sharpMovingPrimeWindowMass, criticalMellinPrimeMass,
    criticalMellinPrimeMass, hexpUpper, hexpLower, Nat.floor_natCast] at hwindow
  rw [← hwindow, hfull, hlow]
  ring

/-- Concise form of the Abel relation with the user's exact square-root main term. -/
theorem dyadicWeightedPrimeWindow_eq_main_add_errorIncrement
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) =
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        dyadicCriticalMellinErrorIncrement n := by
  rw [dyadicWeightedPrimeWindow_eq_criticalMellinErrorIncrement hn,
    dyadicCriticalMellinErrorIncrement,
    Real.sqrt_div (Nat.cast_nonneg n)]
  ring

/-- The requested dyadic prime inequality is *exactly* an upper subpower bound for the Abel
endpoint-plus-primitive error increment; no information is lost in either direction. -/
theorem dyadicWeightedPrimeWindow_upper_iff_errorIncrement
    {n : ℕ} (hn : 2 ≤ n) (C epsilon : ℝ) :
    (∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n + C * (n : ℝ) ^ epsilon ↔
      dyadicCriticalMellinErrorIncrement n ≤ C * (n : ℝ) ^ epsilon := by
  rw [dyadicWeightedPrimeWindow_eq_main_add_errorIncrement hn]
  constructor <;> intro h <;> linarith

/-- The open all-epsilon lower estimate is unchanged when the finite prime--polar coefficient is
replaced by the first difference of the Chebyshev potential.  This is the sharp-window form of the
remaining RH proof burden. -/
theorem sharpPrimePolar_subpowerLower_iff_chebyshev
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → L ≤ Real.log n) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ sharpPrimePolarCoefficient L (Real.log n) +
          C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ sharpPrimeChebyshevCoefficient L (Real.log n) +
          C * (n : ℝ) ^ epsilon) := by
  constructor
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [← sharpPrimePolarCoefficient_eq_chebyshevCoefficient hL (hN n hn)]
    exact htail n hn
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [sharpPrimePolarCoefficient_eq_chebyshevCoefficient hL (hN n hn)]
    exact htail n hn

/-- The sharp endpoint correction is nonnegative for nonnegative window width. -/
theorem sharpPrimeWindowEndpointCorrection_nonneg
    {L x : ℝ} (hL : 0 ≤ L) :
    0 ≤ sharpPrimeWindowEndpointCorrection L x := by
  rw [sharpPrimeWindowEndpointCorrection]
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (sub_nonneg.mpr (Real.one_le_exp (by linarith)))

end RHTower
