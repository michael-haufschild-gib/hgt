import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder

/-!
# Exact finite decomposition of mixed Euler deletion

Subtracting unit deletion removes the ordinary mixed source. The principal power
terms cancel exactly, and the two half endpoints are retained before multiplication.
The result isolates the arithmetic remainder series and a terminal error.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- Principal-integral contribution to an ordinary power sum. -/
def powerMain (s : ℂ) (N : ℕ) : ℂ := (N : ℂ) ^ (1 - s) / (1 - s)

/-- The real diagonal exponent, written without a real-to-complex conversion. -/
def diagonalExponent (s : ℂ) : ℂ := s + star s

/-- The quadratic dilation power. -/
def quadraticPower (s : ℂ) (p : ℕ) : ℂ := (p : ℂ) ^ (2 - diagonalExponent s)

/-- The half-endpoint dilation power. -/
def boundaryPower (s : ℂ) (p : ℕ) : ℂ := (p : ℂ) ^ (1 - diagonalExponent s)

/-- Exact main term, half endpoint, and actual remainder at every cutoff. -/
theorem rawPrefix_decomposition (s : ℂ) (N : ℕ) :
    rawPrefix s N = riemannZeta s + powerMain s N + kernel s N / 2 + powerSumRemainder s N := by
  dsimp [powerMain, powerSumRemainder]
  ring

/-- Positive-integer Euler amplitude as a single complex power. -/
theorem amplitude_eq_cpow (s : ℂ) {p : ℕ} (hp : 0 < p) :
    amplitude s p = (p : ℂ) ^ (1 - s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (by exact_mod_cast hp.ne')]
  simp [amplitude, kernel]

/-- Complex powers preserve multiplication of natural bases. -/
theorem nat_mul_cpow (p N : ℕ) (z : ℂ) :
    ((p * N : ℕ) : ℂ) ^ z = (p : ℂ) ^ z * (N : ℂ) ^ z := by
  simpa only [Nat.cast_mul, Complex.ofReal_natCast] using
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg N) z

/-- Principal-integral contributions scale by the Euler amplitude. -/
theorem powerMain_mul (s : ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    powerMain s (p * N) = amplitude s p * powerMain s N := by
  rw [powerMain, nat_mul_cpow, amplitude_eq_cpow s hp, powerMain]
  ring

/-- Conjugation of the elementary principal contribution. -/
theorem star_powerMain (s : ℂ) (N : ℕ) : star (powerMain s N) = powerMain (star s) N := by
  simp only [powerMain, star_div₀, star_nat_cpow, star_sub, star_one]

/-- Conjugation of ordinary positive-integer weights. -/
theorem star_kernel (s : ℂ) (N : ℕ) : star (kernel s N) = kernel (star s) N := by
  simp only [kernel, star_nat_cpow, star_neg]

/-- Product of a weight and a principal endpoint at a positive cutoff. -/
theorem kernel_mul_star_powerMain (s : ℂ) {N : ℕ} (hN : 0 < N) :
    kernel s N * star (powerMain s N) =
      kernel (diagonalExponent s - 1) N / (1 - star s) := by
  rw [star_powerMain, powerMain, ← mul_div_assoc, kernel, kernel,
    ← Complex.cpow_add _ _ (by exact_mod_cast hN.ne')]
  congr 2
  dsimp [diagonalExponent]
  ring

/-- The ordinary diagonal weight is the product with its conjugate. -/
theorem kernel_mul_star_kernel (s : ℂ) {N : ℕ} (hN : 0 < N) :
    kernel s N * star (kernel s N) = kernel (diagonalExponent s) N := by
  rw [star_kernel, kernel, kernel, kernel,
    ← Complex.cpow_add _ _ (by exact_mod_cast hN.ne')]
  congr 1
  dsimp [diagonalExponent]
  ring

/-- The product of two principal amplitudes is the quadratic dilation power. -/
theorem amplitude_mul_star_amplitude (s : ℂ) {p : ℕ} (hp : 0 < p) :
    amplitude s p * star (amplitude s p) = quadraticPower s p := by
  rw [amplitude_eq_cpow s hp, star_nat_cpow,
    ← Complex.cpow_add _ _ (by exact_mod_cast hp.ne')]
  unfold quadraticPower diagonalExponent
  congr 1
  simp only [star_sub, star_one]
  ring

/-- Mixing an amplitude with a conjugate weight gives the boundary dilation power. -/
theorem amplitude_mul_star_kernel (s : ℂ) {p : ℕ} (hp : 0 < p) :
    amplitude s p * star (kernel s p) = boundaryPower s p := by
  rw [amplitude_eq_cpow s hp, star_kernel, kernel,
    ← Complex.cpow_add _ _ (by exact_mod_cast hp.ne')]
  unfold boundaryPower diagonalExponent
  congr 1
  ring

/-- Exact expansion of the arithmetic endpoint pairing; every remainder is retained. -/
theorem endpointPairing_decomposition (s : ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    amplitude s p * dilationEndpointPairing s p N =
      amplitude s p * star (riemannZeta s) * rawPrefix s N +
      quadraticPower s p * rawPrefix (diagonalExponent s - 1) N / (1 - star s) +
      boundaryPower s p * rawPrefix (diagonalExponent s) N / 2 + remainderPrefix s p N := by
  unfold dilationEndpointPairing remainderPrefix rawPrefix
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  change amplitude s p * (kernel s (n + 1) * star (rawPrefix s (p * (n + 1)))) = _
  rw [rawPrefix_decomposition s (p * (n + 1))]
  simp only [star_add, star_div₀, star_ofNat, powerMain_mul s hp, kernel_mul, star_mul]
  have hmain := kernel_mul_star_powerMain s (N := n + 1) (by omega)
  have hdiag := kernel_mul_star_kernel s (N := n + 1) (by omega)
  have hscale := amplitude_mul_star_amplitude s hp
  have hboundary := amplitude_mul_star_kernel s hp
  calc
    _ = (amplitude s p * star (riemannZeta s)) * kernel s (n + 1) +
        (amplitude s p * star (amplitude s p)) *
          (kernel s (n + 1) * star (powerMain s (n + 1))) +
        (amplitude s p * star (kernel s p)) *
          (kernel s (n + 1) * star (kernel s (n + 1))) / 2 +
        amplitude s p * (kernel s (n + 1) * star (powerSumRemainder s (p * (n + 1)))) := by ring
    _ = _ := by rw [hmain, hdiag, hscale, hboundary]; ring

/-- Unit deletion has identically zero mixed prefix. -/
theorem mixedPrefix_one (s Z : ℂ) (N : ℕ) : mixedPrefix s Z 1 N = 0 := by
  simp [mixedPrefix, centeredTail, amplitude, kernel]

/-- Subtracting unit deletion eliminates the ordinary mixed source exactly. -/
theorem mixedPrefix_sub_unit (s : ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    mixedPrefix s (riemannZeta s) p (p * N) =
      (amplitude s p - 1) * (riemannZeta s * star (riemannZeta s)) +
      (quadraticPower s p * rawPrefix (diagonalExponent s - 1) N -
        rawPrefix (diagonalExponent s - 1) (p * N)) / (1 - star s) +
      (boundaryPower s p * rawPrefix (diagonalExponent s) N -
        rawPrefix (diagonalExponent s) (p * N)) / 2 +
      remainderPrefix s p N - remainderPrefix s 1 (p * N) +
      centeredTail s (riemannZeta s) p (p * N) *
        star (rawPrefix s (p * N) - riemannZeta s) := by
  have h := mixedPrefix_eq_ordinary_endpoint_pairing s (riemannZeta s) hp N
  have h1 := mixedPrefix_eq_ordinary_endpoint_pairing s (riemannZeta s) (p := 1) (by omega) (p * N)
  rw [mixedPrefix_one] at h1
  simp only [one_mul] at h1
  rw [endpointPairing_decomposition s hp N] at h
  rw [endpointPairing_decomposition s (p := 1) (by omega) (p * N)] at h1
  simp only [quadraticPower, boundaryPower, Complex.one_cpow, Nat.cast_one,
    amplitude, kernel, Complex.one_cpow, mul_one] at h1
  rw [centeredTail, Nat.mul_div_cancel_left N hp, star_sub]
  linear_combination h - h1

/-- Exact centered deletion at a complete-cell endpoint. -/
theorem centeredTail_block (s : ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    centeredTail s (riemannZeta s) p (p * N) =
      (kernel s p - amplitude s p) * kernel s N / 2 +
      powerSumRemainder s (p * N) - amplitude s p * powerSumRemainder s N := by
  rw [centeredTail, Nat.mul_div_cancel_left N hp,
    rawPrefix_decomposition s (p * N), rawPrefix_decomposition s N,
    powerMain_mul s hp, kernel_mul]
  ring

/-- The conjugate amplitude with an ordinary weight has the same boundary power. -/
theorem kernel_mul_star_amplitude (s : ℂ) {p : ℕ} (hp : 0 < p) :
    kernel s p * star (amplitude s p) = boundaryPower s p := by
  rw [amplitude_eq_cpow s hp, star_nat_cpow, kernel,
    ← Complex.cpow_add _ _ (by exact_mod_cast hp.ne')]
  unfold boundaryPower diagonalExponent
  congr 1
  simp only [star_sub, star_one]
  ring

/-- Endpoint error after its half-endpoint cancellation is retained explicitly. -/
def endpointError (s : ℂ) (p N : ℕ) : ℂ :=
  centeredTail s (riemannZeta s) p (p * N) *
      star (rawPrefix s (p * N) - riemannZeta s) +
    (quadraticPower s p - boundaryPower s p) * kernel (diagonalExponent s - 1) N /
      2 / (1 - star s)

/-- The endpoint error contains only decaying remainder products. -/
theorem endpointError_decomposition (s : ℂ) {p N : ℕ} (hp : 0 < p) (hN : 0 < N) :
    endpointError s p N =
      centeredTail s (riemannZeta s) p (p * N) *
        (star (kernel s (p * N)) / 2 + star (powerSumRemainder s (p * N))) +
      powerSumRemainder s (p * N) * star (powerMain s (p * N)) -
      amplitude s p * powerSumRemainder s N * star (powerMain s (p * N)) := by
  have hcross : (kernel s p - amplitude s p) * kernel s N / 2 *
      star (powerMain s (p * N)) =
      (boundaryPower s p - quadraticPower s p) * kernel (diagonalExponent s - 1) N /
        2 / (1 - star s) := by
    rw [powerMain_mul s hp, star_mul]
    calc
      _ = (kernel s p * star (amplitude s p) - amplitude s p * star (amplitude s p)) *
          (kernel s N * star (powerMain s N)) / 2 := by ring
      _ = _ := by rw [kernel_mul_star_amplitude s hp, amplitude_mul_star_amplitude s hp,
        kernel_mul_star_powerMain s hN]; ring
  have hu : star (rawPrefix s (p * N) - riemannZeta s) =
      star (powerMain s (p * N)) + star (kernel s (p * N)) / 2 +
        star (powerSumRemainder s (p * N)) := by
    rw [rawPrefix_decomposition]
    simp only [star_sub, star_add, star_div₀, star_ofNat]
    ring
  rw [endpointError, hu, centeredTail_block s hp N]
  linear_combination hcross

/-- The first power-sum difference after the two half endpoints cancel. -/
def renormalizedPowerDifference (s : ℂ) (p N : ℕ) : ℂ :=
  quadraticPower s p * rawPrefix (diagonalExponent s - 1) N -
    rawPrefix (diagonalExponent s - 1) (p * N) -
    (quadraticPower s p - boundaryPower s p) * kernel (diagonalExponent s - 1) N / 2

/-- The renormalized power difference is a constant plus actual decaying remainders. -/
theorem renormalizedPowerDifference_decomposition (s : ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    renormalizedPowerDifference s p N =
      (quadraticPower s p - 1) * riemannZeta (diagonalExponent s - 1) +
      quadraticPower s p * powerSumRemainder (diagonalExponent s - 1) N -
      powerSumRemainder (diagonalExponent s - 1) (p * N) := by
  have hmain : amplitude (diagonalExponent s - 1) p = quadraticPower s p := by
    rw [amplitude_eq_cpow _ hp]
    unfold quadraticPower
    congr 1
    ring
  have hkernel : kernel (diagonalExponent s - 1) p = boundaryPower s p := by
    unfold kernel boundaryPower
    congr 1
    ring
  rw [renormalizedPowerDifference, rawPrefix_decomposition _ N,
    rawPrefix_decomposition _ (p * N), powerMain_mul _ hp, kernel_mul, hmain, hkernel]
  ring

/-- Exact decomposition with its vanishing endpoint error isolated. -/
theorem mixedPrefix_decomposition_with_error (s : ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    mixedPrefix s (riemannZeta s) p (p * N) =
      (amplitude s p - 1) * (riemannZeta s * star (riemannZeta s)) +
      renormalizedPowerDifference s p N / (1 - star s) +
      (boundaryPower s p * rawPrefix (diagonalExponent s) N -
        rawPrefix (diagonalExponent s) (p * N)) / 2 +
      remainderPrefix s p N - remainderPrefix s 1 (p * N) + endpointError s p N := by
  rw [mixedPrefix_sub_unit s hp N, renormalizedPowerDifference, endpointError]
  ring

end RHTower.DeletionMixedRefinement
