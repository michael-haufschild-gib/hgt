import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation
import GaloisForLFunctions.RHTower.WeldRateLattice

/-!
# All-even Jacobi signs in the semilocal Sonin source

This module isolates the exact closed Fourier kernel that drives the semilocal all-even
Jacobi residue tower.  It proves the alternating sign at every positive even degree, the
strict positive-weight packet theorem, and the unique-factorization fact excluding every
nontrivial zero prime-log frequency.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

/-- The positive normalization appearing in the archimedean Jacobi Fourier transform. -/
def semilocalArchimedeanJacobiNormalization (n : ℕ) : ℝ :=
  Real.sqrt ((Nat.factorial (2 * n) : ℝ)) /
    ((2 : ℝ) ^ n * (Nat.factorial n : ℝ))

theorem semilocalArchimedeanJacobiNormalization_pos (n : ℕ) :
    0 < semilocalArchimedeanJacobiNormalization n := by
  unfold semilocalArchimedeanJacobiNormalization
  exact div_pos (Real.sqrt_pos.2 (by positivity)) (mul_pos (by positivity) (by positivity))

/-- The closed Fourier transform predicted by the archimedean Jacobi recurrence. -/
def semilocalArchimedeanJacobiFourierClosedForm (n : ℕ) (t : ℝ) : ℂ :=
  Complex.I ^ n * semilocalArchimedeanJacobiNormalization n *
    semilocalArchimedeanCharacteristic t * Real.tanh t ^ n

/-- At even degree the complex phase is the real alternating sign. -/
theorem semilocalArchimedeanJacobiFourierClosedForm_even (k : ℕ) (t : ℝ) :
    semilocalArchimedeanJacobiFourierClosedForm (2 * k) t =
      ((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k) : ℝ) := by
  rw [semilocalArchimedeanJacobiFourierClosedForm, pow_mul, Complex.I_sq]
  norm_cast

/-- The real all-even Fourier kernel. -/
def semilocalArchimedeanEvenJacobiKernel (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
    semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k)

theorem semilocalArchimedeanCharacteristic_pos (t : ℝ) :
    0 < semilocalArchimedeanCharacteristic t :=
  Real.rpow_pos_of_pos (Real.cosh_pos t) (-(1 : ℝ) / 2)

theorem tanh_even_pow_pos {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t ≠ 0) :
    0 < Real.tanh t ^ (2 * k) := by
  have htanh : Real.tanh t ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hsinh : Real.sinh t ≠ 0 := by
      simpa using Real.sinh_strictMono.injective.ne ht
    exact div_ne_zero hsinh (Real.cosh_pos t).ne'
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero htanh) hk

/-- Every nonzero frequency has the rigid sign `(-1)^k` at positive even degree `2k`. -/
theorem semilocalArchimedeanEvenJacobiKernel_signed_pos
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t ≠ 0) :
    0 < (-1 : ℝ) ^ k * semilocalArchimedeanEvenJacobiKernel k t := by
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [semilocalArchimedeanEvenJacobiKernel]
  calc
    0 < semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k) :=
      mul_pos
        (mul_pos (semilocalArchimedeanJacobiNormalization_pos _)
          (semilocalArchimedeanCharacteristic_pos t))
        (tanh_even_pow_pos hk ht)
    _ = (-1 : ℝ) ^ k *
        (((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
          semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k))) := by
      rw [← mul_assoc, hsign, one_mul]

/-- A nonempty positive packet of nonzero frequencies retains the same strict alternating sign. -/
theorem semilocalArchimedeanEvenJacobiKernel_weightedPacket_signed_pos
    {ι : Type*} {k : ℕ} (hk : 0 < k) (s : Finset ι) (hs : s.Nonempty)
    (weight frequency : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hfrequency : ∀ i ∈ s, frequency i ≠ 0) :
    0 < (-1 : ℝ) ^ k *
      ∑ i ∈ s, weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_pos hs
  intro i hi
  rw [Finset.mul_sum]
  have hkernel := semilocalArchimedeanEvenJacobiKernel_signed_pos hk (hfrequency i hi)
  nlinarith [hweight i hi]

/-- A finite integer packet on distinct primes has nonzero prime-log frequency unless it is the
zero packet. -/
theorem finitePrimeLogFrequency_ne_zero
    {n : ℕ} (p : Fin n → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (m : Fin n → ℤ) (hm : ∃ i, m i ≠ 0) :
    ∑ i, (m i : ℝ) * Real.log (p i) ≠ 0 := by
  intro hzero
  have hindex : Function.Injective
      (fun i : Fin n => (⟨p i, hprime i⟩ : Nat.Primes)) := by
    intro i j hij
    exact hp (congrArg Subtype.val hij)
  have hLI := primeLog_linearIndependent.comp
    (fun i : Fin n => (⟨p i, hprime i⟩ : Nat.Primes)) hindex
  have hall : ∀ i, m i = 0 := (Fintype.linearIndependent_iff.mp hLI) m (by
    simpa [zsmul_eq_mul] using hzero)
  obtain ⟨i, hi⟩ := hm
  exact hi (hall i)

/-- Finite Poisson packets over distinct prime-log frequencies already satisfy the full
all-even alternating sign law.  The infinite Poisson expansion is obtained by summable passage
from these packets. -/
theorem finitePrimePoissonPacket_evenJacobi_signed_pos
    {ι : Type*} {n k : ℕ} (hk : 0 < k)
    (p : Fin n → ℕ) (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (packet : ι → Fin n → ℤ) (s : Finset ι) (hs : s.Nonempty)
    (hpacket : ∀ j ∈ s, ∃ i, packet j i ≠ 0)
    (weight : ι → ℝ) (hweight : ∀ j ∈ s, 0 < weight j) :
    0 < (-1 : ℝ) ^ k * ∑ j ∈ s, weight j *
      semilocalArchimedeanEvenJacobiKernel k
        (∑ i, (packet j i : ℝ) * Real.log (p i)) := by
  exact semilocalArchimedeanEvenJacobiKernel_weightedPacket_signed_pos hk s hs weight
    (fun j ↦ ∑ i, (packet j i : ℝ) * Real.log (p i)) hweight
    (fun j hj ↦ finitePrimeLogFrequency_ne_zero p hp hprime (packet j) (hpacket j hj))

end GaloisForLFunctions.RHTower
