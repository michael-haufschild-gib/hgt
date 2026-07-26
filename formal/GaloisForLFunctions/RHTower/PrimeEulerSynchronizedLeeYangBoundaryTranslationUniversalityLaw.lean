import GaloisForLFunctions.RHTower.PrimeEulerLeeYangAmplitudeNoGo
import GaloisForLFunctions.RHTower.PrimeWordSynchronizedCluster

/-!
# Prime Euler synchronized Lee-Yang boundary translation

The physical Euler square-root amplitude is exactly one vertical spectral translation of the
centered prime Lee-Yang field. The translation commutes with every finite synchronized prime
product, so the complete cluster zero wall moves rigidly from `Im z = 0` to `Im z = 1/2`,
independently of support size or prime composition.

No Riemann-hypothesis premise, limiting argument, or completed-source factorization occurs.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Primewise square-root Euler normalization is the shift `z ↦ z - I/2`. -/
theorem physicalCenteredEulerLeeYangField_eq_centered_shift
    (p : Nat.Primes) (z : ℂ) :
    _root_.RHTower.physicalCenteredEulerLeeYangField p z =
      _root_.RHTower.centeredPrimeLeeYangField p (z - Complex.I / 2) := by
  rw [_root_.RHTower.physicalCenteredEulerLeeYangField]
  unfold _root_.RHTower.centeredPrimeLeeYangField
    _root_.RHTower.centeredPrimeMark
    _root_.RHTower.primeLeeYangLog
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Product of physical Euler fields on one finite synchronized prime support. -/
def physicalSynchronizedPrimeClusterField
    (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  ∏ p ∈ P, _root_.RHTower.physicalCenteredEulerLeeYangField p z

/-- Physical two-pure-state synchronized prime-cluster partition. -/
def physicalSynchronizedPrimeClusterPartition
    (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  1 + physicalSynchronizedPrimeClusterField P z

/-- The primewise shift survives every finite synchronized product exactly. -/
theorem physicalSynchronizedPrimeClusterField_eq_centered_shift
    (P : Finset Nat.Primes) (z : ℂ) :
    physicalSynchronizedPrimeClusterField P z =
      synchronizedPrimeClusterField P (z - Complex.I / 2) := by
  simp only [physicalSynchronizedPrimeClusterField,
    synchronizedPrimeClusterField,
    physicalCenteredEulerLeeYangField_eq_centered_shift]

/-- The complete physical cluster partition is the translated centered cluster partition. -/
theorem physicalSynchronizedPrimeClusterPartition_eq_centered_shift
    (P : Finset Nat.Primes) (z : ℂ) :
    physicalSynchronizedPrimeClusterPartition P z =
      synchronizedPrimeClusterPartition P (z - Complex.I / 2) := by
  rw [physicalSynchronizedPrimeClusterPartition,
    synchronizedPrimeClusterPartition,
    physicalSynchronizedPrimeClusterField_eq_centered_shift]

/-- Every zero of a nonempty physical synchronized cluster lies on the displaced boundary
`Im z = 1/2`. -/
theorem physicalSynchronizedPrimeClusterPartition_zero_im
    {P : Finset Nat.Primes} (hP : P.Nonempty) {z : ℂ}
    (hz : physicalSynchronizedPrimeClusterPartition P z = 0) :
    z.im = 1 / 2 := by
  rw [physicalSynchronizedPrimeClusterPartition_eq_centered_shift] at hz
  have hzero :=
    synchronizedPrimeClusterPartition_zero_im hP hz
  norm_num [Complex.div_im] at hzero ⊢
  linarith

/-- **Prime Euler synchronized Lee-Yang boundary-translation universality.** Field transport,
partition transport, and the displaced zero wall hold simultaneously for every finite support. -/
theorem primeEuler_synchronizedLeeYang_boundaryTranslationUniversality
    (P : Finset Nat.Primes) (z : ℂ) :
    physicalSynchronizedPrimeClusterField P z =
        synchronizedPrimeClusterField P (z - Complex.I / 2) ∧
      physicalSynchronizedPrimeClusterPartition P z =
        synchronizedPrimeClusterPartition P (z - Complex.I / 2) ∧
      (P.Nonempty →
        physicalSynchronizedPrimeClusterPartition P z = 0 →
          z.im = 1 / 2) := by
  exact ⟨physicalSynchronizedPrimeClusterField_eq_centered_shift P z,
    physicalSynchronizedPrimeClusterPartition_eq_centered_shift P z,
    fun hP hz =>
      physicalSynchronizedPrimeClusterPartition_zero_im hP hz⟩

end

end GaloisForLFunctions.RHTower
