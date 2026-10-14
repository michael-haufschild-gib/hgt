import GaloisForLFunctions.RHTower.PaperPrimeRotationCoherentLimit
import GaloisForLFunctions.HTGeometry.FinitePhasePacketKernel

/-! # A positive-definite prime interaction kernel from native rotation compressions -/

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

def paperPrimeCoherentKernel (p r : Nat.Primes) : ℂ :=
  (Real.log p : ℂ) * (Real.log r : ℂ) *
    forwardWindowKernel (((Real.log p - Real.log r : ℝ) : ℂ) * Complex.I)

theorem paperPrimeCoherentKernel_self (p : Nat.Primes) :
    paperPrimeCoherentKernel p p = (Real.log p ^ 2 : ℝ) := by
  simp [paperPrimeCoherentKernel, pow_two]

theorem paperPrimeCoherentEnergy_eq_kernel (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    (paperPrimeCoherentEnergy s a : ℂ) =
      ∑ p ∈ s, ∑ r ∈ s, (starRingEnd ℂ (a p) * a r) * paperPrimeCoherentKernel p r := by
  rw [paperPrimeCoherentEnergy, finitePhaseEnergy_eq_kernel]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [show -Real.log r - -Real.log p = Real.log p - Real.log r by ring]
  have he : starRingEnd ℂ (paperPrimeCoherentLimitCoefficient a p) *
      paperPrimeCoherentLimitCoefficient a r =
        (starRingEnd ℂ (a p) * a r) * ((Real.log p : ℂ) * (Real.log r : ℂ)) := by
    simp only [paperPrimeCoherentLimitCoefficient, map_mul, map_neg, Complex.conj_ofReal,
      Complex.conj_I, Complex.ofReal_neg]
    calc
      _ = (starRingEnd ℂ (a p) * a r) * ((Real.log p : ℂ) * (Real.log r : ℂ)) *
          (-(Complex.I * Complex.I)) := by ring
      _ = _ := by simp
  rw [he, paperPrimeCoherentKernel, mul_assoc]

/-- Strict positivity of every finite prime kernel form, with its exact nullspace. -/
theorem paperPrimeCoherentKernel_pos_iff (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    0 < (∑ p ∈ s, ∑ r ∈ s,
      (starRingEnd ℂ (a p) * a r) * paperPrimeCoherentKernel p r).re ↔
        ∃ p ∈ s, a p ≠ 0 := by
  rw [← paperPrimeCoherentEnergy_eq_kernel, Complex.ofReal_re,
    paperPrimeCoherentEnergy_pos_iff]

end
end RHTower
