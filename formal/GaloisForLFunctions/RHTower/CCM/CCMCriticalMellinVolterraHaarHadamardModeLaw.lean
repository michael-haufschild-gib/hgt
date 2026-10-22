import GaloisForLFunctions.HTGeometry.FiniteModalHadamardAlgebra
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinVolterraHaarFinitePacket

/-!
# Hadamard mode law for critical Mellin--Volterra--Haar packets

Pointwise multiplication of two finite critical-Mellin packets creates every pairwise product of
their sampled exponential nodes. Faithfulness of each Volterra--Haar transfer leaves node collision
as the only obstruction: the maximal Hankel block has size d*e exactly when those product nodes are
distinct, and the next block is singular.
-/

open Complex
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

theorem det_criticalMellinVolterraHaarFinitePacket_mul_ne_zero_iff
    {d e : ℕ} {L₁ L₂ : ℝ}
    {amplitude₁ exponent₁ : Fin d → ℂ}
    {amplitude₂ exponent₂ : Fin e → ℂ}
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hexponent₁ : ∀ i, 0 < (exponent₁ i).re)
    (hexponent₂ : ∀ j, 0 < (exponent₂ j).re)
    (hamplitude₁ : ∀ i, amplitude₁ i ≠ 0)
    (hamplitude₂ : ∀ j, amplitude₂ j ≠ 0) :
    (HTGeometry.algebraicHankelMatrix
        (fun n =>
          criticalMellinVolterraHaarFinitePacket L₁ amplitude₁ exponent₁ n *
          criticalMellinVolterraHaarFinitePacket L₂ amplitude₂ exponent₂ n)
        (d * e)).det ≠ 0 ↔
      Function.Injective (fun p : Fin d × Fin e =>
        Complex.exp (exponent₁ p.1) * Complex.exp (exponent₂ p.2)) := by
  have hexponent₁0 : ∀ i, exponent₁ i ≠ 0 := by
    intro i hi
    have hpositive := hexponent₁ i
    rw [hi] at hpositive
    norm_num at hpositive
  have hexponent₂0 : ∀ j, exponent₂ j ≠ 0 := by
    intro j hj
    have hpositive := hexponent₂ j
    rw [hj] at hpositive
    norm_num at hpositive
  rw [criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence
      hexponent₁0,
    criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence
      hexponent₂0]
  unfold HTGeometry.finiteModalTransferSequence
  exact HTGeometry.det_algebraicHankelMatrix_finiteModalSequence_mul_ne_zero_iff
    (fun i => mul_ne_zero (hamplitude₁ i)
      (criticalMellinVolterraHaarMultiplier_ne_zero hL₁ (hexponent₁ i)))
    (fun j => mul_ne_zero (hamplitude₂ j)
      (criticalMellinVolterraHaarMultiplier_ne_zero hL₂ (hexponent₂ j)))

theorem criticalMellinVolterraHaarFinitePacket_mul_exact_hankel_mode_count
    {d e : ℕ} {L₁ L₂ : ℝ}
    {amplitude₁ exponent₁ : Fin d → ℂ}
    {amplitude₂ exponent₂ : Fin e → ℂ}
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hexponent₁ : ∀ i, 0 < (exponent₁ i).re)
    (hexponent₂ : ∀ j, 0 < (exponent₂ j).re)
    (hamplitude₁ : ∀ i, amplitude₁ i ≠ 0)
    (hamplitude₂ : ∀ j, amplitude₂ j ≠ 0)
    (hnode : Function.Injective (fun p : Fin d × Fin e =>
      Complex.exp (exponent₁ p.1) * Complex.exp (exponent₂ p.2))) :
    (HTGeometry.algebraicHankelMatrix
        (fun n =>
          criticalMellinVolterraHaarFinitePacket L₁ amplitude₁ exponent₁ n *
          criticalMellinVolterraHaarFinitePacket L₂ amplitude₂ exponent₂ n)
        (d * e)).det ≠ 0 ∧
      (HTGeometry.algebraicHankelMatrix
        (fun n =>
          criticalMellinVolterraHaarFinitePacket L₁ amplitude₁ exponent₁ n *
          criticalMellinVolterraHaarFinitePacket L₂ amplitude₂ exponent₂ n)
        (d * e + 1)).det = 0 := by
  have hexponent₁0 : ∀ i, exponent₁ i ≠ 0 := by
    intro i hi
    have hpositive := hexponent₁ i
    rw [hi] at hpositive
    norm_num at hpositive
  have hexponent₂0 : ∀ j, exponent₂ j ≠ 0 := by
    intro j hj
    have hpositive := hexponent₂ j
    rw [hj] at hpositive
    norm_num at hpositive
  rw [criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence
      hexponent₁0,
    criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence
      hexponent₂0]
  unfold HTGeometry.finiteModalTransferSequence
  exact HTGeometry.finiteModalSequence_mul_exact_hankel_mode_count
    (fun i => mul_ne_zero (hamplitude₁ i)
      (criticalMellinVolterraHaarMultiplier_ne_zero hL₁ (hexponent₁ i)))
    (fun j => mul_ne_zero (hamplitude₂ j)
      (criticalMellinVolterraHaarMultiplier_ne_zero hL₂ (hexponent₂ j)))
    hnode

end

end RHTower
