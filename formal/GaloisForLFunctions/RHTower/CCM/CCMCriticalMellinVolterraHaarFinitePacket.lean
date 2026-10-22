import GaloisForLFunctions.HTGeometry.FiniteModalTransfer
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinVolterraHaarMode

/-!
# Finite-packet faithfulness of the critical-Mellin Volterra--Haar filter

The one-mode transfer law is lifted to arbitrary finite packets.  After sampling at integer
observation labels, every exponent `w i` has node `exp (w i)` and its amplitude is multiplied by
the explicit Volterra--Haar transfer factor.  On the open right half-plane, the filter preserves
the maximal Hankel determinant up to a nonzero product and therefore preserves exact modal count
whenever the sampled nodes are distinct.
-/

open Complex
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- A finite packet of Volterra--Haar mode responses sampled at the natural-number labels. -/
def criticalMellinVolterraHaarFinitePacket {d : ℕ} (L : ℝ)
    (amplitude exponent : Fin d → ℂ) (n : ℕ) : ℂ :=
  ∑ i, amplitude i *
    criticalMellinVolterraModeAdjacentBlock L (n : ℝ) (exponent i)

/-- The sampled packet is exactly a diagonally filtered finite modal sequence. -/
theorem criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence
    {d : ℕ} {L : ℝ} {amplitude exponent : Fin d → ℂ}
    (hexponent : ∀ i, exponent i ≠ 0) :
    criticalMellinVolterraHaarFinitePacket L amplitude exponent =
      HTGeometry.finiteModalTransferSequence
        (fun i ↦ criticalMellinVolterraHaarMultiplier L (exponent i))
        amplitude (fun i ↦ Complex.exp (exponent i)) := by
  funext n
  rw [criticalMellinVolterraHaarFinitePacket,
    HTGeometry.finiteModalTransferSequence,
    HTGeometry.finiteModalSequence]
  apply Finset.sum_congr rfl
  intro i _
  rw [criticalMellinVolterraModeAdjacentBlock_eq (hexponent i)]
  · rw [← Complex.exp_nat_mul]
    have hn : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_num
    rw [hn]
    rw [mul_comm (exponent i) (n : ℂ)]
    ring

/-- **Exact finite-packet transfer determinant.**  The Volterra--Haar observation multiplies the
unfiltered sampled modal determinant by the product of its explicit transfer factors. -/
theorem det_criticalMellinVolterraHaarFinitePacket
    {d : ℕ} (L : ℝ) (amplitude exponent : Fin d → ℂ)
    (hexponent : ∀ i, exponent i ≠ 0) :
    (HTGeometry.algebraicHankelMatrix
        (criticalMellinVolterraHaarFinitePacket L amplitude exponent) d).det =
      (HTGeometry.algebraicHankelMatrix
        (HTGeometry.finiteModalSequence amplitude (fun i ↦ Complex.exp (exponent i))) d).det *
        ∏ i, criticalMellinVolterraHaarMultiplier L (exponent i) := by
  rw [criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence hexponent]
  exact HTGeometry.det_algebraicHankelMatrix_finiteModalTransferSequence _ _ _

/-- In the open right half-plane the filter preserves, in both directions, nonsingularity of the
maximal modal Hankel block. -/
theorem det_criticalMellinVolterraHaarFinitePacket_ne_zero_iff
    {d : ℕ} {L : ℝ} {amplitude exponent : Fin d → ℂ}
    (hL : 0 < L) (hexponent : ∀ i, 0 < (exponent i).re) :
    (HTGeometry.algebraicHankelMatrix
        (criticalMellinVolterraHaarFinitePacket L amplitude exponent) d).det ≠ 0 ↔
      (HTGeometry.algebraicHankelMatrix
        (HTGeometry.finiteModalSequence amplitude (fun i ↦ Complex.exp (exponent i))) d).det ≠ 0 := by
  have hexponent0 : ∀ i, exponent i ≠ 0 := by
    intro i hi
    have hpositive := hexponent i
    rw [hi] at hpositive
    norm_num at hpositive
  rw [det_criticalMellinVolterraHaarFinitePacket L amplitude exponent hexponent0]
  have htransfer :
      (∏ i, criticalMellinVolterraHaarMultiplier L (exponent i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦
      criticalMellinVolterraHaarMultiplier_ne_zero hL (hexponent i)
  constructor
  · intro hfiltered hbase
    exact hfiltered (by simp [hbase])
  · intro hbase
    exact mul_ne_zero hbase htransfer

/-- **Finite-packet right-half-plane faithfulness.**  Positive-growth exponents with distinct
sampled nodes and nonzero amplitudes retain their exact noiseless Hankel mode count. -/
theorem criticalMellinVolterraHaarFinitePacket_exact_hankel_mode_count
    {d : ℕ} {L : ℝ} {amplitude exponent : Fin d → ℂ}
    (hL : 0 < L) (hexponent : ∀ i, 0 < (exponent i).re)
    (hnode : Function.Injective fun i ↦ Complex.exp (exponent i))
    (hamplitude : ∀ i, amplitude i ≠ 0) :
    (HTGeometry.algebraicHankelMatrix
        (criticalMellinVolterraHaarFinitePacket L amplitude exponent) d).det ≠ 0 ∧
      (HTGeometry.algebraicHankelMatrix
        (criticalMellinVolterraHaarFinitePacket L amplitude exponent) (d + 1)).det = 0 := by
  have hexponent0 : ∀ i, exponent i ≠ 0 := by
    intro i hi
    have hpositive := hexponent i
    rw [hi] at hpositive
    norm_num at hpositive
  rw [criticalMellinVolterraHaarFinitePacket_eq_finiteModalTransferSequence hexponent0]
  exact HTGeometry.finiteModalTransferSequence_exact_hankel_mode_count
    hnode hamplitude (fun i ↦
      criticalMellinVolterraHaarMultiplier_ne_zero hL (hexponent i))

end

end RHTower
