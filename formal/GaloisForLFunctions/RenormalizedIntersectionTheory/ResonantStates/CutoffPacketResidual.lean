import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeckeCutoffSource
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeckeCutoffShifts
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffDilation

/-!
# The residual norm of an automorphic cutoff packet

At cutoffs at least two, modular returns vanish. The joint cutoff Gram
identity therefore transfers the full Hecke residual of any finite complex
packet to its unitary-dilation model, including all interference terms.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- An arbitrary finite combination of genuine automorphic truncations. -/
def automorphicCutoffPacket {ι : Type*} (S : Finset ι) (u : ℂ)
    (Y : ι → ℝ) (c : ι → ℂ) (z : ℍ) : ℂ :=
  ∑ i ∈ S, c i * automorphicTruncation u (Y i) z

/-- Hecke action is linear on the packet before restricting to the fundamental domain. -/
theorem dyadicHecke_packet {ι : Type*} (S : Finset ι) (u : ℂ)
    (Y : ι → ℝ) (c : ι → ℂ) (z : ℍ) :
    dyadicHecke (automorphicCutoffPacket S u Y c) z =
      ∑ i ∈ S, c i * dyadicHecke (automorphicTruncation u (Y i)) z := by
  simp only [dyadicHecke, automorphicCutoffPacket, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The packet residual is the sum of the actual residuals. -/
theorem automorphicCutoffPacket_residual {ι : Type*} (S : Finset ι) (u : ℂ)
    (Y : ι → ℝ) (c : ι → ℂ) (z : ℍ) :
    dyadicHecke (automorphicCutoffPacket S u Y c) z -
      ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * automorphicCutoffPacket S u Y c z =
      ∑ i ∈ S, c i * dyadicEigenResidualAt u (Y i) z := by
  rw [dyadicHecke_packet]
  simp only [automorphicCutoffPacket, dyadicEigenResidualAt, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Above cutoff two the full residual has the same three cutoff terms as the cusp model. -/
theorem dyadicEigenResidualAt_cutoff_shifts {u : ℂ} (hAu : msA u = 0)
    {Y : ℝ} (hY : 2 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    dyadicEigenResidualAt u Y z =
      (2 : ℂ) ^ u * truncatedLineModel u (Y * 2) z +
        (2 : ℂ) ^ (-u) * truncatedLineModel u (Y / 2) z -
          ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * truncatedLineModel u Y z := by
  rw [dyadicEigenResidualAt_eq_heckeRemainder hAu hY hz]
  have he := hecke_cutoff_shifts Nat.prime_two hAu Y z
  rw [heckeTruncated_eq Nat.prime_two] at he
  norm_num only [Nat.cast_ofNat] at he
  linear_combination he

/-- All interference terms in the full packet residual agree with the cusp model. -/
theorem cutoffPacket_residual_isometry {ι : Type*} (S : Finset ι) {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    (Y : ι → ℝ) (c : ι → ℂ) (hY : ∀ i ∈ S, 2 ≤ Y i) :
    (∫ z in fd, ‖∑ i ∈ S, c i * dyadicEigenResidualAt u (Y i) z‖ ^ 2) =
      ∫ y, ‖∑ i ∈ S, c i *
        ((2 : ℂ) ^ u * cuspCutoff u (Y i * 2) y +
          (2 : ℂ) ^ (-u) * cuspCutoff u (Y i / 2) y -
            ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * cuspCutoff u (Y i) y)‖ ^ 2 := by
  let J := S ×ˢ (Finset.univ : Finset (Fin 3))
  let H : ι × Fin 3 → ℝ := fun j => ![Y j.1 * 2, Y j.1 / 2, Y j.1] j.2
  let C : ι × Fin 3 → ℂ := fun j =>
    c j.1 * ![(2 : ℂ) ^ u, (2 : ℂ) ^ (-u), -((2 : ℂ) ^ u + (2 : ℂ) ^ (-u))] j.2
  have hH : ∀ j ∈ J, 1 ≤ H j := by
    intro j hj
    have hi := hY j.1 (Finset.mem_product.mp hj).1
    rcases j with ⟨i, k⟩
    fin_cases k <;> simp only [H, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;> linarith
  have he := resonant_finite_combination_isometry J (fun _ => u) H C
    (fun _ _ => hu) (fun _ _ => hur) (fun _ _ => hAu) hH
  have hleft : (∫ z in fd, ‖∑ i ∈ S, c i * dyadicEigenResidualAt u (Y i) z‖ ^ 2) =
      ∫ z in fd, ‖∑ j ∈ J, C j * truncatedLineModel u (H j) z‖ ^ 2 := by
    refine setIntegral_congr_fun isClosed_fd.measurableSet fun z hz => ?_
    congr 1
    simp only [J, Finset.sum_product, Fin.sum_univ_three, C, H,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dyadicEigenResidualAt_cutoff_shifts hAu (hY i hi) hz]
    ring
  rw [hleft, he]
  congr 1
  funext y
  congr 1
  simp only [J, Finset.sum_product, Fin.sum_univ_three, C, H,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
