import GaloisForLFunctions.HTGeometry.FiniteQuditHermitianUnit
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.TracefreeAperture

/-!
# Spectral aperture of the traceless qudit sector

Every real packet of non-identity Hermitian qudit units has zero trace. The
trace-free Hessian inequality therefore bounds its squared operator by
`(D-1)/D` times its Frobenius energy. Identity removal is built into the packet,
so the bound applies to every coefficient array without an extra trace premise.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {D : ℕ} [NeZero D]

/-- The non-identity part of a real Hermitian-unit packet. -/
noncomputable def tracelessQuditPacket (c : Fin D × Fin D → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ p ∈ Finset.univ.erase ((0, 0) : Fin D × Fin D), (c p : ℂ) • quditHermUnit p

theorem tracelessQuditPacket_isHermitian (c : Fin D × Fin D → ℝ) :
    (tracelessQuditPacket c).IsHermitian := by
  change (tracelessQuditPacket c)ᴴ = tracelessQuditPacket c
  unfold tracelessQuditPacket
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.conjTranspose_smul, quditHermUnit_conjTranspose]
  simp

theorem tracelessQuditPacket_trace (c : Fin D × Fin D → ℝ) :
    (tracelessQuditPacket c).trace = 0 := by
  simp only [tracelessQuditPacket, Matrix.trace_sum, Matrix.trace_smul, trace_quditHermUnit]
  apply Finset.sum_eq_zero
  intro p hp
  rw [if_neg (Finset.ne_of_mem_erase hp), smul_zero]

/-- Every traceless qudit packet has the dimension-improved positive spectral complement. -/
theorem tracelessQuditPacket_aperture (c : Fin D × Fin D → ℝ) :
    (((((D : ℝ) - 1) * frobSq (tracelessQuditPacket c) : ℝ) : ℂ) •
        (1 : Matrix (Fin D) (Fin D) ℂ) -
      ((D : ℝ) : ℂ) • ((tracelessQuditPacket c)ᴴ * tracelessQuditPacket c)).PosSemidef := by
  have h := tracefree_aperture
    (tracelessQuditPacket_isHermitian c) (tracelessQuditPacket_trace c)
  simp only [Fintype.card_fin] at h
  exact ⟨h.1, fun x => h.2 x⟩

/-- Each qudit eigenvalue pays at least the trace-free share of the full matrix energy. -/
theorem tracelessQuditPacket_eigenvalue_bound (c : Fin D × Fin D → ℝ) (i : Fin D) :
    (D : ℝ) * ((tracelessQuditPacket_isHermitian c).eigenvalues i)^2 ≤
      ((D : ℝ) - 1) * frobSq (tracelessQuditPacket c) := by
  simpa only [Fintype.card_fin] using tracefree_eigenvalue_sq_bound
    (tracelessQuditPacket_isHermitian c) (tracelessQuditPacket_trace c) i

#print axioms tracelessQuditPacket_aperture
#print axioms tracelessQuditPacket_eigenvalue_bound

end GaloisForLFunctions.HTGeometry
