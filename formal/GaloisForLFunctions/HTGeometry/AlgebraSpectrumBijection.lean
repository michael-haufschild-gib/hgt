import GaloisForLFunctions.HTGeometry.AlgebraSpectrumProper

/-!
# The global chart bijection

The fibrewise bijection of `AlgebraSpectrumFibre` assembles to a bijection from the preimage of an
open set of parameters onto the corresponding part of the root locus.  With the continuity of the
inverse chart (`AlgebraSpectrumChart`) this is the homeomorphism that transports the local
homeomorphism property from the root locus to the complex-point space.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

namespace AlgSpec

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **The global chart bijection.**  Where a chosen element generates and the relation it satisfies
is fibrewise separable with the expected fibre count, the chart map is a bijection from the
preimage of `U` onto the part of the root locus above `U`. -/
theorem bijOn_toPlane {θ : B} {p : ℂ[X][X]} (hp : Polynomial.aeval θ p = 0) (hmonic : p.Monic)
    {U : Set ℂ}
    (hgen : ∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
      (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q)
    (hsep : ∀ s ∈ U, (biFibre p s).Separable)
    (hcard : ∀ s ∈ U, {χ : AlgSpec B | proj B χ = s}.ncard = p.natDegree) :
    Set.BijOn (toPlane (B := B) θ) (proj B ⁻¹' U) {z : ℂ × ℂ | z ∈ BiRootLocus p ∧ z.1 ∈ U} := by
  refine ⟨?_, toPlane_injOn hgen, ?_⟩
  · intro χ hχ
    exact ⟨toPlane_mem_biRootLocus hp χ, hχ⟩
  · intro z hz
    obtain ⟨hzroot, hzU⟩ := hz
    have hroot : (biFibre p z.1).eval z.2 = 0 := by
      have h : biEval p z = 0 := hzroot
      rwa [biEval_eq_eval_biFibre] at h
    obtain ⟨χ, hχ, hval⟩ :=
      (bijOn_eval_fibre hp hmonic hgen hzU (hsep _ hzU) (hcard _ hzU)).2.2 hroot
    refine ⟨χ, ?_, ?_⟩
    · show proj B χ ∈ U
      rw [show proj B χ = z.1 from hχ]; exact hzU
    · exact Prod.ext (by exact hχ) hval

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
