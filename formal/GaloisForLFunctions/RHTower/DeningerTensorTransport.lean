import GaloisForLFunctions.RHTower.DeningerFrechetProperties
import GaloisForLFunctions.RHTower.DeningerQuotientSeminorm
import GaloisForLFunctions.HTGeometry.ProjectiveTensorQuotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensoring the Poisson sequence

Over a field every module is flat, so the Poisson sequence stays exact after tensoring with any
coefficient space, and the Poisson operator stays injective.  For the topology, the projective
tensor seminorms transport both ends of the sequence: the tensored Poisson operator is continuous
with the same constant, and the tensored projection onto the cokernel is again a strict surjection
— the projective seminorm on `E ⊗ M_ζ` is the infimum of the projective seminorms of the lifts.

* `deningerTensor_exact`, `deningerTensor_injective`, `deningerTensor_surjective` : the tensored
  sequence is exact.
* `deningerTensor_poisson_bound` : the tensored Poisson operator is continuous.
* `deningerTensor_quotient_strict` : **the tensored projection is strict.**
-/

open scoped TensorProduct

noncomputable section

namespace RHTower

variable (E : Type*) [AddCommGroup E] [Module ℂ E]

/-! ## Exactness -/

/-- **The tensored Poisson sequence is exact at the radial space.** -/
theorem deningerTensor_exact :
    Function.Exact (LinearMap.lTensor E deningerPoissonLM)
      (LinearMap.lTensor E deningerMZetaMk) :=
  Module.Flat.lTensor_exact E deningerPoisson_exact

/-- **The tensored Poisson operator is injective.** -/
theorem deningerTensor_injective :
    Function.Injective (LinearMap.lTensor E deningerPoissonLM) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ deningerPoissonLM_injective

/-- **The tensored projection is surjective.** -/
theorem deningerTensor_surjective :
    Function.Surjective (LinearMap.lTensor E deningerMZetaMk) :=
  LinearMap.lTensor_surjective E deningerMZetaMk_surjective

/-! ## Continuity of the tensored Poisson operator -/

/-- **A seminorm bound for the Poisson operator tensors with the same constant.** -/
theorem deningerTensor_poisson_bound (p : Seminorm ℂ E) (pC : Seminorm ℂ DeningerMeyerCap)
    (q : Seminorm ℂ deningerRadialCompat) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : DeningerMeyerCap, q (deningerPoissonLM f) ≤ C * pC f)
    (z : E ⊗[ℂ] DeningerMeyerCap) :
    GaloisForLFunctions.projTensorSeminorm p q (LinearMap.lTensor E deningerPoissonLM z)
      ≤ C * GaloisForLFunctions.projTensorSeminorm p pC z := by
  have hmap := GaloisForLFunctions.projTensorSeminorm_map_le p pC p q
    (LinearMap.id : E →ₗ[ℂ] E) deningerPoissonLM zero_le_one hC
    (fun x => by rw [LinearMap.id_apply, one_mul]) hb z
  rw [one_mul] at hmap
  exact hmap

/-! ## Strictness of the tensored projection -/

/-- **The tensored projection onto the cokernel is strict**: the projective seminorm on
`E ⊗ M_ζ` is the infimum of the projective seminorms of the lifts. -/
theorem deningerTensor_quotient_strict (p : Seminorm ℂ E) (q : Seminorm ℂ deningerRadialCompat)
    (w : E ⊗[ℂ] DeningerMZeta) :
    GaloisForLFunctions.projTensorSeminorm p
        (deningerQuotientSeminorm (LinearMap.range deningerPoissonLM) q) w
      = sInf {r : ℝ | ∃ z : E ⊗[ℂ] deningerRadialCompat,
          TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) deningerMZetaMk z = w ∧
            GaloisForLFunctions.projTensorSeminorm p q z = r} := by
  refine GaloisForLFunctions.projTensorSeminorm_quotient_eq p q
    (deningerQuotientSeminorm (LinearMap.range deningerPoissonLM) q) deningerMZetaMk ?_ ?_ w
  · intro x ε hε
    obtain ⟨y, hy, hlt⟩ :=
      deningerQuotientSeminorm_exists_lt (LinearMap.range deningerPoissonLM) q x hε
    refine ⟨y, ?_, hlt.le⟩
    rw [deningerMZetaMk, Submodule.mkQ_apply]
    exact hy
  · intro y
    rw [deningerMZetaMk, Submodule.mkQ_apply]
    exact deningerQuotientSeminorm_mk_le (LinearMap.range deningerPoissonLM) q y

end RHTower

end
