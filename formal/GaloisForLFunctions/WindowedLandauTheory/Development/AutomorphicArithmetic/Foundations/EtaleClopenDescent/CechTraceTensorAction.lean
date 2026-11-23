import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechLeftCupBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCupResidue
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Module.Submodule.Bilinear

/-! The traced residue in the left coordinate of the projective
Čech product gives a well-defined action modulo right boundaries. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.WH
open scoped GlobalTheory.CechDR TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- Contract the first tensor factor by a traced wedge residue and
retain the second factor. -/
def traceWedgeTensorAction (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k) :
    (DR k E ⊗[k] DR k E) →ₗ[k] DR k E →ₗ[k] DR k E :=
  TensorProduct.lift (LinearMap.smulRightₗ.comp
    ((LinearMap.mul k (DR k E)).compr₂ (topResidue τ ρ)))

theorem traceWedgeTensorAction_tmul (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k)
    (u v a : DR k E) :
    traceWedgeTensorAction τ ρ (u ⊗ₜ v) a = topResidue τ ρ (u * a) • v := by
  rw [traceWedgeTensorAction, TensorProduct.lift.tmul]
  rfl

/-- A mixed boundary of total cardinal degree d+2 acts by a boundary
on a regular cocycle in complementary form degree. -/
theorem IsFinCover.traceWedgeTensorAction_boundary (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {a b p : ℕ} (hab : a + b = d) (hp : p ≤ d)
    {v : Finset (Fin (d + 1)) → DR k E}
    (hv : v ∈ (cech fun I => omB k E (rB k E x I) b).Z p)
    {t : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → DR k E ⊗[k] DR k E}
    (ht : t ∈ (mixedCech fun I J => Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E))
      (omB k E (rB k E x I) a) (omB k E (rB k E x J) b)).B ((d : ℤ) + 2)) :
    cupAlongLeft (traceWedgeTensorAction τ ρ) v t ∈
      (cech fun J => omB k E (rB k E x J) b).B p := by
  let P (n : ℕ) (I : Finset (Fin (d + 1))) := omB k E (rB k E x I) n
  let A (I J : Finset (Fin (d + 1))) :=
    Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E)) (P a I) (P b J)
  let μ := traceWedgeTensorAction τ ρ
  have hmem {I L J} {z w} (hz : z ∈ A I J) (_ : w ∈ P b L) : μ z w ∈ P b J := by
    refine (show A I J ≤ (P b J).comap (μ.flip w) from Submodule.map₂_le.mpr ?_) hz
    intro u _ v hv
    change μ (u ⊗ₜ v) w ∈ P b J
    rw [traceWedgeTensorAction_tmul]
    exact Submodule.smul_mem _ _ hv
  have hface {I L W J : Finset (Fin (d + 1))} (hW : W ⊂ Finset.univ)
      (hI : I.Nonempty) (_ : L.Nonempty) (hIW : I ⊆ W) (hLW : L ⊆ W)
      {z w} (hz : z ∈ A I J) (hw : w ∈ P b L) : μ z w = 0 := by
    obtain ⟨j, _, hj⟩ := Finset.not_subset.mp (not_le_of_gt hW)
    refine (show A I J ≤ LinearMap.ker (μ.flip w) from Submodule.map₂_le.mpr ?_) hz
    intro u hu v _
    change μ (u ⊗ₜ v) w = 0
    have hreg : u * w ∈ P d W := by
      rw [← hab]
      exact mul_mem_omB (omB_mono (rB_mono hIW) a hu) (omB_mono (rB_mono hLW) b hw)
    rw [traceWedgeTensorAction_tmul, topResidue_apply,
      h.traced_residue_eq_zero_of_missing_chart τ hτ ρ hρ hj (hI.mono hIW) _ hreg, zero_smul]
  refine cupAlongLeft_mem_boundary μ A (P b) (P b) hmem hface (by simpa using hp) hv ?_
  have he : (Fintype.card (Fin (d + 1)) : ℤ) + 1 = (d : ℤ) + 2 := by simp; omega
  rwa [he]

end GlobalTheory.PD
