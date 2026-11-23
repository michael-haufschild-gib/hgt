import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineSmoothDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClosedCutsDimension
import Mathlib.AlgebraicGeometry.Artinian

/-! A smooth scheme of relative dimension d over an algebraically closed
field has no chain of irreducible closed sets of length greater than d. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Order Topology TopologicalSpace

namespace GlobalTheory.SchemeCohomology

/-- A nonempty affine open of a smooth scheme has the relative dimension. -/
theorem topologicalKrullDim_smooth_affineOpen {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (s : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d s]
    {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    topologicalKrullDim (↥U) = (d : ℕ∞) := by
  let e := hU.isoSpec.hom.homeomorph
  calc
    _ = topologicalKrullDim (PrimeSpectrum Γ(X, U)) := e.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(X, U) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)
    _ = _ := ringKrullDim_smooth_affineOpen s d hU hne

/-- The relative dimension bounds the dimension of the underlying space. -/
theorem topologicalKrullDim_smooth_lt_succ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (s : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d s] :
    topologicalKrullDim X < (d + 1 : ℕ) := by
  let C := X.affineCover
  apply topologicalKrullDim_lt_of_openCover (fun i => (C.f i).opensRange) C.iSup_opensRange
  intro j
  let U := (C.f j).opensRange
  change topologicalKrullDim (↥U) < (d + 1 : ℕ)
  by_cases hU : (U : Set X).Nonempty
  · have h : topologicalKrullDim (↥U) = (d : ℕ∞) :=
      topologicalKrullDim_smooth_affineOpen s d (isAffineOpen_opensRange (C.f j)) hU
    rw [h]
    exact_mod_cast Nat.lt_succ_self d
  · apply krullDim_lt_coe_iff.mpr
    intro p
    obtain ⟨x, _⟩ := p.head.isIrreducible.nonempty
    exact (hU ⟨x.1, x.2⟩).elim

end GlobalTheory.SchemeCohomology
