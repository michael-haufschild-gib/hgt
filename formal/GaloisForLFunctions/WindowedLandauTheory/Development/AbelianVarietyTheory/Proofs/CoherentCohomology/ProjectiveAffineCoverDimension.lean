import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFormAvoidance
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothSchemeDimension

/-! A smooth projective scheme of relative dimension `d` over an algebraically
closed field admits a cover by `d + 1` affine opens. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Choose homogeneous basic opens that meet every component of the
successive closed complements. -/
theorem exists_affine_cover_of_smooth_projective {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} {s : X ⟶ Spec (.of K)} (d : ℕ) [SmoothOfRelativeDimension d s]
    (hp : IsProjOver s) :
    ∃ U : Fin (d + 1) → X.Opens, (∀ j, IsAffineOpen (U j)) ∧ ⨆ j, U j = ⊤ := by
  classical
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  letI : CompactSpace X := hp.compactSpace
  letI : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian s }
  have hX : NoetherianSpace X := IsNoetherian.noetherianSpace
  obtain ⟨N, i, hi, -⟩ := hp
  letI : IsClosedImmersion i := hi
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
  let W (f : MvPolynomial (Fin (N + 1)) K) : X.Opens := i ⁻¹ᵁ Proj.basicOpen 𝒜 f
  obtain ⟨F, hF, hc⟩ := @exists_cuts_empty_intersection _ (d + 1)
    (fun _ => {f | f.IsHomogeneous 1}) X _ hX (fun f => (W f : Set X)ᶜ)
    (fun f => (W f).isOpen.isClosed_compl) (topologicalKrullDim_smooth_lt_succ s d)
    (fun _ S => by
      obtain ⟨f, hf, h⟩ := PSpace.exists_form_nonvanishing N 1 (S.image i)
      exact ⟨f, hf, fun x hx =>
        Set.notMem_compl_iff.mpr (h (i x) (Finset.mem_image_of_mem i hx))⟩)
  refine ⟨fun j => W (F j), fun j => ?_, top_le_iff.mp fun x _ => ?_⟩
  · exact (Proj.isAffineOpen_basicOpen 𝒜 _ (hF j) one_pos).preimage i
  · obtain ⟨j, hj⟩ := hc x
    exact Opens.mem_iSup.mpr ⟨j, Set.notMem_compl_iff.mp hj⟩

end GlobalTheory.SchemeCohomology
