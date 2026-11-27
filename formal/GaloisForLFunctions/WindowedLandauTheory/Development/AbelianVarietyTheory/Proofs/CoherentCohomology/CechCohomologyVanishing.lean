import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveLineBundleCechModel

/-! Vanishing is independent of the affine cover used for Čech cohomology. -/

noncomputable section

open AlgebraicGeometry HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

/-- An affine cover of a line bundle computes the vanishing of its
sheaf cohomology whenever the intersections are affine. -/
theorem exactAt_cech_iff_subsingleton_cohomology {R : Type} [CommRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) {L : LB X} (hL : L.IsLB)
    {ι : Type} [LinearOrder ι] (U : ι → X.Opens) (hcov : ⊤ ≤ ⨆ i, U i)
    (ha : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s)) (q : ℕ) :
    (cech f (toMod L) U).ExactAt q ↔ Subsingleton (CohomologyOn (toMod L) ⊤ q) := by
  let F := toMod L
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hL
  let e := cechCohomologyEquiv f F U q
  have a : ModuleCechCohomology ⊤ U F q ≃ₗ[Γ(X, ⊤)] CohomologyOn F ⊤ q := by
    have h := moduleLerayLinearEquiv ⊤ U F q hcov
      (fun s hs => quasicoherent_acyclicOn F (ha s hs))
    rwa [coverInter_empty] at h
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  exact (e.toEquiv.trans a.toEquiv).subsingleton_congr

end GlobalTheory.LineBundleSections
