import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.NoetherianGradedCechModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.SmoothTwistCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistCechComparison

/-! Smooth affine charts presented by section ratios give a perfect model of a line-bundle complex. -/

open AlgebraicGeometry CategoryTheory HTGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] {M H : LB X} (hM : M.IsLB) (hH : H.IsLB)
  {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (s : ι → H.Sec)

include hM hH in
/-- Descend the degree-zero Čech complex to Noetherian coefficients, then extend
the resulting perfect model to the original base. -/
theorem exists_perfect_cech_of_smooth_charts
    (haff : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ (fun i => nonzeroLocus (s i)) I))
    (r : ∀ i, ι → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i, letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := R) (r i))) :
    ∃ (K : CochainComplex (ModuleCat R) ℕ) (φ : K ⟶ cech f (toMod M) (fun i => nonzeroLocus (s i))),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧
      (∀ (S : Type) [CommRing S] (α : R →+* S),
        QuasiIso (((ModuleCat.extendScalars α).mapHomologicalComplex _).map φ)) := by
  let D := GrSum.grading (twistSections_commute f M ⊤ s)
  have ha (i : ι) : IsAffineOpen (nonzeroLocus (s i)) := by
    simpa only [coverInter, top_inf_eq, Finset.inf_singleton] using haff {i} (Finset.singleton_nonempty i)
  obtain ⟨R₀, hR₀, a, b, d, e, Φ, _, hflat, hzero, hfin, ⟨e₀⟩⟩ :=
    SmoothDescent.exists_noetherian_gradedCech_model D
      (fun i => exists_smooth_dehomogenized_twist_chart f hM hH s i (ha i) (r i) (hr i) (hgen i)) 0
  letI := hR₀
  obtain ⟨e₁⟩ := nonempty_gradedCech_iso f hM hH s
  obtain ⟨K, φ, _, hK, hφ⟩ := exists_perfect_cochain_of_noetherian_model _ _ (e₀ ≪≫ e₁)
    (Fintype.card ι) (fun p hp => hzero p hp.le) hflat hfin
    (cech_flat f (fun i => nonzeroLocus (s i)) hM haff)
  exact ⟨K, φ, hK, hφ⟩

end GlobalTheory.LineBundleSections
