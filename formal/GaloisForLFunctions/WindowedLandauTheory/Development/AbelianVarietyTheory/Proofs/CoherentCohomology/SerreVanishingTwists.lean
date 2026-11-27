import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistCechCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.SmoothTwistCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteChartGradedVanishing

/-! Positive Čech cohomology vanishes for sufficiently large twists
by a very ample line bundle on a smooth scheme over a Noetherian ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum HTGeometry MvPolynomial
open GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (.of R)) {M H : LB X} (hM : M.IsLB) (hH : H.IsLB)
  {κ : Type} [LinearOrder κ] (s : κ → H.Sec)

local notation "U" => fun i => nonzeroLocus (s i)
local notation "D" => GrSum.grading (twistSections_commute f M ⊤ s)

include hM hH

/-- The degree-`t` part of the homogeneous localization complex computes
the Čech cohomology of the `t`-th twist. -/
theorem nonempty_gradedCech_twist_iso (t : ℤ) :
    Nonempty (gradedCech (ι := κ) D t ≅ cech f (toMod (twist M H t)) U) := by
  let F := toMod (twist M H t)
  letI (I : Finset κ) := sectionDatumModule f F U I
  let e (I : Finset κ) := twistChartPiece f hM hH s I t
  let φ : (homLocDatum (ι := κ) D t).Hom (sectionDatum F U) :=
    { app := fun I => (e I).toLinearMap.toAddMonoidHom
      comm := fun h z => (twistChartPiece_natural f hM hH s h t z).symm }
  let g : gradedCech (ι := κ) D t ⟶ cech f F U := FinsetCechDatum.linearCochainMap
    (fun h => homLocDatum_res_smul D h t) (res_base_smul f F U) φ
    (fun I a z => (e I).map_smul a z)
  have hg : IsIso g := FinsetCechDatum.isIso_linearCochainMap _ _ _ _ fun I _ => (e I).bijective
  exact ⟨@asIso _ _ _ _ g hg⟩

variable [Fintype κ]

/-- Affine nonvanishing charts with coordinate ratios generating their rings
give a common vanishing threshold in every positive cohomological degree. -/
theorem exists_twist_cech_exactAt_succ [IsNoetherianRing R] [Smooth f]
    (hU : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, κ → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k,
      resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hsurj : ∀ i, letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := R) (r i))) :
    ∃ b : ℤ, ∀ t ≥ b, ∀ q : ℕ, (cech f (toMod (twist M H t)) U).ExactAt (q + 1) := by
  let S := MvPolynomial κ R
  let G := gradedTwistSections f M ⊤ s
  have hfin (i : κ) : Module.Finite S (QuotSMulTop (MvPolynomial.X i - 1 : S) G) := by
    obtain ⟨B, _, _, π, P, _, _, -, hP, -, hπ, -, ⟨e⟩⟩ :=
      exists_smooth_dehomogenized_twist_chart f hM hH s i (hU i) (r i) (hr i) (hsurj i)
    letI : RingHomSurjective π.toRingHom := ⟨hπ⟩
    let j : QuotSMulTop (MvPolynomial.X i - 1 : S) G →ₛₗ[π.toRingHom] P :=
      { e.toAddMonoidHom with map_smul' := fun a x => e.map_smul a x }
    exact (j.finite_iff_of_bijective e.bijective).mpr hP
  obtain ⟨b, hb⟩ := exists_gradedCech_exactAt_succ_of_finite_charts D hfin
  refine ⟨b, fun t ht q => ?_⟩
  obtain ⟨e⟩ := nonempty_gradedCech_twist_iso f hM hH s t
  exact (hb t ht q).of_iso e

end GlobalTheory.LineBundleSections
