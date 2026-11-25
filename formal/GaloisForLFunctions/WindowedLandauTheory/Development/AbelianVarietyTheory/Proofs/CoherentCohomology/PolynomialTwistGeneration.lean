import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DehomogenizedTwistChart
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DehomogenizedKernels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedSaturatingGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LargeDegreeGradedCechExactness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistCechComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AffineCoordinateDegreeGrowth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization

/-! When the coordinate ratios generate the chart rings, homogeneous polynomials generate
the global sections of all sufficiently large twists. -/

noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum HTGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology
open scoped Pointwise

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (hH : H.IsLB) {ι : Type} (s : ι → H.Sec)

local notation "M" => LB.trivial X
local notation "P" => MvPolynomial ι R

private def trivialZeroTwist (V : X.Opens) :
    Γ(X, V) ≃ₗ[Γ(X, V)] TwistSections f M H V 0 :=
  (chartEquiv (LB.isLB_trivial X) PUnit.unit (V := V) le_top).symm.trans
    (zeroTwistEquiv (LB.isLB_trivial X) hH)

private theorem trivialZeroTwist_restrict {V W : X.Opens} (h : V ≤ W) (a : Γ(X, W)) :
    twistSections_res f M h 0 (trivialZeroTwist f hH W a) =
      trivialZeroTwist f hH V (resG X h a) := by
  let eW := chartEquiv (LB.isLB_trivial X) PUnit.unit (V := W) le_top
  let eV := chartEquiv (LB.isLB_trivial X) PUnit.unit (V := V) le_top
  have he : (toMod M).presheaf.map (homOfLE h).op (eW.symm a) = eV.symm (resG X h a) := by
    apply eV.injective
    rw [eV.apply_symm_apply]
    exact (chartEquiv_map (LB.isLB_trivial X) PUnit.unit le_top h (eW.symm a)).trans
      (congrArg (resG X h) (eW.apply_symm_apply a))
  exact (zeroTwistEquiv_restrict (LB.isLB_trivial X) hH h (eW.symm a)).symm.trans
    (congrArg (zeroTwistEquiv (LB.isLB_trivial X) hH) he)

/-- Evaluate a homogeneous polynomial in the given sections by acting on the constant section. -/
def polynomialTwistSections : P →ₗ[P] gradedTwistSections f M ⊤ s :=
  LinearMap.toSpanSingleton P _ (GrSum.of (twistSections_commute f M ⊤ s) 0 (trivialZeroTwist f hH ⊤ 1))

private theorem polynomialTwistSections_isGraded :
    IsGradedMap (polyGrading ι R) (GrSum.grading (twistSections_commute f M ⊤ s))
      (polynomialTwistSections f hH s) := by
  intro n p hp
  have hunit := GrSum.of_mem_grading (twistSections_commute f M ⊤ s) 0 (trivialZeroTwist f hH ⊤ 1)
  simpa only [polynomialTwistSections, LinearMap.toSpanSingleton_apply, zero_add] using
    grSMul_mem (GrSum.grading (twistSections_commute f M ⊤ s)) hp hunit

private theorem polynomialTwistSections_restrict (V : X.Opens) (p : P) :
    gradedTwistSections_res f M s (le_top : V ≤ ⊤) (polynomialTwistSections f hH s p) =
      p • GrSum.of (twistSections_commute f M V s) 0 (trivialZeroTwist f hH V 1) := by
  change gradedTwistSections_res f M s le_top
    (p • GrSum.of (twistSections_commute f M ⊤ s) 0 (trivialZeroTwist f hH ⊤ 1)) = _
  rw [map_smul, gradedTwistSections_res_of, trivialZeroTwist_restrict, map_one]

/-- On the nonvanishing open of `s i`, divide a section of the `t`-th twist by `s i ^ t`. -/
def twistRestrictionRatio (i : ι) (t : ℤ) :
    letI := sectionAlgebra f (nonzeroLocus (s i))
    TwistSections f M H ⊤ t →ₗ[R] Γ(X, nonzeroLocus (s i)) := by
  let V := nonzeroLocus (s i)
  letI := sectionAlgebra f V
  let e := (trivialZeroTwist f hH V).symm.toLinearMap.comp (divTwistSection M (s i) le_rfl t)
  let e' : TwistSections f M H V t →ₗ[R] Γ(X, V) :=
    { e.toAddMonoidHom with
      map_smul' c x := e.map_smul (algebraMap R Γ(X, V) c) x }
  exact e'.comp (twistSections_res f M le_top t)

private theorem lineBundle_restrict_injective [IsIntegral X] (L : LB X)
    {V : X.Opens} (hV : (V : Set X).Nonempty) :
    Function.Injective ((toMod L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) := by
  intro a b hab
  apply sec_ext
  intro k
  by_cases hk : (L.U k : Set X).Nonempty
  · have hne : ((V ⊓ L.U k : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter V.isOpen (L.U k).isOpen hV hk
    letI : Nonempty (V ⊓ L.U k : X.Opens) := hne.to_subtype
    let h : V ⊓ L.U k ≤ ⊤ ⊓ L.U k := inf_le_inf_right _ le_top
    apply (AlgebraicGeometry.map_injective_of_isIntegral X (homOfLE h))
    have hc := congrArg (fun z : Γ(toMod L, V) => coord z k) hab
    simpa only [coord_map] using hc
  · have e : L.U k = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 hk)
    have hW : (⊤ ⊓ L.U k : X.Opens) = ⊥ := by rw [top_inf_eq, e]
    have h : Subsingleton Γ(X, ⊤ ⊓ L.U k) :=
      hW.symm ▸ (inferInstance : Subsingleton Γ(X, (⊥ : X.Opens)))
    exact h.elim _ _

/-- A section on an integral scheme is determined by its ratio on any nonempty chart. -/
theorem twistRestrictionRatio_injective [IsIntegral X] (i : ι) (t : ℤ)
    (hi : (nonzeroLocus (s i) : Set X).Nonempty) :
    letI := sectionAlgebra f (nonzeroLocus (s i))
    Function.Injective (twistRestrictionRatio f hH s i t) := by
  let V := nonzeroLocus (s i)
  let e := (trivialZeroTwist f hH V).symm
  intro a b he
  change e (divTwistSection M (s i) le_rfl t (twistSections_res f M le_top t a)) =
    e (divTwistSection M (s i) le_rfl t (twistSections_res f M le_top t b)) at he
  exact lineBundle_restrict_injective (twist M H t) hi
    (divTwistSection_injective (s i) le_rfl t (e.injective he))

/-- The chart ratio of a polynomial section is evaluation at the ratios of the coordinates. -/
theorem twistRestrictionRatio_eval (i : ι) (r : ι → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r j) * resG X inf_le_right ((s i).f k))
    (t : ℤ) (p : P) (x : TwistSections f M H ⊤ t)
    (hx : polynomialTwistSections f hH s p = GrSum.of (twistSections_commute f M ⊤ s) t x) :
    letI := sectionAlgebra f (nonzeroLocus (s i))
    twistRestrictionRatio f hH s i t x = MvPolynomial.aeval (R := R) r p := by
  let V := nonzeroLocus (s i)
  letI := sectionAlgebra f V
  let π : P →ₐ[R] Γ(X, V) := MvPolynomial.aeval r
  letI := Module.compHom (TwistSections f M H V 0) π.toRingHom
  let J : Submodule P (gradedTwistSections f M V s) := (MvPolynomial.X i - 1 : P) • ⊤
  let e₀ := trivialZeroTwist f hH V
  obtain ⟨e, he⟩ := exists_dehomogenizedTwistChartEquiv s i le_rfl r hr f M hH
  have hρ := congrArg (gradedTwistSections_res f M s (le_top : V ≤ ⊤)) hx
  rw [polynomialTwistSections_restrict, gradedTwistSections_res_of] at hρ
  have hval := congrArg (fun z => e (J.mkQ z)) hρ
  let g := twistSections_commute f M V s
  let xV := twistSections_res f M (le_top : V ≤ ⊤) t x
  have hzero : e (J.mkQ (GrSum.of g 0 (e₀ 1))) = e₀ 1 :=
    (he 0 (e₀ 1)).trans (divTwistSection_zero (s i) le_rfl (e₀ 1))
  have hdiv : e (J.mkQ (GrSum.of g t xV)) = divTwistSection M (s i) le_rfl t xV := he t xV
  change e (J.mkQ (p • GrSum.of g 0 (e₀ 1))) = e (J.mkQ (GrSum.of g t xV)) at hval
  rw [map_smul, map_smul, hzero, hdiv] at hval
  change π p • e₀ 1 = divTwistSection M (s i) le_rfl t xV at hval
  apply e₀.injective
  change e₀ (e₀.symm _) = e₀ (π p)
  rw [e₀.apply_symm_apply]
  change divTwistSection M (s i) le_rfl t xV = e₀ (π p)
  exact hval.symm.trans
    ((e₀.map_smul (π p) 1).symm.trans (congrArg e₀ (mul_one (π p))))

variable [CompactSpace X] [X.IsSeparated]

private theorem polynomialTwistSections_saturates (i : ι) (r : ι → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r j) * resG X inf_le_right ((s i).f k))
    (hπ : letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := R) r)) :
    ∀ y, ∃ k : ℕ, (MvPolynomial.X i : P) ^ k • y ∈ LinearMap.range (polynomialTwistSections f hH s) := by
  let V := nonzeroLocus (s i)
  let G := gradedTwistSections f M ⊤ s
  let C := gradedTwistSections f M V s
  let ρ : G →ₗ[P] C := gradedTwistSections_res f M s le_top
  letI := sectionAlgebra f V
  let π : P →ₐ[R] Γ(X, V) := MvPolynomial.aeval r
  letI := Module.compHom (TwistSections f M H V 0) π.toRingHom
  let g := polynomialTwistSections f hH s
  let u : P := MvPolynomial.X i - 1
  let J : Submodule P G := u • ⊤
  let J' : Submodule P C := u • ⊤
  have hloc : IsLocalizedModule.Away (MvPolynomial.X i : P) ρ := by
    let T (W : X.Opens) : Prop := IsLocalizedModule.Away (MvPolynomial.X i : P)
      (gradedTwistSections_res f M s (le_top : W ≤ ⊤))
    have he : nonzeroLocus (sectionProduct s ({i} : Finset ι)) = V := by
      simpa only [Finset.iInf_singleton] using nonzeroLocus_sectionProduct hH s ({i} : Finset ι)
    have hl : T (nonzeroLocus (sectionProduct s ({i} : Finset ι))) := by
      simpa only [T, xProd, Finset.prod_singleton] using
        isLocalizedModule_gradedTwistSections f (LB.isLB_trivial X) hH s {i}
    exact (congrArg T he).mp hl
  letI := hloc
  have hker : ∀ y, ρ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : P) ^ k • y = 0 := by
    intro y hy
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (MvPolynomial.X i : P)
      (hy.trans (map_zero ρ).symm)
    exact ⟨k, by simpa only [smul_zero] using hk⟩
  have hsat : ∀ z, ∃ k : ℕ, (MvPolynomial.X i : P) ^ k • z ∈ LinearMap.range ρ := by
    intro z
    obtain ⟨k, y, hy⟩ := IsLocalizedModule.Away.surj ρ (MvPolynomial.X i : P) z
    exact ⟨k, y, hy.symm⟩
  have hspec : Function.Bijective (QuotSMulTop.map u ρ) :=
    bijective_specialization_of_saturating (gradedTwistSections_res_isGraded f M s le_top) i hker hsat
  obtain ⟨e, he⟩ := exists_dehomogenizedTwistChartEquiv s i le_rfl r hr f M hH
  have hrestrict (p : P) :
      ρ (g p) = p • GrSum.of (twistSections_commute f M V s) 0 (trivialZeroTwist f hH V 1) := by
    exact polynomialTwistSections_restrict f hH s V p
  have hsurj (q : C ⧸ J') : ∃ p : P, J'.mkQ (ρ (g p)) = q := by
    let e₀ := trivialZeroTwist f hH V
    obtain ⟨p, hp⟩ := hπ (e₀.symm (e q))
    refine ⟨p, e.injective ?_⟩
    rw [hrestrict, map_smul, map_smul, he, divTwistSection_zero]
    change π p • e₀ 1 = e q
    exact ((e₀.map_smul (π p) 1).symm.trans (congrArg e₀ (mul_one (π p)))).trans
      ((congrArg e₀ hp).trans (e₀.apply_symm_apply (e q)))
  apply powers_mem_of_surjective_specialization
    (GrSum.grading (twistSections_commute f M ⊤ s))
    (polynomialTwistSections_isGraded f hH s).isHomogeneous_range i
  change (LinearMap.range g).map J.mkQ = ⊤
  apply top_unique
  intro q _
  obtain ⟨p, hp⟩ := hsurj ((QuotSMulTop.map u ρ) q)
  exact Submodule.mem_map.2 ⟨g p, ⟨p, rfl⟩, hspec.1 hp⟩

/-- For large twists, every section is the value of a homogeneous polynomial of the same degree. -/
theorem exists_homogeneous_polynomial_of_large_twist [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [IsNoetherianRing R] (hcov : ⊤ ≤ ⨆ i, nonzeroLocus (s i))
    (r : ∀ i, ι → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hπ : ∀ i, letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := R) (r i))) :
    ∃ b : ℤ, ∀ n, b ≤ n → ∀ x : TwistSections f M H ⊤ n,
      ∃ p ∈ polyGrading ι R n, polynomialTwistSections f hH s p =
        GrSum.of (twistSections_commute f M ⊤ s) n x := by
  obtain ⟨b, hb⟩ := exists_largeDegree_preimage_of_saturating (polynomialTwistSections_isGraded f hH s)
    (fun i => polynomialTwistSections_saturates f hH s i (r i) (hr i) (hπ i))
    (fun n => gradedTwistSections_exactBot f (LB.isLB_trivial X) hH s n hcov)
  exact ⟨b, fun n hn x => hb n hn _ (GrSum.of_mem_grading (twistSections_commute f M ⊤ s) n x)⟩

/-- In sufficiently large degree, the chart ratios of global sections give exactly the
image of the coordinate polynomials of bounded total degree. -/
theorem range_twistRestrictionRatio_eq [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [IsNoetherianRing R] (hcov : ⊤ ≤ ⨆ i, nonzeroLocus (s i))
    (r : ∀ i, ι → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hπ : ∀ i, letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := R) (r i))) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ i,
      letI := sectionAlgebra f (nonzeroLocus (s i))
      LinearMap.range (twistRestrictionRatio f hH s i n) =
        (MvPolynomial.restrictTotalDegree ι R n).map (MvPolynomial.aeval (R := R) (r i)).toLinearMap := by
  obtain ⟨b, hb⟩ := exists_homogeneous_polynomial_of_large_twist f hH s hcov r hr hπ
  refine ⟨b.toNat, fun n hn i => ?_⟩
  let V := nonzeroLocus (s i)
  letI := sectionAlgebra f V
  let π : P →ₐ[R] Γ(X, V) := MvPolynomial.aeval (r i)
  have hbn : b ≤ (n : ℤ) := by omega
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨p, hp, hx⟩ := hb n hbn x
    have hd := (mem_polyGrading_natCast.mp hp).totalDegree_le
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hd,
      (twistRestrictionRatio_eval f hH s i (r i) (hr i) n p x hx).symm⟩
  · rintro ⟨p, hp, hy⟩
    have hri : r i i = 1 := sectionRatio_self s i le_rfl (r i) (hr i) hH
    obtain ⟨F, hF, he⟩ := DegreeGrowth.exists_isHomogeneous_eval₂Hom_eq
      (algebraMap R Γ(X, V)) (r i) i hri p ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp)
    have hG := polynomialTwistSections_isGraded f hH s (mem_polyGrading_natCast.mpr hF)
    obtain ⟨x, hx⟩ := (GrSum.mem_grading _).1 hG
    have hv : π F = y := he.trans hy
    exact ⟨x, (twistRestrictionRatio_eval f hH s i (r i) (hr i) n F x hx.symm).trans hv⟩

end GlobalTheory.LineBundleSections
