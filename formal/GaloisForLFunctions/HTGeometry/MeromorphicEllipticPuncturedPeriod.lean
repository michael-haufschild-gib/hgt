import GaloisForLFunctions.HTGeometry.MeromorphicEllipticProductSpecialization
import GaloisForLFunctions.HTGeometry.MeromorphicOrderLocalPeriod
import GaloisForLFunctions.HTGeometry.MeromorphicThetaFamilyPoleOrbitBoundaryLocal
import GaloisForLFunctions.HTGeometry.AnalyticSubringFractionEvaluation

/-!
# Elliptic meromorphic fractions with punctured-local periods

Membership in the concrete elliptic meromorphic field is a field-level fixedness statement.
An arbitrary entire quotient representing such an element need not be literally periodic at the
zeros of its denominator.  This module supplies the correct bridge: field-level translation
fixedness gives periodicity on every punctured neighbourhood, which is enough to transport
meromorphic orders and prove compact pole-orbit finiteness.

The final theorem is the finite-family theta orbit obstruction with an elliptic-field certificate.
It has no pointwise convention at poles in its hypotheses.
-/

open Complex Set Filter Topology Function Metric
open scoped Topology

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticPuncturedPeriodDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticPuncturedPeriodComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticPuncturedPeriodComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

/-! ## From field fixedness to a punctured-local period -/

/-- If an entire quotient is fixed in the global meromorphic fraction field by translation by
`q`, then the displayed quotient functions agree after that translation on the punctured
neighbourhood of every point. -/
theorem analyticFraction_eventually_periodic_of_field_fixed
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (Filter.principal Set.univ) f =
      (a : Germ (Filter.principal Set.univ) ℂ))
    (hgb : Germ.coeRingHom (Filter.principal Set.univ) g =
      (b : Germ (Filter.principal Set.univ) ℂ))
    (q : ℂ)
    (hfixed : addTranslationMeroEquiv q
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)
    (p : ℂ) :
    (∀ᶠ z in nhdsWithin p ({p} : Set ℂ)ᶜ,
      f (z + q) / g (z + q) = f z / g z) := by
  let fq : ℂ → ℂ := fun z ↦ f (z + q)
  let gq : ℂ → ℂ := fun z ↦ g (z + q)
  have hTba : addTranslationAnalyticEquiv q b ≠ 0 :=
    fun hzero ↦ hb ((addTranslationAnalyticEquiv q).injective (by simpa using hzero))
  have hfq : AnalyticOnNhd ℂ fq Set.univ :=
    hf.comp (analyticOnNhd_addTranslation q _) (Set.mapsTo_univ _ _)
  have hgq : AnalyticOnNhd ℂ gq Set.univ :=
    hg.comp (analyticOnNhd_addTranslation q _) (Set.mapsTo_univ _ _)
  have hfqa : Germ.coeRingHom (Filter.principal Set.univ) fq =
      (addTranslationAnalyticEquiv q a :
        Germ (Filter.principal Set.univ) ℂ) := by
    change Germ.ofFun (l := Filter.principal Set.univ) (fun z ↦ f (z + q)) =
      (a : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation q)
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
    rw [← hfa]
    rfl
  have hgqb : Germ.coeRingHom (Filter.principal Set.univ) gq =
      (addTranslationAnalyticEquiv q b :
        Germ (Filter.principal Set.univ) ℂ) := by
    change Germ.ofFun (l := Filter.principal Set.univ) (fun z ↦ g (z + q)) =
      (b : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation q)
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
    rw [← hgb]
    rfl
  have hfield :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (addTranslationAnalyticEquiv q a) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (addTranslationAnalyticEquiv q b) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b := by
    rw [← addTranslationMeroEquiv_algebraMap,
      ← addTranslationMeroEquiv_algebraMap, ← map_div₀]
    exact hfixed
  have hlocal := analyticSubring_fraction_eventuallyEq_of_field_eq
    hTba hb hgq hg hfqa hgqb hfa hgb hfield p
  simpa only [fq, gq] using hlocal

/-! ## Integer elliptic periods in the concrete field -/

/-- Every integer combination of `1` and `tau` fixes an element of the concrete
`(1,tau)`-elliptic field. -/
theorem addTranslationMeroEquiv_fixed_of_mem_ellipticMeroField_int
    {tau : ℂ} {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ ellipticMeroField tau) (a b : ℤ) :
    addTranslationMeroEquiv (a • (1 : ℂ) + b • tau) x = x := by
  have hperiods := (mem_ellipticMeroField_iff tau x).mp hx
  have h1 : (1 : ℂ) ∈ meromorphicTranslationStabilizer x := hperiods.1
  have htau : tau ∈ meromorphicTranslationStabilizer x := hperiods.2
  exact AddSubgroup.add_mem (meromorphicTranslationStabilizer x)
    (AddSubgroup.zsmul_mem _ h1 a)
    (AddSubgroup.zsmul_mem _ htau b)

/-! ## Compact pole finiteness without assigned values at poles -/

/-- An entire quotient representing an element of `E_tau` has finitely many poles on every
nontorsion translation orbit.  Elliptic periodicity is used only punctured-locally, exactly where
meromorphic order is insensitive to the value at the centre. -/
theorem poleIndexSet_finite_of_ellipticField_fraction
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (Filter.principal Set.univ) f =
      (a : Germ (Filter.principal Set.univ) ℂ))
    (hgb : Germ.coeRingHom (Filter.principal Set.univ) g =
      (b : Germ (Filter.principal Set.univ) ℂ))
    {tau p q : ℂ} (htau : 0 < tau.im)
    (helliptic :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ∈
        ellipticMeroField tau)
    (hq : ThetaTranslationNontorsion tau q) :
    (poleIndexSet (fun z ↦ f z / g z) p q).Finite := by
  let phi : ℂ → ℂ := fun z ↦ f z / g z
  let r : ℤ → ℂ := fun n ↦ ellipticReduce tau (additiveOrbitPoint p q n)
  let T : Set ℂ :=
    {z ∈ closedBall (0 : ℂ) (1 + ‖tau‖) | meromorphicOrderAt phi z < 0}
  have hphi : MeromorphicOn phi Set.univ :=
    hf.meromorphicOn.div hg.meromorphicOn
  have hT : T.Finite := meromorphic_poles_closedBall_finite hphi (1 + ‖tau‖)
  have hmap : Set.MapsTo r (poleIndexSet phi p q) T := by
    intro n hn
    rw [poleIndexSet, Set.mem_setOf_eq] at hn
    change r n ∈ closedBall (0 : ℂ) (1 + ‖tau‖) ∧
      meromorphicOrderAt phi (r n) < 0
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact ellipticReduce_norm_le tau (additiveOrbitPoint p q n)
    · let A : ℤ := ⌊tauCoordX tau (additiveOrbitPoint p q n)⌋
      let B : ℤ := ⌊tauCoordY tau (additiveOrbitPoint p q n)⌋
      let period : ℂ := A • (1 : ℂ) + B • tau
      have hfixed := addTranslationMeroEquiv_fixed_of_mem_ellipticMeroField_int
        helliptic A B
      have hper : ∀ᶠ z in nhdsWithin (r n) ({r n} : Set ℂ)ᶜ,
          phi (z + period) = phi z := by
        simpa only [phi, period] using
          analyticFraction_eventually_periodic_of_field_fixed
            hb hf hg hfa hgb period hfixed (r n)
      have hord := meromorphicOrderAt_add_eq_of_eventually_periodic hper
      have hdecomp := ellipticReduce_lattice_decomposition
        (z := additiveOrbitPoint p q n) htau.ne'
      have hdecomp' : additiveOrbitPoint p q n = r n + period := by
        simpa only [r, period, A, B, zsmul_eq_mul, mul_one, add_assoc] using hdecomp
      change meromorphicOrderAt phi (r n) < 0
      rw [← hord]
      convert hn using 2
      exact hdecomp'.symm
  have himage : (r '' poleIndexSet phi p q).Finite :=
    hT.subset (Set.image_subset_iff.mpr hmap)
  apply himage.of_finite_image
  exact (ellipticReduce_injective_on_nontorsion_orbit htau.ne' hq).mono
    (Set.subset_univ _)

/-! ## The theta obstruction with a field-level elliptic certificate -/

/-- A separated finite theta-defect family cannot be punctured-locally equal to a translation
coboundary whose primitive is represented by an arbitrary element of the concrete elliptic field.
No literal periodicity at denominator zeros is assumed. -/
theorem thetaDifferentialFamily_ne_ellipticFieldShiftCoboundary_of_eventuallyEq
    {iota : Type*} [DecidableEq iota] {s : Finset iota}
    {L : iota → Polynomial ℂ} {h : iota → ℂ} {tau q : ℂ}
    (htau : 0 < tau.im)
    (hq : ThetaTranslationNontorsion tau q)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant tau q (h j))
    {i0 : iota} (hi0 : i0 ∈ s) (hLi0 : L i0 ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ i0 →
      ThetaTranslationNonresonant tau q (h j - h i0))
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (Filter.principal Set.univ) f =
      (a : Germ (Filter.principal Set.univ) ℂ))
    (hgb : Germ.coeRingHom (Filter.principal Set.univ) g =
      (b : Germ (Filter.principal Set.univ) ℂ))
    (helliptic :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ∈
        ellipticMeroField tau)
    (heq : ∀ n : ℤ, thetaDifferentialFamilySum s L h tau =ᶠ[
      nhdsWithin (additiveOrbitPoint (thetaHalfPeriod tau - h i0) q n)
        ({additiveOrbitPoint (thetaHalfPeriod tau - h i0) q n} : Set ℂ)ᶜ]
      (fun z ↦ f (z + q) / g (z + q) - f z / g z)) : False := by
  let phi : ℂ → ℂ := fun z ↦ f z / g z
  obtain ⟨hpole, hunique⟩ := thetaDifferentialFamilySum_singleton_poleOrbit
    htau hq hnonres hi0 hLi0 hsep
  apply shiftCoboundary_not_singleton_poleOrbit_of_eventuallyEq phi
    (thetaDifferentialFamilySum s L h tau)
    (thetaHalfPeriod tau - h i0) q
  · intro n
    exact (hf.meromorphicOn.div hg.meromorphicOn) _ (Set.mem_univ _)
  · simpa only [phi] using heq
  · exact poleIndexSet_finite_of_ellipticField_fraction
      hb hf hg hfa hgb htau helliptic hq
  · simpa [additiveOrbitPoint] using hpole
  · exact hunique

end

end GaloisForLFunctions
