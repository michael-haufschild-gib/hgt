import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothStalkDomains
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! Section rings of nonempty affine opens of an integral smooth scheme
over a field are integrally closed. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.SchemeCohomology

private theorem integrallyClosed_etale_domain (A B : Type) [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [Algebra A B] [Algebra.Etale A B] :
    IsIntegrallyClosed B := by
  let L := FractionRing A
  let E := B ⊗[A] L
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A))
  have hinj := FaithfulSMul.algebraMap_injective A B
  have hden : Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero ha (hinj (h.trans (map_zero _).symm)))
  haveI : IsDomain E := IsLocalization.isDomain_of_le_nonZeroDivisors E hden
  haveI := Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)
  haveI : IsArtinianRing (L ⊗[A] B) := IsArtinianRing.of_finite L _
  haveI : IsArtinianRing E := (Algebra.TensorProduct.comm A L B).toRingEquiv.isArtinianRing
  have h := UpperTheory.Cb.isIntegrallyClosedIn_smooth_tensor (A := A) (B := B) (L := L)
  letI : Field E := (IsArtinianRing.isField_of_isDomain E).toField
  letI : IsIntegrallyClosedIn B E := h
  letI : FaithfulSMul B E := (faithfulSMul_iff_algebraMap_injective B E).mpr (isIntegrallyClosedIn_iff.mp h).1
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn B E

private theorem integrallyClosed_standardSmooth {K B : Type} [Field K] [CommRing B] [IsDomain B]
    {d : ℕ} {g : K →+* B} (h : g.IsStandardSmoothOfRelativeDimension d) :
    IsIntegrallyClosed B := by
  obtain ⟨φ, -, hφ⟩ := h.exists_etale_mvPolynomial
  haveI := UpperTheory.Cb.isIntegrallyClosed_fin_polynomialRing K d
  algebraize [φ]
  exact integrallyClosed_etale_domain (MvPolynomial (Fin d) K) B

/-- A nonempty affine chart in an integral smooth scheme is normal. -/
theorem integrallyClosed_smooth_affineOpen {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d s]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X, U) := by
  obtain ⟨S, hS, hstd⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  apply IsIntegrallyClosed.of_localization_maximal
  intro m _ hm
  obtain ⟨x, hx, hx'⟩ : ∃ x ∈ S, x ∉ m := by
    by_contra! hall
    exact hm.ne_top (top_le_iff.mp (hS ▸ Ideal.span_le.mpr hall))
  have hx0 : x ≠ 0 := fun h => hx' (h ▸ m.zero_mem)
  haveI : IsDomain (Localization.Away x) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hx0))
  letI : IsIntegrallyClosed (Localization.Away x) := integrallyClosed_standardSmooth
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _ e (hstd x hx))
  let q := m.map (algebraMap Γ(X, U) (Localization.Away x))
  letI := hm.isPrime
  have hd : Disjoint (Submonoid.powers x : Set Γ(X, U)) (m : Set Γ(X, U)) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime x).mpr hx'
  letI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers x) _ _ hm.isPrime hd
  have hq : q.comap (algebraMap Γ(X, U) (Localization.Away x)) = m :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers x) (Localization.Away x) hm.isPrime hd
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (.powers x) (Localization.AtPrime q) q
  letI : IsLocalization m.primeCompl (Localization.AtPrime q) := by
    simpa only [hq] using hloc
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv m.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime m)).toRingEquiv

end GlobalTheory.SchemeCohomology
