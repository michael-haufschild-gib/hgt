import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Unramified.Field

/-! Stalks of smooth schemes over a field are domains. -/

open AlgebraicGeometry CategoryTheory TensorProduct

namespace UpperTheory.Cb

private theorem isDomain_atPrime_of_localization {B : Type*} [CommRing B]
    (M : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    (p : Ideal B) [hp : p.IsPrime] (hM : Disjoint (M : Set B) (p : Set B))
    (h : ∀ (q : Ideal T) [q.IsPrime], IsDomain (Localization.AtPrime q))
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp := by
  let q := p.map (algebraMap B T)
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T p hp hM
  have hc : q.comap (algebraMap B T) = p :=
    IsLocalization.under_map_of_isPrime_disjoint M T hp hM
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime q) q
  haveI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    simpa only [hc] using hloc
  haveI := h q
  let e : Localization.AtPrime q ≃ₐ[B] Bp :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact e.symm.injective.isDomain _

private theorem isDomain_atPrime_of_integrallyClosedIn_pi {B : Type*} [CommRing B]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)] [Algebra B (∀ i, K i)]
    [hB : IsIntegrallyClosedIn B (∀ i, K i)] (p : Ideal B) [p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp := by
  classical
  letI := Fintype.ofFinite ι
  have hinj := (isIntegrallyClosedIn_iff.mp hB).1
  -- The primitive idempotents of the product are integral over the image of B.
  have he (i : ι) : ∃ e : B, algebraMap B (∀ i, K i) e = Pi.single i 1 := by
    apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, ← Pi.single_mul]
  choose e he using he
  have hsum : ∑ i, e i = 1 := by
    apply hinj
    simp [he, Finset.univ_sum_single, ← Pi.one_def]
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ p := by
    by_contra! H
    exact (inferInstance : p.IsPrime).ne_top
      ((Ideal.eq_top_iff_one _).mpr (hsum ▸ p.sum_mem fun i _ => H i))
  let φ := (Pi.evalRingHom K i).comp (algebraMap B (∀ i, K i))
  let D := φ.range
  letI : Algebra B D := φ.rangeRestrict.toAlgebra
  have hidem : IsIdempotentElem (e i) := by
    apply hinj
    simp [he, ← Pi.single_mul]
  haveI : IsLocalization.Away (e i) D := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem
      (fun x y => ?_) φ.rangeRestrict_surjective
    rw [Subtype.ext_iff, ← hinj.eq_iff, map_mul, map_mul, he]
    change algebraMap B (∀ i, K i) x i = algebraMap B (∀ i, K i) y i ↔ _
    refine ⟨fun eq => funext fun j => ?_, fun eq => ?_⟩
    · by_cases hji : j = i
      · subst j
        simp [eq]
      · simp [hji]
    · simpa using congrFun eq i
  refine isDomain_atPrime_of_localization (.powers (e i)) D p ?_
    (fun q _ => IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

private theorem isIntegrallyClosedIn_tensor_of_smooth {A B L : Type*}
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    [Algebra.Smooth A B] [hL : IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by
  obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp hL
  refine isIntegrallyClosedIn_iff.mpr
    ⟨Algebra.TensorProduct.includeLeft_injective (S := A) hinj, fun {x} hx => ?_⟩
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := A) (S := B) (B := L)).2 ⟨x, hx⟩
  have hy' : Algebra.TensorProduct.map (.id B B) (integralClosure A L).val y = x :=
    congrArg Subtype.val hy
  subst x
  clear hx hy
  induction y with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | tmul b y =>
    obtain ⟨a, ha⟩ := hcl y.2
    refine ⟨a • b, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply,
      Subalgebra.coe_val, ← ha, Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul]
    rfl

/-- Smooth base change preserves integral closedness in a base-changed algebra. -/
theorem isIntegrallyClosedIn_smooth_tensor {A B L : Type*}
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    [Algebra.Smooth A B] [IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) :=
  isIntegrallyClosedIn_tensor_of_smooth

private theorem isDomain_atPrime_of_etale (A : Type*) {B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal B) [p.IsPrime] (Bp : Type*) [CommRing Bp] [Algebra B Bp]
    [IsLocalization.AtPrime Bp p] : IsDomain Bp := by
  let L := FractionRing A
  have h₁ : IsIntegrallyClosedIn B (B ⊗[A] L) := isIntegrallyClosedIn_tensor_of_smooth
  haveI := Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)
  haveI := Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[A] B)
  haveI : IsArtinianRing (L ⊗[A] B) := isArtinian_of_tower L inferInstance
  let e := (Algebra.TensorProduct.comm A B L).toRingEquiv
  haveI : IsArtinianRing (B ⊗[A] L) := e.symm.isArtinianRing
  haveI : IsReduced (B ⊗[A] L) := isReduced_of_injective e e.injective
  letI (m : MaximalSpectrum (B ⊗[A] L)) : Field ((B ⊗[A] L) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  haveI := (((IsArtinianRing.equivPi (B ⊗[A] L)).restrictScalars B).isIntegrallyClosedIn).mp h₁
  exact isDomain_atPrime_of_integrallyClosedIn_pi
    (fun m : MaximalSpectrum (B ⊗[A] L) => (B ⊗[A] L) ⧸ m.asIdeal) p Bp

private theorem isIntegrallyClosed_mvPolynomial_fin (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm
  | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv

/-- A finite-variable polynomial ring over an integrally closed domain is integrally closed. -/
theorem isIntegrallyClosed_fin_polynomialRing (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) :=
  isIntegrallyClosed_mvPolynomial_fin A n

private theorem isDomain_atPrime_of_smooth (A : Type*) {B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [p.IsPrime] (Bp : Type*) [CommRing Bp] [Algebra B Bp]
    [IsLocalization.AtPrime Bp p] : IsDomain Bp := by
  obtain ⟨f, hf, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)
  haveI := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_atPrime_of_localization (.powers f)
    (Localization.Away f) p ?_
    (fun q _ => isDomain_atPrime_of_etale (MvPolynomial (Fin n) A) q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

private theorem isDomain_atPrime_of_smooth_of_comap {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [p.IsPrime] (Ap : Type*) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap (p.comap (algebraMap A B))] [IsDomain Ap] [IsIntegrallyClosed Ap]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp := by
  let M := (p.comap (algebraMap A B)).primeCompl
  letI : Algebra B (Ap ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) :=
    IsLocalization.tensorRight _ _
  refine isDomain_atPrime_of_localization
    (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) p ?_
    (fun q _ => isDomain_atPrime_of_smooth Ap q _) Bp
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha h

/-- Local rings of a smooth scheme over a field are domains. -/
theorem isDomain_stalk_of_smooth_over_field {k : Type*} [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) := by
  let y := f x
  let p : Ideal k := y.asIdeal
  haveI : p.IsPrime := y.isPrime
  letI : Algebra k ((Spec (.of k)).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra k y
  haveI : IsLocalization.AtPrime ((Spec (.of k)).presheaf.stalk (f x)) p :=
    StructureSheaf.IsLocalization.to_stalk k y
  haveI : IsDomain ((Spec (.of k)).presheaf.stalk (f x)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ p.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed ((Spec (.of k)).presheaf.stalk (f x)) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  obtain ⟨U, hU, V, hV, hx, e, -⟩ := Smooth.exists_isStandardSmooth f x
  have hs := f.smooth_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  letI := (Spec (.of k)).presheaf.algebra_section_stalk (⟨f x, e hx⟩ : U)
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  have hUloc := hU.isLocalization_stalk ⟨f x, e hx⟩
  have hcomap :
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Spec (.of k), U) Γ(X, V)) =
        (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hx)
  haveI : IsLocalization.AtPrime ((Spec (.of k)).presheaf.stalk (f x))
      ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Spec (.of k), U) Γ(X, V))) := by
    have hc :
        ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap
          (algebraMap Γ(Spec (.of k), U) Γ(X, V))).primeCompl =
          (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal.primeCompl := by
      ext a
      change a ∉ ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap _) ↔
        a ∉ (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal
      rw [hcomap]
    change IsLocalization _ _
    rw [hc]
    exact hUloc
  exact isDomain_atPrime_of_smooth_of_comap (A := Γ(Spec (.of k), U))
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal ((Spec (.of k)).presheaf.stalk (f x)) (X.presheaf.stalk x)

end UpperTheory.Cb
