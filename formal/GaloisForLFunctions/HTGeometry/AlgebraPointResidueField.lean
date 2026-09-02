import GaloisForLFunctions.HTGeometry.PrincipalOpenSeparablePresentation
import GaloisForLFunctions.HTGeometry.PrincipalOpenAdjoinRootSpectrumChart
import GaloisForLFunctions.HTGeometry.ABHN.LocalInvariants

/-!
# Residue field at a rational algebra point

A rational point `R →ₐ[k] k` of a `k`-algebra is surjective through the constant scalars.  After
localizing at its kernel, the resulting local ring has residue field canonically equivalent to
`k`.  This is the algebraic bridge from pointwise spectrum topology to local finite-étale fibres.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 2000000

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- Equal ideals have canonically equivalent quotient rings. -/
def idealQuotientRingEquivOfEq {A : Type*} [CommRing A]
    {I J : Ideal A} (h : I = J) : A ⧸ I ≃+* A ⧸ J := by
  subst J
  exact RingEquiv.refl _

@[simp]
theorem idealQuotientRingEquivOfEq_mk {A : Type*} [CommRing A]
    {I J : Ideal A} (h : I = J) (x : A) :
    idealQuotientRingEquivOfEq h (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J x := by
  subst J
  rfl

/-- The quotient equivalence induced by a surjection evaluates quotient representatives by the
original map, after transporting along an equality of kernel ideals. -/
@[simp]
theorem idealQuotientEquivOfSurjective_apply_mk
    {A C : Type*} [CommRing A] [CommRing C]
    (f : A →+* C) (hf : Function.Surjective f)
    (I : Ideal A) (h : RingHom.ker f = I) (x : A) :
    ((idealQuotientRingEquivOfEq h.symm).trans
      (RingHom.quotientKerEquivOfSurjective hf))
        (Ideal.Quotient.mk I x) = f x := by
  change (RingHom.quotientKerEquivOfSurjective hf)
    (idealQuotientRingEquivOfEq h.symm (Ideal.Quotient.mk I x)) = f x
  rw [idealQuotientRingEquivOfEq_mk]
  rfl

/-- The kernel of a rational algebra point is maximal. -/
theorem algebraPointKernel_isMaximal (chi : R →ₐ[k] k) :
    (RingHom.ker chi.toRingHom).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective chi.toRingHom
  intro z
  exact ⟨algebraMap k R z, chi.commutes z⟩

noncomputable instance algebraPointKernel_isPrime (chi : R →ₐ[k] k) :
    (RingHom.ker chi.toRingHom).IsPrime :=
  (algebraPointKernel_isMaximal chi).isPrime

/-- Evaluation of the local ring at a rational algebra point. -/
def algebraPointLocalizationToField (chi : R →ₐ[k] k) :
    Localization (RingHom.ker chi.toRingHom).primeCompl →+* k :=
  IsLocalization.lift
      (M := (RingHom.ker chi.toRingHom).primeCompl)
      (S := Localization (RingHom.ker chi.toRingHom).primeCompl)
      (g := chi.toRingHom) fun y => by
    rw [isUnit_iff_ne_zero]
    intro hy
    have hyNot : (y : R) ∉ RingHom.ker chi.toRingHom := y.property
    exact hyNot hy

@[simp]
theorem algebraPointLocalizationToField_algebraMap (chi : R →ₐ[k] k) (r : R) :
    algebraPointLocalizationToField chi
        (algebraMap R (Localization (RingHom.ker chi.toRingHom).primeCompl) r) = chi r := by
  rw [algebraPointLocalizationToField, IsLocalization.lift_eq]
  rfl

theorem algebraPointLocalizationToField_surjective (chi : R →ₐ[k] k) :
    Function.Surjective (algebraPointLocalizationToField chi) := by
  intro z
  refine ⟨algebraMap R (Localization (RingHom.ker chi.toRingHom).primeCompl)
    (algebraMap k R z), ?_⟩
  rw [algebraPointLocalizationToField_algebraMap, chi.commutes]
  simp

/-- Evaluation has the unique maximal ideal of the point-local ring as its kernel. -/
theorem algebraPointLocalizationToField_ker (chi : R →ₐ[k] k) :
    RingHom.ker (algebraPointLocalizationToField chi) =
      IsLocalRing.maximalIdeal
        (Localization (RingHom.ker chi.toRingHom).primeCompl) := by
  apply (RingHom.ker_isMaximal_of_surjective _
      (algebraPointLocalizationToField_surjective chi)).eq_of_le
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [IsLocalRing.mem_maximalIdeal]
  intro hunit
  exact (hunit.map (algebraPointLocalizationToField chi)).ne_zero hx

/-- The residue field at a rational algebra point is canonically ring-equivalent to the ground
field. -/
def algebraPointResidueFieldRingEquiv (chi : R →ₐ[k] k) :
    IsLocalRing.ResidueField
        (Localization (RingHom.ker chi.toRingHom).primeCompl) ≃+* k :=
  (idealQuotientRingEquivOfEq
      (algebraPointLocalizationToField_ker chi).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (algebraPointLocalizationToField_surjective chi))

@[simp]
theorem algebraPointResidueFieldRingEquiv_residue (chi : R →ₐ[k] k)
    (x : Localization (RingHom.ker chi.toRingHom).primeCompl) :
    algebraPointResidueFieldRingEquiv chi (IsLocalRing.residue _ x) =
      algebraPointLocalizationToField chi x := by
  exact idealQuotientEquivOfSurjective_apply_mk
    (algebraPointLocalizationToField chi)
    (algebraPointLocalizationToField_surjective chi)
    (IsLocalRing.maximalIdeal _)
    (algebraPointLocalizationToField_ker chi) x

/-- The residue-field equivalence respects the ground-field algebra structures. -/
def algebraPointResidueFieldAlgEquiv (chi : R →ₐ[k] k) :
    IsLocalRing.ResidueField
        (Localization (RingHom.ker chi.toRingHom).primeCompl) ≃ₐ[k] k :=
  { algebraPointResidueFieldRingEquiv chi with
    commutes' := fun z => by
      change algebraPointResidueFieldRingEquiv chi
        (IsLocalRing.residue _
          (algebraMap k (Localization (RingHom.ker chi.toRingHom).primeCompl) z)) = z
      rw [algebraPointResidueFieldRingEquiv_residue]
      change algebraPointLocalizationToField chi
        (algebraMap R (Localization (RingHom.ker chi.toRingHom).primeCompl)
          (algebraMap k R z)) = z
      rw [algebraPointLocalizationToField_algebraMap, chi.commutes]
      simp }

open IsLocalRing
open scoped TensorProduct

/-- Canonical base-change map from the tensor residue fibre to the quotient residue fibre. -/
noncomputable def residueTensorToQuotient
    (T N : Type*) [CommRing T] [IsLocalRing T] [CommRing N] [Algebra T N] :
    TensorProduct T (ResidueField T) N →ₐ[ResidueField T] (N ⧸ maxExt T N) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (ResidueField T) (N ⧸ maxExt T N))
    (Ideal.Quotient.mkₐ T (maxExt T N)) fun _ _ => .all _ _

/-- Canonical inverse from the quotient residue fibre to the tensor residue fibre. -/
noncomputable def residueQuotientToTensor
    (T N : Type*) [CommRing T] [IsLocalRing T] [CommRing N] [Algebra T N] :
    (N ⧸ maxExt T N) →ₐ[ResidueField T] TensorProduct T (ResidueField T) N := by
  let gN : N →+* TensorProduct T (ResidueField T) N :=
    (Algebra.TensorProduct.includeRight (R := T)
      (A := ResidueField T) (B := N)).toRingHom
  have hker : maxExt T N ≤ RingHom.ker gN := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : ResidueField T) ⊗ₜ[T] algebraMap T N t = 0
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rw [show algebraMap T (ResidueField T) t = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ht]
    simp
  refine { Ideal.Quotient.lift (maxExt T N) gN hker with
    commutes' := fun z => ?_ }
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  change (1 : ResidueField T) ⊗ₜ[T] algebraMap T N t =
    algebraMap (ResidueField T) (TensorProduct T (ResidueField T) N)
      (Ideal.Quotient.mk (maximalIdeal T) t)
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rfl

/-- The quotient by the extended maximal ideal is the actual tensor-product residue fibre, with
the existing residue-field algebra structure on both sides. -/
noncomputable def residueTensorQuotientAlgEquiv
    (T N : Type*) [CommRing T] [IsLocalRing T] [CommRing N] [Algebra T N] :
    TensorProduct T (ResidueField T) N ≃ₐ[ResidueField T] (N ⧸ maxExt T N) :=
  AlgEquiv.ofAlgHom (residueTensorToQuotient T N)
    (residueQuotientToTensor T N) (by
      apply AlgHom.ext
      intro x
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [residueTensorToQuotient, residueQuotientToTensor]) (by
      apply AlgHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul z n =>
          obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
          change (1 : ResidueField T) ⊗ₜ[T]
              (algebraMap T N t * n) =
            algebraMap T (ResidueField T) t ⊗ₜ[T] n
          rw [← Algebra.smul_def, TensorProduct.tmul_smul]
          simp [Algebra.smul_def]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy)

namespace AlgSpec

open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
variable [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [IsDomain B]
variable [Module.Finite A B] [Algebra.Etale A B]

/-- A finite étale domain algebra induces a local homeomorphism on its complex-point spectra. -/
theorem isLocalHomeomorph_algebraSpectrumProjection_of_finiteEtale :
    IsLocalHomeomorph (algebraSpectrumProjection (R := A) (B := B)) := by
  apply isLocalHomeomorph_algebraSpectrumProjection_of_principalOpen_adjoinRoot
  intro chi
  let chiA : A →ₐ[ℂ] ℂ := algebraSpectrumProjection chi
  let p : Ideal A := RingHom.ker chiA.toRingHom
  letI : p.IsPrime := algebraPointKernel_isPrime chiA
  let T := Localization p.primeCompl
  let N := Localization (p.primeCompl.map (algebraMap A B))
  letI : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T p.primeCompl fun x hx => by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hx0
      exact hx (hx0 ▸ p.zero_mem)
  have hABinj : Function.Injective (algebraMap A B) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hsmul : a • (1 : B) = 0 := by
      simpa [Algebra.smul_def] using ha
    exact (smul_eq_zero.mp hsmul).resolve_right one_ne_zero
  have hNsub : p.primeCompl.map (algebraMap A B) ≤ nonZeroDivisors B := by
    intro b hb
    rw [mem_nonZeroDivisors_iff_ne_zero]
    obtain ⟨a, ha, rfl⟩ := hb
    intro hz
    have ha0 : a = 0 := hABinj (by simpa using hz)
    exact ha (ha0 ▸ p.zero_mem)
  letI : IsDomain N :=
    IsLocalization.isDomain_of_le_nonZeroDivisors N hNsub
  have hunitN : ∀ y : p.primeCompl, IsUnit (algebraMap A N (y : A)) := fun y => by
    change IsUnit (algebraMap B N (algebraMap A B (y : A)))
    let yB : p.primeCompl.map (algebraMap A B) :=
      ⟨algebraMap A B (y : A), by
        change ∃ a ∈ p.primeCompl, algebraMap A B a = algebraMap A B (y : A)
        exact ⟨y, y.property, rfl⟩⟩
    exact IsLocalization.map_units N yB
  let tN : T →+* N := IsLocalization.lift hunitN
  letI : Algebra T N := tN.toAlgebra
  letI : IsScalarTower A T N := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A N a = tN (algebraMap A T a)
    dsimp [tN]
    rw [IsLocalization.lift_eq]
  have hANinj : Function.Injective (algebraMap A N) :=
    (IsLocalization.injective N hNsub).comp hABinj
  have htNinj : Function.Injective tN := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    have haN : algebraMap A N a = 0 := by
      have haN' := (IsLocalization.lift_mk'_spec hunitN a 0 s).mp (by
        simpa [tN] using hx)
      simpa using haN'
    have ha : a = 0 := hANinj (by simpa using haN)
    simp [ha]
  letI : NoZeroSMulDivisors T N := ⟨by
    intro c x hcx
    rw [Algebra.smul_def] at hcx
    rcases mul_eq_zero.mp hcx with hc | hx
    · left
      apply htNinj
      change tN c = 0 at hc
      exact hc.trans (map_zero tN).symm
    · exact Or.inr hx⟩
  let fN : B →ₐ[A] N := IsScalarTower.toAlgHom A B N
  letI : IsLocalizedModule p.primeCompl fN.toLinearMap := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have hy := hunitN y
      rw [show algebraMap A (Module.End A N) (y : A) =
          (Algebra.lmul A N) (algebraMap A N (y : A)) by
        rw [Algebra.lmul_algebraMap]
        rfl]
      exact hy.map (Algebra.lmul A N).toRingHom
    · intro y
      obtain ⟨⟨b, s⟩, hs⟩ :=
        IsLocalization.surj (p.primeCompl.map (algebraMap A B)) y
      obtain ⟨a, ha, has⟩ := s.property
      refine ⟨⟨b, ⟨a, ha⟩⟩, ?_⟩
      simpa [Algebra.smul_def, fN, IsScalarTower.toAlgHom_apply,
        IsScalarTower.algebraMap_apply A B N, has, mul_comm] using hs
    · intro x₁ x₂ hx
      have hx' : algebraMap B N x₁ = algebraMap B N x₂ := by
        simpa [fN, IsScalarTower.toAlgHom_apply] using hx
      obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq
        (M := p.primeCompl.map (algebraMap A B)) (S := N) hx'
      obtain ⟨a, ha, has⟩ := s.property
      refine ⟨⟨a, ha⟩, ?_⟩
      simpa [Algebra.smul_def, has] using hs
  letI : Module.Finite T N :=
    Module.Finite.equiv
      (localizedAlgebraTensorEquiv A p.primeCompl T B N fN).toLinearEquiv
  letI : Algebra.Etale T N :=
    Algebra.Etale.of_equiv
      (localizedAlgebraTensorEquiv A p.primeCompl T B N fN)
  letI : IsAlgClosed (IsLocalRing.ResidueField T) :=
    ABHN.isAlgClosed_of_ringEquiv
      (algebraPointResidueFieldAlgEquiv chiA).symm.toRingEquiv
  letI : CharZero (IsLocalRing.ResidueField T) :=
    (RingHom.charZero_iff
      (ϕ := (algebraPointResidueFieldAlgEquiv chiA).toRingHom)
      (algebraPointResidueFieldAlgEquiv chiA).injective).mpr inferInstance
  letI : Algebra.Etale (IsLocalRing.ResidueField T)
      (TensorProduct T (IsLocalRing.ResidueField T) N) :=
    Algebra.Etale.baseChange T N (IsLocalRing.ResidueField T)
  letI : Algebra.Etale (IsLocalRing.ResidueField T) (N ⧸ maxExt T N) :=
    Algebra.Etale.of_equiv (residueTensorQuotientAlgEquiv T N)
  obtain ⟨theta, g, hg, q, hq, e, he, hsep⟩ :=
    exists_principalOpen_adjoinRoot_equiv_and_separable_of_residue_finiteEtale
      A B p T N fN
  have hchiA : chiA g ≠ 0 := by
    intro hz
    exact hg hz
  have hchi : chi (algebraMap A B g) ≠ 0 := hchiA
  let rootPoint : AlgSpec (AdjoinRoot q) :=
    principalOpenAdjoinRootHomeomorph g q e ⟨chi, hchi⟩
  let sPoint : AlgSpec (Localization.Away g) :=
    adjoinRootBase q rootPoint
  have hbase : (homeomorphLocalizationAway g) sPoint =
      (⟨chiA, hchiA⟩ : {z : AlgSpec A // z g ≠ 0}) := by
    rw [principalOpenAdjoinRootHomeomorph_base]
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    rfl
  have hspec :
      (algebraPointResidueFieldAlgEquiv chiA).toRingHom.comp
          (principalOpenToResidueRingHom A p T g hg) =
        pointRingHom sPoint := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro a
    have ha := DFunLike.congr_fun (congrArg Subtype.val hbase) a
    change (algebraPointResidueFieldAlgEquiv chiA)
        (principalOpenToResidueRingHom A p T g hg
          (algebraMap A (Localization.Away g) a)) =
      sPoint (algebraMap A (Localization.Away g) a)
    rw [principalOpenToResidueRingHom, RingHom.comp_apply,
      principalOpenToLocalizationRingHom, IsLocalization.Away.lift_eq]
    change algebraPointResidueFieldRingEquiv chiA
        (IsLocalRing.residue T (algebraMap A T a)) = _
    rw [algebraPointResidueFieldRingEquiv_residue,
      algebraPointLocalizationToField_algebraMap]
    change chiA a =
      (precomp (IsScalarTower.toAlgHom ℂ A (Localization.Away g)) sPoint) a
    exact ha.symm
  have hsepComplex : (q.map (pointRingHom sPoint)).Separable := by
    have h := hsep.map
      (f := (algebraPointResidueFieldAlgEquiv chiA).toRingHom)
    rw [Polynomial.map_map, hspec] at h
    exact h
  exact ⟨g, hchi, q, hq, e, hsepComplex⟩

end AlgSpec

end


end GaloisForLFunctions.HTGeometry
