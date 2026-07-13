import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Basic

/-!
# The kernel of the universal derivation in characteristic zero

For a characteristic-zero field extension `L / K`, the kernel of the
universal Kähler derivation `D : L → Ω[L/K]` is exactly the relative
algebraic closure of `K` in `L`.

The nontrivial direction is proved without postulating an extension theorem
for derivations.  A transcendental element is included in a transcendence
basis.  On the resulting rational function field, an explicit coordinate
derivation is obtained from the multivariate polynomial partial derivative
and the fraction-field extension.  The remaining algebraic extension is
separable, hence formally étale, so Kähler base change preserves the nonzero
coordinate differential.
-/

open Set IntermediateField MvPolynomial TensorProduct

namespace GaloisForLFunctions

noncomputable section

/-- Transport a field derivation through an algebra equivalence. -/
def transportDerivation
    {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (D : Derivation K A A) : Derivation K B B :=
  Derivation.mk'
    { toFun := fun b ↦ e (D (e.symm b))
      map_add' := by intro x y; simp
      map_smul' := by
        intro k x
        simp only [Algebra.smul_def, RingHom.id_apply]
        rw [map_mul, e.symm.commutes, ← Algebra.smul_def, D.map_smul,
          Algebra.smul_def, map_mul, e.commutes] }
    (by
      intro x y
      change e (D (e.symm (x * y))) =
        x • e (D (e.symm y)) + y • e (D (e.symm x))
      simp only [map_mul, Derivation.leibniz]
      simp [smul_eq_mul])

@[simp] theorem transportDerivation_apply
    {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (D : Derivation K A A) (b : B) :
    transportDerivation e D b = e (D (e.symm b)) := rfl

/-- A coordinate of an algebraically independent family has nonzero
universal differential in the generated rational function field. -/
theorem kaehlerD_adjoin_coordinate_ne_zero
    {ι K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : ι → L} (hx : AlgebraicIndependent K x) (i : ι) :
    let F := IntermediateField.adjoin K (Set.range x)
    let xi : F := ⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩
    KaehlerDifferential.D K F xi ≠ 0 := by
  classical
  dsimp only
  let F := IntermediateField.adjoin K (Set.range x)
  let Q := FractionRing (MvPolynomial ι K)
  let dpoly : Derivation K (MvPolynomial ι K) Q :=
    MvPolynomial.mkDerivation K (fun j ↦ if j = i then 1 else 0)
  let dfrac : Derivation K Q Q := fractionRingDerivation dpoly
  let e : Q ≃ₐ[K] F := hx.aevalEquivField
  let dF : Derivation K F F := transportDerivation e dfrac
  let xi : F :=
    ⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩
  have heX : e.symm xi = algebraMap (MvPolynomial ι K) Q (MvPolynomial.X i) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change x i = (hx.aevalEquivField
      (algebraMap (MvPolynomial ι K) Q (MvPolynomial.X i)) : F)
    rw [hx.aevalEquivField_algebraMap_apply_coe]
    simp
  have hdpoly : dpoly (MvPolynomial.X i) = 1 := by
    simp [dpoly]
  have hdF : dF xi = 1 := by
    rw [transportDerivation_apply, heX]
    rw [fractionRingDerivation_algebraMap]
    rw [hdpoly, map_one]
  intro hzero
  have hmap := congrArg dF.liftKaehlerDifferential hzero
  rw [Derivation.liftKaehlerDifferential_comp_D, map_zero, hdF] at hmap
  exact one_ne_zero hmap

/-- In characteristic zero, an element killed by the universal relative
derivation is algebraic over the base field. -/
theorem isAlgebraic_of_kaehlerD_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    {g : L} (hg : KaehlerDifferential.D K L g = 0) :
    IsAlgebraic K g := by
  classical
  by_contra htrans
  have hgtr : Transcendental K g := htrans
  have hsingle : AlgebraicIndepOn K id ({g} : Set L) := by
    change AlgebraicIndependent K (fun z : ({g} : Set L) ↦ z.1)
    rw [algebraicIndependent_singleton_iff
      (⟨g, Set.mem_singleton g⟩ : ({g} : Set L))]
    exact hgtr
  have hI : (AlgebraicIndependent.matroid K L).Indep ({g} : Set L) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hsingle
  obtain ⟨B, hBbase, hgB⟩ := hI.exists_isBase_superset
  have hB : IsTranscendenceBasis K ((↑) : B → L) :=
    AlgebraicIndependent.matroid_isBase_iff.mp hBbase
  let F := IntermediateField.adjoin K
    (Set.range ((↑) : B → L))
  let gb : F :=
    ⟨g, IntermediateField.subset_adjoin K (Set.range ((↑) : B → L))
      ⟨(⟨g, hgB (Set.mem_singleton g)⟩ : B), rfl⟩⟩
  have hcoord : KaehlerDifferential.D K F gb ≠ 0 := by
    exact kaehlerD_adjoin_coordinate_ne_zero hB.1
      (⟨g, hgB (Set.mem_singleton g)⟩ : B)
  letI : Algebra.IsAlgebraic F L := hB.isAlgebraic_field
  letI : Algebra.IsIntegral F L := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable F L := by infer_instance
  letI : Algebra.FormallyEtale F L :=
    Algebra.FormallyEtale.of_isSeparable F L
  have hbase : algebraMap F L gb = g := rfl
  have htensor :
      (1 : L) ⊗ₜ[F] KaehlerDifferential.D K F gb = 0 := by
    rw [← KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
      K F L gb]
    rw [hbase, hg, map_zero]
  have hinj := Module.Flat.tensorProduct_mk_injective F
    (KaehlerDifferential K F) L
  apply hcoord
  apply hinj
  simpa using htensor

/-- Algebraic elements have zero universal differential in characteristic
zero. -/
theorem kaehlerD_eq_zero_of_isAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    {g : L} (hg : IsAlgebraic K g) :
    KaehlerDifferential.D K L g = 0 := by
  let F := IntermediateField.adjoin K ({g} : Set L)
  let gf : F :=
    ⟨g, IntermediateField.subset_adjoin K ({g} : Set L) (Set.mem_singleton g)⟩
  letI : Algebra.IsAlgebraic K F :=
    IntermediateField.isAlgebraic_adjoin (K := K)
      (S := ({g} : Set L)) (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact hg.isIntegral)
  letI : Algebra.IsIntegral K F := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable K F := by infer_instance
  letI : Algebra.FormallyEtale K F :=
    Algebra.FormallyEtale.of_isSeparable K F
  have hzeroF : KaehlerDifferential.D K F gf = 0 := Subsingleton.elim _ _
  have hmap := congrArg (KaehlerDifferential.map K K F L) hzeroF
  rw [KaehlerDifferential.map_D, map_zero] at hmap
  simpa [gf] using hmap

/-- In characteristic zero the kernel of the universal derivation is exactly
the relative algebraic closure of the base field. -/
theorem kaehlerD_eq_zero_iff_isAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    {g : L} :
    KaehlerDifferential.D K L g = 0 ↔ IsAlgebraic K g :=
  ⟨isAlgebraic_of_kaehlerD_eq_zero,
    kaehlerD_eq_zero_of_isAlgebraic⟩

end

end GaloisForLFunctions
