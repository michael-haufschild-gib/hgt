/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldNormSequence

/-!
# Cyclic degree-two cohomology as a norm quotient

For a finite cyclic Galois extension `L/K`, the degree-two Galois cohomology of units is the
quotient of `Kˣ` by norms from `Lˣ`.  This is the cohomological form of the cyclic-algebra
parameter group and a direct precursor to local class field theory.  It does not yet identify
this cohomology group with a Brauer group or construct local reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- Base-field units, viewed as the fixed units in the cyclic degree-two resolution. -/
noncomputable def cyclicGaloisH2FixedUnitsBaseAddHom [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ →+ cyclicGaloisH2FixedUnits K L where
  toFun := fun a => ⟨cyclicGaloisBaseUnitsMap (K := K) (L := L) a, by
    change Additive.ofMul (Units.map (cyclicGaloisGenerator K L).toMonoidHom
        (Units.map (algebraMap K L) a.toMul)) -
        Additive.ofMul (Units.map (algebraMap K L) a.toMul) = 0
    have hfixed : Units.map (cyclicGaloisGenerator K L).toMonoidHom
        (Units.map (algebraMap K L) a.toMul) =
          Units.map (algebraMap K L) a.toMul := by
      apply Units.ext
      exact (cyclicGaloisGenerator K L).commutes _
    rw [hfixed, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add _ _ _

/-- Every fixed unit in the cyclic degree-two resolution comes from a base-field unit. -/
theorem cyclicGaloisH2FixedUnitsBaseAddHom_surjective [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (cyclicGaloisH2FixedUnitsBaseAddHom K L) := by
  intro x
  obtain ⟨y, hy⟩ := cyclicGaloisH2FixedUnit_exists_base_unit K L x
  refine ⟨Additive.ofMul y, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  change Units.map (algebraMap K L) y = cyclicGaloisH2FixedUnit K L x
  exact hy

/-- The base-field embedding is injective on cyclic degree-two fixed-unit representatives. -/
theorem cyclicGaloisH2FixedUnitsBaseAddHom_injective [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (cyclicGaloisH2FixedUnitsBaseAddHom K L) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  have hval := congrArg Subtype.val hxy
  have hunits := congrArg Additive.toMul hval
  exact congrArg Units.val hunits

/-- The cyclic fixed-unit representatives are canonically the additive presentation of `Kˣ`. -/
noncomputable def cyclicGaloisH2FixedUnitsBaseAddEquiv [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ ≃+ cyclicGaloisH2FixedUnits K L :=
  AddEquiv.ofBijective (cyclicGaloisH2FixedUnitsBaseAddHom K L)
    ⟨cyclicGaloisH2FixedUnitsBaseAddHom_injective K L,
      cyclicGaloisH2FixedUnitsBaseAddHom_surjective K L⟩

/-- The cyclic degree-two projection expressed directly on base-field units. -/
noncomputable def cyclicGaloisH2BaseProjection [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ →+ cyclicGaloisH2 K L :=
  (cyclicGaloisH2Projection K L).comp (cyclicGaloisH2FixedUnitsBaseAddHom K L)

/-- Every cyclic degree-two cohomology class has a base-field-unit representative. -/
theorem cyclicGaloisH2BaseProjection_surjective [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (cyclicGaloisH2BaseProjection K L) := by
  intro z
  obtain ⟨x, hx⟩ := cyclicGaloisH2Projection_surjective K L z
  obtain ⟨y, hy⟩ := cyclicGaloisH2FixedUnitsBaseAddHom_surjective K L x
  exact ⟨y, by rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply, hy, hx]⟩

/-- The additive subgroup of base-field units that are norms from the cyclic extension. -/
noncomputable def cyclicGaloisH2BaseNormImage [FiniteDimensional K L] :
    AddSubgroup (Additive Kˣ) :=
  (cyclicGaloisAdditiveNormUnits K L).range

/-- A degree-reduced valuation descends through the cyclic norm quotient whenever the valuation
of every norm is a degree-th power.  This is the generic construction behind an unramified local
`H²` invariant with values in `ℤ/nℤ`. -/
noncomputable def cyclicGaloisH2BaseNormQuotient_tameValModNat
    [FiniteDimensional K L]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n) :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L →+ ZMod n :=
  QuotientAddGroup.lift (cyclicGaloisH2BaseNormImage K L) (tameValModNat vK n) (by
    intro a ha
    rw [AddMonoidHom.mem_ker]
    rcases ha with ⟨x, hx⟩
    rw [← hx]
    change tameValModNat vK n
      (Additive.ofMul (Units.map (Algebra.norm K) (Additive.toMul x))) = 0
    exact tameValModNat_norm_eq_zero_of_tameValHom vK vL n (Additive.toMul x)
      (hval (Additive.toMul x)))

/-- Reduction of a split integer valuation modulo `n`, in additive presentation. -/
noncomputable def splitValuationModNat {M : Type*} [CommGroup M]
    (v : M →* Multiplicative ℤ) (n : ℕ) : Additive M →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp
    ((AddEquiv.additiveMultiplicative ℤ).toAddMonoidHom.comp v.toAdditive)

/-- Evaluation formula for the degree-reduced split valuation. -/
theorem splitValuationModNat_apply {M : Type*} [CommGroup M]
    (v : M →* Multiplicative ℤ) (n : ℕ) (x : M) :
    splitValuationModNat v n (Additive.ofMul x) =
      ((Multiplicative.toAdd (v x) : ℤ) : ZMod n) := rfl

/-- A unit of valuation one makes reduction of a split integer valuation onto. -/
theorem splitValuationModNat_surjective {M : Type*} [CommGroup M]
    (v : M →* Multiplicative ℤ) (n : ℕ) (u : M)
    (hu : Multiplicative.toAdd (v u) = 1) :
    Function.Surjective (splitValuationModNat v n) := by
  intro z
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨Additive.ofMul (u ^ m), ?_⟩
  rw [splitValuationModNat_apply, map_zpow]
  have huv : v u = Multiplicative.ofAdd (1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    simpa using hu
  rw [huv]
  simp

/-- If norms contain exactly valuation-zero units and a lift of the uniformizer to the `n`th
power, their image is precisely the kernel of valuation modulo `n`. -/
theorem normImage_eq_splitValuationModNat_ker
    {M N : Type*} [CommGroup M] [CommGroup N]
    (v : M →* Multiplicative ℤ) (n : ℕ) (u : M) (Nmap : N →* M)
    (hu : Multiplicative.toAdd (v u) = 1)
    (hnorm : ∀ b : N, splitValuationModNat v n (Additive.ofMul (Nmap b)) = 0)
    (hzero : ∀ a : M, v a = 1 → ∃ b : N, Nmap b = a)
    (huni : ∃ b : N, Nmap b = u ^ (n : ℤ)) :
    Nmap.toAdditive.range = (splitValuationModNat v n).ker := by
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    exact hnorm b
  · intro a ha
    change ((Multiplicative.toAdd (v a.toMul) : ℤ) : ZMod n) = 0 at ha
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha
    obtain ⟨q, hq⟩ := ha
    let m : ℤ := Multiplicative.toAdd (v a.toMul)
    have huv : v u = Multiplicative.ofAdd (1 : ℤ) := by
      apply Multiplicative.toAdd.injective
      simpa using hu
    have hunit : v (a.toMul * u ^ (-m)) = 1 := by
      rw [map_mul, map_zpow, huv]
      apply Multiplicative.toAdd.injective
      change m + (-m) * 1 = 0
      ring
    obtain ⟨b₀, hb₀⟩ := hzero (a.toMul * u ^ (-m)) hunit
    obtain ⟨bπ, hbπ⟩ := huni
    refine ⟨Additive.ofMul (b₀ * bπ ^ q), ?_⟩
    apply Additive.toMul.injective
    change Nmap (b₀ * bπ ^ q) = a.toMul
    rw [map_mul, map_zpow, hb₀, hbπ, ← zpow_mul]
    change (a.toMul * u ^ (-m)) * u ^ ((n : ℤ) * q) = a.toMul
    rw [show (n : ℤ) * q = m from hq.symm, mul_assoc, ← zpow_add,
      neg_add_cancel, zpow_zero, mul_one]

/-- The finite cyclic norm quotient of a split discrete valuation field is `ℤ/nℤ` whenever
valuation-zero units are norms, every norm has valuation divisible by `n`, and a uniformizer
has norm its `n`th power. -/
noncomputable def splitValuationNormQuotientEquiv
    {M N : Type*} [CommGroup M] [CommGroup N]
    (v : M →* Multiplicative ℤ) (n : ℕ) (u : M) (Nmap : N →* M)
    (hu : Multiplicative.toAdd (v u) = 1)
    (hnorm : ∀ b : N, splitValuationModNat v n (Additive.ofMul (Nmap b)) = 0)
    (hzero : ∀ a : M, v a = 1 → ∃ b : N, Nmap b = a)
    (huni : ∃ b : N, Nmap b = u ^ (n : ℤ)) :
    Additive M ⧸ Nmap.toAdditive.range ≃+ ZMod n :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (normImage_eq_splitValuationModNat_ker v n u Nmap hu hnorm hzero huni)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (splitValuationModNat v n)
      (splitValuationModNat_surjective v n u hu))

/-- A finite field-norm quotient is `ℤ/nℤ` when its valuation is split, its valuation-zero units
are norms, and the valuation of every norm is multiplied by its degree. -/
noncomputable def cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a) :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n := by
  apply splitValuationNormQuotientEquiv (tameValHom vK) n u
    (cyclicGaloisNormUnits K L) hu
  · intro b
    change tameValModNat vK n
      (Additive.ofMul (Units.map (Algebra.norm K) b)) = 0
    exact tameValModNat_norm_eq_zero_of_tameValHom vK vL n b (hval b)
  · intro a ha
    exact hzero a ha
  · refine ⟨Units.map (algebraMap K L) u, ?_⟩
    rw [cyclicGaloisNormUnits_algebraMap, hfinrank]
    simp

/-- Norms are exactly the base-field units representing zero in cyclic degree-two cohomology. -/
theorem cyclicGaloisH2BaseNormImage_eq_ker [FiniteDimensional K L] [IsGalois K L] :
    cyclicGaloisH2BaseNormImage K L = (cyclicGaloisH2BaseProjection K L).ker := by
  ext a
  rw [AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply]
    apply (cyclicGaloisH2Projection_eq_zero_iff_exists_field_norm K L _).mpr
    refine ⟨Additive.toMul y, ?_⟩
    change cyclicGaloisH2FixedUnit K L (cyclicGaloisH2FixedUnitsBaseAddHom K L a) =
      Units.map (algebraMap K L)
        (cyclicGaloisNormUnits K L (Additive.toMul y))
    have hbase : cyclicGaloisH2FixedUnit K L (cyclicGaloisH2FixedUnitsBaseAddHom K L a) =
        Units.map (algebraMap K L) (Additive.toMul a) := by
      rfl
    rw [hbase]
    apply Units.ext
    change algebraMap K L ((Additive.toMul a : Kˣ) : K) =
      algebraMap K L ((cyclicGaloisNormUnits K L (Additive.toMul y) : Kˣ) : K)
    simpa [cyclicGaloisAdditiveNormUnits] using
      congrArg (algebraMap K L) (congrArg Units.val (congrArg Additive.toMul hy).symm)
  · intro ha
    rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply] at ha
    obtain ⟨y, hy⟩ :=
      (cyclicGaloisH2Projection_eq_zero_iff_exists_field_norm K L
        (cyclicGaloisH2FixedUnitsBaseAddHom K L a)).mp ha
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective K L
    have hbase : cyclicGaloisH2FixedUnit K L (cyclicGaloisH2FixedUnitsBaseAddHom K L a) =
        Units.map (algebraMap K L) (Additive.toMul a) := by
      rfl
    rw [hbase] at hy
    exact congrArg Units.val hy.symm

/-- **Cyclic degree-two norm quotient.** For a finite cyclic Galois extension, unit cohomology
in degree two is the base-field unit group modulo norms from the extension. -/
noncomputable def cyclicGaloisH2BaseNormQuotientEquiv [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ cyclicGaloisH2 K L :=
  (QuotientAddGroup.quotientAddEquivOfEq (cyclicGaloisH2BaseNormImage_eq_ker K L)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (cyclicGaloisH2BaseProjection K L)
      (cyclicGaloisH2BaseProjection_surjective K L))

/-- A split valuation identifies the cyclic degree-two cohomology of a finite Galois extension
with `ℤ/nℤ` once the corresponding norm quotient has been classified.  This is a finite-level
local `H²` invariant isomorphism; a Brauer-group comparison is separate infrastructure. -/
noncomputable def cyclicGaloisH2SplitValuationEquiv [FiniteDimensional K L] [IsGalois K L]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a) :
    cyclicGaloisH2 K L ≃+ ZMod n :=
  (cyclicGaloisH2BaseNormQuotientEquiv K L).symm.trans
    (cyclicGaloisH2BaseNormQuotientSplitValuationEquiv K L vK vL n u hu hfinrank hval hzero)

/-- Every cyclic degree-two norm-quotient class is killed by the extension degree.  In the
Brauer interpretation, this is the denominator bound for a degree-`n` cyclic parameter. -/
theorem cyclicGaloisH2BaseProjection_finrank_nsmul_eq_zero [FiniteDimensional K L]
    [IsGalois K L] (x : Additive Kˣ) :
    Module.finrank K L • cyclicGaloisH2BaseProjection K L x = 0 := by
  rw [← (cyclicGaloisH2BaseProjection K L).map_nsmul]
  rw [← AddMonoidHom.mem_ker]
  rw [← cyclicGaloisH2BaseNormImage_eq_ker]
  refine ⟨Additive.ofMul (Units.map (algebraMap K L) (Additive.toMul x)), ?_⟩
  apply Additive.toMul.injective
  change cyclicGaloisNormUnits K L
      (Units.map (algebraMap K L) (Additive.toMul x)) =
    Additive.toMul (Module.finrank K L • x)
  rw [cyclicGaloisNormUnits_algebraMap]
  simp

/-- The entire cyclic degree-two cohomology group is annihilated by the extension degree.
This is the cohomological torsion bound carried by degree-`n` cyclic Brauer parameters. -/
theorem cyclicGaloisH2_finrank_nsmul_eq_zero [FiniteDimensional K L] [IsGalois K L]
    (z : cyclicGaloisH2 K L) : Module.finrank K L • z = 0 := by
  obtain ⟨x, hx⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [← hx]
  exact cyclicGaloisH2BaseProjection_finrank_nsmul_eq_zero K L x

/-- The explicit base-unit quotient by field norms is annihilated by the extension degree.
This is the quotient-level form needed to compare cyclic local parameters with rational local
invariants. -/
theorem cyclicGaloisH2BaseNormQuotient_finrank_nsmul_eq_zero [FiniteDimensional K L]
    [IsGalois K L] (z : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :
    Module.finrank K L • z = 0 := by
  apply (cyclicGaloisH2BaseNormQuotientEquiv K L).injective
  rw [map_nsmul, map_zero]
  exact cyclicGaloisH2_finrank_nsmul_eq_zero K L
    (cyclicGaloisH2BaseNormQuotientEquiv K L z)

end GaloisForLFunctions.HTGeometry.ABHN
