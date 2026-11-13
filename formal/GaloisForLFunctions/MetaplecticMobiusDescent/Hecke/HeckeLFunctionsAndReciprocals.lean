/-
Hecke L-functions and reciprocals adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.KernelSectorArithmetic
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.ActualPeriodicRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.HeckeCharactersAndThetaProducts

/-!
# Hecke L-functions and reciprocals

Ideal coefficients and the Hecke L-function `HeckeFamily.LFunction`, inverse characters, row
closure and conductor presentation; residue characters and the reciprocal `HeckeReciprocal`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


section
namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

namespace ConductorPresentation

open FiniteFourier FiniteConductor
open scoped Classical

noncomputable section

section Transport

variable {A : Type*} [CommRing A]

def quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ

@[simp] theorem quotientCharacter_mk (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl

theorem primitive_quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ

theorem source_le_comap (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

theorem unit_factorization_of_mask (M K : Ideal A) (hMK : M ≤ K)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0) :
    φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMK).toMonoidHom) =
      χ.toUnitHom := by
  apply MonoidHom.ext
  intro u
  apply Units.ext
  change φ (Ideal.Quotient.factor hMK (u : A ⧸ M)) = χ (u : A ⧸ M)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have h := hmask a
  simp only [ha, u.isUnit, ite_true] at h
  simpa only [← ha, Ideal.Quotient.factor_mk] using h.symm

end Transport



theorem comap_ne_bot (M : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)] (I : Ideal (Eisenstein.O ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  let : Finite ((Eisenstein.O ⧸ M) ⧸ I) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hpos : 0 < (I.comap (Ideal.Quotient.mk M)).absNorm := by
    rw [absNorm_comap_eq_quotient_card]
    exact Nat.card_pos
  intro hzero
  rw [hzero, Ideal.absNorm_bot] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_primitive_presentation_above_quotient
    (M : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)] (χ : MulChar (Eisenstein.O ⧸ M) ℂ)
    (J : Ideal (Eisenstein.O ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      M ≤ K ∧ J.comap (Ideal.Quotient.mk M) ≤ K ∧ K ≠ ⊥ ∧
      IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : Eisenstein.O, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, ψ, hJI, hψ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_quotient_above_with_norm_and_mask M χ J hJ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I ψ,
    source_le_comap M I, Ideal.comap_mono hJI, comap_ne_bot M I,
    primitive_quotientCharacter M I ψ hprimitive, hnorm, ?_⟩
  intro a
  simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

theorem exists_primitive_presentation (M : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)]
    (χ : MulChar (Eisenstein.O ⧸ M) ℂ) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : Eisenstein.O, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm

theorem exists_primitive_presentation_above
    (M L : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (Eisenstein.O ⧸ M) ℂ)
    (hL : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ L.absNorm ∧
      ∀ a : Eisenstein.O, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  simpa only [Ideal.comap_map_mk hML] using
    exists_primitive_presentation_above_quotient M χ (L.map (Ideal.Quotient.mk M)) hL

theorem exists_primitive_product_presentation
    (M L₁ L₂ : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)] (hML₁ : M ≤ L₁) (hML₂ : M ≤ L₂)
    (χ ψ : MulChar (Eisenstein.O ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L₁.map (Ideal.Quotient.mk M)))
    (hψ : FactorsThroughIdeal ψ (L₂.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      M ≤ K ∧ L₁ ⊓ L₂ ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ L₁.absNorm * L₂.absNorm ∧
      ∀ a : Eisenstein.O, χ (Ideal.Quotient.mk M a) * ψ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_product_with_norm_and_mask M χ ψ
      (L₁.map (Ideal.Quotient.mk M)) (L₂.map (Ideal.Quotient.mk M)) hχ hψ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I φ,
    source_le_comap M I, ?_, comap_ne_bot M I,
    primitive_quotientCharacter M I φ hprimitive, ?_, ?_⟩
  · have h := Ideal.comap_mono (f := Ideal.Quotient.mk M) hJI
    simpa only [Ideal.comap_inf, Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using h
  · simpa only [Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using hnorm
  · intro a
    simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

theorem exists_primitive_power_presentation
    (M L : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (Eisenstein.O ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) (n : ℕ) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ L.absNorm ∧
      ∀ a : Eisenstein.O, (χ ^ n) (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 :=
  exists_primitive_presentation_above M L hML (χ ^ n) (hχ.pow n)

end

end ConductorPresentation

end
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace ResidueCharacter

open FiniteFourier FiniteConductor
open ConductorPresentation
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

def inflate {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    MulChar (A ⧸ M) ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    (Units.map (Ideal.Quotient.factor hML).toMonoidHom))

theorem inflate_toUnitHom {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    (inflate hML χ).toUnitHom =
      χ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hML).toMonoidHom) := by
  simp only [inflate, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]

theorem inflate_apply_unit {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (u : (A ⧸ M)ˣ) :
    inflate hML χ u = χ (Ideal.Quotient.factor hML (u : A ⧸ M)) :=
  MulChar.ofUnitHom_coe _ u

theorem inflate_apply {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (x : A ⧸ M) :
    inflate hML χ x = if IsUnit x then χ (Ideal.Quotient.factor hML x) else 0 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simpa only [u.isUnit, ite_true] using inflate_apply_unit hML χ u
  · simp only [hx, ite_false, MulChar.map_nonunit _ hx]

theorem inflate_mk {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) (a : A) :
    inflate hML χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then χ (Ideal.Quotient.mk L a) else 0 := by
  simpa only [Ideal.Quotient.factor_mk] using inflate_apply hML χ (Ideal.Quotient.mk M a)

theorem inflate_factorsThrough {M L : Ideal A} [Finite (A ⧸ M)]
    (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    FactorsThroughIdeal (inflate hML χ) (L.map (Ideal.Quotient.mk M)) := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have haL : a - 1 ∈ L := by
    apply (Ideal.mem_quotient_iff_mem hML).mp
    simpa only [map_sub, map_one, ha] using hu
  have ha1 : Ideal.Quotient.mk L a = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr haL
  rw [inflate_apply_unit, ← ha, Ideal.Quotient.factor_mk, ha1, map_one]

theorem inflate_trans {M L K : Ideal A} (hML : M ≤ L) (hLK : L ≤ K)
    (χ : MulChar (A ⧸ K) ℂ) :
    inflate hML (inflate hLK χ) = inflate (hML.trans hLK) χ := by
  apply MulChar.ext
  intro u
  rw [inflate_apply_unit]
  let v : (A ⧸ L)ˣ := Units.map (Ideal.Quotient.factor hML).toMonoidHom u
  change inflate hLK χ (v : A ⧸ L) = _
  rw [inflate_apply_unit, inflate_apply_unit]
  exact congrArg χ (Ideal.Quotient.factor_comp_apply hML hLK (u : A ⧸ M))

theorem inflate_global_units {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk L u) = 1) :
    ∀ u : Aˣ, inflate hML χ (Ideal.Quotient.mk M u) = 1 := by
  intro u
  rw [inflate_mk]
  simp only [u.isUnit.map (Ideal.Quotient.mk M), ite_true, hχ]

theorem isUnit_mk_inf_iff (I J : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk (I ⊓ J) a) ↔
      IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a) := by
  constructor
  · intro h
    constructor
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left)))
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right)))
  · rintro ⟨hI, hJ⟩
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hI
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hJ
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hbI : a * b - 1 ∈ I :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    have hcJ : a * c - 1 ∈ J :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hc)
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (I ⊓ J) (b + c - a * b * c), ?_⟩
    rw [← map_mul]
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
    have hid : a * (b + c - a * b * c) - 1 = -((a * b - 1) * (a * c - 1)) := by ring
    rw [hid]
    exact ⟨I.neg_mem (I.mul_mem_right _ hbI), J.neg_mem (J.mul_mem_left _ hcJ)⟩

theorem finite_quotient_inf (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    Finite (A ⧸ I ⊓ J) := by
  let f : A ⧸ I ⊓ J →+* (A ⧸ I) × (A ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  apply Finite.of_injective f
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
    Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩

def product (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    MulChar (A ⧸ I ⊓ J) ℂ :=
  inflate inf_le_left χ * inflate inf_le_right ψ

theorem product_mk (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (a : A) :
    product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) a) =
      χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) := by
  rw [product, MulChar.mul_apply, inflate_mk, inflate_mk]
  by_cases ha : IsUnit (Ideal.Quotient.mk (I ⊓ J) a)
  · simp only [ha, ite_true]
  · simp only [ha, ite_false, zero_mul]
    by_cases hI : IsUnit (Ideal.Quotient.mk I a)
    · have hJ : ¬ IsUnit (Ideal.Quotient.mk J a) := fun hJ =>
        ha ((isUnit_mk_inf_iff I J a).mpr ⟨hI, hJ⟩)
      rw [MulChar.map_nonunit _ hJ, mul_zero]
    · rw [MulChar.map_nonunit _ hI, zero_mul]

theorem product_global_units (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ)
    (ψ : MulChar (A ⧸ J) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Aˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∀ u : Aˣ, product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) u) = 1 := by
  intro u
  rw [product_mk, hχ, hψ, one_mul]

section PrimitiveProduct



theorem exists_primitive_product (I J : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ I)] [Finite (Eisenstein.O ⧸ J)]
    (χ : MulChar (Eisenstein.O ⧸ I) ℂ) (ψ : MulChar (Eisenstein.O ⧸ J) ℂ) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ I.absNorm * J.absNorm ∧
      ∀ a : Eisenstein.O, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by
  let : Finite (Eisenstein.O ⧸ I ⊓ J) := finite_quotient_inf I J
  obtain ⟨K, φ, hIK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation (I ⊓ J) (product I J χ ψ)
  refine ⟨K, φ, hIK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul I J), ?_⟩
  intro a
  simpa only [product_mk, isUnit_mk_inf_iff] using hmask a

theorem exists_primitive_product_global_units
    (I J : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ I)] [Finite (Eisenstein.O ⧸ J)]
    (χ : MulChar (Eisenstein.O ⧸ I) ℂ) (ψ : MulChar (Eisenstein.O ⧸ J) ℂ)
    (hχ : ∀ u : Eisenstein.Oˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Eisenstein.Oˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ I.absNorm * J.absNorm ∧
      (∀ u : Eisenstein.Oˣ, φ (Ideal.Quotient.mk K u) = 1) ∧
      ∀ a : Eisenstein.O, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hIK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_product I J χ ψ
  refine ⟨K, φ, hIK, hK, hprimitive, hnorm, ?_, hmask⟩
  intro u
  have h := hmask (u : Eisenstein.O)
  simpa only [hχ, hψ, one_mul, u.isUnit.map (Ideal.Quotient.mk I),
    u.isUnit.map (Ideal.Quotient.mk J), and_self, ite_true] using h.symm

end PrimitiveProduct

end

end ResidueCharacter

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace IdealCharacter

open FiniteFourier FiniteConductor
open ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

abbrev UnitInvariant (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : Prop :=
  ∀ u : Aˣ, χ (Ideal.Quotient.mk M u) = 1

theorem residue_eq_of_associated (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {a b : A} (hab : Associated a b) :
    χ (Ideal.Quotient.mk M a) = χ (Ideal.Quotient.mk M b) := by
  obtain ⟨u, rfl⟩ := hab
  rw [map_mul, map_mul, hχ u, mul_one]

theorem isUnit_mk_iff_isCoprime (M : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span ({a} : Set A)) M := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton_sup]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hba : b * a - 1 ∈ M :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    refine ⟨b, -(b * a - 1), M.neg_mem hba, ?_⟩
    ring
  · rintro ⟨b, c, hc, hbc⟩
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have h := congrArg (Ideal.Quotient.mk M) hbc
    simpa only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc,
      add_zero, map_one] using h

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

def value (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (I : Ideal A) : ℂ :=
  if I = ⊥ then 0 else χ (Ideal.Quotient.mk M (generator I))

omit [IsDomain A] in
theorem value_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : value M χ ⊥ = 0 := by
  simp only [value, ite_true]

theorem value_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    value M χ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) := by
  have hI : Ideal.span ({a} : Set A) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  simp only [value, hI, ite_false]
  exact residue_eq_of_associated M χ hχ (associated_generator_span_self a)

def ofResidue (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    Ideal A →*₀ ℂ where
  toFun := value M χ
  map_zero' := value_bot M χ
  map_one' := by
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top, map_one] using
      value_span M χ hχ (one_ne_zero : (1 : A) ≠ 0)
  map_mul' I J := by
    by_cases hI : I = ⊥
    · subst I
      simp only [Ideal.bot_mul, value_bot, zero_mul]
    by_cases hJ : J = ⊥
    · subst J
      simp only [Ideal.mul_bot, value_bot, mul_zero]
    let a := generator I
    let b := generator J
    have ha : a ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have hb : b ≠ 0 := fun h => hJ ((eq_bot_iff_generator_eq_zero J).mpr h)
    have hIa : Ideal.span ({a} : Set A) = I := Ideal.span_singleton_generator I
    have hJb : Ideal.span ({b} : Set A) = J := Ideal.span_singleton_generator J
    calc
      value M χ (I * J) = value M χ (Ideal.span ({a * b} : Set A)) := by
        rw [← Ideal.span_singleton_mul_span_singleton, hIa, hJb]
      _ = χ (Ideal.Quotient.mk M (a * b)) := value_span M χ hχ (mul_ne_zero ha hb)
      _ = χ (Ideal.Quotient.mk M a) * χ (Ideal.Quotient.mk M b) := by
        rw [map_mul, map_mul]
      _ = value M χ I * value M χ J := by
        rw [← hIa, ← hJb, value_span M χ hχ ha, value_span M χ hχ hb]

@[simp] theorem ofResidue_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := value_bot M χ

theorem ofResidue_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    ofResidue M χ hχ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) :=
  value_span M χ hχ ha

theorem ofResidue_of_generator (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {I : Ideal A} (hI : I ≠ ⊥) {a : A}
    (ha : Ideal.span ({a} : Set A) = I) :
    ofResidue M χ hχ I = χ (Ideal.Quotient.mk M a) := by
  have ha0 : a ≠ 0 := by
    intro h
    apply hI
    simpa only [h, Ideal.span_singleton_zero] using ha.symm
  rw [← ha, ofResidue_span M χ hχ ha0]

omit [IsDomain A] [IsPrincipalIdealRing A] in
theorem norm_residue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (a : A ⧸ M) : ‖χ a‖ ≤ 1 := by
  let : Fintype (A ⧸ M)ˣ := Fintype.ofFinite _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    have hn : ‖χ (u : A ⧸ M)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using h
    exact hn.le
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    exact zero_le_one

theorem norm_ofResidue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) (I : Ideal A) :
    ‖ofResidue M χ hχ I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · rw [hI, ofResidue_bot, norm_zero]
    exact zero_le_one
  · change ‖value M χ I‖ ≤ 1
    simp only [value, hI, ite_false]
    exact norm_residue_le_one M χ _

omit [IsDomain A] [IsPrincipalIdealRing A] in

theorem one_unitInvariant (M : Ideal A) : UnitInvariant M (1 : MulChar (A ⧸ M) ℂ) := by
  intro u
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk M))

theorem ofResidue_one (M : Ideal A) (I : Ideal A) :
    ofResidue M 1 (one_unitInvariant M) I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have heq := ofResidue_span M 1 (one_unitInvariant M) hg
    rw [Ideal.span_singleton_generator] at heq
    rw [heq]
    simp only [hI, ite_false]
    have hu : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    by_cases hc : IsCoprime I M
    · simp only [hc, ite_true]
      exact MulChar.one_apply (hu.mpr hc)
    · simp only [hc, ite_false]
      exact MulChar.map_nonunit _ (fun h => hc (hu.mp h))

theorem ofResidue_one_top (I : Ideal A) :
    ofResidue (⊤ : Ideal A) 1 (one_unitInvariant ⊤) I = if I = ⊥ then 0 else 1 := by
  rw [ofResidue_one]
  have h : IsCoprime I (⊤ : Ideal A) := Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq I)
  simp only [h, ite_true]

theorem ofResidue_source_mask (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I = if IsCoprime I M then ofResidue K φ hφ I else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_self]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have h := hmask (generator I)
    have hcop : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span K φ hφ hg,
      Ideal.span_singleton_generator] at h
    simpa only [hcop] using h

theorem ofResidue_finite_deletion (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]

theorem ofResidue_product (M N : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) (I : Ideal A) :
    ofResidue (M ⊓ N) (ResidueCharacter.product M N χ ψ)
        (ResidueCharacter.product_global_units M N χ ψ hχ hψ) I =
      ofResidue M χ hχ I * ofResidue N ψ hψ I := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, mul_zero]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    conv_lhs => rw [← Ideal.span_singleton_generator I]
    rw [ofResidue_span _ _ _ hg, ResidueCharacter.product_mk]
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span N ψ hψ hg,
      Ideal.span_singleton_generator]

section Primitive



theorem exists_primitive_associate (M : Ideal Eisenstein.O) [Finite (Eisenstein.O ⧸ M)]
    (χ : MulChar (Eisenstein.O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      (∀ I : Ideal Eisenstein.O, ofResidue M χ hχ I =
        if IsCoprime I M then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal Eisenstein.O, ofResidue M χ hχ I =
        ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  obtain ⟨K, φ, hMK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_presentation M χ
  have hφ : UnitInvariant K φ := by
    intro u
    have h := hmask (u : Eisenstein.O)
    simpa only [hχ u, u.isUnit.map (Ideal.Quotient.mk M), ite_true] using h.symm
  exact ⟨K, φ, hφ, hMK, hK, hprimitive, hnorm,
    ofResidue_source_mask M K χ φ hχ hφ hmask,
    ofResidue_finite_deletion M K χ φ hχ hφ hmask⟩

theorem exists_primitive_product_associate (M N : Ideal Eisenstein.O)
    [Finite (Eisenstein.O ⧸ M)] [Finite (Eisenstein.O ⧸ N)]
    (χ : MulChar (Eisenstein.O ⧸ M) ℂ) (ψ : MulChar (Eisenstein.O ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal Eisenstein.O) (φ : MulChar (Eisenstein.O ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ M.absNorm * N.absNorm ∧
      (∀ I : Ideal Eisenstein.O, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal Eisenstein.O, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by
  let : Finite (Eisenstein.O ⧸ M ⊓ N) := ResidueCharacter.finite_quotient_inf M N
  obtain ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm, hmask, hdelete⟩ :=
    exists_primitive_associate (M ⊓ N) (ResidueCharacter.product M N χ ψ)
      (ResidueCharacter.product_global_units M N χ ψ hχ hψ)
  refine ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul M N), ?_, ?_⟩
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hmask I)
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hdelete I)

end Primitive

end Principal

end

end IdealCharacter

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeFamily

def Character.product (χ ψ : Character) : Character :=
  Character.ofResidue (χ.modulus ⊓ ψ.modulus)
    (Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot ψ.modulus_ne_bot)
    (ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue)
    (ResidueCharacter.product_global_units _ _ _ _ χ.unit_trivial ψ.unit_trivial)

theorem elementCoeff_product (χ ψ : Character) (z : O) :
    elementCoeff (χ.product ψ) z = elementCoeff χ z * elementCoeff ψ z :=
  ResidueCharacter.product_mk _ _ _ _ z

def Character.inverse (χ : Character) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue⁻¹
  unit_trivial u := by simp [MulChar.inv_apply_eq_inv', χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

def Character.power (χ : Character) (n : ℕ) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue ^ n
  unit_trivial u := by
    let v := Units.map (Ideal.Quotient.mk χ.modulus).toMonoidHom u
    change (χ.residue ^ n) (v : O ⧸ χ.modulus) = 1
    rw [MulChar.pow_apply_coe]
    change χ.residue (Ideal.Quotient.mk χ.modulus u) ^ n = 1
    simp [χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

theorem elementCoeff_power_of_unit (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl

end HeckeFamily

end

end

noncomputable section
namespace EisensteinLatticeCount
open Eisenstein
open scoped Classical

/-- Norm-one coordinates identify the six Eisenstein units. -/
theorem natCard_units_eq_six : Nat.card Oˣ = 6 := by
  let f : Oˣ → unitCoordinates := fun u => ⟨Coordinates.coords u.val, unit_coordinate_mem u⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact Coordinates.coordinateEquiv.injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro z
    have hq : q z.val = 1 := (q_eq_one_iff_unitCoordinates z.val).mpr z.property
    have hnorm : Coordinates.eval z.val.1 z.val.2 *
        conjO (Coordinates.eval z.val.1 z.val.2) = 1 := by
      rw [Coordinates.eval_mul_conj]
      change ((q z.val : ℤ) : O) = 1
      rw [hq, Int.cast_one]
    let u : Oˣ := ⟨Coordinates.eval z.val.1 z.val.2,
      conjO (Coordinates.eval z.val.1 z.val.2), hnorm, (mul_comm _ _).trans hnorm⟩
    refine ⟨u, Subtype.ext ?_⟩
    exact Coordinates.coords_eval _ _
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩), Nat.card_eq_fintype_card]
  norm_num [Fintype.card_coe, unitCoordinates]

end EisensteinLatticeCount
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def idealCoeff (χ : Character) : Ideal O →*₀ ℂ :=
  IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial

@[simp] theorem idealCoeff_zero (χ : Character) : idealCoeff χ 0 = 0 := map_zero _

theorem idealCoeff_span (χ : Character) {z : O} (hz : z ≠ 0) :
    idealCoeff χ (Ideal.span {z}) = elementCoeff χ z :=
  IdealCharacter.ofResidue_span χ.modulus χ.residue χ.unit_trivial hz

theorem coordinateElement_eq_baseline (a b : ℤ) :
    coordinateElement a b = Eisenstein.Coordinates.eval a b := rfl

def coordinateEquiv : (ℤ × ℤ) ≃ O :=
  Equiv.ofBijective (fun n => coordinateElement n.1 n.2)
    ⟨fun _ _ h => Prod.ext
      (Eisenstein.Coordinates.unique_coordinates h).1
      (Eisenstein.Coordinates.unique_coordinates h).2,
      HeckeCoordinates.coordinateElement_surjective⟩

theorem normForm_eq_absNorm_span (n : ℤ × ℤ) :
    EisensteinTheta.normForm n.1 n.2 =
      (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℝ) := by
  rw [coordinateElement_eq_baseline,
    ← ringComplex_norm_sq_eq_absNorm_span,
    Eisenstein.Coordinates.complex_norm_eval_sq]
  simp only [EisensteinTheta.normForm, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two]

def elementTerm (χ : Character) (s : ℂ) (z : O) : ℂ :=
  elementCoeff χ z / (Ideal.absNorm (Ideal.span {z}) : ℂ) ^ s

def idealTerm (χ : Character) (s : ℂ) (I : Ideal O) : ℂ :=
  idealCoeff χ I / (Ideal.absNorm I : ℂ) ^ s

theorem elementTerm_coordinate (χ : Character) (s : ℂ) (n : ℤ × ℤ) :
    elementTerm χ s (coordinateEquiv n) =
      elementCoeff χ (coordinateElement n.1 n.2) /
        (EisensteinTheta.normForm n.1 n.2 : ℂ) ^ s := by
  change elementCoeff χ (coordinateElement n.1 n.2) /
    (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℂ) ^ s = _
  rw [normForm_eq_absNorm_span]
  rw [Complex.ofReal_natCast]

theorem elementTerm_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (elementTerm χ s) (continuedLattice χ s) := by
  apply coordinateEquiv.hasSum_iff.mp
  change HasSum (fun n => elementTerm χ s (coordinateEquiv n)) _
  simpa only [elementTerm_coordinate] using continuedLattice_hasSum χ hs

theorem elementTerm_zero (χ : Character) {s : ℂ} (hs : s ≠ 0) :
    elementTerm χ s 0 = 0 := by
  simp [elementTerm, Complex.zero_cpow hs]

theorem elementTerm_unit_mul (χ : Character) (s : ℂ) (u : Oˣ) (z : O) :
    elementTerm χ s ((u : O) * z) = elementTerm χ s z := by
  unfold elementTerm
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem elementTerm_idealGenerator (χ : Character) (s : ℂ)
    (I : NonzeroIdeal) :
    elementTerm χ s (cubicIdealGenerator I.val) = idealTerm χ s I.val := by
  unfold elementTerm idealTerm
  rw [span_cubicIdealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator χ.modulus χ.residue χ.unit_trivial
    I.property (span_cubicIdealGenerator I.val)).symm

theorem continuedLattice_eq_six_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    continuedLattice χ s = 6 * ∑' I : Ideal O, idealTerm χ s I := by
  have hs₀ : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := SchwartzPlanePoisson.tsum_unit_invariant_ideals (elementTerm χ s)
    (elementTerm_hasSum χ hs).summable (elementTerm_zero χ hs₀)
    (elementTerm_unit_mul χ s)
  rw [(elementTerm_hasSum χ hs).tsum_eq, EisensteinLatticeCount.natCard_units_eq_six] at h
  simp_rw [elementTerm_idealGenerator] at h
  have hsum : (∑' I : NonzeroIdeal, idealTerm χ s I.val) =
      ∑' I : Ideal O, idealTerm χ s I := by
    apply tsum_subtype_eq_of_support_subset
    intro I hI hzero
    exact hI (by rw [hzero]; unfold idealTerm; rw [map_zero]; exact zero_div _)
  rwa [hsum] at h

def LFunction (χ : Character) (s : ℂ) : ℂ := continuedLattice χ s / 6

theorem LFunction_eq_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = ∑' I : Ideal O, idealTerm χ s I := by
  rw [LFunction, continuedLattice_eq_six_ideal_tsum χ hs]
  ring

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

theorem LFunction_entire_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6

end HeckeFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace HeckeIdealSeries
abbrev PrimeIdeal := {P : Ideal Eisenstein.O // Prime P}

def primeProduct (s : Finset PrimeIdeal) : Ideal Eisenstein.O := ∏ P ∈ s, P.val

def primeSet (I : Ideal Eisenstein.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)

@[simp] theorem mem_primeSet (I : Ideal Eisenstein.O) (P : PrimeIdeal) :
    P ∈ primeSet I ↔ P.val ∈ primeSupport I := by
  simp only [primeSet, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨Q,hQ⟩
    have hv := congrArg Subtype.val hQ
    simpa only [←hv] using Q.property
  · intro h
    exact ⟨⟨P.val,h⟩,rfl⟩

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal Eisenstein.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal Eisenstein.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal Eisenstein.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

def mobiusPrimeCoeff (w : Ideal Eisenstein.O → ℂ) (I : Ideal Eisenstein.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal Eisenstein.O → ℂ) (I : Ideal Eisenstein.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal Eisenstein.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal Eisenstein.O → ℂ) :
    (∑' I : Ideal Eisenstein.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal Eisenstein.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal Eisenstein.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

lemma prime_norm_two_le (P : PrimeIdeal) : 2 ≤ Ideal.absNorm P.val := by
  have h0 : Ideal.absNorm P.val ≠ 0 := fun h => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.val ≠ 1 := by
    intro h
    apply P.property.not_unit
    rw [Ideal.absNorm_eq_one_iff.mp h]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal Eisenstein.O) from isUnit_one)
  omega

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)


lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)


lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx


end HeckeIdealSeries
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical
namespace HeckeIdealSeries
noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := O) n).toFinset, weight I


lemma normFiber_tsum (a : Ideal Eisenstein.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal Eisenstein.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal Eisenstein.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOf_absNorm_eq (S := Eisenstein.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈(Ideal.finite_setOf_absNorm_eq (S := Eisenstein.O) n).toFinset,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,(Set.Finite.mem_toFinset (Ideal.finite_setOf_absNorm_eq (S := Eisenstein.O) n)).mp hI⟩ : {I : Ideal Eisenstein.O // Ideal.absNorm I=n}))
  · intro I hI
    exact Finset.mem_univ _
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro I hI
    exact ⟨I.val,(Set.Finite.mem_toFinset (Ideal.finite_setOf_absNorm_eq (S := Eisenstein.O) n)).mpr I.property,rfl⟩
  · intro I hI
    rfl

lemma idealDirichlet_fiber (a : Ideal Eisenstein.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal Eisenstein.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal Eisenstein.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal Eisenstein.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by rw [←I.property,h,map_zero])
      rw [CubicEisenstein.fullIdealWeight,if_neg hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

lemma idealDirichlet_summable (a : Ideal Eisenstein.O→ℂ) (ha : ∀I,‖a I‖≤1) (s : ℂ) (hs : 1< s.re) :
    Summable (fun I : Ideal Eisenstein.O => a I*CubicEisenstein.fullIdealWeight s I) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun I => ?_) (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem idealDirichlet_eq_LSeries (a : Ideal Eisenstein.O→ℂ) (ha : ∀I,‖a I‖≤1)
    (s : ℂ) (hs : 1< s.re) :
    (∑'I : Ideal Eisenstein.O,a I*CubicEisenstein.fullIdealWeight s I)=LSeries (normFiberCoeff a) s := by
  have hh := (idealDirichlet_summable a ha s hs).hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑'I : {I : Ideal Eisenstein.O // Ideal.absNorm I=n},
    a I.val*CubicEisenstein.fullIdealWeight s I.val) _ at hh
  simp_rw [idealDirichlet_fiber] at hh
  exact hh.tsum_eq.symm


end HeckeIdealSeries
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace CenteredMomentSupport
open UniqueFactorizationMonoid

theorem primeSupport_disjoint_iff {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Disjoint (primeSupport I) (primeSupport J) ↔ IsCoprime I J := by
  constructor
  · intro h
    have hr : IsRelPrime I J := (isRelPrime_iff_no_prime_factors hI).mpr (by
      intro P hPI hPJ hP
      apply Finset.disjoint_left.mp h
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hI).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPI⟩
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hJ).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    exact associated_iff_eq.mp (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hr))
  · intro h
    exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors h.isRelPrime)

end CenteredMomentSupport

namespace IdealEuler

open Eisenstein UniqueFactorizationMonoid

open HeckeIdealSeries (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

def normWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := CubicEisenstein.fullIdealWeight s
  map_zero' := by simp [CubicEisenstein.fullIdealWeight]
  map_one' := by simp [CubicEisenstein.fullIdealWeight]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp [CubicEisenstein.fullIdealWeight, hI]
    by_cases hJ : J = 0
    · simp [CubicEisenstein.fullIdealWeight, hJ]
    simp only [CubicEisenstein.fullIdealWeight, hI, hJ, mul_ne_zero hI hJ,
      ite_false, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

def weighted (a : Ideal O →*₀ ℂ) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := a I * normWeight s I
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' I J := by simp only [map_mul]; ring

def series (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := ∑' I : Ideal O, weighted a s I

def inverseSeries (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I : ℂ) * weighted a s I

theorem weighted_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => ‖weighted a s I‖) := by
  apply (CubicEisenstein.fullIdealWeight_summable_norm s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem weighted_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => weighted a s I) :=
  (weighted_summable_norm a ha s hs).of_norm

theorem inverse_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖(moebius I : ℂ) * weighted a s I‖) := by
  apply (weighted_summable_norm a ha s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (IdealCoprimeBilinearSieve.moebius_norm_le_one I)

theorem series_eq_LSeries (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = LSeries (HeckeIdealSeries.normFiberCoeff a) s :=
  HeckeIdealSeries.idealDirichlet_eq_LSeries a ha s hs

theorem inverseSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s * series a s = 1 := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (moebius p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (inverse_summable_norm a ha s hs).mul_norm (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, ((moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (inverse_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone

theorem series_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : series a s ≠ 0 := by
  intro hz
  have h := inverseSeries_mul_series a ha s hs
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem primeValueHom_eq (f : Ideal O →*₀ ℂ) : CanonicalRowCompletion.primeValueHom f = f := by
  ext I
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  · change (if I = 0 then 0 else ((normalizedFactors I).map f).prod) = f I
    simp only [hI, ite_false]
    rw [← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖HeckeIdealSeries.primeNormPower P s‖ < 1
  rw [HeckeIdealSeries.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := HeckeIdealSeries.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  HeckeIdealSeries.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := HeckeIdealSeries.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [HeckeIdealSeries.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [HasProd, Finset.prod_inv_distrib, heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

def deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) : Ideal O →*₀ ℂ :=
  CanonicalRowCompletion.primeValueHom
    (fun I => if I ∈ S.image Subtype.val then 0 else a I)

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [if_pos ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (HeckeIdealSeries.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ HeckeIdealSeries.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← CenteredMomentSupport.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := support_prime hPM
      exact h ⟨P, hp⟩ (HeckeIdealSeries.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((HeckeIdealSeries.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (HeckeIdealSeries.primeSet M) a I

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ HeckeIdealSeries.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (HeckeIdealSeries.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

theorem series_ofResidue_source_mask (M K : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ K)] (χ : MulChar (O ⧸ M) ℂ) (φ : MulChar (O ⧸ K) ℂ)
    (hχ : IdealCharacter.UnitInvariant M χ) (hφ : IdealCharacter.UnitInvariant K φ)
    (hmask : ∀ x : O, χ (Ideal.Quotient.mk M x) =
      if IsUnit (Ideal.Quotient.mk M x) then φ (Ideal.Quotient.mk K x) else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series (IdealCharacter.ofResidue M χ hχ) s =
      series (IdealCharacter.ofResidue K φ hφ) s *
        ∏ P ∈ HeckeIdealSeries.primeSet M,
          (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) :=
  series_of_coprime_mask M hM _ _ (IdealCharacter.norm_ofResidue_le_one K φ hφ)
    (IdealCharacter.ofResidue_source_mask M K χ φ hχ hφ hmask) s hs

theorem exists_primitive_series_associate (M : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ M)] (χ : MulChar (O ⧸ M) ℂ) (hχ : IdealCharacter.UnitInvariant M χ) :
    ∃ (K : Ideal O) (φ : MulChar (O ⧸ K) ℂ) (hφ : IdealCharacter.UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ FiniteFourier.IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ (s : ℂ), 1 < s.re →
        series (IdealCharacter.ofResidue M χ hχ) s =
          series (IdealCharacter.ofResidue K φ hφ) s *
            ∏ P ∈ HeckeIdealSeries.primeSet M,
              (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) := by
  obtain ⟨K, φ, hφ, hMK, hK, hp, hn, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate M χ hχ
  let : Finite (O ⧸ K) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hMK)
  refine ⟨K, φ, hφ, hMK, hK, hp, hn, ?_⟩
  intro s hs
  exact series_of_coprime_mask M hM _ _
    (IdealCharacter.norm_ofResidue_le_one K φ hφ) hmask s hs

end

end IdealEuler

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_le_one (χ : Character) (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (χ : Character) (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)

theorem LFunction_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_ne_zero (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem inverseSeries_mul_LFunction (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff χ) s * LFunction χ s = 1 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.inverseSeries_mul_series (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem LFunction_eq_normFiber_LSeries (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LSeries (HeckeIdealSeries.normFiberCoeff (idealCoeff χ)) s := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_eq_LSeries (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

end HeckeFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeZeroSupremum
open HeckeFamily

def zeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel : Set ℝ := insert (1 / 2) zeroRealParts

def beta : ℝ := sSup zeroSetWithSentinel

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

theorem exists_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hεsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
      (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ beta - ε < s.re := by
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    zeroSet_bddAbove hε hεsmall
  obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hpos, hpole, hz, hlt⟩

theorem beta_le_seven_eighths_of_uniform_margin
    (hbound : 7 / 8 < beta →
      ∃ «ω» σ : ℝ, 0 < «ω» ∧ «ω» < beta - 7 / 8 ∧ 0 < σ ∧
        ∀ (χ : Character) (s : ℂ), 0 < s.re →
          (s ≠ 1 ∨ χ.residue ≠ 1) → LFunction χ s = 0 →
            s.re ≤ beta - Supremum.continuationMargin beta «ω» σ) :
    beta ≤ 7 / 8 := by
  apply Supremum.seven_eighths_of_uniform_margin_with_sentinel zeroSet_bddAbove
  intro hbeta
  obtain ⟨«ω», σ, hω, hωb, hσ, hzeros⟩ := hbound hbeta
  refine ⟨«ω», σ, hω, hωb, hσ, ?_⟩
  rintro x ⟨χ, s, hpos, hpole, hz, rfl⟩
  exact hzeros χ s hpos hpole hz

end HeckeZeroSupremum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_product (χ ψ : Character) (I : Ideal O) :
    idealCoeff (χ.product ψ) I = idealCoeff χ I * idealCoeff ψ I :=
  IdealCharacter.ofResidue_product _ _ _ _ _ _ I

theorem exists_primitive_character (χ : Character) :
    ∃ ψ : Character,
      χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate χ.modulus χ.residue χ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

theorem exists_primitive_product_character (χ ψ : Character) :
    ∃ ρ : Character,
      χ.modulus ⊓ ψ.modulus ≤ ρ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      ρ.modulus.absNorm ≤ χ.modulus.absNorm * ψ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I * idealCoeff ψ I =
        if IsCoprime I (χ.modulus ⊓ ψ.modulus) then idealCoeff ρ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_product_associate χ.modulus ψ.modulus
      χ.residue ψ.residue χ.unit_trivial ψ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

end HeckeFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace CanonicalRowCompletion
/-- Away from the ramified prime, the modulus nine is coprime. -/
lemma nine_coprime_of_not_lambda_dvd (c : O) (hc : ¬lambda ∣ c) :
    IsCoprime (9 : O) c := by
  have hL : IsCoprime lambda c :=
    residue_lambda_prime.irreducible.coprime_iff_not_dvd.mpr hc
  have h3 : IsCoprime (3 : O) c := (hL.mul_left hL).of_isCoprime_of_dvd_left
    (by simpa only [pow_two] using three_dvd_lambda_sq)
  simpa only [show (3 : O) * 3 = 9 by norm_num] using h3.mul_left h3
end CanonicalRowCompletion

namespace HeckeRowClosure
open HeckeFamily

theorem periodic_of_primary (M : Ideal O)
    (hM : M ≤ Ideal.span {lambda ^ 2}) (G F : O →* ℂ)
    (hF : CanonicalCoefficientClass.FactorsModulo M F)
    (hu : ∀ (u : Oˣ) x, G ((u : O) * x) = G x)
    (hz : ∀ x, lambda ∣ x → G x = 0)
    (hagree : ∀ x, lambda ^ 2 ∣ x - 1 → G x = F x) :
    CanonicalCoefficientClass.FactorsModulo M G := by
  intro x y hxy
  have hdiff : lambda ^ 2 ∣ x - y := Ideal.mem_span_singleton.mp (hM hxy)
  have hdiff' : lambda ∣ x - y := (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hdiff
  by_cases hx : lambda ∣ x
  · have hy : lambda ∣ y := by
      convert dvd_sub hx hdiff' using 1 ; ring
    rw [hz x hx, hz y hy]
  · have hg := primaryIdealGenerator_span_ne_zero_iff x |>.mpr hx
    have hspec := primaryIdealGenerator_spec (Ideal.span {x}) hg
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
    have hp : lambda ^ 2 ∣ (u : O) * x - 1 := by
      have hp' : lambda ^ 2 ∣ primaryIdealGenerator (Ideal.span {x}) - 1 := hspec.2
      rwa [mul_comm, hu']
    have hq : lambda ^ 2 ∣ (u : O) * y - 1 := by
      have hd := hdiff.trans (dvd_mul_left (x-y) (u : O))
      convert dvd_sub hp hd using 1 ; ring
    rw [← hu u x, ← hu u y, hagree _ hp, hagree _ hq]
    apply hF
    simpa only [mul_sub] using M.mul_mem_left (u : O) hxy

def quotientRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul

@[simp] theorem quotientRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    quotientRow M G hG (Ideal.Quotient.mk M z) = G z := rfl

def residueRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : MulChar (O ⧸ M) ℂ :=
  MulChar.ofUnitHom (Units.map (quotientRow M G hG))

theorem residueRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    residueRow M G hG (Ideal.Quotient.mk M z) =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := by
  by_cases hz : IsUnit (Ideal.Quotient.mk M z)
  · obtain ⟨u, hu⟩ := hz
    rw [if_pos (hu ▸ u.isUnit), ← hu]
    change MulChar.ofUnitHom (Units.map (quotientRow M G hG)) (u : O ⧸ M) = G z
    rw [MulChar.ofUnitHom_coe]
    change quotientRow M G hG (u : O ⧸ M) = G z
    rw [hu, quotientRow_mk]
  · rw [if_neg hz]
    exact MulChar.map_nonunit _ hz

def rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) : Character :=
  Character.ofResidue M hM (residueRow M G hG) (by
    intro u
    rw [residueRow_mk, if_pos (u.isUnit.map (Ideal.Quotient.mk M)), hu])

theorem elementCoeff_rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) (z : O) :
    elementCoeff (rowCharacter M hM G hG hu) z =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := residueRow_mk M G hG z

def elementHom (η : Character) : O →* ℂ where
  toFun := elementCoeff η
  map_one' := elementCoeff_one η
  map_mul' := elementCoeff_mul η

theorem elementHom_periodic (η : Character) :
    CanonicalCoefficientClass.FactorsModulo η.modulus (elementHom η) := by
  intro x y hxy
  apply congrArg η.residue
  exact Ideal.Quotient.eq.mpr hxy

theorem elementHom_norm (η : Character) (x : O) : ‖elementHom η x‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem rowTwist_unit_mul (η : Character) (m f z : O) (u : Oˣ) (n : O) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z ((u : O)*n) =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  change elementCoeff η ((u : O)*n) * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {(u : O)*n}) = elementCoeff η n * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem rowTwist_unit (η : Character) (m f z : O) (u : Oˣ) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z (u : O) = 1 := by
  simpa using rowTwist_unit_mul η m f z u 1

theorem rowTwist_periodic (η : Character) (m f z : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : lambda ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*lambda^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r})
      (CanonicalRowCompletion.rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _
    (CanonicalRowCompletion.actualPeriodicRow (elementHom η) m u a b r
      ((CanonicalQuadraticSieve.supported_iff_native _).mp hr))
    (CanonicalRowCompletion.actualPeriodicRow_periodic _ _ (elementHom_periodic η) _ _ _ _ _
      ((CanonicalQuadraticSieve.supported_iff_native _).mp hr))
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : lambda ^ 2 ∣ (3 : O) := Eisenstein.lambda_sq_dvd_three
    have hd72 : lambda ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_right.trans Ideal.mul_le_left).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((CanonicalRowCompletion.supported_span_iff n).mp hs).1 hn
  · exact CanonicalRowCompletion.rowTwist_eq_actualPeriodicRow_primary
      _ _ _ _ hmLam hm2 u a b r ((CanonicalQuadraticSieve.supported_iff_native _).mp hr) hpr hx

theorem rowTwist_nonzero_coprime (η : Character) (m f z n : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    CanonicalQuadraticSieve.Supported (Ideal.span {n}) ∧ IsCoprime n (m^6*f^4*z) := by
  have hs : CanonicalQuadraticSieve.Supported (Ideal.span {n}) := by
    by_contra h
    exact hn (CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
      ((CanonicalQuadraticSieve.supported_iff_native _).not.mp h))
  refine ⟨hs, ?_⟩
  have hrow : CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n}) ≠ 0 :=
    right_ne_zero_of_mul hn
  have hp := pow_ne_zero 6 hrow
  rw [← CanonicalRowCompletion.idealRowHom_argument_pow _ _ _
      ((CanonicalQuadraticSieve.supported_iff_native _).mp hs).1,
    CanonicalRowCompletion.idealRowHom_sixth_mask _ _
      ((CanonicalQuadraticSieve.supported_iff_native _).mp hs)] at hp
  by_cases hc : IsCoprime (Ideal.span {n}) (Ideal.span {m^6*f^4*z})
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mp hc
  · simp [hc] at hp

theorem rowTwist_nonzero_unit (η : Character) (m f z n : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*lambda^a*(2 : O)^b*r)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}) n) := by
  obtain ⟨hs, hc⟩ := rowTwist_nonzero_coprime η m f z n hmLam hm2 hn
  have hm : IsCoprime n m := hc.of_isCoprime_of_dvd_right ⟨m^5*f^4*z, by ring⟩
  have hr : IsCoprime n r := hc.of_isCoprime_of_dvd_right
    ⟨m^6*((u : O)*lambda^a*(2 : O)^b), by
      rw [show m^6*f^4*z = m^6*(f^4*z) by ring, hx]; ring⟩
  have h2 := hm.of_isCoprime_of_dvd_right hm2
  have h9 := (CanonicalRowCompletion.nine_coprime_of_not_lambda_dvd n
    ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1).symm
  have h72 : IsCoprime n (72 : O) := by
    convert (h2.pow_right : IsCoprime n ((2 : O)^3)).mul_right h9 using 1 ; norm_num
  have he : elementCoeff η n ≠ 0 := left_ne_zero_of_mul hn
  have hη : IsCoprime (Ideal.span {n}) η.modulus := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
    exact MulChar.apply_ne_zero_iff.mp he
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff,
    IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  exact ⟨⟨⟨hη, (Ideal.isCoprime_span_singleton_iff _ _).mpr hm⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h72⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hr⟩

theorem exists_row_character (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r
    ((CanonicalQuadraticSieve.supported_iff_native _).mpr hr) hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z), ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

def rowConductorBound (η : Character) (m f z : O) : ℕ :=
  η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm *
    ((Ideal.span {f}).absNorm ^ 4 * (Ideal.span {z}).absNorm)

theorem row_modulus_norm_le (η : Character) (m f z : O)
    (hf : f ≠ 0) (hz : z ≠ 0) (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*lambda^a*(2 : O)^b*r) :
    (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}).absNorm ≤
      rowConductorBound η m f z := by
  have hprod : (Ideal.span {f^4*z} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz)
  let : Finite (O ⧸ Ideal.span {f^4*z}) := Ring.HasFiniteQuotients.finiteQuotient hprod
  have hle : (Ideal.span {f^4*z} : Ideal O) ≤ Ideal.span {r} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨(u : O)*lambda^a*(2 : O)^b, by rw [hx]; ring⟩
  have hn := FiniteConductor.absNorm_le_of_le hle
  have heq : (Ideal.span {f^4*z} : Ideal O) = (Ideal.span {f})^4 * Ideal.span {z} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [heq, map_mul, map_pow] at hn
  simpa only [rowConductorBound, map_mul] using
    Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn

theorem exists_row_character_with_conductor (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, χ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      ∀ n : O, elementCoeff χ n =
        CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r
    ((CanonicalQuadraticSieve.supported_iff_native _).mpr hr) hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z),
    row_modulus_norm_le η m f z hf hz u a b r hx, ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

theorem idealCoeff_eq_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero, zero_mul]
  let n := cubicIdealGenerator I
  have hn : n ≠ 0 := cubicIdealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := span_cubicIdealGenerator I
  rw [← hs, idealCoeff_span χ hn, heq]
  change elementCoeff η n * _ = idealCoeff η (Ideal.span {n}) * _
  rw [idealCoeff_span η hn]
  rfl

theorem exists_primitive_row (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      (∀ I : Ideal O, idealCoeff χ I =
        idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I) ∧
      (∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0) := by
  obtain ⟨χ, hnorm, heq⟩ := exists_row_character_with_conductor η m f z hm hf hz hmLam hm2
  obtain ⟨ψ, _, hp, hn, hmask⟩ := exists_primitive_character χ
  exact ⟨χ, ψ, hp, hn.trans hnorm, idealCoeff_eq_row η χ m f z heq, hmask⟩

end HeckeRowClosure

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

def rows (S : Finset (Ideal O)) : Set O :=
  {u | u ≠ 0 ∧ ∀ P ∈ normalizedFactors (Ideal.span {u}),
    P ∈ S ∧ (normalizedFactors (Ideal.span {u})).count P < 6}

def bound (S : Finset (Ideal O)) : ℕ := ((∏ P ∈ S, P)^5).absNorm

theorem row_ideal_dvd (S : Finset (Ideal O)) {u : O} (hu : u ∈ rows S) :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  change (Ideal.span {u} : Ideal O) ∣ (S.prod id)^5
  simpa only [Finset.prod_val] using hd

theorem row_norm_bound (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    {u : O} (hu : u ∈ rows S) : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

theorem rows_subset_normDisk (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    rows S ⊆ (TruncatedPrincipalPoisson.rowNormDisk (bound S) : Set O) := by
  intro u hu
  apply (TruncatedPrincipalPoisson.mem_rowNormDisk _ _).mpr
  refine ⟨?_, row_norm_bound S hS hu⟩
  apply Nat.pos_of_ne_zero
  simpa only [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] using hu.1

theorem rows_finite (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) : (rows S).Finite :=
  (TruncatedPrincipalPoisson.rowNormDisk (bound S)).finite_toSet.subset (rows_subset_normDisk S hS)

end HeckeExceptionalRows

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_ne_zero_of_principal (χ : Character) (hχ : χ.residue = 1) :
    (∑ a, coefficients χ a) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  rw [heq]
  apply mul_ne_zero
  · exact_mod_cast (Nat.card_pos (α := (coordinateQuotientHom χ).ker)).ne'
  · exact_mod_cast (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)).ne'

theorem dualScalar_ne_zero (N : ℕ) [NeZero N] : HeckeTheta.dualScalar N ≠ 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold HeckeTheta.dualScalar
  apply mul_ne_zero <;> apply Complex.ofReal_ne_zero.mpr
  · exact (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _).ne'
  · exact (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _).ne'

theorem principal_dual_constant_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    (HeckeTheta.pair (coefficients χ)).g₀ ≠ 0 := by
  rw [HeckeTheta.pair_g₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (dualScalar_ne_zero χ.period))
    (coefficients_sum_ne_zero_of_principal χ hχ)

def regularizedL (χ : Character) (s : ℂ) : ℂ :=
  HeckeTheta.regularizedLatticeL (coefficients χ) s / 6

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_at_one (χ : Character) :
    regularizedL χ 1 = (Real.pi : ℂ) * (HeckeTheta.pair (coefficients χ)).g₀ / 6 := by
  simp [regularizedL, HeckeTheta.regularizedLatticeL, HeckeTheta.regularizedCompleted]

theorem regularizedL_ne_zero_at_one (χ : Character) (hχ : χ.residue = 1) :
    regularizedL χ 1 ≠ 0 := by
  rw [regularizedL_at_one]
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (principal_dual_constant_ne_zero χ hχ)) (by norm_num)

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

def reciprocal (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then (s - 1) / regularizedL χ s else (LFunction χ s)⁻¹

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

theorem reciprocal_principal_one (χ : Character) (hχ : χ.residue = 1) :
    reciprocal χ 1 = 0 := by simp [reciprocal, hχ]

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end HeckeReciprocal

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
