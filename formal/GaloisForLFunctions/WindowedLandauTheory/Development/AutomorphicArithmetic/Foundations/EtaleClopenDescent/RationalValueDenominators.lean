import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StalkRationalValues

/-! The fraction test with a nonvanishing denominator is equivalent to
regularity and the prescribed value in the local ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- A rational function has the given value after clearing a denominator
that has nonzero value. -/
def Val (B : Subalgebra K L) (e : B →ₐ[K] K) (v : L) (c : K) : Prop :=
  ∃ (b : L) (hb : b ∈ B) (hm : b * v ∈ B),
    e ⟨b, hb⟩ ≠ 0 ∧ e ⟨b * v, hm⟩ = e ⟨b, hb⟩ * c

variable {Y : Scheme.{0}} [IsIntegral Y] {t : Y ⟶ Spec (CommRingCat.of K)}
  [Algebra K Y.functionField] {W : Y.Opens} {B : Subalgebra K Y.functionField}

theorem val_iff_exists_local (hW : IsAffineOpen W) (y : Y.BaseFieldPointOver K t)
    (hy : y.hom default ∈ W) (i : SectionRing t W ≃ₐ[K] B) (e : B →ₐ[K] K)
    (hg : ∀ b, (i b : Y.functionField) =
      (Y.presheaf.germ W (genericPoint Y) ((genericPoint_specializes (y.hom default)).mem_open
        W.isOpen hy)).hom b)
    (he : ∀ b, e (i b) = affinePointEval y hy b) (v : Y.functionField) (c : K) :
    Val B e v c ↔ ∃ z : Y.presheaf.stalk (y.hom default),
      (stalkToFunctionField (y.hom default)).hom z = v ∧ (localPointEval y).hom z = c := by
  let P := y.hom default
  let g := (Y.presheaf.germ W P hy).hom
  let j := (stalkToFunctionField P).hom
  let l := (localPointEval y).hom
  have hj (a : Γ(Y, W)) : j (g a) = (i a : Y.functionField) := by
    rw [hg]
    exact ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hy
      (genericPoint_specializes P)) a
  have hl (a : Γ(Y, W)) : l (g a) = e (i a) :=
    (localPointEval_germ y hy a).trans (he a).symm
  constructor
  · rintro ⟨b, hb, hm, hne, hval⟩
    let a := i.symm ⟨b, hb⟩
    let m := i.symm ⟨b * v, hm⟩
    have ha : i a = ⟨b, hb⟩ := i.apply_symm_apply _
    have hm' : i m = ⟨b * v, hm⟩ := i.apply_symm_apply _
    have hu : IsUnit (g a) := by
      apply (localPointEval_isUnit_iff y _).mp
      apply isUnit_iff_ne_zero.mpr
      change l (g a) ≠ 0
      rwa [hl, ha]
    let z := (↑hu.unit⁻¹ : Y.presheaf.stalk P) * g m
    have hz : g a * z = g m := by
      change g a * (↑hu.unit⁻¹ * g m) = g m
      simpa only [hu.unit_spec] using Units.mul_inv_cancel_left hu.unit (g m)
    have hb0 : b ≠ 0 := by
      intro h
      apply hne
      rw [show (⟨b, hb⟩ : B) = 0 from Subtype.ext h, map_zero]
    refine ⟨z, mul_left_cancel₀ hb0 ?_, mul_left_cancel₀ hne ?_⟩
    · simpa only [map_mul, hj, ha, hm'] using congrArg j hz
    · simpa only [map_mul, hl, ha, hm', hval] using congrArg l hz
  · rintro ⟨z, hz, hc⟩
    let p : W := ⟨P, hy⟩
    let S := (hW.primeIdealOf p).asIdeal.primeCompl
    letI : Algebra Γ(Y, W) (Y.presheaf.stalk P) := Y.presheaf.algebra_section_stalk p
    letI : IsLocalization S (Y.presheaf.stalk P) := hW.isLocalization_stalk p
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj S z
    change z * g b = g a at h
    have hmul : (i b.val : Y.functionField) * v = i a := by
      have h' := congrArg j h
      rw [map_mul, hj, hj, show j z = v from hz, mul_comm v] at h'
      exact h'
    have hu : IsUnit (g b) := IsLocalization.map_units _ b
    refine ⟨i b.val, (i b.val).2, hmul.symm ▸ (i a).2, ?_, ?_⟩
    · change e (i b.val) ≠ 0
      rw [← hl]
      exact isUnit_iff_ne_zero.mp (hu.map l)
    · change e ⟨_, _⟩ = e (i b.val) * c
      rw [show (⟨_, _⟩ : B) = i a from Subtype.ext hmul, ← hl, ← hl]
      have h' := congrArg l h
      rw [map_mul, show l z = c from hc, mul_comm c] at h'
      exact h'.symm

end GlobalTheory.WH
