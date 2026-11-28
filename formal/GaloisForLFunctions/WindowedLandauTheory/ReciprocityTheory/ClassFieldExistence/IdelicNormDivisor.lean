import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicProductNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleDivisor
import GaloisForLFunctions.RHTower.Artin.TheArtinMapOverAnIntermediateFieldIsTheArtinMapOfTheNorm

/-! The divisor of an idelic norm is the ideal norm of its divisor. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions WithZero
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def countIdealHom {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* Multiplicative ℤ where
  toFun I := Multiplicative.ofAdd (count F v I.val)
  map_one' := congrArg Multiplicative.ofAdd (count_one F v)
  map_mul' x y := congrArg Multiplicative.ofAdd (count_mul F v x.ne_zero y.ne_zero)

open Classical in
private theorem count_idealNormHom_prime (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) :
    count K v ((idealNormHom K L (idealUnit w.ne_bot)).val) =
      ∑ u : finitePlacesAbove L v, (u.val.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        count L u.val ((idealUnit w.ne_bot).val) := by
  rw [idealNormHom_idealUnit_prime, Units.val_pow_eq_pow_val, count_pow,
    count_primeIdealUnit]
  by_cases h : w.under (𝓞 K) = v
  · let u : finitePlacesAbove L v :=
      ⟨w, (mem_finitePlacesAbove L v w).mpr ((finitePlace_under_eq_iff w v).mp h)⟩
    rw [Fintype.sum_eq_single u]
    · simp [u, h, count_primeIdealUnit]
    · intro z hz
      rw [count_primeIdealUnit, if_neg (fun hz' => hz (Subtype.ext hz')), mul_zero]
  · rw [if_neg (Ne.symm h), mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro u _
    have hu : u.val ≠ w := by
      intro e
      apply h
      rw [← e]
      exact (finitePlace_under_eq_iff u.val v).mpr inferInstance
    rw [count_primeIdealUnit, if_neg hu, mul_zero]

theorem count_idealNormHom (v : HeightOneSpectrum (𝓞 K)) (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    count K v (idealNormHom K L I).val =
      ∑ w : finitePlacesAbove L v, (w.val.asIdeal.inertiaDeg (𝓞 K) : ℤ) * count L w.val I.val := by
  let f := (countIdealHom v).comp (idealNormHom K L)
  let g : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* Multiplicative ℤ :=
    { toFun J := Multiplicative.ofAdd (∑ w : finitePlacesAbove L v,
        (w.val.asIdeal.inertiaDeg (𝓞 K) : ℤ) * count L w.val J.val)
      map_one' := congrArg Multiplicative.ofAdd (by simp [count_one])
      map_mul' := fun x y => congrArg Multiplicative.ofAdd (by
        simp only [Units.val_mul, count_mul L _ x.ne_zero y.ne_zero, mul_add, Finset.sum_add_distrib, toAdd_ofAdd]) }
  have h : f = g := by
    rw [eq_primeValuesHom f, eq_primeValuesHom g]
    congr 1
    funext w
    exact congrArg Multiplicative.ofAdd (count_idealNormHom_prime v w)
  exact congrArg (fun j : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* Multiplicative ℤ =>
    Multiplicative.toAdd (j I)) h

private theorem log_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℤᵐ⁰)
    (h : ∀ i ∈ s, f i ≠ 0) : log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs j (hj : j ∈ s) := h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      log_mul (h _ (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

variable [IsGalois K L]

theorem ord_ideleNorm (v : HeightOneSpectrum (𝓞 K)) (y : IdeleGroup L) :
    IdeleGroup.ord v (ideleNorm y) =
      ∑ w : finitePlacesAbove L v,
        (w.val.asIdeal.inertiaDeg (𝓞 K) : ℤ) * IdeleGroup.ord w.val y := by
  rw [IdeleGroup.ord, ← IdeleGroup.coe_finiteProj, finiteProj_ideleNorm, coe_finiteLocalNorm,
    map_prod, log_finset_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [valued_finiteCompletion_norm v w.val, log_pow, nsmul_eq_mul, neg_mul_eq_mul_neg,
      IdeleGroup.ord, IdeleGroup.coe_finiteProj]
  · intro w _
    exact (Valuation.ne_zero_iff _).mpr
      (Algebra.norm_ne_zero_iff.mpr (IdeleGroup.finiteProj w.val y).ne_zero)

theorem toFractionalIdeal_ideleNorm (y : IdeleGroup L) :
    IdeleGroup.toFractionalIdeal (ideleNorm (K := K) y) =
      idealNormHom K L (IdeleGroup.toFractionalIdeal y) := by
  refine (IdeleGroup.toFractionalIdeal_eq_iff).mpr fun v => ?_
  rw [ord_ideleNorm, count_idealNormHom]
  simp only [IdeleGroup.count_toFractionalIdeal]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.toFractionalIdeal_ideleNorm
