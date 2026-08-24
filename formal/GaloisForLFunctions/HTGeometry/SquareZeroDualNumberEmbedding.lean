import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Unramified.Basic

/-!
# Square-zero directions are dual-number arcs

A nonzero square-zero element in a commutative algebra is not merely a nilpotent
point: it determines a faithful algebraic infinitesimal arc from the dual
numbers.  Conversely, every embedded dual-number algebra supplies such a
direction.  This file packages that equivalence without any finite-generation,
Noetherian, or reducedness hypothesis.
-/

namespace SquareZeroDualNumber

noncomputable section

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The linear direction spanned by an element of a `k`-algebra. -/
def direction (h : A) : k →ₗ[k] A where
  toFun c := c • h
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := smul_assoc _ _ _

/-- A square-zero element defines the infinitesimal arc `a + bε ↦ a + b h`. -/
def dualNumberMap (h : A) (hsq : h ^ 2 = 0) : DualNumber k →ₐ[k] A :=
  TrivSqZeroExt.liftEquivOfComm ⟨direction h, by
    intro x y
    change (x • h) * (y • h) = 0
    rw [smul_mul_smul, show h * h = 0 by simpa [pow_two] using hsq, smul_zero]⟩

@[simp]
theorem dualNumberMap_apply (h : A) (hsq : h ^ 2 = 0) (x : DualNumber k) :
    dualNumberMap h hsq x = algebraMap k A x.fst + x.snd • h := by
  rfl

/-- A nonzero square-zero direction gives a faithful dual-number arc. -/
theorem dualNumberMap_injective {h : A} (hne : h ≠ 0) (hsq : h ^ 2 = 0) :
    Function.Injective (dualNumberMap (k := k) (A := A) h hsq) := by
  letI : Nontrivial A := ⟨⟨h, 0, hne⟩⟩
  intro x y hxy
  apply sub_eq_zero.mp
  let z := x - y
  have hzmap : dualNumberMap h hsq z = 0 := by
    dsimp [z]
    rw [map_sub, hxy, sub_self]
  rw [dualNumberMap_apply] at hzmap
  have hbase : algebraMap k A z.fst = -(z.snd • h) :=
    eq_neg_of_add_eq_zero_left hzmap
  have hsquare := congrArg (fun q : A => q ^ 2) hbase
  have hbaseSq : algebraMap k A (z.fst ^ 2) = 0 := by
    rw [map_pow]
    calc
      algebraMap k A z.fst ^ 2 = (-(z.snd • h)) ^ 2 := hsquare
      _ = 0 := by
        rw [neg_sq, pow_two, smul_mul_smul,
          show h * h = 0 by simpa [pow_two] using hsq, smul_zero]
  have hzfstSq : z.fst ^ 2 = 0 :=
    (FaithfulSMul.algebraMap_injective k A) (by simpa using hbaseSq)
  have hzfst : z.fst = 0 :=
    (sq_eq_zero_iff).mp (by simpa [pow_two] using hzfstSq)
  have hzsnd : z.snd = 0 := by
    rw [hzfst, map_zero, zero_add] at hzmap
    exact (smul_eq_zero.mp hzmap).resolve_right hne
  apply TrivSqZeroExt.ext hzfst hzsnd

/-- The canonical dual-number arc is faithful exactly when its direction is nonzero. -/
theorem dualNumberMap_injective_iff {h : A} (hsq : h ^ 2 = 0) :
    Function.Injective (dualNumberMap (k := k) (A := A) h hsq) ↔ h ≠ 0 := by
  constructor
  · intro hinj hzero
    have heq : (TrivSqZeroExt.inr (1 : k) : DualNumber k) = 0 := by
      apply hinj
      calc
        dualNumberMap h hsq (TrivSqZeroExt.inr (1 : k)) = h := by
          rw [dualNumberMap_apply, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
            map_zero, zero_add, one_smul]
        _ = 0 := hzero
        _ = dualNumberMap h hsq 0 := (map_zero _).symm
    have hsnd := congrArg TrivSqZeroExt.snd heq
    change (1 : k) = 0 at hsnd
    exact one_ne_zero hsnd
  · intro hne
    exact dualNumberMap_injective hne hsq

/-- An algebra contains a nonzero square-zero element exactly when it contains
an embedded copy of the dual numbers. -/
theorem exists_nonzero_squareZero_iff_exists_dualNumberEmbedding :
    (∃ h : A, h ≠ 0 ∧ h ^ 2 = 0) ↔
      ∃ f : DualNumber k →ₐ[k] A, Function.Injective f := by
  constructor
  · rintro ⟨h, hne, hsq⟩
    exact ⟨dualNumberMap h hsq, dualNumberMap_injective hne hsq⟩
  · rintro ⟨f, hinj⟩
    let epsilon : DualNumber k := TrivSqZeroExt.inr 1
    refine ⟨f epsilon, ?_, ?_⟩
    · intro hzero
      have heq : epsilon = 0 := by
        apply hinj
        rw [hzero, map_zero]
      have hsnd := congrArg TrivSqZeroExt.snd heq
      dsimp only [epsilon] at hsnd
      change (1 : k) = 0 at hsnd
      exact one_ne_zero hsnd
    · calc
        f epsilon ^ 2 = f (epsilon ^ 2) := (map_pow f epsilon 2).symm
        _ = f 0 := by
          congr 1
          simp [epsilon, pow_two]
        _ = 0 := map_zero f

/-- Euler derivation of the dual numbers: it fixes the infinitesimal direction
and kills the scalar direction. -/
def eulerDerivation : Derivation k (DualNumber k) (DualNumber k) where
  toLinearMap :=
    { toFun := fun x => TrivSqZeroExt.inr x.snd
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro c x
        ext <;> simp }
  map_one_eq_zero' := by
    ext <;> simp
  leibniz' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.snd_mul, mul_add, mul_comm]

@[simp]
theorem eulerDerivation_epsilon :
    eulerDerivation (k := k) (TrivSqZeroExt.inr (1 : k)) =
      TrivSqZeroExt.inr (1 : k) := by
  rfl

/-- Dual numbers over a field are formally ramified.  The obstruction is the
nonzero Euler derivation, so this statement does not rely on a reducedness
criterion or finite-presentation machinery. -/
theorem dualNumber_not_formallyUnramified :
    ¬ Algebra.FormallyUnramified k (DualNumber k) := by
  intro h
  letI : Algebra.FormallyUnramified k (DualNumber k) := h
  let D := eulerDerivation (k := k)
  have hlift : D.liftKaehlerDifferential = 0 := Subsingleton.elim _ _
  have hD : D = 0 := by
    rw [← D.liftKaehlerDifferential_comp, hlift]
    rfl
  have heps := DFunLike.congr_fun hD (TrivSqZeroExt.inr (1 : k))
  change (TrivSqZeroExt.inr (1 : k) : DualNumber k) = 0 at heps
  have hsnd := congrArg TrivSqZeroExt.snd heps
  change (1 : k) = 0 at hsnd
  exact one_ne_zero hsnd

/-- Any algebra equivalent to the dual numbers is formally ramified. -/
theorem not_formallyUnramified_of_equiv (e : DualNumber k ≃ₐ[k] A) :
    ¬ Algebra.FormallyUnramified k A := by
  intro h
  letI : Algebra.FormallyUnramified k A := h
  exact dualNumber_not_formallyUnramified (k := k)
    (Algebra.FormallyUnramified.of_equiv e.symm)

/-- The canonical image algebra of an embedded dual-number arc is formally ramified. -/
theorem range_not_formallyUnramified
    (f : DualNumber k →ₐ[k] A) (hinj : Function.Injective f) :
    ¬ Algebra.FormallyUnramified k f.range :=
  not_formallyUnramified_of_equiv (AlgEquiv.ofInjective f hinj)

end

end SquareZeroDualNumber
