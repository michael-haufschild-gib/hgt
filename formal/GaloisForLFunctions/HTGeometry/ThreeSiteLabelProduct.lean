import GaloisForLFunctions.HTGeometry.ChainShellCommutator

/-!
# Three-site Pauli strings as products of two-site labels

A Pauli string supported on three sites `v, w, x` is the product of a two-site label on `v, w` and
one on `w, x`, in either order, exactly when the outer letters agree and the two middle letters
multiply to the middle letter of the string.  The phase of such a product is the single-site phase
at the shared site.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The Pauli label nontrivial at three sites. -/
def tripleLabel (v w x : σ) (a f e : Fin 3) : σ → Option (Fin 3) :=
  fun s => if s = v then some a else if s = w then some f else if s = x then some e else none

theorem tripleLabel_apply (v w x : σ) (a f e : Fin 3) (s : σ) :
    tripleLabel v w x a f e s =
      if s = v then some a else if s = w then some f else if s = x then some e else none := rfl

theorem labelSupport_tripleLabel {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a f e : Fin 3) : labelSupport (tripleLabel v w x a f e) = {v, w, x} := by
  classical
  ext s
  rw [mem_labelSupport, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton,
    tripleLabel_apply]
  by_cases hv : s = v
  · simp [hv]
  · by_cases hw : s = w
    · subst hw
      simp [hv]
    · by_cases hx : s = x
      · subst hx
        simp [hv, hw]
      · simp [hv, hw, hx]

theorem card_labelSupport_tripleLabel {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a f e : Fin 3) : (labelSupport (tripleLabel v w x a f e)).card = 3 := by
  classical
  rw [labelSupport_tripleLabel hvw hwx hvx, Finset.card_insert_of_notMem (by simp [hvw, hvx]),
    Finset.card_insert_of_notMem (by simp [hwx]), Finset.card_singleton]

theorem tripleLabel_left {v w x : σ} (a f e : Fin 3) : tripleLabel v w x a f e v = some a := by
  rw [tripleLabel_apply, if_pos rfl]

theorem tripleLabel_mid {v w x : σ} (hvw : v ≠ w) (a f e : Fin 3) :
    tripleLabel v w x a f e w = some f := by
  rw [tripleLabel_apply, if_neg (Ne.symm hvw), if_pos rfl]

theorem tripleLabel_right {v w x : σ} (hwx : w ≠ x) (hvx : v ≠ x) (a f e : Fin 3) :
    tripleLabel v w x a f e x = some e := by
  rw [tripleLabel_apply, if_neg (Ne.symm hvx), if_neg (Ne.symm hwx), if_pos rfl]

/-- The phase of a two-site product taken in the reversed order. -/
theorem optPhaseProd_pairLabel_rev {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a b d e : Fin 3) :
    optPhaseProd (pairLabel w x d e) (pairLabel v w a b) = optPhase (some d) (some b) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single w]
  · simp [pairLabel_apply, Ne.symm hvw]
  · intro s _ hs
    by_cases hv : s = v
    · subst hv
      simp [pairLabel_apply, hvw, hvx, optPhase_none_left]
    · by_cases hx : s = x
      · subst hx
        simp [pairLabel_apply, hs, Ne.symm hvx, optPhase_none_right]
      · simp [pairLabel_apply, hs, hx, optPhase_none_left]
  · intro hcon
    exact absurd (Finset.mem_univ w) hcon

/-- **A three-site string is a product of two consecutive two-site labels.** -/
theorem tripleLabel_eq_optMulLabel_iff {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a f e a' b d e' : Fin 3) :
    tripleLabel v w x a f e = optMulLabel (pairLabel v w a' b) (pairLabel w x d e') ↔
      (a' = a ∧ e' = e ∧ some f = optMul (some b) (some d)) := by
  classical
  have hPv : optMulLabel (pairLabel v w a' b) (pairLabel w x d e') v = some a' := by
    rw [optMulLabel_pairLabel hvw hwx hvx, if_pos rfl]
  have hPw : optMulLabel (pairLabel v w a' b) (pairLabel w x d e') w =
      optMul (some b) (some d) := by
    rw [optMulLabel_pairLabel hvw hwx hvx, if_neg (Ne.symm hvw), if_pos rfl]
  have hPx : optMulLabel (pairLabel v w a' b) (pairLabel w x d e') x = some e' := by
    rw [optMulLabel_pairLabel hvw hwx hvx, if_neg (Ne.symm hvx), if_neg (Ne.symm hwx), if_pos rfl]
  constructor
  · intro hEq
    have e1 : (some a : Option (Fin 3)) = some a' := by
      rw [← tripleLabel_left (v := v) (w := w) (x := x) a f e, ← hPv, hEq]
    have e2 : (some e : Option (Fin 3)) = some e' := by
      rw [← tripleLabel_right hwx hvx a f e, ← hPx, hEq]
    have e3 : (some f : Option (Fin 3)) = optMul (some b) (some d) := by
      rw [← tripleLabel_mid hvw a f e, ← hPw, hEq]
    exact ⟨(Option.some_injective _ e1).symm, (Option.some_injective _ e2).symm, e3⟩
  · rintro ⟨rfl, rfl, hmid⟩
    funext s
    rw [optMulLabel_pairLabel hvw hwx hvx, ← hmid, tripleLabel_apply]

/-- The same product taken in the reversed order. -/
theorem tripleLabel_eq_optMulLabel_rev_iff {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a f e a' b d e' : Fin 3) :
    tripleLabel v w x a f e = optMulLabel (pairLabel w x d e') (pairLabel v w a' b) ↔
      (a' = a ∧ e' = e ∧ some f = optMul (some b) (some d)) := by
  classical
  have hval : ∀ s : σ, optMulLabel (pairLabel w x d e') (pairLabel v w a' b) s =
      if s = v then some a' else if s = w then optMul (some d) (some b)
        else if s = x then some e' else none := by
    intro s
    show optMul (pairLabel w x d e' s) (pairLabel v w a' b s) = _
    by_cases hv : s = v
    · subst hv
      simp [pairLabel_apply, hvw, hvx, optMul]
    · by_cases hw : s = w
      · subst hw
        simp [pairLabel_apply, hv, optMul]
      · by_cases hx : s = x
        · subst hx
          simp [pairLabel_apply, hv, hw, optMul]
        · simp [pairLabel_apply, hv, hw, hx, optMul]
  have hQv : optMulLabel (pairLabel w x d e') (pairLabel v w a' b) v = some a' := by
    rw [hval, if_pos rfl]
  have hQw : optMulLabel (pairLabel w x d e') (pairLabel v w a' b) w =
      optMul (some d) (some b) := by
    rw [hval, if_neg (Ne.symm hvw), if_pos rfl]
  have hQx : optMulLabel (pairLabel w x d e') (pairLabel v w a' b) x = some e' := by
    rw [hval, if_neg (Ne.symm hvx), if_neg (Ne.symm hwx), if_pos rfl]
  constructor
  · intro hEq
    have e1 : (some a : Option (Fin 3)) = some a' := by
      rw [← tripleLabel_left (v := v) (w := w) (x := x) a f e, ← hQv, hEq]
    have e2 : (some e : Option (Fin 3)) = some e' := by
      rw [← tripleLabel_right hwx hvx a f e, ← hQx, hEq]
    have e3 : (some f : Option (Fin 3)) = optMul (some d) (some b) := by
      rw [← tripleLabel_mid hvw a f e, ← hQw, hEq]
    refine ⟨(Option.some_injective _ e1).symm, (Option.some_injective _ e2).symm, ?_⟩
    rw [e3, optMul_comm]
  · rintro ⟨rfl, rfl, hmid⟩
    funext s
    rw [hval, optMul_comm (some d) (some b), ← hmid, tripleLabel_apply]

end GaloisForLFunctions.HTGeometry
