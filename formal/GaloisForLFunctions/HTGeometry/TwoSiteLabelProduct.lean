import GaloisForLFunctions.HTGeometry.ChainThreeSiteRelation

/-!
# Two-site Pauli strings as products of a two-site and a one-site label

Multiplying a two-site label on `v, w` by a one-site label at `v` or at `w` again gives a label
supported in `{v, w}`; the phase is the single-site phase at the shared site, and the product is
the original label with the shared letter multiplied.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

section Left

variable {v w : σ}

theorem optPhaseProd_pairLabel_siteLabel_left (a b c : Fin 3) :
    optPhaseProd (pairLabel v w a b) (siteLabel v c) = optPhase (some a) (some c) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single v]
  · simp [pairLabel_apply, siteLabel_apply]
  · intro s _ hs
    simp [pairLabel_apply, siteLabel_apply, hs, optPhase_none_right]
  · intro hcon
    exact absurd (Finset.mem_univ v) hcon

theorem optPhaseProd_siteLabel_pairLabel_left (a b c : Fin 3) :
    optPhaseProd (siteLabel v c) (pairLabel v w a b) = optPhase (some c) (some a) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single v]
  · simp [pairLabel_apply, siteLabel_apply]
  · intro s _ hs
    simp [pairLabel_apply, siteLabel_apply, hs, optPhase_none_left]
  · intro hcon
    exact absurd (Finset.mem_univ v) hcon

theorem optMulLabel_pairLabel_siteLabel_left (hvw : v ≠ w) (a b c : Fin 3) (s : σ) :
    optMulLabel (pairLabel v w a b) (siteLabel v c) s =
      if s = v then optMul (some a) (some c) else if s = w then some b else none := by
  show optMul (pairLabel v w a b s) (siteLabel v c s) = _
  by_cases hv : s = v
  · subst hv
    simp [pairLabel_apply, siteLabel_apply]
  · by_cases hw : s = w
    · subst hw
      simp [pairLabel_apply, siteLabel_apply, hv, optMul_none_right]
    · simp [pairLabel_apply, siteLabel_apply, hv, hw, optMul]

/-- **A two-site string as a two-site label times a one-site label at the left site.** -/
theorem pairLabel_eq_optMulLabel_left_iff (hvw : v ≠ w) (f q a b c : Fin 3) :
    pairLabel v w f q = optMulLabel (pairLabel v w a b) (siteLabel v c) ↔
      (b = q ∧ some f = optMul (some a) (some c)) := by
  classical
  have hLv : pairLabel v w f q v = some f := by rw [pairLabel_apply, if_pos rfl]
  have hLw : pairLabel v w f q w = some q := by
    rw [pairLabel_apply, if_neg (Ne.symm hvw), if_pos rfl]
  have hPv : optMulLabel (pairLabel v w a b) (siteLabel v c) v = optMul (some a) (some c) := by
    rw [optMulLabel_pairLabel_siteLabel_left hvw, if_pos rfl]
  have hPw : optMulLabel (pairLabel v w a b) (siteLabel v c) w = some b := by
    rw [optMulLabel_pairLabel_siteLabel_left hvw, if_neg (Ne.symm hvw), if_pos rfl]
  constructor
  · intro hEq
    have e1 : (some f : Option (Fin 3)) = optMul (some a) (some c) := by
      rw [← hLv, ← hPv, hEq]
    have e2 : (some q : Option (Fin 3)) = some b := by rw [← hLw, ← hPw, hEq]
    exact ⟨(Option.some_injective _ e2).symm, e1⟩
  · rintro ⟨rfl, hmid⟩
    funext s
    rw [optMulLabel_pairLabel_siteLabel_left hvw, ← hmid, pairLabel_apply]

end Left

section Right

variable {v w : σ}

theorem optPhaseProd_pairLabel_siteLabel_right (hvw : v ≠ w) (a b c : Fin 3) :
    optPhaseProd (pairLabel v w a b) (siteLabel w c) = optPhase (some b) (some c) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single w]
  · simp [pairLabel_apply, siteLabel_apply, Ne.symm hvw]
  · intro s _ hs
    by_cases hv : s = v
    · subst hv
      simp [pairLabel_apply, siteLabel_apply, hs, optPhase_none_right]
    · simp [pairLabel_apply, siteLabel_apply, hv, hs, optPhase_none_left]
  · intro hcon
    exact absurd (Finset.mem_univ w) hcon

theorem optPhaseProd_siteLabel_pairLabel_right (hvw : v ≠ w) (a b c : Fin 3) :
    optPhaseProd (siteLabel w c) (pairLabel v w a b) = optPhase (some c) (some b) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single w]
  · simp [pairLabel_apply, siteLabel_apply, Ne.symm hvw]
  · intro s _ hs
    by_cases hv : s = v
    · subst hv
      simp [pairLabel_apply, siteLabel_apply, hs, optPhase_none_left]
    · simp [pairLabel_apply, siteLabel_apply, hv, hs, optPhase_none_left]
  · intro hcon
    exact absurd (Finset.mem_univ w) hcon

theorem optMulLabel_pairLabel_siteLabel_right (hvw : v ≠ w) (a b c : Fin 3) (s : σ) :
    optMulLabel (pairLabel v w a b) (siteLabel w c) s =
      if s = v then some a else if s = w then optMul (some b) (some c) else none := by
  show optMul (pairLabel v w a b s) (siteLabel w c s) = _
  by_cases hv : s = v
  · subst hv
    simp [pairLabel_apply, siteLabel_apply, hvw, optMul_none_right]
  · by_cases hw : s = w
    · subst hw
      simp [pairLabel_apply, siteLabel_apply, hv]
    · simp [pairLabel_apply, siteLabel_apply, hv, hw, optMul]

/-- **A two-site string as a two-site label times a one-site label at the right site.** -/
theorem pairLabel_eq_optMulLabel_right_iff (hvw : v ≠ w) (f q a b c : Fin 3) :
    pairLabel v w f q = optMulLabel (pairLabel v w a b) (siteLabel w c) ↔
      (a = f ∧ some q = optMul (some b) (some c)) := by
  classical
  have hLv : pairLabel v w f q v = some f := by rw [pairLabel_apply, if_pos rfl]
  have hLw : pairLabel v w f q w = some q := by
    rw [pairLabel_apply, if_neg (Ne.symm hvw), if_pos rfl]
  have hPv : optMulLabel (pairLabel v w a b) (siteLabel w c) v = some a := by
    rw [optMulLabel_pairLabel_siteLabel_right hvw, if_pos rfl]
  have hPw : optMulLabel (pairLabel v w a b) (siteLabel w c) w = optMul (some b) (some c) := by
    rw [optMulLabel_pairLabel_siteLabel_right hvw, if_neg (Ne.symm hvw), if_pos rfl]
  constructor
  · intro hEq
    have e1 : (some f : Option (Fin 3)) = some a := by rw [← hLv, ← hPv, hEq]
    have e2 : (some q : Option (Fin 3)) = optMul (some b) (some c) := by
      rw [← hLw, ← hPw, hEq]
    exact ⟨(Option.some_injective _ e1).symm, e2⟩
  · rintro ⟨rfl, hmid⟩
    funext s
    rw [optMulLabel_pairLabel_siteLabel_right hvw, ← hmid, pairLabel_apply]

end Right

end GaloisForLFunctions.HTGeometry
