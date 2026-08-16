import GaloisForLFunctions.HTGeometry.PauliLabelSupport

/-!
# One-site and two-site Pauli labels

A one-site label is nontrivial at a single site, a two-site label at two distinct sites.  The
product of two two-site labels sharing exactly one site is supported on three sites, its phase is
the single-site phase at the shared site, and summing the resulting phase differences against two
coefficient vectors reproduces their cross product.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem optPhase_none_left (q : Option (Fin 3)) : optPhase none q = 1 := rfl

theorem fin3_eq_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section Labels

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The Pauli label nontrivial at one site. -/
def siteLabel (v : σ) (a : Fin 3) : σ → Option (Fin 3) :=
  fun s => if s = v then some a else none

/-- The Pauli label nontrivial at two sites. -/
def pairLabel (v w : σ) (a b : Fin 3) : σ → Option (Fin 3) :=
  fun s => if s = v then some a else if s = w then some b else none

theorem siteLabel_apply (v : σ) (a : Fin 3) (s : σ) :
    siteLabel v a s = if s = v then some a else none := rfl

theorem pairLabel_apply (v w : σ) (a b : Fin 3) (s : σ) :
    pairLabel v w a b s = if s = v then some a else if s = w then some b else none := rfl

theorem labelSupport_siteLabel (v : σ) (a : Fin 3) : labelSupport (siteLabel v a) = {v} := by
  ext s
  rw [mem_labelSupport, Finset.mem_singleton, siteLabel_apply]
  by_cases h : s = v
  · simp [h]
  · simp [h]

theorem labelSupport_pairLabel {v w : σ} (hvw : v ≠ w) (a b : Fin 3) :
    labelSupport (pairLabel v w a b) = {v, w} := by
  ext s
  rw [mem_labelSupport, Finset.mem_insert, Finset.mem_singleton, pairLabel_apply]
  by_cases hv : s = v
  · simp [hv]
  · by_cases hw : s = w
    · subst hw
      simp [hv]
    · simp [hv, hw]

theorem card_labelSupport_siteLabel (v : σ) (a : Fin 3) :
    (labelSupport (siteLabel v a)).card = 1 := by
  rw [labelSupport_siteLabel, Finset.card_singleton]

theorem card_labelSupport_pairLabel {v w : σ} (hvw : v ≠ w) (a b : Fin 3) :
    (labelSupport (pairLabel v w a b)).card = 2 := by
  rw [labelSupport_pairLabel hvw, Finset.card_insert_of_notMem (by simpa using hvw),
    Finset.card_singleton]

/-- The phase of the product of two two-site labels sharing their middle site. -/
theorem optPhaseProd_pairLabel {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a b d e : Fin 3) :
    optPhaseProd (pairLabel v w a b) (pairLabel w x d e) = optPhase (some b) (some d) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single w]
  · simp [pairLabel_apply, Ne.symm hvw]
  · intro s _ hs
    by_cases hv : s = v
    · subst hv
      simp [pairLabel_apply, hvw, hvx, optPhase_none_right]
    · by_cases hx : s = x
      · subst hx
        simp [pairLabel_apply, hv, hs, optPhase_none_left]
      · simp [pairLabel_apply, hv, hs, hx, optPhase_none_left]
  · intro hcon
    exact absurd (Finset.mem_univ w) hcon

/-- The label product of two two-site labels sharing their middle site. -/
theorem optMulLabel_pairLabel {v w x : σ} (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x)
    (a b d e : Fin 3) (s : σ) :
    optMulLabel (pairLabel v w a b) (pairLabel w x d e) s =
      if s = v then some a else if s = w then optMul (some b) (some d)
        else if s = x then some e else none := by
  show optMul (pairLabel v w a b s) (pairLabel w x d e s) = _
  by_cases hv : s = v
  · subst hv
    simp [pairLabel_apply, hvw, hvx, optMul_none_right]
  · by_cases hw : s = w
    · subst hw
      simp [pairLabel_apply, hv]
    · by_cases hx : s = x
      · subst hx
        simp [pairLabel_apply, hv, hw]
        rfl
      · simp [pairLabel_apply, hv, hw, hx]
        rfl

end Labels

section StructureConstants

/-- The commutator structure constant of two single-site Pauli labels. -/
def pauliComm (b d : Fin 3) : ℂ := optPhase (some b) (some d) - optPhase (some d) (some b)

/-- **The Pauli structure constants reproduce the cross product.** -/
theorem sum_pauliComm_eq_cross (u v : Fin 3 → ℝ) (f : Fin 3) :
    (∑ b : Fin 3, ∑ d : Fin 3, ((u b : ℂ) * (v d : ℂ)) * (pauliComm b d *
      (if some f = optMul (some b) (some d) then 1 else 0)))
      = 2 * Complex.I * ((crossProduct u v f : ℝ) : ℂ) := by
  rcases fin3_eq_cases f with rfl | rfl | rfl <;>
    simp +decide [Fin.sum_univ_three, pauliComm, optPhase, optMul, crossProduct] <;>
    ring

end StructureConstants

end GaloisForLFunctions.HTGeometry
