import GaloisForLFunctions.HTGeometry.TwoSiteLabelProduct

/-!
# Anticommutation of Pauli labels

Swapping the two arguments of the phase of a label product multiplies it by `-1` at every site
where the two letters are distinct and nonzero.  A pair of labels differing that way at exactly one
site therefore anticommutes.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section SingleSite

theorem optPhase_swap_of_ne {a b : Fin 3} (hab : a ≠ b) :
    optPhase (some b) (some a) = -optPhase (some a) (some b) := by
  rcases fin3_eq_cases a with rfl | rfl | rfl <;> rcases fin3_eq_cases b with rfl | rfl | rfl <;>
    simp_all [optPhase]

theorem optPhase_swap_of_none_left (q : Option (Fin 3)) :
    optPhase q none = optPhase none q := by
  rw [optPhase_none_right, optPhase_none_left]

theorem optPhase_swap_of_eq (a : Fin 3) :
    optPhase (some a) (some a) = optPhase (some a) (some a) := rfl

/-- Two single-qubit letters commute unless they are distinct and both nonzero. -/
theorem optPhase_swap_eq_of_not_anticomm {p q : Option (Fin 3)}
    (h : p = none ∨ q = none ∨ p = q) : optPhase q p = optPhase p q := by
  rcases h with rfl | rfl | rfl
  · rw [optPhase_none_right, optPhase_none_left]
  · rw [optPhase_none_right, optPhase_none_left]
  · rfl

theorem optPhase_ne_zero (p q : Option (Fin 3)) : optPhase p q ≠ 0 := by
  cases p with
  | none => simp [optPhase]
  | some a =>
      cases q with
      | none => simp [optPhase]
      | some b =>
          rcases fin3_eq_cases a with rfl | rfl | rfl <;>
            rcases fin3_eq_cases b with rfl | rfl | rfl <;>
            simp [optPhase, Complex.ext_iff]

end SingleSite

section Strings

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem optPhaseProd_ne_zero (P Q : σ → Option (Fin 3)) : optPhaseProd P Q ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun s _ => optPhase_ne_zero (P s) (Q s)

/-- **Two labels differing at exactly one site anticommute.** -/
theorem optPhaseProd_swap_of_unique_site {P Q : σ → Option (Fin 3)} (s : σ)
    (hs : ∃ a b : Fin 3, P s = some a ∧ Q s = some b ∧ a ≠ b)
    (hother : ∀ t : σ, t ≠ s → (P t = none ∨ Q t = none ∨ P t = Q t)) :
    optPhaseProd Q P = -optPhaseProd P Q := by
  classical
  obtain ⟨a, b, hPa, hQb, hab⟩ := hs
  have hprod : (∏ t ∈ (Finset.univ : Finset σ) \ {s}, optPhase (Q t) (P t)) =
      ∏ t ∈ (Finset.univ : Finset σ) \ {s}, optPhase (P t) (Q t) := by
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at ht
    exact optPhase_swap_eq_of_not_anticomm (hother t ht.2)
  rw [optPhaseProd, optPhaseProd,
    Finset.prod_eq_mul_prod_sdiff_singleton s (fun t => optPhase (Q t) (P t))
      (fun hc => absurd (Finset.mem_univ s) hc),
    Finset.prod_eq_mul_prod_sdiff_singleton s (fun t => optPhase (P t) (Q t))
      (fun hc => absurd (Finset.mem_univ s) hc), hPa, hQb, optPhase_swap_of_ne hab, hprod,
    neg_mul]

theorem optPhaseProd_ne_of_unique_site {P Q : σ → Option (Fin 3)} (s : σ)
    (hs : ∃ a b : Fin 3, P s = some a ∧ Q s = some b ∧ a ≠ b)
    (hother : ∀ t : σ, t ≠ s → (P t = none ∨ Q t = none ∨ P t = Q t)) :
    optPhaseProd P Q ≠ optPhaseProd Q P := by
  rw [optPhaseProd_swap_of_unique_site s hs hother]
  intro hc
  have hzero : (2 : ℂ) * optPhaseProd P Q = 0 := by linear_combination hc
  exact optPhaseProd_ne_zero P Q ((mul_eq_zero.mp hzero).resolve_left two_ne_zero)

end Strings

end GaloisForLFunctions.HTGeometry
