/-
# Circuit dictionary counting and the eigenbasis coordinate change

Two small bridges the static-local complexity laws consume.  First, an orthonormal eigenbasis turns
every pairing of physical states into the pairing of their eigencoordinates, which is what puts a
circuit target into the replica-moment framework.  Second, a padded gate alphabet of `M` choices
gives exactly `M^s` words of length `s`, and the card's depth schedule `(s+1)⌈log₂M⌉ ≤ r/4` is
precisely the dictionary condition `(s+1)log M ≤ (r/2)log 2` of the counting bound.

Main results:
* `parseval_finiteComplexInner` — **the eigenbasis coordinate change**.
* `card_wordIndex` — the padded dictionary has `M^s` members.
* `circuitCount_log_le` — **`(14)`**: the depth schedule implies the counting condition.
-/
import GaloisForLFunctions.HTGeometry.EvolvedStateBundlePairing

open Matrix Complex ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Parseval in an orthonormal eigenbasis.**  The physical pairing is the pairing of the
eigencoordinates. -/
theorem parseval_finiteComplexInner {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (u v : α → ℂ) :
    finiteComplexInner u v
      = ∑ j, conj (finiteComplexInner (e j) u) * finiteComplexInner (e j) v := by
  conv_lhs => rw [← heb.complete u]
  exact finiteComplexInner_sum_smul_left (fun j => finiteComplexInner (e j) u) e v

/-- The padded word index of depth `s` over a gate alphabet. -/
theorem card_wordIndex (Γ : Type*) [Fintype Γ] (s : ℕ) :
    Fintype.card (Fin s → Γ) = Fintype.card Γ ^ s := by
  simp

/-- **`(14)`.**  The card's depth schedule `(s+1)ℓ ≤ r/4`, with `log M ≤ ℓ log 2`, gives the
counting condition of the complete-union bound. -/
theorem circuitCount_log_le {M : ℝ} {ell r s : ℕ}
    (hlog : Real.log M ≤ (ell : ℝ) * Real.log 2)
    (hs : ((s : ℝ) + 1) * (ell : ℝ) ≤ (r : ℝ) / 4) :
    ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hs1 : (0 : ℝ) ≤ (s : ℝ) + 1 := by positivity
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  calc ((s : ℝ) + 1) * Real.log M ≤ ((s : ℝ) + 1) * ((ell : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlog hs1
    _ = (((s : ℝ) + 1) * (ell : ℝ)) * Real.log 2 := by ring
    _ ≤ ((r : ℝ) / 4) * Real.log 2 := mul_le_mul_of_nonneg_right hs hlog2.le
    _ ≤ ((r : ℝ) / 2) * Real.log 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hlog2.le
        linarith

/-- The dictionary bound in the form the counting theorem consumes. -/
theorem card_wordIndex_le_pow {Γ : Type*} [Fintype Γ] {M : ℝ} (hM : (Fintype.card Γ : ℝ) ≤ M)
    (hM1 : 1 ≤ M) (s : ℕ) :
    (Fintype.card (Fin s → Γ) : ℝ) ≤ M ^ (s + 1) := by
  have hcard : (Fintype.card (Fin s → Γ) : ℝ) = (Fintype.card Γ : ℝ) ^ s := by
    rw [card_wordIndex]
    push_cast
    ring
  rw [hcard]
  calc ((Fintype.card Γ : ℝ)) ^ s ≤ M ^ s := pow_le_pow_left₀ (by positivity) hM s
    _ ≤ M ^ (s + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ s)

end GaloisForLFunctions.HTGeometry

end
