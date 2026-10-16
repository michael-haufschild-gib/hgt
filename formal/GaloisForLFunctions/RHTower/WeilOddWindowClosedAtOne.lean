import GaloisForLFunctions.RHTower.WeilOddBlindPoleWeightWindow

/-!
# The blind odd window is closed at pole weight `1`

Prime-blind positivity on odd tests at pole weight `β` (`PrimeBlindPositiveOddAt β`) is a down-set
in `β` capped at `1`.  The pole-weight functional `poleWeightArchRe β f = A(k_f) + (β − 1) Re P(k_f)`
is affine in `β`, so for every fixed blind combination the value at `β = 1` is the limit of the
values at `β < 1`.  Hence the window is closed at its cap: blind odd positivity at every pole weight
`β < 1` already gives blind odd positivity at `1`, and by odd Farkas an odd Weil-positive weight at
the critical pole weight exists as soon as odd Weil-positive weights exist at every sub-critical
pole weight (`exists_weilPositiveOdd_iff_forall_lt_one`).  The odd-positive source problem at the
critical pole weight is therefore the family of sub-critical source problems, where the pole of the
archimedean term only has to be cancelled to density `β < 1`.
-/

open Complex Finsupp Zeta23

noncomputable section

namespace RHTower
open WeilOneSided WeilPoleWeight

/-- The pole-weight functional of a blind combination is affine in `β`. -/
theorem sum_poleWeightArchRe_eq (c : WeilOddTestFn →₀ ℝ) (β : ℝ) :
    (c.sum fun f t => t * poleWeightArchRe β f.1) =
      (c.sum fun f t => t * poleWeightArchRe 1 f.1) +
        (β - 1) * c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1.1 f.1.1)).re := by
  simp only [Finsupp.sum, poleWeightArchRe, sub_self, zero_mul, add_zero, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- **The window is closed at `1`.**  Blind odd positivity at every pole weight `β < 1` gives blind
odd positivity at pole weight `1`. -/
theorem primeBlindPositiveOddAt_one_of_forall_lt
    (h : ∀ β : ℝ, β < 1 → PrimeBlindPositiveOddAt β) : PrimeBlindPositiveOddAt 1 := by
  intro c hc hnull
  set A : ℝ := c.sum fun f t => t * poleWeightArchRe 1 f.1 with hA
  set B : ℝ := c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1.1 f.1.1)).re with hB
  have key : ∀ ε : ℝ, 0 < ε → 0 ≤ A - ε * B := by
    intro ε hε
    have h1 := h (1 - ε) (by linarith) c hc hnull
    rw [sum_poleWeightArchRe_eq, ← hA, ← hB] at h1
    have e : A + (1 - ε - 1) * B = A - ε * B := by ring
    rw [e] at h1
    exact h1
  show 0 ≤ A
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  have hpos : 0 < ε' / (|B| + 1) := by positivity
  have h1 := key _ hpos
  have h2 : -(ε' / (|B| + 1)) * |B| ≤ ε' / (|B| + 1) * B := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le B) hpos.le
    linarith
  have h3 : ε' / (|B| + 1) * |B| ≤ ε' := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg B]
  linarith

/-- The blind odd window at `1` is the intersection of the sub-critical windows. -/
theorem primeBlindPositiveOddAt_one_iff_forall_lt :
    PrimeBlindPositiveOddAt 1 ↔ ∀ β : ℝ, β < 1 → PrimeBlindPositiveOddAt β :=
  ⟨fun h _ hβ => primeBlindPositiveOddAt_anti hβ.le h, primeBlindPositiveOddAt_one_of_forall_lt⟩

/-- **Sub-critical sources give a critical source.**  An odd Weil-positive weight at pole weight
`1` exists iff odd Weil-positive weights exist at every pole weight `β < 1`. -/
theorem exists_weilPositiveOdd_iff_forall_lt_one :
    (∃ lam : ℕ → ℝ, WeilPositiveOdd lam) ↔
      ∀ β : ℝ, β < 1 → ∃ lam : ℕ → ℝ, WeilPositiveOddAt β lam := by
  constructor
  · rintro ⟨lam, h⟩ β hβ
    exact ⟨lam, weilPositiveOddAt_anti hβ.le (weilPositiveOddAt_one_iff.mpr h)⟩
  · intro h
    obtain ⟨lam, hlam⟩ := (exists_weilPositiveOddAt_iff 1).mpr
      (primeBlindPositiveOddAt_one_of_forall_lt fun β hβ =>
        (exists_weilPositiveOddAt_iff β).mp (h β hβ))
    exact ⟨lam, weilPositiveOddAt_one_iff.mp hlam⟩

end RHTower
