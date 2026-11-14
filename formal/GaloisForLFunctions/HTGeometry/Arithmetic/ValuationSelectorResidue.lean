import GaloisForLFunctions.HTGeometry.Arithmetic.FiniteValuationSelector
import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralResidue

/-!
# Residue counts for finite precision selectors

When `v_p(R)=1`, each reciprocal selector factor reduces to one exactly
when its precision test passes, and to zero otherwise. Candidate weights
therefore reduce to conjunction indicators, and their sum reduces to the
number of passing candidates. A prime larger than the candidate family
prevents a nonempty collection of successes from cancelling modulo `p`.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

open Finset
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem not_even_val_of_eq_one {R : ℚ} (hR : padicValRat p R = 1) :
    ¬ Even (padicValRat p R) := by rw [hR, Int.even_iff]; omega

/-- A selector factor is the residue indicator of its precision test. -/
theorem valuationSelectorFactor_residue (R D : ℚ) (k : ℕ)
    (hR : padicValRat p R = 1) :
    ratRes p (1 + R * (D / R ^ k) ^ 2)⁻¹ =
      if D = 0 ∨ (k : ℤ) ≤ padicValRat p D then 1 else 0 := by
  classical
  have hR0 : R ≠ 0 := by intro h; simp [h] at hR
  have hodd := not_even_val_of_eq_one hR
  by_cases hpass : D = 0 ∨ (k : ℤ) ≤ padicValRat p D
  · rw [if_pos hpass]
    rcases hpass with rfl | hpass
    · simp [ratRes_one]
    by_cases hD : D = 0
    · simp [hD, ratRes_one]
    have hprod : 0 < padicValRat p (R * (D / R ^ k) ^ 2) := by
      rw [padicValRat.mul hR0 (pow_ne_zero 2 (div_ne_zero hD (pow_ne_zero k hR0))),
        padicValRat.pow, padicValRat.div hD (pow_ne_zero k hR0), padicValRat.pow, hR]
      norm_cast
      omega
    have hres : ratRes p (1 + R * (D / R ^ k) ^ 2) = 1 := by
      rw [ratRes_add_integral (by simp) hprod.le, ratRes_one,
        ratRes_eq_zero_of_val_pos hprod, add_zero]
    have hu := isPadicUnit_of_ratRes_ne_zero (p := p) (q := 1 + R * (D / R ^ k) ^ 2)
      (by rw [hres]; exact one_ne_zero)
    rw [ratRes_inv hu, hres, inv_one]
  · rw [if_neg hpass]
    push Not at hpass
    apply ratRes_eq_zero_of_val_pos
    rw [padicValRat.inv, odd_factor_val hodd (div_ne_zero hpass.1 (pow_ne_zero k hR0)),
      padicValRat.div hpass.1 (pow_ne_zero k hR0), padicValRat.pow, hR]
    norm_cast
    omega

/-- Multiplying selector factors implements conjunction at the residue level. -/
theorem valuationSelectorWeight_residue {J : Type*} (s : Finset J) (k : J → ℕ)
    (R : ℚ) (D : J → ℚ) (hR : padicValRat p R = 1) :
    ratRes p (valuationSelectorWeight s k R D) =
      if ∀ j ∈ s, D j = 0 ∨ (k j : ℤ) ≤ padicValRat p (D j) then 1 else 0 := by
  classical
  rw [valuationSelectorWeight, ratRes_finset_prod s _
    (fun j _ => odd_factor_inv_integral (not_even_val_of_eq_one hR) _)]
  simp only [valuationSelectorFactor_residue R _ _ hR]
  by_cases hpass : ∀ j ∈ s, D j = 0 ∨ (k j : ℤ) ≤ padicValRat p (D j)
  · rw [if_pos hpass]
    exact prod_eq_one (fun j hj => if_pos (hpass j hj))
  · rw [if_neg hpass]
    push Not at hpass
    obtain ⟨j, hj, hD, hfail⟩ := hpass
    exact prod_eq_zero hj (if_neg (by simp only [hD, false_or]; omega))

/-- The selector sum reduces to the number of candidates passing every
test. This identity holds even when the count vanishes modulo `p`. -/
theorem valuationSelectorSum_residue {G J : Type*} (g : Finset G) (s : Finset J)
    (k : J → ℕ) (R : ℚ) (D : G → J → ℚ) (hR : padicValRat p R = 1) :
    ratRes p (valuationSelectorSum g s k R D) =
      ((g.filter (fun a => ∀ j ∈ s, D a j = 0 ∨
        (k j : ℤ) ≤ padicValRat p (D a j))).card : ZMod p) := by
  classical
  rw [valuationSelectorSum, ratRes_finset_sum g _
    (fun a _ => valuationSelectorWeight_integral s k (not_even_val_of_eq_one hR) (D a))]
  simp only [valuationSelectorWeight_residue s k R _ hR, sum_boole]

/-- Below the residue characteristic, a nonempty collection of successful
candidates cannot cancel. Precision zero is allowed. -/
theorem valuationSelectorSum_residue_ne_zero_iff {G J : Type*}
    (g : Finset G) (s : Finset J) (k : J → ℕ) (R : ℚ) (D : G → J → ℚ)
    (hR : padicValRat p R = 1) (hcard : g.card < p) :
    ratRes p (valuationSelectorSum g s k R D) ≠ 0 ↔
      ∃ a ∈ g, ∀ j ∈ s, D a j = 0 ∨ (k j : ℤ) ≤ padicValRat p (D a j) := by
  classical
  rw [valuationSelectorSum_residue g s k R D hR]
  let good := g.filter (fun a => ∀ j ∈ s, D a j = 0 ∨
    (k j : ℤ) ≤ padicValRat p (D a j))
  have hbound : good.card < p := (card_filter_le g _).trans_lt hcard
  change (good.card : ZMod p) ≠ 0 ↔ _
  rw [Ne, natCast_zmod_eq_zero_iff]
  constructor
  · intro h
    have hpos : 0 < good.card := by
      by_contra hn
      have hz : good.card = 0 := by omega
      exact h (hz ▸ dvd_zero p)
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    exact ⟨a, (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩
  · rintro ⟨a, ha, hpass⟩
    have hpos : 0 < good.card := card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hpass⟩⟩
    exact Nat.not_dvd_of_pos_of_lt hpos hbound

/-- Positive selector parameters make every weight strictly positive. -/
theorem valuationSelectorWeight_pos {J : Type*} (s : Finset J) (k : J → ℕ)
    {R : ℚ} (hR : 0 < R) (D : J → ℚ) :
    0 < valuationSelectorWeight s k R D := by
  apply prod_pos
  intro j _
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hR.le (sq_nonneg _))

/-- With positive parameter, a nonempty candidate family has nonzero sum. -/
theorem valuationSelectorSum_pos {G J : Type*} (g : Finset G) (s : Finset J)
    (k : J → ℕ) {R : ℚ} (hR : 0 < R) (D : G → J → ℚ) (hg : g.Nonempty) :
    0 < valuationSelectorSum g s k R D := by
  apply sum_pos' (fun a _ => (valuationSelectorWeight_pos s k hR (D a)).le)
  obtain ⟨a, ha⟩ := hg
  exact ⟨a, ha, valuationSelectorWeight_pos s k hR (D a)⟩

#print axioms valuationSelectorSum_residue
#print axioms valuationSelectorSum_residue_ne_zero_iff

end GaloisForLFunctions.HTGeometry.Arithmetic
