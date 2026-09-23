/-
Doc 23/24 CPI bridge for the SPUR-R / AMP stack.

`SpurOperator` supplies the pair operator in polar-chain form, `SpurClearance` names
the pair quadratic `q_d`, and `SpurWeights` supplies the electrostatic energy identity.
This module joins those bricks at the exact paper interface:

* at a critical point of the anchor `A`, the pair section evaluates as
  `q_d(c) * A(c) + c^(4 : ℕ) * A''(c)`;
* for a real-root product, the energy identity rewrites this as
  `(q_d(c) - c^(4 : ℕ) * energy(c)) * A(c)`.

This is the formal CPI-to-AMP margin bridge: sign transfer is governed by the single
scalar `q_d(c) - c^(4 : ℕ) * energy(c)`, with no amplitude left in the comparison.
-/
import GaloisForLFunctions.RHTower.SpurClearance
import GaloisForLFunctions.RHTower.SpurOperator
import GaloisForLFunctions.RHTower.SpurWeights

namespace RHTower

open Polynomial

noncomputable section

/-- The denominator-cleared pair polynomial in the polar-chain variables. -/
def spurPairPolar (u v : ℝ) (d : ℕ) (A : ℝ[X]) : ℝ[X] :=
  C u * A - C v * (X * polarStep d A)
    + X ^ (2 : ℕ) * polarStep (d - 1) (polarStep d A)

/-- CPI in pure polar-chain form.

At a critical point of the anchor `A`, the polar companions collapse, leaving the
pair polynomial equal to the pair quadratic times `A(c)` plus the curvature term
`c^(4 : ℕ) A''(c)`. -/
theorem eval_pair_polar_at_critical (u v : ℝ) (A : ℝ[X]) {d : ℕ} {c : ℝ}
    (hcrit : eval c (derivative A) = 0) :
    eval c (spurPairPolar u v d A) =
      (u - v * (d : ℝ) * c + (d : ℝ) * ((d : ℝ) - 1) * c ^ (2 : ℕ)) * eval c A
        + c ^ (4 : ℕ) * eval c (derivative (derivative A)) := by
  have hB₁eval : eval c (polarStep d A) = (d : ℝ) * eval c A := by
    rw [polarStep, eval_sub, eval_mul, eval_C, eval_mul, eval_X, hcrit, mul_zero, sub_zero]
  have hB₁deriv : eval c (derivative (polarStep d A)) =
      -c * eval c (derivative (derivative A)) := by
    rw [polarStep, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_mul, derivative_X, one_mul, eval_sub, eval_mul, eval_C, eval_add,
      eval_mul, eval_X, hcrit]
    ring
  have hcast_sub_one :
      (((d - 1 : ℕ) : ℝ) * (d : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) := by
    by_cases hd0 : d = 0
    · subst d
      norm_num
    · have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
      rw [Nat.cast_sub hd1]
      ring
  have hB₂eval : eval c (polarStep (d - 1) (polarStep d A)) =
      (d : ℝ) * ((d : ℝ) - 1) * eval c A +
        c ^ (2 : ℕ) * eval c (derivative (derivative A)) := by
    rw [polarStep, eval_sub, eval_mul, eval_C, hB₁eval, eval_mul, eval_X, hB₁deriv]
    calc
      ((d - 1 : ℕ) : ℝ) * ((d : ℝ) * eval c A) -
          c * (-c * eval c (derivative (derivative A)))
          = (((d - 1 : ℕ) : ℝ) * (d : ℝ)) * eval c A +
              c ^ (2 : ℕ) * eval c (derivative (derivative A)) := by ring
      _ = (d : ℝ) * ((d : ℝ) - 1) * eval c A +
          c ^ (2 : ℕ) * eval c (derivative (derivative A)) := by
            rw [hcast_sub_one]
  rw [spurPairPolar, eval_add, eval_sub, eval_mul, eval_C, eval_mul, eval_C, eval_mul,
    eval_X, hB₁eval, eval_mul, eval_pow, eval_X, hB₂eval]
  ring

/-- The SPUR-R CPI identity with the paper quadratic `q_d(c) = spurQ a b d c`. -/
theorem eval_spur_pair_at_critical (a b : ℝ) (A : ℝ[X]) {d : ℕ} {c : ℝ}
    (hcrit : eval c (derivative A) = 0) :
    eval c (spurPairPolar (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) d A) =
      spurQ a b d c * eval c A + c ^ (4 : ℕ) * eval c (derivative (derivative A)) := by
  rw [eval_pair_polar_at_critical (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) A hcrit, spurQ]

/-- CPI after the electrostatic energy identity.

For a real-root product anchor, at a nonzero critical point the curvature term is
`-energy(c) * A(c)`, so the pair value is exactly
`(q_d(c) - c^(4 : ℕ) * energy(c)) * A(c)`. This is doc 24's amplitude-free AMP margin form. -/
theorem eval_spur_pair_rootProd_at_critical (a b : ℝ) (s : Multiset ℝ) {d : ℕ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0)
    (hcrit : eval c (derivative (rootProd s)) = 0) :
    eval c (spurPairPolar (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) d (rootProd s)) =
      (spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) *
        eval c (rootProd s) := by
  rw [eval_spur_pair_at_critical a b (rootProd s) hcrit,
    energy_eq_neg_second_derivative hc hcrit]
  ring

/-- Electrostatic energy denominator appearing in the AMP margin. -/
def spurEnergy (s : Multiset ℝ) (c : ℝ) : ℝ :=
  (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum

/-- Positive AMP margin gives copy/sign transfer at a nonzero critical point.

The product form avoids choosing a sign for the anchor: `J(c) * A(c) > 0`
means the pair section and anchor have the same sign. -/
theorem spur_pair_rootProd_eval_mul_anchor_pos_of_margin (a b : ℝ) (s : Multiset ℝ)
    {d : ℕ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0)
    (hcrit : eval c (derivative (rootProd s)) = 0)
    (hmargin : c ^ (4 : ℕ) * spurEnergy s c < spurQ a b d c) :
    0 < eval c (spurPairPolar (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) d (rootProd s)) *
      eval c (rootProd s) := by
  have hmargin' :
      c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum < spurQ a b d c := by
    simpa [spurEnergy] using hmargin
  have hscalar : 0 <
      spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum := by
    linarith
  have hanchor_sq : 0 < eval c (rootProd s) ^ (2 : ℕ) := sq_pos_of_ne_zero hc
  rw [eval_spur_pair_rootProd_at_critical a b s hc hcrit]
  have hmul :
      ((spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) *
            eval c (rootProd s)) * eval c (rootProd s) =
        (spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) *
          eval c (rootProd s) ^ (2 : ℕ) := by
    ring
  rw [hmul]
  exact mul_pos hscalar hanchor_sq

/-- Negative AMP margin gives flip/opposite-sign transfer at a nonzero critical point. -/
theorem spur_pair_rootProd_eval_mul_anchor_neg_of_margin (a b : ℝ) (s : Multiset ℝ)
    {d : ℕ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0)
    (hcrit : eval c (derivative (rootProd s)) = 0)
    (hmargin : spurQ a b d c < c ^ (4 : ℕ) * spurEnergy s c) :
    eval c (spurPairPolar (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) d (rootProd s)) *
      eval c (rootProd s) < 0 := by
  have hmargin' :
      spurQ a b d c < c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum := by
    simpa [spurEnergy] using hmargin
  have hscalar :
      spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum < 0 := by
    linarith
  have hanchor_sq : 0 < eval c (rootProd s) ^ (2 : ℕ) := sq_pos_of_ne_zero hc
  rw [eval_spur_pair_rootProd_at_critical a b s hc hcrit]
  have hmul :
      ((spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) *
            eval c (rootProd s)) * eval c (rootProd s) =
        (spurQ a b d c - c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) *
          eval c (rootProd s) ^ (2 : ℕ) := by
    ring
  rw [hmul]
  exact mul_neg_of_neg_of_pos hscalar hanchor_sq

/-- Boundary AMP margin makes the pair section vanish at the critical point. -/
theorem spur_pair_rootProd_eval_eq_zero_of_margin_eq (a b : ℝ) (s : Multiset ℝ)
    {d : ℕ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0)
    (hcrit : eval c (derivative (rootProd s)) = 0)
    (hmargin : spurQ a b d c = c ^ (4 : ℕ) * spurEnergy s c) :
    eval c (spurPairPolar (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) d (rootProd s)) = 0 := by
  have hmargin' :
      spurQ a b d c = c ^ (4 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum := by
    simpa [spurEnergy] using hmargin
  rw [eval_spur_pair_rootProd_at_critical a b s hc hcrit, hmargin']
  ring

/-- Division-form AMP margin `q/(c^(4 : ℕ) E) > 1` implies copy/sign transfer.

This is a wrapper around `spur_pair_rootProd_eval_mul_anchor_pos_of_margin`; the core
theorem uses the multiplication-cleared inequality. -/
theorem spur_pair_rootProd_eval_mul_anchor_pos_of_margin_div (a b : ℝ) (s : Multiset ℝ)
    {d : ℕ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0)
    (hcrit : eval c (derivative (rootProd s)) = 0)
    (hdenpos : 0 < c ^ (4 : ℕ) * spurEnergy s c)
    (hmargin : 1 < spurQ a b d c / (c ^ (4 : ℕ) * spurEnergy s c)) :
    0 < eval c (spurPairPolar (a ^ (2 : ℕ) + b ^ (2 : ℕ)) (2 * a) d (rootProd s)) *
      eval c (rootProd s) := by
  have hmul : c ^ (4 : ℕ) * spurEnergy s c < spurQ a b d c := by
    rw [lt_div_iff₀ hdenpos] at hmargin
    simpa using hmargin
  exact spur_pair_rootProd_eval_mul_anchor_pos_of_margin a b s hc hcrit hmul

end

end RHTower
