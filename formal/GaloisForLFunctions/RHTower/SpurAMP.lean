/-
Doc 24/25 AMP bridge for the SPUR-R stack.

`SpurClearance` proves lower bounds for the AMP margin, and `SpurCPI`
turns margin `> 1` into copy/sign transfer at a critical point.  This
module composes those layers so tracking-window clearance can be consumed
directly by later copy/flip counting arguments.
-/
import GaloisForLFunctions.RHTower.SpurCPI

namespace RHTower

open Polynomial

noncomputable section

/-- Any certified lower bound above `1` makes the AMP margin itself above `1`. -/
theorem margin_gt_one_of_lower_bound_gt_one {K q denom : ℝ}
    (hK : 1 < K) (hbound : K ≤ q / denom) :
    1 < q / denom :=
  lt_of_lt_of_le hK hbound

/-- A lower bound on the exact AMP margin gives copy/sign transfer.

This is the provider-neutral bridge: Theorem A, Theorem B, or any future
clearance estimate only has to prove a lower bound `K ≤ q/(c^4 E)` with
`1 < K`. -/
theorem spur_pair_rootProd_sign_transfer_of_margin_lower_bound (a b : ℝ)
    (s : Multiset ℝ) {d : ℕ} {c K : ℝ}
    (hc : eval c (rootProd s) ≠ 0)
    (hcrit : eval c (derivative (rootProd s)) = 0)
    (hdenpos : 0 < c ^ 4 * spurEnergy s c)
    (hbound : K ≤ spurQ a b d c / (c ^ 4 * spurEnergy s c))
    (hK : 1 < K) :
    0 < eval c (spurPairPolar (a ^ 2 + b ^ 2) (2 * a) d (rootProd s)) *
      eval c (rootProd s) :=
  spur_pair_rootProd_eval_mul_anchor_pos_of_margin_div a b s hc hcrit hdenpos
    (margin_gt_one_of_lower_bound_gt_one hK hbound)

/-- Theorem A tracking clearance, upgraded from a lower bound to `margin > 1`. -/
theorem theoremA_margin_gt_one_from_tracking {a b R z denom m M : ℝ} {d : ℕ}
    (hdpos : 0 < d) (hm : 0 < m) (hM : 0 ≤ M) (hR : 0 < R)
    (hz : |z| ≤ R)
    (hdsize : 2 * R ^ 2 ≤ (d : ℝ) * b ^ 2)
    (hdenpos : 0 < denom)
    (hden : denom ≤ 2 * (M + 1) * R ^ 4 / (m * (d : ℝ) ^ 2))
    (hlarge : 1 < b ^ 2 * m * (d : ℝ) ^ 2 / (4 * (M + 1) * R ^ 4)) :
    1 < spurQ a b d (z / (d : ℝ)) / denom :=
  margin_gt_one_of_lower_bound_gt_one hlarge
    (theoremA_margin_lower_bound_from_tracking hdpos hm hM hR hz hdsize hdenpos hden)

/-- Theorem A tracking clearance gives copy/sign transfer at a tracked critical point.

The denominator is instantiated as the AMP denominator `c^4 E(c)` with
`c = z/d`.  Analytic facts such as denominator positivity and criticality remain
explicit hypotheses; the finite clearance-to-sign-transfer composition is closed here. -/
theorem spur_pair_rootProd_tracking_sign_transfer (a b : ℝ) (s : Multiset ℝ)
    {d : ℕ} {z m M R : ℝ}
    (hdpos : 0 < d) (hm : 0 < m) (hM : 0 ≤ M) (hR : 0 < R)
    (hz : |z| ≤ R)
    (hdsize : 2 * R ^ 2 ≤ (d : ℝ) * b ^ 2)
    (hdenpos : 0 < (z / (d : ℝ)) ^ 4 * spurEnergy s (z / (d : ℝ)))
    (hden : (z / (d : ℝ)) ^ 4 * spurEnergy s (z / (d : ℝ))
      ≤ 2 * (M + 1) * R ^ 4 / (m * (d : ℝ) ^ 2))
    (hlarge : 1 < b ^ 2 * m * (d : ℝ) ^ 2 / (4 * (M + 1) * R ^ 4))
    (hc : eval (z / (d : ℝ)) (rootProd s) ≠ 0)
    (hcrit : eval (z / (d : ℝ)) (derivative (rootProd s)) = 0) :
    0 < eval (z / (d : ℝ))
        (spurPairPolar (a ^ 2 + b ^ 2) (2 * a) d (rootProd s)) *
      eval (z / (d : ℝ)) (rootProd s) :=
  spur_pair_rootProd_sign_transfer_of_margin_lower_bound a b s hc hcrit hdenpos
    (theoremA_margin_lower_bound_from_tracking hdpos hm hM hR hz hdsize hdenpos hden)
    hlarge

end

end RHTower
