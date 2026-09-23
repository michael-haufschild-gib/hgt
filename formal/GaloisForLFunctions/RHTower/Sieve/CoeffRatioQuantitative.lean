import GaloisForLFunctions.RHTower.Sieve.PolyExpQuantitative
import GaloisForLFunctions.RHTower.Sieve.CoeffRatioBound

/-!
# The majorant at the chosen width, with a rate

Composing the pointwise reduction of `CoeffRatioBound` with the quantitative decay of
`PolyExpQuantitative`: at the smoothing width of the contour argument the majorant times the saving
is not merely `o(1)` but

    coeffMajorant (C(L+2)²) (C'(L+2)) M₀ a t · exp(-κt) ≤ exp(-κv²/2)

for all large `v`, whenever `v² ≤ t ≤ 2v²` and `L + 2 ≤ 3e^v` — the relations the chosen width
satisfies.  With `v = (log N)^{1/20}` this is `exp(-κ(log N)^{1/10}/2)`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The majorant at the chosen width, with a rate.** -/
theorem eventually_coeffMajorant_ratio_le_exp {C C' M₀ a κ : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM₀ : 0 ≤ M₀) (ha : 0 ≤ a) (hκ : 0 < κ) :
    ∀ᶠ v : ℝ in atTop, ∀ t L : ℝ, 0 ≤ t → v ^ (2 : ℕ) ≤ t → t ≤ 2 * v ^ (2 : ℕ) →
      L + 2 ≤ 3 * Real.exp v → 0 ≤ L + 2 →
      coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a t * Real.exp (-(κ * t))
        ≤ Real.exp (-(κ * v ^ (2 : ℕ) / 2)) := by
  have hpoly := eventually_poly_exp_two_sub_sq_le (a := 512 * a)
    (b := 8 * (9 * C) * Real.exp (22 / 4)
        + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
        + M₀ * (4 + 2 * (9 * C)))
    (c := (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4) hκ
  filter_upwards [hpoly, eventually_ge_atTop (0 : ℝ)] with v hv hv0
  intro t L ht0 htlo hthi hL hL0
  exact le_trans
    (coeffMajorant_ratio_le hC hC' hM₀ ha hκ.le hv0 ht0 htlo hthi hL hL0) hv

end RHTower.Sieve
