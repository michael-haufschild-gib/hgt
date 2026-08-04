import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Splitting a count by sign

If a family splits into two sign classes whose sum has a limiting density and whose difference is
`o` of the scale, then each class has half the density:

    R₊ + R₋ = Q,  R₊ - R₋ = S,  Q/N → q,  S/N → 0   ⟹   R±/N → q/2.

This is the card's passage from `(6)` to `(7)`: the absolute pair count carries the squarefree
density and the signed pair count vanishes, so both sign classes are asymptotically equal.

The statement is about limits only — no arithmetic enters — so it applies verbatim to the balanced
pair counts, to the coprime ones, and to any later refinement.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The positive class.** -/
theorem tendsto_pos_class {Rp Rm Q S N : ℝ → ℝ} {q : ℝ}
    (hsum : ∀ x, Rp x + Rm x = Q x) (hdiff : ∀ x, Rp x - Rm x = S x)
    (hQ : Tendsto (fun x => Q x / N x) atTop (𝓝 q))
    (hS : Tendsto (fun x => S x / N x) atTop (𝓝 0)) :
    Tendsto (fun x => Rp x / N x) atTop (𝓝 (q / 2)) := by
  have hlim := (hQ.add hS).div_const (2 : ℝ)
  rw [add_zero] at hlim
  refine hlim.congr fun x => ?_
  have hRp : Rp x = (Q x + S x) / 2 := by
    have h1 := hsum x
    have h2 := hdiff x
    linarith
  rw [hRp]
  ring

/-- **The negative class.** -/
theorem tendsto_neg_class {Rp Rm Q S N : ℝ → ℝ} {q : ℝ}
    (hsum : ∀ x, Rp x + Rm x = Q x) (hdiff : ∀ x, Rp x - Rm x = S x)
    (hQ : Tendsto (fun x => Q x / N x) atTop (𝓝 q))
    (hS : Tendsto (fun x => S x / N x) atTop (𝓝 0)) :
    Tendsto (fun x => Rm x / N x) atTop (𝓝 (q / 2)) := by
  have hlim := (hQ.sub hS).div_const (2 : ℝ)
  rw [sub_zero] at hlim
  refine hlim.congr fun x => ?_
  have hRm : Rm x = (Q x - S x) / 2 := by
    have h1 := hsum x
    have h2 := hdiff x
    linarith
  rw [hRm]
  ring

/-- **Both classes at once.**  The card's equation `(7)`. -/
theorem tendsto_sign_classes {Rp Rm Q S N : ℝ → ℝ} {q : ℝ}
    (hsum : ∀ x, Rp x + Rm x = Q x) (hdiff : ∀ x, Rp x - Rm x = S x)
    (hQ : Tendsto (fun x => Q x / N x) atTop (𝓝 q))
    (hS : Tendsto (fun x => S x / N x) atTop (𝓝 0)) :
    Tendsto (fun x => Rp x / N x) atTop (𝓝 (q / 2))
      ∧ Tendsto (fun x => Rm x / N x) atTop (𝓝 (q / 2)) :=
  ⟨tendsto_pos_class hsum hdiff hQ hS, tendsto_neg_class hsum hdiff hQ hS⟩

/-- **Deleting a small set keeps a positive density.**  With `R'` obtained from `R` by removing at
most `B`, and `B` of density at most `b < q/2`, the survivor still has positive density. -/
theorem le_liminf_after_deletion {R R' B N : ℝ → ℝ} {q b : ℝ}
    (hdel : ∀ x, R x - B x ≤ R' x)
    (hR : Tendsto (fun x => R x / N x) atTop (𝓝 q))
    (hB : Tendsto (fun x => B x / N x) atTop (𝓝 b))
    (hN : ∀ᶠ x in atTop, 0 < N x) :
    ∀ ε > 0, ∀ᶠ x in atTop, q - b - ε ≤ R' x / N x := by
  intro ε hε
  have hlim : Tendsto (fun x => R x / N x - B x / N x) atTop (𝓝 (q - b)) := hR.sub hB
  filter_upwards [hN, hlim.eventually (eventually_gt_nhds (by linarith : q - b - ε < q - b))]
    with x hx hlt
  have hdiv : (R x - B x) / N x ≤ R' x / N x := by
    have hle := hdel x
    gcongr
  have hrw : (R x - B x) / N x = R x / N x - B x / N x := by
    rw [sub_div]
  rw [hrw] at hdiv
  linarith

end RHTower.Sieve
