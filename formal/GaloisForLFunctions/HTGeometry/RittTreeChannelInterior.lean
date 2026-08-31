import GaloisForLFunctions.HTGeometry.RittTreeChannelMap
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The interior channel

For a strictly informative binary channel the two affine signal parameters satisfy `−1 < v < u < 1`,
and the three invariants of the conjugated normal form are then real and sign-definite:

`A = (1−u)/(1−v) ∈ (0,1)`,   `B = (1+u)/(1+v) > 1`,   `λ = (1+v)/(v−1) < 0`.

So `A^p < 1 < B^p`, the first critical value is not a pole because `1 − λA^p > 1`, and in degree two
the image of `A` is positive while `−A` and `−B` are negative.  Every hypothesis of the no-cocycle
theorem holds, and the tree channel map of an interior channel preserves no rational
`k`-differential up to scale.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

noncomputable section

theorem treeA_ofReal (u v : ℝ) : treeA (u : ℂ) (v : ℂ) = ((treeA u v : ℝ) : ℂ) := by
  rw [treeA, treeA]
  push_cast
  ring

theorem treeB_ofReal (u v : ℝ) : treeB (u : ℂ) (v : ℂ) = ((treeB u v : ℝ) : ℂ) := by
  rw [treeB, treeB]
  push_cast
  ring

theorem treeLam_ofReal (v : ℝ) : treeLam (v : ℂ) = ((treeLam v : ℝ) : ℂ) := by
  rw [treeLam, treeLam]
  push_cast
  ring

theorem treeA_pos {u v : ℝ} (huv : v < u) (hu : u < 1) : 0 < treeA u v := by
  rw [treeA]
  apply div_pos <;> linarith

theorem treeA_lt_one {u v : ℝ} (huv : v < u) (hu : u < 1) : treeA u v < 1 := by
  rw [treeA, div_lt_one (by linarith)]
  linarith

theorem one_lt_treeB {u v : ℝ} (hv : -1 < v) (huv : v < u) : 1 < treeB u v := by
  rw [treeB, lt_div_iff₀ (by linarith)]
  linarith

theorem treeLam_neg {v : ℝ} (hv : -1 < v) (hv1 : v < 1) : treeLam v < 0 := by
  rw [treeLam]
  exact div_neg_of_pos_of_neg (by linarith) (by linarith)

/-- **An interior tree channel map preserves no rational `k`-differential up to scale.** -/
theorem treeRG_no_cocycle_interior {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    {k : ℤ} (hk : k ≠ 0) {b : ℂ} (hb : b ≠ 0) {G : RatFunc ℂ} (hG : G ≠ 0)
    (heq : IsRatAffineTransport (treeRG p (u : ℂ) (v : ℂ)) hR k (RatFunc.C b) 0 G) : False := by
  have hp0 : p ≠ 0 := by omega
  have hv1 : v < 1 := lt_trans huv hu
  have hA0 : 0 < treeA u v := treeA_pos huv hu
  have hA1 : treeA u v < 1 := treeA_lt_one huv hu
  have hB1 : 1 < treeB u v := one_lt_treeB hv huv
  have hL : treeLam v < 0 := treeLam_neg hv hv1
  have hApow : treeA u v ^ p < 1 := pow_lt_one₀ (le_of_lt hA0) hA1 hp0
  have hBpow : 1 < treeB u v ^ p := one_lt_pow₀ hB1 hp0
  have hApowpos : 0 < treeA u v ^ p := pow_pos hA0 p
  have hLA : treeLam v * treeA u v ^ p < 0 := mul_neg_of_neg_of_pos hL hApowpos
  have hDen : 0 < 1 - treeLam v * treeA u v ^ p := by linarith
  have hNumpos : 0 < treeA u v - treeB u v * treeLam v * treeA u v ^ p := by
    have : treeB u v * (treeLam v * treeA u v ^ p) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hLA
    nlinarith
  have hImg : 0 < (treeA u v - treeB u v * treeLam v * treeA u v ^ p)
      / (1 - treeLam v * treeA u v ^ p) := div_pos hNumpos hDen
  refine treeRG_no_cocycle hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hk hb hG heq
  · exact_mod_cast ne_of_gt huv
  · exact_mod_cast ne_of_lt hu
  · have : u ≠ -1 := by intro h; rw [h] at huv; linarith
    exact_mod_cast this
  · exact_mod_cast ne_of_lt hv1
  · have : v ≠ -1 := ne_of_gt hv
    exact_mod_cast this
  · rw [treeA_ofReal, treeB_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
    intro h
    have hreal : treeA u v ^ p = treeB u v ^ p := by exact_mod_cast h
    linarith
  · rw [treeA_ofReal, treeLam_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    intro h
    have hreal : 1 - treeLam v * treeA u v ^ p = 0 := by exact_mod_cast h
    linarith
  · intro _
    have hcoe : (treeA (u : ℂ) (v : ℂ)
          - treeB (u : ℂ) (v : ℂ) * treeLam (v : ℂ) * treeA (u : ℂ) (v : ℂ) ^ p)
        / (1 - treeLam (v : ℂ) * treeA (u : ℂ) (v : ℂ) ^ p)
        = (((treeA u v - treeB u v * treeLam v * treeA u v ^ p)
          / (1 - treeLam v * treeA u v ^ p) : ℝ) : ℂ) := by
      rw [treeA_ofReal, treeB_ofReal, treeLam_ofReal]
      push_cast
      ring
    constructor
    · rw [hcoe, treeA_ofReal, ← Complex.ofReal_neg]
      intro h
      have hreal : (treeA u v - treeB u v * treeLam v * treeA u v ^ p)
          / (1 - treeLam v * treeA u v ^ p) = -treeA u v := by exact_mod_cast h
      linarith
    · rw [hcoe, treeB_ofReal, ← Complex.ofReal_neg]
      intro h
      have hreal : (treeA u v - treeB u v * treeLam v * treeA u v ^ p)
          / (1 - treeLam v * treeA u v ^ p) = -treeB u v := by exact_mod_cast h
      linarith

end

end GaloisForLFunctions.HTGeometry
