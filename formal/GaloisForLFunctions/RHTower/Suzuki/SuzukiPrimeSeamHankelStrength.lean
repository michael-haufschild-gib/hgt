import GaloisForLFunctions.RHTower.Suzuki.SuzukiRelativeEdgeParityFloor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Narrow prime seams have vanishing normalized Hankel strength

A packet supported in an interval of width `η`, with buffers of width `d` on both sides, pays a
common Cauchy energy at least

`log(1 + d/s) + log(1 + d/(η - s))`

per unit mass at relative position `s`.  The bracket is exactly minimized at the midpoint, where it
equals `2 log(1 + 2d/η)`: writing `u = s(η - s)`, the product of the two factors is
`1 + d(η + d)/u`, and `u ≤ η²/4` by the arithmetic–geometric mean.

The Hankel strength of such a packet stays bounded — one reflection of norm `w` plus a regular
kernel on a set of measure `2mη`.  So the relative Hankel Rayleigh quotient is at most

`(w + 2mMη)/(log(1 + 2d/η) - B)`,

which tends to zero as the seam narrows: the logarithmic Cauchy energy diverges while the Hankel
strength stays bounded.  Narrow seam packets therefore accumulate at the centre of the relative
contraction, not at either coercivity edge.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-! ## The exact midpoint minimum of the seam bracket -/

/-- The product form of the seam bracket is minimized at the midpoint. -/
theorem seam_product_ge {d η s : ℝ} (hd : 0 < d) (hη : 0 < η) (hs0 : 0 < s) (hs : s < η) :
    (1 + 2 * d / η) ^ (2 : ℕ) ≤ (1 + d / s) * (1 + d / (η - s)) := by
  have hηs : (0 : ℝ) < η - s := by linarith
  have hu : (0 : ℝ) < s * (η - s) := by positivity
  have hamgm : s * (η - s) ≤ η ^ (2 : ℕ) / 4 := by nlinarith [sq_nonneg (s - (η - s))]
  have hprod : (1 + d / s) * (1 + d / (η - s))
      = 1 + (d * η + d ^ (2 : ℕ)) / (s * (η - s)) := by
    field_simp
    ring
  have hsq : (1 + 2 * d / η) ^ (2 : ℕ) = 1 + (d * η + d ^ (2 : ℕ)) / (η ^ (2 : ℕ) / 4) := by
    field_simp
    ring
  rw [hprod, hsq]
  have hnum : (0 : ℝ) < d * η + d ^ (2 : ℕ) := by positivity
  have hstep : (d * η + d ^ (2 : ℕ)) / (η ^ (2 : ℕ) / 4) ≤ (d * η + d ^ (2 : ℕ)) / (s * (η - s)) :=
    div_le_div_of_nonneg_left hnum.le hu hamgm
  linarith

/-- **`(262)`: the exact midpoint minimum of the seam bracket.** -/
theorem seam_bracket_ge {d η s : ℝ} (hd : 0 < d) (hη : 0 < η) (hs0 : 0 < s) (hs : s < η) :
    2 * Real.log (1 + 2 * d / η) ≤ Real.log (1 + d / s) + Real.log (1 + d / (η - s)) := by
  have hηs : (0 : ℝ) < η - s := by linarith
  have h1 : (0 : ℝ) < 1 + d / s := by positivity
  have h2 : (0 : ℝ) < 1 + d / (η - s) := by positivity
  have h0 : (0 : ℝ) < 1 + 2 * d / η := by positivity
  have hprod := seam_product_ge hd hη hs0 hs
  have hlog : Real.log ((1 + 2 * d / η) ^ (2 : ℕ)) ≤ Real.log ((1 + d / s) * (1 + d / (η - s))) :=
    Real.log_le_log (by positivity) hprod
  rwa [Real.log_pow, Real.log_mul (ne_of_gt h1) (ne_of_gt h2)] at hlog

/-! ## The vanishing relative strength -/

/-- The seam Cauchy energy diverges as the seam narrows. -/
theorem tendsto_seam_energy_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (fun η : ℝ => Real.log (1 + 2 * d / η)) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun η : ℝ => η⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hscale : Tendsto (fun η : ℝ => 2 * d / η) (𝓝[>] (0 : ℝ)) atTop := by
    have h := hinv.atTop_mul_const (r := 2 * d) (by linarith)
    refine h.congr fun η => ?_
    ring
  have hshift : Tendsto (fun η : ℝ => 1 + 2 * d / η) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_atTop_add_const_left _ 1 hscale
  exact Real.tendsto_log_atTop.comp hshift

/-- **`(264)`: the relative Hankel strength of a narrow seam packet tends to zero.** -/
theorem tendsto_seam_ratio_zero {d w M B : ℝ} (m : ℕ) (hd : 0 < d) :
    Tendsto (fun η : ℝ => (w + 2 * (m : ℝ) * M * η) / (Real.log (1 + 2 * d / η) - B))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hnum : Tendsto (fun η : ℝ => w + 2 * (m : ℝ) * M * η) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := (tendsto_const_nhds (x := w) (f := 𝓝[>] (0 : ℝ))).add
      ((tendsto_const_nhds (x := 2 * (m : ℝ) * M) (f := 𝓝[>] (0 : ℝ))).mul hid)
    simpa using h
  have hden : Tendsto (fun η : ℝ => Real.log (1 + 2 * d / η) - B) (𝓝[>] (0 : ℝ)) atTop := by
    have h := (tendsto_seam_energy_atTop hd).atTop_add
      (tendsto_const_nhds (x := -B) (f := 𝓝[>] (0 : ℝ)))
    refine h.congr fun η => ?_
    ring
  exact hnum.div_atTop hden

end RHTower
