import GaloisForLFunctions.RHTower.WeilLogShiftMidpointCharacteristic
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMidpoint

/-! Moving from uniform endpoints to their edge center has vanishing phase cost. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMixture_midpoint_edge_complex_pairing (r k : ℕ) (f : Fin (r + 2) → ℂ) :
    (∑ u, (finiteWeilCanonicalMixture r k (1 / 2) u : ℂ) * f u) =
      (∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * (f i.castSucc + f i.succ)) / 2 := by
  apply Complex.ext
  · simpa [Complex.mul_re, Complex.div_re] using
      finiteWeilCanonicalMixture_midpoint_edge_pairing r k (fun u => (f u).re)
  · simpa [Complex.mul_im, Complex.div_im] using
      finiteWeilCanonicalMixture_midpoint_edge_pairing r k (fun u => (f u).im)

theorem finiteWeilCanonicalEdge_phase_shift_bound (r k : ℕ) (f : Fin (r + 1) → ℝ) (c : ℝ) :
    ‖(∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * finiteWeilPhase (f i + c)) -
      ∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * finiteWeilPhase (f i)‖ ≤ |c| := by
  calc
    _ ≤ ∑ i, |finiteWeilCanonicalEdgeMass r k i| * |(f i + c) - f i| :=
      finiteWeilPhase_phase_error _ _ _
    _ = ∑ i, finiteWeilCanonicalEdgeMass r k i * |c| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_pos (finiteWeilCanonicalEdgeMass_pos r k i), show (f i + c) - f i = c by ring]
    _ = _ := by rw [← Finset.sum_mul, finiteWeilCanonicalEdgeMass_sum, one_mul]

def finiteWeilCanonicalEdgeCharacteristic (r k : ℕ) (u : ℝ) : ℂ :=
  ∑ i : Fin (r + 1), (finiteWeilCanonicalEdgeMass r k i : ℂ) *
    finiteWeilPhase (u * (((i : ℕ) : ℝ) - (r : ℝ) / 2))

theorem finiteWeilCanonicalEdgeCharacteristic_midpoint_bound (r k : ℕ) (u : ℝ) :
    ‖finiteWeilCanonicalMidpointCharacteristic r k u - finiteWeilCanonicalEdgeCharacteristic r k u‖ ≤
      |u| / 2 := by
  let f := fun i : Fin (r + 1) => u * (((i : ℕ) : ℝ) - (r : ℝ) / 2)
  let L := ∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * finiteWeilPhase (f i + (-u / 2))
  let R := ∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * finiteWeilPhase (f i + (u / 2))
  let E := finiteWeilCanonicalEdgeCharacteristic r k u
  have hL : ‖L - E‖ ≤ |u| / 2 := by
    simpa only [L, E, f, finiteWeilCanonicalEdgeCharacteristic, abs_div, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      finiteWeilCanonicalEdge_phase_shift_bound r k f (-u / 2)
  have hR : ‖R - E‖ ≤ |u| / 2 := by
    simpa only [R, E, f, finiteWeilCanonicalEdgeCharacteristic, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      finiteWeilCanonicalEdge_phase_shift_bound r k f (u / 2)
  have hM : finiteWeilCanonicalMidpointCharacteristic r k u = (L + R) / 2 := by
    unfold finiteWeilCanonicalMidpointCharacteristic
    rw [finiteWeilCanonicalMixture_midpoint_edge_complex_pairing]
    congr 1
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      congr 1
      congr 1
      dsimp [f]
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      congr 1
      congr 1
      dsimp [f]
      push_cast
      ring
  have hid : finiteWeilCanonicalMidpointCharacteristic r k u - E = ((L - E) + (R - E)) / 2 := by
    rw [hM]
    ring
  change ‖finiteWeilCanonicalMidpointCharacteristic r k u - E‖ ≤ |u| / 2
  rw [hid, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have htri := norm_add_le (L - E) (R - E)
  linarith only [htri, hL, hR]

theorem tendsto_finiteWeilCanonicalEdgeCharacteristic_gaussian (t : ℕ → ℕ) (α : ℝ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeCharacteristic r (2 * (r + 1) ^ 2 + t r)
      (α / Real.sqrt ((r + 1 : ℕ) : ℝ))) atTop (𝓝 ((Real.exp (-(α ^ 2 / 8)) : ℝ) : ℂ)) := by
  apply (tendsto_finiteWeilCanonicalMidpointCharacteristic_gaussian t α).congr_dist
  apply squeeze_zero (g := fun r : ℕ => (|α| / 2) * (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
    (fun r => dist_nonneg)
  · intro r
    rw [dist_eq_norm]
    calc
      _ ≤ |α / Real.sqrt ((r + 1 : ℕ) : ℝ)| / 2 :=
        finiteWeilCanonicalEdgeCharacteristic_midpoint_bound r _ _
      _ = _ := by
        rw [abs_div, abs_of_pos (show 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) by positivity)]
        ring
  · simpa only [mul_zero] using tendsto_finiteWeil_inverse_sqrt_succ.const_mul (|α| / 2)

end RHTower
