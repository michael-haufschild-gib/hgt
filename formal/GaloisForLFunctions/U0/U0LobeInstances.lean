/-
# Mid-angle obstruction instances — the obstructed set is multi-lobed

Exact-rational obstruction witnesses at mid-angles (`arg b` away from `π`), certifying that the
obstructed set in the parameter plane has structure beyond the fixed-point (P1) lobe around
`arg b = π`:

* `lobe_obstructed_112` — a genuine **period-3** obstruction at `arg b ≈ 111.8°` via the general
  preperiodic-entry theorem (`U0ObstructionPatterns.filledJulia_meets_unit_disk_preperiodic`,
  `k=0, n=3`).  The 3-cycle is `⟨-1/4,3/4⟩ → ⟨-3/4,1/4⟩ → ⟨1/4,1/4⟩` of `z² + b`, an exact
  Gaussian-rational instance of the period-3 parameterization `b = -(σ²+σ+2)` (trace `σ`), whose
  rational points come from the genus-0 dynatomic curve `X₁(3)`
  (`computations/p3_lobe_recon/`).

* `lobe_obstructed_ring_127` — a **2-cycle** obstruction INSIDE the window ring
  (`‖b‖ = 11/5 ∈ (2, 2+√2)`) at `arg b ≈ 126.9°`, from a Pythagorean parameter
  `γ = ⟨-8/5,4/5⟩` (`‖γ+1‖ = 1`).  Shows the obstructed set reaches mid-angles within the sharp
  ring, not only near `arg b = π`.

* `lobe_radial_bracket` — the RADIAL companion of the angular `critical_curve_bracket`: on a fixed
  ray (`arg b ≈ 126.9°`) the parameter is obstructed at `‖b‖ = 11/5` and viable at `‖b‖ = 22/5`
  (past the sharp threshold, `U0CurveSectors.viable_of_gt_sharp`), bracketing the boundary of the
  viability set `𝒱` across the ray.

The exact-rational certificate for the DEEP mid-angle lobe (e.g. `‖b‖ ≈ 2.2` at `arg b ≈ 90°`,
numerically obstructed but not by P1/P2 — the witness there is a deep preimage of a 3-cycle) is a
located open sub-problem: direct 3-cycle entry (`‖γ − b‖ ≤ 1`) forces `‖b‖` small, so the ring's
interior lobe needs Gaussian-rational deep-preimage points.  See the card `period3-lobe-instances`.
-/
import GaloisForLFunctions.U0.U0ObstructionPatterns
import GaloisForLFunctions.U0.U0CurveSectors

open Complex Set Bottcher

namespace U0LobeInstances

/-- Norm bound from the squared value: `‖z‖² ≤ 1` gives `‖z‖ ≤ 1`. -/
private theorem norm_le_one_of_normSq_le {z : ℂ} (h : ‖z‖ ^ (2 : ℕ) ≤ 1) : ‖z‖ ≤ 1 := by
  nlinarith [norm_nonneg z, h]

/-- **Period-3 obstruction at a mid-angle** (`arg b ≈ 111.8°`, `‖b‖ = √29/8`).  The exact
Gaussian-rational 3-cycle `⟨-1/4,3/4⟩ → ⟨-3/4,1/4⟩ → ⟨1/4,1/4⟩` of `z² + (-1/4 + 5i/8)` puts a
point of the closed unit disk into `K_b` — a genuine period-3 mechanism, distinct from the
fixed-point (P1) and 2-cycle (P2) lobes. -/
theorem lobe_obstructed_112 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-1/4, 5/8⟩ : ℂ) := by
  have s1 : quadratic (⟨-1/4, 5/8⟩ : ℂ) (⟨-1/4, 3/4⟩ : ℂ) = (⟨-3/4, 1/4⟩ : ℂ) := by
    rw [quadratic_apply, Complex.ext_iff]
    constructor <;> simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im] <;> norm_num
  have s2 : quadratic (⟨-1/4, 5/8⟩ : ℂ) (⟨-3/4, 1/4⟩ : ℂ) = (⟨1/4, 1/4⟩ : ℂ) := by
    rw [quadratic_apply, Complex.ext_iff]
    constructor <;> simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im] <;> norm_num
  have s3 : quadratic (⟨-1/4, 5/8⟩ : ℂ) (⟨1/4, 1/4⟩ : ℂ) = (⟨-1/4, 3/4⟩ : ℂ) := by
    rw [quadratic_apply, Complex.ext_iff]
    constructor <;> simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im] <;> norm_num
  refine U0ObstructionPatterns.filledJulia_meets_unit_disk_preperiodic
    (y := (⟨-1/4, 3/4⟩ : ℂ)) (k := 0) (n := 3) (by norm_num) ?_ ?_
  · show quadratic (⟨-1/4, 5/8⟩ : ℂ) (quadratic (⟨-1/4, 5/8⟩ : ℂ)
        (quadratic (⟨-1/4, 5/8⟩ : ℂ) (⟨-1/4, 3/4⟩ : ℂ))) = (⟨-1/4, 3/4⟩ : ℂ)
    rw [s1, s2, s3]
  · have hd : (⟨-1/4, 3/4⟩ : ℂ) - (⟨-1/4, 5/8⟩ : ℂ) = (⟨0, 1/8⟩ : ℂ) := by
      rw [Complex.ext_iff]; constructor <;> norm_num
    rw [hd]
    refine norm_le_one_of_normSq_le ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num

/-- **2-cycle obstruction inside the window ring** (`‖b‖ = 11/5 ∈ (2, 2+√2)`, `arg b ≈ 126.9°`).
Pythagorean parameter `γ = ⟨-8/5,4/5⟩` with `‖γ+1‖ = 1`, so `‖γ − b‖ = ‖(γ+1)²‖ = 1`; the
obstructed set reaches mid-angles within the sharp ring. -/
theorem lobe_obstructed_ring_127 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-33/25, 44/25⟩ : ℂ) := by
  refine U0ObstructionPatterns.filledJulia_meets_unit_disk_P2 (γ := (⟨-8/5, 4/5⟩ : ℂ)) ?_ ?_
  · rw [Complex.ext_iff]
    constructor <;> simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] <;> norm_num
  · have hd : (⟨-8/5, 4/5⟩ : ℂ) - (⟨-33/25, 44/25⟩ : ℂ) = (⟨-7/25, -24/25⟩ : ℂ) := by
      rw [Complex.ext_iff]; constructor <;> norm_num
    rw [hd]
    refine norm_le_one_of_normSq_le ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num

/-- **Radial bracket of the viability boundary** on the ray `arg b ≈ 126.9°`: the parameter is
obstructed at `‖b‖ = 11/5` (2-cycle) and viable at `‖b‖ = 22/5` (past the sharp threshold `2+√2`,
every direction).  The two parameters are colinear (`bv = 2·bo`), so this brackets `∂𝒱` across a
single ray — the radial companion of the angular `critical_curve_bracket`. -/
theorem lobe_radial_bracket :
    ∃ bo bv : ℂ,
      ‖bo‖ ^ (2 : ℕ) = 121 / 25 ∧ ‖bv‖ ^ (2 : ℕ) = 484 / 25 ∧
      bv.im * bo.re = bv.re * bo.im ∧
      (∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia bo) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia bv) := by
  refine ⟨(⟨-33/25, 44/25⟩ : ℂ), (⟨-66/25, 88/25⟩ : ℂ), ?_, ?_, ?_, lobe_obstructed_ring_127, ?_⟩
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num
  · show (88 / 25 : ℝ) * (-33 / 25) = (-66 / 25) * (44 / 25); norm_num
  · refine U0CurveSectors.viable_of_gt_sharp ?_
    have hsq : ‖(⟨-66/25, 88/25⟩ : ℂ)‖ ^ (2 : ℕ) = 484 / 25 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num
    have hs2 : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    nlinarith [hsq, hs2, Real.sqrt_nonneg 2, norm_nonneg (⟨-66/25, 88/25⟩ : ℂ)]

end U0LobeInstances
