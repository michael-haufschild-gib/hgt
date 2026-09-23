/-
# Closed-form sectors of the critical curve: first two-sided bounds on `ρ(arg b)`

Before any grid, two explicit regions bound the viability set
`𝒱 = {b : K_b ∩ D̄(0,1) = ∅}` inside the dichotomy ring `2 < ‖b‖ ≤ 2+√2`:

* **Viable sector** (`viable_sector_ring`): on the ring `xStar ‖b‖ ≤ 121/50`, so the two-step
  chain criterion becomes the RATIONAL condition `121/50 + 2‖b‖ + 1 < ‖b‖·‖b+1‖`; in
  coordinates, `‖b+1‖² = ‖b‖² + 2·Re b + 1` makes this an explicit region in `(‖b‖, Re b)`.
  At `‖b‖ = 3` it gives: `Re b ≥ −3/50` suffices (`viable_modulus_three`) — the viable sector
  reaches past `arg b = 90°`.

* **Obstructed region, exact `s`-parameterization** (`obstructed_of_s`): with `b = (1−s²)/4`
  the P1 witness condition is EXACTLY the Cassini-type inequality `‖s−3‖·‖s+1‖ ≤ 4` — no
  square-root estimates at all.  The real segment `s ∈ [3, 1+2√2]` recovers the negative-ray
  obstruction interval; complex `s` sweeps the full P1 lobe around `arg b = π`.
-/
import GaloisForLFunctions.U0.U0DiskEscape
import GaloisForLFunctions.U0.U0ObstructionPatterns
import GaloisForLFunctions.U0.U0WindowObstruction

open Complex Set Bottcher U0MonotoneEscape

namespace U0CurveSectors

/-- On the dichotomy ring the escape fixed point is uniformly below `121/50`. -/
theorem xStar_le_ring {B : ℝ} (hB : B ≤ 2 + Real.sqrt 2) : xStar B ≤ 121 / 50 := by
  have hs2 : Real.sqrt 2 ≤ 283 / 200 := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (283 / 200) ^ (2 : ℕ) by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 283 / 200)] at h
  have harg : 1 + 4 * B ≤ (96 / 25 : ℝ) ^ (2 : ℕ) := by
    have : B ≤ 2 + 283 / 200 := le_trans hB (by linarith)
    nlinarith
  have hsq : Real.sqrt (1 + 4 * B) ≤ 96 / 25 := by
    have h := Real.sqrt_le_sqrt harg
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 96 / 25)] at h
  rw [xStar]
  linarith

/-- **The viable sector on the ring**, rational form: two-step escape whenever
`121/50 + 2‖b‖ + 1 < ‖b‖·‖b+1‖`. -/
theorem viable_sector_ring {b : ℂ} (hb2 : 2 < ‖b‖) (hring : ‖b‖ ≤ 2 + Real.sqrt 2)
    (hcond : 121 / 50 + (2 * ‖b‖ + 1) < ‖b‖ * ‖b + 1‖) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  refine U0DiskEscape.viable_of_one_chain hb2 ?_
  have := xStar_le_ring hring
  linarith

/-- The viable sector in `(‖b‖, Re b)` coordinates, via `‖b+1‖² = ‖b‖² + 2·Re b + 1`. -/
theorem viable_sector_ring_re {b : ℂ} (hb2 : 2 < ‖b‖) (hring : ‖b‖ ≤ 2 + Real.sqrt 2)
    (hcond : (121 / 50 + (2 * ‖b‖ + 1)) ^ (2 : ℕ) < ‖b‖ ^ (2 : ℕ) * (‖b‖ ^ (2 : ℕ) + 2 * b.re + 1)) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  refine viable_sector_ring hb2 hring ?_
  have hnorm1 : ‖b + 1‖ ^ (2 : ℕ) = ‖b‖ ^ (2 : ℕ) + 2 * b.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hcond' : (121 / 50 + (2 * ‖b‖ + 1)) ^ (2 : ℕ) < ‖b‖ ^ (2 : ℕ) * ‖b + 1‖ ^ (2 : ℕ) := by
    rw [hnorm1]; exact hcond
  by_contra hcon
  push Not at hcon
  nlinarith [hcond',
    mul_self_le_mul_self (mul_nonneg (norm_nonneg b) (norm_nonneg (b + 1))) hcon]

/-- **Viability at modulus 3 past `arg = 90°`**: any `‖b‖ = 3` with `Re b ≥ −3/50` is viable. -/
theorem viable_modulus_three {b : ℂ} (hmod : ‖b‖ = 3) (hre : -(3 / 50) ≤ b.re) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  refine viable_sector_ring_re (by rw [hmod]; norm_num) (by rw [hmod]; linarith) ?_
  rw [hmod]
  nlinarith [hre]

/-- **The P1 obstructed region, exact `s`-parameterization**: for every complex `s` with
`‖s−3‖·‖s+1‖ ≤ 4`, the parameter `b = (1−s²)/4` has a filled-Julia point in the closed unit
disk.  (The identity `(1+s)/2 + (1−s²)/4 = −(s−3)(s+1)/4` makes the P1 condition exact —
Cassini-type region, no square-root estimates.) -/
theorem obstructed_of_s {s : ℂ} (hcond : ‖s - 3‖ * ‖s + 1‖ ≤ 4) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia ((1 - s ^ (2 : ℕ)) / 4) := by
  refine U0ObstructionPatterns.filledJulia_meets_unit_disk_P1 (s := s) (by ring) ?_
  have hid : (1 + s) / 2 + (1 - s ^ (2 : ℕ)) / 4 = -((s - 3) * (s + 1)) / 4 := by ring
  rw [hid]
  rw [norm_div, norm_neg, norm_mul, Complex.norm_ofNat]
  linarith

/-- The real-`s` segment recovers the negative-ray obstruction: for real `s ∈ [3, 1+2√2]` the
parameter `b = (1−s²)/4` lies on the negative ray with `‖b‖ ∈ [2, 2+√2]`, obstructed. -/
theorem obstructed_real_segment {s : ℝ} (h3 : 3 ≤ s) (hup : s ≤ 1 + 2 * Real.sqrt 2) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia ((1 - (s : ℂ) ^ (2 : ℕ)) / 4) := by
  refine obstructed_of_s ?_
  have hs2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have h1 : ((s : ℂ) - 3) = ((s - 3 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((s : ℂ) + 1) = ((s + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  nlinarith [hs2, Real.sqrt_nonneg 2]

end U0CurveSectors

namespace U0CurveSectors

/-- **Viability above the sharp threshold, every direction**: for `‖b‖ > 2+√2` the closed unit
disk escapes — one quadratic step clears the fixed point (`xStar ‖b‖ < ‖b‖ − 1`), monotone
escape does the rest.  Geometrically: `ρ(θ) ≤ 2+√2` for EVERY direction `θ`. -/
theorem viable_of_gt_sharp {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  refine U0DiskEscape.viable_of_sharp (by linarith) ?_
  have := U0MonotoneEscape.xStar_lt_of_sharp hb
  linarith

/-- **`ρ(π) = 2+√2`, two-sided**: every parameter of modulus `> 2+√2` is viable (any
direction), and AT modulus `2+√2` the parameter `−(2+√2)` is obstructed — the critical curve
attains its maximum exactly at the negative ray, at exactly the window threshold. -/
theorem rho_pi_pinned :
    (∀ b : ℂ, 2 + Real.sqrt 2 < ‖b‖ → ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) ∧
    (∃ b : ℂ, ‖b‖ = 2 + Real.sqrt 2 ∧ ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b) := by
  refine ⟨fun b hb => viable_of_gt_sharp hb, ⟨(((-2 - Real.sqrt 2 : ℝ)) : ℂ), ?_, ?_⟩⟩
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (show (-2 - Real.sqrt 2 : ℝ) < 0 by linarith [Real.sqrt_nonneg 2])]
    ring
  · exact U0WindowObstruction.filledJulia_meets_unit_disk
      (by linarith [Real.sqrt_nonneg 2]) (le_refl _)

/-- The real negative-ray corollary: every real `b < −(2+√2)` is viable. -/
theorem negative_ray_viable {b : ℝ} (hb : b < -(2 + Real.sqrt 2)) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia ((b : ℝ) : ℂ) := by
  refine viable_of_gt_sharp ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (show b < 0 by linarith [Real.sqrt_nonneg 2])]
  linarith

end U0CurveSectors
