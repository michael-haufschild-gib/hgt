/-
# The window obstruction: small parameters whose Julia set meets the unit disk

The window route (a Böttcher branch analytic on a disk containing the unit circle) requires the
filled Julia set to avoid the closed unit disk.  This file proves that near the boundary of the
escape regime the requirement FAILS at explicit parameters: for every real `b ∈ [−2−√2, −2)` the
point `x₀ = √(−β−b)` (with `β = (1+√(1−4b))/2` the repelling fixed point) satisfies

  `x₀ ≤ 1`,  `f_b(x₀) = −β`,  `f_b(−β) = β`,  `f_b(β) = β`

— a finite, hence bounded, orbit: `x₀ ∈ K_b` with `‖x₀‖ ≤ 1`.  Consequences:

* the exterior geometry `filledJulia_exterior` (valid from `‖b‖ ≥ 4`) is NOT extendable to all
  `‖b‖ > 2` — parameters of modulus in `(2, 2+√2]` can have Julia points inside the unit disk;
* no branch of `φ_b` is analytic on any neighborhood of the unit circle at these parameters:
  extending `u0_phiB_independence` below `‖b‖ = 2+√2` requires DIRECTION-DEPENDENT hypotheses
  (the obstruction is real for `b` near the negative axis), not smaller constants.
-/
import GaloisForLFunctions.Bottcher.Dynamics

open Complex Set Bottcher

namespace U0WindowObstruction

/-- **The filled Julia set meets the closed unit disk** for every real `b ∈ [−2−√2, −2)`:
the explicit preimage `√(−β−b)` of the reflected fixed point `−β` lies in `K_b` at modulus
`≤ 1`. -/
theorem filledJulia_meets_unit_disk {b : ℝ} (hb2 : b ≤ -2) (hb : -2 - Real.sqrt 2 ≤ b) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (b : ℂ) := by
  set s : ℝ := Real.sqrt (1 - 4 * b) with hs
  have hs0 : (0 : ℝ) ≤ 1 - 4 * b := by linarith
  have hssq : s ^ (2 : ℕ) = 1 - 4 * b := Real.sq_sqrt hs0
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  set β : ℝ := (1 + s) / 2 with hβ
  have hβfix : β ^ (2 : ℕ) + b = β := by
    rw [hβ]
    linear_combination hssq / 4
  -- x₀² = −β − b ≥ 0
  have hsle : s ≤ -2 * b - 1 := by
    by_contra hcon
    push Not at hcon
    have h3 : 0 < (s - (-2 * b - 1)) * (s + (-2 * b - 1)) :=
      mul_pos (by linarith) (by linarith [hsnn, hb2])
    have h4 : (s - (-2 * b - 1)) * (s + (-2 * b - 1)) = -4 * (b ^ (2 : ℕ) + 2 * b) := by
      linear_combination hssq
    have h5 : 0 ≤ b ^ (2 : ℕ) + 2 * b := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ -b by linarith)
        (show (0 : ℝ) ≤ -(b + 2) by linarith)]
    nlinarith [h3, h4, h5]
  have hx0nn : (0 : ℝ) ≤ -β - b := by
    rw [hβ]
    linarith [hsle]
  set x₀ : ℝ := Real.sqrt (-β - b) with hx₀def
  have hx₀sq : x₀ ^ (2 : ℕ) = -β - b := Real.sq_sqrt hx0nn
  have hx₀nn : 0 ≤ x₀ := Real.sqrt_nonneg _
  -- x₀ ≤ 1 from b ≥ −2−√2
  have hquad : b ^ (2 : ℕ) + 4 * b + 2 ≤ 0 := by
    have h2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h2, hb, hb2,
      mul_nonneg (show (0 : ℝ) ≤ -(b + 2) by linarith)
        (show (0 : ℝ) ≤ Real.sqrt 2 + (b + 2) by linarith [hb]),
      mul_nonneg (Real.sqrt_nonneg 2)
        (show (0 : ℝ) ≤ Real.sqrt 2 + (b + 2) by linarith [hb])]
  have hsge : -2 * b - 3 ≤ s := by
    by_contra hcon
    push Not at hcon
    have h3 : 0 < ((-2 * b - 3) - s) * ((-2 * b - 3) + s) :=
      mul_pos (by linarith) (by linarith [hsnn, hb2])
    have h4 : ((-2 * b - 3) - s) * ((-2 * b - 3) + s) = 4 * (b ^ (2 : ℕ) + 4 * b + 2) := by
      linear_combination -hssq
    nlinarith [h3, h4, hquad]
  have hx0le : -β - b ≤ 1 := by
    rw [hβ]
    linarith [hsge]
  have hx₀le1 : x₀ ≤ 1 := by
    rw [hx₀def]
    calc Real.sqrt (-β - b) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hx0le
      _ = 1 := Real.sqrt_one
  -- the three orbit steps, at the complex level
  have hfb : quadratic (b : ℂ) ((β : ℝ) : ℂ) = ((β : ℝ) : ℂ) := by
    show (((β : ℝ) : ℂ)) ^ (2 : ℕ) + ((b : ℝ) : ℂ) = ((β : ℝ) : ℂ)
    calc (((β : ℝ) : ℂ)) ^ (2 : ℕ) + ((b : ℝ) : ℂ) = (((β ^ (2 : ℕ) + b : ℝ)) : ℂ) := by push_cast; ring
      _ = ((β : ℝ) : ℂ) := by rw [hβfix]
  have hfnb : quadratic (b : ℂ) (-((β : ℝ) : ℂ)) = ((β : ℝ) : ℂ) := by
    show (-((β : ℝ) : ℂ)) ^ (2 : ℕ) + ((b : ℝ) : ℂ) = ((β : ℝ) : ℂ)
    calc (-((β : ℝ) : ℂ)) ^ (2 : ℕ) + ((b : ℝ) : ℂ) = (((β ^ (2 : ℕ) + b : ℝ)) : ℂ) := by push_cast; ring
      _ = ((β : ℝ) : ℂ) := by rw [hβfix]
  have hfx : quadratic (b : ℂ) ((x₀ : ℝ) : ℂ) = -((β : ℝ) : ℂ) := by
    show (((x₀ : ℝ) : ℂ)) ^ (2 : ℕ) + ((b : ℝ) : ℂ) = -((β : ℝ) : ℂ)
    have hr : x₀ ^ (2 : ℕ) + b = -β := by
      rw [hx₀sq]
      ring
    calc (((x₀ : ℝ) : ℂ)) ^ (2 : ℕ) + ((b : ℝ) : ℂ) = (((x₀ ^ (2 : ℕ) + b : ℝ)) : ℂ) := by push_cast; ring
      _ = ((-β : ℝ) : ℂ) := by rw [hr]
      _ = -((β : ℝ) : ℂ) := by push_cast; ring
  -- the orbit is contained in a three-point set
  have horbit : ∀ n : ℕ, (quadratic (b : ℂ))^[n] ((x₀ : ℝ) : ℂ)
      ∈ ({((x₀ : ℝ) : ℂ), -((β : ℝ) : ℂ), ((β : ℝ) : ℂ)} : Set ℂ) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
      rcases ih with h | h | h
      · rw [h, hfx]
        tauto
      · rw [h, hfnb]
        tauto
      · rw [h, hfb]
        tauto
  refine ⟨((x₀ : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀nn]
    exact hx₀le1
  · rw [mem_filledJulia_iff]
    have hfin : ({((x₀ : ℝ) : ℂ), -((β : ℝ) : ℂ), ((β : ℝ) : ℂ)} : Set ℂ).Finite :=
      Set.toFinite _
    refine hfin.isBounded.subset ?_
    rw [Set.range_subset_iff]
    exact horbit

/-- The explicit instance `b = −5/2` (`‖b‖ = 5/2 ∈ (2, 2+√2)`). -/
theorem filledJulia_meets_unit_disk_example :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia ((-5 / 2 : ℝ) : ℂ) := by
  refine filledJulia_meets_unit_disk (by norm_num) ?_
  have h2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, h2]

/-- **Sharpness of the exterior geometry**: the conclusion of `filledJulia_exterior`
(`K_b ⊆ {|z| > 1}`, valid for `‖b‖ ≥ 4`) FAILS at a parameter of modulus `5/2` — the window
route cannot cover all of `2 < ‖b‖`. -/
theorem filledJulia_exterior_fails_at_small :
    ∃ b : ℂ, ‖b‖ = 5 / 2 ∧ ∃ z ∈ filledJulia b, ‖z‖ ≤ 1 := by
  obtain ⟨x, hx1, hxK⟩ := filledJulia_meets_unit_disk_example
  refine ⟨((-5 / 2 : ℝ) : ℂ), ?_, x, hxK, hx1⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  norm_num

end U0WindowObstruction
