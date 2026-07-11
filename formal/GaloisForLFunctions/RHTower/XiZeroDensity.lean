/-
The zero-density bound for the completed zeta ξ: the number of ξ-zeros in a disc of radius `r`
grows at most like `r · log r`.

The Jensen bound `xi_zeroCount_disc_le_logModulus` caps the interior zero count of a disc by the
boundary log-modulus.  Feeding it the unconditional order-≤1 growth envelope `xi_growth_order_le_one` (on the
sphere of radius `2r` centred at the pole-free anchor `s = 2`, where `‖s‖ ≤ 2 + 2r`) turns the log of
the boundary modulus into an `O(r log r)` quantity, while the radius ratio `R/r = 2` contributes the
fixed positive factor `log 2`.  The result is the counting-function growth `N(r) = O(r log r)` — the
convergence-exponent input a Weierstrass/Hadamard product over the ξ-zeros consumes.
-/
import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import GaloisForLFunctions.RHTower.LittlewoodXi
import GaloisForLFunctions.RHTower.RiemannTower

open Complex Metric

namespace RHTower

/-- **The ξ zero-counting function grows at most like `r log r`.**  For every `r ≥ 1`, the total
ξ-zero multiplicity in the closed disc `B(2, r)` is bounded by `C·(1+r)·log(2+r)` for a fixed `C`.
Proof: Jensen's inequality (`xi_zeroCount_disc_le_logModulus`) at centre `2` (`xi 2 ≠ 0`), inner radius
`r`, outer radius `2r`, with the boundary modulus `M` bounded by the unconditional order-one envelope
`xi_growth_order_le_one` (as `‖z‖ ≤ 2+2r` on the sphere); the ratio `R/r = 2` gives the fixed factor
`log 2 > 0`. -/
theorem xi_zeroCount_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (↑(∑ᶠ u, (MeromorphicOn.divisor xi (Metric.closedBall (2 : ℂ) r)) u) : ℝ)
        ≤ C * (1 + r) * Real.log (2 + r) := by
  obtain ⟨C₀, hC₀, hgrow⟩ := xi_growth_order_le_one
  have hL2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(6 * C₀ + |Real.log ‖xi 2‖| + Real.log 2) / Real.log 2, by positivity, ?_⟩
  intro r hr1
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrabs : |r| = r := abs_of_pos hr0
  set R : ℝ := 2 * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRabs : |R| = R := abs_of_pos hRpos
  set M : ℝ := Real.exp (C₀ * (1 + (2 + 2 * r)) * Real.log (2 + (2 + 2 * r))) with hMdef
  have hMnn : 0 ≤ C₀ * (1 + (2 + 2 * r)) * Real.log (2 + (2 + 2 * r)) := by
    apply mul_nonneg (mul_nonneg hC₀.le (by linarith))
    exact Real.log_nonneg (by linarith)
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Real.one_le_exp hMnn
  -- Boundary modulus bound from the unconditional order-one envelope.
  have hbound : ∀ z ∈ sphere (2 : ℂ) |R|, ‖xi z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hznorm : ‖z‖ ≤ 2 + 2 * r := by
      have htri : ‖z‖ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := by
        have h := norm_add_le (z - 2) 2; simpa using h
      rw [hz, hRabs, hRdef] at htri
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2] at htri; linarith
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    refine le_trans (hgrow z) ?_
    rw [hMdef]
    apply Real.exp_le_exp.mpr
    have hfac1 : C₀ * (1 + ‖z‖) ≤ C₀ * (1 + (2 + 2 * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have hfac2 : Real.log (2 + ‖z‖) ≤ Real.log (2 + (2 + 2 * r)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlognn : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
    exact mul_le_mul hfac1 hfac2 hlognn (by positivity)
  -- Jensen's zero-count bound, normalized.
  have hrR : r < R := by rw [hRdef]; linarith
  have hK0 : (↑(∑ᶠ u, (MeromorphicOn.divisor xi (closedBall (2 : ℂ) |r|)) u) : ℝ)
      ≤ ↑(∑ᶠ u, (MeromorphicOn.divisor xi (closedBall (2 : ℂ) |r|)) u) := le_refl _
  have hcount := xi_zeroCount_disc_le_logModulus hr0 hrR hM1 xi_two_ne_zero hbound hK0
  rw [hrabs] at hcount
  have hRr : R / r = 2 := by rw [hRdef]; field_simp
  have h1eq : (1 : ℝ) + (2 + 2 * r) = 3 + 2 * r := by ring
  have h2eq : (2 : ℝ) + (2 + 2 * r) = 4 + 2 * r := by ring
  rw [hRr, hMdef, Real.log_exp, h1eq, h2eq] at hcount
  set N : ℝ := (↑(∑ᶠ u, (MeromorphicOn.divisor xi (closedBall (2 : ℂ) r)) u) : ℝ) with hNdef
  -- Two envelope inequalities.
  have hP : (1 : ℝ) ≤ (1 + r) * Real.log (2 + r) := by
    have hlog1 : (1 : ℝ) ≤ Real.log (2 + r) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      nlinarith [Real.exp_one_lt_d9, hr1]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (1 + r) * Real.log (2 + r) := mul_le_mul (by linarith) hlog1 zero_le_one (by linarith)
  have hQ : (3 + 2 * r) * Real.log (4 + 2 * r) ≤ 6 * (1 + r) * Real.log (2 + r) := by
    have hlog4 : Real.log (4 + 2 * r) ≤ 2 * Real.log (2 + r) := by
      have he : (4 : ℝ) + 2 * r = 2 * (2 + r) := by ring
      rw [he, Real.log_mul (by norm_num) (by linarith)]
      have : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have h3 : (3 : ℝ) + 2 * r ≤ 3 * (1 + r) := by linarith
    have hlognn : 0 ≤ Real.log (4 + 2 * r) := Real.log_nonneg (by linarith)
    calc (3 + 2 * r) * Real.log (4 + 2 * r)
        ≤ (3 * (1 + r)) * (2 * Real.log (2 + r)) := by
          apply mul_le_mul h3 hlog4 hlognn (by linarith)
      _ = 6 * (1 + r) * Real.log (2 + r) := by ring
  have habs : -Real.log ‖xi 2‖ ≤ |Real.log ‖xi 2‖| * ((1 + r) * Real.log (2 + r)) := by
    calc -Real.log ‖xi 2‖ ≤ |Real.log ‖xi 2‖| := neg_le_abs _
      _ = |Real.log ‖xi 2‖| * 1 := by ring
      _ ≤ |Real.log ‖xi 2‖| * ((1 + r) * Real.log (2 + r)) :=
          mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  have hslack : 0 ≤ Real.log 2 * ((1 + r) * Real.log (2 + r)) :=
    mul_nonneg hL2pos.le (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hL2pos]
  nlinarith [hcount, mul_le_mul_of_nonneg_left hQ hC₀.le, habs, hslack]

end RHTower
