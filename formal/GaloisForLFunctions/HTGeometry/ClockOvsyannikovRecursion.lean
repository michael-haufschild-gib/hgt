import GaloisForLFunctions.HTGeometry.ClockOvsyannikovInduction

/-!
# The Ovsyannikov estimate, as a recursion on bounds

The iteration that solves the clock equation in the analytic scale produces, at stage `m`, a state
whose norm at radius `ρ` is controlled by the norm at a larger radius `σ`, with the loss
`K/(σ-ρ)²` and the gain of a double integration. This file turns that single hypothesis into the
closed bound

`N m ρ x y ≤ Kᵐ m^{2m} xᵐ yᵐ / ((m!)² (ρ₀-ρ)^{2m})`,

by induction on `m`, taking the intermediate radius `σ = ρ + (ρ₀-ρ)/(m+1)` at every stage.

The statement is purely scalar: `N m ρ x y` stands for any nonnegative bound on the `m`-th stage at
radius `ρ` over a rectangle of side lengths `x` and `y`, and the only hypothesis is the one step.
So it applies verbatim to either form of the scale, and the concrete construction has only to
discharge the step — which is the double integral of the operator estimate.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Ovsyannikov recursion.** One step with a loss `K/(σ-ρ)²` and a double integration forces
the closed bound at every stage. -/
theorem ovsyannikov_induction {ρ₀ K : ℝ} (hK : 0 ≤ K) (N : ℕ → ℝ → ℝ → ℝ → ℝ)
    (hN0 : ∀ ρ x y : ℝ, N 0 ρ x y ≤ 1)
    (hstep : ∀ (m : ℕ) (ρ σ x y c : ℝ), 0 ≤ c → 0 ≤ x → 0 ≤ y → ρ < σ → σ ≤ ρ₀ →
      (∀ s t : ℝ, 0 ≤ s → s ≤ x → 0 ≤ t → t ≤ y → N m σ s t ≤ c * s ^ m * t ^ m) →
      N (m + 1) ρ x y
        ≤ K / (σ - ρ) ^ 2 * c * (x ^ (m + 1) * y ^ (m + 1) / ((m : ℝ) + 1) ^ 2))
    (m : ℕ) :
    ∀ ρ x y : ℝ, ρ < ρ₀ → 0 ≤ x → 0 ≤ y →
      N m ρ x y ≤ K ^ m * (m : ℝ) ^ (2 * m) * (x ^ m * y ^ m)
        / ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m)) := by
  induction m with
  | zero =>
    intro ρ x y _ _ _
    simpa using hN0 ρ x y
  | succ m ih =>
    intro ρ x y hρ hx hy
    have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hfrac : (0 : ℝ) < (ρ₀ - ρ) / ((m : ℝ) + 1) := by positivity
    set σ : ℝ := ρ + (ρ₀ - ρ) / ((m : ℝ) + 1) with hσdef
    have hρσ : ρ < σ := by rw [hσdef]; linarith
    have hle1 : (ρ₀ - ρ) / ((m : ℝ) + 1) ≤ ρ₀ - ρ := by
      rw [div_le_iff₀ hm1]
      nlinarith [hG]
    have hσρ₀ : σ ≤ ρ₀ := by rw [hσdef]; linarith
    have hgap : σ - ρ = (ρ₀ - ρ) / ((m : ℝ) + 1) := by rw [hσdef]; ring
    have hrem : ρ₀ - σ = (ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1) := by
      rw [hσdef]
      field_simp
      ring
    set c : ℝ := K ^ m * (m : ℝ) ^ (2 * m)
      / ((m.factorial : ℝ) ^ 2 * (ρ₀ - σ) ^ (2 * m)) with hcdef
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hc0 : 0 ≤ c := by
      rw [hcdef]
      positivity
    have hIH : ∀ s t : ℝ, 0 ≤ s → s ≤ x → 0 ≤ t → t ≤ y → N m σ s t ≤ c * s ^ m * t ^ m := by
      intro s t hs _ ht _
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have h0 := hN0 σ s t
        have hc1 : c = 1 := by
          rw [hcdef]
          norm_num
        rw [hc1]
        simpa using h0
      · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hσlt : σ < ρ₀ := by
          rw [hσdef]
          have : (ρ₀ - ρ) / ((m : ℝ) + 1) < ρ₀ - ρ := by
            rw [div_lt_iff₀ hm1]
            nlinarith [hG, hmpos]
          linarith
        have hbase := ih σ s t hσlt hs ht
        calc N m σ s t
            ≤ K ^ m * (m : ℝ) ^ (2 * m) * (s ^ m * t ^ m)
              / ((m.factorial : ℝ) ^ 2 * (ρ₀ - σ) ^ (2 * m)) := hbase
          _ = c * s ^ m * t ^ m := by
              rw [hcdef]
              have hden : ((m.factorial : ℝ) ^ 2 * (ρ₀ - σ) ^ (2 * m)) ≠ 0 := by
                have : (0 : ℝ) < ρ₀ - σ := by
                  rw [hrem]
                  positivity
                positivity
              field_simp
    have hstepped := hstep m ρ σ x y c hc0 hx hy hρσ hσρ₀ hIH
    have hloss : K / (σ - ρ) ^ 2 = K * ((m : ℝ) + 1) ^ 2 / (ρ₀ - ρ) ^ 2 := by
      rw [hgap]
      field_simp
    have hcval : c = K ^ m * ((m : ℝ) + 1) ^ (2 * m)
        / ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m)) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [hcdef]
        norm_num
      · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hd1 : (0 : ℝ) < ((ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m) := by positivity
        have hd2 : (0 : ℝ) < (ρ₀ - ρ) ^ (2 * m) := by positivity
        have hratio := sq_pow_ratio_intermediate hG m
        rw [div_eq_div_iff (ne_of_gt hd1) (ne_of_gt hd2)] at hratio
        rw [hcdef, hrem, div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (K ^ m * (m.factorial : ℝ) ^ 2) * hratio
    rw [hloss, hcval] at hstepped
    have hident := ovsyannikov_step_identity (K := K) (G := ρ₀ - ρ) (x := x) (y := y) hG m
    rw [hident] at hstepped
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact hstepped

end GaloisForLFunctions.HTGeometry
