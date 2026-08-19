import GaloisForLFunctions.HTGeometry.ShiftRatioExpansion
import GaloisForLFunctions.HTGeometry.GammaMonomialShift
import GaloisForLFunctions.HTGeometry.GammaStirlingTelescopeThreshold

/-!
# The Gamma monomial is bounded along each orbit

In a dominant class the shift ratio satisfies `‖ρ_g(s) − 1‖ ≤ K/‖s‖²`, so the telescoped product
`∏_{j<n} ρ_g(s+j)` is bounded by a constant independent of `n`: the exponents sum to
`K ∑_j ‖s+j‖^{-2}`, and `‖s+j‖² ≥ (‖s‖+j)²/2` on the right half plane.

This is what turns "bounded on one strip" into "bounded on the half plane" for a Gamma-monomial
ratio, and it is the last input of the ratio ladder.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- Iterating the functional equation. -/
theorem gammaMonomial_shift_nat {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) : ∀ n : ℕ,
    gammaMonomial lam g (s + (n : ℂ))
      = (∏ j ∈ Finset.range n, ∏ k, (s + (j : ℂ) + lam k) ^ (g k))
        * gammaMonomial lam g s := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hsn : (∑ j, |(lam j).re|) < (s + (n : ℂ)).re := by
        rw [Complex.add_re, Complex.natCast_re]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hstep := gammaMonomial_shift_of_re lam g hsn
      have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
      rw [hcast, hstep, ih, Finset.prod_range_succ]
      ring

/-- On the right half plane the shifted norms grow at least like `(‖s‖+j)/√2`. -/
theorem two_mul_norm_add_natCast_sq_ge {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    (‖s‖ + (j : ℝ)) ^ 2 ≤ 2 * ‖s + (j : ℂ)‖ ^ 2 := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hsq : ‖s‖ ^ 2 + (j : ℝ) ^ 2 ≤ ‖s + (j : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im]
    nlinarith [hs, hj]
  nlinarith [sq_nonneg (‖s‖ - (j : ℝ)), hsq]


/-- **The telescoped shift ratio is bounded, uniformly in the number of steps.** -/
theorem exists_prod_norm_shiftRatio_le {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ B Rb : ℝ, 0 < B ∧ 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      ∀ n : ℕ, ‖∏ j ∈ Finset.range n, ∏ k, (s + (j : ℂ) + lam k) ^ (g k)‖ ≤ B := by
  obtain ⟨K, Rb₀, hK0, hRb₀, hK⟩ := exists_norm_shiftRatio_sub_one_le lam g hdeg hmom
  refine ⟨Real.exp (4 * K), max Rb₀ 1, Real.exp_pos _, le_max_right _ _, ?_⟩
  intro s hs hsn n
  have hre : 0 < s.re := by
    have hnn : (0 : ℝ) ≤ ∑ j, |(lam j).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hsn
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  have hjre : ∀ j : ℕ, (∑ i, |(lam i).re|) < (s + (j : ℂ)).re := by
    intro j
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hjlam : ∀ (j : ℕ) (k : Fin r), s + (j : ℂ) + lam k ≠ 0 := by
    intro j k hcon
    have := re_pos_of_gt_sum_abs lam (hjre j) k
    rw [hcon] at this
    simp at this
  have hjnorm : ∀ j : ℕ, Rb₀ ≤ ‖s + (j : ℂ)‖ := by
    intro j
    exact le_trans (le_trans (le_max_left _ _) hsn) (norm_le_norm_add_natCast hre j)
  have hterm : ∀ j ∈ Finset.range n,
      ‖∏ k, (s + (j : ℂ) + lam k) ^ (g k)‖ ≤ Real.exp (K / ‖s + (j : ℂ)‖ ^ 2) := by
    intro j _
    have hb := hK (s + (j : ℂ)) (hjnorm j) (fun k => hjlam j k)
    have hnorm := norm_sub_le (∏ k, (s + (j : ℂ) + lam k) ^ (g k)) 1
    have hle : ‖∏ k, (s + (j : ℂ) + lam k) ^ (g k)‖ ≤ 1 + K / ‖s + (j : ℂ)‖ ^ 2 := by
      have h1 := norm_add_le ((∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1) 1
      simp only [sub_add_cancel, norm_one] at h1
      linarith [hb, h1]
    exact le_trans hle (by linarith [Real.add_one_le_exp (K / ‖s + (j : ℂ)‖ ^ 2)])
  have hsum : ∑ j ∈ Finset.range n, K / ‖s + (j : ℂ)‖ ^ 2 ≤ 4 * K := by
    have hcmp : ∀ j ∈ Finset.range n,
        K / ‖s + (j : ℂ)‖ ^ 2 ≤ 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by
      intro j _
      have hlow := two_mul_norm_add_natCast_sq_ge hre j
      have hjn : (0 : ℝ) < ‖s + (j : ℂ)‖ := by
        have := norm_le_norm_add_natCast hre j
        linarith
      have hpos : (0 : ℝ) < (‖s‖ + (j : ℝ)) ^ 2 := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        positivity
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s + (j : ℂ)‖ ^ 2)]
      have hratio : (1 : ℝ) ≤ 2 * ‖s + (j : ℂ)‖ ^ 2 / (‖s‖ + (j : ℝ)) ^ 2 := by
        rw [le_div_iff₀ hpos]
        linarith [hlow]
      have hfin : 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) * ‖s + (j : ℂ)‖ ^ 2
          = K * (2 * ‖s + (j : ℂ)‖ ^ 2 / (‖s‖ + (j : ℝ)) ^ 2) := by
        field_simp
      rw [hfin]
      nlinarith [hratio, hK0]
    refine le_trans (Finset.sum_le_sum hcmp) ?_
    rw [← Finset.mul_sum]
    have hhead := sum_inv_sq_shift_head_le hspos n
    have h2 : (1 : ℝ) / ‖s‖ ^ 2 + 1 / ‖s‖ ≤ 2 := by
      have ha : (1 : ℝ) / ‖s‖ ≤ 1 := by
        rw [div_le_one hspos]; linarith
      have hb : (1 : ℝ) / ‖s‖ ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      linarith
    nlinarith [hhead, hK0]
  calc ‖∏ j ∈ Finset.range n, ∏ k, (s + (j : ℂ) + lam k) ^ (g k)‖
      = ∏ j ∈ Finset.range n, ‖∏ k, (s + (j : ℂ) + lam k) ^ (g k)‖ := by rw [norm_prod]
    _ ≤ ∏ j ∈ Finset.range n, Real.exp (K / ‖s + (j : ℂ)‖ ^ 2) :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) hterm
    _ = Real.exp (∑ j ∈ Finset.range n, K / ‖s + (j : ℂ)‖ ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (4 * K) := Real.exp_le_exp.mpr hsum

end

end GaloisForLFunctions.HTGeometry
