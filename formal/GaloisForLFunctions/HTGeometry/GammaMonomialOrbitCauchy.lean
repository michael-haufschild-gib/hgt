import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitBound

/-!
# The orbit limit is approached at rate `1/‖s‖`

Telescoping the functional equation gives

`M(s+n) - M(s) = ∑_{j<n} (ρ_g(s+j) - 1) M(s+j)`,

and in a dominant class each summand is `O(‖s+j‖^{-2})` times a bound for `M` along the orbit.  The
sum of `‖s+j‖^{-2}` is `O(1/‖s‖)`, so the whole orbit stays within `O(1/‖s‖)` of its base point —
uniformly in the number of steps.  This is the Cauchy estimate that produces the orbit limit with a
rate.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The orbit stays within `O(1/‖s‖)` of its base point.** -/
theorem exists_norm_gammaMonomial_orbit_sub_le {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ A Rb : ℝ, 0 ≤ A ∧ 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      ∀ n : ℕ, ‖gammaMonomial lam g (s + (n : ℂ)) - gammaMonomial lam g s‖
        ≤ A * ‖gammaMonomial lam g s‖ / ‖s‖ := by
  obtain ⟨K, Rb₀, hK0, hRb₀, hK⟩ := exists_norm_shiftRatio_sub_one_le lam g hdeg hmom
  obtain ⟨B, Rb₁, hB0, hRb₁, hB⟩ := exists_prod_norm_shiftRatio_le lam g hdeg hmom
  refine ⟨4 * K * B, max (max Rb₀ Rb₁) 1, by positivity, le_max_right _ _, ?_⟩
  intro s hs hsn n
  have hre : 0 < s.re := by
    have hnn : (0 : ℝ) ≤ ∑ j, |(lam j).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hsn
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  have hRb₀s : Rb₀ ≤ ‖s‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsn
  have hRb₁s : Rb₁ ≤ ‖s‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsn
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
  have hjnorm : ∀ j : ℕ, ‖s‖ ≤ ‖s + (j : ℂ)‖ := fun j => norm_le_norm_add_natCast hre j
  -- the orbit bound
  have horbit : ∀ j : ℕ, ‖gammaMonomial lam g (s + (j : ℂ))‖
      ≤ B * ‖gammaMonomial lam g s‖ := by
    intro j
    rw [gammaMonomial_shift_nat lam g hs j, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB s hs hRb₁s j) (norm_nonneg _)
  -- the telescope
  have htel : gammaMonomial lam g (s + (n : ℂ)) - gammaMonomial lam g s
      = ∑ j ∈ Finset.range n, ((∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1)
          * gammaMonomial lam g (s + (j : ℂ)) := by
    have hsum := Finset.sum_range_sub
      (f := fun j : ℕ => gammaMonomial lam g (s + (j : ℂ))) n
    simp only [Nat.cast_zero, add_zero] at hsum
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : s + ((j + 1 : ℕ) : ℂ) = (s + (j : ℂ)) + 1 := by push_cast; ring
    rw [hcast, gammaMonomial_shift_of_re lam g (hjre j)]
    ring
  rw [htel]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Finset.range n,
      ‖((∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1) * gammaMonomial lam g (s + (j : ℂ))‖
        ≤ (2 * K * B * ‖gammaMonomial lam g s‖) * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by
    intro j _
    have hRb₀j : Rb₀ ≤ ‖s + (j : ℂ)‖ := le_trans hRb₀s (hjnorm j)
    have hb := hK (s + (j : ℂ)) hRb₀j (fun k => hjlam j k)
    have hlow := two_mul_norm_add_natCast_sq_ge hre j
    have hjpos : (0 : ℝ) < ‖s + (j : ℂ)‖ := lt_of_lt_of_le hspos (hjnorm j)
    have hpos : (0 : ℝ) < (‖s‖ + (j : ℝ)) ^ 2 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      positivity
    have hb2 : ‖(∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1‖
        ≤ 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by
      refine le_trans hb ?_
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s + (j : ℂ)‖ ^ 2)]
      have hratio : (1 : ℝ) ≤ 2 * ‖s + (j : ℂ)‖ ^ 2 / (‖s‖ + (j : ℝ)) ^ 2 := by
        rw [le_div_iff₀ hpos]
        linarith [hlow]
      have hfin : 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) * ‖s + (j : ℂ)‖ ^ 2
          = K * (2 * ‖s + (j : ℂ)‖ ^ 2 / (‖s‖ + (j : ℝ)) ^ 2) := by
        field_simp
      rw [hfin]
      nlinarith [hratio, hK0]
    rw [norm_mul]
    have hnn : (0 : ℝ) ≤ 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by positivity
    calc ‖(∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1‖ * ‖gammaMonomial lam g (s + (j : ℂ))‖
        ≤ (2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2)) * (B * ‖gammaMonomial lam g s‖) :=
          mul_le_mul hb2 (horbit j) (norm_nonneg _) hnn
      _ = (2 * K * B * ‖gammaMonomial lam g s‖) * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hhead := sum_inv_sq_shift_head_le hspos n
  have hsq : (1 : ℝ) / ‖s‖ ^ 2 ≤ 1 / ‖s‖ := by
    rw [div_le_div_iff₀ (by positivity) hspos]
    nlinarith
  have hnn2 : (0 : ℝ) ≤ 2 * K * B * ‖gammaMonomial lam g s‖ := by positivity
  have hstep : (2 * K * B * ‖gammaMonomial lam g s‖)
      * (∑ j ∈ Finset.range n, (1 : ℝ) / (‖s‖ + (j : ℝ)) ^ 2)
      ≤ (2 * K * B * ‖gammaMonomial lam g s‖) * (2 * (1 / ‖s‖)) := by
    refine mul_le_mul_of_nonneg_left ?_ hnn2
    linarith [hhead, hsq]
  refine le_trans hstep ?_
  rw [div_eq_mul_one_div]
  exact le_of_eq (by ring)

end

end GaloisForLFunctions.HTGeometry
