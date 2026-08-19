import GaloisForLFunctions.HTGeometry.LocallyUniformMTest

/-!
# The orbit limit of a Gamma monomial

Telescoping the functional equation writes `M(s+n)` as `M(s)` plus a partial sum, and the bound of
`GammaMonomialOrbitCauchy` makes that sum absolutely convergent.  So the orbit limit exists and is
given by an explicit series, which is what lets it be recognised as an analytic, `1`-periodic
function.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- One term of the orbit series. -/
def orbitTerm {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (s : ℂ) (j : ℕ) : ℂ :=
  ((∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1) * gammaMonomial lam g (s + (j : ℂ))

/-- Telescoping the functional equation. -/
theorem gammaMonomial_orbit_telescope {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) (n : ℕ) :
    gammaMonomial lam g (s + (n : ℂ))
      = gammaMonomial lam g s + ∑ j ∈ Finset.range n, orbitTerm lam g s j := by
  have hjre : ∀ j : ℕ, (∑ i, |(lam i).re|) < (s + (j : ℂ)).re := by
    intro j
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hsum := Finset.sum_range_sub
    (f := fun j : ℕ => gammaMonomial lam g (s + (j : ℂ))) n
  simp only [Nat.cast_zero, add_zero] at hsum
  have hterm : ∀ j ∈ Finset.range n,
      gammaMonomial lam g (s + ((j + 1 : ℕ) : ℂ)) - gammaMonomial lam g (s + (j : ℂ))
        = orbitTerm lam g s j := by
    intro j _
    have hcast : s + ((j + 1 : ℕ) : ℂ) = (s + (j : ℂ)) + 1 := by push_cast; ring
    rw [hcast, gammaMonomial_shift_of_re lam g (hjre j), orbitTerm]
    ring
  have hsum2 : ∑ j ∈ Finset.range n, orbitTerm lam g s j
      = gammaMonomial lam g (s + (n : ℂ)) - gammaMonomial lam g s := by
    rw [← hsum]
    exact (Finset.sum_congr rfl hterm).symm
  rw [hsum2]
  ring

/-- The orbit series converges absolutely. -/
theorem summable_orbitTerm {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ Rb : ℝ, 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      Summable (fun j : ℕ => ‖orbitTerm lam g s j‖) := by
  obtain ⟨K, Rb₀, hK0, hRb₀, hK⟩ := exists_norm_shiftRatio_sub_one_le lam g hdeg hmom
  obtain ⟨B, Rb₁, hB0, hRb₁, hB⟩ := exists_prod_norm_shiftRatio_le lam g hdeg hmom
  refine ⟨max (max Rb₀ Rb₁) 1, le_max_right _ _, fun s hs hsn => ?_⟩
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
  set D : ℝ := 2 * K * B * ‖gammaMonomial lam g s‖ with hD
  have hD0 : 0 ≤ D := by positivity
  have hmaj : ∀ j : ℕ, ‖orbitTerm lam g s j‖ ≤ D * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j
    have hRb₀j : Rb₀ ≤ ‖s + (j : ℂ)‖ := le_trans hRb₀s (hjnorm j)
    have hb := hK (s + (j : ℂ)) hRb₀j (fun k => hjlam j k)
    have hlow := two_mul_norm_add_natCast_sq_ge hre j
    have hpos : (0 : ℝ) < (‖s‖ + (j : ℝ)) ^ 2 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      positivity
    have hjnpos : (0 : ℝ) < ‖s + (j : ℂ)‖ := lt_of_lt_of_le hspos (hjnorm j)
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
    have horb : ‖gammaMonomial lam g (s + (j : ℂ))‖ ≤ B * ‖gammaMonomial lam g s‖ := by
      rw [gammaMonomial_shift_nat lam g hs j, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB s hs hRb₁s j) (norm_nonneg _)
    have hstep : ‖orbitTerm lam g s j‖
        ≤ (2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2)) * (B * ‖gammaMonomial lam g s‖) := by
      have hnn4 : (0 : ℝ) ≤ 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by
        have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have h1 : (0 : ℝ) ≤ 1 / (‖s‖ + (j : ℝ)) ^ 2 := by positivity
        nlinarith [hK0, h1]
      rw [orbitTerm, norm_mul]
      exact mul_le_mul hb2 horb (norm_nonneg _) hnn4
    have hshrink : (1 : ℝ) / (‖s‖ + (j : ℝ)) ^ 2 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
      have h1 : ((j : ℝ) + 1) ^ 2 ≤ (‖s‖ + (j : ℝ)) ^ 2 := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        nlinarith
      have h2 : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
      exact one_div_le_one_div_of_le h2 h1
    calc ‖orbitTerm lam g s j‖
        ≤ (2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2)) * (B * ‖gammaMonomial lam g s‖) := hstep
      _ ≤ (2 * K * (1 / ((j : ℝ) + 1) ^ 2)) * (B * ‖gammaMonomial lam g s‖) := by
          have hnn : (0 : ℝ) ≤ B * ‖gammaMonomial lam g s‖ := by positivity
          have h2K : (0 : ℝ) ≤ 2 * K := by positivity
          nlinarith [hshrink, hnn, h2K]
      _ = D * (1 / ((j : ℝ) + 1) ^ 2) := by rw [hD]; ring
  have hbase : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h
    refine h2.congr fun j => ?_
    push_cast
    ring
  have hbasesum : Summable (fun j : ℕ => D * (1 / ((j : ℝ) + 1) ^ 2)) := hbase.mul_left D
  exact hbasesum.of_nonneg_of_le (fun j => norm_nonneg _) hmaj

end

end GaloisForLFunctions.HTGeometry
