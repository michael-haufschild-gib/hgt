import GaloisForLFunctions.RHTower.ZetaChiDualResonatorIntegral

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


private theorem narrow_resonator_card {k : ℕ} (S : Finset ℕ)
    (hS : ∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) : S.card ≤ k + 1 := by
  have hsub : S ⊆ Finset.Icc (100 * k) (101 * k) := by
    intro a ha
    exact Finset.mem_Icc.mpr (hS a ha)
  have hb := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hb
  omega

private theorem growing_resonator_cost {k : ℝ} (hk : 1 ≤ k) :
    (101 * k + (5 * k ^ 2) ^ 10 / k ^ 2) * (k + 1) ≤
      204 * ((5 * k ^ 2) ^ 10 / k) := by
  have hk0 : 0 < k := by linarith
  have h17 : 1 ≤ k ^ 17 := one_le_pow₀ hk
  have hp : k ^ 3 ≤ k ^ 20 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr h17) (show 0 ≤ k ^ 3 by positivity)]
  have hN : k ^ 3 ≤ (5 * k ^ 2) ^ 10 := by
    nlinarith only [hp, show 0 ≤ k ^ 20 by positivity]
  have hkN : k ≤ (5 * k ^ 2) ^ 10 / k ^ 2 :=
    (le_div_iff₀ (by positivity : 0 < k ^ 2)).mpr (by nlinarith only [hN])
  have hsum : 101 * k + (5 * k ^ 2) ^ 10 / k ^ 2 ≤
      102 * ((5 * k ^ 2) ^ 10 / k ^ 2) := by linarith
  calc
    _ ≤ (102 * ((5 * k ^ 2) ^ 10 / k ^ 2)) * (2 * k) :=
      mul_le_mul hsum (by linarith) (by positivity) (by positivity)
    _ = _ := by field_simp; ring

/-- A growing complete frequency family has vanishing relative first-moment
error on the literal square-cutoff schedule, uniformly in all coefficients. -/
theorem exists_zetaChi_dual_growing_resonator_integral_bound
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ S : Finset ℕ, (∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) → ∀ c : ℕ → ℂ,
      ‖(∫ t in (5 * (k : ℝ) ^ 2) ^ 10..(2 * (5 * (k : ℝ) ^ 2) ^ 10),
          zetaChiDualCoherentCarrier s (k ^ 2) t * ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) -
        (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) *
          (∫ t in (5 * (k : ℝ) ^ 2) ^ 10..(2 * (5 * (k : ℝ) ^ 2) ^ 10),
            zetaChiDualCoherentCarrier s (k ^ 2) t)‖ ≤
        C * ((5 * (k : ℝ) ^ 2) ^ 10 / k) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaChi_dual_coherent_resonator_integral_bound z hr hz0 hz1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hb
  refine ⟨204 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)] with k hkM hk1
  intro s hs S hS c
  have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by decide) k
  have hk0 : 0 < k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hcard : (S.card : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast narrow_resonator_card S hS
  have hbnd := hM (k ^ 2) (hkM.trans hkk) s hs k hk0 S hS c
  simp only [Nat.cast_pow] at hbnd
  apply hbnd.trans
  calc
    _ ≤ C * (101 * (k : ℝ) + (5 * (k : ℝ) ^ 2) ^ 10 / (k : ℝ) ^ 2) *
        ((k : ℝ) + 1) * ∑ a ∈ S, ‖c a‖ ^ 2 := by gcongr
    _ = C * ((101 * (k : ℝ) + (5 * (k : ℝ) ^ 2) ^ 10 / (k : ℝ) ^ 2) *
        ((k : ℝ) + 1)) * ∑ a ∈ S, ‖c a‖ ^ 2 := by ring
    _ ≤ C * (204 * ((5 * (k : ℝ) ^ 2) ^ 10 / k)) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (growing_resonator_cost hkR) hC.le)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by ring

/-- Every coefficient choice in the complete growing narrow family preserves
a positive physical first mean of the selected coherent carrier. -/
theorem exists_zetaChi_dual_growing_resonator_mean_lower
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ k : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ S : Finset ℕ, (∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) → ∀ c : ℕ → ℂ,
      κ * (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2) ≤
        (∫ t in (5 * (k : ℝ) ^ 2) ^ 10..(2 * (5 * (k : ℝ) ^ 2) ^ 10),
          zetaChiDualCoherentCarrier s (k ^ 2) t * ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)).re := by
  obtain ⟨C, hC, hb⟩ := exists_zetaChi_dual_growing_resonator_integral_bound z hr hz0 hz1
  obtain ⟨κ, hκ, hl⟩ := exists_zetaChi_dual_coherent_block_mean_lower z hr hz0 hz1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hl
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * C / κ)
  refine ⟨κ / 2, by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop M, eventually_ge_atTop L,
    eventually_ge_atTop (1 : ℕ)] with k hk hkM hkL hk1
  intro s hs S hS c
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by decide) k
  have hmean := hM (k ^ 2) (hkM.trans hkk) s hs
  change κ * (5 * ((k ^ 2 : ℕ) : ℝ)) ^ 10 ≤
    (∫ t in (5 * ((k ^ 2 : ℕ) : ℝ)) ^ 10..(2 * (5 * ((k ^ 2 : ℕ) : ℝ)) ^ 10),
      zetaChiDualCoherentCarrier s (k ^ 2) t).re at hmean
  simp only [Nat.cast_pow] at hmean
  have hlarge : 2 * C / κ < (k : ℝ) := hL.trans_le (by exact_mod_cast hkL)
  have hsmall : C / (k : ℝ) ≤ κ / 2 := by
    have hh := (div_lt_iff₀ hκ).mp hlarge
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [hh]
  have henergy : 0 ≤ ∑ a ∈ S, ‖c a‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hmean henergy
  have herr := hk s hs S hS c
  have hreal := (Complex.abs_re_le_norm _).trans herr
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hreal
  have hcost : C * ((5 * (k : ℝ) ^ 2) ^ 10 / k) * (∑ a ∈ S, ‖c a‖ ^ 2) ≤
      (κ / 2) * (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2) := by
    calc
      _ = (C / (k : ℝ)) * (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2) := by ring
      _ ≤ _ := by gcongr
  linarith [(abs_le.mp hreal).1]

end RHTower
