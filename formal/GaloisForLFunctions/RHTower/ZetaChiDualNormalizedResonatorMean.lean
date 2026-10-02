import GaloisForLFunctions.RHTower.ZetaChiDualResonatorMass

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The literal real mass of the growing physical resonator on the BAG height window. -/
def zetaChiDualGrowingResonatorMass (S : Finset ℕ) (c : ℕ → ℂ) (k : ℕ) : ℝ :=
  ∫ t in (5 * (k : ℝ) ^ 2) ^ 10..(2 * (5 * (k : ℝ) ^ 2) ^ 10),
    ‖zetaChiDualResonator S c t‖ ^ 2

/-- Physical resonator mass is comparable to length times energy on the
explicit growing schedule; this does not use an independent phase law. -/
theorem zetaChiDualGrowingResonatorMass_bounds
    {k : ℕ} (hk : 1 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) :
    ((5 * (k : ℝ) ^ 2) ^ 10 / 2) * (∑ a ∈ S, ‖c a‖ ^ 2) ≤
        zetaChiDualGrowingResonatorMass S c k ∧
      zetaChiDualGrowingResonatorMass S c k ≤
        2 * (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2) := by
  have hk0 : 0 < k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h18 : (1 : ℝ) ≤ (k : ℝ) ^ 18 := one_le_pow₀ hkR
  have hp : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 20 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr h18) (show 0 ≤ (k : ℝ) ^ 2 by positivity)]
  have hcost : 404 * (k : ℝ) ^ 2 ≤ (5 * (k : ℝ) ^ 2) ^ 10 / 2 := by
    nlinarith only [hp, show 0 ≤ (k : ℝ) ^ 20 by positivity]
  have hb := norm_integral_zetaChiDualNarrowResonator_sq_sub_energy_le hk0 S c hS
    ((5 * (k : ℝ) ^ 2) ^ 10) ((5 * (k : ℝ) ^ 2) ^ 10)
  rw [show (5 * (k : ℝ) ^ 2) ^ 10 + (5 * (k : ℝ) ^ 2) ^ 10 =
    2 * (5 * (k : ℝ) ^ 2) ^ 10 by ring, intervalIntegral.integral_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  change |zetaChiDualGrowingResonatorMass S c k -
    (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2)| ≤ _ at hb
  have he : 0 ≤ ∑ a ∈ S, ‖c a‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsmall := mul_le_mul_of_nonneg_right hcost he
  have hn : 0 ≤ (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2) := by positivity
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

/-- The actual normalized physical density has a uniform positive selected-carrier
first mean for every nonzero coefficient family on the growing narrow support. -/
theorem exists_zetaChi_dual_growing_resonator_normalized_mean_lower
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ k : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ S : Finset ℕ, (∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) → ∀ c : ℕ → ℂ,
      0 < (∑ a ∈ S, ‖c a‖ ^ 2) →
      0 < zetaChiDualGrowingResonatorMass S c k ∧
      κ ≤ (∫ t in (5 * (k : ℝ) ^ 2) ^ 10..(2 * (5 * (k : ℝ) ^ 2) ^ 10),
        zetaChiDualCoherentCarrier s (k ^ 2) t * ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)).re /
          zetaChiDualGrowingResonatorMass S c k := by
  obtain ⟨κ, hκ, hb⟩ := exists_zetaChi_dual_growing_resonator_mean_lower z hr hz0 hz1
  refine ⟨κ / 2, by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  intro s hs S hS c he
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨hlo, hup⟩ := zetaChiDualGrowingResonatorMass_bounds hk1 S c hS
  have hm : 0 < zetaChiDualGrowingResonatorMass S c k :=
    lt_of_lt_of_le (by positivity) hlo
  refine ⟨hm, (le_div_iff₀ hm).mpr ?_⟩
  calc
    _ ≤ (κ / 2) * (2 * (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    _ = κ * (5 * (k : ℝ) ^ 2) ^ 10 * (∑ a ∈ S, ‖c a‖ ^ 2) := by ring
    _ ≤ _ := hk s hs S hS c

end RHTower
