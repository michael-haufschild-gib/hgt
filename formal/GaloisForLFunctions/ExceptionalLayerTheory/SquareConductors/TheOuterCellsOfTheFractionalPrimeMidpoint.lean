import GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancyOfAtomicRows
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest

/-!
# Outer cells of the prime midpoint

At the lower edge the inverse test is a single power. At the upper edge the
centered prime field consists of the composite atom at 4n. These cells give
sharp moment thresholds and exact power-law distributions.
-/

noncomputable section

open MeasureTheory Finset
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
open GaloisForLFunctions.ExclusionOfTheCriticalState (ordinaryPrimeExcessCoeff)
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Signed discrepancy field of centered prime mass throughout the double interval. -/
def midpointFractionalField (n : ℕ) (b : ℝ) : ℝ → ℝ :=
  field (Ioc (2*n) (4*n)) Nat.cast ordinaryPrimeExcessCoeff (b-1)

/-- The inverse test changes sign at the common endpoint of the two prime intervals. -/
def midpointFractionalTest (n : ℕ) (b t : ℝ) : ℝ :=
  cutPower (-b) (t-↑(2*n)) - 2*cutPower (-b) (t-↑(3*n))

/-- Opposite outer edges isolate a unit test and a composite atom of weight −1.
Their powers are complementary for every choice of fractional order. -/
theorem midpoint_fractional_edge_values {n : ℕ} (hn : 0 < n) (b : ℝ)
    {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    midpointFractionalTest n b (↑(2*n)+u) = u^(-b) ∧
    midpointFractionalField n b (↑(4*n)-u) = -(u^(b-1)) := by
  have hn' : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have ht : ¬ 0 < (↑(2*n):ℝ)+u-↑(3*n) := by push_cast; linarith only [hu.2, hn']
  constructor
  · simp only [midpointFractionalTest, show (↑(2*n):ℝ)+u-↑(2*n)=u by ring,
      cutPower, if_pos hu.1, if_neg ht, mul_zero, sub_zero]
  · unfold midpointFractionalField field
    rw [sum_eq_single (4*n)]
    · have hnp : ¬ (4*n).Prime := by
        rw [show 4*n=2*(2*n) by omega]
        exact Nat.not_prime_mul (by norm_num) (by omega)
      simp [ordinaryPrimeExcessCoeff, hnp, cutPower, hu.1]
    · intro p hp hpn
      have hk : p+1 ≤ 4*n := by have := (mem_Ioc.mp hp).2; omega
      have hh : (p:ℝ)+1 ≤ ↑(4*n) := by exact_mod_cast hk
      have hz : ¬ 0 < (p:ℝ)-(↑(4*n)-u) := by linarith only [hu.2, hh]
      simp only [cutPower, if_neg hz, mul_zero]
    · intro h
      exact (h (mem_Ioc.mpr ⟨by omega, le_rfl⟩)).elim

/-- Exact moment thresholds for arbitrary real powers on the two unit edge
cells. The singular powers in the two tests have complementary orders. -/
theorem midpoint_fractional_edge_moments {n : ℕ} (hn : 0 < n) (b r s : ℝ) :
    (IntegrableOn (fun u : ℝ => |midpointFractionalTest n b (↑(2*n)+u)|^r)
      (Set.Ioo 0 1) ↔ b*r < 1) ∧
    (IntegrableOn (fun u : ℝ => |midpointFractionalField n b (↑(4*n)-u)|^s)
      (Set.Ioo 0 1) ↔ (1-b)*s < 1) := by
  have ht : (fun u : ℝ => |midpointFractionalTest n b (↑(2*n)+u)|^r)
      =ᵐ[volume.restrict (Set.Ioo 0 1)] (fun u => u^((-b)*r)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun _ hu => by
      dsimp only
      rw [(midpoint_fractional_edge_values hn b hu).1,
        abs_of_pos (Real.rpow_pos_of_pos hu.1 _), ← Real.rpow_mul hu.1.le]
  have hf : (fun u : ℝ => |midpointFractionalField n b (↑(4*n)-u)|^s)
      =ᵐ[volume.restrict (Set.Ioo 0 1)] (fun u => u^((b-1)*s)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun _ hu => by
      dsimp only
      rw [(midpoint_fractional_edge_values hn b hu).2, abs_neg,
        abs_of_pos (Real.rpow_pos_of_pos hu.1 _), ← Real.rpow_mul hu.1.le]
  unfold IntegrableOn
  rw [integrable_congr ht, integrable_congr hf]
  change (IntegrableOn _ (Set.Ioo (0:ℝ) 1) ↔ _) ∧ (IntegrableOn _ (Set.Ioo (0:ℝ) 1) ↔ _)
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one,
    intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> constructor <;> intro h <;> linarith only [h]

private lemma power_superlevel {e z : ℝ} (he : e < 0) (hz : 0 < z) :
    {u : ℝ | u ∈ Set.Ioo 0 1 ∧ z < u^e} = Set.Ioo 0 (min 1 (z^e⁻¹)) := by
  ext u
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu.1, lt_min hu.2 ((Real.lt_rpow_inv_iff_of_neg hu.1 hz he).mpr h)⟩
  · rintro ⟨hu, h⟩
    obtain ⟨h₁,h₂⟩ := lt_min_iff.mp h
    exact ⟨⟨hu,h₁⟩,(Real.lt_rpow_inv_iff_of_neg hu hz he).mp h₂⟩

/-- The exact endpoint distributions give weak moment control at both critical
indices. Their tails have exponents −1/b and −1/(1−b). -/
theorem midpoint_edge_distribution {n : ℕ} (hn : 0 < n) {b z : ℝ}
    (hb : b ∈ Set.Ioo 0 1) (hz : 0 < z) :
    volume {u : ℝ | u ∈ Set.Ioo 0 1 ∧ z < |midpointFractionalTest n b (↑(2*n)+u)|} =
        ENNReal.ofReal (min 1 (z^(-b)⁻¹)) ∧
    volume {u : ℝ | u ∈ Set.Ioo 0 1 ∧ z < |midpointFractionalField n b (↑(4*n)-u)|} =
        ENNReal.ofReal (min 1 (z^(b-1)⁻¹)) := by
  have kv (e : ℝ) (he : e < 0) :
      volume {u : ℝ | u ∈ Set.Ioo 0 1 ∧ z < u^e} = ENNReal.ofReal (min 1 (z^e⁻¹)) := by
    rw [power_superlevel he hz, Real.volume_Ioo, sub_zero]
  constructor
  · rw [← kv (-b) (neg_lt_zero.mpr hb.1)]
    congr 1
    ext u
    apply and_congr_right
    intro hu
    rw [(midpoint_fractional_edge_values hn b hu).1,abs_of_pos (Real.rpow_pos_of_pos hu.1 _)]
  · rw [← kv (b-1) (sub_neg.mpr hb.2)]
    congr 1
    ext u
    apply and_congr_right
    intro hu
    rw [(midpoint_fractional_edge_values hn b hu).2,abs_neg,abs_of_pos (Real.rpow_pos_of_pos hu.1 _)]

/-- Every conjugate pair of finite Hölder exponents fails on at least one edge.
The signed Abel integral nevertheless exists for all orders in (0,1). -/
theorem midpoint_no_conjugate_edge_moments {n : ℕ} (hn : 0 < n) (b : ℝ)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : 1/r+1/s=1) :
    ¬ (IntegrableOn (fun u : ℝ => |midpointFractionalTest n b (↑(2*n)+u)|^r) (Set.Ioo 0 1) ∧
       IntegrableOn (fun u : ℝ => |midpointFractionalField n b (↑(4*n)-u)|^s) (Set.Ioo 0 1)) := by
  rintro ⟨h₁,h₂⟩
  obtain ⟨ht,hf⟩ := midpoint_fractional_edge_moments hn b r s
  have ha := (lt_div_iff₀ hr).mpr (ht.mp h₁)
  have hb := (lt_div_iff₀ hs).mpr (hf.mp h₂)
  linarith only [hrs,ha,hb]

/-- Exact local square-integrability thresholds at the two outer edges. -/
theorem midpoint_fractional_square_thresholds {n : ℕ} (hn : 0 < n) (b : ℝ) :
    (IntegrableOn (fun u : ℝ => midpointFractionalTest n b (↑(2*n)+u)^2)
      (Set.Ioo 0 1) ↔ b < 1/2) ∧
    (IntegrableOn (fun u : ℝ => midpointFractionalField n b (↑(4*n)-u)^2)
      (Set.Ioo 0 1) ↔ 1/2 < b) := by
  have h := midpoint_fractional_edge_moments hn b 2 2
  norm_num only [Real.rpow_ofNat, sq_abs] at h
  rw [h.1, h.2]
  constructor <;> constructor <;> intro h <;> linarith only [h]

/-- No order makes the inverse test and the centered field both locally square
integrable at their respective outer endpoints. -/
theorem midpoint_no_common_square_order {n : ℕ} (hn : 0 < n) :
    ¬ ∃ b : ℝ, IntegrableOn (fun u : ℝ => midpointFractionalTest n b (↑(2*n)+u)^2) (Set.Ioo 0 1) ∧
      IntegrableOn (fun u : ℝ => midpointFractionalField n b (↑(4*n)-u)^2) (Set.Ioo 0 1) := by
  rintro ⟨b,ht,hf⟩
  obtain ⟨h₁,h₂⟩ := midpoint_fractional_square_thresholds hn b
  exact (h₁.mp ht).not_gt (h₂.mp hf)

#print axioms midpoint_no_conjugate_edge_moments
#print axioms midpoint_edge_distribution

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
