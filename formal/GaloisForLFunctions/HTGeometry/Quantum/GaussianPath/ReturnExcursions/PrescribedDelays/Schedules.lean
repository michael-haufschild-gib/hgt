import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrescribedDelays.WindowPrice
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

/-! # Growing observation windows after the actual first crossing -/

open MeasureTheory Filter Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
open PrescribedTimes ShortWindows
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Prescheduled windows of arbitrary nonnegative delays on each prefix.
The same constants cover the whole schedule. When the normalized total
length is summable, almost every frozen chain eventually misses all windows. -/
theorem gaussian_scheduled_crossing_windows :
    ∃ c>0, ∀ (J : ℕ → ℕ) (T w : (k : ℕ) → Fin (J k) → ℝ),
      (∀ k i, 0≤T k i) → (∀ k i, 0≤w k i) →
      let charge (k : ℕ) := (∑ i, (1+w k i))/((k+3:ℕ):ℝ)^(65/64:ℝ)
      let visits (k : ℕ) := ⋃ i, crossingWindow k c (T k i) (w k i)
      (Tendsto charge atTop (𝓝 0) → Tendsto (fun k => pathPauliDisorderLaw.real (visits k)) atTop (𝓝 0)) ∧
      (Summable charge → ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ visits k) := by
  obtain ⟨c,hc,C,hC,B,hB,hevent,hprice⟩ := gaussian_crossing_window_price
  refine ⟨c,hc,?_⟩
  intro J T w hT hw charge visits
  let μ := pathPauliDisorderLaw
  let F (k : ℕ) := visits k \ B k
  have hf (k : ℕ) : μ.real (F k) ≤ C*charge k := by
    let V (i : Fin (J k)) := crossingWindow k c (T k i) (w k i)
    have hsub : F k ⊆ ⋃ i, (V i \ B k) := by
      rintro ω ⟨hx,hout⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i,hi,hout⟩
    apply (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans _)
    calc
      _ ≤ ∑ i, C*(1+w k i)/((k+3:ℕ):ℝ)^(65/64:ℝ) :=
        Finset.sum_le_sum fun i _ => hprice k _ (hT k i) _ (hw k i)
      _ = C*charge k := by
        simp only [charge,div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  constructor
  · intro hlim
    have hlimB := probability_vanishes μ B hB hevent
    have hlim' : Tendsto (fun k => μ.real (B k)+C*charge k) atTop (𝓝 0) := by
      simpa only [mul_zero,add_zero] using hlimB.add (hlim.const_mul C)
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim'
    intro k
    have hsub : visits k ⊆ B k ∪ F k := fun ω hω => by
      by_cases hb : ω ∈ B k
      · exact Or.inl hb
      · exact Or.inr ⟨hω,hb⟩
    exact (measureReal_mono hsub).trans ((measureReal_union_le ..).trans (add_le_add le_rfl (hf k)))
  · intro hsum
    have hseries : Summable (fun k => μ.real (F k)) :=
      (hsum.mul_left C).of_nonneg_of_le (fun _ => measureReal_nonneg) hf
    have hmiss : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ F k := by
      apply ae_eventually_notMem
      simpa only [ofReal_measureReal (measure_ne_top μ _)] using hseries.tsum_ofReal_ne_top
    filter_upwards [hmiss,hevent] with ω hω hb
    filter_upwards [hω,hb] with k hk hkb
    exact fun hv => hk ⟨hv,hkb⟩

/-- For every prescribed delay sequence, windows of length K^β exclude
a fixed positive density of gates almost surely for every 0 ≤ β < 1/64. -/
theorem gaussian_pathwise_crossing_windows :
    ∃ c>0, ∀ (β : ℝ), 0≤β → β<1/64 → ∀ T : ℕ → ℝ, (∀ k, 0≤T k) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        ω ∉ crossingWindow k c (T k) (((k+3:ℕ):ℝ)^β) := by
  obtain ⟨c,hc,hs⟩ := gaussian_scheduled_crossing_windows
  refine ⟨c,hc,?_⟩
  intro β hβ hβ' T hT
  let N (k : ℕ) : ℝ := (k+3:ℕ)
  have hN (k : ℕ) : 1 ≤ N k := by change (1:ℝ) ≤ ((k+3:ℕ):ℝ); exact_mod_cast (show 1≤k+3 by omega)
  have hpow : 1<65/64-β := by linarith only [hβ']
  have hseri := (summable_nat_add_iff 3).mpr (Real.summable_nat_rpow_inv.mpr hpow)
  have hb : Summable (fun k => (1+(N k)^β)/(N k)^(65/64:ℝ)) := by
    apply (hseri.mul_left 2).of_nonneg_of_le (fun k => by dsimp only [N]; positivity)
    intro k
    have hn := zero_lt_one.trans_le (hN k)
    have hβ1 : 1 ≤ (N k)^β := Real.one_le_rpow (hN k) hβ
    change _ ≤ 2*((N k)^(65/64-β))⁻¹
    rw [rpow_sub hn]
    calc
      _ ≤ (2*(N k)^β)/(N k)^(65/64:ℝ) := by
        exact div_le_div_of_nonneg_right (by linarith only [hβ1]) (rpow_pos_of_pos hn _).le
      _ = _ := by field_simp
  have h := (hs (fun _ => 1) (fun k _ => T k) (fun k _ => (N k)^β) (fun k _ => hT k)
    (fun k _ => (rpow_pos_of_pos (zero_lt_one.trans_le (hN k)) _).le)).2
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_nsmul,iUnion_const] using
    h (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_nsmul] using hb)

#print axioms gaussian_scheduled_crossing_windows
#print axioms gaussian_pathwise_crossing_windows
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
