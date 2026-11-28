import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrescribedDelays.WindowPrice
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Forecasts of any affordable visit from the full coupling direction -/

open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
open PrescribedTimes ShortWindows
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- If every bin costs at most the same fraction of its mass, selecting
among countably many disjoint bins has that same probability cost. -/
private theorem bin_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E D : ℕ → Set Ω) (hD : ∀ j, MeasurableSet (D j)) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (p : ℝ) (hp : 0≤p) (h : ∀ j, μ.real (E j) ≤ p*μ.real (D j)) :
    μ.real (⋃ j, E j) ≤ p := by
  have he (j : ℕ) : μ (E j) ≤ ENNReal.ofReal p*μ (D j) := by
    simpa only [ENNReal.ofReal_mul hp,ofReal_measureReal (measure_ne_top μ _)] using ENNReal.ofReal_le_ofReal (h j)
  have hm : μ (⋃ j, E j) ≤ ENNReal.ofReal p := calc
    _ ≤ ∑' j, μ (E j) := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal p*μ (D j) := ENNReal.tsum_le_tsum he
    _ = ENNReal.ofReal p*μ (⋃ j, D j) := by rw [ENNReal.tsum_mul_left,measure_iUnion hdis hD]
    _ ≤ ENNReal.ofReal p*1 := mul_le_mul_right (prob_le_one : μ (⋃ j, D j)≤1) _
    _ = _ := mul_one _
  exact ((ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hm).trans_eq
    (ENNReal.toReal_ofReal hp)

/-- The forecaster can know every coupling ratio, and choose any
measurable nonnegative delay from that information. The event counts
a fit by any affordable circuit anywhere in the ensuing window. -/
theorem gaussian_angular_forecast_price :
    ∃ c>0, ∃ C>0, ∃ B : ℕ → Set PathPauliDisorder, (∀ k, MeasurableSet (B k)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ B k) ∧
      ∀ (k : ℕ) (T : (PrefixIndex (k+1) → ℝ) → ℝ), Measurable T → (∀ x, 0≤T x) →
        (∀ x (a : ℝ), 0<a → T (a • x)=T x) → ∀ w ≥ (0:ℝ),
        pathPauliDisorderLaw.real ({ω | ω ∈ crossingWindow k c (T (prefixPoint k ω)) w} \ B k) ≤
          C*(2+w)/((k+3:ℕ):ℝ)^(65/64:ℝ) := by
  obtain ⟨c,hc,C,hC,B,hB,hevent,hprice⟩ := gaussian_directional_window_price
  refine ⟨c,hc,C,hC,B,hB,hevent,?_⟩
  intro k T hT hT₀ hscale w hw
  let X := prefixPoint k
  let D (j : ℕ) := T ⁻¹' Ico (j:ℝ) ((j:ℝ)+1)
  let G (j : ℕ) := X ⁻¹' D j
  let E (j : ℕ) := (crossingWindow k c j (w+1) \ B k) ∩ G j
  have hD (j : ℕ) : MeasurableSet (D j) := hT measurableSet_Ico
  have hG (j : ℕ) : MeasurableSet (G j) := (hD j).preimage (gaussian_pauli_prefix_coordinates_law (k+1)).measurable
  have hbin (i j : ℕ) (hi : i<j) : Disjoint (G i) (G j) := by
    apply disjoint_left.mpr
    intro ω ha hb
    have hn : (i:ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hi)
    exact ha.2.not_ge (hn.trans hb.1)
  have hdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h|h
    · exact hbin i j h
    · exact (hbin j i h).symm
  have hsub : {ω | ω ∈ crossingWindow k c (T (X ω)) w} \ B k ⊆ ⋃ j, E j := by
    rintro ω ⟨⟨t,ht,hfit⟩,hout⟩
    let j := ⌊T (X ω)⌋₊
    have hl : (j:ℝ) ≤ T (X ω) := Nat.floor_le (hT₀ _)
    have hh : T (X ω)<(j:ℝ)+1 := Nat.lt_floor_add_one _
    apply mem_iUnion.mpr
    refine ⟨j,⟨⟨⟨t,⟨?_,?_⟩,hfit⟩,hout⟩,hl,hh⟩⟩
    · exact (add_le_add le_rfl hl).trans ht.1
    · linarith only [ht.2,hh]
  apply (measureReal_mono hsub).trans
  apply bin_union _ E G hG hdis _ (by positivity)
  intro j
  have hsel (x) (u : ℝ) (hu : 0<u) (hd : u • x∈D j) : x∈D j := by
    change T (u • x) ∈ Ico (j:ℝ) ((j:ℝ)+1) at hd
    change T x ∈ Ico (j:ℝ) ((j:ℝ)+1)
    simpa only [hscale x u hu] using hd
  have h := hprice k (D j) (hD j) hsel j (Nat.cast_nonneg _) (w+1) (by linarith only [hw])
  simpa only [show 1+(w+1)=2+w by ring] using h

/-- Finite total normalized observation length excludes every sufficiently
late prefix window on one chain, even for forecasts using the direction. -/
theorem gaussian_angular_forecast_windows :
    ∃ c>0, ∀ (T : (k : ℕ) → (PrefixIndex (k+1) → ℝ) → ℝ) (w : ℕ → ℝ),
      (∀ k, Measurable (T k)) → (∀ k x, 0≤T k x) → (∀ k x (a : ℝ), 0<a → T k (a • x)=T k x) →
      (∀ k, 0≤w k) → Summable (fun k => (2+w k)/((k+3:ℕ):ℝ)^(65/64:ℝ)) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        ω ∉ crossingWindow k c (T k (prefixPoint k ω)) (w k) := by
  obtain ⟨c,hc,C,hC,B,_,hevent,hprice⟩ := gaussian_angular_forecast_price
  refine ⟨c,hc,?_⟩
  intro T w hT hT₀ hscale hw hsum
  let F (k : ℕ) := {ω | ω ∈ crossingWindow k c (T k (prefixPoint k ω)) (w k)} \ B k
  have hh : Summable (fun k => pathPauliDisorderLaw.real (F k)) := by
    apply (hsum.mul_left C).of_nonneg_of_le (fun _ => measureReal_nonneg)
    intro k
    simpa only [mul_div_assoc] using hprice k _ (hT k) (hT₀ k) (hscale k) _ (hw k)
  have hmiss : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ F k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top pathPauliDisorderLaw _)] using hh.tsum_ofReal_ne_top
  filter_upwards [hevent,hmiss] with ω hb hf
  filter_upwards [hb,hf] with k hbk hfk
  exact fun h => hfk ⟨h,hbk⟩

#print axioms gaussian_angular_forecast_price
#print axioms gaussian_angular_forecast_windows
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
