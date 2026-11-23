import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PathCuts

/-! # Detectable physical bonds across arbitrary circuit cuts -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Crossed bonds with signal magnitude above the common detection threshold. -/
def detectable {n : ℕ} {C : TwoQubitCircuit (n+2)} (c : Cut C) (u : PathShell n)
    (t r : ℝ) : Finset (Fin (n+1)) := by
  classical
  exact (crossed c).filter fun e => r < |bondSignal e u t|

/-- One event bounds missed detections on every cut, regardless of how
many gates were used within either color. -/
theorem gaussian_all_cut_detection {a T η β : ℝ} (ha : 0 < a) (hη : 0 < η) (hβ : 0 < β) :
    ∃ r : ℝ, 0 < r ∧ ∀ (n : ℕ) (t : ℝ), t∈Icc a T →
      pathPauliDisorderLaw.real {ω | ∃ C : TwoQubitCircuit (n+2), ∃ c : Cut C,
        ((detectable c (pathPauliDisorderShell ω n) t r).card:ℝ)+η*(n+1:ℕ) < (crossed c).card} ≤ β := by
  classical
  obtain ⟨r,hr,hs⟩ := gaussian_bond_signal_probability (T:=T) ha (mul_pos hη hβ)
  refine ⟨r,hr,?_⟩
  intro n t ht
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by unfold μ pathPauliDisorderLaw; infer_instance
  let m : ℝ := (n+1:ℕ)
  have hm : 0 < m := by dsimp only [m]; positivity
  let S (e : Fin (n+1)) := {ω | |bondSignal e (pathPauliDisorderShell ω n) t| ≤ r}
  have hS (e) : MeasurableSet (S e) := measurableSet_le (measurable_bondSignal e t).abs measurable_const
  let I e := (S e).indicator (fun _ => (1:ℝ))
  let f (ω : PathPauliDisorder) := ∑ e, I e ω
  have hi (e) : Integrable (I e) μ := (integrable_const _).indicator (hS e)
  have hμ (e) : μ.real (S e) ≤ η*β := (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hs n e t ht)).trans_eq
    (ENNReal.toReal_ofReal (mul_pos hη hβ).le)
  have hI (e) : (∫ ω, I e ω ∂μ)=μ.real (S e) := integral_indicator_one (hS e)
  have hmean : ∫ ω, f ω ∂μ ≤ m*(η*β) := by
    rw [show f=(fun ω => ∑ e, I e ω) from rfl,integral_finsetSum _ (fun e _ => hi e)]
    calc _ ≤ ∑ _e : Fin (n+1), η*β := Finset.sum_le_sum (fun e _ => by
           rw [hI]; exact hμ e)
         _ = _ := by simp [nsmul_eq_mul,m]
  let bad (ω : PathPauliDisorder) := Finset.univ.filter fun e : Fin (n+1) => ω∈S e
  have hcard (ω) : f ω=((bad ω).card:ℝ) := by
    simpa only [f,I,bad,Set.indicator_apply] using
      (Finset.sum_boole (R:=ℝ) (fun e => ω∈S e) Finset.univ)
  have hpos : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω => by
    change 0 ≤ f ω
    rw [hcard]
    exact Nat.cast_nonneg _
  have hmark := (mul_meas_ge_le_integral_of_nonneg hpos
    (integrable_finsetSum _ (fun e _ => hi e)) (η*m)).trans hmean
  have bound : μ.real {ω | η*m ≤ f ω} ≤ β := (mul_le_mul_iff_right₀ (mul_pos hη hm)).mp
    (hmark.trans_eq (by ring))
  apply (measureReal_mono (μ:=μ) (s₂:={ω | η*m ≤ f ω}) ?_ (measure_ne_top _ _)).trans bound
  rintro ω ⟨C,c,hcut⟩
  have hcov : crossed c ⊆ detectable c (pathPauliDisorderShell ω n) t r ∪ bad ω := by
    intro e he
    by_cases h : ω∈S e
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,lt_of_not_ge h⟩)
  have hsum := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have h₂ : ((crossed c).card:ℝ) ≤ ((detectable c (pathPauliDisorderShell ω n) t r).card:ℝ)+(bad ω).card := by
    exact_mod_cast hsum
  change η*m ≤ f ω
  rw [hcard]
  change ((detectable c (pathPauliDisorderShell ω n) t r).card:ℝ)+η*m < (crossed c).card at hcut
  linarith only [h₂,hcut]

/-- Apart from an arbitrarily small fraction of bonds, half the
deficit below one gate per bond is detectable across some circuit cut. -/
theorem gaussian_detectable_cut {a T η β : ℝ} (ha : 0 < a) (hη : 0 < η) (hβ : 0 < β) :
    ∃ r : ℝ, 0 < r ∧ ∀ (n : ℕ) (t : ℝ), t∈Icc a T →
      pathPauliDisorderLaw.real {ω | ∃ C : TwoQubitCircuit (n+2), ∀ c : Cut C,
        (C.gateCount:ℝ)+2*((detectable c (pathPauliDisorderShell ω n) t r).card:ℝ)+η*(n+1:ℕ) < (n+1:ℕ)} ≤ β := by
  obtain ⟨r,hr,h⟩ := gaussian_all_cut_detection (T:=T) ha (half_pos hη) hβ
  refine ⟨r,hr,?_⟩
  intro n t ht
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans (h n t ht)
  rintro ω ⟨C,hC⟩
  obtain ⟨c,hcut⟩ := many_crossed C
  refine ⟨C,c,?_⟩
  have hb : ((n+1:ℕ):ℝ) ≤ (C.gateCount:ℝ)+2*((crossed c).card:ℝ) := by exact_mod_cast hcut
  linarith only [hC c,hb]

#print axioms gaussian_detectable_cut
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
