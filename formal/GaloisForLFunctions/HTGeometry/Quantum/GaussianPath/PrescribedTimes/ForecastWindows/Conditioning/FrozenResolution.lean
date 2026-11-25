import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.MaximalWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

/-! # Simultaneous conditional resolution on growing prefixes of one draw -/

open Filter MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
open ShortWindows
noncomputable section

/-- At any prescribed sequence of positive dates, the conditional window
constant eventually grows at most cubically in prefix length, on one
infinite Gaussian chain. The radius may then be chosen from the observed
coordinates. Both the crossing and return budgets can vary by prefix. -/
theorem gaussian_eventual_conditional_resolution
    (j s : ℕ→ℕ) (S : (k : ℕ)→Set (PrefixIndex (k+1))) (a b T : ℕ→ℝ) (hT : ∀ k, 0<T k) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      let d := Fintype.card (ChainLabel (k+3))
      let F := revealedPassage (k+1) (j k) (s k) (S k) (a k) (b k)
      ∀ h> (0:ℝ), μ.real {y | |F (prefixPoint k ω,y)-T k|<h} ≤
        (16*(exp 1)^2*(2*(d:ℝ)+1)*((k:ℝ)+1)^2/T k)*h := by
  let μ (k : ℕ) := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
  let F (k : ℕ) := revealedPassage (k+1) (j k) (s k) (S k) (a k) (b k)
  let D (k : ℕ) := 16*(exp 1)^2*(2*(Fintype.card (ChainLabel (k+3)):ℝ)+1)
  let M (k : ℕ) := D k*((k:ℝ)+1)^2
  have hD (k : ℕ) : 0<D k := by dsimp only [D]; positivity
  have hM (k : ℕ) : 0<M k := mul_pos (hD k) (by positivity)
  let E (k : ℕ) := {x | (x,T k)∈excessKernel (μ k) (F k) (M k/T k)}
  have hm (k : ℕ) : MeasurableSet (E k) :=
    (measurableSet_excessKernel (μ k) (revealedPassage_properties (k+1) (j k) (s k) (S k) (a k) (b k)).1 (div_pos (hM k) (hT k))).preimage
      (measurable_id.prodMk measurable_const)
  let B (k : ℕ) := prefixPoint k ⁻¹' E k
  have hprob (k : ℕ) : pathPauliDisorderLaw.real (B k) ≤ 1/((k:ℝ)+1)^2 := by
    have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage (hm k).nullMeasurableSet
    change pathPauliDisorderLaw.real (B k)=(μ k).real (E k) at he
    rw [he]
    have h := gaussian_first_wait_resolution_tail (k+1) (j k) (s k) (S k) (a k) (b k) (hT k) (hM k)
    apply h.trans_eq
    change D k/(D k*((k:ℝ)+1)^2)=_
    field_simp [(hD k).ne']
  have hsum : Summable (fun k : ℕ => (1:ℝ)/((k:ℝ)+1)^2) := by
    have hh : Summable (fun k : ℕ => (1:ℝ)/(k:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hh
  have hs := hsum.of_norm_bounded (f:=fun k => pathPauliDisorderLaw.real (B k))
    (fun k => by rw [Real.norm_of_nonneg measureReal_nonneg]; exact hprob k)
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have havoid : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω∉B k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top pathPauliDisorderLaw _)] using hs.tsum_ofReal_ne_top
  filter_upwards [havoid] with ω hω
  filter_upwards [hω] with k hk
  intro μ' d F' h hh
  exact le_of_not_gt (fun hbad => hk ⟨h,hh,hbad⟩)

#print axioms gaussian_eventual_conditional_resolution
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
