import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.DisjointWindows

/-! # Positive frequency of any prescribed Gaussian box on disjoint blocks -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- An injective choice of coordinates makes the blocks independent.
A nondegenerate box occurs with a positive lower density on one draw. -/
theorem gaussian_disjoint_box_frequency {K : Type*} [Fintype K]
    (g : ℕ × K → ℕ × PathPauliDirections) (hg : Function.Injective g)
    (lo hi : K → ℝ) (hbox : ∀ j, lo j < hi j) :
    ∃ p : ℝ, 0 < p ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      p*m ≤ ((Finset.range m).filter (fun k => ∀ j, ω (g (k,j)) ∈ Icc (lo j) (hi j))).card := by
  classical
  let blockLaw : Measure (K → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
  letI : IsProbabilityMeasure blockLaw := by dsimp only [blockLaw]; infer_instance
  let blockSeqLaw := Measure.infinitePi fun _ : ℕ => blockLaw
  let readBlock (ω : PathPauliDisorder) (k : ℕ) (j : K) := ω (g (k,j))
  have hread : MeasurePreserving readBlock pathPauliDisorderLaw blockSeqLaw :=
    SpanningDensity.FixedHorizon.disjoint_window_law (gaussianReal 0 1) g hg
  let B : Set (K → ℝ) := univ.pi fun i => Icc (lo i) (hi i)
  have hB : MeasurableSet B := MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc
  have hp : 0 < blockLaw B := by
    simp only [blockLaw,Measure.infinitePi_eq_pi,B,Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (gaussianReal_Icc_pos (hbox i)).ne'
  let f := B.indicator (fun _ : (K → ℝ) => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hB
  have hint : Integrable f blockLaw := (integrable_const 1).indicator hB
  let X (j : ℕ) (ω : ℕ → (K → ℝ)) := f (ω j)
  have hid (j : ℕ) : IdentDistrib (X j) f blockSeqLaw blockLaw := by
    have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => blockLaw) j
    have h : IdentDistrib (Function.eval j) id blockSeqLaw blockLaw :=
      ⟨hm.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hm.map_eq⟩
    exact h.comp hf
  have hind : iIndepFun X blockSeqLaw := iIndepFun_infinitePi (P := fun _ => blockLaw) (fun _ => hf)
  have hs := strong_law_ae_real X ((hid 0).integrable_iff.mpr hint)
    (fun _ _ h => hind.indepFun h) (fun j => (hid j).trans (hid 0).symm)
  rw [(hid 0).integral_eq,show (∫ x, f x ∂blockLaw) = blockLaw.real B by
    simp [f,integral_indicator hB,Measure.real]] at hs
  have hpos : 0 < blockLaw.real B := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  refine ⟨blockLaw.real B/2,by positivity,?_⟩
  filter_upwards [hread.quasiMeasurePreserving.ae hs] with ω hω
  filter_upwards [hω.eventually_const_lt (show blockLaw.real B/2 < blockLaw.real B by linarith),
    eventually_ge_atTop 1] with m hm hmpos
  have hcard : (∑ j ∈ Finset.range m, X j (readBlock ω)) =
      (((Finset.range m).filter (fun j => ∀ i, readBlock ω j i ∈ Icc (lo i) (hi i))).card : ℝ) := by
    have hmem (x : (K → ℝ)) : x ∈ B ↔ ∀ i, x i ∈ Icc (lo i) (hi i) := Set.mem_univ_pi
    simp only [X,f,Set.indicator_apply,hmem,Finset.sum_boole]
  rw [hcard] at hm
  exact ((lt_div_iff₀ (show 0 < (m:ℝ) by exact_mod_cast (by omega : 0 < m))).mp hm).le

#print axioms gaussian_disjoint_box_frequency
end
end GaloisForLFunctions.HTGeometry
