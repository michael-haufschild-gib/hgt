import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.Packets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.ActionLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PhaseLaws.FrequencyDistribution

/-! # Single observations at a prescribed winding of a physical energy pair -/

open MeasureTheory Set Filter Topology Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open PrescribedTimes.PhaseLaws
noncomputable section

abbrev Coupling (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))→ℝ
abbrev Level (k : ℕ) := Fin (2^(k+3))

/-- Relative angular speeds in units of the selected energy gap. -/
def gapFrequency (k : ℕ) (i j : Level k) (x : Coupling k) (l : Outside i j) : ℝ :=
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
  Neg.neg ((E l.val-E j)/(E i-E j))

theorem gapFrequency_measurable (k : ℕ) (i j : Level k) : Measurable (gapFrequency k i j) := by
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))
  have he (l : Level k) : Measurable (fun x => E x l) :=
    (measurable_pi_apply l).comp (continuous_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))).measurable
  exact measurable_pi_lambda _ fun l => (((he l.val).sub (he j)).div ((he i).sub (he j))).neg

/-- Read the off-pair phases when the distinguished pair has accumulated t
radians of energy difference. This includes a single candidate winding. -/
def gapSnapshot (k : ℕ) (i j : Level k) (μ : ProbabilityMeasure (Coupling k)) (t : ℝ) :=
  frequencySnapshot μ (gapFrequency k i j) (gapFrequency_measurable k i j) t

/-- Every nonzero real projection of the off-pair frequencies has an
absolutely continuous law. The projection may mix several observation clocks. -/
theorem gap_projection_ac (k : ℕ) (i j : Level k) (hij : i≠j)
    (μ : Measure (Coupling k)) (hμ : μ≪volume) (m : Outside i j→ℝ) (hm : m≠0) :
    μ.map (fun x => -(∑ l, m l*gapFrequency k i j x l))≪volume := by
  classical
  let w := anchoredWeight i j m
  obtain ⟨l,hl⟩ : ∃ l, m l≠0 := by
    by_contra! h
    exact hm (funext h)
  have ho : ∃ p, p≠i ∧ p≠j ∧ w p≠0 :=
    ⟨l.val,l.property.1,l.property.2,(anchored_outside i j m l).trans_ne hl⟩
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))
  let A (x : Coupling k) := normalizedAction w (E x) i j
  have heq (x : Coupling k) : -(∑ l, m l*gapFrequency k i j x l)=A x := by
    rw [show A x=normalizedAction (anchoredWeight i j m) (E x) i j from rfl,anchored_action]
    simp only [gapFrequency,E,mul_neg,Finset.sum_neg_distrib,neg_neg]
  have hmF : Measurable (fun x => -(∑ l, m l*gapFrequency k i j x l)) :=
    (Finset.measurable_fun_sum _ fun l _ => (((measurable_pi_apply l).comp (gapFrequency_measurable k i j)).const_mul (m l))).neg
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hz
  rw [Measure.map_apply hmF hS]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hμ.ae_le (physical_normalized_action_null k i j hij w (anchored_balance i j m) ho S hz)] with x hx
  simpa only [mem_preimage,heq,A,E] using hx

/-- At large prescribed pair winding, the remaining D−2 phases of a
Gaussian local Hamiltonian have Haar law in the limit. A restriction of
the coupling law to a fixed positive-probability event is allowed. -/
theorem gapSnapshot_haar (k : ℕ) (i j : Level k) (hij : i≠j)
    (μ : ProbabilityMeasure (Coupling k)) (hμ : (μ : Measure (Coupling k))≪volume) :
    Tendsto (gapSnapshot k i j μ) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  refine frequencySnapshot_haar μ (gapFrequency k i j) (gapFrequency_measurable k i j) ?_
  intro m hm
  apply gap_projection_ac k i j hij _ hμ (fun l => (m l:ℝ))
  intro hz
  apply hm
  funext l
  have hl : (m l:ℝ)=0 := congrFun hz l
  change m l=0
  exact_mod_cast hl

/-- On the original product Gaussian, one specified candidate with winding
n and closing angle x has the full off-pair limiting distribution. -/
theorem gaussian_high_winding_snapshot (k : ℕ) (i j : Level k) (hij : i≠j) (x : ℝ) :
    let μ : ProbabilityMeasure (Coupling k) := ⟨centredProductGaussian _ 1,inferInstance⟩
    Tendsto (fun n : ℕ => gapSnapshot k i j μ (2*π*((n:ℝ)-x))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  intro μ
  have ht : Tendsto (fun n : ℕ => (n:ℝ)-x) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (b+x)] with n hn
    linarith only [hn]
  exact (gapSnapshot_haar k i j hij μ (productGaussian_absolutelyContinuous _ one_ne_zero _)).comp
    (ht.const_mul_atTop two_pi_pos)

#print axioms gaussian_high_winding_snapshot
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
