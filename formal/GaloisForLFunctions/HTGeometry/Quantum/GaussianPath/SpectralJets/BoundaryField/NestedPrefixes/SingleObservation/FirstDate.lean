import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation.ScalarReading
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.FirstPrecisionReturn
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.FirstTravel

/-! # One larger-prefix reading at the smaller prefix's first post-crossing return -/

open Set Filter MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
open PrecisionReturns SharpOccupation PrescribedTimes PrescribedTimes.ShortWindows LocalPatches.PhysicalSpeed
noncomputable section

private theorem small_generator (j : ℕ) (ω : PathPauliDisorder) :
    prefixGenerator (j+1) (prefixPoint j ω)=originalGenerator j ω :=
  Subtype.ext (numberedGenerator_shell _)

/-- The size threshold for existence of a first crossing can be chosen
before drawing the Gaussian chain: the entropy test depends only on size. -/
private theorem eventually_crossing_positive :
    ∀ᶠ j : ℕ in atTop, ∀ᵐ ω ∂pathPauliDisorderLaw,
      0<crossingOrigin (j+1) (nearHilbertContinuousCircuitBudget (j+3)) (9/80) (prefixPoint j ω) := by
  filter_upwards [gaussian_capped_first_passage] with j hj
  filter_upwards [hj] with ω hw
  let x := prefixPoint j ω
  let R := 1+∑ i, |x i|
  have hsum : 0≤∑ i, |x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hR : 0<R := add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcap (i) : |x i|≤R := (Finset.single_le_sum (f:=fun l => |x l|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  have h := (hw R hR hcap).trans_le (min_le_left ..)
  exact (div_nonneg (by unfold travelProduct LocalPatches.localCrossingWidth; positivity) hR.le).trans_lt h

/-- Fix any sufficiently large smaller register and any strict larger
extension. At the very first smaller-register dip following its true 9/80
crossing, the larger register fits the empty circuit with probability
tending to its exact Haar mass as the smaller return error decreases. -/
theorem gaussian_single_first_date :
    ∀ᶠ j : ℕ in atTop, ∀ (k s : ℕ), j<k → 2*s<j+3 →
      ∀ (δ : ℕ → ℝ), (∀ n, 0<δ n) → Tendsto δ atTop (𝓝[>] (0:ℝ)) →
      ∀ ε∈Ioo (0:ℝ) (sqrt 2),
        let σ (ω : PathPauliDisorder) := crossingOrigin (j+1) (nearHilbertContinuousCircuitBudget (j+3))
          (9/80) (prefixPoint j ω)
        let v (n : ℕ) (ω : PathPauliDisorder) := firstVisit (originalGenerator j ω) (σ ω) s (δ n)
        Tendsto (fun n => pathPauliDisorderLaw.real {ω | orbitCircuitDistance (originalGenerator k ω) 0
          (v n ω)≤ε}) atTop (𝓝 (zeroGateArcDensity (2^(k+3)) (physicalArc ε))) := by
  filter_upwards [eventually_crossing_positive] with j hσ
  intro k s hj hs δ hδ hlim ε he σ v
  let a := crossingOrigin (j+1) (nearHilbertContinuousCircuitBudget (j+3)) (9/80)
  let t (n : ℕ) (ω : PathPauliDisorder) := firstVisit (prefixGenerator (j+1) (prefixPoint j ω))
    (a (prefixPoint j ω)) s (δ n)
  have hsame (n : ℕ) (ω : PathPauliDisorder) : t n (eraseTerminal k ω)=v n ω := by
    dsimp only [t,v,σ,prefixPoint,a]
    rw [shell_before hj]
    exact congrArg (fun H => firstVisit H _ s (δ n)) (small_generator j ω)
  have hm (n : ℕ) : Measurable (t n) := (measurable_first_visit _ _ a
    (measurable_crossingOrigin _ _ _) (hδ n)).comp (gaussian_pauli_prefix_coordinates_law (j+1)).measurable
  have hdiv : ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n => t n (eraseTerminal k ω)) atTop atTop := by
    filter_upwards [hσ,gaussian_first_return_precision_exponent] with ω hpos hω
    obtain ⟨hmin,hexp,_⟩ := hω j (σ ω) hpos s hs
    have hpow : 3≤2^(j+3) := (by decide : 3≤2^3).trans (Nat.pow_le_pow_right (by decide) (by omega))
    have h := FieldWindows.diverges_of_precision_exponent
      (by exact_mod_cast (show 0<2^(j+3)-2 by omega))
      (fun η hη => hpos.trans_le (hmin η hη).1.1) hexp
    simpa only [hsame,v] using h.comp hlim
  simpa only [hsame] using scalar_reading k t hm hdiv he

#print axioms gaussian_single_first_date
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
