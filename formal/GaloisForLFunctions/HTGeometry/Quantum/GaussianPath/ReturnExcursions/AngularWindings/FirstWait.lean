import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.InverseTime
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.Reflection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.PhysicalCenters

/-! # A single lifted circuit winding at the original elapsed first wait -/

open MeasureTheory Set Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
open PrescribedTimes ShortWindows SharpOccupation
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
noncomputable section

/-- The actual first affordable visit after the plateau crossing supplies a net circuit and
one integer for each eigenline. Subtracting the phase at the crossing leaves the elapsed
wait as the only clock. The same winding passes every time-free linear test. -/
theorem gaussian_first_wait_winding :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k s : ℕ,
      let K := k+3
      let X := prefixPoint k ω
      let P := nearHilbertContinuousCircuitBudget K
      let σ := crossingOrigin (k+1) P (9/80) X
      let Δ := crossingWait (k+1) P s X
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian K) X
      let A (i : Level k) := -E i/(2*π)
      let x := physicalArc (7/20)
      ∃ W ∈ atMostQuarterCircuitNet K s, ∃ m : Level k → ℤ,
        let b (i : Level k) := lineTurns k W.val X i-σ*A i+(m i:ℝ)
        (∃ p : ℝ, ∀ i, |Δ*A i-b i-p|≤x/2) ∧
        (∀ T U : ℝ, 0<T → Δ∈Icc T U → inverseWindow A b x T U) ∧
        ∀ w : Level k → ℝ, (∑ i, w i)=0 → (∑ i, w i*b i)=0 →
          Δ*|∑ i, w i*A i| ≤ (x/2)*∑ i, |w i| := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hsimple k s
  intro K X P σ Δ E A x
  let u := pathPauliDisorderShell ω (k+1)
  let H := pathHamiltonian u
  have hfirst := ElapsedWindow.first_wait_fit (k+1) P s X
  obtain ⟨hΔ,hgate⟩ := hfirst
  have hvisit := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr hgate
  rw [show numberedGenerator (k+1) X=H from numberedGenerator_shell u] at hvisit
  obtain ⟨c,hc,C,hC,herr⟩ := hvisit
  obtain ⟨W,hW,hnear⟩ := atMostQuarterCircuitNet_cover C hC
  have hf : ‖unitaryEvolution H (σ+Δ)-c • W.val‖ ≤ 7/20 := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (c • C.eval.val) _).trans
    rw [←smul_sub,norm_smul,hc,one_mul]
    rw [dist_eq_norm] at hnear
    change ‖unitaryEvolution H (σ+Δ)-c • C.eval.val‖ ≤ 1/10 at herr
    linarith only [herr,hnear]
  have hε : (7/20:ℝ) ∈ Ioo (0:ℝ) (sqrt 2) := by
    constructor
    · norm_num
    · exact ((by norm_num : (7/20:ℝ)<1).trans_le (Real.one_le_sqrt.mpr (by norm_num)))
  have hx := (physicalArc_spec hε.1 hε.2).1
  have harc := physical_corrected_arc k ω W.val W.2 (σ+Δ) hc hε (hsimple k).injective hf
  change (fun i => (((σ+Δ)*A i-lineTurns k W.val X i:ℝ):UnitAddCircle))∈enclosingUnitArc x at harc
  obtain ⟨m,p,hp⟩ := winding_of_arc A (lineTurns k W.val X) ⟨x,hx.1.le,hx.2.le⟩ harc
  refine ⟨W,hW,m,?_⟩
  intro b
  have hh (i) : |Δ*A i-b i-p| ≤ x/2 := by
    rw [show Δ*A i-b i-p=(σ+Δ)*A i-(lineTurns k W.val X i+(m i:ℝ))-p by dsimp only [b]; ring]
    exact hp i
  refine ⟨⟨p,hh⟩,?_,?_⟩
  · intro T U hT hwin
    exact (winding_iff_inverse A b hT (hwin.1.trans hwin.2)).mp ⟨Δ,hwin,p,hh⟩
  · intro w hw hb
    exact winding_test (U:=Δ) A b w hΔ hw hb ⟨Δ,⟨le_rfl,le_rfl⟩,p,hh⟩

#print axioms gaussian_first_wait_winding
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
