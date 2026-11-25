import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.CircuitColumns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.CenteredMesh
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent

/-! # Measurable physical circuit corrections in sorted spectral order -/

open Matrix MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open PrescribedTimes SharpOccupation
noncomputable section

/-- The entry used for a sorted level lives in the physical qubit basis
of the actual circuit. Only the eigenline labels are renumbered. -/
def lineEntry (k : ℕ) (W : Register (k+3)) (x : Coupling k) (l : Level k) :=
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
  let p := qubitConfigFin (k+3)
  circuitEntry (E ∘ p) (numberedGenerator (k+1) x) W (p.symm l)

def lineTurns (k : ℕ) (W : Register (k+3)) (x : Coupling k) (l : Level k) :=
  (lineEntry k W x l).arg/(2*π)

theorem measurable_lineTurns (k : ℕ) (W : Register (k+3)) (l : Level k) :
    Measurable (fun x => lineTurns k W x l) := by
  let p := qubitConfigFin (k+3)
  have hE := (continuous_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))).measurable
  have hH : Continuous (numberedGenerator (k+1)) := by unfold numberedGenerator; fun_prop
  have hh (a b) : Measurable (fun x => numberedGenerator (k+1) x a b) :=
    ((continuous_apply b).comp ((continuous_apply a).comp hH)).measurable
  have h := measurable_circuitEntry hh
    (measurable_pi_lambda _ fun j => (measurable_pi_apply (p j)).comp hE) W (p.symm l)
  exact (Complex.measurable_arg.comp h).div_const _

theorem measurable_centerOffset (k : ℕ) (W : Register (k+3)) (i j : Level k) :
    Measurable (fun x => centerOffset i j (lineTurns k W x)) := by
  apply measurable_pi_lambda
  intro l
  exact (AddCircle.continuous_mk' (1:ℝ)).measurable.comp
    ((measurable_lineTurns k W j).sub (measurable_lineTurns k W l.val))

/-- Evaluating the physical evolution against a circuit forces the sorted,
corrected torus packet to fit the short angular arc at exactly that time. -/
theorem physical_corrected_arc (k : ℕ) (ω : PathPauliDisorder) (W : Register (k+3))
    (hW : W∈unitary (Register (k+3))) (t : ℝ) {c : ℂ} (hc : ‖c‖=1)
    {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let u := pathPauliDisorderShell ω (k+1)
    let H := pathHamiltonian u
    let X : Coupling k := fun l => u (pathCoeffEquiv (k+1) l)
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) X
    Function.Injective (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues →
    ‖unitaryEvolution H t-c • W‖≤ε →
    (fun l => ((t*(-E l/(2*π))-lineTurns k W X l:ℝ):UnitAddCircle))∈enclosingUnitArc (physicalArc ε) := by
  intro u H X E hi hfit
  let p := qubitConfigFin (k+3)
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  obtain ⟨e,he⟩ := physical_sorted_order k ω hi
  let σ := p.trans e.symm
  have hl (j) : hH.eigenvalues (σ j)=E (p j) := by
    simpa only [σ,Equiv.trans_apply,e.apply_symm_apply] using he (e.symm (p j))
  let v := fun j => hermitianEigenBasis H hH (σ j)
  have hbase : IsOrthoEigenBasis H v (E ∘ p) := by
    have hb := (isOrthoEigenBasis_hermitian H hH).reindex σ
    rwa [show (fun j => hH.eigenvalues (σ j))=E ∘ p from funext hl] at hb
  have hinj : Function.Injective (E ∘ p) := by
    intro a b h
    exact σ.injective (hi ((hl a).trans (h.trans (hl b).symm)))
  let B (l : Level k) := (lineEntry k W X l).arg
  let θ (l : Level k) := -t*E l-B l
  have hchord (l : Level k) : ‖Complex.exp ((θ l:ℂ)*Complex.I)-Complex.exp ((c.arg:ℂ)*Complex.I)‖≤ε := by
    have h := circuit_column_chord hbase hinj hW t hc hε.2 hfit (p.symm l)
    have hh : numberedGenerator (k+1) X=H := numberedGenerator_shell u
    simpa only [θ,B,lineEntry,p,hh,Function.comp_apply,Equiv.apply_symm_apply,E] using h
  have ha := enclosing_of_common_chord θ c.arg hε hchord
  have hangle (l : Level k) : t*(-E l/(2*π))-lineTurns k W X l=θ l/(2*π) := by
    dsimp only [lineTurns,θ,B]
    ring
  simpa only [hangle] using ha

#print axioms physical_corrected_arc
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
