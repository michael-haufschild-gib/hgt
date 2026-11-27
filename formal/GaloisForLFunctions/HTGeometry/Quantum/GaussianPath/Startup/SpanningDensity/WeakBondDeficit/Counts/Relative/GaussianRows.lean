import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.RelativeTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.BoxTails

/-! # Relative count tails on a progression of physical Gaussian bonds -/
open MeasureTheory Finset Set Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open Counts BlockDilations.AdaptiveCuts
open private row_law from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.BoxTails
noncomputable section

/-- The exponent is proportional to the expected count even when the
bond radius tends to zero. Distinct progressions may overlap. -/
theorem relative_box_tail (s d m : ℕ) (hd : 0<d) (h : ℝ) :
    let M := bondLaw.real (weakBond h)*m
    pathPauliDisorderLaw.real {ω | (boxCount ω s d m h:ℝ)≤M/4 ∨ 4*M≤(boxCount ω s d m h:ℝ)}
      ≤2*exp (-M/4) := by
  classical
  intro M
  let B := weakBond h
  let A := {x : Fin m→(Fin 9→ℝ) | (sampleCount B x:ℝ)≤M/4 ∨ 4*M≤(sampleCount B x:ℝ)}
  have hB : MeasurableSet B := weakBond_measurable _
  have hcount : Measurable (fun x : Fin m→(Fin 9→ℝ) => (sampleCount B x:ℝ)) := by
    have calcCount (x : Fin m→(Fin 9→ℝ)) :
        (∑ j, B.indicator (fun _ => (1:ℝ)) (x j))=(sampleCount B x:ℝ) := by
      simp only [sampleCount,Set.indicator_apply,Finset.sum_boole]
    simp_rw [←calcCount]
    exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hB).comp (measurable_pi_apply i)
  have hA : MeasurableSet A := (measurableSet_le hcount measurable_const).union (measurableSet_le measurable_const hcount)
  have he := (row_law s d m hd).measureReal_preimage hA.nullMeasurableSet
  rw [Measure.infinitePi_eq_pi] at he
  exact he.le.trans (by simpa only [Fintype.card_fin] using relative_sample_tail (I:=Fin m) bondLaw B hB)

#print axioms relative_box_tail
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
