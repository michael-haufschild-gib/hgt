import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Time gained from operator clearance at a first contact -/

open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrecisionReturns
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A strict interior fit at an observed date advances the first visit by at
least its error margin divided by one plus half the spectral width, capped
by the entire elapsed time since the observing origin. -/
theorem first_visit_margin {N : ℕ} (H : selfAdjoint (Reg N)) (a : ℝ) (s : ℕ) {t e : ℝ}
    (he : 0<e) (hat : a≤t) (hfit : orbitCircuitDistance H s t≤e) :
    let r := min (t-a) ((e-orbitCircuitDistance H s t)/(1+circuitHamiltonianSpectralWidth H/2))
    firstVisit H a s e ≤ t-r := by
  intro r
  obtain ⟨L,hL,hLip⟩ := orbitCircuitDistance_lipschitz_spectralWidth H s
  have hden : 0<1+circuitHamiltonianSpectralWidth H/2 := by rw [←hL]; positivity
  have hr : 0≤r := le_min (sub_nonneg.mpr hat) (div_nonneg (sub_nonneg.mpr hfit) hden.le)
  have hleft : r≤t-a := min_le_left ..
  have hgain := (le_div_iff₀ hden).mp (show r≤_ from min_le_right ..)
  have hd := hLip.dist_le_mul (t-r) t
  rw [Real.dist_eq,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_nonneg hr] at hd
  apply (firstVisit_isLeast H a s he).2
  refine ⟨by linarith only [hleft], (hasProjectiveCircuitApproximation_iff_infDist ..).mpr ?_⟩
  rw [hL] at hd
  change orbitCircuitDistance H s (t-r)≤e
  linarith only [(abs_le.mp hd).2,hgain,hr]

/-- Interior clearance at the smaller budget's first date strictly advances
the comparison budget's first date from the same outside origin. -/
theorem strict_of_first_margin {N : ℕ} (H : selfAdjoint (Reg N)) (a : ℝ) (s j : ℕ) {e : ℝ}
    (he : 0<e) (hfar : e<orbitCircuitDistance H s a)
    (hfit : orbitCircuitDistance H j (firstVisit H a s e)<e) :
    firstVisit H a j e < firstVisit H a s e := by
  let v := firstVisit H a s e
  have hs := (firstVisit_isLeast H a s he).1
  have hd : orbitCircuitDistance H s v≤e := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hs.2
  have hav : a<v := hs.1.lt_of_ne fun h => hfar.not_ge (h.symm ▸ hd)
  have hden : 0<1+circuitHamiltonianSpectralWidth H/2 := by
    obtain ⟨L,hL,_⟩ := orbitCircuitDistance_lipschitz_spectralWidth H j
    rw [←hL]; positivity
  exact (first_visit_margin H a j he hav.le hfit.le).trans_lt
    (sub_lt_self _ (lt_min (sub_pos.mpr hav) (div_pos (sub_pos.mpr hfit) hden)))

#print axioms first_visit_margin
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
