import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Reflection of circuit distances about a physical return -/

open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrescribedTimes
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Reflecting a time about an affordable date adds at most the closing
circuit's budget and error. Applying the same reflection twice gives the
reverse bound, valid at every budget below the original one. -/
theorem reflected_distances {n s : ℕ} (H : selfAdjoint (Reg n)) {v e : ℝ}
    (hv : HasProjectiveCircuitApproximation n e s (unitaryEvolution H.val v))
    (j : ℕ) (t : ℝ) :
    orbitCircuitDistance H (s+j) (v-t) ≤ e + orbitCircuitDistance H j t ∧
    ∀ k, s+k ≤ j → orbitCircuitDistance H j t - e ≤ orbitCircuitDistance H k (v-t) := by
  have step (b : ℕ) (u : ℝ) :
      orbitCircuitDistance H (s+b) (v-u) ≤ e + orbitCircuitDistance H b u := by
    have hu := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val u)
      b (orbitCircuitDistance H b u)).mpr le_rfl
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      (affordable_add_time H hv (hu.neg_time H))
  refine ⟨step j t, ?_⟩
  intro k hk
  have h := step k (v-t)
  rw [sub_sub_cancel] at h
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr h
  have h' : orbitCircuitDistance H j t ≤ e + orbitCircuitDistance H k (v-t) :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans hk,he⟩
  linarith only [h']

/-- A first visit after the crossing is attained at crossing plus elapsed
wait, even for budgets that already fit at the crossing. -/
theorem first_wait_fit (n P s : ℕ) (x : PrefixIndex n → ℝ) :
    let σ := crossingOrigin n P (9/80) x
    let Δ := crossingWait n P s x
    0 ≤ Δ ∧ pathGateDistance n s x (σ+Δ) ≤ 1/10 := by
  intro σ Δ
  obtain ⟨v,hv,he⟩ := (crossingWait_le_iff n P s x Δ).mp le_rfl
  have hmin : Δ ≤ v-σ := (crossingWait_le_iff n P s x (v-σ)).mpr
    ⟨v,⟨hv.1,by change v ≤ σ+(v-σ); linarith⟩,he⟩
  have hlo : σ ≤ v := hv.1
  have hup : v ≤ σ+Δ := hv.2
  have hdate : σ+Δ=v := by linarith only [hmin,hup]
  exact ⟨by linarith only [hlo,hup],hdate.symm ▸ he⟩

#print axioms reflected_distances
#print axioms first_wait_fit
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
