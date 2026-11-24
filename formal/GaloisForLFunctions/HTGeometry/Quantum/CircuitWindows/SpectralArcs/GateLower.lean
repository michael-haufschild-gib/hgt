import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Products
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Necessary joint accuracy for two short circuit visits -/

open Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralArcs
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Chord obtained by bisecting the angle of an operator error. -/
def halfChord (d : ℝ) := 2*sin (arcsin (d/2)/2)

theorem budget_antitone {n : ℕ} (H : selfAdjoint (Reg n)) {i j : ℕ} (hij : i≤j) (v : ℝ) :
    orbitCircuitDistance H j v ≤ orbitCircuitDistance H i v := by
  obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr
    (le_rfl : orbitCircuitDistance H i v ≤ _)
  exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp ⟨z,hz,C,hC.trans hij,hfit⟩

/-- Cancelling two affordable endpoints bounds the angle of their lag,
even when the two fitted circuits have different budgets. -/
theorem halfChord_le_pair {n : ℕ} (H : selfAdjoint (Reg n)) (i j : ℕ) (v t : ℝ) :
    halfChord (orbitCircuitDistance H (i+j) t) ≤
      max (orbitCircuitDistance H i v) (orbitCircuitDistance H j (v+t)) := by
  let m := max (orbitCircuitDistance H i v) (orbitCircuitDistance H j (v+t))
  let θ := arcsin (m/2)
  let δ := arcsin (orbitCircuitDistance H (i+j) t/2)
  have hθ : 0≤θ := arcsin_nonneg.mpr (div_nonneg
    ((Metric.infDist_nonneg : 0 ≤ orbitCircuitDistance H i v).trans (le_max_left ..)) zero_le_two)
  have hδ : 0≤δ := arcsin_nonneg.mpr (div_nonneg Metric.infDist_nonneg zero_le_two)
  have upper (k u) := (budget_antitone H (Nat.zero_le k) u).trans_lt (orbitCircuitDistance_zeroGate_lt_two H u)
  have hm : m<2 := max_lt (upper i v) (upper j (v+t))
  have hm' : 0 ≤ m := (Metric.infDist_nonneg : 0 ≤ orbitCircuitDistance H i v).trans (le_max_left ..)
  have hs : 2*sin θ=m := by
    dsimp only [θ]; rw [sin_arcsin (by linarith only [hm']) (by linarith only [hm])]; ring
  have hle : δ/2≤θ := by
    by_cases h : π/2≤2*θ
    · have hcap : δ ≤ π/2 := arcsin_le_pi_div_two _
      linarith only [hcap,h]
    have hfit (k u) (hku : orbitCircuitDistance H k u ≤ m) :
        HasProjectiveCircuitApproximation n (2*sin θ) k (unitaryEvolution H.val u) :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr (hs.symm ▸ hku)
    have hlag := AngularError.affordable_add_angle H hθ (le_of_not_ge h)
      (HasProjectiveCircuitApproximation.neg_time H (hfit i v (le_max_left ..)))
      (hfit j (v+t) (le_max_right ..))
    rw [show -v+(v+t)=t by abel] at hlag
    have he : orbitCircuitDistance H (i+j) t ≤ 2*sin (2*θ) :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hlag
    have hδ' : δ ≤ arcsin (sin (2*θ)) := arcsin_le_arcsin (by linarith only [he])
    rw [arcsin_sin (by linarith only [hθ,pi_pos]) (le_of_not_ge h)] at hδ'
    linarith only [hδ']
  have hh : sin (δ/2) ≤ sin θ := monotoneOn_sin
    ⟨by linarith only [hδ,pi_pos],hle.trans (arcsin_le_pi_div_two _)⟩
    ⟨by linarith only [hθ,pi_pos],arcsin_le_pi_div_two _⟩ hle
  change 2*sin (δ/2) ≤ m
  linarith only [hh,hs]

#print axioms halfChord_le_pair
end
end GaloisForLFunctions.HTGeometry.SpectralArcs
