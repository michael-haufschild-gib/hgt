import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ArcLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Every free affine period has infinitely many fine scalar visits -/

open Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FineAffordability
open SharpOccupation EntrySensitivity.PrescribedCharacters.VisitIndices
noncomputable section

theorem free_scalar_visits {N : ℕ} (H : selfAdjoint (SharpOccupation.Register N))
    (b : Fin N → Bool) (a τ : ℝ) (hf : FreeAtStep (projectiveFrequency H.2.isHermitian.eigenvalues b) τ)
    {ε : ℝ} (he : 0<ε) :
    {n : ℕ | HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val (a+(n:ℝ)*τ))}.Infinite := by
  let δ := min ε (1/10:ℝ)
  have hd : 0<δ := lt_min he (by norm_num)
  have hs : δ<sqrt 2 := (min_le_right ..).trans_lt (by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2])
  let r := physicalArc δ
  have hr := (physicalArc_spec hd hs).1
  let E := H.2.isHermitian.eigenvalues
  let A := visitSet H 0 δ
  have heq : arcTimes E (fun _ => 0) r=A := by
    ext t
    have ht : 2*π*r=4*arcsin (δ/2) := by dsimp only [r,physicalArc]; field_simp; ring
    have hneg : t∈arcTimes E (fun _ => 0) r ↔
        HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val (-t)) := by
      let z : Icc (0:ℝ) 2 := ⟨δ,hd.le,(min_le_right ..).trans (by norm_num)⟩
      change _ ↔ HasProjectiveCircuitApproximation N (z:ℝ) 0 (unitaryEvolution H.val (-t))
      rw [zeroGateApproximation_iff_enclosingArc H (-t) z]
      change spectralEnclosingArcLength (fun j => t*E j+0)≤2*π*r ↔
        spectralEnclosingArcLength (fun j => -(-t*E j))≤4*arcsin (δ/2)
      simp only [add_zero,neg_mul,neg_neg,ht]
    constructor
    · intro hh
      simpa only [neg_neg] using HasProjectiveCircuitApproximation.neg_time H (hneg.mp hh)
    · intro hh
      exact hneg.mpr (HasProjectiveCircuitApproximation.neg_time H hh)
  have hl := arc_timeLaw E (fun _ => 0) b ⟨r,hr.1.le,hr.2.le⟩ a τ hf
  rw [heq] at hl
  have hm : MeasurableSet A := by
    rw [show A={t | orbitCircuitDistance H 0 t≤δ} from Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist ..]
    exact (isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const).measurableSet
  have hpos : 0<zeroGateArcDensity (Fintype.card (Fin N → Bool)) r :=
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (pow_pos hr.1 _)
  apply (return_index_spacing (fun j : ℕ => a+(j:ℝ)*τ) A hm hpos hl).1.mono
  rintro n ⟨z,hz,C,hC,herr⟩
  exact ⟨z,hz,C,hC,herr.trans (min_le_left ..)⟩

#print axioms free_scalar_visits
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FineAffordability
