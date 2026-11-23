import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.AffineSignal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondSections

/-! # Geometric bond-signal thresholds uniform over every exterior -/
open Matrix MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- A bond is detectable at threshold b^L up to physical time L.
The base is independent of prefix length, bond and exterior fields. -/
theorem geometric_bond_sections {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    ∃ b > 0, ∀ L : ℕ, 0 < L → ∀ (n : ℕ) (e : Fin (n+1)) (u : PathShell n) (t : ℝ),
      t∈Set.Icc a (L:ℝ) →
      let H := pathHamiltonian (exteriorShell u e)
      let P := finitePauliMatrix (pathWord (bondLabel e))
      let Y := finitePauliMatrix (bondReporter e)
      let S := fun i => finitePauliMatrix (pathWord ((localNumbering e i).val))
      (Measure.pi (fun _ : Fin (localLabels e).card => gaussianReal 0 1))
        {x | |signal (affineHamiltonian H S x) Y (Complex.I • (P*Y)) t|≤b^L} ≤ ENNReal.ofReal η := by
  classical
  choose r hr h using fun m => geometric_affine_signal m (π/(4*a)) (h:=1) zero_lt_one hη
  let I := Finset.range 43
  have hI : I.Nonempty := ⟨0,by decide⟩
  let b := I.inf' hI r
  have hb : 0 < b := (Finset.lt_inf'_iff hI).mpr (fun i _ => hr i)
  refine ⟨b,hb,?_⟩
  intro L hL n e u t ht H P Y S
  let m := (localLabels e).card
  obtain ⟨hY,hB,hnY,hnB,v,hv,hsig⟩ := bond_affine_witness ha ht.1 u e
  have hsmall := h m L hL (Fin (n+2) → Bool) H Y (Complex.I • (P*Y)) S
    (isSelfAdjoint_pathHamiltonian _) hY hB hnY hnB
    (fun i => (finitePauliMatrix_isHermitian _).isSelfAdjoint) (fun i => (norm_finitePauliMatrix _).le)
    t (by simpa only [abs_of_pos (ha.trans_le ht.1)] using ht.2) v hv (by rwa [one_pow])
  have hm : m∈I := Finset.mem_range.mpr (Nat.lt_succ_of_le (pathOverlaps_card_le _))
  exact (measure_mono fun x hx => hx.trans (pow_le_pow_left₀ hb.le (Finset.inf'_le r hm) L)).trans hsmall

#print axioms geometric_bond_sections
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
