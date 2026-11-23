import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability

/-! # First circuit visit with a freely chosen eigenbasis -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
private abbrev Basis (N : ℕ) := unitaryGroup (Fin N → Bool) ℂ

/-- Dates at which some unitary conjugate admits the requested budget. -/
def affordableDates {N : ℕ} (H : selfAdjoint (Reg N)) (s : ℕ) (ε : ℝ) : Set ℝ :=
  {t | ∃ W : Basis N, HasProjectiveCircuitApproximation N ε s (W.val*unitaryEvolution H.val t*star W.val)}

/-- Compactness of the basis group preserves closedness when projecting
the joint circuit-fit condition onto the physical time axis. -/
theorem closed_affordableDates {N : ℕ} (H : selfAdjoint (Reg N)) (s : ℕ) (ε : ℝ) :
    IsClosed (affordableDates H s ε) := by
  letI : CompactSpace (Basis N) := isCompact_iff_compactSpace.mp isCompact_matrixUnitaryGroup
  let U (p : ℝ × Basis N) := p.2.val*unitaryEvolution H.val p.1*star p.2.val
  have hcW : Continuous (fun p : ℝ × Basis N => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hcU : Continuous U := (hcW.mul (continuous_unitaryEvolution.comp
    (continuous_const.prodMk continuous_fst))).mul hcW.star
  let F := {p : ℝ × Basis N | Metric.infDist (U p) (phaseCircuitMatrixImageAtMost N s) ≤ ε}
  have hF : IsClosed F := isClosed_le ((Metric.continuous_infDist_pt _).comp hcU) continuous_const
  have he : affordableDates H s ε = Prod.fst '' F := by
    ext t
    constructor
    · rintro ⟨W,hW⟩
      exact ⟨(t,W),(hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hW,rfl⟩
    · rintro ⟨⟨u,W⟩,h,rfl⟩
      exact ⟨W,(hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr h⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hF

/-- Earliest date at or after a with a fitting conjugate. -/
def firstVisit {N : ℕ} (H : selfAdjoint (Reg N)) (a : ℝ) (s : ℕ) (ε : ℝ) : ℝ :=
  sInf (Ici a ∩ affordableDates H s ε)

theorem firstVisit_isLeast {N : ℕ} (H : selfAdjoint (Reg N)) (a : ℝ) (s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsLeast (Ici a ∩ affordableDates H s ε) (firstVisit H a s ε) := by
  obtain ⟨⟨hu,hv⟩,_⟩ := PrecisionReturns.firstVisit_isLeast H a s hε
  have hne : (Ici a ∩ affordableDates H s ε).Nonempty :=
    ⟨_,hu,1,by simpa only [OneMemClass.coe_one,one_mul,star_one,mul_one] using hv⟩
  have hb : BddBelow (Ici a ∩ affordableDates H s ε) := ⟨a,fun _ h => h.1⟩
  exact ⟨(isClosed_Ici.inter (closed_affordableDates H s ε)).csInf_mem hne hb,fun _ ht => csInf_le hb ht⟩

#print axioms firstVisit_isLeast
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation
