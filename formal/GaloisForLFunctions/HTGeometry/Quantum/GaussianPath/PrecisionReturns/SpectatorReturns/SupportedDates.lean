import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PhaseCenters
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.FirstVisit

/-! # First fitting date with a prescribed number of active wires -/

open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section
private abbrev Basis (N : ℕ) := unitaryGroup (Fin N→Bool) ℂ

/-- Dates at which the evolution is within ε of a unitary acting on at
most b wires in some basis. The local unitary includes the free global phase. -/
def supportedDates {N : ℕ} (H : selfAdjoint (Register N)) (b : ℕ) (ε : ℝ) : Set ℝ :=
  {t | ∃ S : Finset (Fin N), S.card ≤ b ∧ ∃ V B : Basis N,
    IsSiteSupported S B.val ∧ ‖V.val*unitaryEvolution H.val t*star V.val-B.val‖≤ε}

private theorem support_closed {N : ℕ} (S : Finset (Fin N)) :
    IsClosed {B : Register N | IsSiteSupported S B} := by
  let L := liftLocalMatrixLinear (fun _ : Fin N => Bool) S
  have he : {B : Register N | IsSiteSupported S B} = (L.range : Set (Register N)) := by
    ext B
    constructor
    · intro h
      obtain ⟨P,hP⟩ := exists_liftLocalMatrix_of_isSiteSupported h
      exact ⟨P,hP.symm⟩
    · rintro ⟨P,rfl⟩
      exact isSiteSupported_liftLocalMatrix S P
  rw [he]
  exact Submodule.closed_of_finiteDimensional _

theorem isClosed_supportedDates {N : ℕ} (H : selfAdjoint (Register N)) (b : ℕ) (ε : ℝ) :
    IsClosed (supportedDates H b ε) := by
  letI : CompactSpace (Basis N) := isCompact_iff_compactSpace.mp isCompact_matrixUnitaryGroup
  let P := ℝ × (Basis N × Basis N)
  let F (S : Finset (Fin N)) : Set P :=
    {p | IsSiteSupported S p.2.2.val ∧ ‖p.2.1.val*unitaryEvolution H.val p.1*star p.2.1.val-p.2.2.val‖≤ε}
  have hV : Continuous (fun p : P => p.2.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hB : Continuous (fun p : P => p.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hu : Continuous (fun p : P => unitaryEvolution H.val p.1) :=
    continuous_unitaryEvolution.comp (continuous_const.prodMk continuous_fst)
  have hF (S : Finset (Fin N)) : IsClosed (F S) :=
    ((support_closed S).preimage hB).inter
      (isClosed_le (((hV.mul hu).mul hV.star).sub hB).norm continuous_const)
  let I := {S : Finset (Fin N) // S.card ≤ b}
  have he : supportedDates H b ε = ⋃ S : I, Prod.fst '' F S.val := by
    ext t
    constructor
    · rintro ⟨S,hs,V,B,hS,h⟩
      exact mem_iUnion.mpr ⟨⟨S,hs⟩,(t,V,B),⟨hS,h⟩,rfl⟩
    · intro h
      obtain ⟨S,⟨t,V,B⟩,hF,rfl⟩ := mem_iUnion.mp h
      exact ⟨S.val,S.property,V,B,hF⟩
  rw [he]
  exact isClosed_iUnion_of_finite fun S => isClosedMap_fst_of_compactSpace _ (hF S.val)

/-- Earliest supported fit after the observation origin. -/
def firstSupportedDate {N : ℕ} (H : selfAdjoint (Register N)) (a : ℝ) (b : ℕ) (ε : ℝ) :=
  sInf (Ici a ∩ supportedDates H b ε)

theorem firstSupportedDate_isLeast {N : ℕ} (H : selfAdjoint (Register N)) (a : ℝ) (b : ℕ)
    {ε : ℝ} (he : 0<ε) : IsLeast (Ici a ∩ supportedDates H b ε) (firstSupportedDate H a b ε) := by
  obtain ⟨ha,z,hz,C,hc,hfit⟩ := (firstVisit_isLeast H a 0 he).1
  let B := z • C.eval.val
  have hb : B ∈ unitary (Register N) := by
    have h : star z*z=1 := by rw [Complex.star_def,Complex.conj_mul',hz]; norm_num
    apply Unitary.mem_iff.mpr
    simp only [B,star_smul,smul_mul_smul_comm,C.eval.property.1,C.eval.property.2,
      h,(mul_comm z (star z)).trans h,one_smul,and_self]
  have hcard := C.card_touchedSites_le
  have hm : firstVisit H a 0 ε ∈ supportedDates H b ε :=
    ⟨C.touchedSites,by omega,1,⟨B,hb⟩,C.isSiteSupported_touchedSites.complex_smul z,by
      simpa only [OneMemClass.coe_one,one_mul,star_one,mul_one] using hfit⟩
  have hne : (Ici a ∩ supportedDates H b ε).Nonempty := ⟨_,ha,hm⟩
  have hl : BddBelow (Ici a ∩ supportedDates H b ε) := ⟨a,fun _ ht => ht.1⟩
  exact ⟨(isClosed_Ici.inter (isClosed_supportedDates H b ε)).csInf_mem hne hl,fun _ ht => csInf_le hl ht⟩

#print axioms firstSupportedDate_isLeast
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
