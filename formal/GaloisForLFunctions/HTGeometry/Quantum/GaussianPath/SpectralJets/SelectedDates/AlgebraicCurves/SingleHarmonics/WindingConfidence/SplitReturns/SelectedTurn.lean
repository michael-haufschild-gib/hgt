import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns.Multiples

/-! # A prescribed full turn with excess scalar return probability -/

open Finset Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open PrescribedTimes WeakBonds WeakBonds.NormalizedRadius
noncomputable section

/-- Scalar probability on the register's own spectral clock, restricted
to a bandwidth of at least two in physical units. -/
def fullTurnMass (n k : ℕ) (ε : ℝ) :=
  (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real {x |
    2≤circuitHamiltonianSpectralWidth (prefixGenerator n x) ∧
    pathGateDistance n 0 x (fullTurn n k x)≤ε}

/-- Some deterministic integer multiple has at least the Gaussian
weak-bond mass divided by the number of candidate multiples. Its
preceding extremal antipode sees the return within half a period. -/
theorem gaussian_selected_full_turn (n m Q : ℕ) (a : Fin (n+1)) {δ : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤1) :
    let M : ℕ := (Q+1)^(2^(leftBlock a).card+2^(rightBlock a).card)
    let T := π*((m:ℝ)+1)*(M:ℝ)
    ∃ q : ℕ, 1≤q ∧ q≤M ∧ bulkMass*(2*gaussianDensityFloor*δ)^9 ≤
      (M:ℝ)*fullTurnMass n ((m+1)*q) (4*π/(Q+1:ℝ)+9*T*δ) := by
  intro M T
  have hM : 0<M := pow_pos (Nat.succ_pos Q) _
  letI : NeZero M := ⟨hM.ne'⟩
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let ε := 4*π/(Q+1:ℝ)+9*T*δ
  let A (i : Fin M) := {x | 2≤circuitHamiltonianSpectralWidth (prefixGenerator n x) ∧
    pathGateDistance n 0 x (fullTurn n ((m+1)*(i.val+1)) x)≤ε}
  let p (i : Fin M) := μ.real (A i)
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty p
  have hp (j : Fin M) : p j ≤ p i := hi ▸ le_sup' p (Finset.mem_univ j)
  refine ⟨i.val+1,Nat.succ_le_succ (Nat.zero_le _),i.isLt,?_⟩
  have hl := gaussian_multiple_full_turn n m Q a hδ hδ'
  apply hl.trans
  calc
    _ ≤ μ.real (⋃ i, A i) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      obtain ⟨hw,q,hq,hqM,hfit⟩ := hx
      let j : Fin M := ⟨q-1,by omega⟩
      have hj : j.val+1=q := Nat.sub_add_cancel hq
      exact mem_iUnion.mpr ⟨j,hw,by change pathGateDistance _ _ _ (fullTurn n ((m+1)*(j.val+1)) x)≤ε; rwa [hj]⟩
    _ ≤ ∑ j, p j := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin M, p i := sum_le_sum fun j _ => hp j
    _ = _ := by rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rfl

#print axioms gaussian_selected_full_turn
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
