import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PacketData
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.IndependentTests
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PhysicalFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PacketOverlap

/-! # Compatible missing inputs bound the number of disjoint Choi reporters -/
open Matrix Finset Real GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback SpanningDensity.FixedHorizon
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
noncomputable section
variable {n m : ℕ}

private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- With mean signal r and localization error r/4, a quarter-error circuit
admits at most 16/r² pairwise compatible missing-input tests. Their local
supports may be larger than the triples carrying the flips. -/
theorem compatible_reporter_count (e f : Fin m→Fin (n+1)) (x y : Fin m→Fin (n+2))
    (S : Fin m→Finset (Fin (n+2))) (hadj : ∀ i, (e i).succ=(f i).castSucc)
    (hsub : ∀ i, tripleSites (e i) (f i)⊆S i)
    (hd : ∀ i j, i≠j → Disjoint (S i) (S j))
    (hx : ∀ i, x i∈tripleSites (e i) (f i)) (hy : ∀ i, y i∈tripleSites (e i) (f i))
    (C : TwoQubitCircuit (n+2)) (hm : ∀ i, x i∉inputs (circuitWord C) (y i))
    (hc : ∀ i j, i≠j → ¬conflicting (circuitWord C) x y i j)
    (U : Reg (n+2)) (hU : U∈unitary _) (K : Fin m→Reg (n+2)) (r : ℝ) (hr : 0<r)
    (hKn : ∀ i, ‖K i‖≤1) (hKs : ∀ i, IsSiteSupported (S i) (K i))
    (hmean : ∀ i, r≤‖(K i).trace/(Fintype.card (Fin (n+2)→Bool):ℂ)‖)
    (herr : ∀ i, ‖star U*packetProbe (e i) (x i)*U*packetImage (e i) (f i) (x i)-K i‖≤r/4)
    (z : ℂ) (hz : ‖z‖=1) (he : ‖U-z • C.eval.val‖≤1/4) : (m:ℝ)*r^2≤16 := by
  rcases Nat.eq_zero_or_pos m with rfl|hpos
  · norm_num
  let P i := packetProbe (e i) (x i)
  let B i := packetImage (e i) (f i) (x i)
  let Q i := packetProbe (e i) (y i)
  have hne (i) : x i≠y i := fun h => hm i (h ▸ knows_self _ _)
  have ho (i j : Fin m) (hne' : i≠j) (hcross : x j∉inputs (circuitWord C) (y i)) :
      inner ℂ (choiVector (P i*C.eval.val*B i)) (choiVector (P j*C.eval.val*B j))=0 := by
    have hQ := probe_supported (y i) (tripleAxis (e i) (y i))
    have hdis : Disjoint {y i} (S j) := (hd i j hne').mono_left ((singleton_subset_iff.mpr (hy i)).trans (hsub i))
    have hcomm : Commute (Q i) (B j) := commute_of_isSiteSupported_disjoint hdis hQ
      (IsSiteSupported.mono (hsub j) (packetImage_supported (hadj j) (hx j)))
    apply orthogonal_of_missing_input C (x i) (x j) (y i) (hm i) hcross (P i) (P j)
      (B i) (B j) (Q i) (finitePauliMatrix_isHermitian _) (probe_supported _ _)
      (probe_supported _ _) hQ (finitePauliMatrix_mul_self _)
    rw [(packetImage_hermitian (e i) (f i) (x i)).eq,←mul_assoc,hcomm.eq,mul_assoc,
      packetImage_flip (hadj i) (hx i) (hy i) (hne i),mul_neg,mul_assoc]
  have hpair (i j : Fin m) (hne' : i≠j) :
      inner ℂ (choiVector (P i*C.eval.val*B i)) (choiVector (P j*C.eval.val*B j))=0 := by
    by_cases h : x j∈inputs (circuitWord C) (y i)
    · exact inner_eq_zero_symm.mp (ho j i hne'.symm (fun h' => hc i j hne' ⟨h',h⟩))
    · exact ho i j hne' h
  have H := packet_overlap hpos U C.eval.val hU C.eval.property P B K S
    (fun _ => finitePauliMatrix_isHermitian _) (fun i => packetImage_hermitian _ _ _)
    (fun _ => (norm_finitePauliMatrix _).le)
    (fun i => (CStarRing.norm_of_mem_unitary (packetImage_unitary (hadj i) (x i))).le)
    hKn hKs hd hr hmean herr hpair
  have hfit := overlap_of_fit U C.eval.val hU C.eval.property z hz he
  have hsqrt : 0<sqrt (m:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hpos)
  have h₁ : 3/4≤‖inner ℂ (choiVector U) (choiVector C.eval.val)‖ :=
    (by norm_num : (3:ℝ)/4≤1-(1/4)^2/2).trans hfit
  have h₂ : (m:ℝ)*r≤4*sqrt m := by
    linarith only [H,mul_le_mul_of_nonneg_left h₁ (mul_nonneg (Nat.cast_nonneg m) hr.le)]
  have h₃ : sqrt m*r≤4 := (mul_le_mul_iff_right₀ hsqrt).mp (by
    rw [←mul_assoc,←sq,sq_sqrt (Nat.cast_nonneg _)]
    linarith only [h₂])
  have h₄ := mul_self_le_mul_self (mul_nonneg hsqrt.le hr.le) h₃
  calc (m:ℝ)*r^2 = (sqrt m)^2*r^2 := by rw [sq_sqrt (Nat.cast_nonneg _)]
       _ = (sqrt m*r)*(sqrt m*r) := by ring
       _ ≤ 4*4 := h₄
       _ = _ := by norm_num

#print axioms compatible_reporter_count
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
