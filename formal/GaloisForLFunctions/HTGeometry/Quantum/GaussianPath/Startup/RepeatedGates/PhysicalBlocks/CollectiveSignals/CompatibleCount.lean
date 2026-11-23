import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.LocalTest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.IndependentTests
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PhysicalFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PacketOverlap

/-! # A fitting circuit admits at most order sin(t)⁻⁴ independent packet tests -/
open Matrix Finset Real GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback SpanningDensity.FixedHorizon
noncomputable section
variable {n m : ℕ}

/-- A local quadratic transfer is amplified in the Choi overlap even when
each individual packet signal is weaker than the physical fitting error. -/
theorem compatible_count (e f : Fin m→Fin (n+1)) (x y : Fin m→Fin (n+2))
    (hadj : ∀ i, (e i).succ=(f i).castSucc)
    (hd : ∀ i j, i≠j → Disjoint (tripleSites (e i) (f i)) (tripleSites (e j) (f j)))
    (hx : ∀ i, x i∈tripleSites (e i) (f i)) (hy : ∀ i, y i∈tripleSites (e i) (f i))
    (C : TwoQubitCircuit (n+2)) (hm : ∀ i, x i∉inputs (circuitWord C) (y i))
    (hc : ∀ i j, i≠j → ¬conflicting (circuitWord C) x y i j)
    (u : PathShell n) (t δ : ℝ) (hδ : 0≤δ) (hs : 0 < (sin t)^2)
    (hcoup : ∀ i l, l∈(tripleSites (e i) (f i)).biUnion pathIncidentLabels →
      |u l-tripleField (e i) (f i) (1/sqrt 2) l|≤δ)
    (herr : 126*|t|*δ≤(sin t)^2/4) (z : ℂ) (hz : ‖z‖=1)
    (he : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    (m:ℝ)*(sin t)^4≤16 := by
  rcases Nat.eq_zero_or_pos m with rfl|hpos
  · norm_num
  let S i := tripleSites (e i) (f i)
  let P i := packetProbe (e i) (x i)
  let B i := packetImage (e i) (f i) (x i)
  let Q i := packetProbe (e i) (y i)
  let K i := packetTest (e i) (f i) (x i) t
  let U := unitaryEvolution (pathHamiltonian u) t
  have hU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
  have hne (i) : x i≠y i := fun h => hm i (h ▸ knows_self _ _)
  have ho (i j : Fin m) (hne' : i≠j) (hcross : x j∉inputs (circuitWord C) (y i)) :
      inner ℂ (choiVector (P i*C.eval.val*B i)) (choiVector (P j*C.eval.val*B j))=0 := by
    have hQ := onsite_probe_supported (y i) (tripleAxis (e i) (y i))
    have hdis : Disjoint {y i} (S j) := (hd i j hne').mono_left (singleton_subset_iff.mpr (hy i))
    have hcomm : Commute (Q i) (B j) := commute_of_isSiteSupported_disjoint hdis hQ
      (packetImage_supported (hadj j) (hx j))
    apply orthogonal_of_missing_input C (x i) (x j) (y i) (hm i) hcross (P i) (P j)
      (B i) (B j) (Q i) (finitePauliMatrix_isHermitian _) (onsite_probe_supported _ _)
      (onsite_probe_supported _ _) hQ (finitePauliMatrix_mul_self _)
    rw [(packetImage_hermitian (e i) (f i) (x i)).eq,←mul_assoc,hcomm.eq,mul_assoc,
      packetImage_flip (hadj i) (hx i) (hy i) (hne i),mul_neg,mul_assoc]
  have hpair (i j : Fin m) (hne' : i≠j) :
      inner ℂ (choiVector (P i*C.eval.val*B i)) (choiVector (P j*C.eval.val*B j))=0 := by
    by_cases h : x j∈inputs (circuitWord C) (y i)
    · exact inner_eq_zero_symm.mp (ho j i hne'.symm (fun h' => hc i j hne' ⟨h',h⟩))
    · exact ho i j hne' h
  have hmean (i) : (sin t)^2≤‖(K i).trace/(Fintype.card (Fin (n+2)→Bool):ℂ)‖ := by
    rw [show (K i).trace/_=(sin t:ℂ)^2 from packet_transfer (hadj i) (hx i) (hy i) (hne i) t,
      ←Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.le]
  have H := packet_overlap hpos U C.eval.val hU C.eval.property P B K S
    (fun _ => finitePauliMatrix_isHermitian _) (fun i => packetImage_hermitian _ _ _)
    (fun _ => (norm_finitePauliMatrix _).le)
    (fun i => (CStarRing.norm_of_mem_unitary (packetImage_unitary (hadj i) (x i))).le)
    (fun i => (CStarRing.norm_of_mem_unitary (packetTest_unitary (hadj i) (x i) t)).le)
    (fun i => packetTest_supported (hadj i) (hx i) t) hd hs hmean
    (fun i => packetTest_local_error (hadj i) (hx i) u hδ t (hcoup i)) hpair
  have hfit := overlap_of_fit U C.eval.val hU C.eval.property z hz he
  have hsqrt : 0 < sqrt (m:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hpos)
  have h₁ : 3/4≤‖inner ℂ (choiVector U) (choiVector C.eval.val)‖ := (by norm_num : (3:ℝ)/4≤1-(1/4)^2/2).trans hfit
  have h₂ : (m:ℝ)*(sin t)^2≤4*sqrt m := by
    linarith only [H,mul_le_mul_of_nonneg_left h₁ (mul_nonneg (Nat.cast_nonneg _) hs.le),
      mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg m)]
  have h₃ : sqrt m*(sin t)^2≤4 := (mul_le_mul_iff_right₀ hsqrt).mp (by
    rw [←mul_assoc,←sq,sq_sqrt (Nat.cast_nonneg _)]
    linarith only [h₂])
  have h₄ := mul_self_le_mul_self (mul_nonneg hsqrt.le hs.le) h₃
  calc (m:ℝ)*(sin t)^4 = (sqrt m)^2*(sin t)^4 := by rw [sq_sqrt (Nat.cast_nonneg m)]
       _ = (sqrt m*(sin t)^2)*(sqrt m*(sin t)^2) := by ring
       _ ≤ 4*4 := h₄
       _ = _ := by norm_num

#print axioms compatible_count
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
