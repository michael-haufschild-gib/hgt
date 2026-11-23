import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PacketOverlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.WeakBoundary
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal

/-! # Overlap with the physical evolution across separated weak boundaries -/
open Matrix RHTower GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open WeakBonds
noncomputable section
variable {n m : ℕ}

private theorem bond_in_middle {a b e : Fin (n+1)} (ha : a<e) (hb : e<b) :
    e.castSucc∈middleBlock a b ∧ e.succ∈middleBlock a b := by
  simp only [middleBlock,Finset.mem_Ioc,Fin.lt_def,Fin.le_def,Fin.val_castSucc,Fin.val_succ] at ha hb ⊢
  omega

/-- Multiplying a localized reporter by its calibrated input preserves
the two-boundary estimate. -/
theorem bond_packet_error (u : PathShell n) {a b e : Fin (n+1)} (ha : a<e) (hb : e<b) (t : ℝ) :
    let U := unitaryEvolution (pathHamiltonian u) t
    let W := unitaryEvolution (packet u (middleBlock a b)) t
    ‖Uᴴ*bondOutput e*U*bondInput e-Wᴴ*bondOutput e*W*bondInput e‖ ≤
      2*|t| *(‖edgePart u a‖+‖edgePart u b‖) := by
  intro U W
  have h := weak_boundary_reporter u (ha.trans hb) (bondOutput e)
    (bond_output_supported (bond_in_middle ha hb).1) t
  change ‖Uᴴ*bondOutput e*U-Wᴴ*bondOutput e*W‖ ≤ _*‖bondOutput e‖ at h
  rw [show ‖bondOutput e‖=1 from norm_finitePauliMatrix _,mul_one] at h
  rw [←sub_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (bond_input_norm e) (norm_nonneg _)).trans
    ((mul_one _).le.trans h))

/-- The normalized signal can be read from any bracketing packet up
to the combined strength of its two boundary couplings times 2|t|. -/
theorem bond_packet_signal_error (u : PathShell n) {a b e : Fin (n+1)} (ha : a<e) (hb : e<b) (t : ℝ) :
    |bondSignal e u t-signal (packet u (middleBlock a b)) (bondOutput e) (bondInput e) t| ≤
      2*|t| *(‖edgePart u a‖+‖edgePart u b‖) := by
  let H := pathHamiltonian u
  let K := packet u (middleBlock a b)
  let Y := bondOutput e
  let B := bondInput e
  let d : ℂ := Fintype.card (Fin (n+2) → Bool)
  change |(d⁻¹*(unitaryEvolution H (-t)*Y*unitaryEvolution H t*B).trace).re-
    (d⁻¹*(unitaryEvolution K (-t)*Y*unitaryEvolution K t*B).trace).re| ≤ _
  have hu : unitaryEvolution H (-t)=star (unitaryEvolution H t) :=
    EigenlineSignals.adjoint_evolution ⟨H,isSelfAdjoint_pathHamiltonian u⟩ t
  have hw : unitaryEvolution K (-t)=star (unitaryEvolution K t) :=
    EigenlineSignals.adjoint_evolution ⟨K,packet_selfAdjoint u _⟩ t
  rw [hu,hw,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans ((norm_normalizedTrace_sub_le_l2OpNorm _ _).trans
    (bond_packet_error u ha hb t))

/-- Every oriented family of detectable crossed bonds in disjoint packets
bounds the normalized overlap with the entire circuit. Localization costs
only the largest two-boundary leakage of an individual reporter. -/
theorem selected_bond_overlap (hm : 0 < m) (u : PathShell n) (t : ℝ)
    (C : TwoQubitCircuit (n+2)) (S : Finset (Fin (n+2)))
    (hc : ∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S)
    (e a b : Fin m → Fin (n+1)) (hi : Function.Injective e)
    (hl : ∀ i, (e i).castSucc∈S) (hr : ∀ i, (e i).succ∉S)
    (he : ∀ i, a i < e i ∧ e i < b i)
    (hd : ∀ i j, i≠j → Disjoint (middleBlock (a i) (b i)) (middleBlock (a j) (b j)))
    {r δ : ℝ} (hpos : δ < r) (hsig : ∀ i, r ≤ |bondSignal (e i) u t|)
    (hweak : ∀ i, 2*|t| *(‖edgePart u (a i)‖+‖edgePart u (b i)‖) ≤ δ) :
    (m:ℝ)*(r-δ)*‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian u) t))
      (choiVector C.eval.val)‖ ≤ 2*Real.sqrt m+m*δ := by
  let U := unitaryEvolution (pathHamiltonian u) t
  let M i := middleBlock (a i) (b i)
  let W i := unitaryEvolution (packet u (M i)) t
  let Y i := bondOutput (e i)
  let B i := bondInput (e i)
  let F i := Uᴴ*Y i*U*B i
  let K i := (W i)ᴴ*Y i*W i*B i
  let d : ℂ := Fintype.card (Fin (n+2) → Bool)
  have hW (i) := unitaryEvolution_mem_unitary (packet_selfAdjoint u (M i)) t
  have hI (i) : (e i).castSucc∈M i ∧ (e i).succ∈M i := by
    exact bond_in_middle (he i).1 (he i).2
  have hY (i) := bond_output_supported (hI i).1
  have hB (i) := bond_input_supported (hI i).1 (hI i).2
  have hn (i) : ‖Y i‖=1 := norm_finitePauliMatrix _
  have hbn (i) : ‖B i‖ ≤ 1 := bond_input_norm _
  have hK (i) : IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) (M i) (K i) := by
    have hw := isSiteSupported_unitaryEvolution (packet_supported u (M i)) t
    exact ((hw.conjTranspose.matrix_mul (hY i)).matrix_mul hw).matrix_mul (hB i)
  have hk (i) : ‖K i‖ ≤ 1 := by
    have h : ‖star (W i)*Y i*W i‖=1 := by
      rw [CStarRing.norm_mul_mem_unitary _ (hW i),
        CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (hW i)),hn]
    calc ‖K i‖ ≤ ‖star (W i)*Y i*W i‖*‖B i‖ := norm_mul_le _ _
         _ ≤ 1 := by rw [h,one_mul]; exact hbn i
  have herr (i) : ‖F i-K i‖ ≤ δ := (bond_packet_error u (he i).1 (he i).2 t).trans (hweak i)
  have hmean (i) : r-δ ≤ ‖(K i).trace/d‖ := by
    have hevol : unitaryEvolution (pathHamiltonian u) (-t)=star U :=
      EigenlineSignals.adjoint_evolution ⟨_,isSelfAdjoint_pathHamiltonian u⟩ t
    have hh := hsig i
    change r ≤ |(d⁻¹*(unitaryEvolution (pathHamiltonian u) (-t)*Y i*U*B i).trace).re| at hh
    rw [hevol] at hh
    have h₁ : r ≤ ‖d⁻¹*(F i).trace‖ := hh.trans (Complex.abs_re_le_norm _)
    have h₂ := (norm_normalizedTrace_sub_le_l2OpNorm (F i) (K i)).trans (herr i)
    have h₃ := norm_sub_norm_le (d⁻¹*(F i).trace) (d⁻¹*(K i).trace)
    change ‖d⁻¹*(F i).trace-d⁻¹*(K i).trace‖≤δ at h₂
    rw [div_eq_mul_inv,mul_comm (K i).trace]
    exact sub_le_iff_le_add.mpr (by linarith only [h₁,h₂,h₃])
  exact packet_overlap hm U C.eval.val (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t)
    C.eval.property Y B K M (fun i => finitePauliMatrix_isHermitian _) (fun i => bond_input_hermitian _)
    (fun i => (hn i).le) hbn hk hK hd (sub_pos.mpr hpos) hmean herr
    (fun i j hij => oriented_bond_orthogonal C S hc (fun h => hij (hi h)) (hl i) (hl j) (hr i))

#print axioms selected_bond_overlap
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
