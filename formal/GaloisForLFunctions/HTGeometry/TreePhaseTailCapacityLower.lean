import GaloisForLFunctions.HTGeometry.NestedPathCutWitness

/-!
# Phase-tail circuit-capacity lower law on trees

For a diagonal two-body phase evolution supported on a spanning tree, every `G`-gate circuit
misses a cut carrying all but at most `G` edge phases.  The resulting four-configuration invariant
turns that residual phase into an operator-norm obstruction.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def edgeP11Value (x : Config Q) : Sym2 Q → ℝ :=
  Sym2.lift ⟨(fun u v => if x u = true ∧ x v = true then 1 else 0), by
    intro u v
    simp [and_comm]⟩

@[simp] theorem edgeP11Value_mk (x : Config Q) (u v : Q) :
    edgeP11Value x s(u, v) = if x u = true ∧ x v = true then 1 else 0 := by
  simp [edgeP11Value, Sym2.lift_mk]

noncomputable def treePhaseEnergy (P : SimpleGraph Q) [Fintype P.edgeSet]
    (β : Sym2 Q → ℝ) (x : Config Q) : ℝ :=
  ∑ e ∈ P.edgeFinset, β e * edgeP11Value x e

noncomputable def treePhaseEvolution (P : SimpleGraph Q) [Fintype P.edgeSet]
    (β : Sym2 Q → ℝ) : Matrix (Config Q) (Config Q) ℂ :=
  Matrix.diagonal fun x => Complex.exp (-(Complex.I * (treePhaseEnergy P β x : ℂ)))

theorem treePhaseEvolution_unitary (P : SimpleGraph Q) [Fintype P.edgeSet]
    (β : Sym2 Q → ℝ) :
    treePhaseEvolution P β ∈ Matrix.unitaryGroup (Config Q) ℂ := by
  apply mem_unitaryGroup_diagonal_general
  intro x
  rw [Complex.norm_exp]
  simp [treePhaseEnergy]

def edgeCrosses (A : Finset Q) : Sym2 Q → Bool :=
  Sym2.lift ⟨(fun u v => decide ((u ∈ A) ≠ (v ∈ A))), by
    intro u v
    simp only [ne_eq, decide_eq_decide]
    tauto⟩

@[simp] theorem edgeCrosses_mk (A : Finset Q) (u v : Q) :
    edgeCrosses A s(u, v) = true ↔ (u ∈ A) ≠ (v ∈ A) := by
  simp [edgeCrosses, Sym2.lift_mk]

noncomputable def negativeEdgeLabel (β : Sym2 Q → ℝ) (u v : Q) : Bool :=
  decide (β s(u, v) < 0)

theorem negativeEdgeLabel_symmetric (P : SimpleGraph Q) (β : Sym2 Q → ℝ) :
    BooleanEdgeFieldSymmetric P (negativeEdgeLabel β) := by
  intro u v huv
  simp only [negativeEdgeLabel]
  rw [Sym2.eq_swap]

theorem edgeP11Value_cut_mixed_mk
    (A : Finset Q) (σ : Q → Bool) (u v : Q) :
    edgeP11Value (cutFourConfig A σ false false) s(u, v) +
        edgeP11Value (cutFourConfig A σ true true) s(u, v) -
        edgeP11Value (cutFourConfig A σ false true) s(u, v) -
        edgeP11Value (cutFourConfig A σ true false) s(u, v) =
      if (u ∈ A) ≠ (v ∈ A) then
        if σ u = σ v then 1 else -1
      else 0 := by
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
    cases hσu : σ u <;> cases hσv : σ v <;>
    simp [edgeP11Value, cutFourConfig, orientedBit, hu, hv, hσu, hσv]

theorem treePhaseEnergy_cut_mixed
    (P : SimpleGraph Q) [Fintype P.edgeSet] (hP : P.IsTree)
    (β : Sym2 Q → ℝ) (A : Finset Q) :
    ∃ σ : Q → Bool,
      treePhaseEnergy P β (cutFourConfig A σ false false) +
          treePhaseEnergy P β (cutFourConfig A σ true true) -
          treePhaseEnergy P β (cutFourConfig A σ false true) -
          treePhaseEnergy P β (cutFourConfig A σ true false) =
        ∑ e ∈ P.edgeFinset.filter (fun e => edgeCrosses A e = true), |β e| := by
  obtain ⟨σ, hσ⟩ := exists_booleanOrientation_of_isTree hP
    (negativeEdgeLabel β) (negativeEdgeLabel_symmetric P β)
  refine ⟨σ, ?_⟩
  simp only [treePhaseEnergy, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v huv
  have hadj : P.Adj u v := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huv
  have hsign := hσ hadj
  rw [show
    β s(u, v) * edgeP11Value (cutFourConfig A σ false false) s(u, v) +
          β s(u, v) * edgeP11Value (cutFourConfig A σ true true) s(u, v) -
          β s(u, v) * edgeP11Value (cutFourConfig A σ false true) s(u, v) -
          β s(u, v) * edgeP11Value (cutFourConfig A σ true false) s(u, v) =
        β s(u, v) *
          (edgeP11Value (cutFourConfig A σ false false) s(u, v) +
            edgeP11Value (cutFourConfig A σ true true) s(u, v) -
            edgeP11Value (cutFourConfig A σ false true) s(u, v) -
            edgeP11Value (cutFourConfig A σ true false) s(u, v)) by ring,
    edgeP11Value_cut_mixed_mk]
  simp only [edgeCrosses_mk]
  by_cases hcross : (u ∈ A) ≠ (v ∈ A)
  · rw [if_pos hcross, if_pos hcross]
    by_cases hneg : β s(u, v) < 0
    · have hlabel : negativeEdgeLabel β u v = true := by simp [negativeEdgeLabel, hneg]
      rw [hlabel] at hsign
      cases hσu : σ u <;> cases hσv : σ v <;>
        simp [hσu, hσv, abs_of_neg hneg] at hsign ⊢
    · have hlabel : negativeEdgeLabel β u v = false := by simp [negativeEdgeLabel, hneg]
      rw [hlabel] at hsign
      have hnonneg : 0 ≤ β s(u, v) := le_of_not_gt hneg
      cases hσu : σ u <;> cases hσv : σ v <;>
        simp [hσu, hσv, abs_of_nonneg hnonneg] at hsign ⊢
  · rw [if_neg hcross, if_neg hcross]
    simp

theorem edgeCrosses_iff_not_monochromatic
    (A : Finset Q) (ε : Q → Bool) (hA : ∀ q, q ∈ A ↔ ε q = true)
    (e : Sym2 Q) :
    edgeCrosses A e = true ↔ edgeMonochromatic ε e ≠ true := by
  revert e
  apply Sym2.ind
  intro u v
  rw [edgeCrosses_mk]
  unfold edgeMonochromatic
  rw [Sym2.lift_mk]
  rw [hA, hA]
  cases hεu : ε u <;> cases hεv : ε v <;> simp [hεu, hεv]

/-- Four target phases near a factorizing circuit obey the same `4ε` obstruction as the normalized
`1,1,1,u` witness. -/
theorem norm_four_target_difference_le
    {u₀₀ u₀₁ u₁₀ u₁₁ w₀₀ w₀₁ w₁₀ w₁₁ : ℂ} {ε : ℝ}
    (hfac : w₀₀ * w₁₁ = w₀₁ * w₁₀)
    (h₀₀ : ‖u₀₀ - w₀₀‖ ≤ ε) (h₀₁ : ‖u₀₁ - w₀₁‖ ≤ ε)
    (h₁₀ : ‖u₁₀ - w₁₀‖ ≤ ε) (h₁₁ : ‖u₁₁ - w₁₁‖ ≤ ε)
    (nu₀₀ : ‖u₀₀‖ = 1) (nu₁₁ : ‖u₁₁‖ = 1)
    (nu₀₁ : ‖u₀₁‖ = 1) (nu₁₀ : ‖u₁₀‖ = 1)
    (nw₀₁ : ‖w₀₁‖ ≤ 1) (nw₁₁ : ‖w₁₁‖ ≤ 1) :
    ‖u₀₀ * u₁₁ - u₀₁ * u₁₀‖ ≤ 4 * ε := by
  have hleft : ‖u₀₀ * u₁₁ - w₀₀ * w₁₁‖ ≤ 2 * ε := by
    have hsplit : u₀₀ * u₁₁ - w₀₀ * w₁₁ =
        u₀₀ * (u₁₁ - w₁₁) + w₁₁ * (u₀₀ - w₀₀) := by ring
    rw [hsplit]
    calc
      ‖u₀₀ * (u₁₁ - w₁₁) + w₁₁ * (u₀₀ - w₀₀)‖ ≤
          ‖u₀₀ * (u₁₁ - w₁₁)‖ + ‖w₁₁ * (u₀₀ - w₀₀)‖ := norm_add_le _ _
      _ = ‖u₀₀‖ * ‖u₁₁ - w₁₁‖ + ‖w₁₁‖ * ‖u₀₀ - w₀₀‖ := by rw [norm_mul, norm_mul]
      _ ≤ 2 * ε := by
        rw [nu₀₀]
        nlinarith [h₀₀, h₁₁, nw₁₁, norm_nonneg (u₀₀ - w₀₀)]
  have hright : ‖w₀₁ * w₁₀ - u₀₁ * u₁₀‖ ≤ 2 * ε := by
    have hsplit : w₀₁ * w₁₀ - u₀₁ * u₁₀ =
        w₀₁ * (w₁₀ - u₁₀) + (w₀₁ - u₀₁) * u₁₀ := by ring
    rw [hsplit]
    calc
      ‖w₀₁ * (w₁₀ - u₁₀) + (w₀₁ - u₀₁) * u₁₀‖ ≤
          ‖w₀₁ * (w₁₀ - u₁₀)‖ + ‖(w₀₁ - u₀₁) * u₁₀‖ := norm_add_le _ _
      _ = ‖w₀₁‖ * ‖w₁₀ - u₁₀‖ + ‖w₀₁ - u₀₁‖ * ‖u₁₀‖ := by rw [norm_mul, norm_mul]
      _ ≤ 2 * ε := by
        rw [nu₁₀, norm_sub_rev w₁₀ u₁₀, norm_sub_rev w₀₁ u₀₁]
        nlinarith [h₀₁, h₁₀, nw₀₁, norm_nonneg (u₁₀ - w₁₀)]
  calc
    ‖u₀₀ * u₁₁ - u₀₁ * u₁₀‖ =
        ‖(u₀₀ * u₁₁ - w₀₀ * w₁₁) + (w₀₁ * w₁₀ - u₀₁ * u₁₀)‖ := by
          rw [hfac]
          ring_nf
    _ ≤ ‖u₀₀ * u₁₁ - w₀₀ * w₁₁‖ + ‖w₀₁ * w₁₀ - u₀₁ * u₁₀‖ := norm_add_le _ _
    _ ≤ 4 * ε := by linarith

/-- **Phase-tail capacity lower law.**  If every deletion of at most `G` tree edges leaves a
phase chord larger than `4ε`, no support-certified circuit with at most `G` two-qubit gates can
approximate the tree phase evolution in operator norm. -/
theorem treePhase_twoGateCount_gt {L G : ℕ}
    (P : SimpleGraph (PairQubit L)) [DecidableRel P.Adj] (hP : P.IsTree)
    (β : Sym2 (PairQubit L) → ℝ)
    (c : List (LocalGate (PairQubit L))) {ε : ℝ}
    (hclose : ‖circuitMatrix c - treePhaseEvolution P β‖ ≤ ε)
    (htail : ∀ N : Finset (Sym2 (PairQubit L)), N ⊆ P.edgeFinset → N.card ≤ G →
      4 * ε < ‖Complex.exp (-(Complex.I *
        ((∑ e ∈ P.edgeFinset \ N, |β e| : ℝ) : ℂ))) - 1‖) :
    G < twoGateCount c := by
  by_contra hnot
  have hcost : twoGateCount c ≤ G := Nat.le_of_not_gt hnot
  obtain ⟨cutLabel, A, hA, hsep, hmonoCard⟩ :=
    exists_tree_cut_separating_circuit c P hP
  let N : Finset (Sym2 (PairQubit L)) :=
    P.edgeFinset.filter fun e => edgeMonochromatic cutLabel e = true
  have hNsub : N ⊆ P.edgeFinset := Finset.filter_subset _ _
  have hNcard : N.card ≤ G := by
    exact le_trans hmonoCard hcost
  have hcrossEdges :
      P.edgeFinset.filter (fun e => edgeCrosses A e = true) = P.edgeFinset \ N := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff, N]
    constructor
    · rintro ⟨heP, hcross⟩
      refine ⟨heP, ?_⟩
      rintro ⟨_, hmono⟩
      exact (edgeCrosses_iff_not_monochromatic A cutLabel hA e).mp hcross hmono
    · rintro ⟨heP, hnotmono⟩
      refine ⟨heP, ?_⟩
      apply (edgeCrosses_iff_not_monochromatic A cutLabel hA e).mpr
      intro hmono
      exact hnotmono ⟨heP, hmono⟩
  obtain ⟨σ, hmixed⟩ := treePhaseEnergy_cut_mixed P hP β A
  rw [hcrossEdges] at hmixed
  let x00 := cutFourConfig A σ false false
  let x01 := cutFourConfig A σ false true
  let x10 := cutFourConfig A σ true false
  let x11 := cutFourConfig A σ true true
  let W := circuitMatrix c
  let U := treePhaseEvolution P β
  have hfactor : W x00 x00 * W x11 x11 = W x01 x01 * W x10 x10 := by
    dsimp only [W, x00, x01, x10, x11]
    exact hsep.fourPoint_diagonal_cut
  have hentry (x : Config (PairQubit L)) : ‖U x x - W x x‖ ≤ ε := by
    have hnorm : ‖(W - U) x x‖ ≤ ‖W - U‖ := norm_entry_le_l2_opNorm _ _ _
    have hrewrite : (W - U) x x = W x x - U x x := rfl
    rw [hrewrite, norm_sub_rev] at hnorm
    exact le_trans hnorm hclose
  have hUdiag (x : Config (PairQubit L)) :
      U x x = Complex.exp (-(Complex.I * (treePhaseEnergy P β x : ℂ))) := by
    simp [U, treePhaseEvolution]
  have hUnorm (x : Config (PairQubit L)) : ‖U x x‖ = 1 := by
    rw [hUdiag, Complex.norm_exp]
    simp [treePhaseEnergy]
  have hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := circuitMatrix_unitary c
  have htarget := norm_four_target_difference_le hfactor
    (hentry x00) (hentry x01) (hentry x10) (hentry x11)
    (hUnorm x00) (hUnorm x11) (hUnorm x01) (hUnorm x10)
    (entry_norm_bound_of_unitary hWunit _ _) (entry_norm_bound_of_unitary hWunit _ _)
  let φ : ℝ := ∑ e ∈ P.edgeFinset \ N, |β e|
  have hphaseProduct :
      ‖U x00 x00 * U x11 x11 - U x01 x01 * U x10 x10‖ =
        ‖Complex.exp (-(Complex.I * (φ : ℂ))) - 1‖ := by
    rw [hUdiag, hUdiag, hUdiag, hUdiag]
    have hmixed' :
        treePhaseEnergy P β x00 + treePhaseEnergy P β x11 -
          treePhaseEnergy P β x01 - treePhaseEnergy P β x10 = φ := by
      simpa [x00, x01, x10, x11, φ] using hmixed
    let z := Complex.exp (Complex.I *
      ((treePhaseEnergy P β x01 + treePhaseEnergy P β x10 : ℝ) : ℂ))
    have hz : ‖z‖ = 1 := by rw [Complex.norm_exp]; simp [z]
    calc
      ‖Complex.exp (-(Complex.I * (treePhaseEnergy P β x00 : ℂ))) *
          Complex.exp (-(Complex.I * (treePhaseEnergy P β x11 : ℂ))) -
        Complex.exp (-(Complex.I * (treePhaseEnergy P β x01 : ℂ))) *
          Complex.exp (-(Complex.I * (treePhaseEnergy P β x10 : ℂ)))‖ =
        ‖(Complex.exp (-(Complex.I * (treePhaseEnergy P β x00 : ℂ))) *
            Complex.exp (-(Complex.I * (treePhaseEnergy P β x11 : ℂ))) -
          Complex.exp (-(Complex.I * (treePhaseEnergy P β x01 : ℂ))) *
            Complex.exp (-(Complex.I * (treePhaseEnergy P β x10 : ℂ)))) * z‖ := by
              rw [norm_mul, hz, mul_one]
      _ = ‖Complex.exp (-(Complex.I *
          ((treePhaseEnergy P β x00 + treePhaseEnergy P β x11 -
            treePhaseEnergy P β x01 - treePhaseEnergy P β x10 : ℝ) : ℂ))) - 1‖ := by
        congr 1
        rw [show
          (Complex.exp (-(Complex.I * (treePhaseEnergy P β x00 : ℂ))) *
              Complex.exp (-(Complex.I * (treePhaseEnergy P β x11 : ℂ))) -
            Complex.exp (-(Complex.I * (treePhaseEnergy P β x01 : ℂ))) *
              Complex.exp (-(Complex.I * (treePhaseEnergy P β x10 : ℂ)))) * z =
        Complex.exp (-(Complex.I *
          ((treePhaseEnergy P β x00 + treePhaseEnergy P β x11 -
            treePhaseEnergy P β x01 - treePhaseEnergy P β x10 : ℝ) : ℂ))) - 1 by
          simp only [z]
          rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
            ← Complex.exp_add]
          congr 1 <;> push_cast <;> ring_nf <;> simp]
      _ = ‖Complex.exp (-(Complex.I * (φ : ℂ))) - 1‖ := by rw [hmixed']
  have htail' := htail N hNsub hNcard
  change 4 * ε < ‖Complex.exp (-(Complex.I * (φ : ℂ))) - 1‖ at htail'
  rw [← hphaseProduct] at htail'
  linarith

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
