import GaloisForLFunctions.HTGeometry.TwoLocalProjectiveTrotterCompilerLaw

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance matrixCStarAlgebraQubitCone (n : ℕ) :
    CStarAlgebra (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) where

/-- Projective operator-norm hardness against every continuous two-qubit
circuit below one gate budget. -/
def ProjectiveCircuitSeparated (n : ℕ) (ε : ℝ) (P : ℕ)
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) : Prop :=
  ∀ c : ℂ, ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
    C.gateCount ≤ P →
      ε < ‖U - c •
        (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖

/-- Projective circuit approximation below one gate budget. -/
def HasProjectiveCircuitApproximation (n : ℕ) (ε : ℝ) (P : ℕ)
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
    C.gateCount ≤ P ∧
      ‖U - c •
        (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤ ε

/-- Hardness against a gate budget remains true for every smaller budget. -/
theorem ProjectiveCircuitSeparated.mono_budget
    {n : ℕ} {ε : ℝ} {P Q : ℕ}
    {U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ}
    (h : ProjectiveCircuitSeparated n ε P U) (hQP : Q ≤ P) :
    ProjectiveCircuitSeparated n ε Q U := by
  intro c hc C hC
  exact h c hc C (hC.trans hQP)

theorem norm_projectiveCircuitEval
    {n : ℕ} {c : ℂ} (hc : ‖c‖ = 1) (C : TwoQubitCircuit n) :
    ‖c • (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)‖ = 1 := by
  rw [norm_smul, hc]
  simp

/-- Backward cone for the actual continuous `SU(4)` circuit model, including
global phases. -/
theorem projectiveCircuitSeparated_left_of_product
    {n : ℕ}
    {U V W : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ}
    (hV : V ∈ Matrix.unitaryGroup _ ℂ)
    (hproduct : U * V = W)
    {εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : r ≤ P)
    (hlate : ProjectiveCircuitSeparated n εlate P W)
    (hincrement : HasProjectiveCircuitApproximation n εincrement r V)
    (herror : εearly + εincrement ≤ εlate) :
    ProjectiveCircuitSeparated n εearly (P - r) U := by
  intro cU hcU CU hCU
  by_contra hnot
  have hUapprox : ‖U - cU •
      (CU.eval : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤ εearly :=
    le_of_not_gt hnot
  obtain ⟨cV, hcV, CV, hCV, hVapprox⟩ := hincrement
  let C := CU.mul CV
  have hCcount : C.gateCount ≤ P := by
    dsimp [C]
    rw [TwoQubitCircuit.mul_gateCount]
    have : P - r + r = P := Nat.sub_add_cancel hr
    omega
  have hcUV : ‖cU * cV‖ = 1 := by rw [norm_mul, hcU, hcV, one_mul]
  have hlate' := hlate (cU * cV) hcUV C hCcount
  have hphase :
      (cU * cV) •
          (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) =
        (cU • (CU.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) *
        (cV • (CV.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) := by
    rw [show (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) =
        (CU.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) *
        (CV.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) by
      exact congrArg Subtype.val (TwoQubitCircuit.mul_eval CU CV)]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hVnorm : ‖V‖ = 1 := CStarRing.norm_of_mem_unitary hV
  have hCUnorm : ‖cU •
      (CU.eval : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ = 1 :=
    norm_projectiveCircuitEval hcU CU
  have hdist :
      ‖W - (cU * cV) •
        (C.eval : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤
        εearly + εincrement := by
    rw [← hproduct, hphase]
    let AU : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ := cU • CU.eval
    let AV : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ := cV • CV.eval
    have hsplit : U * V - AU * AV = (U - AU) * V + AU * (V - AV) := by
      noncomm_ring
    rw [hsplit]
    calc
      ‖(U - AU) * V + AU * (V - AV)‖ ≤
          ‖(U - AU) * V‖ + ‖AU * (V - AV)‖ := norm_add_le _ _
      _ ≤ ‖U - AU‖ * ‖V‖ + ‖AU‖ * ‖V - AV‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ = ‖U - AU‖ + ‖V - AV‖ := by
          have hAUnorm : ‖AU‖ = 1 := by
            simpa [AU] using hCUnorm
          rw [hVnorm, hAUnorm, mul_one, one_mul]
      _ ≤ εearly + εincrement := add_le_add hUapprox hVapprox
  linarith

theorem unitaryEvolution_sub_mul
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)) (T τ : ℝ) :
    unitaryEvolution (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) (T - τ) *
      unitaryEvolution H τ = unitaryEvolution H T := by
  let X : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ := (-Complex.I) • H
  have hcomm : Commute ((T - τ) • X) (τ • X) :=
    ((Commute.refl X).smul_left (T - τ)).smul_right τ
  let _ : NormedAlgebra ℚ
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  unfold unitaryEvolution
  rw [← NormedSpace.exp_add_of_commute hcomm]
  congr 1
  dsimp [X]
  module

/-- Autonomous specialization: one hard late time plus a compiled increment
forces an entire earlier projective hard section. -/
theorem projectiveCircuitSeparated_unitaryEvolution_backward_cone
    {n : ℕ}
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    {T τ εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : r ≤ P)
    (hlate : ProjectiveCircuitSeparated n εlate P
      (unitaryEvolution H T))
    (hincrement : HasProjectiveCircuitApproximation n εincrement r
      (unitaryEvolution H τ))
    (herror : εearly + εincrement ≤ εlate) :
    ProjectiveCircuitSeparated n εearly (P - r)
      (unitaryEvolution H (T - τ)) := by
  exact projectiveCircuitSeparated_left_of_product
    (n := n)
    (U := unitaryEvolution H (T - τ))
    (V := unitaryEvolution H τ)
    (W := unitaryEvolution H T)
    (εearly := εearly) (εincrement := εincrement) (εlate := εlate)
    (P := P) (r := r)
    (unitaryEvolution_mem_unitary H.property τ)
    (unitaryEvolution_sub_mul H T τ) hr hlate hincrement herror

/-- Quantitative interval law. A single hard endpoint of a static two-local
Hamiltonian forces a whole hard interval behind it once one finite product
formula fits inside the endpoint gate and error budgets. -/
theorem twoLocal_projectiveCircuitHard_backwardInterval
    {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ))
    (hlocal : HasPauliWeightAtMost (Fin n) 2 H)
    {T W εearly εincrement εlate : ℝ} {P r : ℕ}
    (hr : 0 < r)
    (hcost : r * Fintype.card (PauliTracelessLabel n 2) ≤ P)
    (hsmall : ∀ τ ∈ Set.Icc (0 : ℝ) W,
      |τ / (r : ℝ)| *
        (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
        ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤ 1)
    (hcompiler : ∀ τ ∈ Set.Icc (0 : ℝ) W,
      3 * (Fintype.card (PauliTracelessLabel n 2) : ℝ) ^ (3 : ℕ) *
        ‖(H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) * |τ| ^ (2 : ℕ) / r ≤
        εincrement)
    (hlate : ProjectiveCircuitSeparated n εlate P
      (unitaryEvolution H T))
    (herror : εearly + εincrement ≤ εlate) :
    ∀ t ∈ Set.Icc (T - W) T,
      ProjectiveCircuitSeparated n εearly
        (P - r * Fintype.card (PauliTracelessLabel n 2))
        (unitaryEvolution H t) := by
  intro t ht
  let τ := T - t
  have hτ : τ ∈ Set.Icc (0 : ℝ) W := by
    constructor <;> dsimp [τ] <;> linarith [ht.1, ht.2]
  obtain ⟨c, hc, C, hCcount, hCerror⟩ :=
    exists_twoLocal_projectiveTrotterCircuit_normBound
      hn H hlocal τ r hr (hsmall τ hτ)
  have hincrement : HasProjectiveCircuitApproximation n εincrement
      (r * Fintype.card (PauliTracelessLabel n 2))
      (unitaryEvolution H τ) := by
    refine ⟨c, hc, C, hCcount.le, hCerror.trans (hcompiler τ hτ)⟩
  have hcone := projectiveCircuitSeparated_unitaryEvolution_backward_cone
    H hcost hlate hincrement herror
  simpa [τ] using hcone

end

end GaloisForLFunctions.HTGeometry
