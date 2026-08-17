import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityLaw

/-!
# Exact return and operator-norm complexity reflection for the inverse-square chain

The rational inverse-square and inverse-cube coefficients admit the explicit common denominator
`(L!)^3`.  This gives a nonminimal exact return period.  Adjoint reversal of support-certified
local circuits then proves exact operator-norm complexity reflection.  The capstone transfers the
existing laboratory-time floor/ceiling ramp to both sides of the exact return.
-/
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix


open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

theorem factorialCube_mul_invSq_exists {L k : ℕ} (hk0 : 0 < k) (hkL : k ≤ L) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 3) * (1 / (k : ℝ) ^ 2) = N := by
  rcases Nat.dvd_factorial hk0 hkL with ⟨a, ha⟩
  refine ⟨k * a ^ 3, ?_⟩
  rw [ha]
  push_cast
  have hkR : (k : ℝ) ≠ 0 := by positivity
  field_simp

theorem factorialCube_mul_invCube_exists {L k : ℕ} (hk0 : 0 < k) (hkL : k ≤ L) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 3) * (1 / (k : ℝ) ^ 3) = N := by
  rcases Nat.dvd_factorial hk0 hkL with ⟨a, ha⟩
  refine ⟨a ^ 3, ?_⟩
  rw [ha]
  push_cast
  have hkR : (k : ℝ) ≠ 0 := by positivity
  field_simp

def inverseCubeBridgeCount {L : ℕ} (x : Config (PairQubit L)) : ℕ :=
  ∑ j : Fin L, if h : j.val + 1 < L then
    if x (j, true) = true ∧ x (⟨j.val + 1, h⟩, false) = true then 1 else 0
  else 0

theorem inverseCubeBridge_sum_eq_count {L : ℕ} (x : Config (PairQubit L)) :
    (∑ j : Fin L, if h : j.val + 1 < L then
      if x (j, true) = true ∧ x (⟨j.val + 1, h⟩, false) = true then (1 : ℝ) else 0
    else 0) = inverseCubeBridgeCount x := by
  unfold inverseCubeBridgeCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> norm_num

theorem exists_factorialCube_mul_inverseSquareMatchingEnergy {L : ℕ}
    (x : Config (PairQubit L)) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 3) * inverseSquareMatchingEnergy x = N := by
  classical
  have hterm : ∀ j : Fin L, ∃ N : ℕ,
      ((L.factorial : ℝ) ^ 3) *
        (if x (j, false) = true ∧ x (j, true) = true
          then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0) = N := by
    intro j
    by_cases hx : x (j, false) = true ∧ x (j, true) = true
    · rcases factorialCube_mul_invSq_exists (L := L) (k := j.val + 1)
          (by omega) (by omega) with ⟨N, hN⟩
      exact ⟨N, by simpa [hx] using hN⟩
    · exact ⟨0, by simp [hx]⟩
  choose N hN using hterm
  refine ⟨∑ j : Fin L, N j, ?_⟩
  unfold inverseSquareMatchingEnergy
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  convert hN j using 1
  norm_num

theorem exists_factorialCube_mul_inverseCubeBridgeEnergy {L : ℕ} (hL : 0 < L)
    (x : Config (PairQubit L)) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 3) * inverseCubeBridgeEnergy x = N := by
  rcases factorialCube_mul_invCube_exists (L := L) (k := L) hL le_rfl with ⟨a, ha⟩
  refine ⟨a * inverseCubeBridgeCount x, ?_⟩
  rw [inverseCubeBridgeEnergy, inverseCubeBridge_sum_eq_count]
  push_cast
  calc
    ((L.factorial : ℝ) ^ 3) *
        (1 / (L : ℝ) ^ 3 * inverseCubeBridgeCount x) =
        (((L.factorial : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3)) *
          inverseCubeBridgeCount x := by ring
    _ = (a : ℝ) * inverseCubeBridgeCount x := by rw [ha]

theorem exists_factorialCube_mul_inverseSquareChainEnergy {L : ℕ}
    (x : Config (PairQubit L)) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 3) * inverseSquareChainEnergy x = N := by
  rcases exists_factorialCube_mul_inverseSquareMatchingEnergy x with ⟨a, ha⟩
  by_cases hL : L = 0
  · subst L
    refine ⟨a, ?_⟩
    simpa [inverseSquareChainEnergy, inverseCubeBridgeEnergy] using ha
  · rcases exists_factorialCube_mul_inverseCubeBridgeEnergy (Nat.pos_of_ne_zero hL) x with
      ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [inverseSquareChainEnergy, mul_add, ha, hb]
    push_cast
    rfl

noncomputable def inverseSquareChainReturnPeriod (L : ℕ) : ℝ :=
  2 * Real.pi * (L.factorial : ℝ) ^ 3

theorem inverseSquareChain_exact_return (L : ℕ) :
    inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L) = 1 := by
  rw [inverseSquareChainEvolution_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, one_apply, ↓reduceIte]
    rcases exists_factorialCube_mul_inverseSquareChainEnergy x with ⟨N, hN⟩
    have hphase : inverseSquareChainReturnPeriod L * inverseSquareChainEnergy x =
        2 * Real.pi * N := by
      unfold inverseSquareChainReturnPeriod
      rw [mul_assoc, hN]
    have hphaseC : (inverseSquareChainReturnPeriod L : ℂ) *
        (inverseSquareChainEnergy x : ℂ) = ((2 * Real.pi * N : ℝ) : ℂ) := by
      exact_mod_cast hphase
    rw [hphaseC]
    convert Complex.exp_int_mul_two_pi_mul_I (-(N : ℤ)) using 1
    norm_num
    ring_nf
  · simp [Matrix.diagonal, hxy]

theorem inverseSquareChainEvolution_add (L : ℕ) (s t : ℝ) :
    inverseSquareChainEvolution L (s + t) =
      inverseSquareChainEvolution L s * inverseSquareChainEvolution L t := by
  rw [inverseSquareChainEvolution_diagonal, inverseSquareChainEvolution_diagonal,
    inverseSquareChainEvolution_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem inverseSquareChainEvolution_return_reflect (L : ℕ) (t : ℝ) :
    inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L - t) =
      (inverseSquareChainEvolution L t)ᴴ := by
  have hsplit := inverseSquareChainEvolution_add L
      (inverseSquareChainReturnPeriod L - t) t
  have hsum : inverseSquareChainReturnPeriod L - t + t =
      inverseSquareChainReturnPeriod L := by ring
  rw [hsum, inverseSquareChain_exact_return] at hsplit
  have hunit := inverseSquareChainEvolution_unitary L t
  have hright : inverseSquareChainEvolution L t *
      (inverseSquareChainEvolution L t)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hunit
  calc
    inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L - t) =
        inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L - t) * 1 := by simp
    _ = inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L - t) *
        (inverseSquareChainEvolution L t * (inverseSquareChainEvolution L t)ᴴ) := by rw [hright]
    _ = (inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L - t) *
        inverseSquareChainEvolution L t) * (inverseSquareChainEvolution L t)ᴴ := by
          rw [Matrix.mul_assoc]
    _ = (inverseSquareChainEvolution L t)ᴴ := by rw [← hsplit]; simp

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

omit [Fintype Q] in
theorem SeparatesAcross.conjTranspose {A : Finset Q}
    {M : Matrix (Config Q) (Config Q) ℂ} (hM : SeparatesAcross A M) :
    SeparatesAcross A Mᴴ := by
  rcases hM with ⟨MA, MB, hM⟩
  refine ⟨MAᴴ, MBᴴ, fun x y => ?_⟩
  simp only [Matrix.conjTranspose_apply, hM]
  exact map_mul (starRingEnd ℂ) _ _

def adjointLocalGate (g : LocalGate Q) : LocalGate Q where
  support := g.support
  matrix := g.matrixᴴ
  arity_le_two := g.arity_le_two
  unitary := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp g.unitary
  separates := fun A hA => (g.separates A hA).conjTranspose

theorem circuitMatrix_append (c d : List (LocalGate Q)) :
    circuitMatrix (c ++ d) = circuitMatrix c * circuitMatrix d := by
  induction c with
  | nil => simp [circuitMatrix]
  | cons g c ih => simp [circuitMatrix, ih, Matrix.mul_assoc]

def adjointCircuit : List (LocalGate Q) → List (LocalGate Q)
  | [] => []
  | g :: c => adjointCircuit c ++ [adjointLocalGate g]

@[simp] theorem circuitMatrix_adjointCircuit (c : List (LocalGate Q)) :
    circuitMatrix (adjointCircuit c) = (circuitMatrix c)ᴴ := by
  induction c with
  | nil => simp [adjointCircuit, circuitMatrix]
  | cons g c ih =>
      rw [adjointCircuit, circuitMatrix_append, ih]
      simp [circuitMatrix, adjointLocalGate, Matrix.conjTranspose_mul]

theorem twoGateCount_append {L : ℕ} (c d : List (LocalGate (PairQubit L))) :
    twoGateCount (c ++ d) = twoGateCount c + twoGateCount d := by
  induction c with
  | nil => simp [twoGateCount]
  | cons g c ih => simp [twoGateCount, ih, add_assoc]

@[simp] theorem twoGateCount_adjointCircuit {L : ℕ}
    (c : List (LocalGate (PairQubit L))) :
    twoGateCount (adjointCircuit c) = twoGateCount c := by
  induction c with
  | nil => simp [adjointCircuit, twoGateCount]
  | cons g c ih =>
      rw [adjointCircuit, twoGateCount_append, ih]
      simp [twoGateCount, adjointLocalGate, Nat.add_comm]

/-- Operator-norm two-qubit-gate complexity, with `⊤` for an unreachable target. -/
noncomputable def operatorTwoGateComplexity (L : ℕ) (ε t : ℝ) : ℕ∞ :=
  ⨅ c ∈ {c : List (LocalGate (PairQubit L)) | OperatorApproximates t ε c},
    (twoGateCount c : ℕ∞)

theorem operatorTwoGateComplexity_le_of_circuit {L : ℕ} {ε t : ℝ}
    {c : List (LocalGate (PairQubit L))} (hc : OperatorApproximates t ε c) :
    operatorTwoGateComplexity L ε t ≤ (twoGateCount c : ℕ∞) := by
  refine le_trans (iInf_le _ c) ?_
  exact iInf_le
    (fun _ : c ∈ {c : List (LocalGate (PairQubit L)) | OperatorApproximates t ε c} =>
      (twoGateCount c : ℕ∞)) hc

theorem le_operatorTwoGateComplexity_iff {L : ℕ} (ε t : ℝ) (G : ℕ∞) :
    G ≤ operatorTwoGateComplexity L ε t ↔
      ∀ c : List (LocalGate (PairQubit L)),
        OperatorApproximates t ε c → G ≤ (twoGateCount c : ℕ∞) := by
  rw [operatorTwoGateComplexity, le_iInf_iff]
  constructor
  · intro h c hc
    exact le_iInf_iff.mp (h c) hc
  · intro h c
    exact le_iInf fun hc => h c hc

theorem OperatorApproximates.adjointCircuit_return_reflect {L : ℕ} {ε t : ℝ}
    {c : List (LocalGate (PairQubit L))} (hc : OperatorApproximates t ε c) :
    OperatorApproximates (inverseSquareChainReturnPeriod L - t) ε (adjointCircuit c) := by
  unfold OperatorApproximates at hc ⊢
  rw [circuitMatrix_adjointCircuit, inverseSquareChainEvolution_return_reflect]
  calc
    ‖(circuitMatrix c)ᴴ - (inverseSquareChainEvolution L t)ᴴ‖ =
        ‖(circuitMatrix c - inverseSquareChainEvolution L t)ᴴ‖ := by
          rw [Matrix.conjTranspose_sub]
    _ = ‖circuitMatrix c - inverseSquareChainEvolution L t‖ :=
      Matrix.l2_opNorm_conjTranspose _
    _ ≤ ε := hc

/-- Exact return makes operator-norm local-circuit complexity palindromic. -/
theorem operatorTwoGateComplexity_exact_return_reflect (L : ℕ) (ε t : ℝ) :
    operatorTwoGateComplexity L ε (inverseSquareChainReturnPeriod L - t) =
      operatorTwoGateComplexity L ε t := by
  apply le_antisymm
  · rw [le_operatorTwoGateComplexity_iff]
    intro c hc
    have hadj := hc.adjointCircuit_return_reflect
    simpa using operatorTwoGateComplexity_le_of_circuit hadj
  · rw [le_operatorTwoGateComplexity_iff]
    intro c hc
    have hadj := hc.adjointCircuit_return_reflect
    have htime : inverseSquareChainReturnPeriod L -
        (inverseSquareChainReturnPeriod L - t) = t := by ring
    rw [htime] at hadj
    simpa using operatorTwoGateComplexity_le_of_circuit hadj

theorem inverseSquareChain_operatorComplexity_floor_ceil {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexity L ε t ∧
      operatorTwoGateComplexity L ε t ≤
        ((⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) := by
  have hramp := inverseSquareChain_floor_ceil_growth hε hεmax htMin htLab
  constructor
  · rw [le_operatorTwoGateComplexity_iff]
    intro c hc
    exact_mod_cast hramp.1 c hc
  · rcases hramp.2 with ⟨c, hcost, herr⟩
    have hc : OperatorApproximates t ε c := le_of_lt herr
    have hle := operatorTwoGateComplexity_le_of_circuit hc
    rwa [hcost] at hle

/-- One connected static chain has a linear laboratory-time complexity excursion and an exact
factorial-cube return; both sides of the return carry the same floor/ceiling bounds. -/
theorem inverseSquareChain_growth_exactReturn_reflection {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    inverseSquareChainEvolution L (inverseSquareChainReturnPeriod L) = 1 ∧
      operatorTwoGateComplexity L ε (inverseSquareChainReturnPeriod L - t) =
        operatorTwoGateComplexity L ε t ∧
      ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexity L ε t ∧
      operatorTwoGateComplexity L ε t ≤ ((⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) ∧
      ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexity L ε (inverseSquareChainReturnPeriod L - t) ∧
      operatorTwoGateComplexity L ε (inverseSquareChainReturnPeriod L - t) ≤
        ((⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) := by
  have href := operatorTwoGateComplexity_exact_return_reflect L ε t
  have hb := inverseSquareChain_operatorComplexity_floor_ceil hε hεmax htMin htLab
  refine ⟨inverseSquareChain_exact_return L, href, hb.1, hb.2, ?_, ?_⟩
  · rw [href]
    exact hb.1
  · rw [href]
    exact hb.2

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

