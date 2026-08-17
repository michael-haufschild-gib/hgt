import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

def pairSupport {L : ℕ} (j : Fin L) : Finset (PairQubit L) :=
  {(j, false), (j, true)}

@[simp] theorem pairSupport_card {L : ℕ} (j : Fin L) : (pairSupport j).card = 2 := by
  simp [pairSupport]

noncomputable def pairPhaseValue {L : ℕ} (j : Fin L) (θ : ℝ)
    (x : Config (PairQubit L)) : ℂ :=
  if x (j, false) = true ∧ x (j, true) = true
    then Complex.exp (-(Complex.I * (θ : ℂ))) else 1

noncomputable def pairPhaseMatrix {L : ℕ} (j : Fin L) (θ : ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal (pairPhaseValue j θ)

theorem pairPhaseMatrix_unitary {L : ℕ} (j : Fin L) (θ : ℝ) :
    pairPhaseMatrix j θ ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
  apply mem_unitaryGroup_diagonal_general
  intro x
  unfold pairPhaseValue
  split_ifs
  · rw [Complex.norm_exp]
    simp
  · norm_num

set_option maxHeartbeats 10000 in
theorem pairPhaseMatrix_separates {L : ℕ} (j : Fin L) (θ : ℝ)
    (A : Finset (PairQubit L))
    (hcut : pairSupport j ⊆ A ∨ Disjoint (pairSupport j) A) :
    SeparatesAcross A (pairPhaseMatrix j θ) := by
  rcases hcut with hinside | houtside
  · have hj0 : (j, false) ∈ A := hinside (by simp [pairSupport])
    have hj1 : (j, true) ∈ A := hinside (by simp [pairSupport])
    let f : On A → ℂ := fun z =>
      if z ⟨(j, false), hj0⟩ = true ∧ z ⟨(j, true), hj1⟩ = true
        then Complex.exp (-(Complex.I * (θ : ℂ))) else 1
    rcases separatesAcross_diagonal_fst A f with ⟨MA, MB, hsep⟩
    refine ⟨MA, MB, fun x y => ?_⟩
    rw [← hsep x y]
    by_cases hxy : x = y
    · subst y
      simp [pairPhaseMatrix, pairPhaseValue, f]
    · simp [pairPhaseMatrix, Matrix.diagonal, hxy]
  · have hj0 : (j, false) ∉ A := by
      intro h
      exact (Finset.disjoint_left.mp houtside) (by simp [pairSupport]) h
    have hj1 : (j, true) ∉ A := by
      intro h
      exact (Finset.disjoint_left.mp houtside) (by simp [pairSupport]) h
    let f : Off A → ℂ := fun z =>
      if z ⟨(j, false), hj0⟩ = true ∧ z ⟨(j, true), hj1⟩ = true
        then Complex.exp (-(Complex.I * (θ : ℂ))) else 1
    rcases separatesAcross_diagonal_snd A f with ⟨MA, MB, hsep⟩
    refine ⟨MA, MB, fun x y => ?_⟩
    rw [← hsep x y]
    by_cases hxy : x = y
    · subst y
      simp [pairPhaseMatrix, pairPhaseValue, f]
    · simp [pairPhaseMatrix, Matrix.diagonal, hxy]

noncomputable def pairPhaseGate {L : ℕ} (j : Fin L) (θ : ℝ) :
    LocalGate (PairQubit L) where
  support := pairSupport j
  matrix := pairPhaseMatrix j θ
  arity_le_two := by simp
  unitary := pairPhaseMatrix_unitary j θ
  separates := pairPhaseMatrix_separates j θ

noncomputable def matchingPhaseCircuit {L : ℕ} (js : List (Fin L)) (t : ℝ) :
    List (LocalGate (PairQubit L)) :=
  js.map (fun j => pairPhaseGate j (t / (((j.val + 1 : ℕ) : ℝ) ^ 2)))

noncomputable def listMatchingEnergy {L : ℕ} (js : List (Fin L))
    (x : Config (PairQubit L)) : ℝ :=
  (js.map fun j => if x (j, false) = true ∧ x (j, true) = true
    then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0).sum

set_option maxHeartbeats 10000 in
theorem matchingPhaseCircuit_matrix {L : ℕ} (js : List (Fin L)) (t : ℝ) :
    circuitMatrix (matchingPhaseCircuit js t) =
      Matrix.diagonal (fun x =>
        Complex.exp (-(Complex.I * (t * listMatchingEnergy js x)))) := by
  induction js with
  | nil =>
      ext x y
      simp [matchingPhaseCircuit, circuitMatrix, listMatchingEnergy]
  | cons j js ih =>
      rw [matchingPhaseCircuit, List.map_cons, circuitMatrix]
      change pairPhaseMatrix j (t / (((j.val + 1 : ℕ) : ℝ) ^ 2)) *
          circuitMatrix (matchingPhaseCircuit js t) = _
      rw [ih, pairPhaseMatrix, Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      unfold pairPhaseValue listMatchingEnergy
      by_cases hx : x (j, false) = true ∧ x (j, true) = true
      · simp only [List.map_cons, List.sum_cons]
        rw [if_pos hx, if_pos hx]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      · simp [hx]

@[simp] theorem matchingPhaseCircuit_twoGateCount {L : ℕ} (js : List (Fin L)) (t : ℝ) :
    twoGateCount (matchingPhaseCircuit js t) = js.length := by
  induction js with
  | nil => simp [matchingPhaseCircuit, twoGateCount]
  | cons j js ih =>
      rw [matchingPhaseCircuit, List.map_cons, twoGateCount]
      have hcard : (pairPhaseGate j (t / (((j.val + 1 : ℕ) : ℝ) ^ 2))).support.card = 2 := by
        simp [pairPhaseGate]
      rw [if_pos hcard]
      change 1 + twoGateCount (matchingPhaseCircuit js t) = js.length + 1
      rw [ih]
      omega

noncomputable def pairMatchingWeight {L : ℕ} (x : Config (PairQubit L)) (j : Fin L) : ℝ :=
  if x (j, false) = true ∧ x (j, true) = true
    then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0

theorem inverseSquareMatchingEnergy_eq_sum_pairMatchingWeight {L : ℕ}
    (x : Config (PairQubit L)) :
    inverseSquareMatchingEnergy x = ∑ j : Fin L, pairMatchingWeight x j := by
  rfl

def initialPairEmbedding {L K : ℕ} (hKL : K ≤ L) : Fin K → Fin L :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt hKL⟩

def initialPairList {L K : ℕ} (hKL : K ≤ L) : List (Fin L) :=
  List.ofFn (initialPairEmbedding hKL)

@[simp] theorem initialPairList_length {L K : ℕ} (hKL : K ≤ L) :
    (initialPairList hKL).length = K := by
  simp [initialPairList]

def initialPairs (L K : ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => j.val < K)

def tailPairs (L K : ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => K ≤ j.val)

theorem listMatchingEnergy_initialPairList {L K : ℕ} (hKL : K ≤ L)
    (x : Config (PairQubit L)) :
    listMatchingEnergy (initialPairList hKL) x =
      ∑ j ∈ initialPairs L K, pairMatchingWeight x j := by
  unfold listMatchingEnergy initialPairList
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_bij (fun i _ => initialPairEmbedding hKL i) ?_ ?_ ?_ ?_
  · intro i hi
    simp [initialPairs, initialPairEmbedding]
  · intro i hi j hj hij
    apply Fin.ext
    simpa [initialPairEmbedding] using congrArg Fin.val hij
  · intro j hj
    have hjK : j.val < K := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjK⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i hi
    rfl

theorem initialPairList_twoGateCount {L K : ℕ} (hKL : K ≤ L) (t : ℝ) :
    twoGateCount (matchingPhaseCircuit (initialPairList hKL) t) = K := by
  simp

theorem sum_tailPairs_inv_sq_eq_Ioc (L K : ℕ) :
    ∑ j ∈ tailPairs L K, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) =
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 2 := by
  refine Finset.sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
  · intro j hj
    have hjK : K ≤ j.val := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_Ioc]
    exact ⟨by omega, by omega⟩
  · intro i hi j hj hij
    exact Fin.ext (Nat.add_right_cancel hij)
  · intro n hn
    have hnK : K < n := (Finset.mem_Ioc.mp hn).1
    have hnL : n ≤ L := (Finset.mem_Ioc.mp hn).2
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le K) hnK
    let j : Fin L := ⟨n - 1, by omega⟩
    refine ⟨j, ?_, ?_⟩
    simp [tailPairs, j]
    omega
    · dsimp [j]
      omega
  · intro j hj
    rfl

theorem pairMatchingWeight_nonneg {L : ℕ} (x : Config (PairQubit L)) (j : Fin L) :
    0 ≤ pairMatchingWeight x j := by
  unfold pairMatchingWeight
  split_ifs <;> positivity

theorem pairMatchingWeight_le_inv_sq {L : ℕ} (x : Config (PairQubit L)) (j : Fin L) :
    pairMatchingWeight x j ≤ 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) := by
  unfold pairMatchingWeight
  split_ifs
  · exact le_rfl
  · positivity

theorem inverseSquareMatchingEnergy_le_initial_add_tail {L K : ℕ}
    (hKL : K ≤ L) (x : Config (PairQubit L)) :
    inverseSquareMatchingEnergy x ≤ listMatchingEnergy (initialPairList hKL) x +
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 2 := by
  rw [inverseSquareMatchingEnergy_eq_sum_pairMatchingWeight,
    listMatchingEnergy_initialPairList hKL, ← sum_tailPairs_inv_sq_eq_Ioc]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin L => j.val < K) (pairMatchingWeight x)
  have hfirst : Finset.univ.filter (fun j : Fin L => j.val < K) = initialPairs L K := rfl
  have htail : Finset.univ.filter (fun j : Fin L => ¬j.val < K) = tailPairs L K := by
    ext j
    simp [tailPairs]
  rw [hfirst, htail] at hsplit
  rw [← hsplit]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j hj
  exact pairMatchingWeight_le_inv_sq x j

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
