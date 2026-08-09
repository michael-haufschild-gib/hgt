import GaloisForLFunctions.HTGeometry.InterfinityGeometry.GramStateSystem

/-!
# A nonfillable Gram-labelled horn

Three experiments in `ℂ³` are clocked by a two-periodic source system: one vector is constant,
and the other two exchange places between even and odd steps.  Every pairwise overlap limit is
realized on a cofinal synchronization, and the proposed full Gram label

`G = !![1, 1/2, 1/2; 1/2, 1, 0; 1/2, 0, 1]`

is strictly positive definite; nevertheless no single synchronization realizes it, so the
two-edge horn has no filler.

A second, three-periodic system adds one state whose Gram matrix is exactly `G`.  Its labelled
one-skeleton is the same as that of the two-periodic system, but only it realizes the `G`-labelled
triangle.  Hence the labelled one-skeleton does not determine the two-simplices.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open Filter Topology

noncomputable section

/-! ## Three unit vectors in `ℂ³` -/

/-- The ambient one-particle space of the model. -/
abbrev ParityH := EuclideanSpace ℂ (Fin 3)

/-- A vector of `ℂ³` with real coordinates. -/
def evec (a b c : ℝ) : ParityH := WithLp.toLp 2 ![(a : ℂ), (b : ℂ), (c : ℂ)]

theorem inner_evec (a b c a' b' c' : ℝ) :
    (inner ℂ (evec a b c) (evec a' b' c') : ℂ) = ((a * a' + b * b' + c * c' : ℝ) : ℂ) := by
  simp [evec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

private theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

private theorem sq_sqrt_three : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

private theorem sq_sqrt_twothirds : Real.sqrt (2 / 3) * Real.sqrt (2 / 3) = 2 / 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- The constant experiment vector. -/
def vecA : ParityH := evec 1 0 0

/-- The second experiment vector of the even state. -/
def vecB : ParityH := evec (1 / 2) (Real.sqrt 3 / 2) 0

/-- The third experiment vector of the even state. -/
def vecC : ParityH := evec 0 0 1

/-- The third experiment vector of the extra three-periodic state. -/
def vecC' : ParityH := evec (1 / 2) (-(1 / (2 * Real.sqrt 3))) (Real.sqrt (2 / 3))

theorem norm_eq_one_of_inner_self {v : ParityH} (h : (inner ℂ v v : ℂ) = 1) : ‖v‖ = 1 := by
  have h1 : ‖v‖ ^ 2 = RCLike.re (inner ℂ v v : ℂ) := norm_sq_eq_re_inner v
  rw [h] at h1
  norm_num at h1
  rcases h1 with h1 | h1
  · exact h1
  · linarith [norm_nonneg v]

@[simp] theorem inner_vecA_vecA : (inner ℂ vecA vecA : ℂ) = 1 := by
  rw [vecA, inner_evec, show ((1 : ℝ) * 1 + 0 * 0 + 0 * 0) = 1 by ring]
  norm_num

@[simp] theorem inner_vecB_vecB : (inner ℂ vecB vecB : ℂ) = 1 := by
  rw [vecB, inner_evec,
    show ((1 : ℝ) / 2 * (1 / 2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) + 0 * 0) = 1 by
      nlinarith [sq_sqrt_three]]
  norm_num

@[simp] theorem inner_vecC_vecC : (inner ℂ vecC vecC : ℂ) = 1 := by
  rw [vecC, inner_evec, show ((0 : ℝ) * 0 + 0 * 0 + 1 * 1) = 1 by ring]
  norm_num

@[simp] theorem inner_vecC'_vecC' : (inner ℂ vecC' vecC' : ℂ) = 1 := by
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt_three_pos
  rw [vecC', inner_evec,
    show ((1 : ℝ) / 2 * (1 / 2) + -(1 / (2 * Real.sqrt 3)) * -(1 / (2 * Real.sqrt 3)) +
        Real.sqrt (2 / 3) * Real.sqrt (2 / 3)) = 1 by
      rw [sq_sqrt_twothirds]
      field_simp
      nlinarith [sq_sqrt_three]]
  norm_num

@[simp] theorem inner_vecA_vecB : (inner ℂ vecA vecB : ℂ) = 1 / 2 := by
  rw [vecA, vecB, inner_evec,
    show ((1 : ℝ) * (1 / 2) + 0 * (Real.sqrt 3 / 2) + 0 * 0) = 1 / 2 by ring]
  norm_num

@[simp] theorem inner_vecB_vecA : (inner ℂ vecB vecA : ℂ) = 1 / 2 := by
  rw [vecA, vecB, inner_evec,
    show ((1 : ℝ) / 2 * 1 + Real.sqrt 3 / 2 * 0 + 0 * 0) = 1 / 2 by ring]
  norm_num

@[simp] theorem inner_vecA_vecC : (inner ℂ vecA vecC : ℂ) = 0 := by
  rw [vecA, vecC, inner_evec, show ((1 : ℝ) * 0 + 0 * 0 + 0 * 1) = 0 by ring]
  norm_num

@[simp] theorem inner_vecC_vecA : (inner ℂ vecC vecA : ℂ) = 0 := by
  rw [vecA, vecC, inner_evec, show ((0 : ℝ) * 1 + 0 * 0 + 1 * 0) = 0 by ring]
  norm_num

@[simp] theorem inner_vecB_vecC : (inner ℂ vecB vecC : ℂ) = 0 := by
  rw [vecB, vecC, inner_evec,
    show ((1 : ℝ) / 2 * 0 + Real.sqrt 3 / 2 * 0 + 0 * 1) = 0 by ring]
  norm_num

@[simp] theorem inner_vecC_vecB : (inner ℂ vecC vecB : ℂ) = 0 := by
  rw [vecB, vecC, inner_evec,
    show ((0 : ℝ) * (1 / 2) + 0 * (Real.sqrt 3 / 2) + 1 * 0) = 0 by ring]
  norm_num

@[simp] theorem inner_vecA_vecC' : (inner ℂ vecA vecC' : ℂ) = 1 / 2 := by
  rw [vecA, vecC', inner_evec,
    show ((1 : ℝ) * (1 / 2) + 0 * -(1 / (2 * Real.sqrt 3)) + 0 * Real.sqrt (2 / 3)) = 1 / 2 by
      ring]
  norm_num

@[simp] theorem inner_vecC'_vecA : (inner ℂ vecC' vecA : ℂ) = 1 / 2 := by
  rw [vecA, vecC', inner_evec,
    show ((1 : ℝ) / 2 * 1 + -(1 / (2 * Real.sqrt 3)) * 0 + Real.sqrt (2 / 3) * 0) = 1 / 2 by
      ring]
  norm_num

@[simp] theorem inner_vecB_vecC' : (inner ℂ vecB vecC' : ℂ) = 0 := by
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt_three_pos
  rw [vecB, vecC', inner_evec,
    show ((1 : ℝ) / 2 * (1 / 2) + Real.sqrt 3 / 2 * -(1 / (2 * Real.sqrt 3)) +
        0 * Real.sqrt (2 / 3)) = 0 by field_simp; ring]
  norm_num

@[simp] theorem inner_vecC'_vecB : (inner ℂ vecC' vecB : ℂ) = 0 := by
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt_three_pos
  rw [vecB, vecC', inner_evec,
    show ((1 : ℝ) / 2 * (1 / 2) + -(1 / (2 * Real.sqrt 3)) * (Real.sqrt 3 / 2) +
        Real.sqrt (2 / 3) * 0) = 0 by field_simp; ring]
  norm_num

@[simp] theorem norm_vecA : ‖vecA‖ = 1 := norm_eq_one_of_inner_self inner_vecA_vecA
@[simp] theorem norm_vecB : ‖vecB‖ = 1 := norm_eq_one_of_inner_self inner_vecB_vecB
@[simp] theorem norm_vecC : ‖vecC‖ = 1 := norm_eq_one_of_inner_self inner_vecC_vecC
@[simp] theorem norm_vecC' : ‖vecC'‖ = 1 := norm_eq_one_of_inner_self inner_vecC'_vecC'

/-! ## The two source systems -/

/-- The three source experiments. -/
abbrev ParityLabel := Fin 3

/-- Vectors of the two-periodic system: the second and third experiment exchange places. -/
def xVec : Fin 2 → ParityLabel → ParityH := ![![vecA, vecB, vecC], ![vecA, vecC, vecB]]

/-- Vectors of the three-periodic system: one extra state realizes the full Gram label. -/
def yVec : Fin 3 → ParityLabel → ParityH :=
  ![![vecA, vecB, vecC'], ![vecA, vecB, vecC], ![vecA, vecC, vecB]]

/-- Clocked overlaps of the two-periodic system. -/
def xWeight (s : Fin 2) (a b : ParityLabel) : ℂ := inner ℂ (xVec s a) (xVec s b)

/-- Clocked overlaps of the three-periodic system. -/
def yWeight (s : Fin 3) (a b : ParityLabel) : ℂ := inner ℂ (yVec s a) (yVec s b)

/-- The even-state Gram matrix. -/
def mEven : Matrix ParityLabel ParityLabel ℂ := !![1, 1/2, 0; 1/2, 1, 0; 0, 0, 1]

/-- The odd-state Gram matrix. -/
def mOdd : Matrix ParityLabel ParityLabel ℂ := !![1, 0, 1/2; 0, 1, 0; 1/2, 0, 1]

/-- The Gram matrix of the extra three-periodic state. -/
def mFull : Matrix ParityLabel ParityLabel ℂ := !![1, 1/2, 1/2; 1/2, 1, 0; 1/2, 0, 1]

theorem xWeight_zero (a b : ParityLabel) : xWeight 0 a b = mEven a b := by
  fin_cases a <;> fin_cases b <;> simp [xWeight, xVec, mEven]

theorem xWeight_one (a b : ParityLabel) : xWeight 1 a b = mOdd a b := by
  fin_cases a <;> fin_cases b <;> simp [xWeight, xVec, mOdd]

theorem yWeight_zero (a b : ParityLabel) : yWeight 0 a b = mFull a b := by
  fin_cases a <;> fin_cases b <;> simp [yWeight, yVec, mFull]

theorem yWeight_one (a b : ParityLabel) : yWeight 1 a b = mEven a b := by
  fin_cases a <;> fin_cases b <;> simp [yWeight, yVec, mEven]

theorem yWeight_two (a b : ParityLabel) : yWeight 2 a b = mOdd a b := by
  fin_cases a <;> fin_cases b <;> simp [yWeight, yVec, mOdd]

private theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by revert x; decide

private theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by revert x; decide

/-! ## The clocks -/

/-- The `k`-periodic clock. -/
def clockState (k : ℕ) [NeZero k] (n : ℕ) : Fin k :=
  ⟨n % k, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))⟩

theorem cofinal_clockState (k : ℕ) [NeZero k] (s : Fin k) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ clockState k n = s := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (NeZero.ne k)
  refine ⟨k * N + s.val, ?_, ?_⟩
  · calc N = 1 * N := (one_mul N).symm
      _ ≤ k * N := Nat.mul_le_mul_right N hk
      _ ≤ k * N + s.val := Nat.le_add_right _ _
  · apply Fin.ext
    show (k * N + s.val) % k = s.val
    rw [show k * N + s.val = s.val + k * N by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt s.isLt]

/-- The two-periodic realizability datum. -/
def xDatum : GramNerveDatum ParityLabel :=
  stateOverlapDatum (fun _ => True) (clockState 2) xWeight

/-- The three-periodic realizability datum. -/
def yDatum : GramNerveDatum ParityLabel :=
  stateOverlapDatum (fun _ => True) (clockState 3) yWeight

theorem xRealizes_iff {n : ℕ} (p : GramSimplex ParityLabel n) :
    xDatum.Realizes p ↔ ∃ s : Fin 2, ∀ r r', p.2 r r' = xWeight s (p.1 r) (p.1 r') := by
  rw [xDatum, realizes_stateOverlapDatum_iff (cofinal_clockState 2)]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => trivial, h⟩⟩

theorem yRealizes_iff {n : ℕ} (p : GramSimplex ParityLabel n) :
    yDatum.Realizes p ↔ ∃ s : Fin 3, ∀ r r', p.2 r r' = yWeight s (p.1 r) (p.1 r') := by
  rw [yDatum, realizes_stateOverlapDatum_iff (cofinal_clockState 3)]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => trivial, h⟩⟩

/-! ## The horn and the proposed filler -/

/-- The labelled edge with a prescribed overlap. -/
def edgeLabel (g : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, g; g, 1]

/-- The two-edge horn: the vertices `A, B` and `A, C` with overlap `1/2`. -/
def hornEdgeAB : GramSimplex ParityLabel 2 := (![0, 1], edgeLabel (1/2))

/-- The second edge of the horn. -/
def hornEdgeAC : GramSimplex ParityLabel 2 := (![0, 2], edgeLabel (1/2))

/-- The proposed triangle with the full Gram label. -/
def fullTriangle : GramSimplex ParityLabel 3 := (![0, 1, 2], mFull)

theorem xRealizes_hornEdgeAB : xDatum.Realizes hornEdgeAB := by
  rw [xRealizes_iff]
  refine ⟨0, ?_⟩
  intro r r'
  rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
    simp [hornEdgeAB, edgeLabel, xWeight_zero, mEven]

theorem xRealizes_hornEdgeAC : xDatum.Realizes hornEdgeAC := by
  rw [xRealizes_iff]
  refine ⟨1, ?_⟩
  intro r r'
  rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
    simp [hornEdgeAC, edgeLabel, xWeight_one, mOdd]

/-- **The horn has no filler.**  No single synchronization of the two-periodic system realizes the
full Gram label. -/
theorem not_xRealizes_fullTriangle : ¬ xDatum.Realizes fullTriangle := by
  rw [xRealizes_iff]
  rintro ⟨s, hs⟩
  rcases fin2_cases s with rfl | rfl
  · have h := hs 0 2
    simp [fullTriangle, mFull, xWeight_zero, mEven] at h
  · have h := hs 0 1
    simp [fullTriangle, mFull, xWeight_one, mOdd] at h

/-- **The three-periodic system realizes the triangle.** -/
theorem yRealizes_fullTriangle : yDatum.Realizes fullTriangle := by
  rw [yRealizes_iff]
  refine ⟨0, ?_⟩
  intro r r'
  rcases fin3_cases r with rfl | rfl | rfl <;> rcases fin3_cases r' with rfl | rfl | rfl <;>
    simp [fullTriangle, yWeight_zero]

/-! ## The proposed label is a strictly positive definite Gram matrix -/

theorem mFull_det : mFull.det = 1 / 2 := by
  simp [mFull, Matrix.det_fin_three]
  norm_num

theorem mFull_isHermitian : mFull.IsHermitian := by
  show Matrix.conjTranspose mFull = mFull
  ext a b
  fin_cases a <;> fin_cases b <;> simp [mFull, Matrix.conjTranspose_apply]

/-! ## The labelled one-skeleta agree -/

/-- On any pair of labels the extra state reproduces one of the two-periodic states. -/
theorem exists_xWeight_matching (a : Fin 2 → ParityLabel) :
    ∃ s : Fin 2, ∀ r r', mFull (a r) (a r') = xWeight s (a r) (a r') := by
  have h0 : ∀ x : ParityLabel, x = 0 ∨ x = 1 ∨ x = 2 := fin3_cases
  rcases h0 (a 0) with e0 | e0 | e0 <;> rcases h0 (a 1) with e1 | e1 | e1
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩
  · exact ⟨1, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_one, mFull, mOdd]⟩
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩
  · exact ⟨1, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_one, mFull, mOdd]⟩
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩
  · exact ⟨0, fun r r' => by
      rcases fin2_cases r with rfl | rfl <;> rcases fin2_cases r' with rfl | rfl <;>
        simp [e0, e1, xWeight_zero, mFull, mEven]⟩

/-- **The two systems have the same labelled one-skeleton.** -/
theorem edge_realizes_iff (p : GramSimplex ParityLabel 2) :
    xDatum.Realizes p ↔ yDatum.Realizes p := by
  rw [xRealizes_iff, yRealizes_iff]
  constructor
  · rintro ⟨s, hs⟩
    rcases fin2_cases s with rfl | rfl
    · exact ⟨1, fun r r' => by rw [hs r r', xWeight_zero, ← yWeight_one]⟩
    · exact ⟨2, fun r r' => by rw [hs r r', xWeight_one, ← yWeight_two]⟩
  · rintro ⟨s, hs⟩
    rcases fin3_cases s with rfl | rfl | rfl
    · obtain ⟨s', hs'⟩ := exists_xWeight_matching p.1
      exact ⟨s', fun r r' => by rw [hs r r', yWeight_zero, hs' r r']⟩
    · exact ⟨0, fun r r' => by rw [hs r r', yWeight_one, ← xWeight_zero]⟩
    · exact ⟨1, fun r r' => by rw [hs r r', yWeight_two, ← xWeight_one]⟩

/-- The full Gram label is the Gram matrix of three unit vectors of `ℂ³`. -/
theorem mFull_eq_gram (a b : ParityLabel) : mFull a b = inner ℂ (yVec 0 a) (yVec 0 b) :=
  (yWeight_zero a b).symm

end

end GaloisForLFunctions.HTGeometry.Interfinity
