import GaloisForLFunctions.HTGeometry.CoherenceFlatness
import GaloisForLFunctions.RHTower.XiPrimeMarkedCycleRelocation

/-!
# Switching gauge and cycle obstruction for Route K

Finite marked-prime characteristic determinants are invariant under simultaneous row/column sign
switching.  The Boolean flatness theorem upgrades this elementary similarity law to an exact graph
statement: every symmetric edge-sign field with trivial closed-walk holonomy is determinant-blind
on a matrix supported by its connected graph.  Reflection pairing cannot recover that erased data.

Together with `XiPrimeMarkedCycleRelocation`, this isolates the finite boundary sharply.  Flat
edge signs are gauge; a nonzero triangle holonomy can be determinant-visible and remains visible
after centered reflection pairing.  No infinite trace-class correction or Xi determinant identity
is assumed here.
-/

open scoped Matrix

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Real sign represented by a Boolean switching coordinate. -/
def routeKBoolSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem routeKBoolSign_false : routeKBoolSign false = 1 := rfl

@[simp] theorem routeKBoolSign_true : routeKBoolSign true = -1 := rfl

@[simp] theorem routeKBoolSign_sq (b : Bool) :
    routeKBoolSign b * routeKBoolSign b = 1 := by
  cases b <;> norm_num

@[simp] theorem routeKBoolSign_xor (a b : Bool) :
    routeKBoolSign (Bool.xor a b) = routeKBoolSign a * routeKBoolSign b := by
  cases a <;> cases b <;> norm_num [routeKBoolSign]

/-- Simultaneous row/column sign switching. -/
def routeKDiagonalSignGauge {ι : Type*}
    (ε : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => ε i * A i j * ε j

theorem routeKDiagonalSignGauge_eq_diagonal_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (A : Matrix ι ι ℝ) :
    routeKDiagonalSignGauge ε A =
      Matrix.diagonal ε * A * Matrix.diagonal ε := by
  ext i j
  simp [routeKDiagonalSignGauge, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Characteristic determinant for a finite marked-prime packet. -/
def routeKFiniteCharacteristic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (w : ℝ) : ℝ :=
  (w • (1 : Matrix ι ι ℝ) - A).det

/-- Any involutive diagonal sign switching preserves the characteristic determinant. -/
theorem routeKFiniteCharacteristic_signGauge_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (A : Matrix ι ι ℝ) (w : ℝ) :
    routeKFiniteCharacteristic (routeKDiagonalSignGauge ε A) w =
      routeKFiniteCharacteristic A w := by
  let D : Matrix ι ι ℝ := Matrix.diagonal ε
  have hconj :
      w • (1 : Matrix ι ι ℝ) - routeKDiagonalSignGauge ε A =
        D * (w • (1 : Matrix ι ι ℝ) - A) * D := by
    ext i j
    simp only [D, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst j
      simp [routeKDiagonalSignGauge]
      calc
        w - ε i * A i i * ε i =
            w * (ε i * ε i) - ε i * A i i * ε i := by
              rw [hε i, mul_one]
        _ = ε i * (w - A i i) * ε i := by ring
    · simp [routeKDiagonalSignGauge, hij]
  have hdetSq : D.det * D.det = 1 := by
    dsimp [D]
    rw [Matrix.det_diagonal, ← Finset.prod_mul_distrib]
    simp [hε]
  rw [routeKFiniteCharacteristic, routeKFiniteCharacteristic, hconj,
    Matrix.det_mul, Matrix.det_mul]
  calc
    D.det * (w • (1 : Matrix ι ι ℝ) - A).det * D.det =
        (D.det * D.det) * (w • (1 : Matrix ι ι ℝ) - A).det := by ring
    _ = (w • (1 : Matrix ι ι ℝ) - A).det := by rw [hdetSq, one_mul]

/-- Boolean vertex switching is a determinant gauge on every finite packet. -/
theorem routeKFiniteCharacteristic_booleanGauge_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → Bool) (A : Matrix ι ι ℝ) (w : ℝ) :
    routeKFiniteCharacteristic
        (routeKDiagonalSignGauge (fun i => routeKBoolSign (ε i)) A) w =
      routeKFiniteCharacteristic A w := by
  apply routeKFiniteCharacteristic_signGauge_eq
  intro i
  exact routeKBoolSign_sq (ε i)

/-- Twist only graph-supported off-diagonal entries by a Boolean edge field. -/
def routeKGraphEdgeTwist {ι : Type*}
    (G : SimpleGraph ι) [DecidableRel G.Adj] (c : ι → ι → Bool)
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if G.Adj i j then routeKBoolSign (c i j) * A i j else A i j

/-- A flat symmetric edge field on a connected support graph is exactly one diagonal sign gauge
on every matrix supported by that graph. -/
theorem exists_routeKGraphEdgeTwist_eq_diagonalSignGauge_of_flat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [DecidableRel G.Adj] (hG : G.Connected)
    (c : ι → ι → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c)
    (hflat : BooleanEdgeFieldFlat G c)
    (A : Matrix ι ι ℝ)
    (hsupport : ∀ ⦃i j⦄, i ≠ j → ¬G.Adj i j → A i j = 0) :
    ∃ ε : ι → Bool,
      routeKGraphEdgeTwist G c A =
        routeKDiagonalSignGauge (fun i => routeKBoolSign (ε i)) A := by
  obtain ⟨ε, hε⟩ := exists_booleanOrientation_of_flat hG c hsymm hflat
  refine ⟨ε, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp [routeKGraphEdgeTwist, routeKDiagonalSignGauge]
    calc
      A i i = A i i * (routeKBoolSign (ε i) * routeKBoolSign (ε i)) := by
        rw [routeKBoolSign_sq, mul_one]
      _ = routeKBoolSign (ε i) * A i i * routeKBoolSign (ε i) := by ring
  · by_cases hadj : G.Adj i j
    · rw [routeKGraphEdgeTwist]
      simp only [hε hadj, hadj, if_true, routeKBoolSign_xor,
        routeKDiagonalSignGauge]
      ring
    · have hzero := hsupport hij hadj
      simp [routeKGraphEdgeTwist, routeKDiagonalSignGauge, hadj, hzero]

/-- Closed-walk-flat edge signs cannot change any finite characteristic determinant. -/
theorem routeKFiniteCharacteristic_graphEdgeTwist_eq_of_flat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [DecidableRel G.Adj] (hG : G.Connected)
    (c : ι → ι → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c)
    (hflat : BooleanEdgeFieldFlat G c)
    (A : Matrix ι ι ℝ)
    (hsupport : ∀ ⦃i j⦄, i ≠ j → ¬G.Adj i j → A i j = 0)
    (w : ℝ) :
    routeKFiniteCharacteristic (routeKGraphEdgeTwist G c A) w =
      routeKFiniteCharacteristic A w := by
  obtain ⟨ε, hgauge⟩ :=
    exists_routeKGraphEdgeTwist_eq_diagonalSignGauge_of_flat
      hG c hsymm hflat A hsupport
  rw [hgauge]
  exact routeKFiniteCharacteristic_booleanGauge_eq ε A w

/-- Reflection pairing does not recover information erased by a flat switching gauge. -/
theorem routeKFinitePairedCharacteristic_graphEdgeTwist_eq_of_flat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [DecidableRel G.Adj] (hG : G.Connected)
    (c : ι → ι → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c)
    (hflat : BooleanEdgeFieldFlat G c)
    (A : Matrix ι ι ℝ)
    (hsupport : ∀ ⦃i j⦄, i ≠ j → ¬G.Adj i j → A i j = 0)
    (w : ℝ) :
    routeKFiniteCharacteristic (routeKGraphEdgeTwist G c A) w *
        routeKFiniteCharacteristic (routeKGraphEdgeTwist G c A) (-w) =
      routeKFiniteCharacteristic A w * routeKFiniteCharacteristic A (-w) := by
  rw [routeKFiniteCharacteristic_graphEdgeTwist_eq_of_flat
      hG c hsymm hflat A hsupport w,
    routeKFiniteCharacteristic_graphEdgeTwist_eq_of_flat
      hG c hsymm hflat A hsupport (-w)]

/-- Trace-power cumulant of the three-prime relocation packet. -/
def routeKThreePrimeTracePower
    (q edge : Fin 3 → ℝ) (m : ℕ) : ℝ :=
  Matrix.trace ((routeKThreePrimeRelocationMatrix q edge) ^ m)

/-- The quadratic trace cumulant is blind to one-edge orientation. -/
theorem routeKThreePrimeTracePower_two_edgeFlip_eq
    (q edge : Fin 3 → ℝ) :
    routeKThreePrimeTracePower q edge 2 =
      routeKThreePrimeTracePower q (routeKThreePrimeEdgeFlip edge) 2 := by
  simp [routeKThreePrimeTracePower, routeKThreePrimeRelocationMatrix,
    routeKThreePrimeEdgeFlip, pow_two, Matrix.trace_fin_three]

/-- The cubic trace cumulant detects the triangle with exact edge-flip difference twelve times
the cycle product. -/
theorem routeKThreePrimeTracePower_three_sub_edgeFlip
    (q edge : Fin 3 → ℝ) :
    routeKThreePrimeTracePower q edge 3 -
        routeKThreePrimeTracePower q (routeKThreePrimeEdgeFlip edge) 3 =
      12 * edge 0 * edge 1 * edge 2 := by
  simp [routeKThreePrimeTracePower, routeKThreePrimeRelocationMatrix,
    routeKThreePrimeEdgeFlip, pow_succ, Matrix.trace_fin_three]
  ring

/-- The quartic trace cumulant couples triangle orientation to the diagonal background. -/
theorem routeKThreePrimeTracePower_four_sub_edgeFlip
    (q edge : Fin 3 → ℝ) :
    routeKThreePrimeTracePower q edge 4 -
        routeKThreePrimeTracePower q (routeKThreePrimeEdgeFlip edge) 4 =
      16 * (q 0 + q 1 + q 2) * edge 0 * edge 1 * edge 2 := by
  simp [routeKThreePrimeTracePower, routeKThreePrimeRelocationMatrix,
    routeKThreePrimeEdgeFlip, pow_succ, Matrix.trace_fin_three]
  ring

/-- Trace cumulant of the positive relocation sector paired with its negative. -/
def routeKThreePrimePairedTracePower
    (q edge : Fin 3 → ℝ) (m : ℕ) : ℝ :=
  routeKThreePrimeTracePower q edge m +
    routeKThreePrimeTracePower (fun i => -q i) (fun i => -edge i) m

/-- Reflection pairing cancels the cubic triangle cumulant exactly. -/
theorem routeKThreePrimePairedTracePower_three_eq_zero
    (q edge : Fin 3 → ℝ) :
    routeKThreePrimePairedTracePower q edge 3 = 0 := by
  simp [routeKThreePrimePairedTracePower, routeKThreePrimeTracePower,
    routeKThreePrimeRelocationMatrix, pow_succ, Matrix.trace_fin_three]
  ring

/-- Quartic is the first reflection-even trace cumulant that can see the triangle: its one-edge
flip difference is twice the unpaired quartic difference. -/
theorem routeKThreePrimePairedTracePower_four_sub_edgeFlip
    (q edge : Fin 3 → ℝ) :
    routeKThreePrimePairedTracePower q edge 4 -
        routeKThreePrimePairedTracePower q (routeKThreePrimeEdgeFlip edge) 4 =
      32 * (q 0 + q 1 + q 2) * edge 0 * edge 1 * edge 2 := by
  simp [routeKThreePrimePairedTracePower, routeKThreePrimeTracePower,
    routeKThreePrimeRelocationMatrix, routeKThreePrimeEdgeFlip,
    pow_succ, Matrix.trace_fin_three]
  ring

/-- Positive RVM diagonal and nonzero triangle force quartic paired-cumulant detection. -/
theorem routeKThreePrimePairedTracePower_four_ne_edgeFlip
    (q edge : Fin 3 → ℝ)
    (hq : ∀ i, 0 < q i) (hedge : ∀ i, edge i ≠ 0) :
    routeKThreePrimePairedTracePower q edge 4 ≠
      routeKThreePrimePairedTracePower q (routeKThreePrimeEdgeFlip edge) 4 := by
  intro heq
  have hzero :
      routeKThreePrimePairedTracePower q edge 4 -
          routeKThreePrimePairedTracePower q (routeKThreePrimeEdgeFlip edge) 4 = 0 :=
    sub_eq_zero.mpr heq
  rw [routeKThreePrimePairedTracePower_four_sub_edgeFlip] at hzero
  have hsum : q 0 + q 1 + q 2 ≠ 0 := by
    have : 0 < q 0 + q 1 + q 2 := by nlinarith [hq 0, hq 1, hq 2]
    exact ne_of_gt this
  have hnonzero :
      32 * (q 0 + q 1 + q 2) * edge 0 * edge 1 * edge 2 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) hsum) (hedge 0)) (hedge 1))
      (hedge 2)
  exact hnonzero hzero

end

end RHTower
