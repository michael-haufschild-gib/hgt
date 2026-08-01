import GaloisForLFunctions.HTGeometry.ThreeControlHermitianCycleObserverTimeSharpness

/-!
# Prime-marked cycle law for Route K

A trace-class correction of a diagonal Riemann--von Mangoldt skeleton cannot retain arithmetic
orientation through diagonal coefficients or isolated off-diagonal edges alone.  On a three-label
packet the first switching-invariant orientation is the closed-cycle product.  This file computes
that term exactly and proves that pairing a sector with its negative, as required by the evenness
of centered Xi, does not erase the cycle when the background reciprocal skeleton is positive.

The result is unconditional finite-packet infrastructure.  It neither constructs the conjectural
all-prime trace-class correction nor assumes any Xi zero lies on the critical line.
-/

open scoped Matrix

namespace RHTower

noncomputable section

/-- Three marked reciprocal-skeleton values with real symmetric edge corrections.  Edge `0`
joins vertices `0,1`, edge `1` joins `1,2`, and edge `2` joins `2,0`. -/
def routeKThreePrimeRelocationMatrix
    (q edge : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q 0, edge 0, edge 2;
     edge 0, q 1, edge 1;
     edge 2, edge 1, q 2]

/-- Characteristic determinant `det(wI-A)` of the three-label relocation packet. -/
def routeKThreePrimeCharacteristic
    (q edge : Fin 3 → ℝ) (w : ℝ) : ℝ :=
  (!![w - q 0, -edge 0, -edge 2;
      -edge 0, w - q 1, -edge 1;
      -edge 2, -edge 1, w - q 2] : Matrix (Fin 3) (Fin 3) ℝ).det

/-- Flip one edge while retaining every diagonal value and edge magnitude. -/
def routeKThreePrimeEdgeFlip (edge : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-edge 0, edge 1, edge 2]

/-- Product of the characteristic functions at `w` and `-w`.  Up to the harmless odd-dimensional
sign, this is the characteristic determinant of the sector paired with its negative. -/
def routeKThreePrimePairedCharacteristic
    (q edge : Fin 3 → ℝ) (w : ℝ) : ℝ :=
  routeKThreePrimeCharacteristic q edge w *
    routeKThreePrimeCharacteristic q edge (-w)

/-- The finite relocation packet is symmetric, so it is a legitimate real self-adjoint shadow. -/
theorem routeKThreePrimeRelocationMatrix_transpose
    (q edge : Fin 3 → ℝ) :
    (routeKThreePrimeRelocationMatrix q edge)ᵀ =
      routeKThreePrimeRelocationMatrix q edge := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [routeKThreePrimeRelocationMatrix]

/-- Exact three-label characteristic law.  Every proper-edge contribution is a square; the only
term sensitive to one edge sign is the closed-cycle holonomy. -/
theorem routeKThreePrimeCharacteristic_eq
    (q edge : Fin 3 → ℝ) (w : ℝ) :
    routeKThreePrimeCharacteristic q edge w =
      (w - q 0) * ((w - q 1) * (w - q 2) - (edge 1) ^ 2) -
      (edge 0) ^ 2 * (w - q 2) -
      (edge 2) ^ 2 * (w - q 1) -
      2 * edge 0 * edge 1 * edge 2 := by
  simp [routeKThreePrimeCharacteristic, Matrix.det_fin_three]
  ring

/-- A one-edge sign flip changes the unpaired characteristic function by exactly four times the
cycle product.  No diagonal or forest term contributes. -/
theorem routeKThreePrimeCharacteristic_sub_edgeFlip
    (q edge : Fin 3 → ℝ) (w : ℝ) :
    routeKThreePrimeCharacteristic q edge w -
        routeKThreePrimeCharacteristic q
          (routeKThreePrimeEdgeFlip edge) w =
      -4 * edge 0 * edge 1 * edge 2 := by
  simp [routeKThreePrimeCharacteristic, routeKThreePrimeEdgeFlip,
    Matrix.det_fin_three]
  ring

/-- Exact even-paired cycle law.  Centered-Xi reflection pairing preserves the triangle
orientation through its interaction with the nonzero diagonal skeleton. -/
theorem routeKThreePrimePairedCharacteristic_sub_edgeFlip
    (q edge : Fin 3 → ℝ) (w : ℝ) :
    routeKThreePrimePairedCharacteristic q edge w -
        routeKThreePrimePairedCharacteristic q
          (routeKThreePrimeEdgeFlip edge) w =
      -8 * (edge 0 * edge 1 * edge 2) *
        (-(q 0 + q 1 + q 2) * w ^ 2 - q 0 * q 1 * q 2 +
          q 0 * (edge 1) ^ 2 + q 1 * (edge 2) ^ 2 +
          q 2 * (edge 0) ^ 2) := by
  simp [routeKThreePrimePairedCharacteristic,
    routeKThreePrimeCharacteristic, routeKThreePrimeEdgeFlip,
    Matrix.det_fin_three]
  ring

/-- Forest boundary: if the closed-cycle product vanishes, flipping one edge is invisible to the
characteristic determinant. -/
theorem routeKThreePrimeCharacteristic_edgeFlip_eq_of_cycle_eq_zero
    (q edge : Fin 3 → ℝ)
    (hcycle : edge 0 * edge 1 * edge 2 = 0) (w : ℝ) :
    routeKThreePrimeCharacteristic q edge w =
      routeKThreePrimeCharacteristic q (routeKThreePrimeEdgeFlip edge) w := by
  rw [← sub_eq_zero, routeKThreePrimeCharacteristic_sub_edgeFlip]
  calc
    -4 * edge 0 * edge 1 * edge 2 =
        -4 * (edge 0 * edge 1 * edge 2) := by ring
    _ = 0 := by rw [hcycle, mul_zero]

/-- The same forest blindness persists after reflection pairing. -/
theorem routeKThreePrimePairedCharacteristic_edgeFlip_eq_of_cycle_eq_zero
    (q edge : Fin 3 → ℝ)
    (hcycle : edge 0 * edge 1 * edge 2 = 0) (w : ℝ) :
    routeKThreePrimePairedCharacteristic q edge w =
      routeKThreePrimePairedCharacteristic q
        (routeKThreePrimeEdgeFlip edge) w := by
  rw [← sub_eq_zero,
    routeKThreePrimePairedCharacteristic_sub_edgeFlip, hcycle]
  ring

/-- Positive reciprocal RVM background makes every nonzero triangle detectable by the even paired
determinant at `w=0` or `w=1`.  Thus Xi evenness cannot justify discarding cycle holonomy. -/
theorem exists_routeKThreePrimePairedCharacteristic_ne_edgeFlip
    (q edge : Fin 3 → ℝ)
    (hq : ∀ i, 0 < q i) (hedge : ∀ i, edge i ≠ 0) :
    ∃ w : ℝ,
      routeKThreePrimePairedCharacteristic q edge w ≠
        routeKThreePrimePairedCharacteristic q
          (routeKThreePrimeEdgeFlip edge) w := by
  let c : ℝ := -q 0 * q 1 * q 2 +
    q 0 * (edge 1) ^ 2 + q 1 * (edge 2) ^ 2 + q 2 * (edge 0) ^ 2
  have hsum : q 0 + q 1 + q 2 ≠ 0 := by
    have hpos : 0 < q 0 + q 1 + q 2 := by
      nlinarith [hq 0, hq 1, hq 2]
    exact ne_of_gt hpos
  have hcycle : edge 0 * edge 1 * edge 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hedge 0) (hedge 1)) (hedge 2)
  by_cases hc : c = 0
  · refine ⟨1, ?_⟩
    intro heq
    have hd : routeKThreePrimePairedCharacteristic q edge 1 -
        routeKThreePrimePairedCharacteristic q
          (routeKThreePrimeEdgeFlip edge) 1 = 0 := sub_eq_zero.mpr heq
    have hdiff : routeKThreePrimePairedCharacteristic q edge 1 -
        routeKThreePrimePairedCharacteristic q
          (routeKThreePrimeEdgeFlip edge) 1 =
        -8 * (edge 0 * edge 1 * edge 2) *
          (-(q 0 + q 1 + q 2)) := by
      rw [routeKThreePrimePairedCharacteristic_sub_edgeFlip]
      change -q 0 * q 1 * q 2 +
        q 0 * (edge 1) ^ 2 + q 1 * (edge 2) ^ 2 +
          q 2 * (edge 0) ^ 2 = 0 at hc
      calc
        -8 * (edge 0 * edge 1 * edge 2) *
            (-(q 0 + q 1 + q 2) * 1 ^ 2 - q 0 * q 1 * q 2 +
              q 0 * edge 1 ^ 2 + q 1 * edge 2 ^ 2 +
              q 2 * edge 0 ^ 2) =
            -8 * (edge 0 * edge 1 * edge 2) *
              (-(q 0 + q 1 + q 2) +
                (-q 0 * q 1 * q 2 + q 0 * edge 1 ^ 2 +
                  q 1 * edge 2 ^ 2 + q 2 * edge 0 ^ 2)) := by ring
        _ = -8 * (edge 0 * edge 1 * edge 2) *
              (-(q 0 + q 1 + q 2)) := by rw [hc]; ring
    rw [hdiff] at hd
    have hneg : -(q 0 + q 1 + q 2) = 0 :=
      (mul_eq_zero.mp hd).resolve_left
        (mul_ne_zero (by norm_num) hcycle)
    exact hsum (neg_eq_zero.mp hneg)
  · refine ⟨0, ?_⟩
    intro heq
    have hd : routeKThreePrimePairedCharacteristic q edge 0 -
        routeKThreePrimePairedCharacteristic q
          (routeKThreePrimeEdgeFlip edge) 0 = 0 := sub_eq_zero.mpr heq
    have hdiff : routeKThreePrimePairedCharacteristic q edge 0 -
        routeKThreePrimePairedCharacteristic q
          (routeKThreePrimeEdgeFlip edge) 0 =
        -8 * (edge 0 * edge 1 * edge 2) * c := by
      rw [routeKThreePrimePairedCharacteristic_sub_edgeFlip]
      dsimp [c]
      ring
    rw [hdiff] at hd
    exact hc ((mul_eq_zero.mp hd).resolve_left
      (mul_ne_zero (by norm_num) hcycle))

end

end RHTower
