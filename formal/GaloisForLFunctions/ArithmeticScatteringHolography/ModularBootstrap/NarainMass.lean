import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ScalarChargeCoordinates

/-!
# Two-torus Narain masses and chiral positivity

The complex structure and complexified area determine a positive quadratic
mass on momentum and winding. Its two chiral components are sums of squares.
On scalar charges, primitive coordinates separate the two target moduli.
-/

open RHTower RHTower.HeckeFactorization

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

noncomputable section

/-- The integer left-right spin of a momentum-winding charge. -/
def chargeSpin (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ :=
  q.1.1 * q.2.1 + q.1.2 * q.2.2

/-- Real two-dimensional quadratic form for complex structure `σ`. -/
def targetQuadratic (σ : D4BMUpperHalfPlaneCoordinate) (v : ℝ × ℝ) : ℝ :=
  (σ.y * v.1) ^ 2 + (v.2 - σ.x * v.1) ^ 2

/-- The Narain squared mass; the conformal dimension is half this value. -/
def narainMassSq (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  (targetQuadratic σ ((q.1.1 : ℝ) + ρ.x * q.2.2, (q.1.2 : ℝ) - ρ.x * q.2.1) +
    ρ.y ^ 2 * targetQuadratic σ ((q.2.2 : ℝ), -(q.2.1 : ℝ))) / (ρ.y * σ.y)

theorem targetQuadratic_nonneg (σ : D4BMUpperHalfPlaneCoordinate) (v : ℝ × ℝ) :
    0 ≤ targetQuadratic σ v := add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The target quadratic form uses the Eisenstein convention after one sign change. -/
theorem targetQuadratic_poincare (σ : D4BMUpperHalfPlaneCoordinate) (p : ℤ × ℤ) :
    targetQuadratic σ ((p.1 : ℝ), (p.2 : ℝ)) =
      d4BMPoincareQuadratic σ (p.1, -p.2) := by
  dsimp only [targetQuadratic, d4BMPoincareQuadratic]
  push_cast
  ring

/-- The positive-spin chiral mass is explicitly a sum of two squares. -/
theorem narainMassSq_add_spin (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainMassSq ρ σ q + 2 * (chargeSpin q : ℝ) =
      ((σ.y * ((q.1.1 : ℝ) + ρ.x * q.2.2) -
          ρ.y * (-(q.2.1 : ℝ) - σ.x * q.2.2)) ^ 2 +
        ((q.1.2 : ℝ) - ρ.x * q.2.1 - σ.x * ((q.1.1 : ℝ) + ρ.x * q.2.2) +
          ρ.y * σ.y * q.2.2) ^ 2) / (ρ.y * σ.y) := by
  dsimp only [narainMassSq, targetQuadratic, chargeSpin]
  push_cast
  field_simp [ρ.y_pos.ne', σ.y_pos.ne']
  ring

/-- The negative-spin chiral mass is explicitly a sum of two squares. -/
theorem narainMassSq_sub_spin (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainMassSq ρ σ q - 2 * (chargeSpin q : ℝ) =
      ((σ.y * ((q.1.1 : ℝ) + ρ.x * q.2.2) +
          ρ.y * (-(q.2.1 : ℝ) - σ.x * q.2.2)) ^ 2 +
        ((q.1.2 : ℝ) - ρ.x * q.2.1 - σ.x * ((q.1.1 : ℝ) + ρ.x * q.2.2) -
          ρ.y * σ.y * q.2.2) ^ 2) / (ρ.y * σ.y) := by
  dsimp only [narainMassSq, targetQuadratic, chargeSpin]
  push_cast
  field_simp [ρ.y_pos.ne', σ.y_pos.ne']
  ring

/-- Both left and right conformal weights are nonnegative at every target modulus. -/
theorem narain_chiral_nonneg (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    0 ≤ narainMassSq ρ σ q + 2 * (chargeSpin q : ℝ) ∧
    0 ≤ narainMassSq ρ σ q - 2 * (chargeSpin q : ℝ) := by
  rw [narainMassSq_add_spin, narainMassSq_sub_spin]
  constructor <;> exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_pos ρ.y_pos σ.y_pos).le

/-- The conformal dimension is at least the absolute spin. -/
theorem two_mul_abs_spin_le_massSq (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    2 * |(chargeSpin q : ℝ)| ≤ narainMassSq ρ σ q := by
  obtain ⟨hp, hm⟩ := narain_chiral_nonneg ρ σ q
  have h : |2 * (chargeSpin q : ℝ)| ≤ narainMassSq ρ σ q :=
    abs_le.mpr ⟨by linarith only [hp], by linarith only [hm]⟩
  simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h

/-- Scalar masses factor into one quadratic expression for each target modulus. -/
theorem narainMassSq_scalarParameters (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (k : ℕ) (a : D4BMPrimitiveIntegerPair) (d : ℤ) :
    narainMassSq ρ σ (scalarParameters k a d) =
      targetQuadratic σ ((a.pair.1 : ℝ), (a.pair.2 : ℝ)) *
        d4BMPoincareQuadratic ρ ((k : ℤ) + 1, d) / (ρ.y * σ.y) := by
  dsimp only [narainMassSq, targetQuadratic, scalarParameters, d4BMPoincareQuadratic]
  push_cast
  congr 1
  ring

/-- The square target gives the integer sum of the four squared charges. -/
theorem narainMassSq_square (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainMassSq zI zI q =
      (q.1.1 : ℝ) ^ 2 + (q.1.2 : ℝ) ^ 2 + (q.2.1 : ℝ) ^ 2 + (q.2.2 : ℝ) ^ 2 := by
  dsimp only [narainMassSq, targetQuadratic, zI]
  ring

/-- An explicit inverse bound for the target quadratic form. -/
def targetCoercivityConstant (σ : D4BMUpperHalfPlaneCoordinate) : ℝ :=
  (2 * σ.y ^ 2 + 1 + 2 * σ.x ^ 2) / σ.y ^ 2

theorem targetCoercivityConstant_pos (σ : D4BMUpperHalfPlaneCoordinate) :
    0 < targetCoercivityConstant σ :=
  div_pos (by positivity) (sq_pos_of_pos σ.y_pos)

theorem targetQuadratic_coercive (σ : D4BMUpperHalfPlaneCoordinate) (v : ℝ × ℝ) :
    v.1 ^ 2 + v.2 ^ 2 ≤ targetCoercivityConstant σ * targetQuadratic σ v := by
  rw [targetCoercivityConstant, div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos σ.y_pos)).mpr
  apply sub_nonneg.mp
  calc
    (2 * σ.y ^ 2 + 1 + 2 * σ.x ^ 2) * targetQuadratic σ v -
        (v.1 ^ 2 + v.2 ^ 2) * σ.y ^ 2 =
      2 * (σ.y ^ 2 * v.1) ^ 2 + σ.y ^ 2 * (2 * σ.x * v.1 - v.2) ^ 2 +
        (1 + 2 * σ.x ^ 2) * (v.2 - σ.x * v.1) ^ 2 := by
          dsimp only [targetQuadratic]
          ring
    _ ≥ 0 := by positivity

/-- Euclidean size of an integer momentum-winding charge. -/
def chargeEuclideanSq (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  (q.1.1 : ℝ) ^ 2 + (q.1.2 : ℝ) ^ 2 + (q.2.1 : ℝ) ^ 2 + (q.2.2 : ℝ) ^ 2

/-- A uniform inverse mass bound at fixed target moduli. -/
def massCoercivityConstant (ρ σ : D4BMUpperHalfPlaneCoordinate) : ℝ :=
  ρ.y * σ.y * targetCoercivityConstant σ * (2 + (2 * ρ.x ^ 2 + 1) / ρ.y ^ 2)

theorem massCoercivityConstant_pos (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    0 < massCoercivityConstant ρ σ := by
  apply mul_pos (mul_pos (mul_pos ρ.y_pos σ.y_pos) (targetCoercivityConstant_pos σ))
  have h : 0 ≤ (2 * ρ.x ^ 2 + 1) / ρ.y ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  linarith only [h]

/-- The mass controls all four integer charges, uniformly at fixed moduli. -/
theorem chargeEuclideanSq_le_mass (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    chargeEuclideanSq q ≤ massCoercivityConstant ρ σ * narainMassSq ρ σ q := by
  let u : ℝ × ℝ :=
    ((q.1.1 : ℝ) + ρ.x * q.2.2, (q.1.2 : ℝ) - ρ.x * q.2.1)
  let w : ℝ × ℝ := ((q.2.2 : ℝ), -(q.2.1 : ℝ))
  have hu := targetQuadratic_coercive σ u
  have hw := targetQuadratic_coercive σ w
  have hU := targetQuadratic_nonneg σ u
  have hW := targetQuadratic_nonneg σ w
  have hD := (targetCoercivityConstant_pos σ).le
  have hB : 0 ≤ 2 * ρ.x ^ 2 + 1 := by positivity
  have hshift : chargeEuclideanSq q ≤
      2 * (u.1 ^ 2 + u.2 ^ 2) + (2 * ρ.x ^ 2 + 1) * (w.1 ^ 2 + w.2 ^ 2) := by
    apply sub_nonneg.mp
    calc
      2 * (u.1 ^ 2 + u.2 ^ 2) + (2 * ρ.x ^ 2 + 1) * (w.1 ^ 2 + w.2 ^ 2) -
          chargeEuclideanSq q =
        ((q.1.1 : ℝ) + 2 * ρ.x * q.2.2) ^ 2 +
          ((q.1.2 : ℝ) - 2 * ρ.x * q.2.1) ^ 2 := by
            dsimp only [u, w, chargeEuclideanSq]
            ring
      _ ≥ 0 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hscale : 2 * targetQuadratic σ u + (2 * ρ.x ^ 2 + 1) * targetQuadratic σ w ≤
      (2 + (2 * ρ.x ^ 2 + 1) / ρ.y ^ 2) *
        (targetQuadratic σ u + ρ.y ^ 2 * targetQuadratic σ w) := by
    apply sub_nonneg.mp
    calc
      (2 + (2 * ρ.x ^ 2 + 1) / ρ.y ^ 2) *
          (targetQuadratic σ u + ρ.y ^ 2 * targetQuadratic σ w) -
          (2 * targetQuadratic σ u + (2 * ρ.x ^ 2 + 1) * targetQuadratic σ w) =
        2 * ρ.y ^ 2 * targetQuadratic σ w +
          ((2 * ρ.x ^ 2 + 1) / ρ.y ^ 2) * targetQuadratic σ u := by
            field_simp [ρ.y_pos.ne']
            ring
      _ ≥ 0 := add_nonneg (mul_nonneg (by positivity) hW)
        (mul_nonneg (div_nonneg hB (sq_nonneg _)) hU)
  calc
    chargeEuclideanSq q ≤
        2 * (u.1 ^ 2 + u.2 ^ 2) + (2 * ρ.x ^ 2 + 1) * (w.1 ^ 2 + w.2 ^ 2) := hshift
    _ ≤ 2 * (targetCoercivityConstant σ * targetQuadratic σ u) +
        (2 * ρ.x ^ 2 + 1) * (targetCoercivityConstant σ * targetQuadratic σ w) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (by norm_num))
        (mul_le_mul_of_nonneg_left hw hB)
    _ = targetCoercivityConstant σ *
        (2 * targetQuadratic σ u + (2 * ρ.x ^ 2 + 1) * targetQuadratic σ w) := by ring
    _ ≤ targetCoercivityConstant σ * ((2 + (2 * ρ.x ^ 2 + 1) / ρ.y ^ 2) *
        (targetQuadratic σ u + ρ.y ^ 2 * targetQuadratic σ w)) :=
      mul_le_mul_of_nonneg_left hscale hD
    _ = massCoercivityConstant ρ σ * narainMassSq ρ σ q := by
      dsimp only [massCoercivityConstant, narainMassSq, u, w]
      field_simp [ρ.y_pos.ne', σ.y_pos.ne']

private theorem one_le_chargeEuclideanSq {q : (ℤ × ℤ) × (ℤ × ℤ)}
    (hq : q ≠ ((0, 0), (0, 0))) : 1 ≤ chargeEuclideanSq q := by
  by_cases hn : q.1 = (0, 0)
  · have hw : q.2 ≠ (0, 0) := fun hw => hq (Prod.ext hn hw)
    have hh := d4BM_one_le_sq_add_sq_of_int_pair_ne_zero q.2 hw
    simpa only [chargeEuclideanSq, hn, Int.cast_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add] using hh
  · have hh := d4BM_one_le_sq_add_sq_of_int_pair_ne_zero q.1 hn
    dsimp only [chargeEuclideanSq]
    linarith only [hh, sq_nonneg (q.2.1 : ℝ), sq_nonneg (q.2.2 : ℝ)]

/-- Nonvacuum masses have a positive uniform gap at fixed target moduli. -/
theorem narainMassSq_gap (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {q : (ℤ × ℤ) × (ℤ × ℤ)} (hq : q ≠ ((0, 0), (0, 0))) :
    1 / massCoercivityConstant ρ σ ≤ narainMassSq ρ σ q := by
  apply (div_le_iff₀ (massCoercivityConstant_pos ρ σ)).mpr
  simpa only [mul_comm] using (one_le_chargeEuclideanSq hq).trans
    (chargeEuclideanSq_le_mass ρ σ q)

/-- Every nonvacuum charge has strictly positive conformal dimension. -/
theorem narainMassSq_pos (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {q : (ℤ × ℤ) × (ℤ × ℤ)} (hq : q ≠ ((0, 0), (0, 0))) :
    0 < narainMassSq ρ σ q :=
  lt_of_lt_of_le (one_div_pos.mpr (massCoercivityConstant_pos ρ σ))
    (narainMassSq_gap ρ σ hq)

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMassSq_pos
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narain_chiral_nonneg
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMassSq_scalarParameters
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMassSq_gap
