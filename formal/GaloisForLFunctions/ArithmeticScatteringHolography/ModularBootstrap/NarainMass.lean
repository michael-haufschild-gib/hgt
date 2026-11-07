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

theorem targetQuadratic_eq_zero (σ : D4BMUpperHalfPlaneCoordinate) (v : ℝ × ℝ) :
    targetQuadratic σ v = 0 ↔ v = (0, 0) := by
  constructor
  · intro h
    change (σ.y * v.1) ^ 2 + (v.2 - σ.x * v.1) ^ 2 = 0 at h
    have h₁ : σ.y * v.1 = 0 :=
      pow_eq_zero (le_antisymm (by nlinarith only [h, sq_nonneg (v.2 - σ.x * v.1)])
        (sq_nonneg _))
    have hv : v.1 = 0 := (mul_eq_zero.mp h₁).resolve_left σ.y_pos.ne'
    have hv₂ : v.2 = 0 := by
      simp only [targetQuadratic, hv, mul_zero, zero_pow (by decide : 2 ≠ 0),
        sub_zero, zero_add] at h
      exact pow_eq_zero h
    exact Prod.ext hv hv₂
  · rintro rfl
    simp [targetQuadratic]

/-- The target quadratic form uses the Eisenstein convention after one sign change. -/
theorem targetQuadratic_poincare (σ : D4BMUpperHalfPlaneCoordinate) (p : ℤ × ℤ) :
    targetQuadratic σ ((p.1 : ℝ), (p.2 : ℝ)) =
      d4BMPoincareQuadratic σ (p.1, -p.2) := by
  dsimp only [targetQuadratic, d4BMPoincareQuadratic]
  push_cast
  ring

/-- Every nonvacuum charge has strictly positive conformal dimension. -/
theorem narainMassSq_pos (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {q : (ℤ × ℤ) × (ℤ × ℤ)} (hq : q ≠ ((0, 0), (0, 0))) :
    0 < narainMassSq ρ σ q := by
  apply div_pos _ (mul_pos ρ.y_pos σ.y_pos)
  have h₁ := targetQuadratic_nonneg σ
    ((q.1.1 : ℝ) + ρ.x * q.2.2, (q.1.2 : ℝ) - ρ.x * q.2.1)
  have h₂ := targetQuadratic_nonneg σ ((q.2.2 : ℝ), -(q.2.1 : ℝ))
  have hy : 0 < ρ.y ^ 2 := sq_pos_of_pos ρ.y_pos
  have hprod := mul_nonneg hy.le h₂
  by_contra h
  have hle := le_of_not_gt h
  have hprod_zero : ρ.y ^ 2 * targetQuadratic σ ((q.2.2 : ℝ), -(q.2.1 : ℝ)) = 0 :=
    le_antisymm (by linarith only [hle, h₁]) hprod
  have hw := (mul_eq_zero.mp hprod_zero).resolve_left hy.ne'
  have hw' := (targetQuadratic_eq_zero σ _).mp hw
  have hw₁ : q.2.1 = 0 := by exact_mod_cast neg_eq_zero.mp (congrArg Prod.snd hw')
  have hw₂ : q.2.2 = 0 := by exact_mod_cast congrArg Prod.fst hw'
  have hzero : targetQuadratic σ
      ((q.1.1 : ℝ) + ρ.x * q.2.2, (q.1.2 : ℝ) - ρ.x * q.2.1) = 0 := by
    linarith only [hle, h₁, hprod]
  have hn : targetQuadratic σ ((q.1.1 : ℝ), (q.1.2 : ℝ)) = 0 := by
    simpa only [hw₁, hw₂, Int.cast_zero, mul_zero, add_zero, sub_zero] using hzero
  have hn' := (targetQuadratic_eq_zero σ _).mp hn
  exact hq (Prod.ext
    (Prod.ext (by exact_mod_cast congrArg Prod.fst hn')
      (by exact_mod_cast congrArg Prod.snd hn')) (Prod.ext hw₁ hw₂))

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
  <;> ring

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
  <;> ring

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

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMassSq_pos
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narain_chiral_nonneg
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMassSq_scalarParameters
