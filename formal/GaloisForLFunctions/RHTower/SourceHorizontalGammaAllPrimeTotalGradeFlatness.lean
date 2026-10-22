import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedExteriorSource

/-!
# All-prime fixed-total-grade flatness of the literal Gamma exterior

The existing `(2,3)` equal-depth full-grade law is not special to those primes or to equal
depths.  The sum of the two source modular rates is strictly negative at every ordered pair of
prime-power cells.  Assigning local grade `g / (-(rate i + rate j))` makes the *total* modular
exponent equal to `-g`.  Consequently every literal cross-prime exterior coefficient is the
critical coefficient multiplied by the same positive scalar `exp (-g)`.

Every fixed-coefficient finite linear observation therefore has exactly the same vanishing
locus at every total grade.  This rules out grade selection by this projective/linear exterior
alone.  It does not rule out a fixed-source-frame comparison, a grade-dependent arithmetic
coefficient, or a nonlinear/singular observation.  No Xi zero or RH premise enters.
-/

namespace RHTower

noncomputable section

/-- Positive magnitude of the pair's source modular rate. -/
def primitivePairTotalModularRate (i j : Nat.Primes × ℕ) : ℝ :=
  -(xiGammaEulerPrimitiveModularRate i + xiGammaEulerPrimitiveModularRate j)

private theorem primitivePairTotalModularRate_pos (i j : Nat.Primes × ℕ) :
    0 < primitivePairTotalModularRate i j := by
  have hi : 0 < Real.log (i.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast i.1.property.one_lt)
  have hj : 0 < Real.log (j.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast j.1.property.one_lt)
  have hHi : 0 < xiGammaEulerBoundaryHalfHeight i.1 i.2 := by
    unfold xiGammaEulerBoundaryHalfHeight
    positivity
  have hHj : 0 < xiGammaEulerBoundaryHalfHeight j.1 j.2 := by
    unfold xiGammaEulerBoundaryHalfHeight
    positivity
  rw [primitivePairTotalModularRate,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  nlinarith

/-- Local grade forced by the same total modular exponent on every pair. -/
def primitivePairFixedTotalGrade (g : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  g / primitivePairTotalModularRate i j

/-- All ordered prime-power pairs lie on one common scalar grade orbit. -/
theorem primitivePairFixedTotalGrade_exterior_flat
    (g : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularExterior
        (primitivePairFixedTotalGrade g i j) i j =
      Real.exp (-g) * xiGammaEulerPrimitiveModularExterior 0 i j := by
  rw [xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq]
  have hR : primitivePairTotalModularRate i j ≠ 0 :=
    (primitivePairTotalModularRate_pos i j).ne'
  have hrate :
      primitivePairFixedTotalGrade g i j *
          (xiGammaEulerPrimitiveModularRate i +
            xiGammaEulerPrimitiveModularRate j) = -g := by
    have hS : xiGammaEulerPrimitiveModularRate i +
        xiGammaEulerPrimitiveModularRate j ≠ 0 := by
      intro h
      apply hR
      simp [primitivePairTotalModularRate, h]
    unfold primitivePairFixedTotalGrade primitivePairTotalModularRate
    field_simp [hS]
  rw [hrate]
  simp only [zero_mul, Real.exp_zero]
  ring

/-- A single exterior coefficient has grade-independent zero status. -/
theorem primitivePairFixedTotalGrade_exterior_zero_iff
    (g : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularExterior
        (primitivePairFixedTotalGrade g i j) i j = 0 ↔
      xiGammaEulerPrimitiveModularExterior 0 i j = 0 := by
  rw [primitivePairFixedTotalGrade_exterior_flat]
  simp

/-- The same scalar factors out of every fixed-coefficient finite packet. -/
theorem primitivePairFixedTotalGrade_finite_linear_flat
    (g : ℝ)
    (S : Finset ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)))
    (c : ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) → ℝ) :
    (∑ x ∈ S, c x *
      xiGammaEulerPrimitiveModularExterior
        (primitivePairFixedTotalGrade g x.1 x.2) x.1 x.2) =
      Real.exp (-g) *
        (∑ x ∈ S, c x * xiGammaEulerPrimitiveModularExterior 0 x.1 x.2) := by
  simp_rw [primitivePairFixedTotalGrade_exterior_flat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Such a finite observation cannot acquire a new zero at a nonneutral grade. -/
theorem primitivePairFixedTotalGrade_finite_linear_zero_iff
    (g : ℝ)
    (S : Finset ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)))
    (c : ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) → ℝ) :
    (∑ x ∈ S, c x *
      xiGammaEulerPrimitiveModularExterior
        (primitivePairFixedTotalGrade g x.1 x.2) x.1 x.2) = 0 ↔
      (∑ x ∈ S, c x *
        xiGammaEulerPrimitiveModularExterior 0 x.1 x.2) = 0 := by
  rw [primitivePairFixedTotalGrade_finite_linear_flat]
  simp

end

end RHTower
