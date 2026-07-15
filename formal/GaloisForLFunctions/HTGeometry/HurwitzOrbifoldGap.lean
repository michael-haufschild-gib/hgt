import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge

/-!
# The sharp Hurwitz gap for hyperbolic triangle orbifolds

For ordered integral cone orders `2 ≤ a ≤ b ≤ c`, positive hyperbolic excess cannot be
arbitrarily small.  The first possible value is `1/42`, attained by `(2,3,7)`.

This file proves the gap directly by the finite symbolic case split behind the classical Hurwitz
bound.  It closes the discrete geometric input used by the projective topological-capacity law:
the interval `(0,1/42)` contains no integral triangle-orbifold curvature.  No numerical search or
dynamical flow is involved.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Normalized positive curvature excess of an ordered three-cone sphere orbifold.  Hyperbolicity
is the condition that this rational number is positive. -/
def triangleOrbifoldExcess (a b c : ℕ) : ℚ :=
  1 - ((a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹)

/-- Reciprocal antitonicity specialized to positive natural cone orders cast to `ℚ`. -/
lemma natCast_inv_le_natCast_inv (n x : ℕ) (hn : 0 < n) (h : n ≤ x) :
    ((x : ℚ)⁻¹) ≤ ((n : ℚ)⁻¹) := by
  apply inv_anti₀
  · exact_mod_cast hn
  · exact_mod_cast h

/-- The sharp discrete Hurwitz gap.  Every ordered integral hyperbolic triangle signature has
orbifold excess at least `1/42`. -/
theorem hyperbolicTriangle_excess_ge_one_over_fortyTwo
    (a b c : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hhyperbolic : 0 < triangleOrbifoldExcess a b c) :
    (1 : ℚ) / 42 ≤ triangleOrbifoldExcess a b c := by
  have conclude (A B C : ℚ)
      (haInv : ((a : ℚ)⁻¹) ≤ A)
      (hbInv : ((b : ℚ)⁻¹) ≤ B)
      (hcInv : ((c : ℚ)⁻¹) ≤ C)
      (hgap : (1 : ℚ) / 42 ≤ 1 - (A + B + C)) :
      (1 : ℚ) / 42 ≤ triangleOrbifoldExcess a b c := by
    dsimp [triangleOrbifoldExcess]
    linarith
  by_cases ha2 : a = 2
  · subst a
    have hb3 : 3 ≤ b := by
      by_contra h
      have hb2 : b = 2 := by omega
      subst b
      have hc0 : (0 : ℚ) ≤ ((c : ℚ)⁻¹) := by positivity
      dsimp [triangleOrbifoldExcess] at hhyperbolic
      norm_num at hhyperbolic
      linarith
    by_cases hb3eq : b = 3
    · subst b
      have hc7 : 7 ≤ c := by
        by_contra h
        have hc6 : c ≤ 6 := by omega
        have hc3 : 3 ≤ c := hbc
        interval_cases c <;> norm_num [triangleOrbifoldExcess] at hhyperbolic
      apply conclude ((1 : ℚ) / 2) ((1 : ℚ) / 3) ((1 : ℚ) / 7)
      · norm_num
      · norm_num
      · simpa [one_div] using natCast_inv_le_natCast_inv 7 c (by omega) hc7
      · norm_num
    · have hb4 : 4 ≤ b := by omega
      by_cases hb4eq : b = 4
      · subst b
        have hc5 : 5 ≤ c := by
          by_contra h
          have hc4 : c = 4 := by omega
          subst c
          norm_num [triangleOrbifoldExcess] at hhyperbolic
        apply conclude ((1 : ℚ) / 2) ((1 : ℚ) / 4) ((1 : ℚ) / 5)
        · norm_num
        · norm_num
        · simpa [one_div] using natCast_inv_le_natCast_inv 5 c (by omega) hc5
        · norm_num
      · have hb5 : 5 ≤ b := by omega
        have hc5 : 5 ≤ c := hb5.trans hbc
        apply conclude ((1 : ℚ) / 2) ((1 : ℚ) / 5) ((1 : ℚ) / 5)
        · norm_num
        · simpa [one_div] using natCast_inv_le_natCast_inv 5 b (by omega) hb5
        · simpa [one_div] using natCast_inv_le_natCast_inv 5 c (by omega) hc5
        · norm_num
  · by_cases ha3 : a = 3
    · subst a
      by_cases hb3 : b = 3
      · subst b
        have hc4 : 4 ≤ c := by
          by_contra h
          have hc3 : c = 3 := by omega
          subst c
          norm_num [triangleOrbifoldExcess] at hhyperbolic
        apply conclude ((1 : ℚ) / 3) ((1 : ℚ) / 3) ((1 : ℚ) / 4)
        · norm_num
        · norm_num
        · simpa [one_div] using natCast_inv_le_natCast_inv 4 c (by omega) hc4
        · norm_num
      · have hb4 : 4 ≤ b := by omega
        have hc4 : 4 ≤ c := hb4.trans hbc
        apply conclude ((1 : ℚ) / 3) ((1 : ℚ) / 4) ((1 : ℚ) / 4)
        · norm_num
        · simpa [one_div] using natCast_inv_le_natCast_inv 4 b (by omega) hb4
        · simpa [one_div] using natCast_inv_le_natCast_inv 4 c (by omega) hc4
        · norm_num
    · have ha4 : 4 ≤ a := by omega
      have hb4 : 4 ≤ b := ha4.trans hab
      have hc4 : 4 ≤ c := hb4.trans hbc
      apply conclude ((1 : ℚ) / 4) ((1 : ℚ) / 4) ((1 : ℚ) / 4)
      · simpa [one_div] using natCast_inv_le_natCast_inv 4 a (by omega) ha4
      · simpa [one_div] using natCast_inv_le_natCast_inv 4 b (by omega) hb4
      · simpa [one_div] using natCast_inv_le_natCast_inv 4 c (by omega) hc4
      · norm_num

/-- There is no intermediate integral triangle-orbifold phase strictly between parabolicity and
the Hurwitz quantum `1/42`. -/
theorem hyperbolicTriangle_no_excess_below_one_over_fortyTwo
    (a b c : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hhyperbolic : 0 < triangleOrbifoldExcess a b c) :
    ¬triangleOrbifoldExcess a b c < (1 : ℚ) / 42 := by
  exact not_lt_of_ge
    (hyperbolicTriangle_excess_ge_one_over_fortyTwo a b c ha hab hbc hhyperbolic)

/-- The `(2,3,7)` signature attains the first positive triangle-orbifold excess exactly. -/
@[simp]
theorem triangleOrbifoldExcess_two_three_seven :
    triangleOrbifoldExcess 2 3 7 = (1 : ℚ) / 42 := by
  norm_num [triangleOrbifoldExcess]

end GaloisForLFunctions.HTGeometry
