import GaloisForLFunctions.OrderSixMetaplecticTheory.TheRatioTracesReadTheRelationOfTheOppositePairs

/-!
# The quadratic grade vanishes when −1 is not a square

The theta coefficients are even, `T(−h) = T(h)`, and the cubic character is even, `χ(−1) = 1`. So a twist of `θ²` by
an odd character of `O/q` is an odd Dirichlet series in `h` and vanishes identically
(`besselDirichlet_eq_zero_of_odd`). The quadratic character `λ` of `O/q` is odd exactly when
`N(q) ≡ 3 mod 4`. Then the quadratic twist `L_λ` and the conjugate sextic twist `L_{χ̄λ}` are
identically zero (`quadraticGrade_vanish`): at these prime columns the sextic main term is absent, unconditionally.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

/-- **Odd coefficients give the zero series.** -/
theorem besselDirichlet_eq_zero_of_odd (Q : O → ℂ) (hQ : ∀ h, Q (-h) = -Q h) (s : ℂ) :
    besselDirichlet Q s = 0 := by
  set F : O → ℂ := fun h => if h = 0 then 0 else Q h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) with hF
  have hodd : ∀ h, F (-h) = -F h := by
    intro h
    simp only [hF, neg_eq_zero, cuspFrequency_neg, norm_neg]
    split_ifs
    · simp
    · rw [hQ, neg_mul]
  have h2 : ∑' h, F h = -∑' h, F h := by
    rw [← tsum_neg, ← (Equiv.neg O).tsum_eq F]
    exact tsum_congr fun h => by simp only [Equiv.neg_apply, hodd]
  have h0 : ∑' h, F h = 0 := by linear_combination h2 / 2
  exact h0

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem quadTwistCoeff_neg (h : O) : P.quadTwistCoeff (-h) = -(-P.lam (-1)) * P.quadTwistCoeff h := by
  rw [quadTwistCoeff, quadTwistCoeff, rationalSourceResidualFourierCoefficient_neg, map_neg,
    show -P.res h = -1 * P.res h by ring, map_mul]
  ring

theorem sexticTwistCoeff_neg (h : O) : P.sexticTwistCoeff (-h) = -(-P.lam (-1)) * P.sexticTwistCoeff h := by
  have hc : (P.chi ^ 2) (-1) = 1 := by rw [MulChar.pow_apply' _ (by norm_num), P.chi_neg_one, one_pow]
  rw [sexticTwistCoeff, sexticTwistCoeff, rationalSourceResidualFourierCoefficient_neg, map_neg,
    show -P.res h = -1 * P.res h by ring, map_mul, map_mul, hc]
  ring

/-- **The quadratic grade vanishes for odd `λ`.** If `λ(−1) = −1`, `L_λ ≡ 0` and `L_{χ̄λ} ≡ 0`. -/
theorem quadraticGrade_vanish (hodd : P.lam (-1) = -1) (s : ℂ) :
    besselDirichlet P.quadTwistCoeff s = 0 ∧ besselDirichlet P.sexticTwistCoeff s = 0 :=
  ⟨besselDirichlet_eq_zero_of_odd _ (fun h => by rw [P.quadTwistCoeff_neg, hodd]; ring) s,
    besselDirichlet_eq_zero_of_odd _ (fun h => by rw [P.sexticTwistCoeff_neg, hodd]; ring) s⟩

/-- `λ(−1) = −1` when `N(q) ≡ 3 mod 4`. -/
theorem lam_neg_one_of_card (h2 : (2 : P.Res) ≠ 0) (hN : Fintype.card P.Res % 4 = 3) : P.lam (-1) = -1 := by
  simp only [lam, MulChar.ringHomComp_apply]
  rw [quadraticChar_neg_one (P.ringChar_ne_two h2), ZMod.χ₄_nat_three_mod_four hN]
  simp

/-- **At prime columns with `N(q) ≡ 3 mod 4` the quadratic and the conjugate sextic twists vanish.** -/
theorem quadraticGrade_vanish_of_card (h2 : (2 : P.Res) ≠ 0) (hN : Fintype.card P.Res % 4 = 3) (s : ℂ) :
    besselDirichlet P.quadTwistCoeff s = 0 ∧ besselDirichlet P.sexticTwistCoeff s = 0 :=
  P.quadraticGrade_vanish (P.lam_neg_one_of_card h2 hN) s

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
