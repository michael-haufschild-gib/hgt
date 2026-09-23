import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedCutoffPolynomial
/-! # The actual theta cutoff coefficient cone

The positive rank-six source fixes five positive Jacobi coefficients. They give
an exact alternating coefficient formula for its monic degree-six minimizer,
a positive imaginary-axis readout, and an exact formula for the remaining
signed norm. Positivity of that norm is not assumed or concluded.
-/

open Polynomial HTGeometry
noncomputable section
namespace ThetaCuspCutoffJacobiAlgebra
private theorem functional_neg (s : ℕ → ℝ) (p : ℝ[X]) :
    momentFunctional s (-p) = -momentFunctional s p := by
  simpa using momentFunctional_smul s (-1) p

private theorem functional_reflect {s : ℕ → ℝ} (hs : ∀ n, Odd n → s n = 0)
    (p : ℝ[X]) : momentFunctional s (p.comp (-X)) = momentFunctional s p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, momentFunctional_add, hp, hq]
  | monomial n a =>
    rcases Nat.even_or_odd n with hn | hn
    · rw [monomial_comp, hn.neg_pow, C_mul_X_pow_eq_monomial]
    · have hz : momentFunctional s (C a * X^n) = 0 := by
        rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul,
          momentFunctional_X_pow, hs n hn, mul_zero]
      rw [monomial_comp, hn.neg_pow, mul_neg, functional_neg, hz,
        ← C_mul_X_pow_eq_monomial, hz]
      simp

private theorem alpha_of_reflect {s : ℕ → ℝ} (hs : ∀ n, Odd n → s n = 0)
    (n : ℕ) (hp : (monicOrtho s n).comp (-X) = monicOrtho s n ∨
      (monicOrtho s n).comp (-X) = -monicOrtho s n) :
    monicOrthoAlpha s n = 0 := by
  have hh := functional_reflect hs (X * monicOrtho s n * monicOrtho s n)
  rcases hp with hp | hp
  all_goals
    simp only [mul_comp, X_comp, hp] at hh
    simp only [neg_mul, mul_neg, neg_neg] at hh
    rw [functional_neg] at hh
    unfold monicOrthoAlpha momentInner
    have hz : momentFunctional s (X * monicOrtho s n * monicOrtho s n) = 0 := by linarith
    rw [hz, zero_div]

private theorem step {s : ℕ → ℝ} (hs : PositiveMomentFormBelow s 6)
    (ho : ∀ n, Odd n → s n = 0) (n : ℕ) (hn : n+1 ≤ 6)
    (hp : (monicOrtho s n).comp (-X) = monicOrtho s n ∨
      (monicOrtho s n).comp (-X) = -monicOrtho s n) :
    monicOrtho s (n+1) = X * monicOrtho s n -
      C (monicOrthoBeta s n) * monicOrtho s (n-1) := by
  have h := X_mul_monicOrtho_below hs hn
  rw [alpha_of_reflect ho n hp, zero_smul, add_zero,
    Polynomial.smul_eq_C_mul] at h
  exact eq_sub_of_add_eq h.symm

private theorem shape {s : ℕ → ℝ} (hs : PositiveMomentFormBelow s 6)
    (ho : ∀ n, Odd n → s n = 0) :
    monicOrtho s 6 = X^(6 : ℕ) -
      C (monicOrthoBeta s 1 + monicOrthoBeta s 2 + monicOrthoBeta s 3 +
        monicOrthoBeta s 4 + monicOrthoBeta s 5) * X^(4 : ℕ) +
      C (monicOrthoBeta s 1 * monicOrthoBeta s 3 +
        monicOrthoBeta s 1 * monicOrthoBeta s 4 +
        monicOrthoBeta s 2 * monicOrthoBeta s 4 +
        monicOrthoBeta s 1 * monicOrthoBeta s 5 +
        monicOrthoBeta s 2 * monicOrthoBeta s 5 +
        monicOrthoBeta s 3 * monicOrthoBeta s 5) * X^(2 : ℕ) -
      C (monicOrthoBeta s 1 * monicOrthoBeta s 3 * monicOrthoBeta s 5) := by
  let b := monicOrthoBeta s
  have p1 : monicOrtho s 1 = X := by
    have h := step hs ho 0 (by omega) (Or.inl (by simp))
    simpa [monicOrthoBeta] using h
  have p2 : monicOrtho s 2 = X^(2 : ℕ) - C (b 1) := by
    rw [step hs ho 1 (by omega) (Or.inr (by simp [p1])), p1, monicOrtho_zero]
    dsimp [b]; ring
  have p3 : monicOrtho s 3 = X^(3 : ℕ) - C (b 1+b 2)*X := by
    rw [step hs ho 2 (by omega) (Or.inl (by simp [p2])), p2, p1]
    simp only [b, map_add]; ring
  have p4 : monicOrtho s 4 = X^(4 : ℕ) - C (b 1+b 2+b 3)*X^(2 : ℕ)+C (b 1*b 3) := by
    rw [step hs ho 3 (by omega) (Or.inr (by simp [p3]; ring)), p3, p2]
    simp only [b, map_add, map_mul]; ring
  have p5 : monicOrtho s 5 = X^(5 : ℕ)-C (b 1+b 2+b 3+b 4)*X^(3 : ℕ)+
      C (b 1*b 3+b 1*b 4+b 2*b 4)*X := by
    rw [step hs ho 4 (by omega) (Or.inl (by simp [p4]; ring)), p4, p3]
    simp only [b, map_add, map_mul]; ring
  rw [step hs ho 5 (by omega) (Or.inr (by simp [p5]; ring)), p5, p4]
  simp only [b, map_add, map_mul]; ring
private theorem functional_C_mul_X_pow (s : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    momentFunctional s (C c * X^k) = c*s k := by
  rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul, momentFunctional_X_pow]

private theorem shape_square (s : ℕ → ℝ) (S E F : ℝ) :
    momentInner s (X^(6 : ℕ)-C S*X^(4 : ℕ)+C E*X^(2 : ℕ)-C F)
      (X^(6 : ℕ)-C S*X^(4 : ℕ)+C E*X^(2 : ℕ)-C F) =
      s 12-2*S*s 10+(S^(2 : ℕ)+2*E)*s 8-2*(S*E+F)*s 6+
        (E^(2 : ℕ)+2*S*F)*s 4-2*E*F*s 2+F^(2 : ℕ)*s 0 := by
  unfold momentInner
  have hp : (X^(6 : ℕ)-C S*X^(4 : ℕ)+C E*X^(2 : ℕ)-C F)*(X^(6 : ℕ)-C S*X^(4 : ℕ)+C E*X^(2 : ℕ)-C F) =
      C 1*X^(12 : ℕ) + C (-2*S)*X^(10 : ℕ)+C (S^(2 : ℕ)+2*E)*X^(8 : ℕ)+
        C (-2*(S*E+F))*X^(6 : ℕ)+C (E^(2 : ℕ)+2*S*F)*X^(4 : ℕ)+
        C (-2*E*F)*X^(2 : ℕ)+C (F^(2 : ℕ))*X^(0 : ℕ) := by
    simp only [map_one, map_add, map_mul, map_neg, map_pow, map_ofNat]
    ring
  rw [hp]
  simp only [momentFunctional_add, functional_C_mul_X_pow]
  ring

end ThetaCuspCutoffJacobiAlgebra

namespace RHTower

/-- Sum of the five positive Jacobi coefficients below the theta cutoff. -/
def thetaCuspCutoffJacobiSum (a : ℝ) : ℝ :=
  let b := monicOrthoBeta (thetaCuspCenterMixedSignedJet a)
  b 1+b 2+b 3+b 4+b 5

/-- The six separated Jacobi products in the quadratic cutoff coefficient. -/
def thetaCuspCutoffJacobiPairs (a : ℝ) : ℝ :=
  let b := monicOrthoBeta (thetaCuspCenterMixedSignedJet a)
  b 1*b 3+b 1*b 4+b 2*b 4+b 1*b 5+b 2*b 5+b 3*b 5

/-- The strictly positive constant magnitude of the actual theta cutoff. -/
def thetaCuspCutoffJacobiProduct (a : ℝ) : ℝ :=
  let b := monicOrthoBeta (thetaCuspCenterMixedSignedJet a)
  b 1*b 3*b 5

private theorem cutoff_positive_below {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
    PositiveMomentFormBelow (thetaCuspCenterMixedSignedJet a) 6 :=
  positiveMomentFormBelow_of_hankelPosDef (thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha)

/-- The actual cutoff has alternating even coefficients fixed by the lower Jacobi data. -/
theorem thetaCuspCenterMixedCutoffPolynomial_eq_jacobi
    {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
    thetaCuspCenterMixedCutoffPolynomial a = X^(6 : ℕ)-C (thetaCuspCutoffJacobiSum a)*X^(4 : ℕ)+
      C (thetaCuspCutoffJacobiPairs a)*X^(2 : ℕ)-C (thetaCuspCutoffJacobiProduct a) := by
  apply ThetaCuspCutoffJacobiAlgebra.shape (cutoff_positive_below ha0 ha)
  intro n hn
  obtain ⟨k,hk⟩ := hn
  rw [show n=2*k+1 by omega]
  exact thetaCuspCenterMixedSignedJet_odd a k

/-- Every displayed cutoff coefficient magnitude is strictly positive. -/
theorem thetaCuspCutoffJacobi_coefficients_pos
    {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
    0<thetaCuspCutoffJacobiSum a ∧ 0<thetaCuspCutoffJacobiPairs a ∧
      0<thetaCuspCutoffJacobiProduct a := by
  have hb (n : ℕ) (hn : 0<n) (hn6 : n<6) :
      0 < monicOrthoBeta (thetaCuspCenterMixedSignedJet a) n :=
    monicOrthoBeta_pos_below (cutoff_positive_below ha0 ha) hn hn6
  have h1 := hb (n:=1) (by omega) (by omega)
  have h2 := hb (n:=2) (by omega) (by omega)
  have h3 := hb (n:=3) (by omega) (by omega)
  have h4 := hb (n:=4) (by omega) (by omega)
  have h5 := hb (n:=5) (by omega) (by omega)
  dsimp only [thetaCuspCutoffJacobiSum, thetaCuspCutoffJacobiPairs,
    thetaCuspCutoffJacobiProduct]
  exact ⟨by positivity, by positivity, by positivity⟩

/-- Reflection fixes the actual degree-six minimizer before rank seven is known positive. -/
theorem thetaCuspCenterMixedCutoffPolynomial_even
    {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
    (thetaCuspCenterMixedCutoffPolynomial a).comp (-X) =
      thetaCuspCenterMixedCutoffPolynomial a := by
  rw [thetaCuspCenterMixedCutoffPolynomial_eq_jacobi ha0 ha]
  simp only [sub_comp, add_comp, pow_comp, mul_comp, C_comp, X_comp]
  ring

/-- Positive real magnitude of the cutoff on the imaginary axis. -/
def thetaCuspCutoffImaginarySymbol (a d : ℝ) : ℝ :=
  d^(6 : ℕ)+thetaCuspCutoffJacobiSum a*d^(4 : ℕ)+thetaCuspCutoffJacobiPairs a*d^(2 : ℕ)+
    thetaCuspCutoffJacobiProduct a

/-- The imaginary-axis readout retains every Jacobi coefficient with positive sign. -/
theorem thetaCuspCenterMixedCutoffPolynomial_eval_imaginary
    {a : ℝ} (ha0 : 0<a) (ha : a<1/2) (d : ℝ) :
    (thetaCuspCenterMixedCutoffPolynomial a).eval₂ Complex.ofRealHom (Complex.I*(d:ℂ)) =
      -(thetaCuspCutoffImaginarySymbol a d : ℂ) := by
  rw [thetaCuspCenterMixedCutoffPolynomial_eq_jacobi ha0 ha]
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_mul, eval₂_C, eval₂_X,
    Complex.ofRealHom_eq_coe, thetaCuspCutoffImaginarySymbol, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
  have hI6 : (Complex.I : ℂ)^(6 : ℕ) = -1 := by
    calc Complex.I^(6 : ℕ) = (Complex.I^(2 : ℕ))^(3 : ℕ) := by ring
         _ = -1 := by norm_num
  norm_num [hI6]
  ring

/-- A mixed geometric jet cannot cancel the actual cutoff's leading or constant terms. -/
theorem thetaCuspCutoffImaginarySymbol_square_lower
    {a : ℝ} (ha0 : 0<a) (ha : a<1/2) (d : ℝ) :
    (d^(6 : ℕ)+thetaCuspCutoffJacobiProduct a)^(2 : ℕ) ≤ (thetaCuspCutoffImaginarySymbol a d)^(2 : ℕ) := by
  obtain ⟨hS,hE,hF⟩ := thetaCuspCutoffJacobi_coefficients_pos ha0 ha
  have h0 : 0 ≤ d^(6 : ℕ)+thetaCuspCutoffJacobiProduct a := by positivity
  have hle : d^(6 : ℕ)+thetaCuspCutoffJacobiProduct a ≤ thetaCuspCutoffImaginarySymbol a d := by
    unfold thetaCuspCutoffImaginarySymbol
    nlinarith [mul_nonneg hS.le (pow_nonneg (sq_nonneg d) 2),
      mul_nonneg hE.le (sq_nonneg d)]
  exact pow_le_pow_left₀ h0 hle 2

/-- Exact rank-seven minimal norm in raw source-derivative coordinates. -/
theorem thetaCuspCenterMixedCutoffPolynomial_norm_eq_raw_jacobi
    {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
    let S := thetaCuspCutoffJacobiSum a
    let E := thetaCuspCutoffJacobiPairs a
    let F := thetaCuspCutoffJacobiProduct a
    let d := fun n => iteratedDeriv n (thetaCuspCenterMixedDensity a) 0
    momentInner (thetaCuspCenterMixedSignedJet a) (thetaCuspCenterMixedCutoffPolynomial a)
      (thetaCuspCenterMixedCutoffPolynomial a) =
      d 12+2*S*d 10+(S^(2 : ℕ)+2*E)*d 8+2*(S*E+F)*d 6+
        (E^(2 : ℕ)+2*S*F)*d 4+2*E*F*d 2+F^(2 : ℕ)*d 0 := by
  dsimp only
  rw [thetaCuspCenterMixedCutoffPolynomial_eq_jacobi ha0 ha, ThetaCuspCutoffJacobiAlgebra.shape_square]
  have hj := thetaCuspCenterMixedSignedJet_even a
  have h0 := hj 0
  have h2 := hj 1
  have h4 := hj 2
  have h6 := hj 3
  have h8 := hj 4
  have h10 := hj 5
  have h12 := hj 6
  norm_num at h0 h2 h4 h6 h8 h10 h12
  rw [h0,h2,h4,h6,h8,h10,h12]
  norm_num

end RHTower
