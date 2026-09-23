import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaNyquistFlux

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set

noncomputable section

namespace RHTower

/-- Symmetric polarization of the finite shifted reciprocal Hankel quadratic. -/
def xiShiftedReciprocalHankelBilinear
    (y : ℝ) {N : ℕ} (c e : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    c i * e j * (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ))).re

theorem xiShiftedReciprocalHankelBilinear_self
    (y : ℝ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y c c =
      xiShiftedReciprocalHankelQuadratic y c := by
  rfl

theorem xiShiftedReciprocalHankelBilinear_symm
    (y : ℝ) {N : ℕ} (c e : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y c e =
      xiShiftedReciprocalHankelBilinear y e c := by
  rw [xiShiftedReciprocalHankelBilinear, xiShiftedReciprocalHankelBilinear,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [add_comm (j : ℕ) (i : ℕ)]
  ring

theorem xiShiftedReciprocalHankelBilinear_add_left
    (y : ℝ) {N : ℕ} (c e f : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y (c + e) f =
      xiShiftedReciprocalHankelBilinear y c f +
        xiShiftedReciprocalHankelBilinear y e f := by
  simp only [xiShiftedReciprocalHankelBilinear, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem xiShiftedReciprocalHankelBilinear_sub_left
    (y : ℝ) {N : ℕ} (c e f : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y (c - e) f =
      xiShiftedReciprocalHankelBilinear y c f -
        xiShiftedReciprocalHankelBilinear y e f := by
  simp only [xiShiftedReciprocalHankelBilinear, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem xiShiftedReciprocalHankelBilinear_add_right
    (y : ℝ) {N : ℕ} (c e f : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y c (e + f) =
      xiShiftedReciprocalHankelBilinear y c e +
        xiShiftedReciprocalHankelBilinear y c f := by
  rw [xiShiftedReciprocalHankelBilinear_symm,
    xiShiftedReciprocalHankelBilinear_add_left,
    xiShiftedReciprocalHankelBilinear_symm y e c,
    xiShiftedReciprocalHankelBilinear_symm y f c]

theorem xiShiftedReciprocalHankelBilinear_sub_right
    (y : ℝ) {N : ℕ} (c e f : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y c (e - f) =
      xiShiftedReciprocalHankelBilinear y c e -
        xiShiftedReciprocalHankelBilinear y c f := by
  rw [xiShiftedReciprocalHankelBilinear_symm,
    xiShiftedReciprocalHankelBilinear_sub_left,
    xiShiftedReciprocalHankelBilinear_symm y e c,
    xiShiftedReciprocalHankelBilinear_symm y f c]

theorem xiShiftedReciprocalHankelQuadratic_add
    (y : ℝ) {N : ℕ} (c e : Fin N → ℝ) :
    xiShiftedReciprocalHankelQuadratic y (c + e) =
      xiShiftedReciprocalHankelQuadratic y c +
        xiShiftedReciprocalHankelQuadratic y e +
          2 * xiShiftedReciprocalHankelBilinear y c e := by
  rw [← xiShiftedReciprocalHankelBilinear_self,
    xiShiftedReciprocalHankelBilinear_add_left,
    xiShiftedReciprocalHankelBilinear_add_right,
    xiShiftedReciprocalHankelBilinear_add_right,
    xiShiftedReciprocalHankelBilinear_symm y e c]
  simp only [xiShiftedReciprocalHankelBilinear_self]
  ring

theorem xiShiftedReciprocalHankelQuadratic_sub
    (y : ℝ) {N : ℕ} (c e : Fin N → ℝ) :
    xiShiftedReciprocalHankelQuadratic y (c - e) =
      xiShiftedReciprocalHankelQuadratic y c +
        xiShiftedReciprocalHankelQuadratic y e -
          2 * xiShiftedReciprocalHankelBilinear y c e := by
  rw [← xiShiftedReciprocalHankelBilinear_self,
    xiShiftedReciprocalHankelBilinear_sub_left,
    xiShiftedReciprocalHankelBilinear_sub_right,
    xiShiftedReciprocalHankelBilinear_sub_right,
    xiShiftedReciprocalHankelBilinear_symm y e c]
  simp only [xiShiftedReciprocalHankelBilinear_self]
  ring

theorem xiShiftedReciprocalHankelBilinear_add_sub
    (y : ℝ) {N : ℕ} (c e : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y (c + e) (c - e) =
      xiShiftedReciprocalHankelQuadratic y c -
        xiShiftedReciprocalHankelQuadratic y e := by
  rw [xiShiftedReciprocalHankelBilinear_add_left,
    xiShiftedReciprocalHankelBilinear_sub_right,
    xiShiftedReciprocalHankelBilinear_sub_right,
    xiShiftedReciprocalHankelBilinear_symm y e c]
  simp only [xiShiftedReciprocalHankelBilinear_self]
  ring

/-- Polarized literal completed prime--Gamma balance. -/
def routeUShiftedCompletedPrimeGammaCrossBalance
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ)
    (t : {τ : ℝ // 0 < τ}) : ℝ :=
  (routeUShiftedCompletedPrimeGammaBalance y d (c + e) t -
      routeUShiftedCompletedPrimeGammaBalance y d (c - e) t) / 4

/-- Positive-time filtered cross-source kernel. -/
def routeUShiftedFilteredCompletedSourceCrossKernel
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ) (t : ℝ) : ℝ :=
  (routeUShiftedFilteredCompletedSourceKernel y d (c + e) t -
      routeUShiftedFilteredCompletedSourceKernel y d (c - e) t) / 4

theorem routeUShiftedFilteredCompletedSourceCrossKernel_eq
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ)
    {t : ℝ} (ht : 0 < t) :
    routeUShiftedFilteredCompletedSourceCrossKernel y d c e t =
      t ^ (2 * d) * Real.exp (-(y * t)) *
        routeUShiftedCompletedPrimeGammaCrossBalance y d c e ⟨t, ht⟩ := by
  rw [routeUShiftedFilteredCompletedSourceCrossKernel,
    routeUShiftedFilteredCompletedSourceKernel,
    routeUShiftedFilteredCompletedSourceKernel,
    dif_pos ht, dif_pos ht,
    routeUShiftedCompletedPrimeGammaCrossBalance]
  ring

theorem integrableOn_routeUShiftedFilteredCompletedSourceCrossKernel
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    IntegrableOn
      (routeUShiftedFilteredCompletedSourceCrossKernel y d c e) (Ioi (0 : ℝ)) := by
  exact ((integrableOn_routeUShiftedFilteredCompletedSourceKernel hy d (c + e)).sub
    (integrableOn_routeUShiftedFilteredCompletedSourceKernel hy d (c - e))).div_const 4

/-- Integral cross capital of the literal completed source. -/
def routeUShiftedFilteredCompletedSourceCrossCapital
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    routeUShiftedFilteredCompletedSourceCrossKernel y d c e t

theorem routeUShiftedFilteredCompletedSourceCrossCapital_eq
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    routeUShiftedFilteredCompletedSourceCrossCapital y d c e =
      Real.pi * ((2 * d).factorial : ℝ) *
        xiShiftedReciprocalHankelBilinear y c e := by
  calc
    routeUShiftedFilteredCompletedSourceCrossCapital y d c e =
        (routeUShiftedFilteredCompletedSourceCapital y d (c + e) -
          routeUShiftedFilteredCompletedSourceCapital y d (c - e)) / 4 := by
      rw [routeUShiftedFilteredCompletedSourceCrossCapital,
        routeUShiftedFilteredCompletedSourceCapital,
        routeUShiftedFilteredCompletedSourceCapital]
      change (∫ t in Ioi (0 : ℝ),
          (routeUShiftedFilteredCompletedSourceKernel y d (c + e) t -
            routeUShiftedFilteredCompletedSourceKernel y d (c - e) t) / 4) = _
      rw [integral_div,
        integral_sub
          (integrableOn_routeUShiftedFilteredCompletedSourceKernel hy d (c + e))
          (integrableOn_routeUShiftedFilteredCompletedSourceKernel hy d (c - e))]
    _ = Real.pi * ((2 * d).factorial : ℝ) *
          xiShiftedReciprocalHankelBilinear y c e := by
      rw [routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
        routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
        xiShiftedReciprocalHankelQuadratic_add,
        xiShiftedReciprocalHankelQuadratic_sub]
      ring

theorem routeUShiftedFilteredCompletedSourceCapital_add
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    routeUShiftedFilteredCompletedSourceCapital y d (c + e) =
      routeUShiftedFilteredCompletedSourceCapital y d c +
        routeUShiftedFilteredCompletedSourceCapital y d e +
          2 * routeUShiftedFilteredCompletedSourceCrossCapital y d c e := by
  rw [routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCrossCapital_eq hy,
    xiShiftedReciprocalHankelQuadratic_add]
  ring

theorem routeUShiftedFilteredCompletedSourceCapital_sub
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    routeUShiftedFilteredCompletedSourceCapital y d (c - e) =
      routeUShiftedFilteredCompletedSourceCapital y d c +
        routeUShiftedFilteredCompletedSourceCapital y d e -
          2 * routeUShiftedFilteredCompletedSourceCrossCapital y d c e := by
  rw [routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCrossCapital_eq hy,
    xiShiftedReciprocalHankelQuadratic_sub]
  ring

theorem routeUShiftedFilteredCompletedSourceCapital_sub_eq_cross_add_sub
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    routeUShiftedFilteredCompletedSourceCapital y d c -
        routeUShiftedFilteredCompletedSourceCapital y d e =
      routeUShiftedFilteredCompletedSourceCrossCapital y d (c + e) (c - e) := by
  rw [routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy,
    routeUShiftedFilteredCompletedSourceCrossCapital_eq hy,
    xiShiftedReciprocalHankelBilinear_add_sub]
  ring

theorem routeUShiftedFilteredCompletedSourceCapital_parallelogram
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    2 * (routeUShiftedFilteredCompletedSourceCapital y d c +
        routeUShiftedFilteredCompletedSourceCapital y d e) =
      routeUShiftedFilteredCompletedSourceCapital y d (c + e) +
        routeUShiftedFilteredCompletedSourceCapital y d (c - e) := by
  rw [routeUShiftedFilteredCompletedSourceCapital_add hy,
    routeUShiftedFilteredCompletedSourceCapital_sub hy]
  ring

theorem routeUShiftedFilteredCompletedSourceCrossCapital_eq_difference
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    4 * routeUShiftedFilteredCompletedSourceCrossCapital y d c e =
      routeUShiftedFilteredCompletedSourceCapital y d (c + e) -
        routeUShiftedFilteredCompletedSourceCapital y d (c - e) := by
  rw [routeUShiftedFilteredCompletedSourceCapital_add hy,
    routeUShiftedFilteredCompletedSourceCapital_sub hy]
  ring

theorem routeUShiftedFilteredCompletedSourceCapital_neg_trichotomy
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ)
    (hneg : routeUShiftedFilteredCompletedSourceCapital y d (c + e) < 0) :
    routeUShiftedFilteredCompletedSourceCapital y d c < 0 ∨
      routeUShiftedFilteredCompletedSourceCapital y d e < 0 ∨
        routeUShiftedFilteredCompletedSourceCrossCapital y d c e < 0 := by
  rw [routeUShiftedFilteredCompletedSourceCapital_add hy] at hneg
  by_contra h
  push Not at h
  obtain ⟨hc, he, hce⟩ := h
  linarith

theorem routeUShiftedFilteredCompletedSourceCrossCapital_strict_of_add_neg
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ)
    (hc : 0 ≤ routeUShiftedFilteredCompletedSourceCapital y d c)
    (he : 0 ≤ routeUShiftedFilteredCompletedSourceCapital y d e)
    (hneg : routeUShiftedFilteredCompletedSourceCapital y d (c + e) < 0) :
    2 * routeUShiftedFilteredCompletedSourceCrossCapital y d c e <
        -(routeUShiftedFilteredCompletedSourceCapital y d c +
          routeUShiftedFilteredCompletedSourceCapital y d e) ∧
      -(routeUShiftedFilteredCompletedSourceCapital y d c +
          routeUShiftedFilteredCompletedSourceCapital y d e) ≤ 0 := by
  rw [routeUShiftedFilteredCompletedSourceCapital_add hy] at hneg
  constructor <;> linarith

theorem exists_routeUShiftedCompletedPrimeGammaCrossBalance_neg_of_crossCapital_neg
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ)
    (hcap : routeUShiftedFilteredCompletedSourceCrossCapital y d c e < 0) :
    ∃ t : {τ : ℝ // 0 < τ},
      routeUShiftedCompletedPrimeGammaCrossBalance y d c e t < 0 := by
  by_contra h
  push Not at h
  have hkernel : 0 ≤ routeUShiftedFilteredCompletedSourceCrossCapital y d c e := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [routeUShiftedFilteredCompletedSourceCrossKernel_eq y d c e ht]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg ht.le _) (Real.exp_nonneg _)) (h ⟨t, ht⟩)
  exact (not_lt_of_ge hkernel) hcap

theorem exists_routeUShiftedCompletedPrimeGammaPolarizedAnomaly_of_capital_add_neg
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c e : Fin (d + 1) → ℝ)
    (hneg : routeUShiftedFilteredCompletedSourceCapital y d (c + e) < 0) :
    (∃ t : {τ : ℝ // 0 < τ},
        routeUShiftedCompletedPrimeGammaBalance y d c t < 0) ∨
      (∃ t : {τ : ℝ // 0 < τ},
        routeUShiftedCompletedPrimeGammaBalance y d e t < 0) ∨
      (∃ t : {τ : ℝ // 0 < τ},
        routeUShiftedCompletedPrimeGammaCrossBalance y d c e t < 0) := by
  rcases routeUShiftedFilteredCompletedSourceCapital_neg_trichotomy hy d c e hneg with
    hc | he | hce
  · exact Or.inl
      (exists_routeUShiftedCompletedPrimeGammaBalance_neg_of_capital_neg y d c hc)
  · exact Or.inr (Or.inl
      (exists_routeUShiftedCompletedPrimeGammaBalance_neg_of_capital_neg y d e he))
  · exact Or.inr (Or.inr
      (exists_routeUShiftedCompletedPrimeGammaCrossBalance_neg_of_crossCapital_neg
        y d c e hce))

/-- Antipodal action on a hard-edge polynomial. -/
def routeUHardEdgeAntipodalPolynomial (P : Polynomial ℝ) : Polynomial ℝ :=
  P.comp (-Polynomial.X)

theorem eval_routeUHardEdgeAntipodalPolynomial
    (P : Polynomial ℝ) (x : ℝ) :
    (routeUHardEdgeAntipodalPolynomial P).eval x = P.eval (-x) := by
  simp [routeUHardEdgeAntipodalPolynomial]

theorem routeUHardEdgeAntipodalPolynomial_involutive
    (P : Polynomial ℝ) :
    routeUHardEdgeAntipodalPolynomial (routeUHardEdgeAntipodalPolynomial P) = P := by
  exact Polynomial.comp_neg_X_comp_neg_X P

/-- Chebyshev modes diagonalize the antipodal action. -/
theorem routeUHardEdgeAntipodalPolynomial_chebyshevT (n : ℤ) :
    routeUHardEdgeAntipodalPolynomial (Polynomial.Chebyshev.T ℝ n) =
      Polynomial.C ((n.negOnePow : ℤ) : ℝ) * Polynomial.Chebyshev.T ℝ n := by
  apply Polynomial.funext
  intro x
  rw [eval_routeUHardEdgeAntipodalPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.Chebyshev.T_eval_neg]

/-- Even eigencoordinate of one antipodal orbit. -/
def routeUHardEdgeEvenChannel (P : Polynomial ℝ) : Polynomial ℝ :=
  (1 / 2 : ℝ) • (P + routeUHardEdgeAntipodalPolynomial P)

/-- Odd eigencoordinate of one antipodal orbit. -/
def routeUHardEdgeOddChannel (P : Polynomial ℝ) : Polynomial ℝ :=
  (1 / 2 : ℝ) • (P - routeUHardEdgeAntipodalPolynomial P)

theorem routeUHardEdgeEvenChannel_add_oddChannel (P : Polynomial ℝ) :
    routeUHardEdgeEvenChannel P + routeUHardEdgeOddChannel P = P := by
  rw [routeUHardEdgeEvenChannel, routeUHardEdgeOddChannel]
  module

theorem routeUHardEdgeEvenChannel_sub_oddChannel (P : Polynomial ℝ) :
    routeUHardEdgeEvenChannel P - routeUHardEdgeOddChannel P =
      routeUHardEdgeAntipodalPolynomial P := by
  rw [routeUHardEdgeEvenChannel, routeUHardEdgeOddChannel]
  module

theorem routeUHardEdgeAntipodalPolynomial_evenChannel (P : Polynomial ℝ) :
    routeUHardEdgeAntipodalPolynomial (routeUHardEdgeEvenChannel P) =
      routeUHardEdgeEvenChannel P := by
  rw [routeUHardEdgeAntipodalPolynomial, routeUHardEdgeEvenChannel]
  simp only [Polynomial.smul_comp, Polynomial.add_comp]
  simp only [routeUHardEdgeAntipodalPolynomial,
    Polynomial.comp_neg_X_comp_neg_X]
  module

theorem routeUHardEdgeAntipodalPolynomial_oddChannel (P : Polynomial ℝ) :
    routeUHardEdgeAntipodalPolynomial (routeUHardEdgeOddChannel P) =
      -routeUHardEdgeOddChannel P := by
  rw [routeUHardEdgeAntipodalPolynomial, routeUHardEdgeOddChannel]
  simp only [Polynomial.smul_comp, Polynomial.sub_comp]
  simp only [routeUHardEdgeAntipodalPolynomial,
    Polynomial.comp_neg_X_comp_neg_X]
  module

/-- Physical hard-edge inversion is the antipodal map in the Cayley chart. -/
theorem xiHardEdgeCayleyCoordinate_inversion
    {a x : ℝ} (ha : a ≠ 0) (hx : x ≠ 0) :
    xiHardEdgeCayleyCoordinate (a : ℂ) ((a ^ (2 : ℕ) / x : ℝ) : ℂ) =
      -xiHardEdgeCayleyCoordinate (a : ℂ) (x : ℂ) := by
  rw [xiHardEdgeCayleyCoordinate, xiHardEdgeCayleyCoordinate]
  push_cast
  norm_cast
  field_simp [ha, hx]
  ring

/-- Degree-free Cauchy density transforms with the exact inversion Jacobian. -/
theorem routeUHardEdgeCauchyDensity_antipodal_inversion
    {a x : ℝ} (ha : a ≠ 0) (hx : x ≠ 0) (P : Polynomial ℝ) :
    x ^ (2 : ℕ) * routeUHardEdgeCauchyDensity a
        (routeUHardEdgeAntipodalPolynomial P) x =
      a ^ (2 : ℕ) * routeUHardEdgeCauchyDensity a P (a ^ (2 : ℕ) / x) := by
  rw [routeUHardEdgeCauchyDensity, routeUHardEdgeCauchyDensity,
    eval_routeUHardEdgeAntipodalPolynomial]
  have hleft : a ^ (2 : ℕ) + x ^ (2 : ℕ) ≠ 0 := by positivity
  have hinv : a ^ (2 : ℕ) + (a ^ (2 : ℕ) / x) ^ (2 : ℕ) ≠ 0 := by positivity
  have hcoord :
      -((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ))) =
        (a ^ (2 : ℕ) - (a ^ (2 : ℕ) / x) ^ (2 : ℕ)) /
          (a ^ (2 : ℕ) + (a ^ (2 : ℕ) / x) ^ (2 : ℕ)) := by
    field_simp [ha, hx]
    ring
  rw [hcoord]
  field_simp [ha, hx, hleft, hinv]
  ring

/-- Sum of two zero-padded hard-edge coefficient channels. -/
def routeUHardEdgeCommonFullCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Fin (routeUHardEdgeCommonLiftDegree a P Q + 1) → ℝ :=
  routeUHardEdgeCommonLeftCoefficients a P Q +
    routeUHardEdgeCommonRightCoefficients a P Q

/-- Difference of two zero-padded hard-edge coefficient channels. -/
def routeUHardEdgeCommonAntipodalCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Fin (routeUHardEdgeCommonLiftDegree a P Q + 1) → ℝ :=
  routeUHardEdgeCommonLeftCoefficients a P Q -
    routeUHardEdgeCommonRightCoefficients a P Q

theorem xiHardEdgeReciprocalPolynomial_add
    (a : ℝ) (P Q : Polynomial ℝ) :
    xiHardEdgeReciprocalPolynomial a (P + Q) =
      xiHardEdgeReciprocalPolynomial a P +
        xiHardEdgeReciprocalPolynomial a Q := by
  simp [xiHardEdgeReciprocalPolynomial]

theorem xiHardEdgeReciprocalPolynomial_sub
    (a : ℝ) (P Q : Polynomial ℝ) :
    xiHardEdgeReciprocalPolynomial a (P - Q) =
      xiHardEdgeReciprocalPolynomial a P -
        xiHardEdgeReciprocalPolynomial a Q := by
  simp [xiHardEdgeReciprocalPolynomial]

theorem ofFn_routeUHardEdgeCommonFullCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Polynomial.ofFn (routeUHardEdgeCommonLiftDegree a P Q + 1)
        (routeUHardEdgeCommonFullCoefficients a P Q) =
      xiHardEdgeReciprocalPolynomial a (P + Q) := by
  rw [routeUHardEdgeCommonFullCoefficients, map_add,
    ofFn_routeUHardEdgeCommonLeftCoefficients,
    ofFn_routeUHardEdgeCommonRightCoefficients,
    xiHardEdgeReciprocalPolynomial_add]

theorem ofFn_routeUHardEdgeCommonAntipodalCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Polynomial.ofFn (routeUHardEdgeCommonLiftDegree a P Q + 1)
        (routeUHardEdgeCommonAntipodalCoefficients a P Q) =
      xiHardEdgeReciprocalPolynomial a (P - Q) := by
  rw [routeUHardEdgeCommonAntipodalCoefficients, map_sub,
    ofFn_routeUHardEdgeCommonLeftCoefficients,
    ofFn_routeUHardEdgeCommonRightCoefficients,
    xiHardEdgeReciprocalPolynomial_sub]

theorem routeUHardEdgeCommonFullQuadratic_eq_trace_re
    (a : ℝ) (P Q : Polynomial ℝ) :
    xiShiftedReciprocalHankelQuadratic (a ^ (2 : ℕ))
        (routeUHardEdgeCommonFullCoefficients a P Q) =
      (xiShiftedReciprocalTraceHankel (a ^ (2 : ℕ))
        (xiHardEdgeReciprocalPolynomial a (P + Q))).re := by
  have htrace := xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    (sq_nonneg a) 0 (routeUHardEdgeCommonLiftDegree a P Q + 1)
      (routeUHardEdgeCommonFullCoefficients a P Q)
  simp only [pow_zero, one_mul, ofFn_routeUHardEdgeCommonFullCoefficients,
    Nat.mul_zero, Nat.zero_add] at htrace
  rw [xiShiftedReciprocalHankelQuadratic, htrace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem routeUHardEdgeCommonAntipodalQuadratic_eq_trace_re
    (a : ℝ) (P Q : Polynomial ℝ) :
    xiShiftedReciprocalHankelQuadratic (a ^ (2 : ℕ))
        (routeUHardEdgeCommonAntipodalCoefficients a P Q) =
      (xiShiftedReciprocalTraceHankel (a ^ (2 : ℕ))
        (xiHardEdgeReciprocalPolynomial a (P - Q))).re := by
  have htrace := xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    (sq_nonneg a) 0 (routeUHardEdgeCommonLiftDegree a P Q + 1)
      (routeUHardEdgeCommonAntipodalCoefficients a P Q)
  simp only [pow_zero, one_mul, ofFn_routeUHardEdgeCommonAntipodalCoefficients,
    Nat.mul_zero, Nat.zero_add] at htrace
  rw [xiShiftedReciprocalHankelQuadratic, htrace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem routeUHardEdgeLiftQuadratic_eq_trace_re
    (a : ℝ) (P : Polynomial ℝ) :
    xiShiftedReciprocalHankelQuadratic (a ^ (2 : ℕ))
        (xiHardEdgeLiftCoefficients a P) =
      (xiShiftedReciprocalTraceHankel (a ^ (2 : ℕ))
        (xiHardEdgeReciprocalPolynomial a P)).re := by
  have htrace := xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    (sq_nonneg a) 0 (xiHardEdgeLiftSize a P)
      (xiHardEdgeLiftCoefficients a P)
  simp only [pow_zero, one_mul, ofFn_xiHardEdgeLiftCoefficients,
    Nat.mul_zero, Nat.zero_add] at htrace
  rw [xiShiftedReciprocalHankelQuadratic, htrace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- Full common-filter source capital of two polynomial channels. -/
def routeUHardEdgeCommonFullPrimeGammaCapital
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) : ℝ :=
  routeUShiftedFilteredCompletedSourceCapital (a.1 ^ (2 : ℕ))
    (routeUHardEdgeCommonLiftDegree a.1 P Q)
    (routeUHardEdgeCommonFullCoefficients a.1 P Q)

/-- Polarized cross capital between two common-filter polynomial channels. -/
def routeUHardEdgeCommonCrossPrimeGammaCapital
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) : ℝ :=
  routeUShiftedFilteredCompletedSourceCrossCapital (a.1 ^ (2 : ℕ))
    (routeUHardEdgeCommonLiftDegree a.1 P Q)
    (routeUHardEdgeCommonLeftCoefficients a.1 P Q)
    (routeUHardEdgeCommonRightCoefficients a.1 P Q)

theorem routeUHardEdgeCommonFullPrimeGammaCapital_eq
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) :
    routeUHardEdgeCommonFullPrimeGammaCapital a P Q =
      Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree a.1 P Q).factorial : ℝ) *
        xiShiftedReciprocalHankelQuadratic (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonFullCoefficients a.1 P Q) := by
  exact routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic
    (sq_pos_of_pos a.2) _ _

theorem routeUHardEdgeCommonCrossPrimeGammaCapital_eq
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) :
    routeUHardEdgeCommonCrossPrimeGammaCapital a P Q =
      Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree a.1 P Q).factorial : ℝ) *
        xiShiftedReciprocalHankelBilinear (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLeftCoefficients a.1 P Q)
          (routeUHardEdgeCommonRightCoefficients a.1 P Q) := by
  exact routeUShiftedFilteredCompletedSourceCrossCapital_eq
    (sq_pos_of_pos a.2) _ _ _

theorem routeUHardEdgeCommonFullCapital_neg_trichotomy
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ)
    (hneg : routeUHardEdgeCommonFullPrimeGammaCapital a P Q < 0) :
    routeUHardEdgeCommonLeftPrimeGammaCapital a P Q < 0 ∨
      routeUHardEdgeCommonRightPrimeGammaCapital a P Q < 0 ∨
        routeUHardEdgeCommonCrossPrimeGammaCapital a P Q < 0 := by
  exact routeUShiftedFilteredCompletedSourceCapital_neg_trichotomy
    (sq_pos_of_pos a.2) (routeUHardEdgeCommonLiftDegree a.1 P Q)
    (routeUHardEdgeCommonLeftCoefficients a.1 P Q)
    (routeUHardEdgeCommonRightCoefficients a.1 P Q) hneg

theorem exists_routeUHardEdgeCommonPolarizedPrimeGammaAnomaly_of_fullCapital_neg
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ)
    (hneg : routeUHardEdgeCommonFullPrimeGammaCapital a P Q < 0) :
    (routeUHardEdgeCommonLeftPrimeGammaCapital a P Q < 0 ∧
      ∃ t : {τ : ℝ // 0 < τ},
        routeUShiftedCompletedPrimeGammaBalance (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLiftDegree a.1 P Q)
          (routeUHardEdgeCommonLeftCoefficients a.1 P Q) t < 0) ∨
    (routeUHardEdgeCommonRightPrimeGammaCapital a P Q < 0 ∧
      ∃ t : {τ : ℝ // 0 < τ},
        routeUShiftedCompletedPrimeGammaBalance (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLiftDegree a.1 P Q)
          (routeUHardEdgeCommonRightCoefficients a.1 P Q) t < 0) ∨
    (routeUHardEdgeCommonCrossPrimeGammaCapital a P Q < 0 ∧
      ∃ t : {τ : ℝ // 0 < τ},
        routeUShiftedCompletedPrimeGammaCrossBalance (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLiftDegree a.1 P Q)
          (routeUHardEdgeCommonLeftCoefficients a.1 P Q)
          (routeUHardEdgeCommonRightCoefficients a.1 P Q) t < 0) := by
  rcases routeUHardEdgeCommonFullCapital_neg_trichotomy a P Q hneg with hc | he | hce
  · exact Or.inl ⟨hc,
      exists_routeUShiftedCompletedPrimeGammaBalance_neg_of_capital_neg
        (a.1 ^ (2 : ℕ)) _ _ hc⟩
  · exact Or.inr (Or.inl ⟨he,
      exists_routeUShiftedCompletedPrimeGammaBalance_neg_of_capital_neg
        (a.1 ^ (2 : ℕ)) _ _ he⟩)
  · exact Or.inr (Or.inr ⟨hce,
      exists_routeUShiftedCompletedPrimeGammaCrossBalance_neg_of_crossCapital_neg
        (a.1 ^ (2 : ℕ)) _ _ _ hce⟩)

/-- Actual even source polynomial of the cofinal explicit Route-U packet. -/
def routeUExplicitAntipodalEvenSourcePolynomial
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : Polynomial ℝ :=
  routeUHardEdgeEvenChannel
    (routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t))

/-- Actual odd source polynomial of the cofinal explicit Route-U packet. -/
def routeUExplicitAntipodalOddSourcePolynomial
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : Polynomial ℝ :=
  routeUHardEdgeOddChannel
    (routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t))

theorem routeUExplicitAntipodalChannels_sum
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) :
    routeUExplicitAntipodalEvenSourcePolynomial P t n k +
        routeUExplicitAntipodalOddSourcePolynomial P t n k =
      routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t) := by
  exact routeUHardEdgeEvenChannel_add_oddChannel _

theorem routeUExplicitAntipodalChannels_difference
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) :
    routeUExplicitAntipodalEvenSourcePolynomial P t n k -
        routeUExplicitAntipodalOddSourcePolynomial P t n k =
      routeUHardEdgeAntipodalPolynomial
        (routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t)) := by
  exact routeUHardEdgeEvenChannel_sub_oddChannel _

theorem routeUExplicitAntipodalFullQuadratic_eq_explicitQuadratic
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) :
    xiShiftedReciprocalHankelQuadratic
        (routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ))
        (routeUHardEdgeCommonFullCoefficients
          (routeUHardEdgeMass (k : ℝ))
          (routeUExplicitAntipodalEvenSourcePolynomial P t n k)
          (routeUExplicitAntipodalOddSourcePolynomial P t n k)) =
      routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k := by
  let packet := routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t)
  let evenPacket := routeUExplicitAntipodalEvenSourcePolynomial P t n k
  let oddPacket := routeUExplicitAntipodalOddSourcePolynomial P t n k
  have hfull := routeUHardEdgeCommonFullQuadratic_eq_trace_re
    (routeUHardEdgeMass (k : ℝ)) evenPacket oddPacket
  have horiginal := routeUHardEdgeLiftQuadratic_eq_trace_re
    (routeUHardEdgeMass (k : ℝ)) packet
  have hsum : evenPacket + oddPacket = packet := by
    exact routeUExplicitAntipodalChannels_sum P t n k
  rw [hsum] at hfull
  change xiShiftedReciprocalHankelQuadratic
      (routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ))
      (routeUHardEdgeCommonFullCoefficients
        (routeUHardEdgeMass (k : ℝ)) evenPacket oddPacket) =
    xiShiftedReciprocalHankelQuadratic
      (routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ))
      (xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ)) packet)
  exact hfull.trans horiginal.symm

/-- Full common-filter capital of the actual explicit antipodal channel pair. -/
def routeUExplicitAntipodalFullPrimeGammaCapital
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : ℝ :=
  routeUHardEdgeCommonFullPrimeGammaCapital
    ⟨routeUHardEdgeMass (k : ℝ), routeUHardEdgeMass_pos (k : ℝ)⟩
    (routeUExplicitAntipodalEvenSourcePolynomial P t n k)
    (routeUExplicitAntipodalOddSourcePolynomial P t n k)

theorem routeUExplicitAntipodalFullPrimeGammaCapital_eq
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) :
    routeUExplicitAntipodalFullPrimeGammaCapital P t n k =
      Real.pi *
        ((2 * routeUHardEdgeCommonLiftDegree (routeUHardEdgeMass (k : ℝ))
          (routeUExplicitAntipodalEvenSourcePolynomial P t n k)
          (routeUExplicitAntipodalOddSourcePolynomial P t n k)).factorial : ℝ) *
        routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k := by
  rw [routeUExplicitAntipodalFullPrimeGammaCapital,
    routeUHardEdgeCommonFullPrimeGammaCapital_eq,
    routeUExplicitAntipodalFullQuadratic_eq_explicitQuadratic]

/-- Labelled diagonal-or-cross anomaly of the actual explicit antipodal pair. -/
def RouteUExplicitAntipodalPrimeGammaAlternative
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : Prop :=
  let a : RouteUPositiveHardEdgeMass :=
    ⟨routeUHardEdgeMass (k : ℝ), routeUHardEdgeMass_pos (k : ℝ)⟩
  let E := routeUExplicitAntipodalEvenSourcePolynomial P t n k
  let O := routeUExplicitAntipodalOddSourcePolynomial P t n k
  (routeUHardEdgeCommonLeftPrimeGammaCapital a E O < 0 ∧
      ∃ s : {σ : ℝ // 0 < σ},
        routeUShiftedCompletedPrimeGammaBalance (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLiftDegree a.1 E O)
          (routeUHardEdgeCommonLeftCoefficients a.1 E O) s < 0) ∨
    (routeUHardEdgeCommonRightPrimeGammaCapital a E O < 0 ∧
      ∃ s : {σ : ℝ // 0 < σ},
        routeUShiftedCompletedPrimeGammaBalance (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLiftDegree a.1 E O)
          (routeUHardEdgeCommonRightCoefficients a.1 E O) s < 0) ∨
    (routeUHardEdgeCommonCrossPrimeGammaCapital a E O < 0 ∧
      ∃ s : {σ : ℝ // 0 < σ},
        routeUShiftedCompletedPrimeGammaCrossBalance (a.1 ^ (2 : ℕ))
          (routeUHardEdgeCommonLiftDegree a.1 E O)
          (routeUHardEdgeCommonLeftCoefficients a.1 E O)
          (routeUHardEdgeCommonRightCoefficients a.1 E O) s < 0)

theorem routeUExplicitAntipodalPrimeGammaAlternative_of_fullCapital_neg
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ)
    (hneg : routeUExplicitAntipodalFullPrimeGammaCapital P t n k < 0) :
    RouteUExplicitAntipodalPrimeGammaAlternative P t n k := by
  exact exists_routeUHardEdgeCommonPolarizedPrimeGammaAnomaly_of_fullCapital_neg
    ⟨routeUHardEdgeMass (k : ℝ), routeUHardEdgeMass_pos (k : ℝ)⟩
    (routeUExplicitAntipodalEvenSourcePolynomial P t n k)
    (routeUExplicitAntipodalOddSourcePolynomial P t n k) hneg

/-- Fixed-carrier cofinal false-RH phase with a labelled literal source anomaly at every mass. -/
def XiShiftedHardEdgeCofinalPrimeGammaPolarizationPhase : Prop :=
  ∃ (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n K : ℕ),
    ∀ k : ℕ, K ≤ k →
      routeUExplicitAntipodalFullPrimeGammaCapital P t n k < 0 ∧
      RouteUExplicitAntipodalPrimeGammaAlternative P t n k ∧
      routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ) <
        routeUParabolicDegreeHorizon *
          (routeUExplicitFiniteHankelSize n k
            (routeUXiHeatPhysicalReal P t) : ℝ) ^ (2 : ℕ) ∧
      routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) ≤
        (n + 1) * (k + 1) + 2

/-- False RH is exactly a cofinal actual antipodal channel family with a labelled literal
diagonal or cross completed prime--Gamma inversion at every sufficiently large mass. -/
theorem not_rh_iff_xiShiftedHardEdgeCofinalPrimeGammaPolarizationPhase :
    ¬ RiemannHypothesis ↔ XiShiftedHardEdgeCofinalPrimeGammaPolarizationPhase := by
  rw [not_rh_iff_xiShiftedHardEdgeCofinalLinearNegativePhase]
  constructor
  · rintro ⟨P, t, n, K, hphase⟩
    refine ⟨P, t, n, K, fun k hk => ?_⟩
    obtain ⟨hquad, hlower, hupper⟩ := hphase k hk
    have hcapital : routeUExplicitAntipodalFullPrimeGammaCapital P t n k < 0 := by
      rw [routeUExplicitAntipodalFullPrimeGammaCapital_eq]
      have hfactor : 0 < Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree (routeUHardEdgeMass (k : ℝ))
            (routeUExplicitAntipodalEvenSourcePolynomial P t n k)
            (routeUExplicitAntipodalOddSourcePolynomial P t n k)).factorial : ℝ) := by
        positivity
      nlinarith
    exact ⟨hcapital,
      routeUExplicitAntipodalPrimeGammaAlternative_of_fullCapital_neg
        P t n k hcapital,
      hlower, hupper⟩
  · rintro ⟨P, t, n, K, hphase⟩
    refine ⟨P, t, n, K, fun k hk => ?_⟩
    obtain ⟨hcapital, _halternative, hlower, hupper⟩ := hphase k hk
    have hquad :
        routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k < 0 := by
      rw [routeUExplicitAntipodalFullPrimeGammaCapital_eq] at hcapital
      have hfactor : 0 < Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree (routeUHardEdgeMass (k : ℝ))
            (routeUExplicitAntipodalEvenSourcePolynomial P t n k)
            (routeUExplicitAntipodalOddSourcePolynomial P t n k)).factorial : ℝ) := by
        positivity
      nlinarith
    exact ⟨hquad, hlower, hupper⟩

/-- Premise-free Route-U source polarization dichotomy. -/
theorem riemannHypothesis_or_xiShiftedHardEdgeCofinalPrimeGammaPolarizationPhase :
    RiemannHypothesis ∨ XiShiftedHardEdgeCofinalPrimeGammaPolarizationPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (not_rh_iff_xiShiftedHardEdgeCofinalPrimeGammaPolarizationPhase.mp hRH)

end RHTower
