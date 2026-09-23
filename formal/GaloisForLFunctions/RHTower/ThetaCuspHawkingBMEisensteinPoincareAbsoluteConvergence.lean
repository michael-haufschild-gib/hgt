import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly
import GaloisForLFunctions.RHTower.SuzukiPolynomialEventSummability

/-!
# Absolute convergence of the completed-Eisenstein primitive Poincare series

For an upper-half-plane coordinate `z = x + i y`, set

`Q_z(c,d) = (c y)^(2 : ℕ) + (c x + d)^(2 : ℕ)`.

The primitive-pair Eisenstein seed is `(y / Q_z(c,d))^s`.  This module proves, from the corpus
one-dimensional integer-power summability theorem, that the full primitive-pair family is
absolutely summable whenever `Re(s) > 1`.  The missing two-dimensional estimate is an explicit
positive-definite coercivity law

`(1+|c|)(1+|d|) <= D_z Q_z(c,d)`.

The half-plane and convergence inequalities live inside structures, so the headline theorems
have no external hypotheses.  The module also classifies the `c = 0` primitive pairs as exactly
`(0,1)` and `(0,-1)` and proves that their total seed is `2 y^s`; hence the conventional factor
`1/2` produces the leading constant term `y^s`.

This is the convergence-chamber entrance to the actual Poincare/Fourier equality and truncated
Stokes theorem.  It does not assert that equality or analytic continuation.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [POINCARE CONVERGENCE CHAMBER]`
-/

open Complex Real Finset Filter Topology
open scoped BigOperators NNReal

namespace RHTower
noncomputable section

structure D4BMUpperHalfPlaneCoordinate where
  x : ℝ
  y : ℝ
  y_pos : 0 < y

structure D4BMEisensteinAbsoluteConvergenceParameter where
  s : ℂ
  re_gt_one : 1 < s.re

def d4BMPoincareQuadratic (z : D4BMUpperHalfPlaneCoordinate) (p : ℤ × ℤ) : ℝ :=
  ((p.1 : ℝ) * z.y) ^ 2 + ((p.1 : ℝ) * z.x + (p.2 : ℝ)) ^ 2

lemma d4BM_one_le_sq_add_sq_of_int_pair_ne_zero (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  have hp' : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_cases hc : p.1 = 0
    · right
      intro hd
      exact hp (Prod.ext hc hd)
    · exact Or.inl hc
  rcases hp' with hc | hd
  · have hcNat : 1 ≤ p.1.natAbs := (Int.natAbs_pos.mpr hc)
    have hcReal : (1 : ℝ) ≤ |(p.1 : ℝ)| := by
      rw [show |(p.1 : ℝ)| = (p.1.natAbs : ℝ) by simp [Int.cast_abs]]
      exact_mod_cast hcNat
    nlinarith [sq_nonneg (p.2 : ℝ), sq_abs (p.1 : ℝ)]
  · have hdNat : 1 ≤ p.2.natAbs := (Int.natAbs_pos.mpr hd)
    have hdReal : (1 : ℝ) ≤ |(p.2 : ℝ)| := by
      rw [show |(p.2 : ℝ)| = (p.2.natAbs : ℝ) by simp [Int.cast_abs]]
      exact_mod_cast hdNat
    nlinarith [sq_nonneg (p.1 : ℝ), sq_abs (p.2 : ℝ)]

lemma d4BM_product_one_add_abs_le_four_sq_add_sq (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    (1 + |(p.1 : ℝ)|) * (1 + |(p.2 : ℝ)|) ≤
      4 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) := by
  have h1 := d4BM_one_le_sq_add_sq_of_int_pair_ne_zero p hp
  have hc : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
  have hd : 0 ≤ |(p.2 : ℝ)| := abs_nonneg _
  have hc2 : |(p.1 : ℝ)| ^ 2 = (p.1 : ℝ) ^ 2 := sq_abs _
  have hd2 : |(p.2 : ℝ)| ^ 2 = (p.2 : ℝ) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|(p.1 : ℝ)| - |(p.2 : ℝ)|),
    sq_nonneg (|(p.1 : ℝ)| - 1), sq_nonneg (|(p.2 : ℝ)| - 1)]

lemma d4BM_scaled_lattice_sq_le_quadratic
    (z : D4BMUpperHalfPlaneCoordinate) (p : ℤ × ℤ) :
    z.y ^ 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤
      (2 * z.y ^ 2 + 1 + 2 * z.x ^ 2) * d4BMPoincareQuadratic z p := by
  have hy2 : 0 ≤ z.y ^ 2 := sq_nonneg _
  have hcx : 0 ≤ ((p.1 : ℝ) * z.x + (p.2 : ℝ)) ^ 2 := sq_nonneg _
  have hcy : 0 ≤ ((p.1 : ℝ) * z.y) ^ 2 := sq_nonneg _
  have hd : (p.2 : ℝ) ^ 2 ≤
      2 * ((p.1 : ℝ) * z.x + (p.2 : ℝ)) ^ 2 +
        2 * ((p.1 : ℝ) * z.x) ^ 2 := by
    nlinarith [sq_nonneg (((p.1 : ℝ) * z.x + (p.2 : ℝ)) + (p.1 : ℝ) * z.x)]
  rw [d4BMPoincareQuadratic]
  nlinarith [mul_self_nonneg ((p.1 : ℝ) * z.y),
    mul_self_nonneg ((p.1 : ℝ) * z.x)]

def d4BMPoincareCoercivityConstant (z : D4BMUpperHalfPlaneCoordinate) : ℝ :=
  4 * (2 * z.y ^ 2 + 1 + 2 * z.x ^ 2) / z.y ^ 2

lemma d4BMPoincareCoercivityConstant_pos (z : D4BMUpperHalfPlaneCoordinate) :
    0 < d4BMPoincareCoercivityConstant z := by
  unfold d4BMPoincareCoercivityConstant
  have hK : 0 < 2 * z.y ^ 2 + 1 + 2 * z.x ^ 2 := by
    nlinarith [sq_nonneg z.y, sq_nonneg z.x]
  exact div_pos (mul_pos (by norm_num) hK) (sq_pos_of_pos z.y_pos)

lemma d4BMPoincareQuadratic_pos (z : D4BMUpperHalfPlaneCoordinate)
    (p : ℤ × ℤ) (hp : p ≠ (0, 0)) : 0 < d4BMPoincareQuadratic z p := by
  by_cases hc : p.1 = 0
  · have hd : p.2 ≠ 0 := by
      intro hd
      exact hp (Prod.ext hc hd)
    have hdR : (p.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
    simp [d4BMPoincareQuadratic, hc, sq_pos_of_ne_zero hdR]
  · have hcR : (p.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hcy : (p.1 : ℝ) * z.y ≠ 0 := mul_ne_zero hcR z.y_pos.ne'
    rw [d4BMPoincareQuadratic]
    nlinarith [sq_pos_of_ne_zero hcy,
      sq_nonneg ((p.1 : ℝ) * z.x + (p.2 : ℝ))]

lemma d4BM_lattice_product_le_coercivity_mul_quadratic
    (z : D4BMUpperHalfPlaneCoordinate) (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    (1 + |(p.1 : ℝ)|) * (1 + |(p.2 : ℝ)|) ≤
      d4BMPoincareCoercivityConstant z * d4BMPoincareQuadratic z p := by
  have hprod := d4BM_product_one_add_abs_le_four_sq_add_sq p hp
  have hscale := d4BM_scaled_lattice_sq_le_quadratic z p
  have hy2 : 0 < z.y ^ 2 := sq_pos_of_pos z.y_pos
  rw [d4BMPoincareCoercivityConstant, div_mul_eq_mul_div]
  apply (le_div_iff₀ hy2).2
  calc
    (1 + |(p.1 : ℝ)|) * (1 + |(p.2 : ℝ)|) * z.y ^ 2 =
        z.y ^ 2 * ((1 + |(p.1 : ℝ)|) * (1 + |(p.2 : ℝ)|)) := by ring
    _ ≤ z.y ^ 2 * (4 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = 4 * (z.y ^ 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by ring
    _ ≤ 4 * ((2 * z.y ^ 2 + 1 + 2 * z.x ^ 2) * d4BMPoincareQuadratic z p) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 4 * (2 * z.y ^ 2 + 1 + 2 * z.x ^ 2) * d4BMPoincareQuadratic z p := by ring

lemma d4BM_quadratic_rpow_neg_majorized
    (z : D4BMUpperHalfPlaneCoordinate) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    d4BMPoincareQuadratic z p ^ (-sigma) ≤
      d4BMPoincareCoercivityConstant z ^ sigma *
        ((1 + |(p.1 : ℝ)|) ^ (-sigma) * (1 + |(p.2 : ℝ)|) ^ (-sigma)) := by
  let P : ℝ := (1 + |(p.1 : ℝ)|) * (1 + |(p.2 : ℝ)|)
  let D : ℝ := d4BMPoincareCoercivityConstant z
  let Q : ℝ := d4BMPoincareQuadratic z p
  have hP : 0 < P := by dsimp [P]; positivity
  have hD : 0 < D := d4BMPoincareCoercivityConstant_pos z
  have hQ : 0 < Q := d4BMPoincareQuadratic_pos z p hp
  have hPDQ : P ≤ D * Q := d4BM_lattice_product_le_coercivity_mul_quadratic z p hp
  have hanti : (D * Q) ^ (-sigma) ≤ P ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hP hPDQ (by linarith)
  have hfactor : D ^ sigma * (D * Q) ^ (-sigma) = Q ^ (-sigma) := by
    rw [Real.mul_rpow hD.le hQ.le, Real.rpow_neg hD.le,
      Real.rpow_neg hQ.le]
    have hDr : D ^ sigma ≠ 0 := (Real.rpow_pos_of_pos hD sigma).ne'
    have hQr : Q ^ sigma ≠ 0 := (Real.rpow_pos_of_pos hQ sigma).ne'
    field_simp
  change Q ^ (-sigma) ≤ D ^ sigma *
    ((1 + |(p.1 : ℝ)|) ^ (-sigma) * (1 + |(p.2 : ℝ)|) ^ (-sigma))
  calc
    Q ^ (-sigma) = D ^ sigma * (D * Q) ^ (-sigma) := hfactor.symm
    _ ≤ D ^ sigma * P ^ (-sigma) :=
      mul_le_mul_of_nonneg_left hanti (Real.rpow_nonneg hD.le _)
    _ = D ^ sigma *
        ((1 + |(p.1 : ℝ)|) ^ (-sigma) * (1 + |(p.2 : ℝ)|) ^ (-sigma)) := by
      rw [show P = (1 + |(p.1 : ℝ)|) * (1 + |(p.2 : ℝ)|) by rfl,
        Real.mul_rpow (by positivity) (by positivity)]

theorem summable_d4BMPoincareQuadratic_cpow_norm
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : {p : ℤ × ℤ // p ≠ (0, 0)} =>
      d4BMPoincareQuadratic z p.1 ^ (-P.s.re) := by
  have hsigma : 0 ≤ P.s.re := by linarith [P.re_gt_one]
  have hbase := summable_int_one_add_abs_rpow P.re_gt_one
  have hprod : Summable fun p : ℤ × ℤ =>
      (1 + |(p.1 : ℝ)|) ^ (-P.s.re) * (1 + |(p.2 : ℝ)|) ^ (-P.s.re) :=
    Summable.mul_of_nonneg hbase hbase (fun _ => by positivity) (fun _ => by positivity)
  have hmaj := hprod.mul_left (d4BMPoincareCoercivityConstant z ^ P.s.re)
  refine Summable.of_nonneg_of_le
    (fun p => Real.rpow_nonneg (d4BMPoincareQuadratic_pos z p.1 p.2).le _) ?_
    (hmaj.subtype fun p : ℤ × ℤ => p ≠ (0, 0))
  intro p
  exact d4BM_quadratic_rpow_neg_majorized z P.s.re hsigma p.1 p.2

structure D4BMPrimitiveIntegerPair where
  pair : ℤ × ℤ
  primitive : Int.gcd pair.1 pair.2 = 1

lemma D4BMPrimitiveIntegerPair.pair_ne_zero (p : D4BMPrimitiveIntegerPair) :
    p.pair ≠ (0, 0) := by
  intro hp
  have hc : p.pair.1 = 0 := congrArg Prod.fst hp
  have hd : p.pair.2 = 0 := congrArg Prod.snd hp
  have hprim := p.primitive
  simp [hc, hd] at hprim

def D4BMPrimitiveIntegerPair.toNonzeroPair (p : D4BMPrimitiveIntegerPair) :
    {p : ℤ × ℤ // p ≠ (0, 0)} :=
  ⟨p.pair, p.pair_ne_zero⟩

lemma D4BMPrimitiveIntegerPair.toNonzeroPair_injective :
    Function.Injective D4BMPrimitiveIntegerPair.toNonzeroPair := by
  intro p q hpq
  cases p
  cases q
  simp only [toNonzeroPair, Subtype.mk.injEq] at hpq
  simp_all

theorem summable_d4BMPrimitivePoincareQuadratic_rpow_neg
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareQuadratic z p.pair ^ (-P.s.re) := by
  have h := (summable_d4BMPoincareQuadratic_cpow_norm z P).comp_injective
    D4BMPrimitiveIntegerPair.toNonzeroPair_injective
  simpa [Function.comp_def, D4BMPrimitiveIntegerPair.toNonzeroPair] using h

def d4BMPoincareSeed
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (p : D4BMPrimitiveIntegerPair) : ℂ :=
  ((z.y / d4BMPoincareQuadratic z p.pair : ℝ) : ℂ) ^ s

theorem norm_d4BMPoincareSeed
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeed z s p‖ =
      z.y ^ s.re * d4BMPoincareQuadratic z p.pair ^ (-s.re) := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  rw [d4BMPoincareSeed,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos z.y_pos hQ)]
  rw [Real.div_rpow z.y_pos.le hQ.le, Real.rpow_neg hQ.le]
  simp only [div_eq_mul_inv]

theorem summable_d4BMPoincareSeed
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair => d4BMPoincareSeed z P.s p := by
  have hreal := (summable_d4BMPrimitivePoincareQuadratic_rpow_neg z P).mul_left
    (z.y ^ P.s.re)
  refine Summable.of_norm_bounded hreal fun p => ?_
  exact (norm_d4BMPoincareSeed z P.s p).le

def d4BMRawEisensteinPoincareSeries
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair, d4BMPoincareSeed z P.s p

def d4BMCompletedEisensteinPoincareSeries
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawEisensteinPoincareSeries z P

theorem d4BM_completedEisensteinPoincareSeries_absoluteConvergence
    (z : D4BMUpperHalfPlaneCoordinate) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      reflectedCompletedLambda (2 * P.s) * (1 / 2 : ℂ) * d4BMPoincareSeed z P.s p := by
  exact (summable_d4BMPoincareSeed z P).mul_left _

theorem D4BMPrimitiveIntegerPair.firstRow_classification
    (p : D4BMPrimitiveIntegerPair) (hp : p.pair.1 = 0) :
    p.pair.2 = 1 ∨ p.pair.2 = -1 := by
  have hnat : p.pair.2.natAbs = 1 := by
    simpa [hp] using p.primitive
  simpa using (Int.natAbs_eq_iff.mp hnat)

theorem d4BMPoincareSeed_firstRow
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (p : D4BMPrimitiveIntegerPair)
    (hp : p.pair.1 = 0) :
    d4BMPoincareSeed z s p = (z.y : ℂ) ^ s := by
  rcases p.firstRow_classification hp with hd | hd
  · simp [d4BMPoincareSeed, d4BMPoincareQuadratic, hp, hd]
  · simp [d4BMPoincareSeed, d4BMPoincareQuadratic, hp, hd]

abbrev D4BMPrimitiveFirstRowPair :=
  {p : D4BMPrimitiveIntegerPair // p.pair.1 = 0}

def d4BMPrimitiveFirstRowPairOfBool (epsilon : Bool) : D4BMPrimitiveFirstRowPair := by
  refine ⟨⟨(0, if epsilon then 1 else -1), ?_⟩, rfl⟩
  cases epsilon <;> norm_num

lemma d4BMPrimitiveFirstRowPairOfBool_bijective :
    Function.Bijective d4BMPrimitiveFirstRowPairOfBool := by
  constructor
  · intro epsilon delta h
    cases epsilon <;> cases delta <;>
      simp_all [d4BMPrimitiveFirstRowPairOfBool]
  · intro p
    rcases p with ⟨⟨⟨c, d⟩, hprim⟩, hc⟩
    simp only at hc
    subst c
    have hnat : d.natAbs = 1 := by simpa using hprim
    rcases Int.natAbs_eq_iff.mp hnat with hd | hd
    · subst d
      refine ⟨true, ?_⟩
      rfl
    · subst d
      refine ⟨false, ?_⟩
      rfl

def d4BMPrimitiveFirstRowEquiv : Bool ≃ D4BMPrimitiveFirstRowPair :=
  Equiv.ofBijective d4BMPrimitiveFirstRowPairOfBool
    d4BMPrimitiveFirstRowPairOfBool_bijective

theorem tsum_d4BMPoincareSeed_firstRow
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) :
    (∑' p : D4BMPrimitiveFirstRowPair, d4BMPoincareSeed z s p.1) =
      2 * (z.y : ℂ) ^ s := by
  rw [← (d4BMPrimitiveFirstRowEquiv.tsum_eq
    (fun p : D4BMPrimitiveFirstRowPair => d4BMPoincareSeed z s p.1))]
  simp [d4BMPrimitiveFirstRowEquiv, d4BMPrimitiveFirstRowPairOfBool,
    d4BMPoincareSeed_firstRow]

end
end RHTower
