import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# Parikh--Wilczek finite-polynomial grade darkness

The literal Schwarzschild Parikh--Wilczek Borel holonomy is quadratic in grade. For every
polynomial degree bound `d`, its order-`2d+1` alternating binomial packet therefore annihilates
every degree-`d` polynomial readout, uniformly in spectral parameter. The packet's outer product
is an explicit nonzero, symmetric, finite-support kernel whose every finite principal section is
positive semidefinite. It kills separable polynomial energies and, more strongly, every bivariate
polynomial reporter with outer-variable degree at most `d`.

The order is sharp: order `2d` applied to the degree-`d` monomial reports exactly
`(2d)! * (4 * wall)^d`; at the explicit open-strip point `1/4 + I` this is nonzero. Hence no fixed
finite polynomial nonlinearity recovers literal PW grade observability. Any surviving PW-B route
requires unbounded/nonpolynomial grade resolution or an independent dynamical channel.

`[NEW] [SHARP CLASSIFICATION] [FINITE-POLYNOMIAL DARK SECTOR] [NO-GO] [PAPER-PROVED]
[LEAN-PROVED]`
-/


open Complex Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The exact quadratic polynomial carrying the PW grade shift `4k(k+1)`. -/
def schwarzschildParikhWilczekBorelGradePolynomial : ℝ[X] :=
  C 4 * X * (X + C 1)

/-- Evaluating the grade polynomial at a natural grade recovers the literal PW shift. -/
theorem schwarzschildParikhWilczekBorelGradePolynomial_eval (k : ℕ) :
    schwarzschildParikhWilczekBorelGradePolynomial.eval (k : ℝ) =
      schwarzschildParikhWilczekBorelGradeShift k := by
  simp [schwarzschildParikhWilczekBorelGradePolynomial,
    schwarzschildParikhWilczekBorelGradeShift]

/-- The PW grade shift has polynomial degree at most two. -/
theorem schwarzschildParikhWilczekBorelGradePolynomial_natDegree_le :
    schwarzschildParikhWilczekBorelGradePolynomial.natDegree ≤ 2 := by
  unfold schwarzschildParikhWilczekBorelGradePolynomial
  refine natDegree_mul_le.trans ?_
  have hleft : (C (4 : ℝ) * X).natDegree ≤ 1 :=
    natDegree_mul_le.trans (by simp)
  have hright : (X + C (1 : ℝ)).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp)
  omega

/-- Polynomial in grade whose values are imaginary PW Borel holonomies at fixed `s`. -/
def schwarzschildParikhWilczekBorelHolonomyGradePolynomial (s : ℂ) : ℝ[X] :=
  C (schwarzschildParikhWilczekBorelWallFactor s) *
    (C (schwarzschildParikhWilczekBorelSpectralCoordinate s) +
      schwarzschildParikhWilczekBorelGradePolynomial)

/-- The polynomial model agrees exactly with the literal imaginary recoil holonomy. -/
theorem schwarzschildParikhWilczekBorelHolonomyGradePolynomial_eval
    (s : ℂ) (k : ℕ) :
    (schwarzschildParikhWilczekBorelHolonomyGradePolynomial s).eval (k : ℝ) =
      (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im := by
  rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization,
    schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift]
  simp [schwarzschildParikhWilczekBorelHolonomyGradePolynomial,
    schwarzschildParikhWilczekBorelGradePolynomial_eval]

/-- Every fixed-spectral-parameter PW holonomy profile has grade degree at most two. -/
theorem schwarzschildParikhWilczekBorelHolonomyGradePolynomial_natDegree_le
    (s : ℂ) :
    (schwarzschildParikhWilczekBorelHolonomyGradePolynomial s).natDegree ≤ 2 := by
  unfold schwarzschildParikhWilczekBorelHolonomyGradePolynomial
  refine natDegree_mul_le.trans ?_
  have hleft :
      (C (schwarzschildParikhWilczekBorelWallFactor s)).natDegree ≤ 0 := by
    simp
  have hright :
      (C (schwarzschildParikhWilczekBorelSpectralCoordinate s) +
          schwarzschildParikhWilczekBorelGradePolynomial).natDegree ≤ 2 :=
    (natDegree_add_le _ _).trans
      (max_le (by simp) schwarzschildParikhWilczekBorelGradePolynomial_natDegree_le)
  omega

/-- First finite-difference order strictly above the composed degree bound `2d`. -/
def schwarzschildParikhWilczekPolynomialGradeDarkOrder (d : ℕ) : ℕ :=
  2 * d + 1

/-- Alternating binomial weight of order `2d+1`, extended by zero beyond its support. -/
def schwarzschildParikhWilczekPolynomialGradeDarkWeight (d k : ℕ) : ℝ :=
  let n := schwarzschildParikhWilczekPolynomialGradeDarkOrder d
  (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)

/-- Order `2d+1` annihilates every degree-`d` polynomial readout of literal PW holonomy. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkWeight_annihilates
    (d : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ d) (s : ℂ) :
    ∑ k ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
      schwarzschildParikhWilczekPolynomialGradeDarkWeight d k *
        P.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im = 0 := by
  let n := schwarzschildParikhWilczekPolynomialGradeDarkOrder d
  let Q := P.comp (schwarzschildParikhWilczekBorelHolonomyGradePolynomial s)
  have hQdeg : Q.natDegree < n := by
    dsimp only [Q]
    apply lt_of_le_of_lt Polynomial.natDegree_comp_le
    have hbase := schwarzschildParikhWilczekBorelHolonomyGradePolynomial_natDegree_le s
    have hmul : P.natDegree *
        (schwarzschildParikhWilczekBorelHolonomyGradePolynomial s).natDegree ≤ 2 * d := by
      nlinarith
    exact hmul.trans_lt (by dsimp only [n, schwarzschildParikhWilczekPolynomialGradeDarkOrder]; omega)
  have hz : (fwdDiff (1 : ℝ))^[n] Q.eval 0 = 0 := by
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQdeg]
    rfl
  rw [fwdDiff_iter_eq_sum_shift] at hz
  rw [show schwarzschildParikhWilczekPolynomialGradeDarkOrder d = n by rfl]
  rw [← hz]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zsmul_eq_mul]
  simp only [zero_add, nsmul_eq_mul, mul_one, Q, Polynomial.eval_comp]
  rw [schwarzschildParikhWilczekBorelHolonomyGradePolynomial_eval]
  simp [schwarzschildParikhWilczekPolynomialGradeDarkWeight, n]

/-- Top supported dark weight is exactly one. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkWeight_endpoint (d : ℕ) :
    schwarzschildParikhWilczekPolynomialGradeDarkWeight d
      (schwarzschildParikhWilczekPolynomialGradeDarkOrder d) = 1 := by
  simp [schwarzschildParikhWilczekPolynomialGradeDarkWeight]

/-- Dark weight vanishes strictly beyond its finite-difference order. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkWeight_eq_zero_of_order_lt
    (d k : ℕ) (hk : schwarzschildParikhWilczekPolynomialGradeDarkOrder d < k) :
    schwarzschildParikhWilczekPolynomialGradeDarkWeight d k = 0 := by
  simp [schwarzschildParikhWilczekPolynomialGradeDarkWeight,
    Nat.choose_eq_zero_of_lt hk]

/-- Rank-one outer-product kernel generated by the polynomial dark packet. -/
def schwarzschildParikhWilczekPolynomialGradeDarkMatrix (d i j : ℕ) : ℝ :=
  schwarzschildParikhWilczekPolynomialGradeDarkWeight d i *
    schwarzschildParikhWilczekPolynomialGradeDarkWeight d j

/-- Polynomial dark kernel is symmetric. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkMatrix_symmetric
    (d i j : ℕ) :
    schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j =
      schwarzschildParikhWilczekPolynomialGradeDarkMatrix d j i := by
  simp [schwarzschildParikhWilczekPolynomialGradeDarkMatrix, mul_comm]

/-- Top diagonal entry of the polynomial dark kernel is exactly one. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkMatrix_endpoint (d : ℕ) :
    schwarzschildParikhWilczekPolynomialGradeDarkMatrix d
      (schwarzschildParikhWilczekPolynomialGradeDarkOrder d)
      (schwarzschildParikhWilczekPolynomialGradeDarkOrder d) = 1 := by
  simp [schwarzschildParikhWilczekPolynomialGradeDarkMatrix,
    schwarzschildParikhWilczekPolynomialGradeDarkWeight_endpoint]

/-- Polynomial dark kernel is nonzero at every reporter degree. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkMatrix_ne_zero (d : ℕ) :
    schwarzschildParikhWilczekPolynomialGradeDarkMatrix d ≠ 0 := by
  intro h
  have hend := congrFun (congrFun h
    (schwarzschildParikhWilczekPolynomialGradeDarkOrder d))
      (schwarzschildParikhWilczekPolynomialGradeDarkOrder d)
  rw [schwarzschildParikhWilczekPolynomialGradeDarkMatrix_endpoint] at hend
  norm_num at hend

/-- Kernel vanishes once either grade lies beyond `2d+1`. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkMatrix_finiteSupport
    (d i j : ℕ)
    (hij : schwarzschildParikhWilczekPolynomialGradeDarkOrder d < i ∨
      schwarzschildParikhWilczekPolynomialGradeDarkOrder d < j) :
    schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j = 0 := by
  rcases hij with hi | hj
  · simp [schwarzschildParikhWilczekPolynomialGradeDarkMatrix,
      schwarzschildParikhWilczekPolynomialGradeDarkWeight_eq_zero_of_order_lt d i hi]
  · simp [schwarzschildParikhWilczekPolynomialGradeDarkMatrix,
      schwarzschildParikhWilczekPolynomialGradeDarkWeight_eq_zero_of_order_lt d j hj]

/-- Every finite principal section is positive semidefinite because its quadratic form is a square. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkMatrix_finiteQuadraticForm_nonneg
    (d : ℕ) {N : ℕ} (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      v i * schwarzschildParikhWilczekPolynomialGradeDarkMatrix d (i : ℕ) (j : ℕ) * v j := by
  rw [show (∑ i : Fin N, ∑ j : Fin N,
      v i * schwarzschildParikhWilczekPolynomialGradeDarkMatrix d (i : ℕ) (j : ℕ) * v j) =
      (∑ i, v i * schwarzschildParikhWilczekPolynomialGradeDarkWeight d (i : ℕ)) ^ (2 : ℕ) by
        simpa only [schwarzschildParikhWilczekPolynomialGradeDarkMatrix] using
          finite_rankOneQuadraticForm_eq_sq
            (fun i : Fin N =>
              schwarzschildParikhWilczekPolynomialGradeDarkWeight d (i : ℕ)) v]
  positivity

/-- Pairing of the dark kernel with two univariate polynomial PW reporters. -/
def schwarzschildParikhWilczekPolynomialCrossGradeEnergy
    (d : ℕ) (P Q : ℝ[X]) (s : ℂ) : ℝ :=
  ∑ i ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
    ∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
      schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j *
        P.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im *
          Q.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im

/-- Every separable degree-bounded polynomial cross-grade energy is exactly dark. -/
theorem schwarzschildParikhWilczekPolynomialCrossGradeEnergy_zero
    (d : ℕ) (P Q : ℝ[X]) (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (s : ℂ) :
    schwarzschildParikhWilczekPolynomialCrossGradeEnergy d P Q s = 0 := by
  have hleft :=
    schwarzschildParikhWilczekPolynomialGradeDarkWeight_annihilates d P hP s
  have hright :=
    schwarzschildParikhWilczekPolynomialGradeDarkWeight_annihilates d Q hQ s
  rw [schwarzschildParikhWilczekPolynomialCrossGradeEnergy]
  calc
    (∑ i ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
      ∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
        schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j *
          P.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im *
            Q.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im) =
      (∑ i ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
        schwarzschildParikhWilczekPolynomialGradeDarkWeight d i *
          P.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im) *
      (∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
        schwarzschildParikhWilczekPolynomialGradeDarkWeight d j *
          Q.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp [schwarzschildParikhWilczekPolynomialGradeDarkMatrix]
        ring
    _ = 0 := by rw [hleft, hright]; norm_num

/-- Dark-kernel pairing with a nested bivariate polynomial evaluated on two PW grades. -/
def schwarzschildParikhWilczekBivariatePolynomialCrossGradeEnergy
    (d : ℕ) (B : Polynomial (Polynomial ℝ)) (s : ℂ) : ℝ :=
  ∑ i ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
    ∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
      schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j *
        B.eval₂
          (Polynomial.evalRingHom
            (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im)
          (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im

/-- Every bivariate reporter of outer-variable degree at most `d` is exactly dark. -/
theorem schwarzschildParikhWilczekBivariatePolynomialCrossGradeEnergy_zero
    (d : ℕ) (B : Polynomial (Polynomial ℝ)) (hB : B.natDegree ≤ d)
    (s : ℂ) :
    schwarzschildParikhWilczekBivariatePolynomialCrossGradeEnergy d B s = 0 := by
  rw [schwarzschildParikhWilczekBivariatePolynomialCrossGradeEnergy]
  apply Finset.sum_eq_zero
  intro i hi
  let Pi : ℝ[X] := B.map
    (Polynomial.evalRingHom
      (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im)
  have hPi : Pi.natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hB
  have hz :=
    schwarzschildParikhWilczekPolynomialGradeDarkWeight_annihilates d Pi hPi s
  calc
    ∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
        schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j *
          B.eval₂
            (Polynomial.evalRingHom
              (schwarzschildParikhWilczekBorelRecoilHolonomy s i).im)
            (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im =
      schwarzschildParikhWilczekPolynomialGradeDarkWeight d i *
        (∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
          schwarzschildParikhWilczekPolynomialGradeDarkWeight d j *
            Pi.eval (schwarzschildParikhWilczekBorelRecoilHolonomy s j).im) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              simp only [schwarzschildParikhWilczekPolynomialGradeDarkMatrix, Pi]
              rw [Polynomial.eval_map]
              ring
    _ = 0 := by rw [hz]; ring

/-- Exact top-coefficient extraction by an alternating binomial finite difference. -/
theorem alternatingBinomialWeightedPolynomialEval_eq_factorial_mul_coeff
    (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) * P.eval (k : ℝ) =
        (Nat.factorial n : ℝ) * P.coeff n := by
  by_cases hlt : P.natDegree < n
  · have hz : (fwdDiff (1 : ℝ))^[n] P.eval 0 = 0 := by
      rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt]
      rfl
    rw [fwdDiff_iter_eq_sum_shift] at hz
    calc
      (∑ k ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) * P.eval (k : ℝ)) =
        ∑ k ∈ Finset.range (n + 1),
          ((-1) ^ (n - k) * ↑(n.choose k)) • P.eval (0 + k • (1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [zsmul_eq_mul]
            push_cast
            ring_nf
      _ = 0 := hz
      _ = (Nat.factorial n : ℝ) * P.coeff n := by
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
        ring
  · have heq : P.natDegree = n := Nat.le_antisymm hP (Nat.le_of_not_gt hlt)
    have htop := congrFun P.fwdDiff_iter_degree_eq_factorial 0
    rw [heq, fwdDiff_iter_eq_sum_shift] at htop
    calc
      (∑ k ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) * P.eval (k : ℝ)) =
        ∑ k ∈ Finset.range (n + 1),
          ((-1) ^ (n - k) * ↑(n.choose k)) • P.eval (0 + k • (1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [zsmul_eq_mul]
            push_cast
            ring_nf
      _ = P.leadingCoeff * (Nat.factorial n : ℝ) := htop
      _ = (Nat.factorial n : ℝ) * P.coeff n := by
        have hlc : P.leadingCoeff = P.coeff n := by
          rw [Polynomial.leadingCoeff, heq]
        rw [hlc]
        ring

/-- Quadratic coefficient of the PW holonomy profile is exactly four times the wall factor. -/
theorem schwarzschildParikhWilczekBorelHolonomyGradePolynomial_coeff_two
    (s : ℂ) :
    (schwarzschildParikhWilczekBorelHolonomyGradePolynomial s).coeff 2 =
      4 * schwarzschildParikhWilczekBorelWallFactor s := by
  unfold schwarzschildParikhWilczekBorelHolonomyGradePolynomial
  rw [Polynomial.coeff_C_mul]
  have hgrade : schwarzschildParikhWilczekBorelGradePolynomial =
      C (4 : ℝ) * X ^ (2 : ℕ) + C 4 * X := by
    unfold schwarzschildParikhWilczekBorelGradePolynomial
    simp
    ring_nf
  rw [hgrade]
  simp
  ring

/-- Order `2d` retains the degree-`d` monomial as `(2d)! * (4 * wall)^d`. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkOrder_sharp
    (d : ℕ) (s : ℂ) :
    ∑ k ∈ Finset.range (2 * d + 1),
      ((-1 : ℝ) ^ (2 * d - k) * ((2 * d).choose k : ℝ)) *
        (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im ^ d =
      (Nat.factorial (2 * d) : ℝ) *
        (4 * schwarzschildParikhWilczekBorelWallFactor s) ^ d := by
  let H := schwarzschildParikhWilczekBorelHolonomyGradePolynomial s
  have hH : H.natDegree ≤ 2 :=
    schwarzschildParikhWilczekBorelHolonomyGradePolynomial_natDegree_le s
  have hpow : (H ^ d).natDegree ≤ 2 * d := by
    calc
      (H ^ d).natDegree ≤ d * H.natDegree := Polynomial.natDegree_pow_le
      _ ≤ d * 2 := Nat.mul_le_mul_left d hH
      _ = 2 * d := by omega
  calc
    (∑ k ∈ Finset.range (2 * d + 1),
        ((-1 : ℝ) ^ (2 * d - k) * ((2 * d).choose k : ℝ)) *
          (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im ^ d) =
      ∑ k ∈ Finset.range (2 * d + 1),
        ((-1 : ℝ) ^ (2 * d - k) * ((2 * d).choose k : ℝ)) *
          (H ^ d).eval (k : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Polynomial.eval_pow,
              schwarzschildParikhWilczekBorelHolonomyGradePolynomial_eval]
    _ = (Nat.factorial (2 * d) : ℝ) * (H ^ d).coeff (2 * d) :=
      alternatingBinomialWeightedPolynomialEval_eq_factorial_mul_coeff
        (2 * d) (H ^ d) hpow
    _ = (Nat.factorial (2 * d) : ℝ) *
        (4 * schwarzschildParikhWilczekBorelWallFactor s) ^ d := by
      rw [show 2 * d = d * 2 by omega,
        Polynomial.coeff_pow_of_natDegree_le hH,
        schwarzschildParikhWilczekBorelHolonomyGradePolynomial_coeff_two]

/-- Explicit open-critical-strip spectral point with unit PW wall factor. -/
def schwarzschildParikhWilczekPolynomialGradeSharpSpectralPoint : ℂ :=
  (1 / 4 : ℂ) + Complex.I

/-- The sharpness point `1/4 + I` has wall factor one. -/
theorem schwarzschildParikhWilczekPolynomialGradeSharpSpectralPoint_wall :
    schwarzschildParikhWilczekBorelWallFactor
      schwarzschildParikhWilczekPolynomialGradeSharpSpectralPoint = 1 := by
  norm_num [schwarzschildParikhWilczekBorelWallFactor,
    schwarzschildParikhWilczekPolynomialGradeSharpSpectralPoint]

/-- Order `2d` is not universally dark: a degree-`d` monomial survives at `1/4 + I`. -/
theorem schwarzschildParikhWilczekPolynomialGradeDarkOrder_minimal_witness
    (d : ℕ) :
    ∑ k ∈ Finset.range (2 * d + 1),
      ((-1 : ℝ) ^ (2 * d - k) * ((2 * d).choose k : ℝ)) *
        (schwarzschildParikhWilczekBorelRecoilHolonomy
          schwarzschildParikhWilczekPolynomialGradeSharpSpectralPoint k).im ^ d ≠ 0 := by
  rw [schwarzschildParikhWilczekPolynomialGradeDarkOrder_sharp,
    schwarzschildParikhWilczekPolynomialGradeSharpSpectralPoint_wall]
  positivity

end

end RHTower
