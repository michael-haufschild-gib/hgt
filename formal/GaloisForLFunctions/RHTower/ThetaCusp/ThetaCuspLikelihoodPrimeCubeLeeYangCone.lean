import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodPrimeSquareSignWall
import GaloisForLFunctions.HTGeometry.LeeYangTwoSpinCircle
import GaloisForLFunctions.HTGeometry.UnitCircleRootRadialOrientation

/-!
# Prime-cube Lee--Yang cone for theta-likelihood shells

A positive symmetric four-band packet at rapidities `±L/2, ±3L/2` has strict negative
upper-half-plane current exactly when its inner coefficient is at most three times its endpoint
coefficient.  Sufficiency is the unit-circle-root orientation of
`1 + rX + rX² + X³`; necessity is an explicit positive-current witness on `Re z = π/L`.

The actual theta-likelihood `p³` boundary packet exits this sharp cone for all sufficiently small
positive boundary coordinates.  Its four rapidities are all nonzero.  Thus zero-rapidity diagonal
subtraction, which repairs the prime-square wall, cannot be the general composite correction.

All statements are exact and unconditional.  No estimate, computation, or RH hypothesis is used.
-/

open Complex Real Finset Polynomial Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem thetaPositiveFactorPairs_prime_cube {p : ℕ} (hp : p.Prime) :
    thetaPositiveFactorPairs (p ^ (3 : ℕ)) =
      {(0, p ^ (3 : ℕ) - 1), (p - 1, p ^ (2 : ℕ) - 1),
        (p ^ (2 : ℕ) - 1, p - 1), (p ^ (3 : ℕ) - 1, 0)} := by
  ext q
  constructor
  · intro hq
    have hprod : (q.1 + 1) * (q.2 + 1) = p ^ (3 : ℕ) :=
      (Finset.mem_filter.mp hq).2
    have hdvd : q.1 + 1 ∣ p ^ (3 : ℕ) := ⟨q.2 + 1, hprod.symm⟩
    obtain ⟨i, hi, hqi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases q with ⟨m, n⟩
    simp only at hprod hqi
    interval_cases i
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [pow_zero] at hqi
      left
      have hn : n + 1 = p ^ (3 : ℕ) := by simpa [hqi] using hprod
      apply Prod.ext <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [pow_one] at hqi
      right
      left
      have hn : n + 1 = p ^ (2 : ℕ) := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        calc
          p * (n + 1) = p ^ (3 : ℕ) := by simpa [hqi] using hprod
          _ = p * p ^ (2 : ℕ) := by ring
      apply Prod.ext <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      right
      left
      have hn : n + 1 = p := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
        calc
          p ^ (2 : ℕ) * (n + 1) = p ^ (3 : ℕ) := by simpa [hqi] using hprod
          _ = p ^ (2 : ℕ) * p := by ring
      apply Prod.ext <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      right
      right
      have hn : n + 1 = 1 := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 3)
        simpa [hqi] using hprod
      apply Prod.ext <;> omega
  · intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have hp0 : 0 < p ^ (3 : ℕ) := pow_pos hp.pos 3
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> omega
      · omega

    · have hpp : p < p ^ (2 : ℕ) := by
        calc
          p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
          _ = p ^ (2 : ℕ) := by ring
      have hp2p3 : p ^ (2 : ℕ) < p ^ (3 : ℕ) := by
        calc
          p ^ (2 : ℕ) < p ^ (2 : ℕ) * p :=
            lt_mul_of_one_lt_right (pow_pos hp.pos 2) hp.one_lt
          _ = p ^ (3 : ℕ) := by ring
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> omega
      · rw [Nat.sub_add_cancel hp.pos,
          Nat.sub_add_cancel (pow_pos hp.pos 2)]
        ring
    · have hpp : p < p ^ (2 : ℕ) := by
        calc
          p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
          _ = p ^ (2 : ℕ) := by ring
      have hp2p3 : p ^ (2 : ℕ) < p ^ (3 : ℕ) := by
        calc
          p ^ (2 : ℕ) < p ^ (2 : ℕ) * p :=
            lt_mul_of_one_lt_right (pow_pos hp.pos 2) hp.one_lt
          _ = p ^ (3 : ℕ) := by ring
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> omega
      · rw [Nat.sub_add_cancel (pow_pos hp.pos 2),
          Nat.sub_add_cancel hp.pos]
        ring
    · have hp0 : 0 < p ^ (3 : ℕ) := pow_pos hp.pos 3
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> omega
      · omega

theorem thetaFactorPairLogDisplacement_primeCube_left {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (0, p ^ (3 : ℕ) - 1) = -3 * Real.log p / 2 := by
  unfold thetaFactorPairLogDisplacement
  simp only [Nat.zero_add, Nat.cast_one, Real.log_one, zero_sub, neg_div]
  rw [Nat.sub_add_cancel (pow_pos hp.pos 3), Nat.cast_pow, Real.log_pow]
  norm_num
  ring

theorem thetaFactorPairLogDisplacement_primeCube_innerLeft {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (p - 1, p ^ (2 : ℕ) - 1) = -Real.log p / 2 := by
  unfold thetaFactorPairLogDisplacement
  rw [Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel (pow_pos hp.pos 2),
    Nat.cast_pow, Real.log_pow]
  norm_num
  ring

theorem thetaFactorPairLogDisplacement_primeCube_innerRight {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (p ^ (2 : ℕ) - 1, p - 1) = Real.log p / 2 := by
  unfold thetaFactorPairLogDisplacement
  rw [Nat.sub_add_cancel (pow_pos hp.pos 2), Nat.sub_add_cancel hp.pos,
    Nat.cast_pow, Real.log_pow]
  norm_num
  ring

theorem thetaFactorPairLogDisplacement_primeCube_right {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (p ^ (3 : ℕ) - 1, 0) = 3 * Real.log p / 2 := by
  unfold thetaFactorPairLogDisplacement
  simp only [Nat.zero_add, Nat.cast_one, Real.log_one, sub_zero]
  rw [Nat.sub_add_cancel (pow_pos hp.pos 3), Nat.cast_pow, Real.log_pow]
  norm_num

def primeCubeCoefficientPolynomial (r : ℝ) : Polynomial ℂ :=
  C 1 * X ^ (3 : ℕ) + C (r : ℂ) * X ^ (2 : ℕ) + C (r : ℂ) * X + C 1

theorem primeCubeCoefficientPolynomial_natDegree (r : ℝ) :
    (primeCubeCoefficientPolynomial r).natDegree = 3 := by
  simpa [primeCubeCoefficientPolynomial] using
    (Polynomial.natDegree_cubic (R := ℂ) (a := (1 : ℂ))
      (b := (r : ℂ)) (c := (r : ℂ)) (d := (1 : ℂ)) one_ne_zero)

theorem primeCubeCoefficientPolynomial_ne_zero (r : ℝ) :
    primeCubeCoefficientPolynomial r ≠ 0 := by
  intro h
  have hdeg := primeCubeCoefficientPolynomial_natDegree r
  rw [h] at hdeg
  norm_num at hdeg

theorem primeCubeCoefficientPolynomial_eval_factor (r : ℝ) (z : ℂ) :
    (primeCubeCoefficientPolynomial r).eval z =
      (z + 1) * (z ^ (2 : ℕ) + ((r - 1 : ℝ) : ℂ) * z + 1) := by
  simp [primeCubeCoefficientPolynomial]
  ring

theorem primeCubeCoefficientPolynomial_roots_unit
    {r : ℝ} (hr0 : 0 < r) (hr3 : r ≤ 3) :
    ∀ z ∈ (primeCubeCoefficientPolynomial r).roots, ‖z‖ = 1 := by
  intro z hz
  have hP := primeCubeCoefficientPolynomial_ne_zero r
  have hzero : (primeCubeCoefficientPolynomial r).eval z = 0 :=
    (Polynomial.mem_roots hP).mp hz
  rw [primeCubeCoefficientPolynomial_eval_factor] at hzero
  rcases mul_eq_zero.mp hzero with hleft | hquad
  · have hzneg : z = -1 := by linear_combination hleft
    rw [hzneg, norm_neg, norm_one]
  · let c : ℝ := (r - 1) / 2
    have hc : |c| ≤ 1 := by
      rw [abs_le]
      constructor <;> dsimp [c] <;> linarith
    apply GaloisForLFunctions.diagonal_zeros_on_circle hc
    have hcoef : (2 : ℂ) * (c : ℂ) = ((r - 1 : ℝ) : ℂ) := by
      dsimp [c]
      push_cast
      ring
    rw [hcoef]
    exact hquad

def primeCubeExponentialMode (omega : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (omega : ℂ) * z)

def primeCubeCoefficientPhase (L a b : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) *
      (primeCubeExponentialMode (-3 * L / 2) z +
        primeCubeExponentialMode (3 * L / 2) z) +
    (b : ℂ) *
      (primeCubeExponentialMode (-L / 2) z +
        primeCubeExponentialMode (L / 2) z)

def primeCubeCoefficientPhaseDerivative (L a b : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) *
      ((Complex.I * ((-3 * L / 2 : ℝ) : ℂ)) *
          primeCubeExponentialMode (-3 * L / 2) z +
        (Complex.I * ((3 * L / 2 : ℝ) : ℂ)) *
          primeCubeExponentialMode (3 * L / 2) z) +
    (b : ℂ) *
      ((Complex.I * ((-L / 2 : ℝ) : ℂ)) *
          primeCubeExponentialMode (-L / 2) z +
        (Complex.I * ((L / 2 : ℝ) : ℂ)) *
          primeCubeExponentialMode (L / 2) z)

def primeCubeCoefficientCurrent (L a b : ℝ) (z : ℂ) : ℝ :=
  (primeCubeCoefficientPhaseDerivative L a b z *
    (starRingEnd ℂ) (primeCubeCoefficientPhase L a b z)).im

theorem hasDerivAt_primeCubeExponentialMode (omega : ℝ) (z : ℂ) :
    HasDerivAt (primeCubeExponentialMode omega)
      ((Complex.I * (omega : ℂ)) * primeCubeExponentialMode omega z) z := by
  let c : ℂ := Complex.I * (omega : ℂ)
  have h := (Complex.hasDerivAt_exp (c * z)).comp z
      ((hasDerivAt_id z).const_mul c)
  have hval : Complex.exp (c * z) * (c * 1) = c * Complex.exp (c * z) := by
    ring
  rw [hval] at h
  exact h

theorem hasDerivAt_primeCubeCoefficientPhase (L a b : ℝ) (z : ℂ) :
    HasDerivAt (primeCubeCoefficientPhase L a b)
      (primeCubeCoefficientPhaseDerivative L a b z) z := by
  have hm3 := hasDerivAt_primeCubeExponentialMode (-3 * L / 2) z
  have hp3 := hasDerivAt_primeCubeExponentialMode (3 * L / 2) z
  have hm1 := hasDerivAt_primeCubeExponentialMode (-L / 2) z
  have hp1 := hasDerivAt_primeCubeExponentialMode (L / 2) z
  have h := ((hm3.add hp3).const_mul (a : ℂ)).add
    ((hm1.add hp1).const_mul (b : ℂ))
  exact h

theorem centeredUnitCirclePolynomialPhase_primeCubeCoefficientPolynomial
    (r L : ℝ) (z : ℂ) :
    centeredUnitCirclePolynomialPhase (primeCubeCoefficientPolynomial r) L z =
      primeCubeCoefficientPhase L 1 r z := by
  unfold centeredUnitCirclePolynomialPhase primeCubeCoefficientPhase
  rw [primeCubeCoefficientPolynomial_natDegree]
  simp only [primeCubeCoefficientPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, one_mul]
  let q : ℂ := Complex.exp (Complex.I * (L : ℂ) * z)
  let c : ℂ := Complex.exp
    (-Complex.I * (((3 : ℝ) * L / 2 : ℝ) : ℂ) * z)
  change c * (q ^ (3 : ℕ) + (r : ℂ) * q ^ (2 : ℕ) + (r : ℂ) * q + 1) = _
  have hterm (j : ℕ) :
      c * q ^ j =
        Complex.exp
          (Complex.I * (((j : ℝ) - 3 / 2) * L : ℂ) * z) := by
    dsimp [c, q]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_add, mul_add, mul_add, hterm 3,
    show c * 1 = c * q ^ (0 : ℕ) by simp, hterm 0]
  rw [show c * ((r : ℂ) * q ^ (2 : ℕ)) = (r : ℂ) * (c * q ^ (2 : ℕ)) by ring,
    show c * ((r : ℂ) * q) = (r : ℂ) * (c * q ^ (1 : ℕ)) by ring,
    hterm 2, hterm 1]
  have hm3 :
      Complex.exp (Complex.I * (((0 : ℝ) - 3 / 2) * L : ℂ) * z) =
        primeCubeExponentialMode (-3 * L / 2) z := by
    unfold primeCubeExponentialMode
    congr 1
    push_cast
    ring
  have hm1 :
      Complex.exp (Complex.I * (((1 : ℝ) - 3 / 2) * L : ℂ) * z) =
        primeCubeExponentialMode (-L / 2) z := by
    unfold primeCubeExponentialMode
    congr 1
    push_cast
    ring
  have hp1 :
      Complex.exp (Complex.I * (((2 : ℝ) - 3 / 2) * L : ℂ) * z) =
        primeCubeExponentialMode (L / 2) z := by
    unfold primeCubeExponentialMode
    congr 1
    push_cast
    ring
  have hp3 :
      Complex.exp (Complex.I * (((3 : ℝ) - 3 / 2) * L : ℂ) * z) =
        primeCubeExponentialMode (3 * L / 2) z := by
    unfold primeCubeExponentialMode
    congr 1
    push_cast
    ring
  norm_num at hm3 hm1 hp1 hp3 ⊢
  rw [hm3, hm1, hp1, hp3]
  ring

theorem primeCubeCoefficientPhase_eq_scale_centeredPolynomial
    {a : ℝ} (ha : a ≠ 0) (b L : ℝ) (z : ℂ) :
    primeCubeCoefficientPhase L a b z =
      (a : ℂ) * centeredUnitCirclePolynomialPhase
        (primeCubeCoefficientPolynomial (b / a)) L z := by
  rw [centeredUnitCirclePolynomialPhase_primeCubeCoefficientPolynomial]
  unfold primeCubeCoefficientPhase
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hba : (a : ℂ) * ((b / a : ℝ) : ℂ) = (b : ℂ) := by
    push_cast
    field_simp [hac]
  let O : ℂ := primeCubeExponentialMode (-3 * L / 2) z +
    primeCubeExponentialMode (3 * L / 2) z
  let J : ℂ := primeCubeExponentialMode (-L / 2) z +
    primeCubeExponentialMode (L / 2) z
  change (a : ℂ) * O + (b : ℂ) * J =
    (a : ℂ) * ((1 : ℂ) * O + ((b / a : ℝ) : ℂ) * J)
  rw [← hba]
  ring

theorem primeCubeCoefficientPhaseDerivative_eq_scale_centeredPolynomial
    {a : ℝ} (ha : a ≠ 0) (b L : ℝ) (z : ℂ) :
    primeCubeCoefficientPhaseDerivative L a b z =
      (a : ℂ) * centeredUnitCirclePolynomialPhaseDerivative
        (primeCubeCoefficientPolynomial (b / a)) L z := by
  have hleft := hasDerivAt_primeCubeCoefficientPhase L a b z
  have hright :=
    (hasDerivAt_centeredUnitCirclePolynomialPhase
      (primeCubeCoefficientPolynomial (b / a)) L z).const_mul (a : ℂ)
  have hfun : primeCubeCoefficientPhase L a b =
      fun u => (a : ℂ) * centeredUnitCirclePolynomialPhase
        (primeCubeCoefficientPolynomial (b / a)) L u := by
    funext u
    exact primeCubeCoefficientPhase_eq_scale_centeredPolynomial ha b L u
  rw [hfun] at hleft
  exact hleft.unique hright

theorem primeCubeCoefficientCurrent_eq_sq_mul_centeredPolynomial
    {a : ℝ} (ha : a ≠ 0) (b L : ℝ) (z : ℂ) :
    primeCubeCoefficientCurrent L a b z =
      a ^ (2 : ℕ) *
        (centeredUnitCirclePolynomialPhaseDerivative
            (primeCubeCoefficientPolynomial (b / a)) L z *
          (starRingEnd ℂ) (centeredUnitCirclePolynomialPhase
            (primeCubeCoefficientPolynomial (b / a)) L z)).im := by
  unfold primeCubeCoefficientCurrent
  rw [primeCubeCoefficientPhaseDerivative_eq_scale_centeredPolynomial ha,
    primeCubeCoefficientPhase_eq_scale_centeredPolynomial ha]
  simp only [map_mul, Complex.conj_ofReal]
  simp [Complex.mul_im]
  ring

theorem primeCubeCoefficientCurrent_lt_zero_of_le_three_mul
    {L a b : ℝ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 3 * a)
    {z : ℂ} (hz : 0 < z.im) :
    primeCubeCoefficientCurrent L a b z < 0 := by
  have hr0 : 0 < b / a := div_pos hb ha
  have hr3 : b / a ≤ 3 := (div_le_iff₀ ha).2 (by linarith)
  have hcenter := centeredUnitCirclePolynomialPhase_current_lt_zero
    (primeCubeCoefficientPolynomial (b / a))
    (primeCubeCoefficientPolynomial_ne_zero (b / a))
    (by rw [primeCubeCoefficientPolynomial_natDegree]; omega)
    (primeCubeCoefficientPolynomial_roots_unit hr0 hr3) hL hz
  rw [primeCubeCoefficientCurrent_eq_sq_mul_centeredPolynomial ha.ne' b L]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos ha) hcenter

theorem primeCubeCoefficientPhase_eq_cos (L a b : ℝ) (z : ℂ) :
    primeCubeCoefficientPhase L a b z =
      2 * (a : ℂ) * Complex.cos ((((3 * L / 2 : ℝ) : ℂ) * z)) +
        2 * (b : ℂ) * Complex.cos ((((L / 2 : ℝ) : ℂ) * z)) := by
  unfold primeCubeCoefficientPhase primeCubeExponentialMode
  have houter :
      Complex.exp (Complex.I * ((-3 * L / 2 : ℝ) : ℂ) * z) +
          Complex.exp (Complex.I * ((3 * L / 2 : ℝ) : ℂ) * z) =
        2 * Complex.cos ((((3 * L / 2 : ℝ) : ℂ) * z)) := by
    rw [Complex.two_cos]
    have hm :
        Complex.I * ((-3 * L / 2 : ℝ) : ℂ) * z =
          -((((3 * L / 2 : ℝ) : ℂ) * z) * Complex.I) := by
      push_cast
      ring
    have hp :
        Complex.I * ((3 * L / 2 : ℝ) : ℂ) * z =
          (((3 * L / 2 : ℝ) : ℂ) * z) * Complex.I := by ring
    rw [hm, hp]
    ring
  have hinner :
      Complex.exp (Complex.I * ((-L / 2 : ℝ) : ℂ) * z) +
          Complex.exp (Complex.I * ((L / 2 : ℝ) : ℂ) * z) =
        2 * Complex.cos ((((L / 2 : ℝ) : ℂ) * z)) := by
    rw [Complex.two_cos]
    have hm :
        Complex.I * ((-L / 2 : ℝ) : ℂ) * z =
          -((((L / 2 : ℝ) : ℂ) * z) * Complex.I) := by
      push_cast
      ring
    have hp :
        Complex.I * ((L / 2 : ℝ) : ℂ) * z =
          (((L / 2 : ℝ) : ℂ) * z) * Complex.I := by ring
    rw [hm, hp]
    ring
  rw [houter, hinner]
  ring

theorem primeCubeCoefficientPhaseDerivative_eq_sin (L a b : ℝ) (z : ℂ) :
    primeCubeCoefficientPhaseDerivative L a b z =
      -(3 * L * a : ℂ) * Complex.sin ((((3 * L / 2 : ℝ) : ℂ) * z)) -
        (L * b : ℂ) * Complex.sin ((((L / 2 : ℝ) : ℂ) * z)) := by
  have hfun : primeCubeCoefficientPhase L a b = fun u =>
      2 * (a : ℂ) * Complex.cos ((((3 * L / 2 : ℝ) : ℂ) * u)) +
        2 * (b : ℂ) * Complex.cos ((((L / 2 : ℝ) : ℂ) * u)) := by
    funext u
    exact primeCubeCoefficientPhase_eq_cos L a b u
  have hleft := hasDerivAt_primeCubeCoefficientPhase L a b z
  rw [hfun] at hleft
  have houter :=
    ((Complex.hasDerivAt_cos ((((3 * L / 2 : ℝ) : ℂ) * z))).comp z
      ((hasDerivAt_id z).const_mul (((3 * L / 2 : ℝ) : ℂ)))).const_mul
        (2 * (a : ℂ))
  have hinner :=
    ((Complex.hasDerivAt_cos ((((L / 2 : ℝ) : ℂ) * z))).comp z
      ((hasDerivAt_id z).const_mul (((L / 2 : ℝ) : ℂ)))).const_mul
        (2 * (b : ℂ))
  have hright := houter.add hinner
  have hu := hleft.unique hright
  convert hu using 1
  all_goals push_cast
  all_goals ring_nf

def primeCubeReflectionWallPoint (L y : ℝ) : ℂ :=
  (Real.pi / L : ℝ) + (y : ℂ) * Complex.I

theorem primeCubeCoefficientPhase_wall (L a b y : ℝ) (hL : L ≠ 0) :
    primeCubeCoefficientPhase L a b (primeCubeReflectionWallPoint L y) =
      2 * Complex.I *
        ((a * Real.sinh (3 * L * y / 2) - b * Real.sinh (L * y / 2) : ℝ) : ℂ) := by
  rw [primeCubeCoefficientPhase_eq_cos]
  have hinner :
      (((L / 2 : ℝ) : ℂ) * primeCubeReflectionWallPoint L y) =
        ((Real.pi / 2 : ℝ) : ℂ) + (((L * y / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold primeCubeReflectionWallPoint
    push_cast
    field_simp [hL]
  have houter :
      (((3 * L / 2 : ℝ) : ℂ) * primeCubeReflectionWallPoint L y) =
        ((3 * Real.pi / 2 : ℝ) : ℂ) +
          (((3 * L * y / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold primeCubeReflectionWallPoint
    push_cast
    field_simp [hL]
  have hthree :
      (((3 * Real.pi / 2 : ℝ) : ℂ)) =
        (Real.pi : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hinner, houter, Complex.cos_add_mul_I, Complex.cos_add_mul_I]
  rw [hthree, Complex.cos_add, Complex.sin_add]
  push_cast
  simp
  ring

theorem primeCubeCoefficientPhaseDerivative_wall (L a b y : ℝ) (hL : L ≠ 0) :
    primeCubeCoefficientPhaseDerivative L a b (primeCubeReflectionWallPoint L y) =
      (((L * (3 * a * Real.cosh (3 * L * y / 2) -
        b * Real.cosh (L * y / 2)) : ℝ) : ℂ)) := by
  rw [primeCubeCoefficientPhaseDerivative_eq_sin]
  have hinner :
      (((L / 2 : ℝ) : ℂ) * primeCubeReflectionWallPoint L y) =
        ((Real.pi / 2 : ℝ) : ℂ) + (((L * y / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold primeCubeReflectionWallPoint
    push_cast
    field_simp [hL]
  have houter :
      (((3 * L / 2 : ℝ) : ℂ) * primeCubeReflectionWallPoint L y) =
        ((3 * Real.pi / 2 : ℝ) : ℂ) +
          (((3 * L * y / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold primeCubeReflectionWallPoint
    push_cast
    field_simp [hL]
  have hthree :
      (((3 * Real.pi / 2 : ℝ) : ℂ)) =
        (Real.pi : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hinner, houter, Complex.sin_add_mul_I, Complex.sin_add_mul_I]
  rw [hthree, Complex.sin_add, Complex.cos_add]
  push_cast
  simp
  ring

theorem primeCubeCoefficientCurrent_wall (L a b y : ℝ) (hL : L ≠ 0) :
    primeCubeCoefficientCurrent L a b (primeCubeReflectionWallPoint L y) =
      -L * Real.sinh (L * y) *
        (b - a * (2 * Real.cosh (L * y) + 1)) *
        (b - a * (6 * Real.cosh (L * y) - 3)) := by
  unfold primeCubeCoefficientCurrent
  rw [primeCubeCoefficientPhaseDerivative_wall L a b y hL,
    primeCubeCoefficientPhase_wall L a b y hL]
  let S : ℝ := a * Real.sinh (3 * L * y / 2) - b * Real.sinh (L * y / 2)
  let C : ℝ := 3 * a * Real.cosh (3 * L * y / 2) - b * Real.cosh (L * y / 2)
  change (((L * C : ℝ) : ℂ) *
    (starRingEnd ℂ) (2 * Complex.I * (S : ℂ))).im = _
  have hstar :
      (starRingEnd ℂ) (2 * Complex.I * (S : ℂ)) =
        -2 * Complex.I * (S : ℂ) := by
    change star (2 * Complex.I * (S : ℂ)) = _
    rw [Complex.star_def, map_mul, map_mul]
    rw [map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hstar]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  dsimp [C, S]
  have h3 : 3 * L * y / 2 = 3 * (L * y / 2) := by ring
  have h2 : L * y = 2 * (L * y / 2) := by ring
  have hsinh3 :
      Real.sinh (3 * (L * y / 2)) =
        Real.sinh (L * y / 2) *
          (4 * Real.cosh (L * y / 2) ^ (2 : ℕ) - 1) := by
    rw [Real.sinh_three_mul, Real.cosh_sq]
    ring
  have hcosh2 :
      Real.cosh (2 * (L * y / 2)) =
        2 * Real.cosh (L * y / 2) ^ (2 : ℕ) - 1 := by
    rw [Real.cosh_two_mul, Real.cosh_sq]
    ring
  rw [h3, hsinh3, Real.cosh_three_mul, h2,
    Real.sinh_two_mul, hcosh2]
  ring

theorem exists_primeCubeCoefficientCurrent_pos_of_three_mul_lt
    {L a b : ℝ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (hanti : 3 * a < b) :
    ∃ z : ℂ, 0 < z.im ∧ 0 < primeCubeCoefficientCurrent L a b z := by
  let r : ℝ := b / (3 * a)
  let t : ℝ := Real.arcosh r
  let y : ℝ := t / L
  have hden : 0 < 3 * a := mul_pos (by norm_num) ha
  have hr : 1 < r := by
    dsimp [r]
    exact (lt_div_iff₀ hden).2 (by simpa [mul_comm] using hanti)
  have ht : 0 < t := Real.arcosh_pos hr
  have hy : 0 < y := div_pos ht hL
  have hLy : L * y = t := by
    dsimp [y]
    field_simp [hL.ne']
  have hcosh : Real.cosh t = r := Real.cosh_arcosh hr.le
  have hb_eq : b = 3 * a * r := by
    dsimp [r]
    field_simp [ha.ne']
  have hfac1 : 0 < b - a * (2 * r + 1) := by
    rw [hb_eq]
    have : 0 < a * (r - 1) := mul_pos ha (sub_pos.mpr hr)
    rw [show 3 * a * r - a * (2 * r + 1) = a * (r - 1) by ring]
    exact this
  have hfac2 : b - a * (6 * r - 3) < 0 := by
    rw [hb_eq]
    have : 0 < 3 * a * (r - 1) := mul_pos hden (sub_pos.mpr hr)
    nlinarith
  refine ⟨primeCubeReflectionWallPoint L y, ?_, ?_⟩
  · simpa [primeCubeReflectionWallPoint] using hy
  · rw [primeCubeCoefficientCurrent_wall L a b y hL.ne', hLy, hcosh]
    have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
    have hpref :
        -L * Real.sinh t * (b - a * (2 * r + 1)) < 0 :=
      mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hL) hsinh) hfac1
    exact mul_pos_of_neg_of_neg hpref hfac2

theorem primeCubeCoefficientCurrent_lt_zero_iff_leeYangCone
    {L a b : ℝ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) :
    (∀ z : ℂ, 0 < z.im → primeCubeCoefficientCurrent L a b z < 0) ↔
      b ≤ 3 * a := by
  constructor
  · intro hcurrent
    by_contra hcone
    have hanti : 3 * a < b := lt_of_not_ge hcone
    obtain ⟨z, hz, hpos⟩ :=
      exists_primeCubeCoefficientCurrent_pos_of_three_mul_lt hL ha hb hanti
    have hneg := hcurrent z hz
    linarith
  · intro hcone z hz
    exact primeCubeCoefficientCurrent_lt_zero_of_le_three_mul hL ha hb hcone hz

theorem hasDerivAt_thetaCuspLikelihoodSwapMassShellPhase
    (k : ℕ) (B D : ℝ) (z : ℂ) :
    HasDerivAt (thetaCuspLikelihoodSwapMassShellPhase k B D)
      (thetaCuspLikelihoodSwapMassShellPhaseDerivative k B D z) z := by
  unfold thetaCuspLikelihoodSwapMassShellPhase
    thetaCuspLikelihoodSwapMassShellPhaseDerivative
  apply HasDerivAt.fun_sum
  intro q hq
  let A : ℂ :=
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) D +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) D *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ)
  have hmode :=
    hasDerivAt_primeCubeExponentialMode (thetaFactorPairLogDisplacement q) z
  have hscaled := hmode.const_mul A
  simpa only [A, primeCubeExponentialMode, mul_assoc] using hscaled

def thetaCuspLikelihoodPrimeCubeEndpointScale (p : ℕ) (B : ℝ) : ℝ :=
  B * thetaCuspLikelihoodRayWeight (p ^ (3 : ℕ))

def thetaCuspLikelihoodPrimeCubeInnerScale (p : ℕ) (B : ℝ) : ℝ :=
  thetaCuspLikelihoodScaledBoundaryTerm p B *
      thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) +
    thetaCuspLikelihoodRayWeight p *
      thetaCuspLikelihoodScaledBoundaryTerm (p ^ (2 : ℕ)) B

theorem thetaCuspLikelihoodSwapMassShellPhase_eq_prime_cube_boundary
    {p : ℕ} (hp : p.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhase (p ^ (3 : ℕ)) B 0 z =
      primeCubeCoefficientPhase (Real.log p)
        (thetaCuspLikelihoodPrimeCubeEndpointScale p B)
        (thetaCuspLikelihoodPrimeCubeInnerScale p B) z := by
  unfold thetaCuspLikelihoodSwapMassShellPhase
  rw [thetaPositiveFactorPairs_prime_cube hp]
  have hp2 := hp.two_le
  obtain ⟨hpp, hp2p3⟩ := prime_lt_sq_and_sq_lt_cube hp
  have hleft : (0, p ^ (3 : ℕ) - 1) ∉
      ({(p - 1, p ^ (2 : ℕ) - 1), (p ^ (2 : ℕ) - 1, p - 1),
        (p ^ (3 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      have hfst := congrArg Prod.fst h
      omega
    constructor
    · intro h
      have hfst := congrArg Prod.fst h
      omega
    · intro h
      have hfst := congrArg Prod.fst h
      omega
  have hinnerLeft : (p - 1, p ^ (2 : ℕ) - 1) ∉
      ({(p ^ (2 : ℕ) - 1, p - 1), (p ^ (3 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h
    · have hfst := congrArg Prod.fst h
      omega
    · have hfst := congrArg Prod.fst h
      omega
  have hinnerRight : (p ^ (2 : ℕ) - 1, p - 1) ∉
      ({(p ^ (3 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    intro h
    have hsnd := congrArg Prod.snd h
    omega
  rw [Finset.sum_insert hleft, Finset.sum_insert hinnerLeft,
    Finset.sum_insert hinnerRight, Finset.sum_singleton]
  have hpSub : p - 1 + 1 = p := by omega
  have hpSqSub : p ^ (2 : ℕ) - 1 + 1 = p ^ (2 : ℕ) := by omega
  have hpCubeSub : p ^ (3 : ℕ) - 1 + 1 = p ^ (3 : ℕ) := by omega
  rw [hpSub, hpSqSub, hpCubeSub]
  simp only [Nat.zero_add]
  rw [thetaCuspLikelihoodScaledBoundaryTerm_one B]
  simp only [thetaCuspLikelihoodScaledBoundaryTerm_zero]
  have hRone : thetaCuspLikelihoodRayWeight 1 = 0 := by
    simp [thetaCuspLikelihoodRayWeight, thetaCuspLikelihoodGap]
  rw [hRone]
  simp only [zero_mul, add_zero, mul_zero, zero_add]
  rw [thetaFactorPairLogDisplacement_primeCube_left hp,
    thetaFactorPairLogDisplacement_primeCube_innerLeft hp,
    thetaFactorPairLogDisplacement_primeCube_innerRight hp,
    thetaFactorPairLogDisplacement_primeCube_right hp]
  unfold thetaCuspLikelihoodPrimeCubeEndpointScale
    thetaCuspLikelihoodPrimeCubeInnerScale primeCubeCoefficientPhase
    primeCubeExponentialMode
  push_cast
  ring

theorem thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime_cube_boundary
    {p : ℕ} (hp : p.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhaseDerivative (p ^ (3 : ℕ)) B 0 z =
      primeCubeCoefficientPhaseDerivative (Real.log p)
        (thetaCuspLikelihoodPrimeCubeEndpointScale p B)
        (thetaCuspLikelihoodPrimeCubeInnerScale p B) z := by
  have hleft :=
    hasDerivAt_thetaCuspLikelihoodSwapMassShellPhase (p ^ (3 : ℕ)) B 0 z
  have hright := hasDerivAt_primeCubeCoefficientPhase (Real.log p)
    (thetaCuspLikelihoodPrimeCubeEndpointScale p B)
    (thetaCuspLikelihoodPrimeCubeInnerScale p B) z
  have hfun : thetaCuspLikelihoodSwapMassShellPhase (p ^ (3 : ℕ)) B 0 =
      primeCubeCoefficientPhase (Real.log p)
        (thetaCuspLikelihoodPrimeCubeEndpointScale p B)
        (thetaCuspLikelihoodPrimeCubeInnerScale p B) := by
    funext u
    exact thetaCuspLikelihoodSwapMassShellPhase_eq_prime_cube_boundary hp B u
  rw [hfun] at hleft
  exact hleft.unique hright

theorem thetaCuspLikelihoodSwapMassShellCurrent_eq_prime_cube_boundary
    {p : ℕ} (hp : p.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellCurrent (p ^ (3 : ℕ)) B 0 z =
      primeCubeCoefficientCurrent (Real.log p)
        (thetaCuspLikelihoodPrimeCubeEndpointScale p B)
        (thetaCuspLikelihoodPrimeCubeInnerScale p B) z := by
  unfold thetaCuspLikelihoodSwapMassShellCurrent primeCubeCoefficientCurrent
  rw [thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime_cube_boundary hp,
    thetaCuspLikelihoodSwapMassShellPhase_eq_prime_cube_boundary hp]

theorem thetaFactorPairLogDisplacement_ne_zero_prime_cube
    {p : ℕ} (hp : p.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs (p ^ (3 : ℕ))) :
    thetaFactorPairLogDisplacement q ≠ 0 := by
  rw [thetaPositiveFactorPairs_prime_cube hp] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  all_goals
    simp only [thetaFactorPairLogDisplacement_primeCube_left hp,
      thetaFactorPairLogDisplacement_primeCube_innerLeft hp,
      thetaFactorPairLogDisplacement_primeCube_innerRight hp,
      thetaFactorPairLogDisplacement_primeCube_right hp]
  all_goals
    have hlog : 0 < Real.log p :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    linarith

theorem eventually_thetaCuspLikelihoodPrimeCube_antiCone
    {p : ℕ} (hp : p.Prime) :
    ∀ᶠ B : ℝ in 𝓝[>] 0,
      3 * thetaCuspLikelihoodPrimeCubeEndpointScale p B <
        thetaCuspLikelihoodPrimeCubeInnerScale p B := by
  let F : ℝ → ℝ := fun B =>
    thetaCuspLikelihoodPrimeCubeInnerScale p B -
      3 * thetaCuspLikelihoodPrimeCubeEndpointScale p B
  have hpSq : 2 ≤ p ^ (2 : ℕ) := by nlinarith [hp.two_le]
  have hRp : 0 < thetaCuspLikelihoodRayWeight p :=
    thetaCuspLikelihoodRayWeight_pos hp.two_le
  have hRpSq : 0 < thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) :=
    thetaCuspLikelihoodRayWeight_pos hpSq
  have hF0 : 0 < F 0 := by
    dsimp [F, thetaCuspLikelihoodPrimeCubeInnerScale,
      thetaCuspLikelihoodPrimeCubeEndpointScale]
    rw [thetaCuspLikelihoodScaledBoundaryTerm_zero,
      thetaCuspLikelihoodScaledBoundaryTerm_zero]
    norm_num
    positivity
  have hcont : ContinuousAt F 0 := by
    dsimp [F, thetaCuspLikelihoodPrimeCubeInnerScale,
      thetaCuspLikelihoodPrimeCubeEndpointScale]
    unfold thetaCuspLikelihoodScaledBoundaryTerm
    fun_prop
  have htend : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) :=
    hcont.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hev : ∀ᶠ B : ℝ in 𝓝[>] 0, 0 < F B :=
    htend.eventually (Ioi_mem_nhds hF0)
  filter_upwards [hev] with B hB
  dsimp [F] at hB
  linarith

theorem eventually_exists_thetaCuspLikelihoodSwapPrimeCubeCurrent_pos
    {p : ℕ} (hp : p.Prime) :
    ∀ᶠ B : ℝ in 𝓝[>] 0,
      ∃ z : ℂ, 0 < z.im ∧
        0 < thetaCuspLikelihoodSwapMassShellCurrent (p ^ (3 : ℕ)) B 0 z := by
  have hlog : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨hpp, hp2p3⟩ := prime_lt_sq_and_sq_lt_cube hp
  have hpCube : 2 ≤ p ^ (3 : ℕ) := hp.two_le.trans (hpp.le.trans hp2p3.le)
  have hpSq : 2 ≤ p ^ (2 : ℕ) := by nlinarith [hp.two_le]
  filter_upwards [self_mem_nhdsWithin,
    eventually_thetaCuspLikelihoodPrimeCube_antiCone hp] with B hB hanti
  change 0 < B at hB
  have ha : 0 < thetaCuspLikelihoodPrimeCubeEndpointScale p B := by
    unfold thetaCuspLikelihoodPrimeCubeEndpointScale
    exact mul_pos hB (thetaCuspLikelihoodRayWeight_pos hpCube)
  have hb : 0 < thetaCuspLikelihoodPrimeCubeInnerScale p B := by
    unfold thetaCuspLikelihoodPrimeCubeInnerScale
    have hSp := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg
      hp.two_le hB.le
    have hSpSq := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg
      hpSq hB.le
    have hRp := thetaCuspLikelihoodRayWeight_pos hp.two_le
    have hRpSq := thetaCuspLikelihoodRayWeight_pos hpSq
    positivity
  obtain ⟨z, hz, hcurrent⟩ :=
    exists_primeCubeCoefficientCurrent_pos_of_three_mul_lt
      hlog ha hb hanti
  refine ⟨z, hz, ?_⟩
  rw [thetaCuspLikelihoodSwapMassShellCurrent_eq_prime_cube_boundary hp]
  exact hcurrent

end

end RHTower
