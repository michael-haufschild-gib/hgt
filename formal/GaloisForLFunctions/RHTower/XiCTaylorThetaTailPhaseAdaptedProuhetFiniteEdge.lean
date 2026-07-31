import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

/-!
# Exact Prouhet cancellation of the finite translation edge

For fixed Taylor degree, evaluation of the positive cosine--sine phase section along an affine
translation depth is a polynomial in that depth.  The order-`m` zero of a phase-adapted Prouhet
packet at `X = 1` therefore kills the finite-section translation vector exactly once `m` exceeds
the Taylor degree.  This is a finite identity; no limit or degree-uniform estimate is used.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The finite positive phase section, regarded as a polynomial in its real source parameter
rather than in the spectral variable. -/
def finitePositivePhaseParameterPolynomial (d : ℕ) (z : ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (2 * d + 1),
    C (((I * z) ^ k) / k.factorial) * X ^ k

theorem finitePositivePhaseParameterPolynomial_eval
    (d : ℕ) (z : ℂ) (x : ℝ) :
    (finitePositivePhaseParameterPolynomial d z).eval (x : ℂ) =
      (finitePositivePhasePolynomial d x).eval z := by
  rw [finitePositivePhasePolynomial_eq_taylor]
  unfold finitePositivePhaseParameterPolynomial finitePositivePhaseTaylorPolynomial
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [mul_pow, mul_pow]
  ring

theorem finitePositivePhaseParameterPolynomial_natDegree_le
    (d : ℕ) (z : ℂ) :
    (finitePositivePhaseParameterPolynomial d z).natDegree ≤ 2 * d := by
  unfold finitePositivePhaseParameterPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

/-- Affine source translation written as a polynomial in the integer depth. -/
def finitePositivePhaseAffineDepthPolynomial
    (d : ℕ) (z : ℂ) (a L : ℝ) : ℂ[X] :=
  (finitePositivePhaseParameterPolynomial d z).comp
    (C (L : ℂ) * X + C (a : ℂ))

theorem finitePositivePhaseAffineDepthPolynomial_eval
    (d : ℕ) (z : ℂ) (a L : ℝ) (K : ℕ) :
    (finitePositivePhaseAffineDepthPolynomial d z a L).eval (K : ℂ) =
      (finitePositivePhasePolynomial d (a + (K : ℝ) * L)).eval z := by
  unfold finitePositivePhaseAffineDepthPolynomial
  rw [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_C]
  have harg : (L : ℂ) * (K : ℂ) + (a : ℂ) =
      ((a + (K : ℝ) * L : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, finitePositivePhaseParameterPolynomial_eval]

theorem finitePositivePhaseAffineDepthPolynomial_natDegree_le
    (d : ℕ) (z : ℂ) (a L : ℝ) :
    (finitePositivePhaseAffineDepthPolynomial d z a L).natDegree ≤ 2 * d := by
  have haffine : (C (L : ℂ) * X + C (a : ℂ) : ℂ[X]).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    refine max_le ((natDegree_C_mul_le _ _).trans ?_) ?_
    · simp
    · simp
  unfold finitePositivePhaseAffineDepthPolynomial
  calc
    ((finitePositivePhaseParameterPolynomial d z).comp
        (C (L : ℂ) * X + C (a : ℂ))).natDegree ≤
        (finitePositivePhaseParameterPolynomial d z).natDegree *
          (C (L : ℂ) * X + C (a : ℂ) : ℂ[X]).natDegree := natDegree_comp_le
    _ ≤ (2 * d) * 1 := Nat.mul_le_mul
      (finitePositivePhaseParameterPolynomial_natDegree_le d z) haffine
    _ = 2 * d := by omega

/-- Scalar extension of Prouhet cancellation: a real coefficient packet annihilates complex
polynomial tests of smaller degree. -/
theorem complex_shifted_polynomial_pairing_eq_zero_of_sub_one_pow_dvd
    {G : ℝ[X]} {p : ℂ[X]} {m : ℕ} (N : ℕ)
    (hdiv : (X - 1) ^ m ∣ G) (hp : p.natDegree < m) :
    ∑ i ∈ G.support, (G.coeff i : ℂ) * p.eval ((N + i : ℕ) : ℂ) = 0 := by
  have hdivC : (X - 1) ^ m ∣ G.map (algebraMap ℝ ℂ) := by
    obtain ⟨Q, hQ⟩ := hdiv
    refine ⟨Q.map (algebraMap ℝ ℂ), ?_⟩
    calc
      G.map (algebraMap ℝ ℂ) =
          (((X - 1) ^ m * Q).map (algebraMap ℝ ℂ)) :=
        congrArg (fun S : ℝ[X] => S.map (algebraMap ℝ ℂ)) hQ
      _ = (X - 1) ^ m * Q.map (algebraMap ℝ ℂ) := by simp
  have h := GaloisForLFunctions.shifted_polynomial_pairing_eq_zero_of_sub_one_pow_dvd
    (R := ℂ) (G := G.map (algebraMap ℝ ℂ)) (p := p) N hdivC hp
  have hinj : Function.Injective (algebraMap ℝ ℂ) := Complex.ofReal_injective
  rw [support_map_of_injective G hinj] at h
  simpa only [coeff_map, Complex.coe_algebraMap] using h

/-- An order-`m` phase-adapted packet kills the entire value vector of every degree-`2d` finite
positive phase section along an affine dyadic translate, provided `2d < m`. -/
theorem phaseAdaptedProuhet_finitePositivePhaseAffineDepthValue_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z : ℂ)
    (hm : 2 * d < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval z = 0 := by
  dsimp only
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  let p := finitePositivePhaseAffineDepthPolynomial d z a L
  have hp : p.natDegree < m :=
    lt_of_le_of_lt
      (finitePositivePhaseAffineDepthPolynomial_natDegree_le d z a L) hm
  have hdiv := X_sub_one_pow_dvd_phaseAdaptedTwoEndpointProuhetPolynomial
    m u q r tau
  have h := complex_shifted_polynomial_pairing_eq_zero_of_sub_one_pow_dvd
    (G := P) (p := p) N hdiv hp
  simpa only [P, p, finitePositivePhaseAffineDepthPolynomial_eval] using h

/-- The spectral derivative of the finite phase section, again regarded as a polynomial in the
real source parameter.  The exponent remains at most `2d`. -/
def finitePositivePhaseDerivativeParameterPolynomial (d : ℕ) (z : ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (2 * d),
    C (I * (I * z) ^ k / k.factorial) * X ^ (k + 1)

theorem finitePositivePhaseDerivativeParameterPolynomial_eval
    (d : ℕ) (z : ℂ) (x : ℝ) :
    (finitePositivePhaseDerivativeParameterPolynomial d z).eval (x : ℂ) =
      (finitePositivePhasePolynomial d x).derivative.eval z := by
  rw [eval_derivative_finitePositivePhasePolynomial_eq_sum]
  unfold finitePositivePhaseDerivativeParameterPolynomial
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [show (x : ℂ) * I * z = (x : ℂ) * (I * z) by ring, mul_pow, pow_succ]
  ring

theorem finitePositivePhaseDerivativeParameterPolynomial_natDegree_le
    (d : ℕ) (z : ℂ) :
    (finitePositivePhaseDerivativeParameterPolynomial d z).natDegree ≤ 2 * d := by
  unfold finitePositivePhaseDerivativeParameterPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Finset.mem_range.mp hk

def finitePositivePhaseDerivativeAffineDepthPolynomial
    (d : ℕ) (z : ℂ) (a L : ℝ) : ℂ[X] :=
  (finitePositivePhaseDerivativeParameterPolynomial d z).comp
    (C (L : ℂ) * X + C (a : ℂ))

theorem finitePositivePhaseDerivativeAffineDepthPolynomial_eval
    (d : ℕ) (z : ℂ) (a L : ℝ) (K : ℕ) :
    (finitePositivePhaseDerivativeAffineDepthPolynomial d z a L).eval (K : ℂ) =
      (finitePositivePhasePolynomial d
        (a + (K : ℝ) * L)).derivative.eval z := by
  unfold finitePositivePhaseDerivativeAffineDepthPolynomial
  rw [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_C]
  have harg : (L : ℂ) * (K : ℂ) + (a : ℂ) =
      ((a + (K : ℝ) * L : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, finitePositivePhaseDerivativeParameterPolynomial_eval]

theorem finitePositivePhaseDerivativeAffineDepthPolynomial_natDegree_le
    (d : ℕ) (z : ℂ) (a L : ℝ) :
    (finitePositivePhaseDerivativeAffineDepthPolynomial d z a L).natDegree ≤ 2 * d := by
  have haffine : (C (L : ℂ) * X + C (a : ℂ) : ℂ[X]).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    refine max_le ((natDegree_C_mul_le _ _).trans ?_) ?_
    · simp
    · simp
  unfold finitePositivePhaseDerivativeAffineDepthPolynomial
  calc
    ((finitePositivePhaseDerivativeParameterPolynomial d z).comp
        (C (L : ℂ) * X + C (a : ℂ))).natDegree ≤
        (finitePositivePhaseDerivativeParameterPolynomial d z).natDegree *
          (C (L : ℂ) * X + C (a : ℂ) : ℂ[X]).natDegree := natDegree_comp_le
    _ ≤ (2 * d) * 1 := Nat.mul_le_mul
      (finitePositivePhaseDerivativeParameterPolynomial_natDegree_le d z) haffine
    _ = 2 * d := by omega

theorem phaseAdaptedProuhet_finitePositivePhaseAffineDepthDerivative_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z : ℂ)
    (hm : 2 * d < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z = 0 := by
  dsimp only
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  let p := finitePositivePhaseDerivativeAffineDepthPolynomial d z a L
  have hp : p.natDegree < m :=
    lt_of_le_of_lt
      (finitePositivePhaseDerivativeAffineDepthPolynomial_natDegree_le d z a L) hm
  have hdiv := X_sub_one_pow_dvd_phaseAdaptedTwoEndpointProuhetPolynomial
    m u q r tau
  have h := complex_shifted_polynomial_pairing_eq_zero_of_sub_one_pow_dvd
    (G := P) (p := p) N hdiv hp
  simpa only [P, p, finitePositivePhaseDerivativeAffineDepthPolynomial_eval] using h

/-- The finite translated phase packet contributes zero off-diagonal current against every fixed
seam vector.  Value and derivative cancellation are used together, so no positive estimate of an
edge piece is introduced. -/
theorem phaseAdaptedProuhet_finitePositivePhaseAffineDepthHermitianCross_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z E E' : ℂ)
    (hm : 2 * d < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, P.coeff j *
      symmetricHermitianCrossCurrentData
        ((finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval z)
        ((finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z)
        E E' = 0 := by
  dsimp only
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  let V : ℕ → ℂ := fun j =>
    (finitePositivePhasePolynomial d
      (a + ((N + j : ℕ) : ℝ) * L)).eval z
  let D : ℕ → ℂ := fun j =>
    (finitePositivePhasePolynomial d
      (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z
  have hV : ∑ j ∈ P.support, (P.coeff j : ℂ) * V j = 0 := by
    simpa only [P, V] using
      phaseAdaptedProuhet_finitePositivePhaseAffineDepthValue_sum_eq_zero
        d m N u q r tau a L z hm
  have hD : ∑ j ∈ P.support, (P.coeff j : ℂ) * D j = 0 := by
    simpa only [P, D] using
      phaseAdaptedProuhet_finitePositivePhaseAffineDepthDerivative_sum_eq_zero
        d m N u q r tau a L z hm
  change ∑ j ∈ P.support, P.coeff j *
    (D j * (starRingEnd ℂ) E + E' * (starRingEnd ℂ) (V j)).im = 0
  rw [show (∑ j ∈ P.support, P.coeff j *
      (D j * (starRingEnd ℂ) E + E' * (starRingEnd ℂ) (V j)).im) =
      (∑ j ∈ P.support, (P.coeff j : ℂ) *
        (D j * (starRingEnd ℂ) E + E' * (starRingEnd ℂ) (V j))).im by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [Complex.mul_im]]
  rw [show (∑ j ∈ P.support, (P.coeff j : ℂ) *
      (D j * (starRingEnd ℂ) E + E' * (starRingEnd ℂ) (V j))) =
      (∑ j ∈ P.support, (P.coeff j : ℂ) * D j) *
          (starRingEnd ℂ) E +
        E' * (starRingEnd ℂ)
          (∑ j ∈ P.support, (P.coeff j : ℂ) * V j) by
    calc
      (∑ j ∈ P.support, (P.coeff j : ℂ) *
          (D j * (starRingEnd ℂ) E + E' * (starRingEnd ℂ) (V j))) =
          ∑ j ∈ P.support,
            (((P.coeff j : ℂ) * D j) * (starRingEnd ℂ) E +
              E' * (starRingEnd ℂ) ((P.coeff j : ℂ) * V j)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [map_mul, Complex.conj_ofReal]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, map_sum, Finset.mul_sum]]
  rw [hD, hV, map_zero]
  simp

end

end RHTower
