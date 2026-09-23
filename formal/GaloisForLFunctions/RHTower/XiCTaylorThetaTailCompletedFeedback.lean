import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedSource

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Derivative in the spectral variable of the finite cosine section. -/
def truncatedCosineSectionDerivative (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
      ((x : ℂ) ^ (2 * k) / (2 * k).factorial)

theorem hasDerivAt_truncatedCosineSection (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => truncatedCosineSection d w x)
      (truncatedCosineSectionDerivative d z x) z := by
  unfold truncatedCosineSection truncatedCosineSectionDerivative
  rw [show (fun w : ℂ => ∑ k ∈ Finset.range (d + 1),
      (-1 : ℂ) ^ k * (w * (x : ℂ)) ^ (2 * k) / (2 * k).factorial) =
      fun w : ℂ => ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * w ^ (2 * k) * (x : ℂ) ^ (2 * k) /
          (2 * k).factorial by
    funext w
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring]
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (w : ℂ) =>
      (-1 : ℂ) ^ k * w ^ (2 * k) * (x : ℂ) ^ (2 * k) /
        (2 * k).factorial)
    (A' := fun (k : ℕ) =>
      (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
        ((x : ℂ) ^ (2 * k) / (2 * k).factorial))
    (fun k _hk => by
      have hpow := hasDerivAt_pow (2 * k) z
      have hscaled :=
        ((HasDerivAt.const_mul ((-1 : ℂ) ^ k) hpow).mul_const
          ((x : ℂ) ^ (2 * k))).div_const
          (((2 * k).factorial : ℕ) : ℂ)
      simpa only [Pi.mul_apply, Pi.div_apply] using!
        hscaled.congr_deriv (by ring))
  rw [show
    (∑ k ∈ Finset.range (d + 1), fun w : ℂ =>
      (-1 : ℂ) ^ k * w ^ (2 * k) * (x : ℂ) ^ (2 * k) /
        (2 * k).factorial) =
      fun w : ℂ => ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * w ^ (2 * k) * (x : ℂ) ^ (2 * k) /
          (2 * k).factorial by
    funext w
    simp only [Finset.sum_apply]] at hsum
  exact hsum

theorem integrableOn_thetaCuspFullSource_mul_truncatedCosineSectionDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * truncatedCosineSectionDerivative d z x)
      (Ioi 0) := by
  unfold truncatedCosineSectionDerivative
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          ((x : ℂ) ^ (2 * k) / (2 * k).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)) *
          (((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k).factorial)) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => by
    have hbase := integrableOn_pow_mul_thetaCuspFullSource_complex (2 * k)
    have hdiv := hbase.mul_const (((2 * k).factorial : ℂ)⁻¹)
    have hscaled := hdiv.const_mul
      (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)))
    simpa only [div_eq_mul_inv, mul_assoc] using hscaled

theorem xiCTaylorPolynomial_oddCutoff_eval_sum (d : ℕ) (z : ℂ) :
    (xiCTaylorPolynomial (2 * d + 1)).eval z =
      ∑ k ∈ Finset.range (d + 1),
        (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
          (-1 : ℂ) ^ k * z ^ (2 * k)) := by
  rw [xiCTaylorPolynomial_eval, xiCTaylorApprox_oddCutoff_eq_evenMagnitude_eval]
  rw [xiCTaylorEvenMagnitudePolynomial]
  rw [show eval₂ (algebraMap ℝ ℂ) (-z ^ (2 : ℕ))
      (∑ k ∈ Finset.range (d + 1),
        C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k) =
      ∑ k ∈ Finset.range (d + 1),
        eval₂ (algebraMap ℝ ℂ) (-z ^ (2 : ℕ))
          (C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k) by
    change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) (-z ^ (2 : ℕ)))
        (∑ k ∈ Finset.range (d + 1),
          C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k) = _
    rw [map_sum]
    simp only [Polynomial.coe_eval₂RingHom]]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [neg_pow, ← pow_mul]
  push_cast
  ac_rfl

theorem xiCTaylorPolynomial_oddCutoff_derivative_eval_sum (d : ℕ) (z : ℂ) :
    (xiCTaylorPolynomial (2 * d + 1)).derivative.eval z =
      ∑ k ∈ Finset.range (d + 1),
        (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
          (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)) := by
  let P : Polynomial ℂ := xiCTaylorPolynomial (2 * d + 1)
  have hfun : (fun w : ℂ => P.eval w) = fun w : ℂ =>
      ∑ k ∈ Finset.range (d + 1),
        (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
          (-1 : ℂ) ^ k * w ^ (2 * k)) := by
    funext w
    exact xiCTaylorPolynomial_oddCutoff_eval_sum d w
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (w : ℂ) =>
      (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
        (-1 : ℂ) ^ k * w ^ (2 * k)))
    (A' := fun (k : ℕ) =>
      (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)))
    (fun k _hk => by
      have hpow := hasDerivAt_pow (2 * k) z
      simpa only [Pi.mul_apply] using!
        (HasDerivAt.const_mul
          ((((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
            (-1 : ℂ) ^ k)) hpow).congr_deriv (by ring))
  have hsum' : HasDerivAt (fun w : ℂ => P.eval w)
      (∑ k ∈ Finset.range (d + 1),
        (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
          (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1))) z := by
    rw [hfun]
    rw [show
      (∑ k ∈ Finset.range (d + 1), fun w : ℂ =>
        (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
          (-1 : ℂ) ^ k * w ^ (2 * k))) =
        fun w : ℂ => ∑ k ∈ Finset.range (d + 1),
          (((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
            (-1 : ℂ) ^ k * w ^ (2 * k)) by
      funext w
      simp only [Finset.sum_apply]] at hsum
    exact hsum
  simpa only [P] using (P.hasDerivAt z).unique hsum'

/-- The derivative of every odd Xi Taylor section is the derivative cosine transform of the same
completed theta source. -/
theorem xiCTaylorPolynomial_oddCutoff_derivative_eval_eq_fullSource
    (d : ℕ) (z : ℂ) :
    (xiCTaylorPolynomial (2 * d + 1)).derivative.eval z =
      2 * ∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x : ℂ) * truncatedCosineSectionDerivative d z x := by
  rw [xiCTaylorPolynomial_oddCutoff_derivative_eval_sum]
  unfold truncatedCosineSectionDerivative
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          ((x : ℂ) ^ (2 * k) / (2 * k).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)) *
          (((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k).factorial)) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [thetaCuspRawEvenCoefficient_eq_fullSource_complex_integral]
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro k _
    have hbase := integrableOn_pow_mul_thetaCuspFullSource_complex (2 * k)
    have hdiv := hbase.mul_const (((2 * k).factorial : ℂ)⁻¹)
    have hscaled := hdiv.const_mul
      (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)))
    simpa only [div_eq_mul_inv, mul_assoc] using hscaled

theorem integrableOn_thetaCuspFullSource_mul_tailSecondSection
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondSection d z x)
      (Ioi 0) := by
  unfold thetaCuspTailSecondSection
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((-1 : ℂ) ^ k * z ^ (2 * k)) *
          (((x ^ (2 * k + 2) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k + 2).factorial)) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => by
    have hbase := integrableOn_pow_mul_thetaCuspFullSource_complex (2 * k + 2)
    have hdiv := hbase.mul_const (((2 * k + 2).factorial : ℂ)⁻¹)
    have hscaled := hdiv.const_mul (((-1 : ℂ) ^ k * z ^ (2 * k)))
    simpa only [div_eq_mul_inv, mul_assoc] using hscaled

theorem integrableOn_thetaCuspFullSource_mul_tailSecondSectionDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondSectionDerivative d z x)
      (Ioi 0) := by
  unfold thetaCuspTailSecondSectionDerivative
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)) *
          (((x ^ (2 * k + 2) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k + 2).factorial)) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => by
    have hbase := integrableOn_pow_mul_thetaCuspFullSource_complex (2 * k + 2)
    have hdiv := hbase.mul_const (((2 * k + 2).factorial : ℂ)⁻¹)
    have hscaled := hdiv.const_mul
      (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)))
    simpa only [div_eq_mul_inv, mul_assoc] using hscaled

theorem integrableOn_thetaCuspFullSource_mul_tailSecondCoreAtom
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondCoreAtom d z x)
      (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => (thetaCuspFullSource x : ℂ)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspFullSource_complex 0
  have hsection := integrableOn_thetaCuspFullSource_mul_tailSecondSection d z
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ => (thetaCuspFullSource x : ℂ) -
        (z ^ (2 : ℕ) + 1 / 4) *
          ((thetaCuspFullSource x : ℂ) * thetaCuspTailSecondSection d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtom
    ring]
  exact hbase.sub (hsection.const_mul (z ^ (2 : ℕ) + 1 / 4))

theorem integrableOn_thetaCuspFullSource_mul_tailSecondCoreAtomDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondCoreAtomDerivative d z x)
      (Ioi 0) := by
  have hs := integrableOn_thetaCuspFullSource_mul_tailSecondSection d z
  have hsd := integrableOn_thetaCuspFullSource_mul_tailSecondSectionDerivative d z
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
      fun x : ℝ => (-2 * z) *
          ((thetaCuspFullSource x : ℂ) * thetaCuspTailSecondSection d z x) -
        (z ^ (2 : ℕ) + 1 / 4) *
          ((thetaCuspFullSource x : ℂ) *
            thetaCuspTailSecondSectionDerivative d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtomDerivative
    ring]
  exact (hs.const_mul (-2 * z)).sub (hsd.const_mul (z ^ (2 : ℕ) + 1 / 4))

/-- Differentiated completion identity for one finite core atom. -/
theorem sq_mul_tailSecondCoreAtomDerivative_add
    (d : ℕ) (z : ℂ) (x : ℝ) :
    z ^ (2 : ℕ) * thetaCuspTailSecondCoreAtomDerivative d z x +
        2 * z * thetaCuspTailSecondCoreAtom d z x =
      (z ^ (2 : ℕ) + 1 / 4) * truncatedCosineSectionDerivative (d + 1) z x +
        2 * z * truncatedCosineSection (d + 1) z x := by
  let f : ℂ → ℂ := fun w =>
    w ^ (2 : ℕ) * thetaCuspTailSecondCoreAtom d w x
  let g : ℂ → ℂ := fun w =>
    (w ^ (2 : ℕ) + 1 / 4) * truncatedCosineSection (d + 1) w x - 1 / 4
  have hfun : f = g := by
    funext w
    exact sq_mul_thetaCuspTailSecondCoreAtom_eq_completion_mul_cosine_sub d w x
  have hf : HasDerivAt f
      (z ^ (2 : ℕ) * thetaCuspTailSecondCoreAtomDerivative d z x +
        2 * z * thetaCuspTailSecondCoreAtom d z x) z := by
    dsimp only [f]
    simpa only [Pi.mul_apply] using!
      ((hasDerivAt_pow 2 z).mul
        (hasDerivAt_thetaCuspTailSecondCoreAtom d z x)).congr_deriv (by ring)
  have hg : HasDerivAt g
      ((z ^ (2 : ℕ) + 1 / 4) * truncatedCosineSectionDerivative (d + 1) z x +
        2 * z * truncatedCosineSection (d + 1) z x) z := by
    dsimp only [g]
    have hquad : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + 1 / 4) (2 * z) z := by
      simpa only [Pi.add_apply] using!
        ((hasDerivAt_pow 2 z).add_const (1 / 4 : ℂ)).congr_deriv (by ring)
    simpa only [Pi.mul_apply, Pi.sub_apply] using!
      ((hquad.mul (hasDerivAt_truncatedCosineSection (d + 1) z x)).sub_const
        (1 / 4 : ℂ)).congr_deriv (by ring)
  rw [hfun] at hf
  exact hf.unique hg

/-- Integrated derivative balance: the completed core atom and the next Xi Taylor section carry
the same finite derivative data after the completion multiplier. -/
theorem completedFullSource_coreAtom_derivative_balance (d : ℕ) (z : ℂ) :
    z ^ (2 : ℕ) *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x) +
      2 * z *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondCoreAtom d z x) =
      (z ^ (2 : ℕ) + 1 / 4) *
          (xiCTaylorPolynomial (2 * (d + 1) + 1)).derivative.eval z +
        2 * z * xiCTaylorApprox (2 * (d + 1) + 1) z := by
  have hcore := integrableOn_thetaCuspFullSource_mul_tailSecondCoreAtom d z
  have hcoreD :=
    integrableOn_thetaCuspFullSource_mul_tailSecondCoreAtomDerivative d z
  have hcos := integrableOn_thetaCuspFullSource_mul_truncatedCosineSection (d + 1) z
  have hcosD :=
    integrableOn_thetaCuspFullSource_mul_truncatedCosineSectionDerivative (d + 1) z
  rw [xiCTaylorPolynomial_oddCutoff_derivative_eval_eq_fullSource (d + 1) z,
    xiCTaylorApprox_oddCutoff_eq_fullSource_truncatedCosine (d + 1) z]
  have hpoint : (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) *
        (z ^ (2 : ℕ) * thetaCuspTailSecondCoreAtomDerivative d z x +
          2 * z * thetaCuspTailSecondCoreAtom d z x)) =
      fun x : ℝ =>
        (thetaCuspFullSource x : ℂ) *
          ((z ^ (2 : ℕ) + 1 / 4) * truncatedCosineSectionDerivative (d + 1) z x +
            2 * z * truncatedCosineSection (d + 1) z x) := by
    funext x
    rw [sq_mul_tailSecondCoreAtomDerivative_add]
  have hint :
      (∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x : ℂ) *
          (z ^ (2 : ℕ) * thetaCuspTailSecondCoreAtomDerivative d z x +
            2 * z * thetaCuspTailSecondCoreAtom d z x)) =
        ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ) *
            ((z ^ (2 : ℕ) + 1 / 4) * truncatedCosineSectionDerivative (d + 1) z x +
              2 * z * truncatedCosineSection (d + 1) z x) := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrFun hpoint x
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      (z ^ (2 : ℕ) * thetaCuspTailSecondCoreAtomDerivative d z x +
        2 * z * thetaCuspTailSecondCoreAtom d z x)) =
      fun x : ℝ => z ^ (2 : ℕ) * ((thetaCuspFullSource x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x) +
        2 * z * ((thetaCuspFullSource x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) by
    funext x; ring,
    integral_add (hcoreD.const_mul (z ^ (2 : ℕ))) (hcore.const_mul (2 * z)),
    integral_const_mul, integral_const_mul] at hint
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ((z ^ (2 : ℕ) + 1 / 4) * truncatedCosineSectionDerivative (d + 1) z x +
        2 * z * truncatedCosineSection (d + 1) z x)) =
      fun x : ℝ => (z ^ (2 : ℕ) + 1 / 4) * ((thetaCuspFullSource x : ℂ) *
          truncatedCosineSectionDerivative (d + 1) z x) +
        2 * z * ((thetaCuspFullSource x : ℂ) *
          truncatedCosineSection (d + 1) z x) by
    funext x; ring,
    integral_add (hcosD.const_mul (z ^ (2 : ℕ) + 1 / 4)) (hcos.const_mul (2 * z)),
    integral_const_mul, integral_const_mul] at hint
  linear_combination 2 * hint

/-- **Completed-source derivative feedback.**  The completed theta contribution to the finite core
derivative is exactly the next Xi Taylor derivative plus the fixed central seam.  The identity is
denominator-free and remains valid at `z=0`. -/
theorem pow_four_mul_two_fullSource_coreAtomDerivative_integral_eq_taylor_feedback
    (d : ℕ) (z : ℂ) :
    z ^ (4 : ℕ) *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x) =
      z ^ (2 : ℕ) * (z ^ (2 : ℕ) + 1 / 4) *
          (xiCTaylorPolynomial (2 * (d + 1) + 1)).derivative.eval z +
        (z / 2) *
          (xiCTaylorApprox 1 0 - xiCTaylorApprox (2 * (d + 1) + 1) z) := by
  have hbalance := completedFullSource_coreAtom_derivative_balance d z
  have hvalue :=
    sq_mul_two_fullSource_coreAtom_integral_eq_completion_mul_taylor_sub_seam d z
  linear_combination z ^ (2 : ℕ) * hbalance - 2 * z * hvalue

end

end RHTower
