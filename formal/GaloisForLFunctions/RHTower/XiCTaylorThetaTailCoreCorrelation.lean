import GaloisForLFunctions.RHTower.XiCTaylorThetaTailConvexCore

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

def thetaCuspTailSecondSectionDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
      ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)

theorem hasDerivAt_thetaCuspTailSecondSection
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => thetaCuspTailSecondSection d w x)
      (thetaCuspTailSecondSectionDerivative d z x) z := by
  unfold thetaCuspTailSecondSection thetaCuspTailSecondSectionDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (w : ℂ) => (-1 : ℂ) ^ k * w ^ (2 * k) *
      ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))
    (A' := fun (k : ℕ) => (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) *
      z ^ (2 * k - 1) *
        ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))
    (fun k _hk => by
      have hpow := hasDerivAt_pow (2 * k) z
      have hscaled :=
        (HasDerivAt.const_mul ((-1 : ℂ) ^ k) hpow).mul_const
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)
      convert hscaled using 1 <;> ring)
  convert hsum using 1
  funext w
  simp only [Finset.sum_apply]

def thetaCuspTailSecondCoreAtomDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  -2 * z * thetaCuspTailSecondSection d z x -
    (z ^ 2 + 1 / 4) * thetaCuspTailSecondSectionDerivative d z x

theorem hasDerivAt_thetaCuspTailSecondCoreAtom
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => thetaCuspTailSecondCoreAtom d w x)
      (thetaCuspTailSecondCoreAtomDerivative d z x) z := by
  unfold thetaCuspTailSecondCoreAtom thetaCuspTailSecondCoreAtomDerivative
  have hquad : HasDerivAt (fun w : ℂ => w ^ 2 + 1 / 4) (2 * z) z := by
    convert (hasDerivAt_pow 2 z).add_const (1 / 4 : ℂ) using 1 <;> ring
  convert (hasDerivAt_const z (1 : ℂ)).sub
    (hquad.mul (hasDerivAt_thetaCuspTailSecondSection d z x)) using 1 <;> ring

theorem integrableOn_thetaCuspTailSecondDensity_mul_sectionDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondSectionDerivative d z x) (Ioi 0) := by
  unfold thetaCuspTailSecondSectionDerivative
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            ((-1 : ℂ) ^ k *
              ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring]
  exact MeasureTheory.integrable_finset_sum _ fun k _ => by
    simpa only [one_pow, mul_one] using
      (integrableOn_thetaCuspTailSecondDensity_mul_term k (1 : ℂ)).const_mul
        (((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1))

theorem integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) (Ioi 0) := by
  have hs := integrableOn_thetaCuspTailSecondDensity_mul_section d z
  have hsd :=
    integrableOn_thetaCuspTailSecondDensity_mul_sectionDerivative d z
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
      fun x : ℝ => (-2 * z) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSection d z x) -
        (z ^ 2 + 1 / 4) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSectionDerivative d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtomDerivative
    ring]
  exact (hs.const_mul (-2 * z)).sub (hsd.const_mul (z ^ 2 + 1 / 4))

def thetaCuspTailSecondAverageSectionDerivative
    (d : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k *
      ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)

theorem evenMagnitudeLift_thetaCuspTailEvenPolynomial_eval_sum
    (d : ℕ) (z : ℂ) :
    (evenMagnitudeLift (thetaCuspTailEvenPolynomial d)).eval z =
      ∑ k ∈ Finset.range (d + 1),
        (thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k * z ^ (2 * k) := by
  rw [evenMagnitudeLift_eval, thetaCuspTailEvenPolynomial]
  rw [show eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
      (∑ k ∈ Finset.range (d + 1),
        C (thetaCuspTailEvenCoefficient k) * X ^ k) =
      ∑ k ∈ Finset.range (d + 1),
        eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
          (C (thetaCuspTailEvenCoefficient k) * X ^ k) by
    change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) (-z ^ 2))
        (∑ k ∈ Finset.range (d + 1),
          C (thetaCuspTailEvenCoefficient k) * X ^ k) = _
    rw [map_sum]
    simp only [Polynomial.coe_eval₂RingHom]]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [neg_pow, ← pow_mul]
  change (thetaCuspTailEvenCoefficient k : ℂ) *
      ((-1 : ℂ) ^ k * z ^ (2 * k)) =
    (thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k * z ^ (2 * k)
  ring

theorem evenMagnitudeLift_thetaCuspTailEvenPolynomial_derivative_eval
    (d : ℕ) (z : ℂ) :
    (evenMagnitudeLift (thetaCuspTailEvenPolynomial d)).derivative.eval z =
      thetaCuspTailSecondAverageSectionDerivative d z := by
  let A : Polynomial ℂ := evenMagnitudeLift (thetaCuspTailEvenPolynomial d)
  have hfun : (fun w : ℂ => A.eval w) = fun w : ℂ =>
      ∑ k ∈ Finset.range (d + 1),
        (thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k * w ^ (2 * k) := by
    funext w
    exact evenMagnitudeLift_thetaCuspTailEvenPolynomial_eval_sum d w
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (w : ℂ) =>
      (thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k * w ^ (2 * k))
    (A' := fun (k : ℕ) =>
      (thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k *
        ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1))
    (fun k _hk => by
      have hpow := hasDerivAt_pow (2 * k) z
      convert HasDerivAt.const_mul
        ((thetaCuspTailEvenCoefficient k : ℂ) * (-1 : ℂ) ^ k) hpow using 1 <;> ring)
  have hsum' : HasDerivAt (fun w : ℂ => A.eval w)
      (thetaCuspTailSecondAverageSectionDerivative d z) z := by
    rw [hfun]
    unfold thetaCuspTailSecondAverageSectionDerivative
    convert hsum using 1
    funext w
    simp only [Finset.sum_apply]
  simpa only [A] using (A.hasDerivAt z).unique hsum'

theorem thetaCuspTailSecondAverageSectionDerivative_eq_integral
    (d : ℕ) (z : ℂ) :
    thetaCuspTailSecondAverageSectionDerivative d z =
      (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondSectionDerivative d z x := by
  unfold thetaCuspTailSecondAverageSectionDerivative
  unfold thetaCuspTailSecondSectionDerivative
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (thetaCuspTailSecondDensity x : ℂ) *
          ((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) by
    funext x
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [thetaCuspTailEvenCoefficient_eq_second_complex_integral]
    calc
      ((1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) *
          (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) =
        (1 / 2 : ℂ) * ((∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) *
              (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)))) := by ring
      _ = (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
          ((thetaCuspTailSecondDensity x : ℂ) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) *
              (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1))) := by
        rw [MeasureTheory.integral_mul_const]
      _ = (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            ((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
              ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) := by
        congr 2
        funext x
        ring
  · intro k _
    have h := integrableOn_thetaCuspTailSecondDensity_mul_term k (1 : ℂ)
    have hs := h.const_mul
      (((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1)) /
        ((-1 : ℂ) ^ k))
    by_cases hk : k = 0
    · subst k
      simp
    · have hsign : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      convert hs using 1
      funext x
      field_simp
      ring

theorem xiCTaylorThetaTailCorePolynomial_derivative_eval
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).derivative.eval z =
      -2 * z *
          (evenMagnitudeLift (thetaCuspTailEvenPolynomial d)).eval z -
        (z ^ 2 + 1 / 4) *
          thetaCuspTailSecondAverageSectionDerivative d z := by
  let U : Polynomial ℂ := xiCTaylorThetaTailCorePolynomial d
  let A : Polynomial ℂ := evenMagnitudeLift (thetaCuspTailEvenPolynomial d)
  have hfun : (fun w : ℂ => U.eval w) = fun w : ℂ =>
      1 / 2 - (w ^ 2 + 1 / 4) * A.eval w := by
    funext w
    dsimp only [U, A]
    rw [xiCTaylorThetaTailCorePolynomial, evenMagnitudeLift_eval,
      evenMagnitudeLift_eval]
    simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_sub, eval₂_X]
    push_cast
    ring
  have hquad : HasDerivAt (fun w : ℂ => w ^ 2 + 1 / 4) (2 * z) z := by
    convert (hasDerivAt_pow 2 z).add_const (1 / 4 : ℂ) using 1 <;> ring
  have hformula : HasDerivAt (fun w : ℂ =>
      1 / 2 - (w ^ 2 + 1 / 4) * A.eval w)
      (-2 * z * A.eval z -
        (z ^ 2 + 1 / 4) * A.derivative.eval z) z := by
    convert (hasDerivAt_const z (1 / 2 : ℂ)).sub
      (hquad.mul (A.hasDerivAt z)) using 1 <;> ring
  have hU : HasDerivAt (fun w : ℂ => U.eval w)
      (-2 * z * A.eval z -
        (z ^ 2 + 1 / 4) * A.derivative.eval z) z := by
    rw [hfun]
    exact hformula
  have hunique := (U.hasDerivAt z).unique hU
  rw [evenMagnitudeLift_thetaCuspTailEvenPolynomial_derivative_eval] at hunique
  simpa only [U, A] using hunique

theorem xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).derivative.eval z =
      (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x := by
  rw [xiCTaylorThetaTailCorePolynomial_derivative_eval]
  have hS := thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_second_integral d z
  rw [← evenMagnitudeLift_eval] at hS
  have hSd :=
    thetaCuspTailSecondAverageSectionDerivative_eq_integral d z
  have hintS := integrableOn_thetaCuspTailSecondDensity_mul_section d z
  have hintSd :=
    integrableOn_thetaCuspTailSecondDensity_mul_sectionDerivative d z
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
      fun x : ℝ => (-2 * z) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSection d z x) -
        (z ^ 2 + 1 / 4) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSectionDerivative d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtomDerivative
    ring]
  rw [integral_sub (hintS.const_mul (-2 * z))
      (hintSd.const_mul (z ^ 2 + 1 / 4)),
    integral_const_mul, integral_const_mul]
  rw [hS, hSd]
  ring

theorem integrableOn_thetaCuspTailSecondDensity_mul_coreAtom
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) (Ioi 0) := by
  have hmass := integrableOn_thetaCuspTailSecondDensity_complex
  have hsection := integrableOn_thetaCuspTailSecondDensity_mul_section d z
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) -
        (z ^ 2 + 1 / 4) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSection d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtom
    ring]
  exact hmass.sub (hsection.const_mul (z ^ 2 + 1 / 4))

def xiCTaylorThetaTailCoreCorrelationKernel
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  (((thetaCuspTailSecondDensity p.1 : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z p.1) *
    (starRingEnd ℂ) ((thetaCuspTailSecondDensity p.2 : ℂ) *
      thetaCuspTailSecondCoreAtom d z p.2)).im

theorem xiCTaylorThetaTailCore_current_eq_correlationIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreCorrelationKernel d z p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let g : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  have hf : Integrable f mu :=
    integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z
  have hg : Integrable g mu :=
    integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z
  have hgconj : Integrable (fun x => (starRingEnd ℂ) (g x)) mu := by
    exact (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg
  have hfg : Integrable (fun p : ℝ × ℝ =>
      f p.1 * (starRingEnd ℂ) (g p.2)) (mu.prod mu) :=
    hf.mul_prod hgconj
  have hmul : (∫ p : ℝ × ℝ,
      f p.1 * (starRingEnd ℂ) (g p.2) ∂mu.prod mu) =
      (∫ x : ℝ, f x ∂mu) *
        (starRingEnd ℂ) (∫ y : ℝ, g y ∂mu) := by
    have h := MeasureTheory.integral_prod_mul (μ := mu) (ν := mu)
      f (fun y => (starRingEnd ℂ) (g y))
    rw [integral_conj] at h
    exact h
  have him := integral_im hfg
  have him' : (∫ p : ℝ × ℝ,
      f p.1 * (starRingEnd ℂ) (g p.2) ∂mu.prod mu).im =
      ∫ p : ℝ × ℝ,
        (f p.1 * (starRingEnd ℂ) (g p.2)).im ∂mu.prod mu := by
    simpa using him.symm
  have hder :=
    xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral d z
  have hval := xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral d z
  change (((xiCTaylorThetaTailCorePolynomial d).derivative.eval z) *
      (starRingEnd ℂ) ((xiCTaylorThetaTailCorePolynomial d).eval z)).im = _
  rw [hder, hval]
  change (((1 / 2 : ℂ) * ∫ x : ℝ, f x ∂mu) *
      (starRingEnd ℂ) ((1 / 2 : ℂ) * ∫ y : ℝ, g y ∂mu)).im = _
  rw [map_mul, show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    rw [map_div₀, map_one, map_ofNat]]
  rw [show ((1 / 2 : ℂ) * ∫ x : ℝ, f x ∂mu) *
      ((1 / 2 : ℂ) * (starRingEnd ℂ) (∫ y : ℝ, g y ∂mu)) =
      (1 / 4 : ℂ) * ((∫ x : ℝ, f x ∂mu) *
        (starRingEnd ℂ) (∫ y : ℝ, g y ∂mu)) by ring]
  rw [← hmul]
  rw [show ((1 / 4 : ℂ) * (∫ p : ℝ × ℝ,
      f p.1 * (starRingEnd ℂ) (g p.2) ∂mu.prod mu)).im =
      (1 / 4 : ℝ) * (∫ p : ℝ × ℝ,
        f p.1 * (starRingEnd ℂ) (g p.2) ∂mu.prod mu).im by
    rw [Complex.mul_im]
    norm_num]
  rw [him']
  congr 1

def xiCTaylorThetaTailCoreSymmetricCorrelationKernel
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  (xiCTaylorThetaTailCoreCorrelationKernel d z p +
    xiCTaylorThetaTailCoreCorrelationKernel d z p.swap) / 2

/-- The unweighted symmetric pair current.  The full source contribution is this kernel multiplied
by the two canonical density values. -/
def xiCTaylorThetaTailCorePairCurrent
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  ((thetaCuspTailSecondCoreAtomDerivative d z p.1 *
      (starRingEnd ℂ) (thetaCuspTailSecondCoreAtom d z p.2)).im +
    (thetaCuspTailSecondCoreAtomDerivative d z p.2 *
      (starRingEnd ℂ) (thetaCuspTailSecondCoreAtom d z p.1)).im) / 2

theorem xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) :
    xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p =
      thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 *
        xiCTaylorThetaTailCorePairCurrent d z p := by
  rcases p with ⟨x, y⟩
  unfold xiCTaylorThetaTailCoreSymmetricCorrelationKernel
    xiCTaylorThetaTailCoreCorrelationKernel
    xiCTaylorThetaTailCorePairCurrent
  simp only [Prod.swap_prod_mk, Prod.fst, Prod.snd, map_mul,
    Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    zero_sub, mul_zero]
  push_cast
  ring

theorem integral_coreCorrelationKernel_eq_symmetric
    (d : ℕ) (z : ℂ) :
    (∫ p : ℝ × ℝ,
      xiCTaylorThetaTailCoreCorrelationKernel d z p
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let K : ℝ × ℝ → ℝ :=
    xiCTaylorThetaTailCoreCorrelationKernel d z
  have hswap : (∫ p : ℝ × ℝ, K p.swap ∂mu.prod mu) =
      ∫ p : ℝ × ℝ, K p ∂mu.prod mu := by
    exact MeasureTheory.integral_prod_swap (μ := mu) (ν := mu) K
  unfold xiCTaylorThetaTailCoreSymmetricCorrelationKernel
  change (∫ p : ℝ × ℝ, K p ∂mu.prod mu) =
    ∫ p : ℝ × ℝ, (K p + K p.swap) / 2 ∂mu.prod mu
  rw [show (fun p : ℝ × ℝ => (K p + K p.swap) / 2) =
      fun p : ℝ × ℝ => (1 / 2 : ℝ) * (K p + K p.swap) by
    funext p
    ring]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_add]
  · rw [hswap]
    ring
  · have hf : Integrable (fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x)
        (volume.restrict (Ioi 0)) :=
      integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z
    have hg : Integrable (fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x)
        (volume.restrict (Ioi 0)) :=
      integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z
    have hgconj : Integrable (fun x : ℝ =>
        (starRingEnd ℂ) ((thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x))
        (volume.restrict (Ioi 0)) :=
      (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg
    have hprod := hf.mul_prod hgconj
    have him := hprod.im
    convert him using 1
  · have hf : Integrable (fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x)
        (volume.restrict (Ioi 0)) :=
      integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z
    have hg : Integrable (fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x)
        (volume.restrict (Ioi 0)) :=
      integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z
    have hgconj : Integrable (fun x : ℝ =>
        (starRingEnd ℂ) ((thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x))
        (volume.restrict (Ioi 0)) :=
      (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg
    have hprod := hf.mul_prod hgconj
    exact hprod.im.swap

theorem xiCTaylorThetaTailCore_current_eq_symmetricCorrelationIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [xiCTaylorThetaTailCore_current_eq_correlationIntegral,
    integral_coreCorrelationKernel_eq_symmetric]

end
end RHTower
