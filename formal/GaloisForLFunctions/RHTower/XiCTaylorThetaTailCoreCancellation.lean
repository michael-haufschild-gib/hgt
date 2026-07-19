import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCorrelation

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

def thetaCuspTailSecondSectionSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
      ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial)

def thetaCuspTailSecondSectionSourceSecondDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
      ((2 * k + 1 : ℕ) : ℂ) *
        ((x : ℂ) ^ (2 * k) / (2 * k + 2).factorial)

theorem hasDerivAt_thetaCuspTailSecondSection_source
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspTailSecondSection d z t)
      (thetaCuspTailSecondSectionSourceDerivative d z x) x := by
  unfold thetaCuspTailSecondSection
    thetaCuspTailSecondSectionSourceDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (t : ℝ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) *
        ((t : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))
    (A' := fun (k : ℕ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
        ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))
    (fun k _hk => by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt
      have hpow := hbase.pow (2 * k + 2)
      have hscaled :=
        (HasDerivAt.const_mul ((-1 : ℂ) ^ k * z ^ (2 * k)) hpow).mul_const
          (((2 * k + 2).factorial : ℂ)⁻¹)
      have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      convert hscaled using 1
      · funext y
        simp only [Pi.pow_apply, div_eq_mul_inv]
        ring
      · rw [hsub]
        simp only [div_eq_mul_inv]
        ring)
  convert hsum using 1
  funext t
  simp only [Finset.sum_apply]

theorem hasDerivAt_thetaCuspTailSecondSectionSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      thetaCuspTailSecondSectionSourceDerivative d z t)
      (thetaCuspTailSecondSectionSourceSecondDerivative d z x) x := by
  unfold thetaCuspTailSecondSectionSourceDerivative
    thetaCuspTailSecondSectionSourceSecondDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (t : ℝ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
        ((t : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))
    (A' := fun (k : ℕ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
        ((2 * k + 1 : ℕ) : ℂ) *
          ((x : ℂ) ^ (2 * k) / (2 * k + 2).factorial))
    (fun k _hk => by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt
      have hpow := hbase.pow (2 * k + 1)
      have hscaled :=
        (HasDerivAt.const_mul
          ((-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ)) hpow).mul_const
            (((2 * k + 2).factorial : ℂ)⁻¹)
      have hsub : 2 * k + 1 - 1 = 2 * k := by omega
      convert hscaled using 1
      · funext y
        simp only [Pi.pow_apply, div_eq_mul_inv]
        ring
      · rw [hsub]
        simp only [div_eq_mul_inv]
        ring)
  convert hsum using 1
  funext t
  simp only [Finset.sum_apply]

theorem thetaCuspTailSecondSectionSourceSecondDerivative_eq_truncatedCosine
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSectionSourceSecondDerivative d z x =
      truncatedCosineSection d z x := by
  unfold thetaCuspTailSecondSectionSourceSecondDerivative
    truncatedCosineSection
  apply Finset.sum_congr rfl
  intro k _
  have hfac : (2 * k + 2).factorial =
      (2 * k).factorial * (2 * k + 1) * (2 * k + 2) := by
    calc
      (2 * k + 2).factorial = (2 * k + 1).factorial * (2 * k + 2) := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ]
        ring
      _ = ((2 * k).factorial * (2 * k + 1)) * (2 * k + 2) := by
        rw [Nat.factorial_succ]
        ring
  have hratio :
      (((2 * k + 2 : ℕ) : ℂ) * ((2 * k + 1 : ℕ) : ℂ)) /
          (((2 * k + 2).factorial : ℕ) : ℂ) =
        1 / (((2 * k).factorial : ℕ) : ℂ) := by
    rw [hfac]
    push_cast
    have hfac0 : (((2 * k).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k)
    have hodd : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : 2 * k + 1 ≠ 0)
    have heven : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : 2 * k + 2 ≠ 0)
    have hodd' : 2 * (k : ℂ) + 1 ≠ 0 := by
      rw [show 2 * (k : ℂ) + 1 = ((2 * k + 1 : ℕ) : ℂ) by
        push_cast
        ring]
      exact hodd
    field_simp [hfac0, hodd, heven, hodd']
  rw [mul_pow]
  calc
    (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
          ((2 * k + 1 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k) / (2 * k + 2).factorial) =
        (-1 : ℂ) ^ k * z ^ (2 * k) * (x : ℂ) ^ (2 * k) *
          ((((2 * k + 2 : ℕ) : ℂ) * ((2 * k + 1 : ℕ) : ℂ)) /
            (((2 * k + 2).factorial : ℕ) : ℂ)) := by
      push_cast
      ring
    _ = (-1 : ℂ) ^ k * z ^ (2 * k) * (x : ℂ) ^ (2 * k) *
          (1 / (((2 * k).factorial : ℕ) : ℂ)) := by rw [hratio]
    _ = (-1 : ℂ) ^ k * (z ^ (2 * k) * (x : ℂ) ^ (2 * k)) /
          (2 * k).factorial := by
      push_cast
      ring

def thetaCuspTailSecondCoreAtomSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  -(z ^ 2 + 1 / 4) *
    thetaCuspTailSecondSectionSourceDerivative d z x

theorem hasDerivAt_thetaCuspTailSecondCoreAtom_source
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspTailSecondCoreAtom d z t)
      (thetaCuspTailSecondCoreAtomSourceDerivative d z x) x := by
  unfold thetaCuspTailSecondCoreAtom
    thetaCuspTailSecondCoreAtomSourceDerivative
  convert (hasDerivAt_const x (1 : ℂ)).sub
    ((hasDerivAt_thetaCuspTailSecondSection_source d z x).const_mul
      (z ^ 2 + 1 / 4)) using 1 <;> ring

theorem hasDerivAt_thetaCuspTailSecondCoreAtomSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      thetaCuspTailSecondCoreAtomSourceDerivative d z t)
      (-(z ^ 2 + 1 / 4) * truncatedCosineSection d z x) x := by
  unfold thetaCuspTailSecondCoreAtomSourceDerivative
  have h := (hasDerivAt_thetaCuspTailSecondSectionSourceDerivative d z x).const_mul
    (-(z ^ 2 + 1 / 4))
  rw [thetaCuspTailSecondSectionSourceSecondDerivative_eq_truncatedCosine] at h
  exact h

theorem thetaCuspTailSecondCoreAtom_sourceSecondDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) :
    deriv (fun t : ℝ => deriv
      (fun u : ℝ => thetaCuspTailSecondCoreAtom d z u) t) x =
      -(z ^ 2 + 1 / 4) * truncatedCosineSection d z x := by
  have hfirst : deriv (fun u : ℝ => thetaCuspTailSecondCoreAtom d z u) =
      fun t : ℝ => thetaCuspTailSecondCoreAtomSourceDerivative d z t := by
    funext t
    exact (hasDerivAt_thetaCuspTailSecondCoreAtom_source d z t).deriv
  rw [hfirst]
  exact (hasDerivAt_thetaCuspTailSecondCoreAtomSourceDerivative d z x).deriv

/-- The canonical density contains both the raw positive tail and the completed even theta source.
This is the first identity in the cancellation analysis that uses the full theta completion, rather
than positivity and two derivatives alone. -/
theorem thetaCuspTailSecondDensity_eq_tail_add_four_fullSource (x : ℝ) :
    thetaCuspTailSecondDensity x =
      thetaCuspTailDerivative 0 x + 4 * thetaCuspFullSource x := by
  rw [thetaCuspFullSource_eq_tail_second_sub]
  unfold thetaCuspTailSecondDensity
  ring

/-- The canonical density has the same elementary half-exponential reflection defect as the raw
one-sided theta tail.  The completed difference `rho - T = 4 Phi` is the even part. -/
theorem thetaCuspTailSecondDensity_neg (x : ℝ) :
    thetaCuspTailSecondDensity (-x) =
      thetaCuspTailSecondDensity x + thetaCuspReflectionMode x := by
  rw [thetaCuspTailSecondDensity_eq_tail_add_four_fullSource,
    thetaCuspTailSecondDensity_eq_tail_add_four_fullSource,
    thetaCuspTailDerivative_zero_neg, thetaCuspFullSource_neg]
  simp only [thetaCuspReflectionMode]
  ring

/-- Subtracting the raw tail removes the whole reflection defect of the canonical density. -/
theorem thetaCuspTailSecondDensity_sub_tail_neg (x : ℝ) :
    thetaCuspTailSecondDensity (-x) - thetaCuspTailDerivative 0 (-x) =
      thetaCuspTailSecondDensity x - thetaCuspTailDerivative 0 x := by
  rw [thetaCuspTailSecondDensity_neg, thetaCuspTailDerivative_zero_neg]
  simp only [thetaCuspReflectionMode]
  ring

/-- Exact finite-section completion identity.  The shifted second section is not an independent
kernel: after multiplication by `z^2` it is the defect of the next ordinary cosine section. -/
theorem truncatedCosineSection_succ_eq_one_sub_sq_mul_secondSection
    (d : ℕ) (z : ℂ) (x : ℝ) :
    truncatedCosineSection (d + 1) z x =
      1 - z ^ 2 * thetaCuspTailSecondSection d z x := by
  unfold truncatedCosineSection thetaCuspTailSecondSection
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    one_mul]
  rw [show z ^ 2 *
      (∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      ∑ k ∈ Finset.range (d + 1),
        z ^ 2 * ((-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) by
    rw [Finset.mul_sum]]
  have hsum :
      (∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ (k + 1) * (z * (x : ℂ)) ^ (2 * (k + 1)) /
          (2 * (k + 1)).factorial) =
      -(∑ k ∈ Finset.range (d + 1),
        z ^ 2 * ((-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    rw [show (-1 : ℂ) ^ (k + 1) = -((-1 : ℂ) ^ k) by
      rw [pow_succ]
      ring]
    rw [mul_pow]
    rw [show z ^ (2 * k + 2) = z ^ 2 * z ^ (2 * k) by
      rw [pow_add]
      ring]
    ring
  rw [hsum]
  ring

/-- The completion-compensated form of each convex-core atom.  It exposes the exact seam
`-1/4` and the next finite cosine section without dividing by `z`. -/
theorem sq_mul_thetaCuspTailSecondCoreAtom_eq_completion_mul_cosine_sub
    (d : ℕ) (z : ℂ) (x : ℝ) :
    z ^ 2 * thetaCuspTailSecondCoreAtom d z x =
      (z ^ 2 + 1 / 4) * truncatedCosineSection (d + 1) z x - 1 / 4 := by
  have hsection : z ^ 2 * thetaCuspTailSecondSection d z x =
      1 - truncatedCosineSection (d + 1) z x := by
    rw [truncatedCosineSection_succ_eq_one_sub_sq_mul_secondSection]
    ring
  unfold thetaCuspTailSecondCoreAtom
  calc
    z ^ 2 * (1 - (z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x) =
        z ^ 2 - (z ^ 2 + 1 / 4) *
          (z ^ 2 * thetaCuspTailSecondSection d z x) := by ring
    _ = z ^ 2 - (z ^ 2 + 1 / 4) *
          (1 - truncatedCosineSection (d + 1) z x) := by rw [hsection]
    _ = (z ^ 2 + 1 / 4) * truncatedCosineSection (d + 1) z x - 1 / 4 := by ring

/-- Multiplication by the completion monomial `z^2` has one exact radial current cost.  This
identity isolates that cost from the completion-compensated cosine correlation. -/
theorem orientedPolynomialCurrent_X_sq_mul
    (P : Polynomial ℂ) (z : ℂ) :
    orientedPolynomialCurrent (X ^ 2 * P) z =
      Complex.normSq z ^ 2 * orientedPolynomialCurrent P z -
        2 * Complex.normSq z * z.im * Complex.normSq (P.eval z) := by
  unfold orientedPolynomialCurrent
  simp only [derivative_mul, derivative_X_pow, Nat.cast_ofNat, eval_add, eval_mul,
    eval_C, eval_pow, eval_X, map_mul, map_pow]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  norm_num
  ring

/-- The exact one-source integration-by-parts identity, including its boundary seam.  It is
stated at the finite-section level and follows by comparing the two already proved canonical
representations of the same core polynomial. -/
theorem integral_thetaCuspTailSecondDensity_mul_coreAtom_eq_seam_sub_tail
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      1 - 4 * (z ^ 2 + 1 / 4) *
        ∫ x : ℝ in Ioi 0,
          (thetaCuspTailDerivative 0 x : ℂ) *
            truncatedCosineSection d z x := by
  have hrho := xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral d z
  have htail := xiCTaylorThetaTailCorePolynomial_eval_eq_integral d z
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
        2 * (xiCTaylorThetaTailCorePolynomial d).eval z := by
          rw [hrho]
          ring
    _ = 2 * (1 / 2 - (z ^ 2 + 1 / 4) *
          (2 * ∫ x : ℝ in Ioi 0,
            (thetaCuspTailDerivative 0 x : ℂ) *
              truncatedCosineSection d z x)) := by rw [htail]
    _ = 1 - 4 * (z ^ 2 + 1 / 4) *
          ∫ x : ℝ in Ioi 0,
            (thetaCuspTailDerivative 0 x : ℂ) *
              truncatedCosineSection d z x := by ring

/-- The core current after integrating by parts in exactly the value variable.  The first term is
the uncancelled seam and the second is the mixed `rho`--`T` correlation.  Keeping these terms
together is essential: neither has a useful sign separately. -/
theorem xiCTaylorThetaTailCore_current_eq_seam_sub_mixed
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        (∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x).im -
      ((∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x) *
        (starRingEnd ℂ)
          ((z ^ 2 + 1 / 4) *
            ∫ y : ℝ in Ioi 0,
              (thetaCuspTailDerivative 0 y : ℂ) *
                truncatedCosineSection d z y)).im := by
  have hder :=
    xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral d z
  have hval := xiCTaylorThetaTailCorePolynomial_eval_eq_integral d z
  unfold orientedPolynomialCurrent
  rw [hder, hval]
  let I : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let M : ℂ := ∫ y : ℝ in Ioi 0,
    (thetaCuspTailDerivative 0 y : ℂ) * truncatedCosineSection d z y
  let A : ℂ := z ^ 2 + 1 / 4
  change (((1 / 2 : ℂ) * I) *
      (starRingEnd ℂ) (1 / 2 - A * (2 * M))).im =
    (1 / 4 : ℝ) * I.im - (I * (starRingEnd ℂ) (A * M)).im
  have hcomplex : ((1 / 2 : ℂ) * I) *
      (starRingEnd ℂ) (1 / 2 - A * (2 * M)) =
        (1 / 4 : ℂ) * I - I * (starRingEnd ℂ) (A * M) := by
    simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat]
    ring
  rw [hcomplex, Complex.sub_im]
  rw [show ((1 / 4 : ℂ) * I).im = (1 / 4 : ℝ) * I.im by
    rw [Complex.mul_im]
    norm_num]

theorem integrableOn_thetaCuspTailDerivative_mul_truncatedCosineSection
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailDerivative 0 x : ℂ) *
        truncatedCosineSection d z x) (Ioi 0) := by
  unfold truncatedCosineSection
  rw [show (fun x : ℝ => (thetaCuspTailDerivative 0 x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) / (2 * k).factorial) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (thetaCuspTailDerivative 0 x : ℂ) *
          ((-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) /
            (2 * k).factorial) by
    funext x
    rw [Finset.mul_sum]]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => by
    have hbase : IntegrableOn
        (fun x : ℝ => ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ))
        (Ioi 0) :=
      (integrableOn_pow_mul_thetaCuspTailDerivative (2 * k) 0).ofReal
    have hscaled := hbase.const_mul
      (((-1 : ℂ) ^ k * z ^ (2 * k)) /
        (((2 * k).factorial : ℕ) : ℂ))
    convert hscaled using 1
    funext x
    push_cast
    rw [mul_pow]
    ring

def xiCTaylorThetaTailCoreMixedCorrelationKernel
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  (((thetaCuspTailSecondDensity p.1 : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z p.1) *
    (starRingEnd ℂ)
      ((z ^ 2 + 1 / 4) *
        ((thetaCuspTailDerivative 0 p.2 : ℂ) *
          truncatedCosineSection d z p.2))).im

/-- Product-measure form of the asymmetric integration-by-parts identity.  This is the exact
finite object on which any source-specific cancellation estimate must act. -/
theorem xiCTaylorThetaTailCore_current_eq_seam_sub_mixedCorrelationIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        (∫ x : ℝ in Ioi 0,
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x).im) -
      ∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreMixedCorrelationKernel d z p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let g : ℝ → ℂ := fun y =>
    (z ^ 2 + 1 / 4) *
      ((thetaCuspTailDerivative 0 y : ℂ) * truncatedCosineSection d z y)
  have hf : Integrable f mu :=
    integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z
  have hg : Integrable g mu :=
    (integrableOn_thetaCuspTailDerivative_mul_truncatedCosineSection d z).const_mul
      (z ^ 2 + 1 / 4)
  have hgconj : Integrable (fun y => (starRingEnd ℂ) (g y)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg
  have hprod : Integrable (fun p : ℝ × ℝ =>
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
  have him : (∫ p : ℝ × ℝ,
      f p.1 * (starRingEnd ℂ) (g p.2) ∂mu.prod mu).im =
      ∫ p : ℝ × ℝ,
        (f p.1 * (starRingEnd ℂ) (g p.2)).im ∂mu.prod mu := by
    simpa using (integral_im hprod).symm
  have hfim : (∫ x : ℝ, f x ∂mu).im =
      ∫ x : ℝ, (f x).im ∂mu := by
    simpa using (integral_im hf).symm
  rw [xiCTaylorThetaTailCore_current_eq_seam_sub_mixed]
  change (1 / 4 : ℝ) * (∫ x : ℝ, f x ∂mu).im -
      ((∫ x : ℝ, f x ∂mu) *
        (starRingEnd ℂ)
          ((z ^ 2 + 1 / 4) *
            ∫ y : ℝ, (thetaCuspTailDerivative 0 y : ℂ) *
              truncatedCosineSection d z y ∂mu)).im = _
  rw [hfim]
  have hgIntegral : (∫ y : ℝ, g y ∂mu) =
      (z ^ 2 + 1 / 4) *
        ∫ y : ℝ, (thetaCuspTailDerivative 0 y : ℂ) *
          truncatedCosineSection d z y ∂mu := by
    simpa only [g] using
      (MeasureTheory.integral_const_mul (μ := mu) (z ^ 2 + 1 / 4)
        (fun y : ℝ => (thetaCuspTailDerivative 0 y : ℂ) *
          truncatedCosineSection d z y))
  rw [← hgIntegral, ← hmul, him]
  simp only [mu, f, g, xiCTaylorThetaTailCoreMixedCorrelationKernel]

end
end RHTower
