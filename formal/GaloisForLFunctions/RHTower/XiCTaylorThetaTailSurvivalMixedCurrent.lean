import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSurvivalPolarization

/-!
# Survival form of the oriented current of the theta-tail core polynomial

With the theta-tail survival function `S = -4 Θ'`, second density `D = 4 Θ'' = -S'`, truncated
second section `σ_d(z, x) = Σ_(k ≤ d) (-1)^k z^(2k) x^(2k+2) / (2k+2)!` and core atom
`A_d(z, x) = 1 - (z^2 + 1/4) σ_d(z, x)`, this module integrates `∫_0^∞ D ∂_z A_d` by parts against
`S` (the boundary terms vanish at `0` and at `∞`). Writing `V_d(z) = ∫_0^∞ S ∂_x A_d` and
`W_d(z) = ∫_0^∞ S ∂_x ∂_z A_d`, the core polynomial is `Q_d(z) = (1 + V_d(z))/2` with
`Q_d'(z) = W_d(z)/2`, so its oriented current `Im(Q_d'(z) conj Q_d(z))` equals
`(1/4) Im(W_d conj(1 + V_d))`.

## Main results

- `integral_density_mul_coreAtomDerivative_eq_survival_sourceSpectralDerivative`:
  `∫_0^∞ D(x) ∂_z A_d(z, x) dx = ∫_0^∞ S(x) ∂_x ∂_z A_d(z, x) dx`.
- `xiCTaylorThetaTailCorePolynomial_eval_eq_survival`: `Q_d(z) = (1 + V_d(z))/2`.
- `xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_survival`: `Q_d'(z) = W_d(z)/2`.
- `xiCTaylorThetaTailCore_current_eq_survival_mixed`: the oriented current of `Q_d` at `z` is
  `(1/4) Im(W_d(z) conj(1 + V_d(z)))`.
- `xiCTaylorThetaTailCore_current_eq_survival_seam_add_cross`: the same current split as
  `(1/4) Im W_d + (1/4) Im(W_d conj V_d)`.

## Hypotheses

Unconditional; all identities hold for every `d : ℕ` and complex `z`.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The mixed derivative `∂_x ∂_z σ_d(z, x)` of the truncated second section. -/
def thetaCuspTailSecondSectionSourceSpectralDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
      ((2 * k + 2 : ℕ) : ℂ) *
        ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial)

/-- The `x`-derivative of `∂_z σ_d(z, x)` is the mixed derivative `∂_x ∂_z σ_d`. -/
theorem hasDerivAt_thetaCuspTailSecondSectionDerivative_source
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspTailSecondSectionDerivative d z t)
      (thetaCuspTailSecondSectionSourceSpectralDerivative d z x) x := by
  unfold thetaCuspTailSecondSectionDerivative
    thetaCuspTailSecondSectionSourceSpectralDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (t : ℝ) =>
      (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
        ((t : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))
    (A' := fun (k : ℕ) =>
      (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
        ((2 * k + 2 : ℕ) : ℂ) *
          ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))
    (fun k _hk => by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using! Complex.ofRealCLM.hasDerivAt
      have hpow := hbase.pow (2 * k + 2)
      have hscaled :=
        (hpow.div_const ((2 * k + 2).factorial : ℂ)).const_mul
          ((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1))
      have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      simpa only [Pi.pow_apply, Pi.div_apply] using!
        hscaled.congr_deriv (by
          rw [hsub]
          ring))
  apply hsum.congr_of_eventuallyEq
  filter_upwards with t
  simp only [Finset.sum_apply]

/-- The mixed derivative `∂_x ∂_z A_d(z, x)` of the core atom. -/
def thetaCuspTailSecondCoreAtomSourceSpectralDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  -2 * z * thetaCuspTailSecondSectionSourceDerivative d z x -
    (z ^ (2 : ℕ) + 1 / 4) *
      thetaCuspTailSecondSectionSourceSpectralDerivative d z x

/-- The `x`-derivative of `∂_z A_d(z, x)` is the mixed derivative `∂_x ∂_z A_d`. -/
theorem hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspTailSecondCoreAtomDerivative d z t)
      (thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x) x := by
  unfold thetaCuspTailSecondCoreAtomDerivative
    thetaCuspTailSecondCoreAtomSourceSpectralDerivative
  simpa only [Pi.sub_apply] using!
    ((hasDerivAt_thetaCuspTailSecondSection_source d z x).const_mul (-2 * z)).sub
      ((hasDerivAt_thetaCuspTailSecondSectionDerivative_source d z x).const_mul
        (z ^ (2 : ℕ) + 1 / 4))

/-- `S(x) ∂_x σ_d(z, x)` is integrable on `(0, ∞)`. -/
theorem integrableOn_thetaCuspTailSurvival_mul_sectionSourceDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondSectionSourceDerivative d z x) (Ioi 0) := by
  unfold thetaCuspTailSurvival thetaCuspTailSecondSectionSourceDerivative
  rw [show (fun x : ℝ => ((-4 * thetaCuspTailDerivative 1 x : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
          ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial)) =
      (fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-4 : ℂ) *
          ((-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) /
            (((2 * k + 2).factorial : ℕ) : ℂ)) *
          (((x ^ (2 * k + 1) * thetaCuspTailDerivative 1 x : ℝ) : ℂ))) by
    funext x
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring_nf]
  exact MeasureTheory.integrable_finsetSum _ fun k _hk =>
    ((integrableOn_pow_mul_thetaCuspTailDerivative (2 * k + 1) 1).ofReal).const_mul _

/-- `S(x) ∂_x ∂_z σ_d(z, x)` is integrable on `(0, ∞)`. -/
theorem integrableOn_thetaCuspTailSurvival_mul_sectionSourceSpectralDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondSectionSourceSpectralDerivative d z x) (Ioi 0) := by
  unfold thetaCuspTailSurvival thetaCuspTailSecondSectionSourceSpectralDerivative
  rw [show (fun x : ℝ => ((-4 * thetaCuspTailDerivative 1 x : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          ((2 * k + 2 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial)) =
      (fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-4 : ℂ) *
          ((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
            ((2 * k + 2 : ℕ) : ℂ) /
              (((2 * k + 2).factorial : ℕ) : ℂ)) *
          (((x ^ (2 * k + 1) * thetaCuspTailDerivative 1 x : ℝ) : ℂ))) by
    funext x
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring_nf]
  exact MeasureTheory.integrable_finsetSum _ fun k _hk =>
    ((integrableOn_pow_mul_thetaCuspTailDerivative (2 * k + 1) 1).ofReal).const_mul _

/-- `S(x) ∂_x ∂_z A_d(z, x)` is integrable on `(0, ∞)`. -/
theorem integrableOn_thetaCuspTailSurvival_mul_coreAtomSourceSpectralDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x) (Ioi 0) := by
  have hs := integrableOn_thetaCuspTailSurvival_mul_sectionSourceDerivative d z
  have hsd :=
    integrableOn_thetaCuspTailSurvival_mul_sectionSourceSpectralDerivative d z
  rw [show (fun x : ℝ => (thetaCuspTailSurvival x : ℂ) *
      thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x) =
      fun x : ℝ => (-2 * z) *
          ((thetaCuspTailSurvival x : ℂ) *
            thetaCuspTailSecondSectionSourceDerivative d z x) -
        (z ^ (2 : ℕ) + 1 / 4) *
          ((thetaCuspTailSurvival x : ℂ) *
            thetaCuspTailSecondSectionSourceSpectralDerivative d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtomSourceSpectralDerivative
    ring]
  exact (hs.const_mul (-2 * z)).sub (hsd.const_mul (z ^ (2 : ℕ) + 1 / 4))

/-- `S(x) σ_d(z, x) → 0` as `x → ∞`, since `S` decays faster than every polynomial grows. -/
theorem thetaCuspTailSurvival_mul_section_tendsto_atTop_zero
    (d : ℕ) (z : ℂ) :
    Tendsto (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) * thetaCuspTailSecondSection d z x)
      atTop (nhds 0) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) * thetaCuspTailSecondSection d z x) =
      (fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-4 : ℂ) * (-1 : ℂ) ^ k * z ^ (2 * k) /
              (((2 * k + 2).factorial : ℕ) : ℂ) *
            (((x ^ (2 * k + 2) * thetaCuspTailDerivative 1 x : ℝ) : ℂ))) by
    funext x
    unfold thetaCuspTailSurvival thetaCuspTailSecondSection
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring]
  have hs := tendsto_finsetSum (Finset.range (d + 1)) (fun k _hk => by
    have hreal := pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (2 * k + 2) 1
    have hc := (Complex.ofRealCLM.continuous.tendsto 0).comp hreal
    simpa using hc.const_mul
      ((-4 : ℂ) * (-1 : ℂ) ^ k * z ^ (2 * k) /
        (((2 * k + 2).factorial : ℕ) : ℂ)))
  simpa using hs

/-- `S(x) ∂_z σ_d(z, x) → 0` as `x → ∞`. -/
theorem thetaCuspTailSurvival_mul_sectionDerivative_tendsto_atTop_zero
    (d : ℕ) (z : ℂ) :
    Tendsto (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondSectionDerivative d z x)
      atTop (nhds 0) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondSectionDerivative d z x) =
      (fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-4 : ℂ) * (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) *
            z ^ (2 * k - 1) /
              (((2 * k + 2).factorial : ℕ) : ℂ) *
            (((x ^ (2 * k + 2) * thetaCuspTailDerivative 1 x : ℝ) : ℂ))) by
    funext x
    unfold thetaCuspTailSurvival thetaCuspTailSecondSectionDerivative
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring]
  have hs := tendsto_finsetSum (Finset.range (d + 1)) (fun k _hk => by
    have hreal := pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (2 * k + 2) 1
    have hc := (Complex.ofRealCLM.continuous.tendsto 0).comp hreal
    simpa using hc.const_mul
      ((-4 : ℂ) * (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) *
        z ^ (2 * k - 1) /
          (((2 * k + 2).factorial : ℕ) : ℂ)))
  simpa using hs

/-- `S(x) ∂_z A_d(z, x) → 0` as `x → ∞`. -/
theorem thetaCuspTailSurvival_mul_coreAtomDerivative_tendsto_atTop_zero
    (d : ℕ) (z : ℂ) :
    Tendsto (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x)
      atTop (nhds 0) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) =
      fun x : ℝ => (-2 * z) *
          ((thetaCuspTailSurvival x : ℂ) *
            thetaCuspTailSecondSection d z x) -
        (z ^ (2 : ℕ) + 1 / 4) *
          ((thetaCuspTailSurvival x : ℂ) *
            thetaCuspTailSecondSectionDerivative d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtomDerivative
    ring]
  simpa using
    ((thetaCuspTailSurvival_mul_section_tendsto_atTop_zero d z).const_mul (-2 * z)).sub
      ((thetaCuspTailSurvival_mul_sectionDerivative_tendsto_atTop_zero d z).const_mul
        (z ^ (2 : ℕ) + 1 / 4))

@[simp] theorem thetaCuspTailSecondCoreAtomDerivative_zero
    (d : ℕ) (z : ℂ) :
    thetaCuspTailSecondCoreAtomDerivative d z 0 = 0 := by
  unfold thetaCuspTailSecondCoreAtomDerivative thetaCuspTailSecondSection
    thetaCuspTailSecondSectionDerivative
  simp

/-- Integration by parts with `D = -S'`: `∫_0^∞ D(x) ∂_z A_d(z, x) dx = ∫_0^∞ S(x) ∂_x ∂_z A_d(z, x) dx`,
the boundary terms vanishing because `∂_z A_d(z, 0) = 0` and `S ∂_z A_d → 0` at infinity. -/
theorem integral_density_mul_coreAtomDerivative_eq_survival_sourceSpectralDerivative
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) =
      ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSurvival x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x := by
  let u : ℝ → ℂ := fun x => (thetaCuspTailSurvival x : ℂ)
  let u' : ℝ → ℂ := fun x => (-thetaCuspTailSecondDensity x : ℂ)
  let v : ℝ → ℂ := fun x => thetaCuspTailSecondCoreAtomDerivative d z x
  let v' : ℝ → ℂ :=
    fun x => thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u', Complex.ofReal_neg] using
      (hasDerivAt_thetaCuspTailSurvival x).ofReal_comp
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    simpa only [v, v'] using
      hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z x
  have hzero : Tendsto (u * v) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hu0 : Tendsto u (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
      have hc := (hasDerivAt_thetaCuspTailSurvival 0).ofReal_comp.continuousAt.tendsto
      simpa only [u, thetaCuspTailSurvival_zero, Complex.ofReal_one] using!
        hc.mono_left inf_le_left
    have hv0 : Tendsto v (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h :=
        (hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z 0).continuousAt.tendsto
      simpa only [v, thetaCuspTailSecondCoreAtomDerivative_zero] using!
        h.mono_left inf_le_left
    simpa only [Pi.mul_apply, one_mul] using! hu0.mul hv0
  have htop : Tendsto (u * v) atTop (nhds 0) := by
    simpa only [Pi.mul_apply, u, v] using!
      thetaCuspTailSurvival_mul_coreAtomDerivative_tendsto_atTop_zero d z
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u') (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x)
    (by simpa only [Pi.mul_apply, u, v'] using!
      integrableOn_thetaCuspTailSurvival_mul_coreAtomSourceSpectralDerivative d z)
    (by
      have h :=
        (integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z).neg
      convert h using 1
      funext x
      dsimp [u', v]
      ring)
    hzero htop
  have hneg : (∫ x : ℝ in Ioi 0, u' x * v x) =
      -∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x := by
    rw [← MeasureTheory.integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [u', v]
    ring
  rw [hneg] at hibp
  change (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) =
    ∫ x : ℝ in Ioi 0, u x * v' x
  linear_combination -hibp

/-- The survival value transform `V_d(z) = ∫_0^∞ S(x) ∂_x A_d(z, x) dx`. -/
def thetaCuspTailSurvivalValueTransform
    (d : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSurvival x : ℂ) *
      thetaCuspTailSecondCoreAtomSourceDerivative d z x

/-- The survival derivative transform `W_d(z) = ∫_0^∞ S(x) ∂_x ∂_z A_d(z, x) dx`. -/
def thetaCuspTailSurvivalDerivativeTransform
    (d : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSurvival x : ℂ) *
      thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x

/-- The truncated theta-tail core polynomial is `Q_d(z) = (1 + V_d(z))/2`. -/
theorem xiCTaylorThetaTailCorePolynomial_eval_eq_survival
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).eval z =
      (1 / 2 : ℂ) * (1 + thetaCuspTailSurvivalValueTransform d z) := by
  rw [xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral,
    integral_density_mul_coreAtom_eq_one_add_survival_sourceDerivative]
  rfl

/-- The derivative of the core polynomial is `Q_d'(z) = W_d(z)/2`. -/
theorem xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_survival
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).derivative.eval z =
      (1 / 2 : ℂ) * thetaCuspTailSurvivalDerivativeTransform d z := by
  rw [xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral,
    integral_density_mul_coreAtomDerivative_eq_survival_sourceSpectralDerivative]
  rfl

/-- The oriented current `Im(Q_d'(z) conj Q_d(z))` of the core polynomial equals
`(1/4) Im(W_d(z) conj(1 + V_d(z)))`. -/
theorem xiCTaylorThetaTailCore_current_eq_survival_mixed
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        (thetaCuspTailSurvivalDerivativeTransform d z *
          (starRingEnd ℂ) (1 + thetaCuspTailSurvivalValueTransform d z)).im := by
  unfold orientedPolynomialCurrent
  rw [xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_survival,
    xiCTaylorThetaTailCorePolynomial_eval_eq_survival, map_mul]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    rw [map_div₀, map_one, map_ofNat]]
  rw [show ((1 / 2 : ℂ) * thetaCuspTailSurvivalDerivativeTransform d z) *
      ((1 / 2 : ℂ) *
        (starRingEnd ℂ) (1 + thetaCuspTailSurvivalValueTransform d z)) =
      (1 / 4 : ℂ) *
        (thetaCuspTailSurvivalDerivativeTransform d z *
          (starRingEnd ℂ) (1 + thetaCuspTailSurvivalValueTransform d z)) by ring]
  rw [Complex.mul_im]
  norm_num

/-- The oriented current of the core polynomial splits as `(1/4) Im W_d(z) + (1/4) Im(W_d(z) conj V_d(z))`. -/
theorem xiCTaylorThetaTailCore_current_eq_survival_seam_add_cross
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        (thetaCuspTailSurvivalDerivativeTransform d z).im +
      (1 / 4 : ℝ) *
        (thetaCuspTailSurvivalDerivativeTransform d z *
          (starRingEnd ℂ) (thetaCuspTailSurvivalValueTransform d z)).im := by
  rw [xiCTaylorThetaTailCore_current_eq_survival_mixed]
  rw [map_add, map_one]
  simp only [mul_add, mul_one, Complex.add_im]

end

end RHTower
