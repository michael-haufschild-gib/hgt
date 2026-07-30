import GaloisForLFunctions.RHTower.XiCTaylorThetaTailScoreCovariance

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

def thetaCuspTailSurvival (x : ℝ) : ℝ :=
  -4 * thetaCuspTailDerivative 1 x

theorem hasDerivAt_thetaCuspTailSurvival (x : ℝ) :
    HasDerivAt thetaCuspTailSurvival (-thetaCuspTailSecondDensity x) x := by
  simpa only [thetaCuspTailSurvival, thetaCuspTailSecondDensity] using!
    ((hasDerivAt_thetaCuspTailDerivative 1 x).const_mul (-4)).congr_deriv (by ring)

@[simp] theorem thetaCuspTailSurvival_zero : thetaCuspTailSurvival 0 = 1 := by
  simp [thetaCuspTailSurvival, thetaCuspTailDerivative_one_zero]

theorem integrableOn_thetaCuspTailSurvival_mul_coreAtomSourceDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z x) (Ioi 0) := by
  unfold thetaCuspTailSurvival thetaCuspTailSecondCoreAtomSourceDerivative
    thetaCuspTailSecondSectionSourceDerivative
  rw [show (fun x : ℝ => ((-4 * thetaCuspTailDerivative 1 x : ℝ) : ℂ) *
      (-(z ^ 2 + 1 / 4) *
        ∑ k ∈ Finset.range (d + 1),
          (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))) =
      (fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-4 : ℂ) * (-(z ^ 2 + 1 / 4)) *
          ((-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) /
            (((2 * k + 2).factorial : ℕ) : ℂ)) *
          (((x ^ (2 * k + 1) * thetaCuspTailDerivative 1 x : ℝ) : ℂ))) by
    funext x
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring_nf]
  exact MeasureTheory.integrable_finsetSum _ fun k _hk =>
    ((integrableOn_pow_mul_thetaCuspTailDerivative (2 * k + 1) 1).ofReal).const_mul _

theorem thetaCuspTailSurvival_mul_coreAtom_tendsto_atTop_zero
    (d : ℕ) (z : ℂ) :
    Tendsto (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) * thetaCuspTailSecondCoreAtom d z x)
      atTop (nhds 0) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSurvival x : ℂ) * thetaCuspTailSecondCoreAtom d z x) =
      (fun x : ℝ => (-4 : ℂ) * (thetaCuspTailDerivative 1 x : ℂ) +
        ∑ k ∈ Finset.range (d + 1),
          (4 : ℂ) * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) /
              (((2 * k + 2).factorial : ℕ) : ℂ) *
            (((x ^ (2 * k + 2) * thetaCuspTailDerivative 1 x : ℝ) : ℂ))) by
    funext x
    unfold thetaCuspTailSurvival thetaCuspTailSecondCoreAtom
      thetaCuspTailSecondSection
    push_cast
    rw [mul_sub, mul_one, Finset.mul_sum]
    rw [Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _hk
    ring]
  have hbaseReal := pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero 0 1
  have hbase : Tendsto (fun x : ℝ =>
      (-4 : ℂ) * (thetaCuspTailDerivative 1 x : ℂ)) atTop (nhds 0) := by
    have hc := (Complex.ofRealCLM.continuous.tendsto 0).comp hbaseReal
    simpa using hc.const_mul (-4 : ℂ)
  have hsum : Tendsto (fun x : ℝ =>
      ∑ k ∈ Finset.range (d + 1),
        (4 : ℂ) * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) /
            (((2 * k + 2).factorial : ℕ) : ℂ) *
          (((x ^ (2 * k + 2) * thetaCuspTailDerivative 1 x : ℝ) : ℂ)))
      atTop (nhds 0) := by
    have hs := tendsto_finsetSum (Finset.range (d + 1)) (fun k _hk => by
      have hreal := pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (2 * k + 2) 1
      have hc := (Complex.ofRealCLM.continuous.tendsto 0).comp hreal
      simpa using hc.const_mul
        ((4 : ℂ) * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) /
          (((2 * k + 2).factorial : ℕ) : ℂ)))
    simpa using hs
  simpa using hbase.add hsum

theorem integral_density_mul_coreAtom_eq_one_add_survival_sourceDerivative
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) * thetaCuspTailSecondCoreAtom d z x) =
      1 + ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSurvival x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceDerivative d z x := by
  let u : ℝ → ℂ := fun x => (thetaCuspTailSurvival x : ℂ)
  let u' : ℝ → ℂ := fun x => (-thetaCuspTailSecondDensity x : ℂ)
  let v : ℝ → ℂ := fun x => thetaCuspTailSecondCoreAtom d z x
  let v' : ℝ → ℂ := fun x => thetaCuspTailSecondCoreAtomSourceDerivative d z x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u', Complex.ofReal_neg] using
      (hasDerivAt_thetaCuspTailSurvival x).ofReal_comp
  have hv (x : ℝ) : HasDerivAt v (v' x) x :=
    hasDerivAt_thetaCuspTailSecondCoreAtom_source d z x
  have hzero : Tendsto (u * v) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hu0 : Tendsto u (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
      have hc := (hasDerivAt_thetaCuspTailSurvival 0).ofReal_comp.continuousAt.tendsto
      simpa only [u, thetaCuspTailSurvival_zero, Complex.ofReal_one] using!
        hc.mono_left inf_le_left
    have hv0 : Tendsto v (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
      have h := (hasDerivAt_thetaCuspTailSecondCoreAtom_source d z 0).continuousAt.tendsto
      have h' : Tendsto v (nhdsWithin 0 (Ioi 0)) (nhds (v 0)) :=
        h.mono_left inf_le_left
      have hv0val : v 0 = 1 := by
        simp [v, thetaCuspTailSecondCoreAtom, thetaCuspTailSecondSection]
      simpa only [hv0val] using h'
    simpa only [Pi.mul_apply, one_mul] using! hu0.mul hv0
  have htop : Tendsto (u * v) atTop (nhds 0) := by
    simpa only [Pi.mul_apply, u, v] using!
      thetaCuspTailSurvival_mul_coreAtom_tendsto_atTop_zero d z
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u') (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x)
    (by simpa only [Pi.mul_apply, u, v'] using!
      integrableOn_thetaCuspTailSurvival_mul_coreAtomSourceDerivative d z)
    (by
      have h := (integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z).neg
      convert h using 1
      funext x
      dsimp [u', v]
      ring)
    hzero htop
  have hneg : (∫ x : ℝ in Ioi 0, u' x * v x) =
      -∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) * thetaCuspTailSecondCoreAtom d z x := by
    rw [← MeasureTheory.integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [u', v]
    ring
  rw [hneg] at hibp
  change (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) * thetaCuspTailSecondCoreAtom d z x) =
    1 + ∫ x : ℝ in Ioi 0, u x * v' x
  linear_combination -hibp

/-- The survival coordinate contains no new moment sequence.  Its `m`th moment is exactly the
next canonical-density moment divided by `m+1`; this is the one-derivative counterpart of the
Euler score recurrence. -/
theorem integral_pow_mul_thetaCuspTailSurvival_shift (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) *
        ∫ x : ℝ in Ioi 0, x ^ m * thetaCuspTailSurvival x =
      ∫ x : ℝ in Ioi 0, x ^ (m + 1) * thetaCuspTailSecondDensity x := by
  have hm1 : 0 < m + 1 := by omega
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => x ^ (m + 1))
    (u' := fun x : ℝ => ((m + 1 : ℕ) : ℝ) * x ^ m)
    (v := thetaCuspTailDerivative 1)
    (v' := thetaCuspTailDerivative 2)
    (fun x _ => by
      simpa using! hasDerivAt_pow (m + 1) x)
    (fun x _ => hasDerivAt_thetaCuspTailDerivative 1 x)
    (integrableOn_pow_mul_thetaCuspTailDerivative (m + 1) 2)
    (by
      simpa only [Pi.mul_apply, ← mul_assoc] using!
        (integrableOn_pow_mul_thetaCuspTailDerivative m 1).const_mul
          (((m + 1 : ℕ) : ℝ)))
    (pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos hm1 1)
    (pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (m + 1) 1)
  unfold thetaCuspTailSurvival thetaCuspTailSecondDensity
  rw [show (fun x : ℝ => (((m + 1 : ℕ) : ℝ) * x ^ m) *
      thetaCuspTailDerivative 1 x) =
      fun x => (((m + 1 : ℕ) : ℝ)) *
        (x ^ m * thetaCuspTailDerivative 1 x) by
    funext x
    ring, integral_const_mul] at hibp
  rw [show (fun x : ℝ => x ^ m * (-4 * thetaCuspTailDerivative 1 x)) =
      fun x => -4 * (x ^ m * thetaCuspTailDerivative 1 x) by
    funext x
    ring,
    show (fun x : ℝ => x ^ (m + 1) * (4 * thetaCuspTailDerivative 2 x)) =
      fun x => 4 * (x ^ (m + 1) * thetaCuspTailDerivative 2 x) by
        funext x
        ring,
    integral_const_mul, integral_const_mul]
  linear_combination -4 * hibp

end

end RHTower
