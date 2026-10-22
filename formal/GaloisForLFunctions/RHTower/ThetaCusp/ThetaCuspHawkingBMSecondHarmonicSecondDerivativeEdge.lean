import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussSquareRootEndpoint

/-!
# Exact second-derivative edge of the BM second-harmonic response

The regular Birmingham--Mokhtari \`++\` hypergeometric response has Gauss gap \`1/2\`.
Its first derivative therefore has the known square-root edge. The exact Gauss ODE upgrades
that result to the second derivative:

\`(1-z) * sqrt(1-z) * F''(z) -> (sqrt(pi)/2) * Gamma(c)/(Gamma(a)Gamma(b)).\`

The coefficient is nonzero on every Xi fibre. Consequently \`F''\` has no finite
unrenormalized AdS endpoint. Any second-order radial Plebanski evaluation of the exact \`++\`
response must include an explicit corner subtraction before taking the boundary limit; a naive
single-Mellin or pointwise endpoint substitution is impossible.

\`[NEW] [BM] [HYPERGEOMETRIC] [SECOND-DERIVATIVE EDGE] [CORNER NO-GO] [LEAN-PROVED]\`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact nonzero coefficient of the second-derivative AdS edge. -/
def d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient
    (n : ℕ) (chi : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (Real.sqrt Real.pi : ℂ) *
    (Complex.Gamma
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
      (Complex.Gamma
            (d4BMCausalHypergeometricA
              (d4BMCausalPlusPlusFrequency n chi) chi) *
        Complex.Gamma
            (d4BMCausalHypergeometricB
              (d4BMCausalPlusPlusFrequency n chi) chi)))

theorem tendsto_d4BMPlusPlusRegularSecondDerivative_edge
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun x : ℝ =>
        (((1 - x : ℝ) : ℂ) * (Real.sqrt (1 - x) : ℂ)) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient n chi)) := by
  let omega := d4BMCausalPlusPlusFrequency n chi
  let a := d4BMCausalHypergeometricA omega chi
  let b := d4BMCausalHypergeometricB omega chi
  let c := d4BMCausalRadialC omega
  let L : ℂ := (Real.sqrt Real.pi : ℂ) *
    (Complex.Gamma c / (Complex.Gamma a * Complex.Gamma b))
  have hF' : Tendsto
      (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) *
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 L) := by
    simpa only [L, a, b, c, omega] using
      tendsto_sqrt_one_sub_mul_d4BMPlusPlusRegularHypergeometricSolutionDerivative
        n chi hchi
  have hF : Tendsto
      (fun x : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMCausalForbiddenBoundaryCoefficient omega chi)) := by
    have h := tendsto_d4BMPlusPlusRegularHypergeometricSolution_one n chi hchi
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    simpa only [omega] using h
  have hsqrt : Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun x : ℝ => (Real.sqrt (1 - x) : ℂ)) 1 := by
      fun_prop
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    change Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) (𝓝 (0 : ℂ))
    simpa using hcont.tendsto.mono_left inf_le_left
  have hx : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    change Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) (𝓝 (1 : ℂ))
    convert (tendsto_id.mono_left inf_le_left).ofReal using 1 <;> norm_num
  have hdrift : Tendsto
      (fun x : ℝ => c - (a + b + 1) * (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (-1 / 2 : ℂ)) := by
    have hcont : ContinuousAt
        (fun x : ℝ => c - (a + b + 1) * (x : ℂ)) 1 := by
      fun_prop
    have h : Tendsto
        (fun x : ℝ => c - (a + b + 1) * (x : ℂ))
        (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
        (𝓝 (c - (a + b + 1) * (1 : ℂ))) :=
      hcont.tendsto.mono_left inf_le_left
    have hgap : c - a - b = 1 / 2 := by
      exact d4BMPlusPlusHypergeometric_gaussGap n chi
    have hlim : c - (a + b + 1) = -1 / 2 := by
      linear_combination hgap
    simpa only [mul_one, hlim] using h
  have hnum : Tendsto
      (fun x : ℝ =>
        -(c - (a + b + 1) * (x : ℂ)) *
            ((Real.sqrt (1 - x) : ℂ) *
              d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ)) +
          a * b * ((Real.sqrt (1 - x) : ℂ) *
            d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ)))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 ((1 / 2 : ℂ) * L)) := by
    have hzero : Tendsto
        (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) *
          d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ))
        (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa using hsqrt.mul hF
    convert hdrift.neg.mul hF' |>.add ((tendsto_const_nhds.mul
      tendsto_const_nhds).mul hzero) using 1
    all_goals ring
  have hquot := hnum.div hx (by norm_num)
  rw [show d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient n chi =
      (1 / 2 : ℂ) * L by
        simp only [d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient,
          L, a, b, c, omega]
        ring]
  have hpos : ∀ᶠ x : ℝ in 𝓝[Ico (0 : ℝ) 1] (1 : ℝ), 0 < x := by
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    have h : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), 0 < x :=
      Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      (fun x : ℝ =>
        (-(c - (a + b + 1) * (x : ℂ)) *
              ((Real.sqrt (1 - x) : ℂ) *
                d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ)) +
            a * b * ((Real.sqrt (1 - x) : ℂ) *
              d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ))) / (x : ℂ)) =ᶠ[
        𝓝[Ico (0 : ℝ) 1] (1 : ℝ)]
      (fun x : ℝ =>
        (((1 - x : ℝ) : ℂ) * (Real.sqrt (1 - x) : ℂ)) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hxmem hx0
    have hxnorm : ‖(x : ℂ)‖ₑ < 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx0.le]
      exact ENNReal.ofReal_lt_one.mpr hxmem.2
    have hode := d4BMPlusPlusRegularHypergeometricSolution_jet_eq_zero
      n chi (x : ℂ) hchi hxnorm
    change (x : ℂ) * (1 - (x : ℂ)) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ) +
        (c - (a + b + 1) * (x : ℂ)) *
          d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ) -
        a * b * d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ) = 0 at hode
    apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hx0.ne')).2
    push_cast
    linear_combination -(Real.sqrt (1 - x) : ℂ) * hode
  simpa using hquot.congr' heq

theorem d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient n chi ≠ 0 := by
  let omega := d4BMCausalPlusPlusFrequency n chi
  let a := d4BMCausalHypergeometricA omega chi
  let b := d4BMCausalHypergeometricB omega chi
  let c := d4BMCausalRadialC omega
  have hp : ∀ j : ℕ, (j : ℂ) ≠ -a ∧ (j : ℂ) ≠ -b ∧ (j : ℂ) ≠ -c := by
    intro j
    simpa only [a, b, c, omega] using
      d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi j
  have hGa : Complex.Gamma a ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro j hj
    apply (hp j).1
    rw [hj]
    ring
  have hGb : Complex.Gamma b ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro j hj
    apply (hp j).2.1
    rw [hj]
    ring
  have hGc : Complex.Gamma c ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro j hj
    apply (hp j).2.2
    rw [hj]
    ring
  have hsqrt : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient
  exact mul_ne_zero (mul_ne_zero (by norm_num) hsqrt)
    (div_ne_zero hGc (mul_ne_zero hGa hGb))

/-- The exact BM second derivative has no finite unrenormalized AdS endpoint. -/
theorem not_tendsto_d4BMPlusPlusRegularSecondDerivative_nhds
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (K : ℂ) :
    ¬ Tendsto
      (fun x : ℝ =>
        d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 K) := by
  intro hfinite
  have hsqrt : Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun x : ℝ => (Real.sqrt (1 - x) : ℂ)) 1 := by
      fun_prop
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    change Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) (𝓝 (0 : ℂ))
    simpa using hcont.tendsto.mono_left inf_le_left
  have hlinear : Tendsto (fun x : ℝ => ((1 - x : ℝ) : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun x : ℝ => ((1 - x : ℝ) : ℂ)) 1 := by
      fun_prop
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    change Tendsto (fun x : ℝ => ((1 - x : ℝ) : ℂ))
      (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) (𝓝 (0 : ℂ))
    simpa using hcont.tendsto.mono_left inf_le_left
  have hzero : Tendsto
      (fun x : ℝ =>
        (((1 - x : ℝ) : ℂ) * (Real.sqrt (1 - x) : ℂ)) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using (hlinear.mul hsqrt).mul hfinite
  have hedge := tendsto_d4BMPlusPlusRegularSecondDerivative_edge n chi hchi
  letI : (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
      norm_num)
  have heq : d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient n chi = 0 :=
    tendsto_nhds_unique hedge hzero
  exact d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient_ne_zero n chi hchi heq

/-- Premise-free Xi specialization of the exact second-derivative edge. -/
theorem tendsto_d4BMXiPlusPlusRegularSecondDerivative_edge
    (n : ℕ) (q : XiZeroCopy) :
    Tendsto
      (fun x : ℝ =>
        (((1 - x : ℝ) : ℂ) * (Real.sqrt (1 - x) : ℂ)) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n
            (d4BMXiMixedHorizonAngularMomentum q) (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMPlusPlusRegularSecondDerivativeEdgeCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q))) := by
  exact tendsto_d4BMPlusPlusRegularSecondDerivative_edge n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

/-- On every Xi fibre, unrenormalized second-order Plebanski radial data has no finite AdS
endpoint. -/
theorem not_tendsto_d4BMXiPlusPlusRegularSecondDerivative_nhds
    (n : ℕ) (q : XiZeroCopy) (K : ℂ) :
    ¬ Tendsto
      (fun x : ℝ =>
        d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n
          (d4BMXiMixedHorizonAngularMomentum q) (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 K) := by
  exact not_tendsto_d4BMPlusPlusRegularSecondDerivative_nhds n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) K

end

end RHTower

