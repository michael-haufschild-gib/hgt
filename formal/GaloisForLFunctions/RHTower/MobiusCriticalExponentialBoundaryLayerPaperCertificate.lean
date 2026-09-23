import GaloisForLFunctions.RHTower.MobiusCriticalBoundaryLayerQuantiles
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscapePaperCertificate

/-!
# Paper certificate: the normalized Möbius carrier has an exponential critical boundary layer

Formal certificate for
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`
`mobius-critical-exponential-boundary-layer-law.md`, with `sigma = 1 + 2 omega`.

```text
(1)  P_omega{d} = mu(d)^(2 : ℕ) d^{-sigma} / (zeta(sigma)/zeta(2 sigma)) ,
(2)  sum_d mu(d)^(2 : ℕ) d^{-sigma} = zeta(sigma)/zeta(2 sigma) ,
(3)  ||(C_omega f)_d||^(2 : ℕ) / ||C_omega f||^(2 : ℕ) = P_omega{d} ,
(4)  Y_omega(d) = 2 omega log d = (sigma - 1) log d ,
(6)  E_omega[exp(-u Y_omega)] -> 1/(1+u) ,
(8)  E_omega[exp(-u Y_omega)]
       = zeta(1+2omega(1+u)) zeta(2+4omega) / (zeta(2+4omega(1+u)) zeta(1+2omega)) ,
(5)  Y_omega => Exp(1) ,
(7)  P_omega{a <= Y_omega <= b} -> e^{-a} - e^{-b} ,
(12) P_omega{d <= exp(c/(2 omega))} -> 1 - e^{-c} ,
(13) P_omega{d >  exp(c/(2 omega))} -> e^{-c} ,
(14)/(15) moving apertures: a cutoff whose rescaled logarithm converges to `c` retains
     `1 - e^{-c}`, and full transport happens exactly along cutoffs whose rescaled logarithm
     diverges.
```

Every statement is unconditional.  The card's remaining gates (contractive synthesis on the moving
aperture, the four-unit boundary transfer, RH) are untouched.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

/-- **Card `(2)`.**  The squarefree Dirichlet-series normalization. -/
theorem boundaryLayerPaper_squarefree_total {sigma : ℝ} (hsigma : 1 < sigma) :
    ((squarefreeMobiusTotal sigma : ℝ) : ℂ) =
      riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ)) :=
  ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma

/-- **Card `(1)`.**  The channel law is a probability measure on the divisor index. -/
theorem boundaryLayerPaper_total_mass {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, squarefreeMobiusProbability sigma n) = 1 :=
  tsum_squarefreeMobiusProbability hsigma

/-- **Card `(3)`.**  The law is exactly the normalized squared-norm law of the analysis channel,
independently of the input vector. -/
theorem boundaryLayerPaper_channel_law
    {sigma : ℝ} (hsigma : 1 < sigma) {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) (n : ℕ) :
    ‖mobiusCriticalShiftChannel sigma f n‖ ^ 2 / ‖mobiusCriticalShiftChannel sigma f‖ ^ 2 =
      squarefreeMobiusProbability sigma n :=
  mobiusChannelPaper_coordinate_probability hsigma hf n

/-- **Card `(4)`.**  The rescaled logarithmic divisor coordinate. -/
theorem boundaryLayerPaper_clock (sigma : ℝ) (n : ℕ) :
    squarefreeMobiusCriticalClock sigma n = (sigma - 1) * Real.log n := rfl

/-- The Laplace weight of the clock is the shifted Dirichlet weight. -/
theorem boundaryLayerPaper_laplace_term {sigma u : ℝ} (n : ℕ) :
    squarefreeMobiusProbability sigma n *
        Real.exp (-(u * squarefreeMobiusCriticalClock sigma n))
      = squarefreeMobiusBoundaryLayerTerm sigma u n := by
  rw [squarefreeMobiusBoundaryLayerTerm, squarefreeMobiusCriticalClock]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : squarefreeMobiusProbability sigma 0 = 0 := by
      simp [squarefreeMobiusProbability, squarefreeMobiusMass, not_squarefree_zero]
    simp [hzero]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring

/-- **Card `(8)`.**  The exact Laplace transform of the rescaled clock. -/
theorem boundaryLayerPaper_laplace_transform {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    ((∑' n : ℕ, squarefreeMobiusProbability sigma n *
        Real.exp (-(u * squarefreeMobiusCriticalClock sigma n)) : ℝ) : ℂ)
      = riemannZeta ((sigma + u * (sigma - 1) : ℝ) : ℂ) *
          riemannZeta (2 * (sigma : ℂ)) /
        (riemannZeta (2 * ((sigma + u * (sigma - 1) : ℝ) : ℂ)) * riemannZeta (sigma : ℂ)) := by
  have hparam : 1 < sigma + u * (sigma - 1) := by nlinarith
  have hcong : (∑' n : ℕ, squarefreeMobiusProbability sigma n *
      Real.exp (-(u * squarefreeMobiusCriticalClock sigma n)))
      = ∑' n : ℕ, squarefreeMobiusBoundaryLayerTerm sigma u n :=
    tsum_congr fun n => boundaryLayerPaper_laplace_term n
  rw [hcong, ofReal_tsum_squarefreeMobiusBoundaryLayerTerm,
    squarefreeMobiusBoundaryLayerLaplace, mobiusCriticalBoundaryParameter,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hparam,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
  have h1 : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have h2 : riemannZeta (2 * (sigma : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith
  have h3 : riemannZeta (2 * ((sigma + u * (sigma - 1) : ℝ) : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith
  field_simp

/-- **Card `(6)`.**  The Laplace transform tends to the mean-one exponential transform. -/
theorem boundaryLayerPaper_laplace_limit {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusBoundaryLayerLaplace sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds ((((1 + u : ℝ) : ℂ))⁻¹)) :=
  tendsto_squarefreeMobiusBoundaryLayerLaplace hu

/-- **Card `(5)`.**  Weak convergence of the rescaled clock to the unit exponential law. -/
theorem boundaryLayerPaper_weak_limit :
    Tendsto squarefreeMobiusCriticalClockProbabilityMeasure
      (nhdsWithin 1 (Ioi 1)) (nhds mobiusCriticalExponentialProbabilityMeasure) :=
  tendsto_squarefreeMobiusCriticalClockProbabilityMeasure

/-- **Card `(7)`.** -/
theorem boundaryLayerPaper_window {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Icc a b))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.exp (-a) - Real.exp (-b))) :=
  tendsto_squarefreeMobiusClockMass_Icc ha hab

/-- **Card `(12)`.**  The divisor-coordinate form of the lower quantile. -/
theorem boundaryLayerPaper_lower_quantile {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun sigma : ℝ =>
        ∑' n : ℕ, (Iic (Real.exp (c / (sigma - 1)))).indicator
          (fun _ => squarefreeMobiusProbability sigma n) (n : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-c))) := by
  refine (tendsto_squarefreeMobiusClockMass_Iic hc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact squarefreeMobiusClockMass_Iic_eq_divisorCutoff hsigma hc

/-- **Card `(13)`.** -/
theorem boundaryLayerPaper_upper_quantile {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Ioi c))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.exp (-c))) :=
  tendsto_squarefreeMobiusClockMass_Ioi hc

/-- **Card §3(1).** -/
theorem boundaryLayerPaper_fixed_cutoff (D : ℝ) :
    Tendsto (fun sigma : ℝ =>
        squarefreeMobiusClockMass sigma (Iic ((sigma - 1) * Real.log D)))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
  tendsto_squarefreeMobiusClockMass_fixed_cutoff D

/-- **Card §3(2), §4(15).** -/
theorem boundaryLayerPaper_moving_cutoff {x : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hx : Tendsto x (nhdsWithin 1 (Ioi 1)) (nhds c)) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Iic (x sigma)))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-c))) :=
  tendsto_squarefreeMobiusClockMass_Iic_moving hc hx

/-- **Card §3(4), §4(14).** -/
theorem boundaryLayerPaper_full_transport {x : ℝ → ℝ}
    (hx : Tendsto x (nhdsWithin 1 (Ioi 1)) atTop) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Iic (x sigma)))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
  tendsto_squarefreeMobiusClockMass_Iic_moving_atTop hx

end RHTower
