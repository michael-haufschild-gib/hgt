import GaloisForLFunctions.RHTower.ProlateOscillatorLadderPin

/-!
# Moving the prolate defect onto the oscillator side

The exact prolate-to-oscillator identity leaves the defect

```text
D(ξ) = (ξ² u″(ξ) + 2ξ u′(ξ))/c ,
```

which involves the *unknown* second derivative of the rescaled profile.  Paired against an
oscillator eigenfunction, that dependence disappears: two integrations by parts move both
derivatives onto the Hermite factor, leaving

```text
⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²φₙ″ + 2ξφₙ′⟩ ,
```

and `φₙ″ = (ξ² − 2n − 1)φₙ` makes the right-hand weight completely explicit.  So the defect pairing
needs no estimate on the profile's derivatives at all — only the profile itself, against a fixed
Gaussian-decaying weight.
-/

open MeasureTheory Filter

open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The two Hermite weights -/

/-- The quadratic Hermite weight `ξ² φₙ(ξ)`. -/
def hermiteSqWeight (n : ℕ) (x : ℝ) : ℝ := x ^ 2 * hermiteFun n x

/-- Its derivative. -/
def hermiteSqWeightDeriv (n : ℕ) (x : ℝ) : ℝ :=
  2 * x * hermiteFun n x + x ^ 2 * deriv (hermiteFun n) x

/-- Its second derivative. -/
def hermiteSqWeightSecondDeriv (n : ℕ) (x : ℝ) : ℝ :=
  2 * hermiteFun n x + 4 * x * deriv (hermiteFun n) x
    + x ^ 2 * deriv (deriv (hermiteFun n)) x

/-- The linear Hermite weight `2ξ φₙ(ξ)`. -/
def hermiteLinWeight (n : ℕ) (x : ℝ) : ℝ := 2 * x * hermiteFun n x

/-- Its derivative. -/
def hermiteLinWeightDeriv (n : ℕ) (x : ℝ) : ℝ :=
  2 * hermiteFun n x + 2 * x * deriv (hermiteFun n) x

theorem hasDerivAt_hermiteSqWeight (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteSqWeight n) (hermiteSqWeightDeriv n x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    have h := hasDerivAt_pow 2 x
    refine h.congr_deriv ?_
    norm_num
  have h := hpow.mul (hasDerivAt_ladderHermiteFun n x)
  refine h.congr_deriv ?_
  rw [hermiteSqWeightDeriv]

theorem hasDerivAt_hermiteSqWeightDeriv (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteSqWeightDeriv n) (hermiteSqWeightSecondDeriv n x) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    have h := hasDerivAt_pow 2 x
    refine h.congr_deriv ?_
    norm_num
  have h1 := hlin.mul (hasDerivAt_ladderHermiteFun n x)
  have h2 := hpow.mul (hasDerivAt_deriv_ladderHermiteFun n x)
  have h := h1.add h2
  refine h.congr_deriv ?_
  rw [hermiteSqWeightSecondDeriv]
  ring

theorem hasDerivAt_hermiteLinWeight (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteLinWeight n) (hermiteLinWeightDeriv n x) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h := hlin.mul (hasDerivAt_ladderHermiteFun n x)
  refine h.congr_deriv ?_
  rw [hermiteLinWeightDeriv]

/-- The combined Hermite side is exactly `ξ²φₙ″ + 2ξφₙ′`. -/
theorem hermiteWeight_combination (n : ℕ) (x : ℝ) :
    hermiteSqWeightSecondDeriv n x - hermiteLinWeightDeriv n x
      = x ^ 2 * deriv (deriv (hermiteFun n)) x + 2 * x * deriv (hermiteFun n) x := by
  rw [hermiteSqWeightSecondDeriv, hermiteLinWeightDeriv]
  ring

/-! ## The transfer -/

/-- **The defect pairing moves onto the Hermite side.**  Both derivatives of the profile are
integrated away; what remains pairs the profile itself against an explicit weight. -/
theorem integral_prolateDefect_transfer {u u' u'' : ℝ → ℝ} (n : ℕ)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hiA : Integrable fun x => u'' x * hermiteSqWeight n x)
    (hiB : Integrable fun x => u x * hermiteSqWeightSecondDeriv n x)
    (hiC : Integrable fun x => u' x * hermiteLinWeight n x)
    (hiD : Integrable fun x => u x * hermiteLinWeightDeriv n x)
    (hWplus : Tendsto (fun x => u' x * hermiteSqWeight n x - u x * hermiteSqWeightDeriv n x)
      atTop (𝓝 0))
    (hWminus : Tendsto (fun x => u' x * hermiteSqWeight n x - u x * hermiteSqWeightDeriv n x)
      atBot (𝓝 0))
    (hPplus : Tendsto (fun x => u x * hermiteLinWeight n x) atTop (𝓝 0))
    (hPminus : Tendsto (fun x => u x * hermiteLinWeight n x) atBot (𝓝 0)) :
    (∫ x, u'' x * hermiteSqWeight n x) + (∫ x, u' x * hermiteLinWeight n x)
      = ∫ x, u x * (x ^ 2 * deriv (deriv (hermiteFun n)) x + 2 * x * deriv (hermiteFun n) x) := by
  have h1 : ∫ x, u'' x * hermiteSqWeight n x = ∫ x, u x * hermiteSqWeightSecondDeriv n x :=
    integral_secondDeriv_mul_comm hu (fun x => hasDerivAt_hermiteSqWeight n x) hu'
      (fun x => hasDerivAt_hermiteSqWeightDeriv n x) hiA hiB hWplus hWminus
  have h2 : ∫ x, u' x * hermiteLinWeight n x = -∫ x, u x * hermiteLinWeightDeriv n x :=
    integral_deriv_mul_eq_neg hu (fun x => hasDerivAt_hermiteLinWeight n x) hiC hiD
      hPplus hPminus
  have h3 : ∫ x, u x * (x ^ 2 * deriv (deriv (hermiteFun n)) x + 2 * x * deriv (hermiteFun n) x)
      = (∫ x, u x * hermiteSqWeightSecondDeriv n x) - ∫ x, u x * hermiteLinWeightDeriv n x := by
    rw [← MeasureTheory.integral_sub hiB hiD]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hermiteSqWeightSecondDeriv, hermiteLinWeightDeriv]
    ring
  rw [h1, h2, h3]
  ring

/-- **The defect pairing, fully explicit.**  Using the oscillator equation
`φₙ″ = (ξ² − 2n − 1)φₙ`, the Hermite side involves no derivative of order two at all. -/
theorem integral_prolateDefect_transfer_explicit {u u' u'' : ℝ → ℝ} (n : ℕ)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hiA : Integrable fun x => u'' x * hermiteSqWeight n x)
    (hiB : Integrable fun x => u x * hermiteSqWeightSecondDeriv n x)
    (hiC : Integrable fun x => u' x * hermiteLinWeight n x)
    (hiD : Integrable fun x => u x * hermiteLinWeightDeriv n x)
    (hWplus : Tendsto (fun x => u' x * hermiteSqWeight n x - u x * hermiteSqWeightDeriv n x)
      atTop (𝓝 0))
    (hWminus : Tendsto (fun x => u' x * hermiteSqWeight n x - u x * hermiteSqWeightDeriv n x)
      atBot (𝓝 0))
    (hPplus : Tendsto (fun x => u x * hermiteLinWeight n x) atTop (𝓝 0))
    (hPminus : Tendsto (fun x => u x * hermiteLinWeight n x) atBot (𝓝 0)) :
    (∫ x, u'' x * hermiteSqWeight n x) + (∫ x, u' x * hermiteLinWeight n x)
      = ∫ x, u x * (x ^ 2 * (x ^ 2 - 2 * n - 1) * hermiteFun n x
          + 2 * x * deriv (hermiteFun n) x) := by
  rw [integral_prolateDefect_transfer n hu hu' hiA hiB hiC hiD hWplus hWminus hPplus hPminus]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [deriv2_hermiteFun]
  ring

/-! ## The sharpened ladder pin -/

/-- **The ladder pin with the defect on the Hermite side.**  Combining `hermitePairing_pin` with the
transfer, the distance from the rescaled eigenvalue to the `n`-th rung is a pairing of the profile
itself against a fixed explicit Gaussian-decaying weight, divided by the bandwidth.  No derivative
of the profile survives. -/
theorem prolateLadder_pin_hermiteSide {u u' u'' D : ℝ → ℝ} {c μ : ℝ} (n : ℕ) (hc : c ≠ 0)
    (hpin : (μ - (2 * n + 1)) * (∫ x, u x * hermiteFun n x) = ∫ x, D x * hermiteFun n x)
    (hD : ∀ x, D x = (x ^ 2 * u'' x + 2 * x * u' x) / c)
    (htransfer : (∫ x, u'' x * hermiteSqWeight n x) + (∫ x, u' x * hermiteLinWeight n x)
      = ∫ x, u x * (x ^ 2 * (x ^ 2 - 2 * n - 1) * hermiteFun n x
          + 2 * x * deriv (hermiteFun n) x))
    (hiA : Integrable fun x => u'' x * hermiteSqWeight n x)
    (hiC : Integrable fun x => u' x * hermiteLinWeight n x) :
    (μ - (2 * n + 1)) * (∫ x, u x * hermiteFun n x)
      = (∫ x, u x * (x ^ 2 * (x ^ 2 - 2 * n - 1) * hermiteFun n x
          + 2 * x * deriv (hermiteFun n) x)) / c := by
  have hsplit : ∫ x, D x * hermiteFun n x
      = ((∫ x, u'' x * hermiteSqWeight n x) + ∫ x, u' x * hermiteLinWeight n x) / c := by
    have hpt : ∀ x, D x * hermiteFun n x
        = (u'' x * hermiteSqWeight n x + u' x * hermiteLinWeight n x) / c := by
      intro x
      rw [hD x, hermiteSqWeight, hermiteLinWeight]
      field_simp
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_div, MeasureTheory.integral_add hiA hiC]
  rw [hpin, hsplit, htransfer]

end RHTower

end
