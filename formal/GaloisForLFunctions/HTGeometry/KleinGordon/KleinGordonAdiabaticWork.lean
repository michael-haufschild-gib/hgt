import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonAdiabatic

/-!
# The work integral, and a background switched on in time

Two completions of the adiabatic estimate.

First the sharp form. The work–energy identity is a derivative; integrating it gives the exact
accounting

`E(t) − E(0) = −∫₀ᵗ re⟪Ẇ(s)u(s), u(s)⟫ ds`,

so the energy the field gains is literally the work the background does on it, with no inequality
anywhere. The exponential bound is what one gets by discarding the sign of the integrand.

Then a concrete instance, so that none of this is vacuous. A fixed real potential switched on and off
by a scalar profile, `W(t) = φ(t)·W₀`, is a moving self-adjoint background whose norm derivative is
`φ̇(t)·W₀` — the hypotheses of the adiabatic estimate reduce to bounds on `φ` and `φ̇`. This is the
setup a clock in a background of varying strength actually sits in.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The exact work integral -/

section Work

variable {W Wd : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- The work density is continuous. -/
theorem continuous_kgWorkDensity (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hWL : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (hWds : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => Wd r y)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun s : ℝ => RCLike.re (inner ℂ (Wd s (kgFieldMildT W (kgFreqInvOp g) h s))
      (kgFieldMildT W (kgFreqInvOp g) h s)) := by
  have hcu : Continuous (kgFieldMildT W (kgFreqInvOp g) h) :=
    continuous_kgFieldMildT hb0 hWb hWs _ h
  have hWu : Continuous fun s : ℝ => Wd s (kgFieldMildT W (kgFreqInvOp g) h s) :=
    continuous_of_strong_comp hWL hWds continuous_id hcu
  exact (RCLike.reCLM (K := ℂ)).continuous.comp (hWu.inner hcu)

/-- **The exact work accounting.** The energy the field gains is the work the background does on
it — an identity, with no inequality anywhere. -/
theorem kgAdiabaticEnergy_sub (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hsa : ∀ (r : ℝ) (x y : Lp ℂ 2 (volume : Measure E)),
      (inner ℂ (W r x) y : ℂ) = inner ℂ x (W r y))
    (hWd : ∀ r : ℝ, HasDerivAt W (Wd r) r) (hWL : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (hWds : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => Wd r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy W g h t - kgAdiabaticEnergy W g h 0
      = -∫ s in (0 : ℝ)..t, RCLike.re (inner ℂ (Wd s (kgFieldMildT W (kgFreqInvOp g) h s))
          (kgFieldMildT W (kgFreqInvOp g) h s)) := by
  have hcont := continuous_kgWorkDensity hb0 hWb hWs hWL hWds g h
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (kgAdiabaticEnergy W g h)
      (-RCLike.re (inner ℂ (Wd s (kgFieldMildT W (kgFreqInvOp g) h s))
        (kgFieldMildT W (kgFreqInvOp g) h s))) s := fun s _ =>
    hasDerivAt_kgAdiabaticEnergy hb0 hWb hWs hsa hWd g h s
  have hint : IntervalIntegrable
      (fun s : ℝ => -RCLike.re (inner ℂ (Wd s (kgFieldMildT W (kgFreqInvOp g) h s))
        (kgFieldMildT W (kgFreqInvOp g) h s))) volume 0 t :=
    (hcont.neg).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hFTC, intervalIntegral.integral_neg]

/-- **The work is bounded by the drift times the accumulated field.** -/
theorem abs_kgAdiabaticEnergy_sub_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hsa : ∀ (r : ℝ) (x y : Lp ℂ 2 (volume : Measure E)),
      (inner ℂ (W r x) y : ℂ) = inner ℂ x (W r y))
    (hWd : ∀ r : ℝ, HasDerivAt W (Wd r) r) (hL0 : 0 ≤ L) (hWL : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (hWds : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => Wd r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    |kgAdiabaticEnergy W g h t - kgAdiabaticEnergy W g h 0|
      ≤ L * ((‖g‖ + ‖h‖) * Real.exp (b * |t|)) ^ (2 : ℕ) * |t| := by
  have hD0 : (0 : ℝ) ≤ ‖g‖ + ‖h‖ := by positivity
  have hgf : ‖kgFreqInvOp (E := E) g‖ ≤ ‖g‖ := by
    have hc := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le g
    rwa [one_mul] at hc
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖RCLike.re (inner ℂ (Wd s (kgFieldMildT W (kgFreqInvOp g) h s))
        (kgFieldMildT W (kgFreqInvOp g) h s))‖
        ≤ L * ((‖g‖ + ‖h‖) * Real.exp (b * |t|)) ^ (2 : ℕ) := by
    intro s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 : ‖kgFieldMildT W (kgFreqInvOp g) h s‖
        ≤ (‖kgFreqInvOp (E := E) g‖ + ‖h‖) * Real.exp (b * |s|) :=
      norm_kgFieldMildT_le hb0 hWb hWs _ h s
    have hexp : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h2 : ‖kgFieldMildT W (kgFreqInvOp g) h s‖ ≤ (‖g‖ + ‖h‖) * Real.exp (b * |t|) := by
      refine h1.trans ?_
      exact mul_le_mul (by linarith) hexp (Real.exp_pos _).le hD0
    have h3 : ‖kgFieldMildT W (kgFreqInvOp g) h s‖ ^ (2 : ℕ)
        ≤ ((‖g‖ + ‖h‖) * Real.exp (b * |t|)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 := abs_re_inner_potential_le (hWL s) (kgFieldMildT W (kgFreqInvOp g) h s)
    rw [Real.norm_eq_abs]
    calc |RCLike.re (inner ℂ (Wd s (kgFieldMildT W (kgFreqInvOp g) h s))
          (kgFieldMildT W (kgFreqInvOp g) h s))|
        ≤ L * ‖kgFieldMildT W (kgFreqInvOp g) h s‖ ^ (2 : ℕ) := h4
      _ ≤ L * ((‖g‖ + ‖h‖) * Real.exp (b * |t|)) ^ (2 : ℕ) := mul_le_mul_of_nonneg_left h3 hL0
  rw [kgAdiabaticEnergy_sub hb0 hWb hWs hsa hWd hWL hWds g h t, abs_neg,
    ← Real.norm_eq_abs]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rwa [sub_zero] at hle

end Work

/-! ## A background switched on in time -/

section Scaled

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {φ φ' : ℝ → ℝ}

/-- A fixed perturbation switched on and off by a scalar profile. -/
def kgScaledPotential (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (φ : ℝ → ℝ) (t : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  ((φ t : ℝ) : ℂ) • W₀

theorem norm_kgScaledPotential (t : ℝ) :
    ‖kgScaledPotential W₀ φ t‖ = |φ t| * ‖W₀‖ := by
  rw [kgScaledPotential, norm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem inner_kgScaledPotential
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (t : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgScaledPotential W₀ φ t x) y : ℂ) = inner ℂ x (kgScaledPotential W₀ φ t y) := by
  show (inner ℂ (((φ t : ℝ) : ℂ) • W₀ x) y : ℂ) = inner ℂ x (((φ t : ℝ) : ℂ) • W₀ y)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hsa x y]

theorem continuous_kgScaledPotential_apply (hφ : Continuous φ)
    (y : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun r : ℝ => kgScaledPotential W₀ φ r y :=
  (Complex.continuous_ofReal.comp hφ).smul continuous_const

/-- **The switched background is norm-differentiable**, with derivative the switched derivative. -/
theorem hasDerivAt_kgScaledPotential (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r) (t : ℝ) :
    HasDerivAt (kgScaledPotential W₀ φ) (kgScaledPotential W₀ φ' t) t := by
  have hc : HasDerivAt (fun s : ℝ => ((φ s : ℝ) : ℂ)) (((φ' t : ℝ) : ℂ)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hφ t)
  exact hc.smul_const W₀

/-- **The adiabatic estimate for a background switched on in time.** The hypotheses reduce to bounds
on the profile and on its derivative. -/
theorem kgScaledPotential_energy_le
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r) {b L : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hφb : ∀ r : ℝ, |φ r| * ‖W₀‖ ≤ b) (hL0 : 0 ≤ L) (hφL : ∀ r : ℝ, |φ' r| * ‖W₀‖ ≤ L)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy (kgScaledPotential W₀ φ) g h t
      ≤ kgAdiabaticEnergy (kgScaledPotential W₀ φ) g h 0
        * Real.exp (L / (1 - b) * |t|) := by
  have hφd : Differentiable ℝ φ := fun r => (hφ r).differentiableAt
  have hφc : Continuous φ := hφd.continuous
  refine kgAdiabaticEnergy_le hb0 hb1 (fun r => by rw [norm_kgScaledPotential]; exact hφb r)
    (fun y => continuous_kgScaledPotential_apply hφc y) (fun r => inner_kgScaledPotential hsa r)
    (fun r => hasDerivAt_kgScaledPotential hφ r) hL0
    (fun r => by rw [norm_kgScaledPotential]; exact hφL r) g h t

end Scaled

end GaloisForLFunctions.HTGeometry
