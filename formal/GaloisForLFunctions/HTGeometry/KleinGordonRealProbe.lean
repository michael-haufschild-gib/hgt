import GaloisForLFunctions.HTGeometry.WienerSynthesisContinuity

/-!
# The real probe

A clock probe is a real-valued field, so the complex construction has to be read through its real
part. That is legitimate exactly when the potential is real, and the potential is real exactly when
the convolving density obeys the reality condition

`a(-η) = conj a(η)`,

because then the conjugate of the potential is the same integral after the substitution `η ↦ -η`.
Under that condition the real part of the field satisfies the same equation — the real part is a
continuous linear map, so it commutes with every derivative — and it is positive at the event where
the datum was concentrated.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] {N : ℕ}

/-! ## Real potentials -/

/-- The reality condition on a convolving density. -/
def IsRealDensity (a : WienerDensity E N) : Prop :=
  ∀ η : E, a (-η) = (starRingEnd ℂ) (a η)

/-- The reality condition on a time-dependent potential. -/
def IsRealFamily (A : WienerFamily E N) : Prop := ∀ t : ℝ, IsRealDensity (A.density t)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgChar_neg (x η : E) : kgChar x (-η) = (starRingEnd ℂ) (kgChar x η) := by
  rw [kgChar, kgChar, inner_neg_left, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- **A density obeying the reality condition has a real potential.** -/
theorem conj_kgPotential {a : WienerDensity E N} (h : IsRealDensity a) (x : E) :
    (starRingEnd ℂ) (kgPotential a x) = kgPotential a x := by
  rw [kgPotential, ← integral_conj]
  have hstep : ∀ η : E, (starRingEnd ℂ) (kgChar x η * a η) = kgChar x (-η) * a (-η) := by
    intro η
    rw [map_mul, kgChar_neg, h η]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
  exact integral_neg_eq_self (fun η : E => kgChar x η * a η) (volume : Measure E)

theorem kgPotential_im {a : WienerDensity E N} (h : IsRealDensity a) (x : E) :
    (kgPotential a x).im = 0 := by
  have hconj := conj_kgPotential h x
  exact Complex.conj_eq_iff_im.mp hconj

/-! ## Real parts of derivatives -/

theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun r : ℝ => (f r).re) f'.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

theorem deriv_re_eq {f : ℝ → ℂ} (hf : ∀ t : ℝ, DifferentiableAt ℝ f t) (t : ℝ) :
    deriv (fun r : ℝ => (f r).re) t = (deriv f t).re :=
  (hasDerivAt_re (hf t).hasDerivAt).deriv

theorem deriv_deriv_re_eq {f : ℝ → ℂ} (hf : ∀ t : ℝ, DifferentiableAt ℝ f t)
    (hf2 : ∀ t : ℝ, DifferentiableAt ℝ (deriv f) t) (t : ℝ) :
    deriv (deriv fun r : ℝ => (f r).re) t = (deriv (deriv f) t).re := by
  have hfun : (deriv fun r : ℝ => (f r).re) = fun r : ℝ => (deriv f r).re := by
    funext r
    exact deriv_re_eq hf r
  rw [hfun]
  exact (hasDerivAt_re (hf2 t).hasDerivAt).deriv

/-! ## The real field -/

/-- The real part of the field: the clock probe. -/
noncomputable def kgRealField (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (x : E) : ℝ :=
  (kgFlowField a G₀ t x).re

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

theorem differentiableAt_kgFlowField_time (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (x : E)
    (t : ℝ) : DifferentiableAt ℝ (fun r : ℝ => kgFlowField a G₀ r x) t :=
  (hasDerivAt_kgFlowField hN a G₀ x t).differentiableAt

theorem differentiableAt_deriv_kgFlowField_time (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (x : E)
    (t : ℝ) : DifferentiableAt ℝ (deriv fun r : ℝ => kgFlowField a G₀ r x) t :=
  (hasDerivAt_deriv_kgFlowField hN a G₀ x t).differentiableAt

theorem differentiableAt_kgFlowField_dir (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ)
    (x v : E) (s : ℝ) :
    DifferentiableAt ℝ (fun q : ℝ => kgFlowField a G₀ t (x + q • v)) s :=
  (hasDerivAt_kgSynthesis_dir_synthesis ((continuous_kgFlowDensity a G₀ t).aestronglyMeasurable)
    (integrable_kgFlowDensity a G₀ hN t) (integrable_kgFreq_mul_kgFlowDensity a G₀ hN t)
    x v s).differentiableAt

theorem deriv_kgFlowField_dir_eq (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ) (x v : E)
    (s : ℝ) :
    deriv (fun q : ℝ => kgFlowField a G₀ t (x + q • v)) s
      = kgSynthesis (kgDirDensity v (kgFlowDensity a G₀ t)) (x + s • v) :=
  (hasDerivAt_kgSynthesis_dir_synthesis ((continuous_kgFlowDensity a G₀ t).aestronglyMeasurable)
    (integrable_kgFlowDensity a G₀ hN t) (integrable_kgFreq_mul_kgFlowDensity a G₀ hN t)
    x v s).deriv

theorem differentiableAt_deriv_kgFlowField_dir (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ)
    (x v : E) (s : ℝ) :
    DifferentiableAt ℝ (deriv fun q : ℝ => kgFlowField a G₀ t (x + q • v)) s := by
  have hfun : (deriv fun q : ℝ => kgFlowField a G₀ t (x + q • v))
      = fun q : ℝ => kgSynthesis (kgDirDensity v (kgFlowDensity a G₀ t)) (x + q • v) := by
    funext q
    exact deriv_kgFlowField_dir_eq a G₀ hN t x v q
  rw [hfun]
  exact (hasDerivAt_kgSynthesis_dir_dir ((continuous_kgFlowDensity a G₀ t).aestronglyMeasurable)
    (integrable_kgFreq_mul_kgFlowDensity a G₀ hN t)
    (integrable_kgFreq_sq_mul_kgFlowDensity a G₀ hN t) x v v s).differentiableAt

/-- **The real field solves the Klein–Gordon equation with a real potential.** -/
theorem kgRealField_wave_equation (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (hreal : IsRealFamily a) (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    deriv (deriv fun r : ℝ => kgRealField a G₀ r x) t
      = ((2 * Real.pi) ^ 2 : ℝ)⁻¹
          * ∑ i, deriv (deriv fun s : ℝ => kgRealField a G₀ t (x + s • b i)) 0
        - kgRealField a G₀ t x
        + (kgPotential (a.density t) x).re * kgRealField a G₀ t x := by
  have hcomplex := kgFlowField_wave_equation a G₀ hN b t x
  have hLHS : deriv (deriv fun r : ℝ => kgRealField a G₀ r x) t
      = (deriv (deriv fun r : ℝ => kgFlowField a G₀ r x) t).re :=
    deriv_deriv_re_eq (differentiableAt_kgFlowField_time a G₀ hN x)
      (differentiableAt_deriv_kgFlowField_time a G₀ hN x) t
  have hdir : ∀ i : ι, deriv (deriv fun s : ℝ => kgRealField a G₀ t (x + s • b i)) 0
      = (deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • b i)) 0).re := fun i =>
    deriv_deriv_re_eq (differentiableAt_kgFlowField_dir a G₀ hN t x (b i))
      (differentiableAt_deriv_kgFlowField_dir a G₀ hN t x (b i)) 0
  have hcast : (((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹ = ((((2 * Real.pi) ^ 2)⁻¹ : ℝ) : ℂ) :=
    (Complex.ofReal_inv _).symm
  rw [hcast] at hcomplex
  have hsum : (∑ i, deriv (deriv fun s : ℝ => kgRealField a G₀ t (x + s • b i)) 0)
      = (∑ i, deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • b i)) 0).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => hdir i
  have him := kgPotential_im (hreal t) x
  rw [hLHS, hcomplex, hsum]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, him, zero_mul, sub_zero,
    Complex.ofReal_re, Complex.ofReal_im, kgRealField]

/-! ## The real probe at the event -/

/-- **The real probe is positive at the event.** -/
theorem kgRealField_zero_pos (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (x₀ : E) :
    0 < kgRealField a (kgConjChar x₀) 0 x₀ := by
  rw [kgRealField, kgFlowField_zero_eq_ofReal, Complex.ofReal_re]
  exact integral_kgFreq_inv_pow_succ_pos (E := E) hN

/-- **The real probe is nonzero on a neighbourhood of the event.** -/
theorem eventually_kgRealField_ne_zero (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (x₀ : E) :
    ∀ᶠ p : ℝ × E in nhds (0, x₀), kgRealField a (kgConjChar x₀) p.1 p.2 ≠ 0 := by
  have hcont : ContinuousAt (fun p : ℝ × E => kgRealField a (kgConjChar x₀) p.1 p.2) (0, x₀) :=
    Complex.continuous_re.continuousAt.comp (continuousAt_kgFlowField hN a (kgConjChar x₀) 0 x₀)
  exact hcont.eventually_ne (kgRealField_zero_pos a hN x₀).ne'

end GaloisForLFunctions.HTGeometry
