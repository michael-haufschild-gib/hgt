import GaloisForLFunctions.HTGeometry.KleinGordonUniformEnergy

/-!
# The real potential

Every conservation statement so far assumes an abstract self-adjoint perturbation. This file exhibits
the class the assumption was written for and shows it is not empty: multiplication by a bounded
**real** function of position.

Such an operator is self-adjoint for the reason the classical energy method is: the potential is real,
so the cross terms in the inner product conjugate into each other. Everything then specialises. The
energy `‖⟨D⟩u‖² + ‖∂ₜu‖² − ∫V|u|²` is exactly conserved; a potential of sup-norm less than one gives an
energy bounded uniformly in time; and an *attractive* potential, `V ≤ 0`, needs no smallness at all —
the field stays bounded forever, which is the statement that a clock sitting in a potential well does
not run away.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section RealPotential

variable {V : E → ℝ} {b : ℝ}

omit [NormedAddCommGroup E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_ofReal_potential (hV : Measurable V) :
    Measurable fun a : E => ((V a : ℝ) : ℂ) :=
  Complex.continuous_ofReal.measurable.comp hV

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] in
theorem norm_ofReal_potential_le (hb : ∀ a : E, |V a| ≤ b) (a : E) :
    ‖((V a : ℝ) : ℂ)‖ ≤ b := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hb a

/-- **Multiplication by a bounded real potential**, as an operator on `L²`. -/
def kgMulOp (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ a : E, |V a| ≤ b) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) (measurable_ofReal_potential hV) hb0
    (norm_ofReal_potential_le hb)

theorem norm_kgMulOp_le (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ a : E, |V a| ≤ b) :
    ‖kgMulOp hV hb0 hb‖ ≤ b :=
  norm_lpBoundedMulCLM_le _ _ _

/-- **A real potential is self-adjoint.** -/
theorem inner_kgMulOp (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ a : E, |V a| ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgMulOp hV hb0 hb x) y : ℂ) = inner ℂ x (kgMulOp hV hb0 hb y) :=
  inner_lpBoundedMulCLM_real _ _ _ (fun a => by
    show (starRingEnd ℂ) (((V a : ℝ) : ℂ)) = ((V a : ℝ) : ℂ)
    exact Complex.conj_ofReal _) x y

/-! ## Conservation and the uniform bounds, for a real potential -/

/-- **The energy of the Klein–Gordon field in a real potential is exactly conserved.** -/
theorem kgRealPotential_energy_conserved (hV : Measurable V) (hb0 : 0 ≤ b)
    (hb : ∀ a : E, |V a| ≤ b) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (kgMulOp hV hb0 hb) g h t‖ ^ 2 + ‖kgFieldVel (kgMulOp hV hb0 hb) g h t‖ ^ 2
        - RCLike.re (inner ℂ (kgMulOp hV hb0 hb
            (kgFieldMild (kgMulOp hV hb0 hb) (kgFreqInvOp g) h t))
          (kgFieldMild (kgMulOp hV hb0 hb) (kgFreqInvOp g) h t))
      = ‖g‖ ^ 2 + ‖h‖ ^ 2
        - RCLike.re (inner ℂ (kgMulOp hV hb0 hb (kgFreqInvOp g)) (kgFreqInvOp g)) :=
  kgFieldEnergy_conserved hb0 (norm_kgMulOp_le hV hb0 hb) (inner_kgMulOp hV hb0 hb) g h t

/-- **A real potential of sup-norm less than one gives an energy bounded uniformly in time.** -/
theorem kgRealPotential_energy_uniform (hV : Measurable V) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hb : ∀ a : E, |V a| ≤ b) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (kgMulOp hV hb0 hb) g h t‖ ^ 2 + ‖kgFieldVel (kgMulOp hV hb0 hb) g h t‖ ^ 2
      ≤ (1 + b) / (1 - b) * (‖g‖ ^ 2 + ‖h‖ ^ 2) :=
  kgFieldEnergy_uniform hb0 hb1 (norm_kgMulOp_le hV hb0 hb) (inner_kgMulOp hV hb0 hb) g h t

/-! ## An attractive potential -/

/-- The potential term of a real potential is the integral of `V|x|²`. -/
theorem re_inner_kgMulOp (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ a : E, |V a| ≤ b)
    (x : Lp ℂ 2 (volume : Measure E)) :
    RCLike.re (inner ℂ (kgMulOp hV hb0 hb x) x)
      = RCLike.re ((∫ a : E, ((V a * ‖(x : E → ℂ) a‖ ^ 2 : ℝ) : ℂ)) : ℂ) := by
  congr 1
  rw [kgMulOp, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure E))
    (measurable_ofReal_potential hV) hb0 (norm_ofReal_potential_le hb) x] with a ha
  have hz : (starRingEnd ℂ) ((x : E → ℂ) a) * (x : E → ℂ) a
      = ((‖(x : E → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  have hcast : ((V a * ‖(x : E → ℂ) a‖ ^ 2 : ℝ) : ℂ)
      = ((V a : ℝ) : ℂ) * ((starRingEnd ℂ) ((x : E → ℂ) a) * (x : E → ℂ) a) := by
    rw [hz]
    push_cast
    ring
  rw [ha, RCLike.inner_apply, map_mul, Complex.conj_ofReal, hcast]
  ring

/-- **An attractive real potential keeps the energy below its initial value**, with no smallness
hypothesis at all. -/
theorem kgRealPotential_energy_le_of_nonpos (hV : Measurable V) (hb0 : 0 ≤ b)
    (hb : ∀ a : E, |V a| ≤ b) (hneg : ∀ a : E, V a ≤ 0)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (kgMulOp hV hb0 hb) g h t‖ ^ 2 + ‖kgFieldVel (kgMulOp hV hb0 hb) g h t‖ ^ 2
      ≤ ‖g‖ ^ 2 + ‖h‖ ^ 2
        - RCLike.re (inner ℂ (kgMulOp hV hb0 hb (kgFreqInvOp g)) (kgFreqInvOp g)) := by
  refine kgFieldEnergy_le_of_nonpos hb0 (norm_kgMulOp_le hV hb0 hb) (inner_kgMulOp hV hb0 hb)
    (fun x => ?_) g h t
  rw [re_inner_kgMulOp hV hb0 hb x]
  have hint : (∫ a : E, ((V a * ‖(x : E → ℂ) a‖ ^ 2 : ℝ) : ℂ))
      = (((∫ a : E, V a * ‖(x : E → ℂ) a‖ ^ 2) : ℝ) : ℂ) := integral_ofReal
  have hre : RCLike.re (((∫ a : E, V a * ‖(x : E → ℂ) a‖ ^ 2 : ℝ) : ℂ))
      = ∫ a : E, V a * ‖(x : E → ℂ) a‖ ^ 2 := RCLike.ofReal_re _
  rw [hint, hre]
  refine integral_nonpos ?_
  intro a
  have hsq : (0 : ℝ) ≤ ‖(x : E → ℂ) a‖ ^ 2 := sq_nonneg _
  have := hneg a
  simpa using mul_nonpos_of_nonpos_of_nonneg this hsq

/-- **The field itself stays bounded for all time in an attractive potential.** -/
theorem kgRealPotential_norm_le_of_nonpos (hV : Measurable V) (hb0 : 0 ≤ b)
    (hb : ∀ a : E, |V a| ≤ b) (hneg : ∀ a : E, V a ≤ 0)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild (kgMulOp hV hb0 hb) (kgFreqInvOp g) h t‖ ^ 2
      ≤ ‖g‖ ^ 2 + ‖h‖ ^ 2
        - RCLike.re (inner ℂ (kgMulOp hV hb0 hb (kgFreqInvOp g)) (kgFreqInvOp g)) :=
  (norm_kgFieldMild_sq_le_energy hb0 (norm_kgMulOp_le hV hb0 hb) g h t).trans
    (kgRealPotential_energy_le_of_nonpos hV hb0 hb hneg g h t)

end RealPotential

end GaloisForLFunctions.HTGeometry
