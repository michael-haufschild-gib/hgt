import GaloisForLFunctions.RHTower.SuzukiParityHankelDecomposition
import GaloisForLFunctions.RHTower.SuzukiToeplitzSechWall

/-!
# The midpoint reflection realizes the abstract reflection of the `sech` wall

The common Toeplitz channel is the difference form `∫ K(x−y) φ(y) ψ(x)`, which depends on the
kernel only through differences.  Midpoint reflection `x ↦ a − x` therefore leaves it invariant as
soon as the kernel is even, because the substitution `(x,y) ↦ (a−x, a−y)` is measure preserving and
sends `x − y` to `y − x`.

The two exponential sources of the half-interval are exchanged by exactly that reflection:
`exp x = e^a · (exp ∘ (a − ·))⁻` on the nose.  So the abstract hypotheses of the `sech` wall —
symmetry, bilinearity, reflection invariance and the source relation `u = e^a • J v` — are all
realized by the literal Toeplitz form and the literal sources, and the abstract conclusion
`b u u = e^{2a} b v v` becomes a statement about them.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The midpoint reflection -/

/-- Midpoint reflection of the half-interval `(0, a)`. -/
def midpointReflect (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (a - x)

theorem measurePreserving_reflBoth (a : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ => (a - p.1, a - p.2))
      (volume.prod volume) (volume.prod volume) :=
  (Measure.measurePreserving_sub_left volume a).prod
    (Measure.measurePreserving_sub_left volume a)

theorem measurableEmbedding_reflBoth (a : ℝ) :
    MeasurableEmbedding (fun p : ℝ × ℝ => (a - p.1, a - p.2)) :=
  ((MeasurableEquiv.subLeft a).prodCongr (MeasurableEquiv.subLeft a)).measurableEmbedding

theorem integral_comp_reflBoth (a : ℝ) (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, F (a - p.1, a - p.2)) = ∫ p : ℝ × ℝ, F p := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact (measurePreserving_reflBoth a).integral_comp (measurableEmbedding_reflBoth a) F

/-- **The difference form is invariant under midpoint reflection.** -/
theorem diffBilinForm_midpointReflect (a : ℝ) (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    diffBilinForm K (midpointReflect a φ) (midpointReflect a ψ) = diffBilinForm K φ ψ := by
  rw [diffBilinForm, diffBilinForm]
  rw [← integral_comp_reflBoth a (fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1)]
  refine integral_congr_ae ?_
  filter_upwards with p
  have hsub : (a - p.1) - (a - p.2) = -(p.1 - p.2) := by ring
  simp only [midpointReflect]
  rw [hsub, hK]

/-! ## The exponential sources -/

/-- The rising exponential source. -/
def expRise : ℝ → ℝ := fun x => Real.exp x

/-- The decaying exponential source. -/
def expDecay : ℝ → ℝ := fun x => Real.exp (-x)

/-- **The midpoint reflection exchanges the two exponential sources.** -/
theorem expRise_eq_exp_smul_midpointReflect (a : ℝ) :
    expRise = Real.exp a • midpointReflect a expDecay := by
  funext x
  simp only [expRise, midpointReflect, expDecay, Pi.smul_apply, smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

/-! ## The realized reflection identity -/

/-- **`(229)`'s reflection input, realized.**  For an even kernel the rising-source energy is
`e^{2a}` times the decaying-source energy. -/
theorem diffBilinForm_expRise_eq (a : ℝ) (K : ℝ → ℝ) (hK : ∀ t, K (-t) = K t)
    (hsymm : ∀ φ ψ : ℝ → ℝ, diffBilinForm K φ ψ = diffBilinForm K ψ φ) :
    diffBilinForm K expRise expRise
      = Real.exp (2 * a) * diffBilinForm K expDecay expDecay := by
  refine RHTower.energy_of_reflected (b := diffBilinForm K) (J := midpointReflect a)
    (fun c x y => ?_) hsymm (fun x y => diffBilinForm_midpointReflect a K x y hK)
    (expRise_eq_exp_smul_midpointReflect a)
  rw [diffBilinForm, diffBilinForm, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with p
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Symmetry and homogeneity of the two channels -/

theorem integral_comp_swap (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, F (p.2, p.1)) = ∫ p : ℝ × ℝ, F p := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact Measure.measurePreserving_swap.integral_comp
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding F

/-- **The Toeplitz channel is symmetric for an even kernel.** -/
theorem diffBilinForm_symm (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    diffBilinForm K φ ψ = diffBilinForm K ψ φ := by
  rw [diffBilinForm, diffBilinForm]
  rw [← integral_comp_swap (fun p : ℝ × ℝ => K (p.1 - p.2) * ψ p.2 * φ p.1)]
  refine integral_congr_ae ?_
  filter_upwards with p
  have hsub : p.2 - p.1 = -(p.1 - p.2) := by ring
  rw [hsub, hK]
  ring

/-- **The Hankel channel is symmetric for any kernel.** -/
theorem sumBilinForm_symm (K φ ψ : ℝ → ℝ) :
    sumBilinForm K φ ψ = sumBilinForm K ψ φ := by
  rw [sumBilinForm, sumBilinForm]
  rw [← integral_comp_swap (fun p : ℝ × ℝ => K (p.1 + p.2) * ψ p.2 * φ p.1)]
  refine integral_congr_ae ?_
  filter_upwards with p
  have hadd : p.2 + p.1 = p.1 + p.2 := by ring
  rw [hadd]
  ring

theorem diffBilinForm_smul_left (c : ℝ) (K φ ψ : ℝ → ℝ) :
    diffBilinForm K (c • φ) ψ = c * diffBilinForm K φ ψ := by
  rw [diffBilinForm, diffBilinForm, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with p
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem sumBilinForm_smul_left (c : ℝ) (K φ ψ : ℝ → ℝ) :
    sumBilinForm K (c • φ) ψ = c * sumBilinForm K φ ψ := by
  rw [sumBilinForm, sumBilinForm, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with p
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **`(229)`'s reflection input, with symmetry discharged.** -/
theorem diffBilinForm_expRise_eq_of_even (a : ℝ) (K : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    diffBilinForm K expRise expRise
      = Real.exp (2 * a) * diffBilinForm K expDecay expDecay :=
  diffBilinForm_expRise_eq a K hK (fun φ ψ => diffBilinForm_symm K φ ψ hK)

/-! ## The Hankel channel under midpoint reflection -/

/-- **`(280)`'s reflected kernel law.**  Midpoint reflection does not preserve the Hankel channel:
it reflects the kernel about `2a`. -/
theorem sumBilinForm_midpointReflect (a : ℝ) (K φ ψ : ℝ → ℝ) :
    sumBilinForm K (midpointReflect a φ) (midpointReflect a ψ)
      = sumBilinForm (fun t => K (2 * a - t)) φ ψ := by
  rw [sumBilinForm, sumBilinForm]
  rw [← integral_comp_reflBoth a (fun p : ℝ × ℝ => K (2 * a - (p.1 + p.2)) * φ p.2 * ψ p.1)]
  refine integral_congr_ae ?_
  filter_upwards with p
  have hadd : (2 : ℝ) * a - ((a - p.1) + (a - p.2)) = p.1 + p.2 := by ring
  simp only [midpointReflect]
  rw [hadd]

end GaloisForLFunctions.RHTower
