import GaloisForLFunctions.HTGeometry.LikelihoodJuliaLift
import GaloisForLFunctions.HTGeometry.LikelihoodPolarizationInformation
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.L2MellinUnitary

/-!
# The reflected binary experiment realizes the likelihood Julia datum

A probability law together with a measurable involution produces a reflected pair.  Its balanced
law is reflection invariant, its posterior contrast is reflection odd, and multiplication by the
truncated contrast and by the visibility, together with the Koopman operator of the involution,
satisfy exactly the axioms of a likelihood Julia datum.  Every conclusion of that abstract theory
therefore holds for the reflected experiment.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- `(LPC.9)`  A reflected binary experiment: a source law and a measurable involution. -/
structure ReflectedPair (X : Type*) [MeasurableSpace X] where
  /-- The source law `P`. -/
  source : Measure X
  isProb : IsProbabilityMeasure source
  /-- The reflection `R`. -/
  reflection : X → X
  measurable_reflection : Measurable reflection
  reflection_involutive : ∀ x, reflection (reflection x) = x

namespace ReflectedPair

variable (E : ReflectedPair X)

instance : IsProbabilityMeasure E.source := E.isProb

/-- `(LPC.9)`  The reflected law `Q = R∗P`. -/
def target : Measure X := E.source.map E.reflection

instance isProbabilityMeasure_target : IsProbabilityMeasure E.target := by
  rw [target]
  constructor
  rw [Measure.map_apply E.measurable_reflection MeasurableSet.univ]
  simp

/-- The reflection as a measurable equivalence. -/
def reflectionEquiv : X ≃ᵐ X where
  toFun := E.reflection
  invFun := E.reflection
  left_inv := E.reflection_involutive
  right_inv := E.reflection_involutive
  measurable_toFun := E.measurable_reflection
  measurable_invFun := E.measurable_reflection

theorem map_target : E.target.map E.reflection = E.source := by
  rw [target, Measure.map_map E.measurable_reflection E.measurable_reflection]
  have : E.reflection ∘ E.reflection = id := funext E.reflection_involutive
  rw [this, Measure.map_id]

/-- `(LPC.11)`  The balanced law is reflection invariant. -/
theorem map_balanced :
    (balancedLaw E.source E.target).map E.reflection = balancedLaw E.source E.target := by
  rw [balancedLaw, Measure.map_smul, Measure.map_add _ _ E.measurable_reflection,
    ← target, E.map_target, add_comm]

theorem measurePreserving_reflection :
    MeasurePreserving E.reflection (balancedLaw E.source E.target)
      (balancedLaw E.source E.target) :=
  ⟨E.measurable_reflection, E.map_balanced⟩

/-! ## The contrast is reflection odd -/

/-- `(LPC.11)`  The posterior contrast of a reflected pair is reflection odd. -/
theorem clamp_neg (t : ℝ) : max (-1) (min 1 (-t)) = -max (-1) (min 1 t) := by
  rcases le_total t (-1) with h | h
  · rw [min_eq_right (le_trans h (by norm_num : (-1:ℝ) ≤ 1)), max_eq_left h,
      min_eq_left (by linarith : (1:ℝ) ≤ -t), max_eq_right (by norm_num : (-1:ℝ) ≤ 1)]
    norm_num
  · rcases le_total (1:ℝ) t with h' | h'
    · rw [min_eq_left h', max_eq_right (by norm_num : (-1:ℝ) ≤ 1),
        min_eq_right (by linarith : -t ≤ 1), max_eq_left (by linarith : -t ≤ -1)]
    · rw [min_eq_right h', max_eq_right h, min_eq_right (by linarith : -t ≤ 1),
        max_eq_right (by linarith : (-1:ℝ) ≤ -t)]

/-- `(LPC.11)`  The posterior contrast of a reflected pair is reflection odd. -/
theorem posteriorContrast_reflection :
    (fun x => posteriorContrast E.source E.target (E.reflection x))
      =ᵐ[balancedLaw E.source E.target] fun x => -posteriorContrast E.source E.target x := by
  have hemb : MeasurableEmbedding E.reflection := E.reflectionEquiv.measurableEmbedding
  have hmap := hemb.rnDeriv_map E.target (balancedLaw E.source E.target)
  rw [E.map_target, E.map_balanced] at hmap
  filter_upwards [hmap, rnDeriv_right_toReal E.source E.target] with x h1 h2
  have hd : posteriorContrast E.source E.target (E.reflection x)
      = (E.source.rnDeriv (balancedLaw E.source E.target) (E.reflection x)).toReal - 1 := rfl
  have hd' : posteriorContrast E.source E.target x
      = (E.source.rnDeriv (balancedLaw E.source E.target) x).toReal - 1 := rfl
  rw [hd, h1, h2, hd']
  ring

/-- `(LPC.11)`  The truncated contrast is reflection odd. -/
theorem truncContrast_reflection :
    (fun x => truncContrast E.source E.target (E.reflection x))
      =ᵐ[balancedLaw E.source E.target] fun x => -truncContrast E.source E.target x := by
  filter_upwards [E.posteriorContrast_reflection] with x hx
  rw [truncContrast, truncContrast, hx, clamp_neg]

/-! ## The likelihood symbols -/

/-- `(LPC.3)`  The complex contrast symbol `d`. -/
def contrastSymbol : X → ℂ := fun x => (truncContrast E.source E.target x : ℂ)

/-- `(LPC.3)`  The complex visibility symbol `a = √(1 - d²)`. -/
def visibilitySymbol : X → ℂ :=
  fun x => ((Real.sqrt (1 - (truncContrast E.source E.target x) ^ 2) : ℝ) : ℂ)

theorem measurable_contrastSymbol : Measurable E.contrastSymbol :=
  Complex.measurable_ofReal.comp (measurable_truncContrast _ _)

theorem measurable_visibilitySymbol : Measurable E.visibilitySymbol :=
  Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp
      (measurable_const.sub ((measurable_truncContrast _ _).pow_const 2)))

theorem sq_truncContrast_le_one (x : X) : (truncContrast E.source E.target x) ^ 2 ≤ 1 := by
  have h := abs_truncContrast_le_one E.source E.target x
  nlinarith [abs_nonneg (truncContrast E.source E.target x),
    sq_abs (truncContrast E.source E.target x)]

theorem norm_contrastSymbol_le_one (x : X) : ‖E.contrastSymbol x‖ ≤ 1 := by
  rw [contrastSymbol, Complex.norm_real, Real.norm_eq_abs]
  exact abs_truncContrast_le_one _ _ x

theorem norm_visibilitySymbol_le_one (x : X) : ‖E.visibilitySymbol x‖ ≤ 1 := by
  rw [visibilitySymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  linarith [sq_nonneg (truncContrast E.source E.target x)]

theorem visibilitySymbol_sq_add_contrastSymbol_sq (x : X) :
    E.visibilitySymbol x * E.visibilitySymbol x + E.contrastSymbol x * E.contrastSymbol x = 1 := by
  rw [visibilitySymbol, contrastSymbol, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_add]
  norm_cast
  rw [← sq, ← sq, Real.sq_sqrt (by linarith [E.sq_truncContrast_le_one x])]
  ring

theorem conj_contrastSymbol (x : X) : (starRingEnd ℂ) (E.contrastSymbol x) = E.contrastSymbol x :=
  Complex.conj_ofReal _

theorem conj_visibilitySymbol (x : X) :
    (starRingEnd ℂ) (E.visibilitySymbol x) = E.visibilitySymbol x :=
  Complex.conj_ofReal _

/-! ## The likelihood operators -/

/-- `(LPC.5)`  Multiplication by the visibility symbol on `L²` of the balanced law. -/
def visibilityOp : Lp ℂ 2 (balancedLaw E.source E.target) →L[ℂ]
    Lp ℂ 2 (balancedLaw E.source E.target) :=
  lpBoundedMulCLM (p := 2) (μ := balancedLaw E.source E.target) E.measurable_visibilitySymbol
    zero_le_one E.norm_visibilitySymbol_le_one

/-- `(LPC.5)`  Multiplication by the contrast symbol on `L²` of the balanced law. -/
def contrastOp : Lp ℂ 2 (balancedLaw E.source E.target) →L[ℂ]
    Lp ℂ 2 (balancedLaw E.source E.target) :=
  lpBoundedMulCLM (p := 2) (μ := balancedLaw E.source E.target) E.measurable_contrastSymbol
    zero_le_one E.norm_contrastSymbol_le_one

theorem visibilityOp_coeFn (f : Lp ℂ 2 (balancedLaw E.source E.target)) :
    (E.visibilityOp f : X → ℂ) =ᵐ[balancedLaw E.source E.target]
      fun x => E.visibilitySymbol x * (f : X → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem contrastOp_coeFn (f : Lp ℂ 2 (balancedLaw E.source E.target)) :
    (E.contrastOp f : X → ℂ) =ᵐ[balancedLaw E.source E.target]
      fun x => E.contrastSymbol x * (f : X → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- `(LPC.10)`  The Koopman operator of the reflection. -/
def koopmanOp : Lp ℂ 2 (balancedLaw E.source E.target) →L[ℂ]
    Lp ℂ 2 (balancedLaw E.source E.target) :=
  (Lp.compMeasurePreservingₗᵢ ℂ E.reflection E.measurePreserving_reflection).toContinuousLinearMap

theorem koopmanOp_coeFn (f : Lp ℂ 2 (balancedLaw E.source E.target)) :
    (E.koopmanOp f : X → ℂ) =ᵐ[balancedLaw E.source E.target] (f : X → ℂ) ∘ E.reflection :=
  Lp.coeFn_compMeasurePreserving f E.measurePreserving_reflection

/-! ## The realization -/

theorem isSelfAdjoint_visibilityOp : IsSelfAdjoint E.visibilityOp := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _ |>.mpr fun f g => ?_).symm
  exact lpBoundedMulCLM_inner_real _ _ _ E.conj_visibilitySymbol f g

theorem isSelfAdjoint_contrastOp : IsSelfAdjoint E.contrastOp := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _ |>.mpr fun f g => ?_).symm
  exact lpBoundedMulCLM_inner_real _ _ _ E.conj_contrastSymbol f g

theorem visibilityOp_sq_add_contrastOp_sq :
    E.visibilityOp ∘L E.visibilityOp + E.contrastOp ∘L E.contrastOp
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 (balancedLaw E.source E.target)) := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (E.visibilityOp (E.visibilityOp f)) (E.contrastOp (E.contrastOp f)),
    E.visibilityOp_coeFn (E.visibilityOp f), E.visibilityOp_coeFn f,
    E.contrastOp_coeFn (E.contrastOp f), E.contrastOp_coeFn f] with x h0 h1 h2 h3 h4
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [h0]
  simp only [Pi.add_apply]
  rw [h1, h2, h3, h4,
    show E.visibilitySymbol x * (E.visibilitySymbol x * (f : X → ℂ) x)
        + E.contrastSymbol x * (E.contrastSymbol x * (f : X → ℂ) x)
      = (E.visibilitySymbol x * E.visibilitySymbol x
        + E.contrastSymbol x * E.contrastSymbol x) * (f : X → ℂ) x by ring,
    E.visibilitySymbol_sq_add_contrastSymbol_sq, one_mul]

theorem visibilityOp_contrastOp_comm :
    E.visibilityOp ∘L E.contrastOp = E.contrastOp ∘L E.visibilityOp := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [E.visibilityOp_coeFn (E.contrastOp f), E.contrastOp_coeFn f,
    E.contrastOp_coeFn (E.visibilityOp f), E.visibilityOp_coeFn f] with x h1 h2 h3 h4
  simp only [ContinuousLinearMap.comp_apply]
  rw [h1, h2, h3, h4]
  ring

theorem ae_comp_reflection {g₁ g₂ : X → ℂ}
    (h : g₁ =ᵐ[balancedLaw E.source E.target] g₂) :
    g₁ ∘ E.reflection =ᵐ[balancedLaw E.source E.target] g₂ ∘ E.reflection :=
  h.comp_tendsto E.measurePreserving_reflection.quasiMeasurePreserving.tendsto_ae

theorem koopmanOp_koopmanOp (f : Lp ℂ 2 (balancedLaw E.source E.target)) :
    E.koopmanOp (E.koopmanOp f) = f := by
  refine Lp.ext ?_
  have hae := E.ae_comp_reflection (E.koopmanOp_coeFn f)
  filter_upwards [E.koopmanOp_coeFn (E.koopmanOp f), hae] with x h1 h2
  rw [h1]
  show (E.koopmanOp f : X → ℂ) (E.reflection x) = (f : X → ℂ) x
  have : ((E.koopmanOp f : X → ℂ) ∘ E.reflection) x
      = (((f : X → ℂ) ∘ E.reflection) ∘ E.reflection) x := h2
  simpa [Function.comp, E.reflection_involutive] using this

theorem koopmanOp_involutive :
    E.koopmanOp ∘L E.koopmanOp
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 (balancedLaw E.source E.target)) :=
  ContinuousLinearMap.ext fun f => E.koopmanOp_koopmanOp f

theorem isSelfAdjoint_koopmanOp : IsSelfAdjoint E.koopmanOp := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _ |>.mpr fun f g => ?_).symm
  have hiso : ∀ u v : Lp ℂ 2 (balancedLaw E.source E.target),
      (inner ℂ (E.koopmanOp u) (E.koopmanOp v) : ℂ) = inner ℂ u v := fun u v =>
    (Lp.compMeasurePreservingₗᵢ ℂ E.reflection E.measurePreserving_reflection).inner_map_map u v
  calc (inner ℂ (E.koopmanOp f) g : ℂ)
      = inner ℂ (E.koopmanOp f) (E.koopmanOp (E.koopmanOp g)) := by rw [E.koopmanOp_koopmanOp]
    _ = inner ℂ f (E.koopmanOp g) := hiso f (E.koopmanOp g)

theorem visibilitySymbol_reflection :
    (fun x => E.visibilitySymbol (E.reflection x))
      =ᵐ[balancedLaw E.source E.target] E.visibilitySymbol := by
  filter_upwards [E.truncContrast_reflection] with x hx
  rw [visibilitySymbol, visibilitySymbol, hx]
  norm_num

theorem contrastSymbol_reflection :
    (fun x => E.contrastSymbol (E.reflection x))
      =ᵐ[balancedLaw E.source E.target] fun x => -E.contrastSymbol x := by
  filter_upwards [E.truncContrast_reflection] with x hx
  rw [contrastSymbol, contrastSymbol, hx, Complex.ofReal_neg]

theorem koopmanOp_visibilityOp :
    E.koopmanOp ∘L E.visibilityOp = E.visibilityOp ∘L E.koopmanOp := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have h1 := E.ae_comp_reflection (E.visibilityOp_coeFn f)
  filter_upwards [E.koopmanOp_coeFn (E.visibilityOp f), h1, E.visibilityOp_coeFn (E.koopmanOp f),
    E.koopmanOp_coeFn f, E.visibilitySymbol_reflection] with x k1 k2 k3 k4 k5
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply] at k1 k2 k3 k4 ⊢
  rw [k1, k2, k3, k4, k5]

theorem koopmanOp_contrastOp :
    E.koopmanOp ∘L E.contrastOp = -(E.contrastOp ∘L E.koopmanOp) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have h1 := E.ae_comp_reflection (E.contrastOp_coeFn f)
  filter_upwards [E.koopmanOp_coeFn (E.contrastOp f), h1,
    Lp.coeFn_neg (E.contrastOp (E.koopmanOp f)), E.contrastOp_coeFn (E.koopmanOp f),
    E.koopmanOp_coeFn f, E.contrastSymbol_reflection] with x k1 k2 k3 k4 k5 k6
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    Function.comp_apply, Pi.neg_apply] at k1 k2 k3 k4 k5 ⊢
  rw [k1, k2, k3, k4, k5, k6]
  ring

/-- **Theorem 2.1.**  A reflected binary experiment realizes a likelihood Julia datum. -/
def juliaDatum : LikelihoodJuliaDatum (Lp ℂ 2 (balancedLaw E.source E.target)) where
  visibility := E.visibilityOp
  contrast := E.contrastOp
  visibility_isSelfAdjoint := E.isSelfAdjoint_visibilityOp
  contrast_isSelfAdjoint := E.isSelfAdjoint_contrastOp
  sq_add_sq := E.visibilityOp_sq_add_contrastOp_sq
  visibility_contrast_comm := E.visibilityOp_contrastOp_comm
  koopman := E.koopmanOp
  koopman_isSelfAdjoint := E.isSelfAdjoint_koopmanOp
  koopman_involutive := E.koopmanOp_involutive
  koopman_visibility := E.koopmanOp_visibilityOp
  koopman_contrast := E.koopmanOp_contrastOp

end ReflectedPair

end

end GaloisForLFunctions.HTGeometry
