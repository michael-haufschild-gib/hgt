import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality

open MeasureTheory Complex ContinuousLinearMap

/-!
# Literal rotating-cylinder material overlap on all spatial modes

The cylinder cutoff and angular helicities act as bounded L² multiplication
operators on an arbitrary measurable spatial geometry. Their adjoints and
sandwich coefficients are identified pointwise almost everywhere. No spatial
mode truncation is made. This is the source material-overlap layer, not the
Maxwell differential/interface boundary map or a conormal landing.
-/

namespace RHTower

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

noncomputable def ptrCylinderSymbol (C : Set X) (x : X) : ℂ := by
  classical
  exact if x ∈ C then 1 else 0

theorem ptrCylinderSymbol_measurable (C : Set X) (hC : MeasurableSet C) :
    Measurable (ptrCylinderSymbol C) := by
  classical
  exact Measurable.ite hC measurable_const measurable_const

omit [MeasurableSpace X] in
theorem ptrCylinderSymbol_norm_le (C : Set X) (x : X) :
    ‖ptrCylinderSymbol C x‖ ≤ 1 := by
  by_cases hx : x ∈ C <;> simp [ptrCylinderSymbol, hx]

def ptrHelicalSymbol (m : ℤ) (θ : X → ℝ) (x : X) : ℂ :=
  GaloisForLFunctions.HTGeometry.rotatingPositiveHarmonic m (θ x) 0 0

theorem ptrHelicalSymbol_measurable (m : ℤ) (θ : X → ℝ)
    (hθ : Measurable θ) : Measurable (ptrHelicalSymbol m θ) := by
  unfold ptrHelicalSymbol
  unfold GaloisForLFunctions.HTGeometry.rotatingPositiveHarmonic
    GaloisForLFunctions.HTGeometry.rotatingModulationPhase
  fun_prop

omit [MeasurableSpace X] in
theorem ptrHelicalSymbol_norm (m : ℤ) (θ : X → ℝ) (x : X) :
    ‖ptrHelicalSymbol m θ x‖ = 1 := by
  exact GaloisForLFunctions.HTGeometry.norm_rotatingPositiveHarmonic m (θ x) 0 0

omit [MeasurableSpace X] in
theorem ptrHelicalSymbol_conj (m : ℤ) (θ : X → ℝ) (x : X) :
    (starRingEnd ℂ) (ptrHelicalSymbol m θ x) =
      GaloisForLFunctions.HTGeometry.rotatingNegativeHarmonic m (θ x) 0 0 := by
  unfold ptrHelicalSymbol
  unfold GaloisForLFunctions.HTGeometry.rotatingPositiveHarmonic
    GaloisForLFunctions.HTGeometry.rotatingNegativeHarmonic
  rw [← Complex.exp_conj]
  congr 1
  simp

def ptrNegativeHelicalSymbol (m : ℤ) (θ : X → ℝ) (x : X) : ℂ :=
  GaloisForLFunctions.HTGeometry.rotatingNegativeHarmonic m (θ x) 0 0

theorem ptrNegativeHelicalSymbol_measurable (m : ℤ) (θ : X → ℝ)
    (hθ : Measurable θ) : Measurable (ptrNegativeHelicalSymbol m θ) := by
  unfold ptrNegativeHelicalSymbol
  unfold GaloisForLFunctions.HTGeometry.rotatingNegativeHarmonic
    GaloisForLFunctions.HTGeometry.rotatingModulationPhase
  fun_prop

omit [MeasurableSpace X] in
theorem ptrNegativeHelicalSymbol_norm (m : ℤ) (θ : X → ℝ) (x : X) :
    ‖ptrNegativeHelicalSymbol m θ x‖ = 1 := by
  exact GaloisForLFunctions.HTGeometry.norm_rotatingNegativeHarmonic m (θ x) 0 0

omit [MeasurableSpace X] in
theorem ptrCylinderSymbol_conj (C : Set X) (x : X) :
    (starRingEnd ℂ) (ptrCylinderSymbol C x) = ptrCylinderSymbol C x := by
  simp [ptrCylinderSymbol]

def ptrCylinderL2Cutoff (C : Set X) (hC : MeasurableSet C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (p := 2) (μ := μ)
    (ptrCylinderSymbol_measurable C hC) (by positivity)
    (ptrCylinderSymbol_norm_le C)

theorem ptrCylinderL2Cutoff_adjoint (C : Set X) (hC : MeasurableSet C) :
    (ptrCylinderL2Cutoff μ C hC).adjoint = ptrCylinderL2Cutoff μ C hC := by
  symm
  exact GaloisForLFunctions.HTGeometry.lpBoundedMulCLM_eq_adjoint_conj_general
    (ptrCylinderSymbol_measurable C hC) (by positivity)
    (ptrCylinderSymbol_norm_le C)
    (ptrCylinderSymbol_measurable C hC) (by positivity)
    (ptrCylinderSymbol_norm_le C)
    (fun x => (ptrCylinderSymbol_conj C x).symm)

def ptrHelicalL2Multiplier (u : X → ℂ) (hu : Measurable u)
    (hu1 : ∀ x, ‖u x‖ ≤ 1) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (p := 2) (μ := μ) hu (by positivity) hu1

theorem ptrHelicalL2Multiplier_norm_le (u : X → ℂ) (hu : Measurable u)
    (hu1 : ∀ x, ‖u x‖ ≤ 1) : ‖ptrHelicalL2Multiplier μ u hu hu1‖ ≤ 1 :=
  norm_lpBoundedMulCLM_le hu (by positivity) hu1

theorem ptrHelicalL2Multiplier_adjoint (m : ℤ) (θ : X → ℝ)
    (hθ : Measurable θ) :
    (ptrHelicalL2Multiplier μ (ptrHelicalSymbol m θ) (ptrHelicalSymbol_measurable m θ hθ)
      (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x))).adjoint =
    ptrHelicalL2Multiplier μ (ptrNegativeHelicalSymbol m θ)
      (ptrNegativeHelicalSymbol_measurable m θ hθ)
      (fun x => le_of_eq (ptrNegativeHelicalSymbol_norm m θ x)) := by
  symm
  exact GaloisForLFunctions.HTGeometry.lpBoundedMulCLM_eq_adjoint_conj_general
    (ptrHelicalSymbol_measurable m θ hθ) (by positivity)
    (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x))
    (ptrNegativeHelicalSymbol_measurable m θ hθ) (by positivity)
    (fun x => le_of_eq (ptrNegativeHelicalSymbol_norm m θ x))
    (fun x => (ptrHelicalSymbol_conj m θ x).symm)

theorem ptrCylinderHelicalAction (C : Set X) (hC : MeasurableSet C)
    (u : X → ℂ) (hu : Measurable u) (hu1 : ∀ x, ‖u x‖ ≤ 1)
    (f : Lp ℂ 2 μ) :
    (((ptrCylinderL2Cutoff μ C hC).adjoint ((ptrHelicalL2Multiplier μ u hu hu1) ((ptrCylinderL2Cutoff μ C hC) f)) : Lp ℂ 2 μ) : X → ℂ)
      =ᵐ[μ] fun x => ptrCylinderSymbol C x * u x * (f : X → ℂ) x := by
  rw [ptrCylinderL2Cutoff_adjoint]
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ)
      (ptrCylinderSymbol_measurable C hC) (by positivity)
      (ptrCylinderSymbol_norm_le C) ((ptrHelicalL2Multiplier μ u hu hu1) ((ptrCylinderL2Cutoff μ C hC) f)),
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hu (by positivity) hu1 ((ptrCylinderL2Cutoff μ C hC) f),
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ)
      (ptrCylinderSymbol_measurable C hC) (by positivity)
      (ptrCylinderSymbol_norm_le C) f] with x hB hU hBf
  dsimp only [ptrCylinderL2Cutoff, ptrHelicalL2Multiplier] at hB hU hBf ⊢
  rw [hB, hU, hBf]
  by_cases hx : x ∈ C <;> simp [ptrCylinderSymbol, hx]

theorem ptrCylinderPositiveHelicalAction (C : Set X) (hC : MeasurableSet C)
    (m : ℤ) (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    (((ptrCylinderL2Cutoff μ C hC).adjoint
      ((ptrHelicalL2Multiplier μ (ptrHelicalSymbol m θ) (ptrHelicalSymbol_measurable m θ hθ)
        (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x)))
        ((ptrCylinderL2Cutoff μ C hC) f)) : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
      fun x => ptrCylinderSymbol C x * ptrHelicalSymbol m θ x * (f : X → ℂ) x :=
  ptrCylinderHelicalAction μ C hC (ptrHelicalSymbol m θ)
    (ptrHelicalSymbol_measurable m θ hθ)
    (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x)) f

theorem ptrCylinderNegativeHelicalAction (C : Set X) (hC : MeasurableSet C)
    (m : ℤ) (θ : X → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    (((ptrCylinderL2Cutoff μ C hC).adjoint
      (((ptrHelicalL2Multiplier μ (ptrHelicalSymbol m θ) (ptrHelicalSymbol_measurable m θ hθ)
        (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x))).adjoint)
        ((ptrCylinderL2Cutoff μ C hC) f)) : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
      fun x => ptrCylinderSymbol C x * ptrNegativeHelicalSymbol m θ x * (f : X → ℂ) x := by
  rw [ptrHelicalL2Multiplier_adjoint μ m θ hθ]
  exact ptrCylinderHelicalAction μ C hC (ptrNegativeHelicalSymbol m θ)
    (ptrNegativeHelicalSymbol_measurable m θ hθ)
    (fun x => le_of_eq (ptrNegativeHelicalSymbol_norm m θ x)) f

theorem ptrCylinderPositiveOverlapIntegral (C : Set X) (hC : MeasurableSet C)
    (m : ℤ) (θ : X → ℝ) (hθ : Measurable θ)
    (f g : Lp ℂ 2 μ) :
    inner ℂ f
      ((ptrCylinderL2Cutoff μ C hC).adjoint
        ((ptrHelicalL2Multiplier μ (ptrHelicalSymbol m θ) (ptrHelicalSymbol_measurable m θ hθ)
          (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x)))
          ((ptrCylinderL2Cutoff μ C hC) g))) =
      ∫ x, (starRingEnd ℂ) ((f : X → ℂ) x) *
        ptrCylinderSymbol C x * ptrHelicalSymbol m θ x * (g : X → ℂ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ptrCylinderPositiveHelicalAction μ C hC m θ hθ g] with x hx
  rw [hx, RCLike.inner_apply']
  ring

theorem ptrCylinderNegativeOverlapIntegral (C : Set X) (hC : MeasurableSet C)
    (m : ℤ) (θ : X → ℝ) (hθ : Measurable θ)
    (f g : Lp ℂ 2 μ) :
    inner ℂ f
      ((ptrCylinderL2Cutoff μ C hC).adjoint
        (((ptrHelicalL2Multiplier μ (ptrHelicalSymbol m θ) (ptrHelicalSymbol_measurable m θ hθ)
          (fun x => le_of_eq (ptrHelicalSymbol_norm m θ x))).adjoint)
          ((ptrCylinderL2Cutoff μ C hC) g))) =
      ∫ x, (starRingEnd ℂ) ((f : X → ℂ) x) *
        ptrCylinderSymbol C x * ptrNegativeHelicalSymbol m θ x * (g : X → ℂ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ptrCylinderNegativeHelicalAction μ C hC m θ hθ g] with x hx
  rw [hx, RCLike.inner_apply']
  ring

end

end RHTower
