import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialDirichletDomain
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadialDirichletTrace

/-! A continuous original physical response with its proved zero tortoise endpoint. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual complete response has a continuous physical representative with the original Dirichlet endpoint. -/
theorem physicalCuspResponse_continuous_zero_trace (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[radialMeasure] physicalCuspResponse q r branch w a hw hd hwi hwr ∧
      (∀ t : ℝ, 0 ≤ t → f t = 0) :=
  radialDirichlet_zero_trace ⟨_,physicalCuspResponse_radialDirichlet_mem q r branch w a hw hd hwi hwr⟩

/-- A continuous representative of the actual original physical response, fixed by its zero extension. -/
def physicalCuspProfile (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) : ℝ → ℂ :=
  (physicalCuspResponse_continuous_zero_trace q r branch w a hw hd hwi hwr).choose

theorem physicalCuspProfile_continuous (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    Continuous (physicalCuspProfile q r branch w a hw hd hwi hwr) :=
  (physicalCuspResponse_continuous_zero_trace q r branch w a hw hd hwi hwr).choose_spec.1

theorem physicalCuspProfile_ae (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspProfile q r branch w a hw hd hwi hwr =ᵐ[radialMeasure]
      physicalCuspResponse q r branch w a hw hd hwi hwr :=
  (physicalCuspResponse_continuous_zero_trace q r branch w a hw hd hwi hwr).choose_spec.2.1

/-- The endpoint value belongs to the original physical response, rather than a newly imposed solution condition. -/
theorem physicalCuspProfile_zero (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspProfile q r branch w a hw hd hwi hwr 0 = 0 :=
  (physicalCuspResponse_continuous_zero_trace q r branch w a hw hd hwi hwr).choose_spec.2.2 0 le_rfl

/-- The actual physical response has zero boundary limit from inside the original tortoise interval. -/
theorem physicalCuspProfile_boundary (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    Tendsto (physicalCuspProfile q r branch w a hw hd hwi hwr) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (physicalCuspProfile_continuous q r branch w a hw hd hwi hwr).tendsto 0
  rw [physicalCuspProfile_zero] at h
  exact h.mono_left inf_le_left

end
end RHTower.D4BMJointSource
