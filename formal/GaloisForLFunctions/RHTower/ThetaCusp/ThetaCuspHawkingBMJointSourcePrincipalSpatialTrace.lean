import GaloisForLFunctions.HTGeometry.L2BesselDistribution
import GaloisForLFunctions.HTGeometry.RealSobolevOddTrace
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalTimeSecondDerivative

/-! Actual continuous radial representatives and the original zero endpoint trace. -/
open MeasureTheory Set Filter Topology TemperedDistribution
open scoped SchwartzMap
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual principal causal response belongs to the full spatial Sobolev domain of order two. -/
theorem principalTimeResponse_memSobolev (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    MemSobolev 2 2 ((principalTimeResponse q branch a i τ : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  rw [principalTimeResponse_wave_graph]
  exact unitWaveEllipticInv_memSobolev _

private theorem principalProfile_exists (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[volume] principalTimeResponse q branch a i τ ∧
      (∀ x : ℝ, f (-x) = -f x) ∧ f 0 = 0 :=
  real_sobolev_odd_zero_trace _ (principalTimeResponse_reflection q branch a i τ) 2 (by norm_num)
    (principalTimeResponse_memSobolev q branch a i τ)

/-- The continuous representative of the original principal response, selected after Sobolev admission. -/
def principalTimeProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) : ℝ → ℂ :=
  Classical.choose (principalProfile_exists q branch a i τ)

theorem principalTimeProfile_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    Continuous (principalTimeProfile q branch a i τ) :=
  (Classical.choose_spec (principalProfile_exists q branch a i τ)).1

/-- The profile is a representative of the actual original response class. -/
theorem principalTimeProfile_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeProfile q branch a i τ =ᵐ[volume] principalTimeResponse q branch a i τ :=
  (Classical.choose_spec (principalProfile_exists q branch a i τ)).2.1

theorem principalTimeProfile_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ x : ℝ) :
    principalTimeProfile q branch a i τ (-x) = -principalTimeProfile q branch a i τ x :=
  (Classical.choose_spec (principalProfile_exists q branch a i τ)).2.2.1 x

/-- The original endpoint has zero pointwise trace, derived from Sobolev regularity and oddness. -/
theorem principalTimeProfile_zero_trace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeProfile q branch a i τ 0 = 0 :=
  (Classical.choose_spec (principalProfile_exists q branch a i τ)).2.2.2

/-- The physical negative-ray boundary limit is the proved original zero trace. -/
theorem principalTimeProfile_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    Tendsto (principalTimeProfile q branch a i τ) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (principalTimeProfile_continuous q branch a i τ).tendsto (0:ℝ)
  rw [principalTimeProfile_zero_trace] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Continuous representatives cannot introduce an arbitrary boundary value on a null set. -/
theorem principalTimeProfile_unique (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) (ha : f =ᵐ[volume] principalTimeResponse q branch a i τ) :
    f = principalTimeProfile q branch a i τ :=
  Measure.eq_of_ae_eq (ha.trans (principalTimeProfile_ae q branch a i τ).symm) hf
    (principalTimeProfile_continuous q branch a i τ)

end
end RHTower.D4BMJointSource
