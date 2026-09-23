import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceEquation
import GaloisForLFunctions.HTGeometry.EuclideanSobolevLaplacianGain
import GaloisForLFunctions.HTGeometry.RealSobolevOddTrace

/-! The genuine Laplace response lies in the original spatial domain and has zero endpoint trace. -/
open MeasureTheory Set Filter Topology TemperedDistribution
open scoped SchwartzMap Laplacian
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual transformed equation places its Laplacian in the original L² space. -/
theorem principalTimeLaplace_laplacian (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      ((w^(2 : ℕ) • principalTimeLaplace q branch a i w-
        (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t)-
          principalRadialPotentialOp q i (principalTimeLaplace q branch a i w) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  let D := Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
  let U := principalTimeLaplace q branch a i w
  let F := ∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t
  let V := principalRadialPotentialOp q i U
  have h := principalTimeLaplace_distribution_equation q branch a i w hw
  change w^(2 : ℕ) • D U-Δ (D U) = D F+D V at h
  change Δ (D U) = D (w^(2 : ℕ) • U-F-V)
  rw [map_sub,map_sub,map_smul]
  have he := congrArg (fun z : 𝓢'(ℝ,ℂ) => w^(2 : ℕ) • D U-z) h
  convert he using 1 <;> abel

/-- Sobolev regularity belongs to the transformed response itself, before any trace is evaluated. -/
theorem principalTimeLaplace_memSobolev (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    MemSobolev 2 2 ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  have hu : MemSobolev 0 2 ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) :=
    memSobolev_zero_iff.mpr ⟨_,rfl⟩
  have hd : MemSobolev 0 2 (Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ))) := by
    rw [principalTimeLaplace_laplacian q branch a i w hw]
    exact memSobolev_zero_iff.mpr ⟨_,rfl⟩
  simpa only [zero_add] using euclidean_sobolev_gain_two hu hd

private theorem laplaceProfile_exists (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[volume] principalTimeLaplace q branch a i w ∧
      (∀ x : ℝ, f (-x) = -f x) ∧ f 0 = 0 :=
  real_sobolev_odd_zero_trace _ (principalTimeLaplace_reflection q branch a i w hw) 2 (by norm_num)
    (principalTimeLaplace_memSobolev q branch a i w hw)

/-- The continuous spatial representative of the actual norm-convergent causal transform. -/
def principalLaplaceProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) : ℝ → ℂ :=
  Classical.choose (laplaceProfile_exists q branch a i w hw)

theorem principalLaplaceProfile_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    Continuous (principalLaplaceProfile q branch a i w hw) :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).1

theorem principalLaplaceProfile_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    principalLaplaceProfile q branch a i w hw =ᵐ[volume] principalTimeLaplace q branch a i w :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).2.1

theorem principalLaplaceProfile_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (x : ℝ) :
    principalLaplaceProfile q branch a i w hw (-x) = -principalLaplaceProfile q branch a i w hw x :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).2.2.1 x

/-- The original endpoint trace is derived from the transformed Sobolev domain and oddness. -/
theorem principalLaplaceProfile_zero_trace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    principalLaplaceProfile q branch a i w hw 0 = 0 :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).2.2.2

theorem principalLaplaceProfile_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    Tendsto (principalLaplaceProfile q branch a i w hw) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (principalLaplaceProfile_continuous q branch a i w hw).tendsto (0:ℝ)
  rw [principalLaplaceProfile_zero_trace] at h
  exact h.mono_left nhdsWithin_le_nhds

end
end RHTower.D4BMJointSource
