import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSeedHorizonCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat

/-!
# Literal full-angular source-horizon trace

The actual branch-dependent direct-minus-image angular kernel reaches the
same literal horizon kernel used by `seedCapField`.  This is a kernel-level
realization, before integration against the original onset derivative.

Proof-chain role:
`full causal kernel horizon trace -> literal seed cap -> strong cap weak
equation -> QNM-cutoff/contact identity -> HB B2`.
-/

open Filter Topology

namespace RHTower.D4BMFullAngularSourceHorizonTrace

open D4BMHorizon D4BMModularCore D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularGoursat
open D4BMFutureSeedHorizon

noncomputable section
set_option autoImplicit false

private theorem closedFullMean_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (fun z : ℝ => angularMean q branch (Real.arcosh (max 1 z)) X k) :=
  (angularMean_smooth q branch X k).continuous.comp
    (Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun z => le_max_left 1 z))

private theorem fullCone_source_horizon (q : XiZeroCopy) (branch : Bool)
    (tau x v X k : ℝ) :
    Tendsto (fun y => if |x-y| ≤ v-tau-y then
      fullAngularRiemannKernel q branch (v-tau-y) x y X k else 0) atBot
      (𝓝 (halfKernel q branch tau x v X k)) := by
  have he : (fun y => if |x-y| ≤ v-tau-y then
      fullAngularRiemannKernel q branch (v-tau-y) x y X k else 0) =ᶠ[atBot]
      (fun y => if tau+x ≤ v then angularMean q branch
        (Real.arcosh (max 1 (invariant (v-tau-y) x y))) X k else 0) := by
    filter_upwards [eventually_le_atBot x] with y hy
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    have hc : x-y ≤ v-tau-y ↔ tau+x ≤ v := by constructor <;> intro h <;> linarith
    simp only [hc]
    split_ifs with h
    · have hz := invariant_causal
        (⟨v-tau-y, x, y, by rw [abs_of_nonneg (sub_nonneg.mpr hy)]; linarith⟩ : CausalPoint)
      rw [fullAngularRiemannKernel_eq_angularMean, max_eq_right hz]
    · rfl
  apply Filter.Tendsto.congr' he.symm
  rw [halfKernel_eq_angularMean]
  split_ifs
  · exact (closedFullMean_continuous q branch X k).continuousAt.tendsto.comp
      (D4BMFutureHorizon.invariant_source_horizon tau x v)
  · exact tendsto_const_nhds

/-- The literal branch-dependent full direct-minus-image kernel has precisely
the source-horizon trace defining `horizonKernel`. -/
theorem fullAngularDirichletKernel_source_horizon (q : XiZeroCopy) (branch : Bool)
    (tau x v X k : ℝ) :
    Tendsto (fun y => angularDirichletKernel q branch (v-tau-y) x y X k) atBot
      (𝓝 (horizonKernel q branch tau x v X k)) := by
  have h := ((fullCone_source_horizon q branch tau x v X k).sub
    (fullCone_source_horizon q branch tau (-x) v X k)).div_const (2 : ℂ)
  convert h using 1
  funext y
  have he : invariant (v-tau-y) (-x) y = invariant (v-tau-y) x (-y) := by
    simp [invariant, Real.sinh_neg, Real.cosh_neg]
  have ha : |(-x)-y| = |x+y| := by
    rw [show -x-y = -(x+y) by ring, abs_neg]
  unfold angularDirichletKernel horizonKernel
  rw [ha, he]
  simp only [fullAngularRiemannKernel_eq_angularMean]

end

end RHTower.D4BMFullAngularSourceHorizonTrace
