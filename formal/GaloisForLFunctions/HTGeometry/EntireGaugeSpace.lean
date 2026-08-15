import GaloisForLFunctions.HTGeometry.ExpJetPolynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# The compact-open Baire space of entire gauges

Entire functions form a closed linear subspace of the compact-open space of continuous maps
`ℂ → ℂ`, by the Weierstrass theorem on locally uniform limits of holomorphic functions.  It is
therefore completely metrizable and Baire, which is what a genericity argument over gauges needs.

Differentiation acts continuously on this space, again by Weierstrass, so every jet coordinate
`(g, z) ↦ g^{(k)}(z)` is jointly continuous.  Adding a polynomial with prescribed coefficients is
a continuous finite-dimensional chart through any prescribed gauge.
-/

open Filter Function Set TopologicalSpace Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Entire functions form a complex linear subspace of the compact-open continuous-map space. -/
def entireGaugeSubmodule : Submodule ℂ C(ℂ, ℂ) where
  carrier := {f | Differentiable ℂ ⇑f}
  zero_mem' := by
    show Differentiable ℂ (fun _ : ℂ => (0 : ℂ))
    exact differentiable_const 0
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    exact hf.const_smul c

/-- Compact-open entire gauges. -/
abbrev EntireGauge := entireGaugeSubmodule

noncomputable instance entireGauge_addCommGroup : AddCommGroup EntireGauge :=
  @Submodule.addCommGroup ℂ C(ℂ, ℂ) inferInstance inferInstance inferInstance entireGaugeSubmodule

noncomputable instance entireGauge_continuousAdd : ContinuousAdd EntireGauge :=
  continuousAdd_induced entireGaugeSubmodule.subtype

noncomputable instance entireGauge_continuousSMul : ContinuousSMul ℂ EntireGauge :=
  continuousSMul_induced entireGaugeSubmodule.subtype

theorem differentiable_entireGauge (g : EntireGauge) : Differentiable ℂ ⇑(g : C(ℂ, ℂ)) := g.2

/-- Entire functions are sequentially closed under compact-open convergence. -/
theorem isSeqClosed_differentiable : IsSeqClosed {f : C(ℂ, ℂ) | Differentiable ℂ ⇑f} := by
  intro u f hu huf
  have hloc : TendstoLocallyUniformly (fun n => ⇑(u n)) ⇑f atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp huf
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (⇑(u n)) Set.univ := by
    filter_upwards [] with n
    exact (hu n).differentiableOn
  have hlimit := hloc.tendstoLocallyUniformlyOn.differentiableOn hdiff isOpen_univ
  intro z
  simpa only [differentiableWithinAt_univ] using hlimit z (Set.mem_univ z)

theorem isClosed_differentiable : IsClosed {f : C(ℂ, ℂ) | Differentiable ℂ ⇑f} :=
  isSeqClosed_differentiable.isClosed

noncomputable instance entireGauge_complete : CompleteSpace EntireGauge :=
  isClosed_differentiable.completeSpace_coe

noncomputable instance entireGauge_completelyMetrizable :
    IsCompletelyMetrizableSpace EntireGauge :=
  isClosed_differentiable.isCompletelyMetrizableSpace

/-- The compact-open entire gauge space is Baire. -/
noncomputable instance entireGauge_baire : BaireSpace EntireGauge := by infer_instance

/-! ### Differentiation is continuous -/

/-- The derivative of an entire gauge, again an entire gauge. -/
def gaugeDeriv (g : EntireGauge) : EntireGauge :=
  ⟨⟨deriv ⇑(g : C(ℂ, ℂ)),
    (differentiable_iteratedDeriv_of_entire g.2 1).continuous.congr
      (fun z => by rw [iteratedDeriv_one])⟩,
   by
     have h := differentiable_iteratedDeriv_of_entire g.2 1
     rwa [iteratedDeriv_one] at h⟩

@[simp] theorem gaugeDeriv_apply (g : EntireGauge) (z : ℂ) :
    (gaugeDeriv g : C(ℂ, ℂ)) z = deriv ⇑(g : C(ℂ, ℂ)) z := rfl

theorem coe_gaugeDeriv (g : EntireGauge) :
    ⇑((gaugeDeriv g : C(ℂ, ℂ))) = deriv ⇑(g : C(ℂ, ℂ)) := rfl

/-- **Differentiation is compact-open continuous on entire gauges.** -/
theorem continuous_gaugeDeriv : Continuous (gaugeDeriv) := by
  rw [continuous_iff_seqContinuous]
  intro u g hu
  have hval : Tendsto (fun n => ((u n : C(ℂ, ℂ)))) atTop (𝓝 (g : C(ℂ, ℂ))) :=
    tendsto_subtype_rng.mp hu
  have hloc : TendstoLocallyUniformly (fun n => ⇑((u n : C(ℂ, ℂ)))) ⇑(g : C(ℂ, ℂ)) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hval
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (⇑((u n : C(ℂ, ℂ)))) Set.univ := by
    filter_upwards [] with n
    exact (u n).2.differentiableOn
  have hderiv := hloc.tendstoLocallyUniformlyOn.deriv hdiff isOpen_univ
  rw [tendstoLocallyUniformlyOn_univ] at hderiv
  rw [tendsto_subtype_rng]
  refine ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr ?_
  exact hderiv

/-- The `k`-th derivative of an entire gauge. -/
def gaugeIteratedDeriv (k : ℕ) : EntireGauge → EntireGauge := gaugeDeriv^[k]

theorem coe_gaugeIteratedDeriv (k : ℕ) (g : EntireGauge) :
    ⇑((gaugeIteratedDeriv k g : C(ℂ, ℂ))) = iteratedDeriv k ⇑(g : C(ℂ, ℂ)) := by
  induction k generalizing g with
  | zero => funext z; simp [gaugeIteratedDeriv, iteratedDeriv_zero]
  | succ k ih =>
      have hstep : gaugeIteratedDeriv (k + 1) g = gaugeIteratedDeriv k (gaugeDeriv g) := by
        rw [gaugeIteratedDeriv, Function.iterate_succ_apply]
        rfl
      rw [hstep, ih (gaugeDeriv g), coe_gaugeDeriv, iteratedDeriv_succ']

theorem continuous_gaugeIteratedDeriv (k : ℕ) : Continuous (gaugeIteratedDeriv k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
      have : gaugeIteratedDeriv (k + 1) = gaugeIteratedDeriv k ∘ gaugeDeriv := by
        funext g
        rw [gaugeIteratedDeriv, Function.iterate_succ_apply]
        rfl
      rw [this]
      exact ih.comp continuous_gaugeDeriv

/-- **Every jet coordinate is jointly continuous in the gauge and the point.** -/
theorem continuous_gaugeJetEval (k : ℕ) :
    Continuous (fun p : EntireGauge × ℂ => iteratedDeriv k ⇑(p.1 : C(ℂ, ℂ)) p.2) := by
  have hcont : Continuous
      (fun p : EntireGauge × ℂ => ((gaugeIteratedDeriv k p.1 : C(ℂ, ℂ)) : ℂ → ℂ) p.2) := by
    exact (continuous_eval (X := ℂ) (Y := ℂ)).comp
      ((continuous_subtype_val.comp ((continuous_gaugeIteratedDeriv k).comp
        continuous_fst)).prodMk continuous_snd)
  refine hcont.congr ?_
  intro p
  exact congrFun (coe_gaugeIteratedDeriv k p.1) p.2

end

end GaloisForLFunctions.HTGeometry
