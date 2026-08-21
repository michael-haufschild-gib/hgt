/-
# One-sided Kronecker--Weyl capture density

The completed-time capture bounds of the incidence layer are stated for centred sampling windows
`[-T,T]`.  The static-local complexity laws quote them for the one-sided window `[0,T]`.  The
one-sided window law is already in the corpus (`clockPhaseWindowLaw`), together with its character
averages; identifying its limit with full Haar measure at a rationally independent frequency turns
Portmanteau into the one-sided capture-density bound with the *same* constant -- no factor of two is
paid.

Main results:
* `clockPhaseWindowLaw_tendsto_haar` — **one-sided Kronecker--Weyl equidistribution**.
* `oneSided_closedTarget_limsup_le_volume` — Portmanteau on the one-sided window.
* `limsup_oneSided_projectiveAmpCapture_le` — **the one-sided capture-density bound**.
* `limsup_oneSided_evolutionCapture_le` — the physical evolution sign convention.
-/
import GaloisForLFunctions.HTGeometry.CompletedTimeBohrMean
import GaloisForLFunctions.HTGeometry.SpectralOrbitCaptureDensity

open MeasureTheory Complex UnitAddTorus Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {d : Type} [Fintype d]

/-- **One-sided Kronecker--Weyl equidistribution.**  A rationally independent phase flow sampled
uniformly on `(0,T]` converges weakly to Haar measure on the full phase torus. -/
theorem clockPhaseWindowLaw_tendsto_haar (omega : d → ℝ)
    (hindependent : RationallyIndependentFrequency omega) :
    Tendsto (clockPhaseWindowLaw omega) atTop (nhds (finiteTorusHaarProbabilityMeasure d)) := by
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro n
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  have hlim := tendsto_integral_mFourier_clockPhaseWindowLaw omega n
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    have hdet : finiteTorusCharacterDetuning (0 : d → ℤ) omega = 0 := by
      simp [finiteTorusCharacterDetuning]
    rwa [if_pos hdet] at hlim
  · rw [if_neg hn]
    have hdet : finiteTorusCharacterDetuning n omega ≠ 0 := fun h => hn (hindependent n h)
    rwa [if_neg hdet] at hlim

/-- Portmanteau on the one-sided window. -/
theorem oneSided_closedTarget_limsup_le_volume (omega : d → ℝ)
    (hindependent : RationallyIndependentFrequency omega)
    {A : Set (UnitAddTorus d)} (hA : IsClosed A) :
    atTop.limsup (fun T => (clockPhaseWindowLaw omega T : Measure (UnitAddTorus d)) A)
      ≤ volume A := by
  have hclosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (clockPhaseWindowLaw_tendsto_haar omega hindependent) hA
  rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hclosed

variable {I : Type} [Fintype I] [DecidableEq I]
variable {C : Type} [Fintype C] [Nonempty C]

/-- **One-sided completed-time density of spectral capture.** -/
theorem limsup_oneSided_projectiveAmpCapture_le
    (lam : I → ℝ) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1) (r : ℕ) :
    atTop.limsup (fun T => (clockPhaseWindowLaw (projectiveFrequency lam ref) T :
        Measure (UnitAddTorus {i : I // i ≠ ref})) (projectiveAmpCaptureTarget ref c a z)) ≤
      ENNReal.ofReal ((Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r) := by
  classical
  have hind : RationallyIndependentFrequency (projectiveFrequency lam ref) :=
    maximallyProjectiveEnergy_projectiveFrequency_independent lam hmax ref
  refine le_trans (oneSided_closedTarget_limsup_le_volume _ hind
    (isClosed_projectiveAmpCaptureTarget ref c a z)) ?_
  have hbox := measureReal_capture_le_return_add_replicaMoment
    (p := fun j => ‖c j‖ ^ 2) (fun j => sq_nonneg _) hcsum ha z hz hznorm
    (R := (∅ : Set (I → ℝ)))
    (Q := {x : I → ℝ | ∃ κ,
      a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit (fun j => ‖c j‖ ^ 2) x) (z κ)})
    MeasurableSet.empty (fun x hx => hx.1) r
  rw [measureReal_empty, zero_add] at hbox
  have hmeas := (measure_projectiveAmpCaptureTarget ref c a z).trans
    (measure_torusAmpCaptureTarget c a z)
  have hfin : (volume : Measure (UnitAddTorus {i : I // i ≠ ref}))
      (projectiveAmpCaptureTarget ref c a z) ≠ ⊤ := measure_ne_top _ _
  have hle : (volume : Measure (UnitAddTorus {i : I // i ≠ ref})).real
      (projectiveAmpCaptureTarget ref c a z) ≤
      (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r := by
    rw [measureReal_def, hmeas, ← measureReal_def]
    exact hbox
  have hstep := ENNReal.ofReal_le_ofReal hle
  rwa [measureReal_def, ENNReal.ofReal_toReal hfin] at hstep

/-- **One-sided completed-time density of Schrödinger capture.** -/
theorem limsup_oneSided_evolutionCapture_le
    (lam : I → ℝ) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1) (r : ℕ) :
    atTop.limsup (fun T => (clockPhaseWindowLaw
        (projectiveFrequency (fun i => -lam i) ref) T :
        Measure (UnitAddTorus {i : I // i ≠ ref})) (projectiveAmpCaptureTarget ref c a z)) ≤
      ENNReal.ofReal ((Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r) :=
  limsup_oneSided_projectiveAmpCapture_le _
    (maximallyProjectiveEnergy_neg hmax) ref c hcsum ha z hz hznorm r

end GaloisForLFunctions.HTGeometry

end
