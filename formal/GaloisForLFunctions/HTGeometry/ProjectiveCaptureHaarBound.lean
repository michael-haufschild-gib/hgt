/-
# The Haar mass of a relative-phase capture event

The quenched incidence bound of the return-excised phase-incidence law bounds the Haar mass of a
capture event on the spectral phase torus by one replica moment.  Combined with the counting chain
this gives the fibrewise bound the plateau law's final assembly consumes: on a fibre whose input
collision is below the replica scale, the Haar mass of the easy-circuit tube is at most `2^{-r/2}`.

Main results:
* `measureReal_projectiveAmpCaptureTarget_le` — the Haar mass is at most the replica moment.
* `measure_projectiveAmpCaptureTarget_le_two_rpow` — **the fibrewise incidence bound `2^{-r/2}`**.
-/
import GaloisForLFunctions.HTGeometry.CompletedTimeCircuitDensity

open MeasureTheory Filter UnitAddTorus

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {C : Type*} [Fintype C] [Nonempty C]

/-- **The Haar mass of a relative-phase capture event is at most one replica moment.** -/
theorem measureReal_projectiveAmpCaptureTarget_le (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1) (r : ℕ) :
    (volume : Measure (UnitAddTorus {i : I // i ≠ ref})).real
        (projectiveAmpCaptureTarget ref c a z)
      ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision (fun j => ‖c j‖ ^ 2) / a ^ 2) ^ r := by
  classical
  have hbox := measureReal_capture_le_return_add_replicaMoment
    (p := fun j => ‖c j‖ ^ 2) (fun j => sq_nonneg _) hcsum ha z hz hznorm
    (R := (∅ : Set (I → ℝ)))
    (Q := {x : I → ℝ | ∃ κ,
      a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit (fun j => ‖c j‖ ^ 2) x) (z κ)})
    MeasurableSet.empty (fun x hx => hx.1) r
  rw [measureReal_empty, zero_add] at hbox
  have hmeas := (measure_projectiveAmpCaptureTarget ref c a z).trans
    (measure_torusAmpCaptureTarget c a z)
  rw [measureReal_def, hmeas, ← measureReal_def]
  exact hbox

/-- **The fibrewise incidence bound.**  On a fibre whose input collision is below the replica scale
and with a dictionary below the replica order, the Haar mass of the capture event is at most
`2^{-r/2}`. -/
theorem measure_projectiveAmpCaptureTarget_le_two_rpow (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1)
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision (fun j => ‖c j‖ ^ 2) ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (volume : Measure (UnitAddTorus {i : I // i ≠ ref}))
        (projectiveAmpCaptureTarget ref c a z)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
  have hle : (volume : Measure (UnitAddTorus {i : I // i ≠ ref})).real
      (projectiveAmpCaptureTarget ref c a z) ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) :=
    le_trans (measureReal_projectiveAmpCaptureTarget_le ref c hcsum ha z hz hznorm r)
      (replicaMoment_le_two_rpow ha z hr hcoll hscale hM hcard hs)
  have hfin : (volume : Measure (UnitAddTorus {i : I // i ≠ ref}))
      (projectiveAmpCaptureTarget ref c a z) ≠ ⊤ := measure_ne_top _ _
  have hstep := ENNReal.ofReal_le_ofReal hle
  rwa [measureReal_def, ENNReal.ofReal_toReal hfin] at hstep

end GaloisForLFunctions.HTGeometry

end
