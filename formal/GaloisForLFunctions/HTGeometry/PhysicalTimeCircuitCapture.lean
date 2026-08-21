/-
# The one-sided physical-time density of the complete circuit union

Assembling the one-sided Kronecker--Weyl capture bound with the eigenbasis bridge gives the
statement the static-local complexity laws quote: for a Hamiltonian with maximally projective
spectrum and a bounded input collision, the long-time density of the *physical* times at which the
evolved state is captured by a depth-`s` circuit dictionary is at most `2^{-r/2}`.

Main results:
* `physicalCaptureSet` — the set of physical times at which the dictionary captures the orbit.
* `limsup_oneSided_physicalCapture_le` — **the completed-time circuit bound in physical time**.
-/
import GaloisForLFunctions.HTGeometry.ClockPhaseEvolutionBridge
import GaloisForLFunctions.HTGeometry.CompletedTimeCircuitDensity

open MeasureTheory Complex UnitAddTorus Set Filter Topology Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type} [Fintype I] [DecidableEq I]
variable {C : Type} [Fintype C] [Nonempty C]

/-- The set of physical times at which the evolved state is captured by the dictionary. -/
def physicalCaptureSet (H : Matrix I I ℂ) (psi : I → ℂ) (a : ℝ) (Z : C → (I → ℂ)) : Set ℝ :=
  {t | ∃ κ, a ≤ finitePureStateFidelity (unitaryEvolution H t *ᵥ psi) (Z κ)}

/-- The physical capture set is the clock-phase preimage of the relative-phase capture target. -/
theorem physicalCaptureSet_eq_preimage {H : Matrix I I ℂ} {e : I → I → ℂ} {lam : I → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (ref : I) (psi : I → ℂ) (a : ℝ) (Z : C → (I → ℂ)) :
    physicalCaptureSet H psi a Z
      = finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) ⁻¹'
          (projectiveAmpCaptureTarget ref (eigenCoords e psi) a
            (fun κ => eigenCoords e (Z κ))) := by
  ext t
  constructor
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, by rwa [← finitePureStateFidelity_unitaryEvolution_eq_orbit heb ref psi (Z κ) t]⟩
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, by rwa [finitePureStateFidelity_unitaryEvolution_eq_orbit heb ref psi (Z κ) t]⟩

/-- **The completed-time circuit bound in physical time, one-sided.**  The long-time density of the
physical times at which the evolution is captured by the dictionary is at most `2^{-r/2}`. -/
theorem limsup_oneSided_physicalCapture_le {H : Matrix I I ℂ} {e : I → I → ℂ} {lam : I → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (psi : I → ℂ) (hpsi : finiteComplexInner psi psi = 1)
    (Z : C → (I → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision (fun j => ‖eigenCoords e psi j‖ ^ 2) ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
        (physicalCaptureSet H psi a Z))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
  classical
  have hcsum : ∑ j, ‖eigenCoords e psi j‖ ^ 2 ≤ 1 :=
    le_of_eq (sum_normSq_eigenCoords heb psi hpsi)
  have hznorm : ∀ κ, ∑ j, ‖eigenCoords e (Z κ) j‖ ^ 2 ≤ 1 :=
    fun κ => le_of_eq (sum_normSq_eigenCoords heb (Z κ) (hZ κ))
  have hzunit : ∀ κ, finiteComplexInner (eigenCoords e (Z κ)) (eigenCoords e (Z κ)) = 1 :=
    fun κ => (finiteComplexInner_eigenCoords heb (Z κ) (Z κ)).trans (hZ κ)
  have hmain := limsup_oneSided_capture_le_two_rpow lam hmax ref (eigenCoords e psi) hcsum ha
    (fun κ => eigenCoords e (Z κ)) hzunit hznorm hr hcoll hscale hM hcard hs
  have hset : ∀ T : ℝ, (windowProbabilityMeasure T : Measure ℝ)
      (physicalCaptureSet H psi a Z)
      = (clockPhaseWindowLaw (projectiveFrequency (fun i => -lam i) ref) T :
          Measure (UnitAddTorus {i : I // i ≠ ref}))
        (projectiveAmpCaptureTarget ref (eigenCoords e psi) a
          (fun κ => eigenCoords e (Z κ))) := by
    intro T
    rw [clockPhaseWindowLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (finiteClockPhasePoint_continuous _).measurable
        (isClosed_projectiveAmpCaptureTarget ref (eigenCoords e psi) a
          (fun κ => eigenCoords e (Z κ))).measurableSet]
    rw [physicalCaptureSet_eq_preimage heb ref psi a Z]
  simpa only [hset] using hmain


/-! ## From an approximation in distance to a fidelity capture -/

theorem sum_normSq_sub_eq {α : Type*} [Fintype α] (u v : α → ℂ) :
    (∑ x, ‖u x - v x‖ ^ 2 : ℝ)
      = (finiteComplexInner u u).re + (finiteComplexInner v v).re
        - 2 * (finiteComplexInner u v).re := by
  simp only [finiteComplexInner, Complex.re_sum, Complex.sq_norm]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-- **An approximation in distance is a fidelity capture.**  Two unit vectors at squared distance
at most `ε²` have squared overlap at least `1 - ε²`. -/
theorem le_finitePureStateFidelity_of_dist_le {α : Type*} [Fintype α] {u v : α → ℂ}
    (hu : finiteComplexInner u u = 1) (hv : finiteComplexInner v v = 1)
    {eps : ℝ} (h : (∑ x, ‖u x - v x‖ ^ 2 : ℝ) ≤ eps ^ 2) :
    1 - eps ^ 2 ≤ finitePureStateFidelity u v := by
  have hexp := sum_normSq_sub_eq u v
  rw [hu, hv] at hexp
  simp only [Complex.one_re] at hexp
  have hre : 1 - eps ^ 2 / 2 ≤ (finiteComplexInner u v).re := by linarith [hexp, h]
  have hfid : ((finiteComplexInner u v).re) ^ 2 ≤ finitePureStateFidelity u v := by
    rw [finitePureStateFidelity, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (finiteComplexInner u v).im, sq_nonneg (finiteComplexInner u v).re]
  rcases le_or_gt 0 (1 - eps ^ 2 / 2) with hpos | hneg
  · have hsq : (1 - eps ^ 2 / 2) ^ 2 ≤ ((finiteComplexInner u v).re) ^ 2 := by
      nlinarith [hre, hpos]
    nlinarith [hsq, hfid, sq_nonneg (eps ^ 2)]
  · have hfid0 : 0 ≤ finitePureStateFidelity u v := by
      rw [finitePureStateFidelity]
      positivity
    nlinarith [hneg, hfid0]

end GaloisForLFunctions.HTGeometry

end
