/-
The single non-linear phase conditioning bound on the product model.

For the Steinhaus product measure over the phase coordinates, if a carrier factors as
`g(x) + P(unitPhase(x_q))` — a background `g` invariant under the coordinate `q` plus a
polynomial `P` (degree `n ≥ 1`) in the single phase `unitPhase(x_q) = e^{2πi x_q}` — then the
whole carrier's small-ball probability is at most `(2π)⁻¹` times the single-phase harmonic
bound for `P`.  This is the hierarchical conditioning step for a NON-isolated prime, whose
character enters the carrier through all its harmonics: conditioning on every other phase
freezes `g` to a constant that the shift-uniform single-phase law absorbs, so the whole
packet is at least as anti-concentrated as `P`'s single phase, uniformly.
-/
import GaloisForLFunctions.RHTower.RouteBSinglePhase
import GaloisForLFunctions.RHTower.RouteBBlockStep

open MeasureTheory
open scoped ENNReal

namespace RHTower
namespace SteinhausModel

open Sublevel

/-- The single-phase harmonic small-ball constant for a degree-`n` polynomial at level `t`. -/
noncomputable def singlePhaseConst (P : Polynomial ℂ) (t : ℝ) : ENNReal :=
  (P.natDegree : ℝ≥0∞)
    * ENNReal.ofReal (2 * Real.pi
        * Real.sqrt (2 * (t / ‖P.leadingCoeff‖) ^ ((P.natDegree : ℝ)⁻¹)))

/-- `unitPhase x` is the circle exponential `e^{iθ}` at angle `θ = 2π x`. -/
theorem unitPhase_eq (x : ℝ) :
    unitPhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  rw [unitPhase, show ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I
    = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((x : ℝ) : ℂ) by push_cast; ring]

/-- Continuity of the angle-parametrised single-phase modulus. -/
theorem continuous_shift_poly_norm (P : Polynomial ℂ) (V : ℂ) :
    Continuous fun z : ℝ => ‖V + P.eval (Complex.exp ((z : ℂ) * Complex.I))‖ :=
  (continuous_const.add ((P.continuous_aeval).comp
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))).norm

/-- **The single-phase integral bound.**  For a fixed background value `V` and a degree-`n`
polynomial `P`, the `[0,1]`-average of the small-ball indicator of `V + P(unitPhase·)` is at
most `(2π)⁻¹` times the single-phase harmonic bound.  The angle rescale `θ = 2π x` turns the
unit-interval average into the `[0,2π]` sublevel measure, then the shift-uniform single-phase
law applies with shift `V`. -/
theorem single_phase_interval_le (P : Polynomial ℂ) (hP : 1 ≤ P.natDegree) (V : ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ x, {y : ℝ | ‖V + P.eval (unitPhase y)‖ ≤ t}.indicator (fun _ => (1 : ENNReal)) x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * singlePhaseConst P t := by
  classical
  set A : Set ℝ := {z : ℝ | ‖V + P.eval (Complex.exp ((z : ℂ) * Complex.I))‖ ≤ t} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le (continuous_shift_poly_norm P V) continuous_const).measurableSet
  set φ : ℝ → ENNReal := fun θ => A.indicator (fun _ => (1 : ENNReal)) θ with hφ
  have hφm : Measurable φ := measurable_const.indicator hAm
  -- pointwise the unit-interval integrand equals φ (2π x)
  have hpt : ∀ x : ℝ,
      {y : ℝ | ‖V + P.eval (unitPhase y)‖ ≤ t}.indicator (fun _ => (1 : ENNReal)) x
        = φ (2 * Real.pi * x) := by
    intro x
    simp only [hφ, hA, Set.indicator_apply, Set.mem_setOf_eq, unitPhase_eq]
  -- the [0,2π] integral of φ is the sublevel measure
  have hint : ∫⁻ θ, φ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
      = volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi)
          ∧ ‖V + P.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ t} := by
    rw [hφ, lintegral_indicator hAm, setLIntegral_one, Measure.restrict_apply hAm]
    congr 1
    ext θ
    simp only [hA, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  calc ∫⁻ x, {y : ℝ | ‖V + P.eval (unitPhase y)‖ ≤ t}.indicator (fun _ => (1 : ENNReal)) x
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∫⁻ x, φ (2 * Real.pi * x) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        lintegral_congr hpt
    _ = ∫⁻ θ, φ θ ∂(Measure.map (fun x : ℝ => 2 * Real.pi * x)
          (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
        rw [lintegral_map hφm (by fun_prop)]
    _ = ∫⁻ θ, φ θ ∂(ENNReal.ofReal (2 * Real.pi)⁻¹
          • volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) := by rw [map_two_pi_smul]
    _ = ENNReal.ofReal (2 * Real.pi)⁻¹
          * ∫⁻ θ, φ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal (2 * Real.pi)⁻¹
          * volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi)
              ∧ ‖V + P.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ t} := by rw [hint]
    _ ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * singlePhaseConst P t := by
        gcongr
        rw [singlePhaseConst]
        exact poly_circle_sublevel_shift P hP V ht

/-- **The single non-linear phase conditioning bound.**  Over the product model, if the
carrier is a background `g` (invariant under coordinate `q`) plus a degree-`n` polynomial `P`
in the single phase `unitPhase(x_q)`, its small-ball probability is at most `(2π)⁻¹` times the
single-phase harmonic bound for `P`.  Conditioning on all coordinates but `q` freezes `g`, and
the shift-uniform single-phase law bounds the remaining `q`-average uniformly; the other
coordinates integrate against probability measures. -/
theorem pi_single_phase_le {ι : Type} [DecidableEq ι] [Fintype ι]
    (g : (ι → ℝ) → ℂ) (P : Polynomial ℂ) (hP : 1 ≤ P.natDegree) (q : ι) {t : ℝ} (ht : 0 ≤ t)
    (hg : ∀ x v, g (Function.update x q v) = g x) (hgm : Measurable g) :
    (Measure.pi (fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)))
        {x : ι → ℝ | ‖g x + P.eval (unitPhase (x q))‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * singlePhaseConst P t := by
  classical
  haveI : ∀ i : ι, IsProbabilityMeasure ((fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)) i) :=
    fun _ => ⟨by simp⟩
  set μ : ι → Measure ℝ := fun _ => volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  set E : Set (ι → ℝ) := {x : ι → ℝ | ‖g x + P.eval (unitPhase (x q))‖ ≤ t} with hE
  have hFm : Measurable (fun x : ι → ℝ => g x + P.eval (unitPhase (x q))) := by
    have hp : Measurable (fun x : ι → ℝ => unitPhase (x q)) := by unfold unitPhase; fun_prop
    exact hgm.add ((P.continuous_aeval.measurable).comp hp)
  have hEm : MeasurableSet E := hFm.norm measurableSet_Iic
  have hf : Measurable (E.indicator (fun _ => (1 : ENNReal))) := measurable_const.indicator hEm
  have hpiE : (Measure.pi μ) E
      = ∫⁻ x, E.indicator (fun _ => (1 : ENNReal)) x ∂(Measure.pi μ) := by
    rw [lintegral_indicator hEm, setLIntegral_one]
  rw [hpiE, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0 : ℝ))]
  rw [show (Finset.univ : Finset ι) = (Finset.univ \ {q}) ∪ {q} from
      (Finset.sdiff_union_of_subset (Finset.subset_univ _)).symm]
  rw [lmarginal_union μ _ hf Finset.sdiff_disjoint]
  have hbound : (∫⋯∫⁻_{q}, E.indicator (fun _ => (1 : ENNReal)) ∂μ)
      ≤ fun _ => ENNReal.ofReal (2 * Real.pi)⁻¹ * singlePhaseConst P t := by
    intro z
    rw [show ({q} : Finset ι) = insert q (∅ : Finset ι) from rfl,
      lmarginal_insert _ hf (by simp)]
    simp only [lmarginal_empty]
    have hval : ∀ x : ℝ, (E.indicator (fun _ => (1 : ENNReal))) (Function.update z q x)
        = {y : ℝ | ‖g z + P.eval (unitPhase y)‖ ≤ t}.indicator (fun _ => (1 : ENNReal)) x := by
      intro x
      rw [hE]
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Function.update_self, hg z x]
    rw [lintegral_congr hval]
    exact single_phase_interval_le P hP (g z) ht
  refine le_trans (lmarginal_mono hbound _) (le_of_eq ?_)
  rw [lmarginal]
  simp only [lintegral_const]
  rw [measure_univ, mul_one]

end SteinhausModel
end RHTower
