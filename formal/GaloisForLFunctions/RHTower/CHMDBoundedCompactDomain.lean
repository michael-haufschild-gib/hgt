import GaloisForLFunctions.RHTower.CHMDCompactGraphCutoffs

/-!
# Localization of the entire maximal Doob domain

Bounded compactly supported measurable functions are graph dense. This is a
localization theorem for the full arithmetic source. Smooth density is a separate
statement: no identification of this set with the compact C2 core is made here.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

def boundedCompactDomain : Set SourceGraph :=
  {p | ∃ (v : ℝ → ℝ) (_ : Measurable v) (hs : MemLp v 2 massMeasure)
    (hd : MemLp (difference v) 2 edgeMeasure) (M : ℝ),
    0 ≤ M ∧ (∀ x, |v x| ≤ M) ∧ HasCompactSupport v ∧
      p = ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v hs hd}

theorem boundedCutoffLift_mem_domain (v : ℝ → ℝ) (hv : Measurable v)
    (hs : MemLp v 2 massMeasure) (hd : MemLp (difference v) 2 edgeMeasure)
    (M : ℝ) (hM : 0 ≤ M) (hvM : ∀ x, |v x| ≤ M) (n : ℕ) :
    boundedCutoffLift v hv hs hd M hM hvM n ∈ boundedCompactDomain := by
  refine ⟨cutoffFunction v n, hv.mul (cutoff_contDiff n).continuous.measurable,
    cutoffFunction_memLp hs n, cutoffFunction_memLp_difference hv hd hM hvM n,
    M, hM, ?_, cutoffFunction_hasCompactSupport v n, rfl⟩
  intro x
  rw [cutoffFunction, abs_mul, abs_of_nonneg (cutoff_nonneg n x)]
  exact (mul_le_of_le_one_right (abs_nonneg _) (cutoff_le_one n x)).trans (hvM x)

theorem bounded_lift_mem_domain_closure (v : ℝ → ℝ) (hv : Measurable v)
    (hs : MemLp v 2 massMeasure) (hd : MemLp (difference v) 2 edgeMeasure)
    (M : ℝ) (hM : 0 ≤ M) (hvM : ∀ x, |v x| ≤ M) :
    ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v hs hd ∈
      closure boundedCompactDomain :=
  isClosed_closure.mem_of_tendsto (boundedCutoffLift_tendsto v hv hs hd M hM hvM)
    (Eventually.of_forall fun n => subset_closure (boundedCutoffLift_mem_domain v hv hs hd M hM hvM n))

/-- No maximal-domain vector is lost by bounded truncation and spatial localization. -/
theorem dense_boundedCompactDomain : Dense boundedCompactDomain := by
  intro p
  apply isClosed_closure.mem_of_tendsto
    (truncate_tendsto massMeasure edgeMeasure left right nonsingular_left nonsingular_right p)
  refine Eventually.of_forall fun n => ?_
  exact bounded_lift_mem_domain_closure (clip n ∘ p.val.fst)
    ((lipschitz_clip n).continuous.measurable.comp (Lp.stronglyMeasurable p.val.fst).measurable)
    ((lipschitz_clip n).comp_memLp (clip_zero n) (Lp.memLp p.val.fst))
    (memLp_contracted_difference massMeasure edgeMeasure left right nonsingular_left nonsingular_right p (lipschitz_clip n))
    n (Nat.cast_nonneg n) (fun x => abs_clip_le n (p.val.fst x))

end RHTower.CHMDDoobGraph
