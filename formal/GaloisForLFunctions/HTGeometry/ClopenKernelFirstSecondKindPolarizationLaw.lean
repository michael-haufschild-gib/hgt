import GaloisForLFunctions.HTGeometry.FirstKindBounded
import GaloisForLFunctions.HTGeometry.GlobalSecondKindEscapeFromClopenKernelLaw

/-!
# Clopen-kernel first/second-kind polarization

If the bounded-kernel locus is closed and contains one point, connectedness makes both aggregate
kernel roots bounded everywhere.  On every real slice this forces a positive Christoffel limit,
summability and decay of the first-kind orthonormal family.  The nonzero Wronskian simultaneously
forces the adjacent recurrence-weighted second-kind coordinates to escape every common bound.

Thus aggregate second-kind kernel boundedness and pointwise weighted second-kind boundedness are
not interchangeable: the same hypothesis forces the former everywhere and rules out the latter
everywhere.  This file packages the previously separate transfer, Christoffel, decay, and
Wronskian conclusions into one universal profile.
-/

open scoped BigOperators
open Polynomial Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Complete clopen-kernel polarization profile.**  From one point in a closed bounded-kernel
locus, every real point has bounded aggregate kernels, bounded first-kind kernel, positive
Christoffel limit, summable and decaying first-kind coordinates, but jointly unbounded adjacent
recurrence-weighted second-kind coordinates. -/
theorem clopenKernel_firstSecondKind_complete_polarization
    (h : PositiveMomentForm s)
    (hclosed : IsClosed {z : ℂ | BoundedKernel s z})
    {z0 : ℂ} (hz0 : BoundedKernel s z0) :
    ∀ x : ℝ,
      BoundedKernel s (x : ℂ) ∧
      FirstKindBounded s (x : ℂ) ∧
      0 < christoffelLimit s x ∧
      Summable (fun k => ((monicOrtho s k).eval x) ^ 2 /
        momentInner s (monicOrtho s k) (monicOrtho s k)) ∧
      Tendsto (fun k => (orthonormalPoly s k).eval x) atTop (nhds 0) ∧
      ∀ C : ℝ, ∃ n : ℕ,
        C < |recurOffSqrt s n * (secondKindNorm s n).eval x| ∨
        C < |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| := by
  intro x
  have hbounded : BoundedKernel s (x : ℂ) :=
    boundedKernel_of_isClosed h hclosed hz0 (x : ℂ)
  have hfirst : FirstKindBounded s (x : ℂ) :=
    firstKindBounded_of_boundedKernel hbounded
  have hchristoffel : 0 < christoffelLimit s x :=
    (firstKindBounded_iff_christoffelLimit_pos h x).mp hfirst
  have hsumComplex :=
    summable_kernel_everywhere_of_isClosed h hclosed hz0 (x : ℂ)
  have hsum : Summable (fun k => ((monicOrtho s k).eval x) ^ 2 /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
    convert hsumComplex using 1
    funext k
    rw [normSq_monicOrthoC_ofReal]
  have hdecay : Tendsto (fun k => (orthonormalPoly s k).eval x) atTop (nhds 0) :=
    tendsto_orthonormalPoly_eval_zero h x hsum
  exact ⟨hbounded, hfirst, hchristoffel, hsum, hdecay,
    weightedSecondKind_escape_everywhere_of_isClosed_boundedKernel h hclosed hz0 x⟩

/-- **Aggregate/coordinate separation.**  At every real point the two kernel roots admit positive
uniform bounds, while no real constant uniformly bounds both adjacent recurrence-weighted
second-kind coordinates. -/
theorem clopenKernel_bounded_aggregate_unbounded_weighted_coordinates
    (h : PositiveMomentForm s)
    (hclosed : IsClosed {z : ℂ | BoundedKernel s z})
    {z0 : ℂ} (hz0 : BoundedKernel s z0) (x : ℝ) :
    ∃ S P : ℝ, 0 < S ∧ 0 < P ∧
      (∀ N, kernelRoot s (fun j => monicOrthoC s j (x : ℂ)) N ≤ S) ∧
      (∀ N, kernelRoot s (fun j => secondKindC s j (x : ℂ)) N ≤ P) ∧
      ∀ C : ℝ, ¬ ∀ n : ℕ,
        |recurOffSqrt s n * (secondKindNorm s n).eval x| ≤ C ∧
        |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| ≤ C := by
  obtain ⟨S, P, hS, hP, hfirst, hsecond⟩ :=
    boundedKernel_of_isClosed h hclosed hz0 (x : ℂ)
  exact ⟨S, P, hS, hP, hfirst, hsecond,
    not_forall_weightedSecondKind_le_of_isClosed_boundedKernel h hclosed hz0 x⟩

end HTGeometry
