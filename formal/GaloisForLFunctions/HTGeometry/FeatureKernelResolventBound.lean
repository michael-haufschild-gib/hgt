import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# Leverage bounds a geometric resolvent

A finite feature kernel `K(x,y) = ∑ⱼ φⱼ(x)φⱼ(y)` is a reproducing kernel, so Cauchy--Schwarz bounds
every off-diagonal value by the diagonal: `|K(x,y)| ≤ sup_x K(x,x)`.  That supremum is the leverage
`L`.

If a resolvent is the geometric series of contractions applied to such a kernel, every summand
inherits the same bound, so the resolvent is at most `L/(1-a)`.  This is the whole mechanism behind
the leverage form of the capacitary bound; the transitive-action case only adds that the diagonal
is then constant and equal to the trace.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {ι X : Type*} [Fintype ι]

/-- The kernel of a finite feature family. -/
def featureKernel (φ : ι → X → ℝ) (x y : X) : ℝ := ∑ j, φ j x * φ j y

theorem featureKernel_diag_nonneg (φ : ι → X → ℝ) (x : X) : 0 ≤ featureKernel φ x x := by
  refine Finset.sum_nonneg fun j _ => ?_
  nlinarith [sq_nonneg (φ j x)]

/-- **Reproducing-kernel Cauchy--Schwarz.** -/
theorem sq_featureKernel_le (φ : ι → X → ℝ) (x y : X) :
    featureKernel φ x y ^ 2 ≤ featureKernel φ x x * featureKernel φ y y := by
  have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => φ j x) (fun j => φ j y)
  have hx : featureKernel φ x x = ∑ j, φ j x ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  have hy : featureKernel φ y y = ∑ j, φ j y ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [featureKernel, hx, hy]
  exact hcs

/-- **The leverage bounds every kernel value.** -/
theorem abs_featureKernel_le {φ : ι → X → ℝ} {L : ℝ} (hL : ∀ x, featureKernel φ x x ≤ L)
    (x y : X) : |featureKernel φ x y| ≤ L := by
  have hL0 : 0 ≤ L := le_trans (featureKernel_diag_nonneg φ x) (hL x)
  have hsq : featureKernel φ x y ^ 2 ≤ L * L := by
    refine le_trans (sq_featureKernel_le φ x y) ?_
    exact mul_le_mul (hL x) (hL y) (featureKernel_diag_nonneg φ y) hL0
  have habs : |featureKernel φ x y| ^ 2 ≤ L ^ 2 := by
    rw [sq_abs]
    nlinarith [hsq]
  nlinarith [habs, abs_nonneg (featureKernel φ x y), hL0]

/-! ## The geometric resolvent -/

/-- **A geometric series of uniformly bounded terms is bounded by `L/(1-a)`.** -/
theorem abs_tsum_le_of_geometric {a L : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (f : ℕ → ℝ) (hf : ∀ m, |f m| ≤ a ^ m * L) :
    |∑' m, f m| ≤ L / (1 - a) := by
  have hsummable : Summable fun m : ℕ => a ^ m * L :=
    (summable_geometric_of_lt_one ha ha1).mul_right L
  have hfsummable : Summable f :=
    Summable.of_norm_bounded hsummable fun m => by simpa using hf m
  have hnorm : |∑' m, f m| ≤ ∑' m, |f m| := by
    have h := norm_tsum_le_tsum_norm (f := f) (by simpa [Real.norm_eq_abs] using hfsummable.abs)
    simpa [Real.norm_eq_abs] using h
  refine le_trans hnorm ?_
  have hbound : ∑' m : ℕ, |f m| ≤ ∑' m : ℕ, a ^ m * L :=
    Summable.tsum_mono hfsummable.abs hsummable (fun m => hf m)
  have hgeom : ∑' m : ℕ, a ^ m * L = L / (1 - a) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one ha ha1]
    field_simp
  rw [← hgeom]
  exact hbound

end GaloisForLFunctions.HTGeometry
