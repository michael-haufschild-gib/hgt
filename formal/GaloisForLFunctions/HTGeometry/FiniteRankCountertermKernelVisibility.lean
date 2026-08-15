import Mathlib

/-!
# Finite-rank counterterm kernel visibility

A finite-dimensional quadratic counterterm vanishes on the kernel of its boundary map.
This leaf formalizes the algebraic visibility gate and the exact rank-one zero-fed
countermodel.  It deliberately does not assert the card's unresolved carrier, density,
or divisor-identification layers.
-/

namespace GaloisForLFunctions.HTGeometry

open QuadraticMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A base quadratic form repaired by a finite-dimensional boundary quadratic form. -/
def finiteRankCounterterm (Q : QuadraticForm ℝ E) (L : E →ₗ[ℝ] F)
    (B : QuadraticForm ℝ F) : QuadraticForm ℝ E :=
  Q + B.comp L

theorem finiteRankCounterterm_apply (Q : QuadraticForm ℝ E) (L : E →ₗ[ℝ] F)
    (B : QuadraticForm ℝ F) (f : E) :
    finiteRankCounterterm Q L B f = Q f + B (L f) := by
  rfl

theorem finiteRankCounterterm_eq_base_on_ker (Q : QuadraticForm ℝ E) (L : E →ₗ[ℝ] F)
    (B : QuadraticForm ℝ F) {f : E} (hf : f ∈ L.ker) :
    finiteRankCounterterm Q L B f = Q f := by
  have hLf : L f = 0 := hf
  simp [finiteRankCounterterm, hLf]

theorem finiteRankCounterterm_nonneg_on_ker (Q : QuadraticForm ℝ E) (L : E →ₗ[ℝ] F)
    (B : QuadraticForm ℝ F) (hR : ∀ f, 0 ≤ finiteRankCounterterm Q L B f)
    {f : E} (hf : f ∈ L.ker) : 0 ≤ Q f := by
  calc
    0 ≤ finiteRankCounterterm Q L B f := hR f
    _ = Q f := finiteRankCounterterm_eq_base_on_ker Q L B hf

/-- Strict positivity of a repair forces strict base positivity on every nonzero
direction invisible to its boundary map. -/
theorem finiteRankCounterterm_pos_on_ker (Q : QuadraticForm ℝ E) (L : E →ₗ[ℝ] F)
    (B : QuadraticForm ℝ F) (hR : ∀ f, f ≠ 0 → 0 < finiteRankCounterterm Q L B f)
    {f : E} (hf : f ∈ L.ker) (hf0 : f ≠ 0) : 0 < Q f := by
  calc
    0 < finiteRankCounterterm Q L B f := hR f hf0
    _ = Q f := finiteRankCounterterm_eq_base_on_ker Q L B hf

theorem finiteRankCounterterm_no_negative_kernel_witness (Q : QuadraticForm ℝ E)
    (L : E →ₗ[ℝ] F) (B : QuadraticForm ℝ F)
    (hR : ∀ f, 0 ≤ finiteRankCounterterm Q L B f) {f : E} (hf : f ∈ L.ker) :
    ¬ Q f < 0 :=
  not_lt_of_ge (finiteRankCounterterm_nonneg_on_ker Q L B hR hf)

def rankOneZeroFedBase (M a : ℝ) : QuadraticForm ℝ ℝ :=
  (M * a) • (QuadraticMap.sq : QuadraticForm ℝ ℝ)

def rankOneZeroFedCounterterm (M a : ℝ) : QuadraticForm ℝ ℝ :=
  -rankOneZeroFedBase M a

theorem rankOneZeroFedCounterterm_cancels (M a x : ℝ) :
    finiteRankCounterterm (rankOneZeroFedBase M a) LinearMap.id
      (rankOneZeroFedCounterterm M a) x = 0 := by
  simp [finiteRankCounterterm, rankOneZeroFedBase, rankOneZeroFedCounterterm,
    QuadraticMap.sq_apply]

theorem rankOneZeroFedBase_one_eq (M a : ℝ) : rankOneZeroFedBase M a 1 = M * a := by
  simp [rankOneZeroFedBase, QuadraticMap.sq_apply]

theorem rankOneZeroFedBase_one_neg {M a : ℝ} (hM : 0 < M) (ha : a < 0) :
    rankOneZeroFedBase M a 1 < 0 := by
  rw [rankOneZeroFedBase_one_eq]
  exact mul_neg_of_pos_of_neg hM ha

theorem finiteRankCounterterm_kernel_isClosed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    IsClosed (L.ker : Set E) :=
  L.isClosed_ker

end GaloisForLFunctions.HTGeometry
