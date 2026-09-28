import GaloisForLFunctions.RHTower.AutocorrelationChainSineCertificate
import GaloisForLFunctions.HTGeometry.OperatorAbsoluteValueBetween

/-!
# A sharp finite-chain bound for nilpotent contractions

The square root of `1 - T†T` records the energy lost at each step. These
defect vectors preserve both the total energy and the full mixed pairing
after telescoping. The sine certificate therefore applies without estimating
the mixed terms separately by a dimension-dependent matrix norm.
-/

open Complex ContinuousLinearMap
open scoped BigOperators InnerProduct
noncomputable section
namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def ccmContractionDefect (T : E →L[ℂ] E) : E →L[ℂ] E :=
  CFC.sqrt (1 - T.adjoint * T)

private theorem defect_square (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ccmContractionDefect T * ccmContractionDefect T = 1 - T.adjoint * T := by
  have hpos : (0 : E →L[ℂ] E) ≤ T.adjoint * T := adjoint_comp_self_nonneg T
  have hn : ‖T.adjoint * T‖ ≤ 1 := by
    change ‖T.adjoint.comp T‖ ≤ 1
    rw [norm_adjoint_comp_self]
    nlinarith [norm_nonneg T]
  exact CFC.sqrt_mul_sqrt_self _
    (sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hn))

/-- The defect preserves the exact mixed difference, including its imaginary part. -/
theorem inner_ccmContractionDefect (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (x y : E) :
    inner ℂ (ccmContractionDefect T x) (ccmContractionDefect T y) =
      inner ℂ x y - inner ℂ (T x) (T y) := by
  let D := ccmContractionDefect T
  have hsa : D.adjoint = D :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 - T.adjoint * T))).adjoint_eq
  calc
    _ = inner ℂ x (D.adjoint (D y)) := (D.adjoint_inner_right x (D y)).symm
    _ = inner ℂ x ((1 - T.adjoint * T) y) := by
      rw [hsa]
      change inner ℂ x ((ccmContractionDefect T * ccmContractionDefect T) y) = _
      rw [defect_square T hT]
    _ = _ := by
      rw [sub_apply, one_apply_eq_self, inner_sub_right,
        mul_apply_eq_comp, T.adjoint_inner_right]

theorem norm_sq_ccmContractionDefect (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (x : E) :
    ‖ccmContractionDefect T x‖ ^ 2 = ‖x‖ ^ 2 - ‖T x‖ ^ 2 := by
  have h := congrArg RCLike.re (inner_ccmContractionDefect T hT x x)
  change RCLike.re (inner ℂ (ccmContractionDefect T x) (ccmContractionDefect T x)) =
    RCLike.re (inner ℂ x x - inner ℂ (T x) (T x)) at h
  simpa only [map_sub, inner_self_eq_norm_sq] using h

/-- No energy is lost when the entire finite defect chain is retained. -/
theorem sum_norm_sq_ccmContractionDefect_pow (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (n : ℕ) (x : E) :
    (∑ k ∈ Finset.range n, ‖ccmContractionDefect T ((T ^ k) x)‖ ^ 2) =
      ‖x‖ ^ 2 - ‖(T ^ n) x‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, norm_sq_ccmContractionDefect T hT,
      pow_succ' T n, mul_apply_eq_comp]
    ring

/-- The full adjacent pairing telescopes as a complex equality. -/
theorem sum_inner_ccmContractionDefect_pow (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (n : ℕ) (x : E) :
    (∑ k ∈ Finset.range n,
      inner ℂ (ccmContractionDefect T ((T ^ k) x))
        (ccmContractionDefect T ((T ^ (k + 1)) x))) =
      inner ℂ x (T x) - inner ℂ ((T ^ n) x) ((T ^ (n + 1)) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, inner_ccmContractionDefect T hT]
    have hpow (j : ℕ) : (T ^ (j + 1)) x = T ((T ^ j) x) := by
      rw [pow_succ', mul_apply_eq_comp]
    simp only [hpow]
    ring

/-- Sharp numerical-radius bound for a nilpotent contraction, on every vector. -/
theorem norm_inner_nilpotent_contraction_le_sine
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (n : ℕ) (hn : T ^ n = 0) (x : E) :
    ‖inner ℂ (T x) x‖ ≤ Real.cos (Real.pi / ((n : ℝ) + 1)) * ‖x‖ ^ 2 := by
  let v : ℕ → E
    | 0 => 0
    | k + 1 => ccmContractionDefect T ((T ^ k) x)
  have hv : v (n + 1) = 0 := by
    change ccmContractionDefect T ((T ^ n) x) = 0
    rw [hn, zero_apply, map_zero]
  have hb := norm_autocorrelation_chain_inner_sum_le n v rfl hv
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hb
  simp only [v, inner_zero_left, norm_zero, zero_pow two_ne_zero, add_zero] at hb
  rw [sum_inner_ccmContractionDefect_pow T hT,
    sum_norm_sq_ccmContractionDefect_pow T hT, hn, zero_apply,
    inner_zero_left, sub_zero, norm_zero, zero_pow two_ne_zero, sub_zero] at hb
  calc
    _ = ‖inner ℂ x (T x)‖ := norm_inner_symm (𝕜 := ℂ) (T x) x
    _ ≤ _ := hb

end RHTower
