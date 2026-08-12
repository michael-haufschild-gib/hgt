import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBranch
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.HelsonDivisorResponse

/-!
# The Helson trace-class realization and its Fredholm crossing response

A divisor-summable coefficient stream `a` is realized as the trace-class Helson operator
`K_a(j,k) = a_{jk}` on `ℓ²`, assembled as an absolutely trace-norm convergent sum of the divisor
blocks.  The realization is coefficient faithful, is self-adjoint for real streams, and its
quadratic form at a vector `u` is the divisor convolution `W_u`.

At a simple nonzero eigenvalue the eigenvalue branch of `K_{a+th}` is differentiable with
derivative `∑ h_n W_u(n)`, so the Fredholm wall `τ ∈ spec K_a` carries the exact crossing covector
`h ↦ -∑ h_n W_u(n)`, which is continuous and nonzero.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open RHTower
open scoped InnerProductSpace

/-- The Helson chart `ℓ²(ℕ)`. -/
abbrev HelsonSpace : Type := lp (fun _ : ℕ => ℂ) 2

/-- The coordinate vector of the Helson chart. -/
noncomputable def helsonBasis (j : ℕ) : HelsonSpace := lp.single 2 j (1 : ℂ)

@[simp] theorem norm_helsonBasis (j : ℕ) : ‖helsonBasis j‖ = 1 := by
  rw [helsonBasis, lp.norm_single (by norm_num), norm_one]

@[simp] theorem inner_helsonBasis_left (j : ℕ) (f : HelsonSpace) :
    inner ℂ (helsonBasis j) f = (f : ℕ → ℂ) j := by
  rw [helsonBasis, lp.inner_single_left]
  simp [RCLike.inner_apply]

@[simp] theorem inner_helsonBasis_right (j : ℕ) (f : HelsonSpace) :
    inner ℂ f (helsonBasis j) = (starRingEnd ℂ) ((f : ℕ → ℂ) j) := by
  rw [helsonBasis, lp.inner_single_right]
  simp [RCLike.inner_apply]

@[simp] theorem helsonBasis_coe (j k : ℕ) :
    ((helsonBasis j : HelsonSpace) : ℕ → ℂ) k = if k = j then 1 else 0 := by
  rw [helsonBasis, lp.single_apply, Pi.single_apply]

section Realization

/-- **`(HFR.5)`.**  The divisor block of the Helson realization. -/
noncomputable def helsonBlockOp (a : ℕ → ℂ) (n : ℕ) : SchattenOneOperator HelsonSpace :=
  ∑ p ∈ n.divisorsAntidiagonal, a n • rankOneSchattenOne (helsonBasis p.1) (helsonBasis p.2)

theorem norm_helsonBlockOp_le (a : ℕ → ℂ) (n : ℕ) :
    ‖helsonBlockOp a n‖ ≤ (divisorWeight n : ℝ) * ‖a n‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ n.divisorsAntidiagonal,
      ‖a n • rankOneSchattenOne (helsonBasis p.1) (helsonBasis p.2)‖ = ‖a n‖ := by
    intro p _
    rw [norm_smul, norm_rankOneSchattenOne, norm_helsonBasis, norm_helsonBasis]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, divisorWeight]

theorem summable_norm_helsonBlockOp {a : ℕ → ℂ} (ha : HelsonSummable a) :
    Summable fun n : ℕ => ‖helsonBlockOp a n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_helsonBlockOp_le a) ha

theorem summable_helsonBlockOp {a : ℕ → ℂ} (ha : HelsonSummable a) :
    Summable (helsonBlockOp a) :=
  Summable.of_norm (summable_norm_helsonBlockOp ha)

/-- **`(HFR.2)`, `(HFR.5)`.**  The Helson operator of a divisor-summable stream, assembled as an
absolutely trace-norm convergent sum of rank ones. -/
noncomputable def helsonOperator (a : ℕ → ℂ) : SchattenOneOperator HelsonSpace :=
  ∑' n : ℕ, helsonBlockOp a n

/-- **Theorem 2.1 (1), `(HFR.3)`.**  The Helson realization is trace class with trace norm at most
the divisor-weighted coefficient mass. -/
theorem norm_helsonOperator_le {a : ℕ → ℂ} (ha : HelsonSummable a) :
    ‖helsonOperator a‖ ≤ ∑' n : ℕ, (divisorWeight n : ℝ) * ‖a n‖ := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_helsonBlockOp ha)) ?_
  exact (summable_norm_helsonBlockOp ha).tsum_le_tsum (norm_helsonBlockOp_le a) ha

/-- The Helson operator is a compact operator on the chart. -/
theorem isCompactOperator_helsonOperator (a : ℕ → ℂ) :
    IsCompactOperator ((helsonOperator a : SchattenOneOperator HelsonSpace) :
      HelsonSpace →L[ℂ] HelsonSpace) :=
  (helsonOperator a).isCompactOperator

theorem coe_helsonOperator {a : ℕ → ℂ} (ha : HelsonSummable a) :
    ((helsonOperator a : SchattenOneOperator HelsonSpace) : HelsonSpace →L[ℂ] HelsonSpace)
      = ∑' n : ℕ, ((helsonBlockOp a n : SchattenOneOperator HelsonSpace) :
          HelsonSpace →L[ℂ] HelsonSpace) := by
  have h := ContinuousLinearMap.map_tsum
    (schattenOneCoeCLM (H := HelsonSpace)) (summable_helsonBlockOp ha)
  simpa [helsonOperator] using h

/-- The quadratic form of a divisor block. -/
theorem inner_helsonBlockOp_apply (a : ℕ → ℂ) (n : ℕ) (x y : HelsonSpace) :
    inner ℂ x (((helsonBlockOp a n : SchattenOneOperator HelsonSpace) :
        HelsonSpace →L[ℂ] HelsonSpace) y)
      = a n * ∑ p ∈ n.divisorsAntidiagonal,
        (starRingEnd ℂ) ((x : ℕ → ℂ) p.1) * (y : ℕ → ℂ) p.2 := by
  classical
  have hcoe : ((helsonBlockOp a n : SchattenOneOperator HelsonSpace) :
        HelsonSpace →L[ℂ] HelsonSpace)
      = ∑ p ∈ n.divisorsAntidiagonal,
        a n • (InnerProductSpace.rankOne ℂ (helsonBasis p.1) (helsonBasis p.2)) := by
    have h := map_sum (schattenOneCoeCLM (H := HelsonSpace))
      (fun p : ℕ × ℕ => a n • rankOneSchattenOne (helsonBasis p.1) (helsonBasis p.2))
      n.divisorsAntidiagonal
    simp only [schattenOneCoeCLM_apply, SchattenOneOperator.coe_smul,
      rankOneSchattenOne_coe] at h
    exact h
  rw [hcoe]
  rw [sum_apply, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_apply, inner_smul_right, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_helsonBasis_left, inner_helsonBasis_right]
  ring

end Realization

end HTGeometry.ConstraintMotiveRelativity
