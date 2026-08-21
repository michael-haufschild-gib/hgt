import Mathlib.Order.Bounds.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Comparison of first eigenvalues under a comparison of metrics

Lemma 1.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), compares the first nonzero eigenvalues of two Kähler metrics on a
compact Riemann surface:

```text
λ'₁ / λ₁  ≥  min_M (g / g') .
```

Once the min–max principle has expressed both eigenvalues as infima of Rayleigh quotients over the
*same* family of test forms, the statement is purely order-theoretic: if the numerator of the second
quotient dominates `c` times the numerator of the first at every test form, the infimum does too.
The proof of the paper's inequality is exactly that observation applied to

```text
∫ (∂̄φ ⊗ ∂φ̄)/g'  =  ∫ [(∂̄φ ⊗ ∂φ̄)/g] · (g/g')  ≥  (min_M g/g') ∫ (∂̄φ ⊗ ∂φ̄)/g .
```
-/

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **Lemma 1.1 of Dai–Yoshikawa, variational form.**

Two families of Rayleigh quotients over a common index set, whose numerators satisfy
`c · Q ≤ Q'` pointwise, have infima satisfying `c · λ ≤ λ'`. -/
theorem mul_isGLB_le_isGLB_of_le
    {ι : Type*} {Q Q' N : ι → ℝ} {c lam lam' : ℝ}
    (hc : 0 ≤ c) (hN : ∀ i, 0 < N i)
    (hQ : ∀ i, c * Q i ≤ Q' i)
    (hlam : IsGLB (Set.range fun i => Q i / N i) lam)
    (hlam' : IsGLB (Set.range fun i => Q' i / N i) lam') :
    c * lam ≤ lam' := by
  refine hlam'.2 ?_
  rintro y ⟨i, rfl⟩
  have hNi : 0 < N i := hN i
  have hstep : c * (Q i / N i) ≤ Q' i / N i := by
    rw [mul_div_assoc']
    gcongr
    exact hQ i
  refine le_trans ?_ hstep
  exact mul_le_mul_of_nonneg_left (hlam.1 ⟨i, rfl⟩) hc

/-- The pointwise step of Lemma 1.1: a weight bounded below by `c` multiplies an energy by at least
`c`.  Stated for a finite sum, which is the form in which the estimate is used after the metric
comparison `g' ≤ c⁻¹ g` is inserted into the Rayleigh quotient. -/
theorem mul_sum_le_sum_mul_weight
    {ι : Type*} (s : Finset ι) {e w : ι → ℝ} {c : ℝ}
    (he : ∀ i ∈ s, 0 ≤ e i) (hw : ∀ i ∈ s, c ≤ w i) :
    c * ∑ i ∈ s, e i ≤ ∑ i ∈ s, e i * w i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (hw i hi) (he i hi)


/-- **The min–max step of Proposition 6.1.**

A family of trial functions with pairwise disjoint supports diagonalizes both the energy and the
norm, so the Rayleigh quotient on their span is bounded by the largest individual quotient:
if `Eᵢ ≤ M Nᵢ` for every `i`, then `Σ cᵢ² Eᵢ ≤ M Σ cᵢ² Nᵢ`. -/
theorem sum_sq_mul_le_of_le
    {ι : Type*} [Fintype ι] (c E N : ι → ℝ) {M : ℝ}
    (hM : ∀ i, E i ≤ M * N i) :
    ∑ i, c i ^ 2 * E i ≤ M * ∑ i, c i ^ 2 * N i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := mul_le_mul_of_nonneg_left (hM i) (sq_nonneg (c i))
  calc c i ^ 2 * E i ≤ c i ^ 2 * (M * N i) := this
    _ = M * (c i ^ 2 * N i) := by ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
