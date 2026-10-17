import Mathlib.NumberTheory.Harmonic.Bounds

/-! The bounded harmonic correction in the real-ratio factorial lift.
This is a component of the explicit signed prime–polar producer package. -/

open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def realHarmonic (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, 1 / (j : ℝ)

private theorem realHarmonic_succ (n : ℕ) :
    realHarmonic (n+1) = realHarmonic n + 1 / ((n : ℝ)+1) := by
  unfold realHarmonic
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
  push_cast
  rfl

private def reciprocalPair (x : ℝ) : ℝ := 1 / (2*x+1) - 1 / (2*x+2)

private theorem harmonic_dyadic (n : ℕ) :
    realHarmonic (2*n) - realHarmonic n =
      ∑ k ∈ Finset.range n, reciprocalPair (k : ℝ) := by
  induction n with
  | zero => simp [realHarmonic]
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega,
      realHarmonic_succ (2*n+1), realHarmonic_succ (2*n), realHarmonic_succ n,
      Finset.sum_range_succ]
    push_cast
    unfold reciprocalPair at ih ⊢
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    have hcancel : 2 / (2*(n : ℝ)+2) = 1 / ((n : ℝ)+1) := by
      field_simp
    linear_combination ih + hcancel

/-- The real-ratio polar correction left by the factorial bi-null stencil. -/
def harmonicCorrection (N : ℕ) : ℝ :=
  4*(N : ℝ) * (realHarmonic (4*N) - 2*realHarmonic (2*N) + realHarmonic N)

theorem harmonicCorrection_eq_pairs (N : ℕ) :
    harmonicCorrection N =
      4*(N : ℝ) * ∑ k ∈ Finset.range N, reciprocalPair ((N : ℝ)+k) := by
  have h1 := harmonic_dyadic N
  have h2 := harmonic_dyadic (2*N)
  rw [show 2*(2*N) = 4*N by omega] at h2
  have hs : (∑ k ∈ Finset.range (2*N), reciprocalPair (k : ℝ)) =
      (∑ k ∈ Finset.range N, reciprocalPair (k : ℝ)) +
        ∑ k ∈ Finset.range N, reciprocalPair ((N : ℝ)+k) := by
    rw [show 2*N = N+N by omega, Finset.sum_range_add]
    push_cast
    rfl
  unfold harmonicCorrection
  congr 1
  linear_combination h2 - h1 + hs

private theorem reciprocalPair_bounds {N k : ℕ} (hN : 1 ≤ N) :
    0 ≤ reciprocalPair ((N : ℝ)+k) ∧
      reciprocalPair ((N : ℝ)+k) ≤ 1 / (4*(N : ℝ)^2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hden1 : 0 < 2*((N : ℝ)+k)+1 := by positivity
  have hden2 : 0 < 2*((N : ℝ)+k)+2 := by positivity
  have heq : reciprocalPair ((N : ℝ)+k) =
      1 / ((2*((N : ℝ)+k)+1)*(2*((N : ℝ)+k)+2)) := by
    unfold reciprocalPair
    field_simp
    ring
  rw [heq]
  constructor
  · positivity
  · apply one_div_le_one_div_of_le (by positivity : 0 < 4*(N : ℝ)^2)
    nlinarith [sq_nonneg ((k : ℝ)), mul_nonneg hn.le hk]

/-- An unconditional constant bound, with no Chebyshev error assumption. -/
theorem harmonicCorrection_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ harmonicCorrection N ∧ harmonicCorrection N ≤ 1 := by
  rw [harmonicCorrection_eq_pairs]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => (reciprocalPair_bounds (k := k) hN).1)
  · have hs : (∑ k ∈ Finset.range N, reciprocalPair ((N : ℝ)+k)) ≤
        (N : ℝ) * (1 / (4*(N : ℝ)^2)) := by
      calc
        _ ≤ ∑ _k ∈ Finset.range N, 1 / (4*(N : ℝ)^2) :=
          Finset.sum_le_sum fun k _ => (reciprocalPair_bounds (k := k) hN).2
        _ = _ := by simp
    calc
      _ ≤ 4*(N : ℝ) * ((N : ℝ)*(1/(4*(N : ℝ)^2))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 1 := by field_simp

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
