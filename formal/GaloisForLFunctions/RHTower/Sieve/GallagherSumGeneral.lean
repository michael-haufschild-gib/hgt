import GaloisForLFunctions.RHTower.Sieve.GallagherSobolev
import GaloisForLFunctions.RHTower.Sieve.WindowDisjointness

/-!
# Gallagher's discrete-to-integral transfer, for an arbitrary `C¹` function

`Sieve/GallagherSum` states the transfer for an exponential sum.  The averaging step of Jutila's
large-values estimate needs it for `‖ζ(1/2+it)‖`-type functions, so the two ingredients already in
the corpus — the pointwise Sobolev bound `Sieve/GallagherSobolev.gallagher_sobolev` and the window
disjointness `Sieve/WindowDisjointness.sum_window_le` — are combined here for a general `C¹` `f`:

```text
∑_{r ≤ R} |f(λ_r)| ≤ δ^{-1}∫_A^{λ_R+δ/2}|f| + ∫_A^{λ_R+δ/2}|f'| ,
```

for `δ`-gapped `λ`.  The right-hand side no longer mentions the points, which is the whole content:
a discrete family of values is paid by one integral over the enclosing interval plus the derivative
integral, with no sum of reciprocal separations anywhere.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Gallagher's transfer for a general `C¹` function.** -/
theorem sum_abs_le_gallagher_general {f f' : ℝ → ℝ} {lam : ℕ → ℝ} {δ A : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hcont' : Continuous f')
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hA : A ≤ lam 0 - δ / 2) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), |f (lam r)|
      ≤ (1 / δ) * (∫ t in A..(lam R + δ / 2), |f t|)
        + (∫ t in A..(lam R + δ / 2), |f' t|) := by
  have hcontf : Continuous f := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (hderiv x).continuousAt
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hterm : ∀ r ∈ Finset.range (R + 1),
      |f (lam r)|
        ≤ (1 / δ) * (∫ t in (lam r - δ / 2)..(lam r + δ / 2), |f t|)
          + (∫ t in (lam r - δ / 2)..(lam r + δ / 2), |f' t|) := by
    intro r _
    have h := gallagher_sobolev (f := f) (f' := f') (a := lam r) (h := δ / 2) hhalf
      (fun x _ => hderiv x) (hcont'.continuousOn)
    have hrw : (1 : ℝ) / (2 * (δ / 2)) = 1 / δ := by
      congr 1
      ring
    rwa [hrw] at h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_window_le (g := fun t => |f t|) hcontf.abs (fun t => abs_nonneg _) hδ hgap hA R
  have h2 := sum_window_le (g := fun t => |f' t|) hcont'.abs (fun t => abs_nonneg _) hδ hgap hA R
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hδinv
  linarith

end RHTower.Sieve
