import Mathlib

/-!
# Log-concavity of a mixture: mean curvature against the variance of the log-slopes

A sum of log-concave functions need not be log-concave, so the log-concavity of a kernel presented as
a series — the theta kernel of the Riemann `ξ`-function among them — is not inherited term by term.
The exact obstruction is a variance.  Writing `Φ = ∑ φ_j` with `φ_j > 0`, and

```text
a j = (log φ_j)′ ,      c j = −(log φ_j)″ ,      w j = φ_j / Φ ,
```

so that `φ_j′ = a j · φ_j` and `φ_j″ = (a j² − c j) · φ_j`, one has the exact identity

```text
Φ″Φ − (Φ′)²  =  ½ ∑_{j,k} φ_j φ_k [ (a j − a k)² − c j − c k ] ,
```

equivalently

```text
−(log Φ)″  =  E_w[c]  −  ½ ∑_{j,k} w_j w_k (a j − a k)²  =  E_w[c] − Var_w[a] .
```

**A mixture of log-concave functions is log-concave exactly when the weighted mean curvature beats
the weighted variance of the log-slopes.**  When one term dominates — as for a theta series on the
range where the smallest frequency wins — the variance is exponentially small and the mixture
inherits the curvature of that term.

Everything here is algebra on finite sums; the derivative hypotheses enter only through the pointwise
relations `φ′ = aφ`, `φ″ = (a² − c)φ`, which is how they are used downstream.
-/

open Finset

namespace GaloisForLFunctions

namespace MixtureLogConcavity

variable {ι : Type*} (F : Finset ι) (φ a c : ι → ℝ)

/-- `Φ · ∑ (a² − c)φ` as a double sum. -/
theorem prod_sum_eq (f g : ι → ℝ) :
    (∑ j ∈ F, f j) * (∑ k ∈ F, g k) = ∑ j ∈ F, ∑ k ∈ F, f j * g k := by
  rw [Finset.sum_mul_sum]

/-- **The mixture curvature identity**, both sides as double sums.  Purely algebraic. -/
theorem mixture_curvature_identity :
    2 * ((∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a k ^ 2 - c k))
        - ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j * a k))
      = ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * ((a j - a k) ^ 2 - c j - c k) := by
  have hswap : ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j ^ 2 - c j)
      = ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a k ^ 2 - c k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hjoin : ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * ((a j - a k) ^ 2 - c j - c k)
      = (∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j ^ 2 - c j))
        + (∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a k ^ 2 - c k))
        - 2 * ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j * a k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hjoin, hswap]
  ring

/-- **Sufficient condition for mixture log-concavity, with a margin.**  If every term has curvature
at least `C` and the weighted variance of the log-slopes is at most `E`, then the mixture has
log-curvature at least `C − E`.  Applied to a theta-type series, `C` is the curvature of the dominant
term and `E` is exponentially small in the frequency gap. -/
theorem mixture_curvature_ge (hφ : ∀ j ∈ F, 0 ≤ φ j) {C E : ℝ}
    (hC : ∀ j ∈ F, C ≤ c j)
    (hE : (∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j - a k) ^ 2) ≤ 2 * E * (∑ j ∈ F, φ j) ^ 2) :
    (C - E) * (∑ j ∈ F, φ j) ^ 2
      ≤ (∑ j ∈ F, a j * φ j) ^ 2 - (∑ j ∈ F, φ j) * (∑ k ∈ F, (a k ^ 2 - c k) * φ k) := by
  have e1 : (∑ j ∈ F, φ j) * (∑ k ∈ F, (a k ^ 2 - c k) * φ k)
      = ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a k ^ 2 - c k) := by
    rw [prod_sum_eq]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ j ∈ F, a j * φ j) ^ 2 = ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j * a k) := by
    rw [sq, prod_sum_eq]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hid := mixture_curvature_identity F φ a c
  have hcsplit : ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * ((a j - a k) ^ 2 - c j - c k)
      = (∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (a j - a k) ^ 2)
        - ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (c j + c k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hcbig : 2 * C * (∑ j ∈ F, φ j) ^ 2
      ≤ ∑ j ∈ F, ∑ k ∈ F, φ j * φ k * (c j + c k) := by
    have hpp : (∑ j ∈ F, φ j) ^ 2 = ∑ j ∈ F, ∑ k ∈ F, φ j * φ k := by
      rw [sq, prod_sum_eq]
    rw [hpp, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hjk : 0 ≤ φ j * φ k := mul_nonneg (hφ j hj) (hφ k hk)
    have : 2 * C ≤ c j + c k := by linarith [hC j hj, hC k hk]
    nlinarith [hjk, this]
  rw [e1, e2]
  rw [hcsplit] at hid
  linarith [hid, hE, hcbig]

end MixtureLogConcavity

end GaloisForLFunctions
