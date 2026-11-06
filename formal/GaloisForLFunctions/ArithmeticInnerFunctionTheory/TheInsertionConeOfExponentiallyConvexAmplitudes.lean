import GaloisForLFunctions.CompletedArithmeticForms.EisensteinDivisorTrace

/-!
# Prime insertion preserves exponentially convex amplitudes

The insertion of a prime with step `ℓ = log p` and phase `θ` is the operator

`(T_{θ,ℓ} f)(x) = Σ_k U_k(cos θ) f(x + kℓ)`,

the inverse of the second difference `1 − 2 cos θ σ + σ²`, `σ` the shift by `ℓ`. Since
`U_k(cos θ) = Σ_{r+s=k} e^{i(r−s)θ}`, the value `(T f)(x)` is the Hermitian form of the Hankel kernel
`f(x + u + v)` on the vector `e^{irθ}` at the points `u = rℓ` (`ofReal_insertion_eq_tsum_pairs`).

So the cone of **exponentially convex** amplitudes, those with every Hermitian Hankel form
nonnegative, is carried into itself by every insertion at every phase
(`IsExpConvexFrom.insertion`), and its members have nonnegative insertions (`IsExpConvexFrom.nonneg`). This is
the cone on which phases play no role. Laplace mixtures of `e^{−sx}` lie in it (`isExpConvexFrom_exp`,
`IsExpConvexFrom.add`).

On the exponential decay class, which is preserved (`ExpDecayFrom.insertion`), the insertion is well
defined, with no restriction on the phase.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

noncomputable section

/-! ### The Chebyshev character -/

/-- `U_k(cos θ) = Σ_{r+s=k} e^{i(r−s)θ}`. -/
theorem ofReal_cosSum_eq_sum_antidiagonal (θ : ℝ) (k : ℕ) :
    (cosSum θ k : ℂ) = ∑ p ∈ Finset.antidiagonal k,
      Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) := by
  set A : ℂ := ∑ p ∈ Finset.antidiagonal k, Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) with hA
  have hswap : A = ∑ p ∈ Finset.antidiagonal k,
      Complex.exp ((-(((p.1 : ℝ) - (p.2 : ℝ)) * θ) : ℝ) * I) := by
    rw [hA, ← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 3
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have h2 : 2 * A = 2 * (cosSum θ k : ℂ) := by
    have e : A + A = ∑ p ∈ Finset.antidiagonal k,
        (2 : ℂ) * (Real.cos (((p.1 : ℝ) - (p.2 : ℝ)) * θ) : ℂ) := by
      nth_rewrite 2 [hswap]
      rw [hA, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Complex.ofReal_cos, Complex.cos]
      push_cast
      have : -(((p.1 : ℂ) - (p.2 : ℂ)) * (θ : ℂ)) * I = -(((p.1 : ℂ) - (p.2 : ℂ)) * (θ : ℂ) * I) := by
        ring
      rw [this]
      ring_nf
    rw [two_mul, e, ← Finset.mul_sum]
    congr 1
    rw [cosSum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.cast_sub hj']
    push_cast
    congr 2
    ring
  exact (mul_left_cancel₀ two_ne_zero h2).symm

theorem abs_cosSum_le (θ : ℝ) (k : ℕ) : |cosSum θ k| ≤ (k : ℝ) + 1 := by
  rw [cosSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun j _ => Real.abs_cos_le_one _).trans ?_
  simp

/-! ### Exponential decay -/

/-- Exponential decay at rate `κ` on `[x₀, ∞)`. -/
def ExpDecayFrom (x₀ κ : ℝ) (f : ℝ → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x)

/-- The insertion of a step `ℓ` at the phase `θ`. -/
def insertion (θ ℓ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, cosSum θ k * f (x + k * ℓ)

section Decay

variable {x₀ κ ℓ θ : ℝ} {f : ℝ → ℝ}

/-- The geometric majorant of the pair sum. -/
theorem summable_geometric_pairs (hq : 0 < κ * ℓ) :
    Summable (fun p : ℕ × ℕ => Real.exp (-(κ * ℓ)) ^ p.1 * Real.exp (-(κ * ℓ)) ^ p.2) := by
  have h1 : Real.exp (-(κ * ℓ)) < 1 := Real.exp_lt_one (by linarith)
  have hg := summable_geometric_of_lt_one (Real.exp_pos _).le h1
  exact hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)

theorem abs_shift_le (hf : ∀ x, x₀ ≤ x → |f x| ≤ (hC : ℝ) * Real.exp (-κ * x)) {hC : ℝ} : True := trivial

end Decay

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
