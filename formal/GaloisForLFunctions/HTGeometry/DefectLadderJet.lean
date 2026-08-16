import GaloisForLFunctions.HTGeometry.IteratedDerivVanishing

/-!
# The jet of the bottom rung of a defect ladder

A *ladder* is a sequence of functions `A 0, A 1, …` in which the derivative of each rung is a
multiple of the next rung corrected by a term proportional to the bottom rung:

`(A m)' = -(c m · A (m+1)) - A 0 · E m`.

If the rungs below level `d` vanish at a point, the correction terms are invisible to the first
`d` derivatives there, and each rung has the pure descending jet

`A m ^ (r) = (-1)^r c m c (m+1) ⋯ c (m+r-1) · A (m+r)`.

In particular the bottom rung is flat to order `d-1` and its first surviving derivative is the
signed descending product of the ladder constants times the first nonvanishing rung.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The ladder jet.**  Below the contact order every rung differentiates by descending the
ladder: the correction proportional to the (flat) bottom rung contributes nothing. -/
theorem iteratedDeriv_ladder {A E : ℕ → ℝ → ℝ} {c : ℕ → ℝ} {y₀ : ℝ}
    (hA : ∀ m, ∀ k : ℕ, ContDiffAt ℝ k (A m) y₀)
    (hE : ∀ m, ∀ k : ℕ, ContDiffAt ℝ k (E m) y₀)
    (hladder : ∀ m, deriv (A m) =ᶠ[𝓝 y₀] fun t => -(c m * A (m + 1) t) - A 0 t * E m t)
    {d : ℕ} (hvan : ∀ j < d, A j y₀ = 0) :
    ∀ r ≤ d, ∀ m, iteratedDeriv r (A m) y₀
      = (-1) ^ r * (∏ j ∈ Finset.range r, c (m + j)) * A (m + r) y₀ := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
      match r with
      | 0 => intro _ m; simp
      | (q + 1) =>
          intro hrd m
          have hflat : ∀ j ≤ q, iteratedDeriv j (A 0) y₀ = 0 := by
            intro j hj
            have hj' := ih j (by omega) (by omega) 0
            rw [hj', hvan (0 + j) (by omega), mul_zero]
          have hstep := ih q (by omega) (by omega) (m + 1)
          have hsub : (fun t => -(c m * A (m + 1) t) - A 0 t * E m t)
              = (fun t => -(c m * A (m + 1) t)) - fun t => A 0 t * E m t := rfl
          have hneg : (fun t => -(c m * A (m + 1) t)) = -fun t => c m * A (m + 1) t := rfl
          have hcd1 : ContDiffAt ℝ (q : ℕ) (fun t => -(c m * A (m + 1) t)) y₀ :=
            ((contDiffAt_const (c := c m)).mul (hA (m + 1) q)).neg
          have hcd2 : ContDiffAt ℝ (q : ℕ) (fun t => A 0 t * E m t) y₀ :=
            (hA 0 q).mul (hE m q)
          have hzero : iteratedDeriv q (fun t => A 0 t * E m t) y₀ = 0 :=
            iteratedDeriv_mul_eq_zero_of_vanishing q (hA 0) (hE m) hflat
          have hlin : iteratedDeriv q (fun t => -(c m * A (m + 1) t)) y₀
              = -(c m * iteratedDeriv q (A (m + 1)) y₀) := by
            rw [hneg, iteratedDeriv_neg, iteratedDeriv_const_mul (c m) (hA (m + 1) q)]
          have hprod : (∏ j ∈ Finset.range (q + 1), c (m + j))
              = c m * ∏ j ∈ Finset.range q, c (m + 1 + j) := by
            rw [Finset.prod_range_succ']
            have hre : (∏ j ∈ Finset.range q, c (m + (j + 1)))
                = ∏ j ∈ Finset.range q, c (m + 1 + j) :=
              Finset.prod_congr rfl fun j _ => congrArg c (by omega)
            rw [hre, Nat.add_zero]
            exact mul_comm _ _
          have hidx : m + (q + 1) = m + 1 + q := by omega
          rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq q (hladder m), hsub,
            iteratedDeriv_sub hcd1 hcd2, hlin, hzero, sub_zero, hstep, hprod, hidx]
          ring

/-- **The bottom rung is flat below the contact order.** -/
theorem iteratedDeriv_ladder_bottom_eq_zero {A E : ℕ → ℝ → ℝ} {c : ℕ → ℝ} {y₀ : ℝ}
    (hA : ∀ m, ∀ k : ℕ, ContDiffAt ℝ k (A m) y₀)
    (hE : ∀ m, ∀ k : ℕ, ContDiffAt ℝ k (E m) y₀)
    (hladder : ∀ m, deriv (A m) =ᶠ[𝓝 y₀] fun t => -(c m * A (m + 1) t) - A 0 t * E m t)
    {d : ℕ} (hvan : ∀ j < d, A j y₀ = 0) {r : ℕ} (hr : r < d) :
    iteratedDeriv r (A 0) y₀ = 0 := by
  rw [iteratedDeriv_ladder hA hE hladder hvan r (by omega) 0, hvan (0 + r) (by omega), mul_zero]

/-- **The first surviving jet of the bottom rung.**  At the contact order the bottom rung acquires
the signed descending product of the ladder constants times the first nonvanishing rung. -/
theorem iteratedDeriv_ladder_bottom_top {A E : ℕ → ℝ → ℝ} {c : ℕ → ℝ} {y₀ : ℝ}
    (hA : ∀ m, ∀ k : ℕ, ContDiffAt ℝ k (A m) y₀)
    (hE : ∀ m, ∀ k : ℕ, ContDiffAt ℝ k (E m) y₀)
    (hladder : ∀ m, deriv (A m) =ᶠ[𝓝 y₀] fun t => -(c m * A (m + 1) t) - A 0 t * E m t)
    {d : ℕ} (hvan : ∀ j < d, A j y₀ = 0) :
    iteratedDeriv d (A 0) y₀ = (-1) ^ d * (∏ j ∈ Finset.range d, c j) * A d y₀ := by
  have h := iteratedDeriv_ladder hA hE hladder hvan d le_rfl 0
  simpa using h

end GaloisForLFunctions.HTGeometry
