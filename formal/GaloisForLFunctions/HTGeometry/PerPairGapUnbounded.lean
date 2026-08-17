import GaloisForLFunctions.HTGeometry.TopLayerNonneg

/-!
# The per-pair relaxation is off by an unbounded factor

Certifying several conjugate pairs one at a time — splitting the compared sum into one summand per
pair and applying the exact one-pair criterion to each — costs the sum of the individual amplitudes.
The true cost is the supremum of the *joint* comparison function, and the two can differ by a factor
growing with the number of pairs.

The witness is the Fejér mechanism.  Taking the `n(n-1)` ordered pairs `(j,k)` with `j ≠ k` from
`{0,…,n-1}` as the pair data, with comparison terms `-cos((j-k)θ)`, the joint comparison function
never exceeds `n`, because the full double sum over *all* ordered pairs is
`‖∑_j e^{ijθ}‖² ≥ 0` and the diagonal contributes exactly `n`.  Each individual term, however, has
supremum `1`, so certifying separately costs `n(n-1)`.

So no per-pair relaxation can decide realizability: it is not merely inexact, its error is unbounded.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **The Dirichlet-kernel positivity.**  The double sum of cosines of all index differences is a
squared modulus, hence nonnegative. -/
theorem sum_sum_cos_sub_nonneg (n : ℕ) (θ : ℝ) :
    0 ≤ ∑ j : Fin n, ∑ k : Fin n, Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) := by
  set z : Fin n → ℂ := fun j => Complex.exp (((j : ℝ) * θ : ℝ) * Complex.I) with hz
  have hterm : ∀ j k : Fin n, (z j * (starRingEnd ℂ) (z k)).re
      = Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) := by
    intro j k
    have hconj : (starRingEnd ℂ) (z k) = Complex.exp ((-((k : ℝ) * θ) : ℝ) * Complex.I) := by
      rw [hz, ← Complex.exp_conj]
      congr 1
      simp
    rw [hz]
    simp only []
    rw [hconj, ← Complex.exp_add]
    rw [show ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I + (((-((k : ℝ) * θ)) : ℝ) : ℂ) * Complex.I)
        = ((((j : ℝ) * θ - (k : ℝ) * θ : ℝ)) : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  have hkey : Complex.normSq (∑ j, z j)
      = ∑ j : Fin n, ∑ k : Fin n, Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) := by
    have h1 : ((Complex.normSq (∑ j, z j) : ℝ) : ℂ)
        = ∑ j : Fin n, ∑ k : Fin n, z j * (starRingEnd ℂ) (z k) := by
      rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re, Complex.re_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hterm j k)
  rw [← hkey]
  exact Complex.normSq_nonneg _

/-- **The joint comparison function is small.**  Summing `-cos((j-k)θ)` over all ordered pairs with
`j ≠ k` never exceeds `n`, uniformly in `θ`. -/
theorem offDiagonal_sum_le (n : ℕ) (θ : ℝ) :
    ∑ j : Fin n, ∑ k : Fin n,
        (if j = k then (0 : ℝ) else -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ)) ≤ n := by
  classical
  have hsplit : ∀ j k : Fin n,
      (if j = k then (0 : ℝ) else -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ))
        = -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ)
          + (if k = j then Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) else 0) := by
    intro j k
    by_cases h : j = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun hcon => h hcon.symm), add_zero]
  have hdiag : ∀ j : Fin n,
      (∑ k : Fin n, if k = j then Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) else 0) = 1 := by
    intro j
    rw [Finset.sum_ite_eq' Finset.univ j (fun k => Real.cos ((j : ℝ) * θ - (k : ℝ) * θ))]
    simp
  have hrw : ∑ j : Fin n, ∑ k : Fin n,
      (if j = k then (0 : ℝ) else -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ))
      = -(∑ j : Fin n, ∑ k : Fin n, Real.cos ((j : ℝ) * θ - (k : ℝ) * θ)) + n := by
    rw [show (∑ j : Fin n, ∑ k : Fin n,
        (if j = k then (0 : ℝ) else -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ)))
        = ∑ j : Fin n, ∑ k : Fin n, (-Real.cos ((j : ℝ) * θ - (k : ℝ) * θ)
            + (if k = j then Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) else 0)) from
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hsplit j k))]
    rw [show (∑ j : Fin n, ∑ k : Fin n, (-Real.cos ((j : ℝ) * θ - (k : ℝ) * θ)
          + (if k = j then Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) else 0)))
        = (∑ j : Fin n, ∑ k : Fin n, -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ))
          + ∑ j : Fin n, ∑ k : Fin n,
              (if k = j then Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) else 0) from by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [← Finset.sum_add_distrib])]
    congr 1
    · rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [← Finset.sum_neg_distrib])
    · rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hdiag j)]
      simp
  rw [hrw]
  have := sum_sum_cos_sub_nonneg n θ
  linarith

/-- A constant dominating `-cos(dθ)` for all `θ` is at least `1`. -/
theorem one_le_of_forall_neg_cos_le {d ρ : ℝ} (hd : d ≠ 0)
    (h : ∀ θ : ℝ, -Real.cos (d * θ) ≤ ρ) : 1 ≤ ρ := by
  have hval := h (Real.pi / d)
  rw [mul_div_cancel₀ _ hd, Real.cos_pi] at hval
  linarith

/-- **The per-pair cost.**  Certifying the `n(n-1)` pairs separately costs at least `n(n-1)`. -/
theorem per_pair_cost_ge (n : ℕ) (ρ : Fin n → Fin n → ℝ)
    (h : ∀ j k : Fin n, j ≠ k → ∀ θ : ℝ,
      -Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) ≤ ρ j k) :
    (n : ℝ) * ((n : ℝ) - 1)
      ≤ ∑ j : Fin n, ∑ k : Fin n, (if j = k then (0 : ℝ) else ρ j k) := by
  classical
  have hone : ∀ j k : Fin n, j ≠ k → 1 ≤ ρ j k := by
    intro j k hjk
    refine one_le_of_forall_neg_cos_le (d := (j : ℝ) - (k : ℝ)) ?_ (fun θ => ?_)
    · have : ((j : ℕ) : ℝ) ≠ ((k : ℕ) : ℝ) := by
        exact_mod_cast Fin.val_ne_of_ne hjk
      intro hcon
      exact this (by linarith [sub_eq_zero.mp hcon])
    · have hrw : ((j : ℝ) - (k : ℝ)) * θ = (j : ℝ) * θ - (k : ℝ) * θ := by ring
      rw [hrw]
      exact h j k hjk θ
  have hlower : ∀ j k : Fin n,
      (if j = k then (0 : ℝ) else 1) ≤ (if j = k then (0 : ℝ) else ρ j k) := by
    intro j k
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos hjk]
    · rw [if_neg hjk, if_neg hjk]
      exact hone j k hjk
  have hcount : ∑ j : Fin n, ∑ k : Fin n, (if j = k then (0 : ℝ) else 1)
      = (n : ℝ) * ((n : ℝ) - 1) := by
    have hinner : ∀ j : Fin n, (∑ k : Fin n, if j = k then (0 : ℝ) else 1) = (n : ℝ) - 1 := by
      intro j
      have hsplit : ∀ k : Fin n, (if j = k then (0 : ℝ) else 1)
          = 1 - (if k = j then (1 : ℝ) else 0) := by
        intro k
        by_cases h' : j = k
        · subst h'; simp
        · rw [if_neg h', if_neg (fun hcon => h' hcon.symm)]; ring
      rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hsplit k),
        Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hinner j)]
    simp
    ring
  calc (n : ℝ) * ((n : ℝ) - 1)
      = ∑ j : Fin n, ∑ k : Fin n, (if j = k then (0 : ℝ) else 1) := hcount.symm
    _ ≤ ∑ j : Fin n, ∑ k : Fin n, (if j = k then (0 : ℝ) else ρ j k) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hlower j k))

end GaloisForLFunctions.HTGeometry
