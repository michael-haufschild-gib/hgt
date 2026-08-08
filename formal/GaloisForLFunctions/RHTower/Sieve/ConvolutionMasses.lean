import GaloisForLFunctions.RHTower.Sieve.ConvolutionSupport
/-!
# The masses of a convolution

The damped `ℓ¹` mass is submultiplicative under Dirichlet convolution: grouping the product set `[1,M]²` by the value
of the product, each fibre dominates the corresponding convolution coefficient, because a nonzero term of the
antidiagonal has both factors in the supports.  Hence

`∑_{k ≤ M²} ‖(a ⍟ b)(k)‖k^{−σ} ≤ (∑_d ‖a_d‖d^{−σ})(∑_e ‖b_e‖e^{−σ})`,

and since a sum of squares is at most the square of the sum for nonnegative terms, the `ℓ²` mass of the convolution
is at most the square of that product.

This is what the large-values first moment consumes for the product `L(a,s)L(b,s) = L(a ⍟ b, s)`.  The `ℓ¹` route is
taken in preference to the sharper `4·(ℓ² mass)(ℓ² mass)`: for prime weights with logarithmic coefficients the two
are of the same order — `(∑_p log p·p^{−σ})² ≍ (log N)²` against `4·cap(2σ)² ≍ (log N)⁴` at `σ = 1 + 1/log N`, so the
`ℓ¹` bound is in fact the better of the two — and it avoids the divisor-count case analysis entirely.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **The damped `ℓ¹` mass is submultiplicative under convolution.**  Grouping the product set by the value of the
product, each fibre dominates the corresponding convolution coefficient. -/
theorem sum_norm_convolution_mul_rpow_le {a b : ℕ → ℂ} {M : ℕ}
    (ha : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hb : ∀ k : ℕ, b k ≠ 0 → k ∈ Finset.Icc 1 M)
    (σ : ℝ) :
    (∑ k ∈ Finset.Icc 1 (M * M), ‖(LSeries.convolution a b) k‖ * (k : ℝ) ^ (-σ))
      ≤ (∑ d ∈ Finset.Icc 1 M, ‖a d‖ * (d : ℝ) ^ (-σ))
          * ∑ e ∈ Finset.Icc 1 M, ‖b e‖ * (e : ℝ) ^ (-σ) := by
  classical
  set P : Finset (ℕ × ℕ) := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M) with hP
  set G : ℕ × ℕ → ℝ := fun x => (‖a x.1‖ * (x.1 : ℝ) ^ (-σ)) * (‖b x.2‖ * (x.2 : ℝ) ^ (-σ)) with hG
  have hprod : (∑ d ∈ Finset.Icc 1 M, ‖a d‖ * (d : ℝ) ^ (-σ))
      * (∑ e ∈ Finset.Icc 1 M, ‖b e‖ * (e : ℝ) ^ (-σ)) = ∑ x ∈ P, G x := by
    rw [hP, hG, Finset.sum_product]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
  rw [hprod]
  -- group the product set by the value of the product
  have hmaps : ∀ x ∈ P, x.1 * x.2 ∈ Finset.Icc 1 (M * M) := by
    intro x hx
    rw [hP, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    exact Nat.mul_le_mul hx.1.2 hx.2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps G]
  refine Finset.sum_le_sum fun k hk => ?_
  -- the fibre dominates the coefficient
  have hexp : ∀ x ∈ Finset.filter (fun x => x.1 * x.2 = k) P,
      ‖a x.1 * b x.2‖ * (k : ℝ) ^ (-σ) = G x := by
    intro x hx
    rw [Finset.mem_filter, hP, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx
    obtain ⟨⟨h1, h2⟩, hmul⟩ := hx
    have h1pos : (0 : ℝ) < (x.1 : ℝ) := by
      have : 0 < x.1 := by omega
      exact_mod_cast this
    have h2pos : (0 : ℝ) < (x.2 : ℝ) := by
      have : 0 < x.2 := by omega
      exact_mod_cast this
    have hk' : ((k : ℕ) : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
      rw [← hmul]
      push_cast
      ring
    rw [hG, hk', Real.mul_rpow h1pos.le h2pos.le, norm_mul]
    ring
  rw [← Finset.sum_congr rfl hexp, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  rw [LSeries.convolution_def]
  refine le_trans (norm_sum_le _ _) ?_
  have hsub : Finset.filter (fun x => ‖a x.1 * b x.2‖ ≠ 0) k.divisorsAntidiagonal
      ⊆ Finset.filter (fun x => x.1 * x.2 = k) P := by
    intro x hx
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hmul, hk0⟩, hne⟩ := hx
    have hane : a x.1 ≠ 0 := by
      intro h
      rw [h, zero_mul, norm_zero] at hne
      exact hne rfl
    have hbne : b x.2 ≠ 0 := by
      intro h
      rw [h, mul_zero, norm_zero] at hne
      exact hne rfl
    rw [Finset.mem_filter, hP, Finset.mem_product]
    exact ⟨⟨ha x.1 hane, hb x.2 hbne⟩, hmul⟩
  calc (∑ x ∈ k.divisorsAntidiagonal, ‖a x.1 * b x.2‖)
      = ∑ x ∈ Finset.filter (fun x => ‖a x.1 * b x.2‖ ≠ 0) k.divisorsAntidiagonal,
          ‖a x.1 * b x.2‖ := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ x ∈ Finset.filter (fun x => x.1 * x.2 = k) P, ‖a x.1 * b x.2‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)

end RHTower.Sieve
end

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- The mean square is at most the square of the first moment, for nonnegative terms. -/
theorem sum_sq_le_sq_sum_of_nonneg {s : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ k ∈ s, 0 ≤ x k) :
    ∑ k ∈ s, (x k) ^ 2 ≤ (∑ k ∈ s, x k) ^ 2 := by
  classical
  have hle : ∀ k ∈ s, (x k) ^ 2 ≤ x k * ∑ j ∈ s, x j := by
    intro k hk
    have hsum : x k ≤ ∑ j ∈ s, x j := Finset.single_le_sum hx hk
    calc (x k) ^ 2 = x k * x k := sq (x k)
      _ ≤ x k * ∑ j ∈ s, x j := mul_le_mul_of_nonneg_left hsum (hx k hk)
  refine le_trans (Finset.sum_le_sum hle) (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

/-- **The `ℓ²` mass of a convolution.**  At most the square of the product of the two damped `ℓ¹` masses. -/
theorem sum_normSq_convolution_le {a b : ℕ → ℂ} {M : ℕ}
    (ha : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hb : ∀ k : ℕ, b k ≠ 0 → k ∈ Finset.Icc 1 M)
    (σ : ℝ) :
    (∑ k ∈ Finset.Icc 1 (M * M), (‖(LSeries.convolution a b) k‖ * (k : ℝ) ^ (-σ)) ^ 2)
      ≤ ((∑ d ∈ Finset.Icc 1 M, ‖a d‖ * (d : ℝ) ^ (-σ))
          * ∑ e ∈ Finset.Icc 1 M, ‖b e‖ * (e : ℝ) ^ (-σ)) ^ 2 := by
  classical
  refine le_trans (sum_sq_le_sq_sum_of_nonneg (fun k _ => by positivity)) ?_
  have hL1 := sum_norm_convolution_mul_rpow_le ha hb σ
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 (M * M), ‖(LSeries.convolution a b) k‖ * (k : ℝ) ^ (-σ) :=
    Finset.sum_nonneg fun k _ => by positivity
  exact pow_le_pow_left₀ hnn hL1 2

end RHTower.Sieve
end
