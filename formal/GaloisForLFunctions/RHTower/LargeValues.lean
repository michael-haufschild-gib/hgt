/-
Toward the Gallagher–Halász large-values inequality: the Sobolev route.

The large-values inequality bounds a sum of `|D(t_r)|²` over well-separated points by the `L²` mass of
`D` and `D'` — the mechanism that turns a mean-value (second-moment) bound into a bound on the number
of *large values* of a Dirichlet polynomial, and hence (through a mollifier) on the number of zeros of
ζ right of the critical line.  This file builds the Sobolev foundation:

* `sqNorm_hasDerivAt` — the derivative of `t ↦ ‖f t‖²` is `2⟪f, f'⟫`, bounded by `2‖f‖‖f'‖`.
* `two_mul_le_div_add_mul` — the AM–GM split `2ab ≤ a²/η + η b²`, which lets the cross term
  `∫ 2‖f‖‖f'‖` be absorbed into `∫‖f‖²` and `∫‖f'‖²` without an integral Cauchy–Schwarz.
* `sobolev_pointwise` — for `t` in an interval `[c, c+δ]`, `‖f t‖² ≤ δ^{-1}∫‖f‖² + 2∫‖f‖‖f'‖`:
  the value at any point is controlled by the interval's `L²` mass plus the derivative cross term.

The summed inequality over separated points (each with its own interval) and the mollifier assembly
build on these.
-/
import Mathlib

open RealInnerProductSpace MeasureTheory intervalIntegral

namespace RHTower

/-- The derivative of `t ↦ ‖f t‖²` is `2⟪f x, f' x⟫_ℝ`. -/
theorem sqNorm_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => ‖f t‖ ^ 2) (2 * inner ℝ (f x) f') x := by
  have hi := HasDerivAt.inner ℝ h h
  have heq : (fun t => inner ℝ (f t) (f t)) = (fun t => ‖f t‖ ^ 2) := by
    funext t; exact real_inner_self_eq_norm_sq (f t)
  rw [heq] at hi
  have hsymm : inner ℝ (f x) f' + inner ℝ f' (f x) = 2 * inner ℝ (f x) f' := by
    rw [real_inner_comm f' (f x)]; ring
  rwa [hsymm] at hi

/-- The derivative of `‖f‖²` is bounded in absolute value by `2‖f‖‖f'‖`. -/
theorem abs_sqNorm_deriv_le {f : ℝ → ℂ} {f' : ℂ} (x : ℝ) :
    |2 * inner ℝ (f x) f'| ≤ 2 * (‖f x‖ * ‖f'‖) := by
  rw [abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (f x) f') (by norm_num)

/-- **AM–GM split.**  For `η > 0` and `a, b ≥ 0`, `2ab ≤ a²/η + η b²` (equivalently
`0 ≤ (a − ηb)²/η`).  This absorbs the Sobolev cross term into the two `L²` masses. -/
theorem two_mul_le_div_add_mul {a b η : ℝ} (hη : 0 < η) :
    2 * (a * b) ≤ a ^ 2 / η + η * b ^ 2 := by
  rw [div_add' _ _ _ (ne_of_gt hη), le_div_iff₀ hη]
  nlinarith [sq_nonneg (a - η * b)]

/-- **The Sobolev pointwise bound.**  For `f` differentiable on `[c, c+δ]` (δ > 0), the value `‖f t‖²`
at any point `t` of the interval is bounded by the interval's mean `L²` mass plus the derivative
cross term: `‖f t‖² ≤ δ^{-1}∫_c^{c+δ}‖f‖² + ∫_c^{c+δ} 2‖f‖‖f'‖`.  Proof: `g = ‖f‖²` has derivative
`2⟪f,f'⟫` of size `≤ 2‖f‖‖f'‖`; the fundamental theorem gives `g t − g u = ∫_u^t g'`, bounded by
`∫_c^{c+δ}|g'|` for every `u`; integrating that inequality over `u ∈ [c,c+δ]` divides by `δ`. -/
theorem sobolev_pointwise {f f' : ℝ → ℂ} {c δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ y ∈ Set.uIcc c (c + δ), HasDerivAt f (f' y) y)
    (hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume c (c + δ))
    (hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume c (c + δ))
    (hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume c (c + δ))
    {t : ℝ} (ht : t ∈ Set.Icc c (c + δ)) :
    ‖f t‖ ^ 2 ≤ (1 / δ) * (∫ u in c..c + δ, ‖f u‖ ^ 2)
      + ∫ u in c..c + δ, 2 * (‖f u‖ * ‖f' u‖) := by
  have hcd : c ≤ c + δ := by linarith
  have huIcc_eq : Set.uIcc c (c + δ) = Set.Icc c (c + δ) := Set.uIcc_of_le hcd
  set g : ℝ → ℝ := fun y => ‖f y‖ ^ 2 with hg
  set g' : ℝ → ℝ := fun y => 2 * inner ℝ (f y) (f' y) with hg'
  have hgderiv : ∀ y ∈ Set.uIcc c (c + δ), HasDerivAt g (g' y) y :=
    fun y hy => sqNorm_hasDerivAt (hf y hy)
  have habs_int : IntervalIntegrable (fun y => |g' y|) volume c (c + δ) := hg'int.abs
  have ht' : t ∈ Set.uIcc c (c + δ) := huIcc_eq ▸ ht
  -- sub-interval bound: |∫_u^t g'| ≤ ∫_c^{c+δ}|g'|
  have hsub : ∀ u ∈ Set.Icc c (c + δ), |∫ y in u..t, g' y| ≤ ∫ y in c..c + δ, |g' y| := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨ht1, ht2⟩ := ht
    rcases le_total u t with hut | hut
    · calc |∫ y in u..t, g' y| ≤ ∫ y in u..t, |g' y| := abs_integral_le_integral_abs hut
        _ ≤ ∫ y in c..c + δ, |g' y| :=
            integral_mono_interval hu1 hut ht2
              (Filter.Eventually.of_forall (fun y => abs_nonneg _)) habs_int
    · rw [intervalIntegral.integral_symm, abs_neg]
      calc |∫ y in t..u, g' y| ≤ ∫ y in t..u, |g' y| := abs_integral_le_integral_abs hut
        _ ≤ ∫ y in c..c + δ, |g' y| :=
            integral_mono_interval ht1 hut hu2
              (Filter.Eventually.of_forall (fun y => abs_nonneg _)) habs_int
  -- for each u: g t ≤ g u + ∫|g'|
  have hbound : ∀ u ∈ Set.Icc c (c + δ), g t ≤ g u + ∫ y in c..c + δ, |g' y| := by
    intro u hu
    have hu' : u ∈ Set.uIcc c (c + δ) := huIcc_eq ▸ hu
    have hsubset : Set.uIcc u t ⊆ Set.uIcc c (c + δ) := Set.uIcc_subset_uIcc hu' ht'
    have hftc : ∫ y in u..t, g' y = g t - g u :=
      integral_eq_sub_of_hasDerivAt (fun y hy => hgderiv y (hsubset hy))
        (hg'int.mono_set hsubset)
    have : g t - g u ≤ ∫ y in c..c + δ, |g' y| := by
      rw [← hftc]; exact le_trans (le_abs_self _) (hsub u hu)
    linarith
  -- integrate over u
  have hKint : IntervalIntegrable (fun _ : ℝ => ∫ y in c..c + δ, |g' y|) volume c (c + δ) :=
    intervalIntegrable_const
  have hIntmono := integral_mono_on hcd intervalIntegrable_const
    (hgint.add hKint) hbound
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hgint hKint,
    intervalIntegral.integral_const] at hIntmono
  simp only [add_sub_cancel_left, smul_eq_mul] at hIntmono
  -- hIntmono : δ * g t ≤ (∫ g) + δ * ∫|g'|
  have habs_le : (∫ y in c..c + δ, |g' y|) ≤ ∫ u in c..c + δ, 2 * (‖f u‖ * ‖f' u‖) :=
    integral_mono_on hcd habs_int hcrossint (fun y _ => abs_sqNorm_deriv_le y)
  have hg_t : g t ≤ (1 / δ) * (∫ u in c..c + δ, g u) + ∫ y in c..c + δ, |g' y| := by
    have hrw : (1 / δ) * (∫ u in c..c + δ, g u) + ∫ y in c..c + δ, |g' y|
        = ((∫ u in c..c + δ, g u) + δ * ∫ y in c..c + δ, |g' y|) / δ := by field_simp
    rw [hrw, le_div_iff₀ hδ]
    linarith [hIntmono]
  calc ‖f t‖ ^ 2 = g t := rfl
    _ ≤ (1 / δ) * (∫ u in c..c + δ, g u) + ∫ y in c..c + δ, |g' y| := hg_t
    _ ≤ (1 / δ) * (∫ u in c..c + δ, ‖f u‖ ^ 2) + ∫ u in c..c + δ, 2 * (‖f u‖ * ‖f' u‖) :=
        add_le_add (le_refl _) habs_le

/-- **The Gallagher grid sum.**  Summing the Sobolev bound over the `R` cells of the uniform grid
`A + kδ` (`k < R`) partitioning `[A, A+Rδ]`, the sum of `‖f‖²` at the left grid points is bounded by
the interval's `L²` mass and the derivative cross term:

  ∑_{k<R} ‖f(A+kδ)‖² ≤ δ^{-1}∫_A^{A+Rδ}‖f‖² + ∫_A^{A+Rδ} 2‖f‖‖f'‖.

Each cell contributes its Sobolev bound; the cell integrals telescope to the whole via
`sum_integral_adjacent_intervals`.  This is the discrete large-values shape: a sum over grid points is
controlled by a mean value (second moment) plus a derivative mean value. -/
theorem gallagher_grid {f f' : ℝ → ℂ} {A δ : ℝ} (hδ : 0 < δ) (R : ℕ)
    (hf : ∀ y ∈ Set.Icc A (A + R * δ), HasDerivAt f (f' y) y)
    (hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (A + R * δ))
    (hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume A (A + R * δ))
    (hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (A + R * δ)) :
    ∑ r ∈ Finset.range R, ‖f (A + r * δ)‖ ^ 2
      ≤ (1 / δ) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
        + ∫ u in A..A + R * δ, 2 * (‖f u‖ * ‖f' u‖) := by
  set a : ℕ → ℝ := fun k => A + k * δ with ha
  have hcell : ∀ k, k < R → Set.uIcc (a k) (a k + δ) ⊆ Set.Icc A (A + R * δ) := by
    intro k hk
    have h1 : A ≤ a k := by rw [ha]; nlinarith [Nat.cast_nonneg (α := ℝ) k, hδ.le]
    have h2 : a k + δ ≤ A + R * δ := by
      rw [ha]; have : ((k : ℝ) + 1) ≤ R := by exact_mod_cast Nat.succ_le_of_lt hk
      nlinarith [hδ.le]
    rw [Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc h1 h2
  have hAle : A ≤ A + R * δ := le_add_of_nonneg_right (by positivity)
  -- per-cell Sobolev bound at the left endpoint
  have hper : ∀ k ∈ Finset.range R, ‖f (a k)‖ ^ 2
      ≤ (1 / δ) * (∫ u in a k..a k + δ, ‖f u‖ ^ 2)
        + ∫ u in a k..a k + δ, 2 * (‖f u‖ * ‖f' u‖) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hsub := hcell k hk
    have hcellsub : Set.uIcc (a k) (a k + δ) ⊆ Set.uIcc A (A + R * δ) := by
      rw [Set.uIcc_of_le hAle]; exact hsub
    exact sobolev_pointwise hδ (fun y hy => hf y (hsub hy))
      (hg'int.mono_set hcellsub) (hgint.mono_set hcellsub) (hcrossint.mono_set hcellsub)
      ⟨le_refl _, by linarith [hδ.le]⟩
  -- adjacent-cell integrability (each cell ⊆ whole)
  have hadj : ∀ (h : ℝ → ℝ), IntervalIntegrable h volume A (A + R * δ) →
      ∀ k < R, IntervalIntegrable h volume (a k) (a (k + 1)) := by
    intro h hh k hk
    have : a (k + 1) = a k + δ := by rw [ha]; push_cast; ring
    rw [this]
    exact hh.mono_set (by
      rw [Set.uIcc_of_le (by linarith : A ≤ A + R * δ)]
      exact hcell k hk)
  have hsum1 : ∑ k ∈ Finset.range R, ∫ u in a k..a (k + 1), ‖f u‖ ^ 2
      = ∫ u in A..A + R * δ, ‖f u‖ ^ 2 := by
    rw [sum_integral_adjacent_intervals (hadj _ hgint)]; norm_num [ha]
  have hsum2 : ∑ k ∈ Finset.range R, ∫ u in a k..a (k + 1), 2 * (‖f u‖ * ‖f' u‖)
      = ∫ u in A..A + R * δ, 2 * (‖f u‖ * ‖f' u‖) := by
    rw [sum_integral_adjacent_intervals (hadj _ hcrossint)]; norm_num [ha]
  have hcelleq : ∀ k, a k + δ = a (k + 1) := fun k => by rw [ha]; push_cast; ring
  calc ∑ r ∈ Finset.range R, ‖f (a r)‖ ^ 2
      ≤ ∑ r ∈ Finset.range R, ((1 / δ) * (∫ u in a r..a r + δ, ‖f u‖ ^ 2)
          + ∫ u in a r..a r + δ, 2 * (‖f u‖ * ‖f' u‖)) := Finset.sum_le_sum hper
    _ = (1 / δ) * (∑ r ∈ Finset.range R, ∫ u in a r..a (r + 1), ‖f u‖ ^ 2)
          + ∑ r ∈ Finset.range R, ∫ u in a r..a (r + 1), 2 * (‖f u‖ * ‖f' u‖) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp_rw [hcelleq]
    _ = (1 / δ) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
          + ∫ u in A..A + R * δ, 2 * (‖f u‖ * ‖f' u‖) := by rw [hsum1, hsum2]

/-- **The large-values inequality.**  If `R` uniform grid points `A + rδ` (`r < R`) all have
`‖f‖ ≥ V ≥ 0`, then their count is bounded by the second moments of `f` and `f'`:

  R · V² ≤ (δ^{-1} + η^{-1}) ∫_A^{A+Rδ}‖f‖² + η ∫_A^{A+Rδ}‖f'‖²     (any η > 0).

Gallagher's grid sum bounds `∑‖f(A+rδ)‖²` by `δ^{-1}∫‖f‖² + ∫2‖f‖‖f'‖`; AM–GM splits the cross term
`∫2‖f‖‖f'‖ ≤ η^{-1}∫‖f‖² + η∫‖f'‖²`; and `R·V² ≤ ∑‖f(A+rδ)‖²` since each value is `≥ V`.  Optimising `η`
turns a mean-value (second-moment) bound into a bound on the number of *large values* — the mechanism
that (through a mollifier) yields Carlson's sublinear zero density. -/
theorem large_values_count {f f' : ℝ → ℂ} {A δ V η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hV0 : 0 ≤ V)
    (R : ℕ) (hf : ∀ y ∈ Set.Icc A (A + R * δ), HasDerivAt f (f' y) y)
    (hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (A + R * δ))
    (hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume A (A + R * δ))
    (hsqf'int : IntervalIntegrable (fun y => ‖f' y‖ ^ 2) volume A (A + R * δ))
    (hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (A + R * δ))
    (hV : ∀ r, r < R → V ≤ ‖f (A + r * δ)‖) :
    (R : ℝ) * V ^ 2 ≤ (1 / δ + 1 / η) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
      + η * (∫ u in A..A + R * δ, ‖f' u‖ ^ 2) := by
  -- lower bound: R·V² ≤ ∑‖f(A+rδ)‖²
  have hlow : (R : ℝ) * V ^ 2 ≤ ∑ r ∈ Finset.range R, ‖f (A + r * δ)‖ ^ 2 := by
    calc (R : ℝ) * V ^ 2 = ∑ _r ∈ Finset.range R, V ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ r ∈ Finset.range R, ‖f (A + r * δ)‖ ^ 2 :=
          Finset.sum_le_sum (fun r hr =>
            pow_le_pow_left₀ hV0 (hV r (Finset.mem_range.mp hr)) 2)
  -- cross term AM–GM: ∫2‖f‖‖f'‖ ≤ (1/η)∫‖f‖² + η∫‖f'‖²
  have hcross : (∫ u in A..A + R * δ, 2 * (‖f u‖ * ‖f' u‖))
      ≤ (1 / η) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
        + η * (∫ u in A..A + R * δ, ‖f' u‖ ^ 2) := by
    have hAle : A ≤ A + R * δ := le_add_of_nonneg_right (by positivity)
    have hRHS : (∫ u in A..A + R * δ, (1 / η) * ‖f u‖ ^ 2 + η * ‖f' u‖ ^ 2)
        = (1 / η) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
          + η * (∫ u in A..A + R * δ, ‖f' u‖ ^ 2) := by
      rw [intervalIntegral.integral_add (hgint.const_mul (1 / η)) (hsqf'int.const_mul η),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hmaj : (∫ u in A..A + R * δ, 2 * (‖f u‖ * ‖f' u‖))
        ≤ ∫ u in A..A + R * δ, (1 / η) * ‖f u‖ ^ 2 + η * ‖f' u‖ ^ 2 := by
      apply integral_mono_on hAle hcrossint
        ((hgint.const_mul (1 / η)).add (hsqf'int.const_mul η))
      intro y _
      have := two_mul_le_div_add_mul (a := ‖f y‖) (b := ‖f' y‖) hη
      rw [div_eq_mul_inv, ← one_div] at this
      linarith [this]
    rw [hRHS] at hmaj
    exact hmaj
  -- assemble
  have hgall := gallagher_grid hδ R hf hg'int hgint hcrossint
  calc (R : ℝ) * V ^ 2 ≤ ∑ r ∈ Finset.range R, ‖f (A + r * δ)‖ ^ 2 := hlow
    _ ≤ (1 / δ) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
          + ∫ u in A..A + R * δ, 2 * (‖f u‖ * ‖f' u‖) := hgall
    _ ≤ (1 / δ) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
          + ((1 / η) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
            + η * (∫ u in A..A + R * δ, ‖f' u‖ ^ 2)) := by linarith [hcross]
    _ = (1 / δ + 1 / η) * (∫ u in A..A + R * δ, ‖f u‖ ^ 2)
          + η * (∫ u in A..A + R * δ, ‖f' u‖ ^ 2) := by ring

end RHTower
