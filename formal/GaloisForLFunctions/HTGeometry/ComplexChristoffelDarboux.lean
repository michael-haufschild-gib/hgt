import GaloisForLFunctions.HTGeometry.ChristoffelDarboux

/-!
# Complex Christoffel--Darboux and the reproducing kernel

The monic orthogonal polynomials have real coefficients, so they evaluate at complex points and
commute with conjugation.  Christoffel--Darboux therefore holds verbatim over `ℂ`, and specializing
`y = conj z` turns its left side into the positive kernel

`∑_{k ≤ n} |Q_k(z)|² / h_k`

whose boundedness in `n` is the criterion separating determinate from indeterminate Hamburger
problems.  The right side becomes a Wronskian in `Q_n, Q_{n+1}` at the single point `z`.
-/

open scoped BigOperators
open Polynomial Complex

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Complex evaluation of the monic orthogonal polynomials. -/
noncomputable def monicOrthoC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  Polynomial.aeval z (monicOrtho s n)

/-- Real coefficients make complex evaluation commute with conjugation. -/
theorem monicOrthoC_conj (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    monicOrthoC s n (starRingEnd ℂ z) = starRingEnd ℂ (monicOrthoC s n z) := by
  simpa [monicOrthoC] using
    Polynomial.aeval_algHom_apply (Complex.conjAe.toAlgHom) z (monicOrtho s n)

/-- The three-term recurrence at a complex point. -/
theorem monicOrthoC_three_term (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    z * monicOrthoC s (n + 1) z =
      monicOrthoC s (n + 2) z
        + ((momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ) *
              monicOrthoC s (n + 1) z
        + ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) * monicOrthoC s n z := by
  have hev := congrArg (Polynomial.aeval z) (monicOrtho_three_term h n)
  simpa [monicOrthoC, Algebra.smul_def, Complex.coe_algebraMap] using hev

/-- **Christoffel--Darboux over `ℂ`.** -/
theorem christoffelDarbouxC (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    (z - w) * ∑ k ∈ Finset.range (n + 1),
        monicOrthoC s k z * monicOrthoC s k w /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = (monicOrthoC s (n + 1) z * monicOrthoC s n w -
          monicOrthoC s n z * monicOrthoC s (n + 1) w) /
        ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) := by
  induction n with
  | zero =>
      have h0 : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s 0)
      have hz0 : monicOrthoC s 0 z = 1 := by simp [monicOrthoC]
      have hw0 : monicOrthoC s 0 w = 1 := by simp [monicOrthoC]
      have hone : monicOrthoC s 1 z - monicOrthoC s 1 w = z - w := by
        simp only [monicOrthoC]
        rw [monicOrtho_eq s 1]
        simp
      simp only [Nat.zero_add, Finset.sum_range_one, hz0, hw0, one_mul, mul_one]
      field_simp
      linear_combination -hone
  | succ n ih =>
      have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s n)
      have hn1 : ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s (n + 1))
      have hrz := monicOrthoC_three_term h n z
      have hrw := monicOrthoC_three_term h n w
      have hez : monicOrthoC s (n + 2) z =
          z * monicOrthoC s (n + 1) z
            - ((momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ) *
              monicOrthoC s (n + 1) z
            - ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) * monicOrthoC s n z := by
        linear_combination -hrz
      have hew : monicOrthoC s (n + 2) w =
          w * monicOrthoC s (n + 1) w
            - ((momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ) *
              monicOrthoC s (n + 1) w
            - ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) * monicOrthoC s n w := by
        linear_combination -hrw
      have hcast : ∀ a b : ℝ, ((a / b : ℝ) : ℂ) = (a : ℂ) / (b : ℂ) := fun a b => by
        push_cast
        ring
      rw [Finset.sum_range_succ, mul_add, ih, hez, hew, hcast, hcast]
      field_simp
      ring

/-- **The reproducing kernel at a single point.**  Specializing `w = conj z` makes the left side the
positive kernel `∑ |Q_k(z)|² / h_k`; the right side is a Wronskian in `Q_n, Q_{n+1}` at `z`. -/
theorem christoffelDarbouxC_conj (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    (z - starRingEnd ℂ z) * ∑ k ∈ Finset.range (n + 1),
        ((Complex.normSq (monicOrthoC s k z) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = (monicOrthoC s (n + 1) z * starRingEnd ℂ (monicOrthoC s n z) -
          monicOrthoC s n z * starRingEnd ℂ (monicOrthoC s (n + 1) z)) /
        ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) := by
  have hcd := christoffelDarbouxC h n z (starRingEnd ℂ z)
  simp only [monicOrthoC_conj] at hcd
  rw [← hcd]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-! ## The real kernel identity

Both sides of `christoffelDarbouxC_conj` are of the form `2i · (real)`, so the identity descends to
a statement about real numbers: the partial sums of the positive kernel are computed exactly by a
single imaginary part at level `n`.  This is the finite identity whose boundedness in `n` is the
indeterminacy criterion. -/

/-- **The real reproducing-kernel identity.**  For every `n` and every `z`, the weighted partial sum
of `|Qₖ(z)|²` is determined by one imaginary part at level `n`. -/
theorem kernelSum_mul_im (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    (∑ k ∈ Finset.range (n + 1),
        Complex.normSq (monicOrthoC s k z) /
          momentInner s (monicOrtho s k) (monicOrtho s k)) * z.im *
        momentInner s (monicOrtho s n) (monicOrtho s n)
      = (monicOrthoC s (n + 1) z * (starRingEnd ℂ) (monicOrthoC s n z)).im := by
  have hn : (momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s n)
  have hcd := christoffelDarbouxC_conj h n z
  have hcast : ∑ k ∈ Finset.range (n + 1),
      ((Complex.normSq (monicOrthoC s k z) : ℝ) : ℂ) /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ((∑ k ∈ Finset.range (n + 1),
          Complex.normSq (monicOrthoC s k z) /
            momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hswap : monicOrthoC s n z * (starRingEnd ℂ) (monicOrthoC s (n + 1) z)
      = (starRingEnd ℂ) (monicOrthoC s (n + 1) z * (starRingEnd ℂ) (monicOrthoC s n z)) := by
    simp [mul_comm]
  rw [hcast, hswap, Complex.sub_conj, Complex.sub_conj] at hcd
  field_simp at hcd
  have hcdR : (2 * z.im) * (∑ k ∈ Finset.range (n + 1),
      Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      = (2 * (monicOrthoC s (n + 1) z * (starRingEnd ℂ) (monicOrthoC s n z)).im) /
        momentInner s (monicOrtho s n) (monicOrtho s n) := by
    exact_mod_cast hcd
  rw [eq_div_iff hn] at hcdR
  linear_combination hcdR / 2

/-! ## Summability of the kernel

The kernel terms are nonnegative, so the series converges exactly when its partial sums are bounded.
By `kernelSum_mul_im` those partial sums are computed by the level-`n` Wronskian expression, so at a
nonreal point the convergence of `∑ |Qₖ(z)|² / hₖ` is equivalent to a bound on that single
expression. -/

theorem kernelTerm_nonneg (h : PositiveMomentForm s) (z : ℂ) (k : ℕ) :
    0 ≤ Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k) :=
  div_nonneg (Complex.normSq_nonneg _) (monicOrtho_inner_self_pos h k).le

/-- Bounded partial sums give summability of the positive kernel. -/
theorem summable_kernel_of_sum_range_le (h : PositiveMomentForm s) (z : ℂ) {C : ℝ}
    (hC : ∀ n, ∑ k ∈ Finset.range n, Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k) ≤ C) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) :=
  summable_of_sum_range_le (fun k => kernelTerm_nonneg h z k) hC

/-- The partial kernel sum at level `n`, solved from `kernelSum_mul_im`. -/
theorem kernelSum_eq (h : PositiveMomentForm s) {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      = (monicOrthoC s (n + 1) z * (starRingEnd ℂ) (monicOrthoC s n z)).im /
        (momentInner s (monicOrtho s n) (monicOrtho s n) * z.im) := by
  have hn : (momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s n)
  have hkey := kernelSum_mul_im h n z
  rw [eq_div_iff (mul_ne_zero hn hz)]
  linear_combination hkey

/-- **Summability criterion at a nonreal point.**  Convergence of the positive kernel follows from a
single bound on the level-`n` Wronskian expression. -/
theorem summable_kernel_of_wronskian_le (h : PositiveMomentForm s) {z : ℂ} (hz : z.im ≠ 0)
    {C : ℝ}
    (hC : ∀ n, (monicOrthoC s (n + 1) z * (starRingEnd ℂ) (monicOrthoC s n z)).im /
        (momentInner s (monicOrtho s n) (monicOrtho s n) * z.im) ≤ C) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  refine summable_kernel_of_sum_range_le (C := max C 0) h z ?_
  intro n
  match n with
  | 0 => simp
  | (m + 1) =>
      rw [kernelSum_eq h hz m]
      exact le_trans (hC m) (le_max_left C 0)

/-! ## The criterion as an equivalence

For a nonnegative series, summability is exactly boundedness of the partial sums, and at a nonreal
point `kernelSum_eq` identifies those partial sums with the level-`n` Wronskian expression.  So
convergence of the kernel is *equivalent* to a bound on that single expression. -/

theorem sum_range_le_tsum_kernel (h : PositiveMomentForm s) (z : ℂ)
    (hsum : Summable (fun k => Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k))) (n : ℕ) :
    ∑ k ∈ Finset.range n, Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k)
      ≤ ∑' k, Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k) :=
  hsum.sum_le_tsum _ (fun i _ => kernelTerm_nonneg h z i)

/-- **Summability of the kernel is boundedness of its partial sums.** -/
theorem summable_kernel_iff (h : PositiveMomentForm s) (z : ℂ) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      ↔ ∃ C : ℝ, ∀ n, ∑ k ∈ Finset.range n, Complex.normSq (monicOrthoC s k z) /
          momentInner s (monicOrtho s k) (monicOrtho s k) ≤ C := by
  constructor
  · intro hsum
    exact ⟨_, sum_range_le_tsum_kernel h z hsum⟩
  · rintro ⟨C, hC⟩
    exact summable_kernel_of_sum_range_le h z hC

/-- **The indeterminacy criterion at a nonreal point.**  Convergence of `∑ |Qₖ(z)|² / hₖ` is
equivalent to boundedness in `n` of the single Wronskian expression
`Im(Qₙ₊₁(z) conj(Qₙ(z))) / (hₙ Im z)`. -/
theorem summable_kernel_iff_wronskian_bdd (h : PositiveMomentForm s) {z : ℂ} (hz : z.im ≠ 0) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      ↔ ∃ C : ℝ, ∀ n, (monicOrthoC s (n + 1) z * (starRingEnd ℂ) (monicOrthoC s n z)).im /
          (momentInner s (monicOrtho s n) (monicOrtho s n) * z.im) ≤ C := by
  constructor
  · intro hsum
    refine ⟨∑' k, Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k), fun n => ?_⟩
    rw [← kernelSum_eq h hz n]
    exact sum_range_le_tsum_kernel h z hsum (n + 1)
  · rintro ⟨C, hC⟩
    exact summable_kernel_of_wronskian_le h hz hC

end HTGeometry
