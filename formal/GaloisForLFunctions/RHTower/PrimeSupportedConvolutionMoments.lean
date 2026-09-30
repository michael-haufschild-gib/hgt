import Mathlib

/-!
# Weighted mass of powers of a prime-supported arithmetic function

Let `a` be an arithmetic function supported on the primes up to `N`, and `w : ℕ → ℝ` a nonnegative
completely multiplicative weight. With the weighted mass `‖f‖²_w = Σ_{1 ≤ n ≤ M} |f(n)|² w(n)`,

`‖a^{⋆m}‖²_w ≤ m! · ‖a‖²_w^m`   (`wMass_pow_le`),

where `a^{⋆m}` is the `m`-fold Dirichlet convolution. The power `a^{⋆m}` is supported on the
integers with exactly `m` prime factors counted with multiplicity (`support_pow_prime`), so for
`n` in its support `(a^{⋆m} ⋆ a)(n) = Σ_{p | n} a^{⋆m}(n/p) a(p)` has at most `m + 1` nonzero terms;
Cauchy–Schwarz and the reindexing `n = d e` (`sum_Icc_sum_divisorsAntidiagonal`) give one factor
`m + 1` per step.

This is the mean-square input of the high moments of prime Dirichlet polynomials: with
`w(n) = n^{−1−2δ}` the mean value theorem turns it into `∫|Σ_p a_p p^{−1/2−δ−it}|^{2m} dt`.
-/

noncomputable section

open ArithmeticFunction Finset

namespace RHTower

/-- The weighted mass `Σ_{1 ≤ n ≤ M} |f(n)|² w(n)`. -/
def wMass (w : ℕ → ℝ) (f : ArithmeticFunction ℂ) (M : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 M, ‖f n‖ ^ 2 * w n

theorem wMass_nonneg {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (f : ArithmeticFunction ℂ) (M : ℕ) :
    0 ≤ wMass w f M :=
  Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hw0 n)

/-- **Reindexing a divisor double sum.** -/
theorem sum_Icc_sum_divisorsAntidiagonal {β : Type*} [AddCommMonoid β] {G : ℕ × ℕ → β}
    {M M₁ M₂ : ℕ}
    (hG : ∀ x : ℕ × ℕ, G x ≠ 0 → (1 ≤ x.1 ∧ x.1 ≤ M₁) ∧ (1 ≤ x.2 ∧ x.2 ≤ M₂))
    (hM : M₁ * M₂ ≤ M) :
    ∑ n ∈ Icc 1 M, ∑ x ∈ n.divisorsAntidiagonal, G x = ∑ d ∈ Icc 1 M₁, ∑ e ∈ Icc 1 M₂, G (d, e) := by
  rw [Finset.sum_sigma', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.2) ?_ ?_ ?_ ?_
  · intro p hp hG0
    have h := hG _ hG0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr h.1, Finset.mem_Icc.mpr h.2⟩
  · intro p₁ hp₁ _ p₂ hp₂ _ he
    obtain ⟨n₁, x₁⟩ := p₁
    obtain ⟨n₂, x₂⟩ := p₂
    simp only at he
    subst he
    have h1 := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hp₁).2).1
    have h2 := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hp₂).2).1
    have : n₁ = n₂ := h1.symm.trans h2
    subst this
    rfl
  · intro x hx hG0
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hG x hG0
    refine ⟨⟨x.1 * x.2, x⟩, ?_, hG0, rfl⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact le_trans (Nat.mul_le_mul h2 h4) hM
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
  · intro p _ _
    rfl

/-- The powers of a prime-supported function live on `Ω(n) = m`, `1 ≤ n ≤ N^m`. -/
theorem support_pow_prime {a : ArithmeticFunction ℂ} {N : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (haN : ∀ k, a k ≠ 0 → k ≤ N) :
    ∀ m k, (a ^ m) k ≠ 0 → cardFactors k = m ∧ 1 ≤ k ∧ k ≤ N ^ m := by
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [pow_zero, one_apply] at hk
    split_ifs at hk with h
    · subst h; exact ⟨cardFactors_one, le_rfl, by simp⟩
    · exact absurd rfl hk
  | succ m ih =>
    intro k hk
    rw [pow_succ, mul_apply] at hk
    obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have hx1 : (a ^ m) x.1 ≠ 0 := left_ne_zero_of_mul hx0
    have hx2 : a x.2 ≠ 0 := right_ne_zero_of_mul hx0
    obtain ⟨hΩ, h1, hN1⟩ := ih x.1 hx1
    have hp := ha x.2 hx2
    have hpN := haN x.2 hx2
    obtain ⟨hmul, hk0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [← hmul]
    refine ⟨?_, ?_, ?_⟩
    · rw [cardFactors_mul (by omega) hp.ne_zero, hΩ, cardFactors_apply_prime hp]
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hp.ne_zero)
    · rw [pow_succ]; exact Nat.mul_le_mul hN1 hpN

/-- **One convolution step, pointwise.** -/
theorem normSq_mul_prime_le {f a : ArithmeticFunction ℂ} {m : ℕ}
    (hf : ∀ k, f k ≠ 0 → cardFactors k = m) (ha : ∀ k, a k ≠ 0 → k.Prime) (n : ℕ) :
    ‖(f * a) n‖ ^ 2 ≤ (m + 1) * ∑ x ∈ n.divisorsAntidiagonal, ‖f x.1‖ ^ 2 * ‖a x.2‖ ^ 2 := by
  classical
  rw [mul_apply]
  set S := n.divisorsAntidiagonal.filter (fun x => f x.1 * a x.2 ≠ 0) with hS
  have hsum : ∑ x ∈ n.divisorsAntidiagonal, f x.1 * a x.2 = ∑ x ∈ S, f x.1 * a x.2 :=
    (Finset.sum_filter_ne_zero _).symm
  rw [hsum]
  have hrhs0 : 0 ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖f x.1‖ ^ 2 * ‖a x.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  -- the count of nonzero terms
  have hcard : (S.card : ℝ) ≤ m + 1 := by
    rcases S.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
    · rw [h, Finset.card_empty]; push_cast; linarith
    have hx₀' := Finset.mem_filter.mp hx₀
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx₀'.1
    have hf0 : f x₀.1 ≠ 0 := left_ne_zero_of_mul hx₀'.2
    have ha0 : a x₀.2 ≠ 0 := right_ne_zero_of_mul hx₀'.2
    have hp := ha _ ha0
    have hΩ : cardFactors n = m + 1 := by
      rw [← hmul, cardFactors_mul (by rintro h; rw [h, zero_mul] at hmul; omega) hp.ne_zero,
        hf _ hf0, cardFactors_apply_prime hp]
    have hinj : S.card ≤ n.primeFactorsList.toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun x => x.2) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
      · have hx' := Finset.mem_filter.mp hx
        obtain ⟨hm, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx'.1
        have hpx := ha _ (right_ne_zero_of_mul hx'.2)
        rw [Finset.mem_coe, List.mem_toFinset, Nat.mem_primeFactorsList hn]
        exact ⟨hpx, ⟨x.1, by rw [← hm, mul_comm]⟩⟩
      · have hx' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hx).1)
        have hy' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hy).1)
        simp only at hxy
        have hp2 : x.2 ≠ 0 := by
          intro h; have := (Finset.mem_filter.mp hx).2; rw [h] at this
          exact this (by rw [ArithmeticFunction.map_zero, mul_zero])
        have h1 : x.1 = y.1 := by
          have := hx'.1.trans hy'.1.symm
          rw [hxy] at this
          exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (hxy ▸ hp2)) this
        exact Prod.ext h1 hxy
    have hle : n.primeFactorsList.toFinset.card ≤ cardFactors n := by
      rw [cardFactors_apply]; exact List.toFinset_card_le _
    have : S.card ≤ m + 1 := hinj.trans (hle.trans hΩ.le)
    exact_mod_cast this
  calc ‖∑ x ∈ S, f x.1 * a x.2‖ ^ 2 ≤ (∑ x ∈ S, ‖f x.1 * a x.2‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (S.card : ℝ) * ∑ x ∈ S, ‖f x.1 * a x.2‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (m + 1) * ∑ x ∈ S, ‖f x.1 * a x.2‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (m + 1) * ∑ x ∈ n.divisorsAntidiagonal, ‖f x.1‖ ^ 2 * ‖a x.2‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => sq_nonneg _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, mul_pow]

/-- **The weighted mass of the powers.** -/
theorem wMass_pow_le {a : ArithmeticFunction ℂ} {w : ℕ → ℝ} {N : ℕ} (hw0 : ∀ n, 0 ≤ w n)
    (hwmul : ∀ d e, w (d * e) = w d * w e) (ha : ∀ k, a k ≠ 0 → k.Prime)
    (haN : ∀ k, a k ≠ 0 → k ≤ N) :
    ∀ m : ℕ, wMass w (a ^ m) (N ^ m) ≤ m.factorial * wMass w a N ^ m := by
  have hsupp := support_pow_prime ha haN
  have hw1 : w 1 ≤ 1 := by
    have h := hwmul 1 1
    rw [one_mul] at h
    by_contra hlt
    push Not at hlt
    nlinarith [hw0 1]
  intro m
  induction m with
  | zero =>
    unfold wMass
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [show Icc 1 1 = {1} from rfl, Finset.sum_singleton, one_apply, if_pos rfl]
    simpa using hw1
  | succ m ih =>
    have hA0 := wMass_nonneg hw0 a N
    have hstep : wMass w (a ^ m * a) (N ^ (m + 1)) ≤ (m + 1) * (wMass w (a ^ m) (N ^ m) *
        wMass w a N) := by
      unfold wMass
      calc ∑ n ∈ Icc 1 (N ^ (m + 1)), ‖(a ^ m * a) n‖ ^ 2 * w n
          ≤ ∑ n ∈ Icc 1 (N ^ (m + 1)), (m + 1) *
              ∑ x ∈ n.divisorsAntidiagonal, ‖(a ^ m) x.1‖ ^ 2 * w x.1 * (‖a x.2‖ ^ 2 * w x.2) := by
            refine Finset.sum_le_sum fun n _ => ?_
            have h := normSq_mul_prime_le (fun k hk => (hsupp m k hk).1) ha n
            have e : ∑ x ∈ n.divisorsAntidiagonal, ‖(a ^ m) x.1‖ ^ 2 * w x.1 * (‖a x.2‖ ^ 2 * w x.2) =
                (∑ x ∈ n.divisorsAntidiagonal, ‖(a ^ m) x.1‖ ^ 2 * ‖a x.2‖ ^ 2) * w n := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x hx => ?_
              obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
              rw [← hmul, hwmul]; ring
            rw [e, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right h (hw0 n)
        _ = (m + 1) * ∑ n ∈ Icc 1 (N ^ (m + 1)),
              ∑ x ∈ n.divisorsAntidiagonal, ‖(a ^ m) x.1‖ ^ 2 * w x.1 * (‖a x.2‖ ^ 2 * w x.2) := by
            rw [Finset.mul_sum]
        _ = (m + 1) * ∑ d ∈ Icc 1 (N ^ m), ∑ e ∈ Icc 1 N,
              ‖(a ^ m) d‖ ^ 2 * w d * (‖a e‖ ^ 2 * w e) := by
            congr 1
            refine sum_Icc_sum_divisorsAntidiagonal (fun x hx => ?_) (by rw [pow_succ])
            have h1 : (a ^ m) x.1 ≠ 0 := by
              intro h; apply hx; rw [h]; simp
            have h2 : a x.2 ≠ 0 := by
              intro h; apply hx; rw [h]; simp
            obtain ⟨-, hlo, hhi⟩ := hsupp m x.1 h1
            exact ⟨⟨hlo, hhi⟩, ⟨(ha _ h2).one_lt.le, haN _ h2⟩⟩
        _ = (m + 1) * ((∑ d ∈ Icc 1 (N ^ m), ‖(a ^ m) d‖ ^ 2 * w d) *
              ∑ e ∈ Icc 1 N, ‖a e‖ ^ 2 * w e) := by
            rw [Finset.sum_mul_sum]
    rw [pow_succ]
    refine hstep.trans ?_
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    have := mul_le_mul_of_nonneg_right ih hA0
    have hm : (0 : ℝ) ≤ m + 1 := by positivity
    calc ((m : ℝ) + 1) * (wMass w (a ^ m) (N ^ m) * wMass w a N)
        ≤ ((m : ℝ) + 1) * (m.factorial * wMass w a N ^ m * wMass w a N) :=
          mul_le_mul_of_nonneg_left this hm
      _ = ((m : ℝ) + 1) * m.factorial * (wMass w a N ^ m * wMass w a N) := by ring

end RHTower
