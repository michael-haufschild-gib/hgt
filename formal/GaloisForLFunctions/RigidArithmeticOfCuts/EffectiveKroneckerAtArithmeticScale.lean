import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Effective Kronecker at arithmetic scale

Kronecker's theorem says that the phases `p^{it}` reach any target on the prime torus. Its quantitative
form needs integrality: two distinct integers `a, b ≤ Q` satisfy `|log a − log b| ≥ 1/Q`.

Take `S` the divisors of `R^D`, `R = Π_{p∈P} p`, and let `B(t) = Σ_{n∈S} ω(n) n^{it}` with the phase `ω`
completely multiplicative on `S` and chosen from the targets. The square `|B|²` is a nonnegative trigonometric
polynomial with frequencies `log(n/m)`, which are separated by integrality. So its mean is computed exactly
up to `|S|² R^{D+1}/T`, and against a character `p^{it} e^{-iθ_p}` its mean is the number of `n ∈ S` with `pn ∈ S`,
a fraction `D/(D+1)` of `S`. Therefore

`Σ_{p∈P} a_p (1 − cos(t log p − θ_p)) ≤ 4 Σ a_p /(D + 1)`

at some `t ∈ [0, T]`, as soon as `T ≥ 8 (D+1) |S| R^{D+1}`. The height is explicit:
`log T ≈ (D + 1) θ(y)`, for the primes up to `y`.

**The short-sum barrier has a left endpoint.** At height `T`, the polynomial `Σ_{p≤y} p^{-σ-it}` has no
cancellation for `y ≲ log T`. So no nontrivial sup bound is possible below length `log T`.
-/

open Finset Complex MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### Separation of logarithms of integers -/

/-- **The arithmetic input.** Distinct integers below `Q` have logarithms at distance at least `1/Q`. -/
theorem one_div_le_abs_log_sub_log {a b Q : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) (haQ : a ≤ Q)
    (hbQ : b ≤ Q) : 1 / (Q : ℝ) ≤ |Real.log a - Real.log b| := by
  have key : ∀ {x y : ℕ}, 1 ≤ x → x < y → y ≤ Q → 1 / (Q : ℝ) ≤ Real.log y - Real.log x := by
    intro x y hx hxy hyQ
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hlog : Real.log (x / y) ≤ (x : ℝ) / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at hlog
    have h1 : (x : ℝ) + 1 ≤ y := by exact_mod_cast hxy
    have h2 : (y : ℝ) ≤ Q := by exact_mod_cast hyQ
    have h3 : 1 / (Q : ℝ) ≤ 1 / (y : ℝ) := one_div_le_one_div_of_le hy0 h2
    have h4 : (x : ℝ) / y - 1 ≤ -(1 / (y : ℝ)) := by
      rw [div_sub_one hy0.ne', ← neg_div, div_le_div_iff_of_pos_right hy0]
      linarith
    linarith
  rcases lt_or_gt_of_ne hab with h | h
  · have := key ha h hbQ
    rw [abs_sub_comm]
    exact this.trans (le_abs_self _)
  · have := key hb h haQ
    exact this.trans (le_abs_self _)

/-- A character integrates to size `2/|λ|`. -/
theorem norm_integral_exp_le {lam : ℝ} (hlam : lam ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, cexp ((lam : ℂ) * I * (t : ℂ))‖ ≤ 2 / |lam| := by
  have hc : (lam : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hlam) I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h1 : ‖cexp ((lam : ℂ) * I * (T : ℂ))‖ = 1 := by
    have : (lam : ℂ) * I * (T : ℂ) = ((lam * T : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖cexp ((lam : ℂ) * I * ((0 : ℝ) : ℂ))‖ = 1 := by simp
  rw [norm_div]
  have hnorm : ‖(lam : ℂ) * I‖ = |lam| := by simp
  rw [hnorm]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc _ ≤ ‖cexp ((lam : ℂ) * I * (T : ℂ))‖ + ‖cexp ((lam : ℂ) * I * ((0 : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

/-- **Mean value of a separated trigonometric polynomial.** -/
theorem norm_integral_trig_sub_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (lam : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ i ∈ s, lam i = 0 ∨ δ ≤ |lam i|) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, ∑ i ∈ s, c i * cexp ((lam i : ℂ) * I * (t : ℂ))) -
        (T : ℂ) * ∑ i ∈ s with lam i = 0, c i‖ ≤ 2 / δ * ∑ i ∈ s, ‖c i‖ := by
  classical
  have hint : ∀ i ∈ s, IntervalIntegrable (fun t : ℝ => c i * cexp ((lam i : ℂ) * I * (t : ℂ))) volume 0 T :=
    fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_finsetSum hint, sum_filter, mul_sum, ← sum_sub_distrib, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  rw [intervalIntegral.integral_const_mul]
  by_cases h0 : lam i = 0
  · have hzero : c i * (∫ t in (0 : ℝ)..T, cexp ((lam i : ℂ) * I * (t : ℂ))) -
        (T : ℂ) * (if lam i = 0 then c i else 0) = 0 := by
      simp [h0]
      ring
    rw [hzero, norm_zero]
    positivity
  · rw [if_neg h0, mul_zero, sub_zero, norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_integral_exp_le h0 T).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) hδ ((hsep i hi).resolve_left h0)

/-! ### The Dirichlet polynomial of the targets -/

variable (P : Finset ℕ) (D : ℕ)

/-- The product of the primes of `P`. -/
def radicalOf : ℕ := ∏ p ∈ P, p

/-- The integers with exponent at most `D` at each prime of `P`. -/
def exponentBox : Finset ℕ := ((radicalOf P) ^ D).divisors

variable {P}

theorem radicalOf_pos (hP : ∀ p ∈ P, p.Prime) : 0 < radicalOf P :=
  prod_pos fun p hp => (hP p hp).pos

theorem mem_exponentBox_pos {n : ℕ} (hn : n ∈ exponentBox P D) : 1 ≤ n :=
  Nat.pos_of_mem_divisors hn

theorem mem_exponentBox_le {n : ℕ} (hn : n ∈ exponentBox P D) :
    n ≤ radicalOf P ^ D :=
  Nat.divisor_le hn

/-- The phase of `n` from the targets `θ`. -/
def targetPhase (P : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) : ℝ := ∑ q ∈ P, (n.factorization q : ℝ) * θ q

theorem targetPhase_mul_prime {θ : ℕ → ℝ} (hP : ∀ p ∈ P, p.Prime) {n p : ℕ} (hn : n ≠ 0)
    (hp : p ∈ P) : targetPhase P θ (n * p) = targetPhase P θ n + θ p := by
  classical
  have hpp := hP p hp
  have hsplit : ∀ q ∈ P, ((n * p).factorization q : ℝ) * θ q =
      (n.factorization q : ℝ) * θ q + if q = p then θ p else 0 := by
    intro q _
    rw [Nat.factorization_mul hn hpp.ne_zero, hpp.factorization]
    by_cases h : q = p
    · subst h
      simp
      ring
    · simp [h]
  rw [targetPhase, sum_congr rfl hsplit, sum_add_distrib, sum_ite_eq' P p, if_pos hp]
  rfl

/-- The Dirichlet polynomial `B(t) = Σ_{n∈S} ω(n) n^{it}` with `ω(n) = e^{-iφ(n)}`. -/
def targetPoly (P : Finset ℕ) (D : ℕ) (θ : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ exponentBox P D, cexp (-(targetPhase P θ n : ℂ) * I) * cexp ((Real.log n : ℂ) * I * (t : ℂ))

/-- The coefficient of the pair `(n, m)` in `|B|²`. -/
private def pairCoeff (P : Finset ℕ) (θ : ℕ → ℝ) (x : ℕ × ℕ) : ℂ :=
  cexp (-(targetPhase P θ x.1 : ℂ) * I) * cexp ((targetPhase P θ x.2 : ℂ) * I)

private lemma norm_pairCoeff (θ : ℕ → ℝ) (x : ℕ × ℕ) : ‖pairCoeff P θ x‖ = 1 := by
  rw [pairCoeff, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The square of `B` as a trigonometric polynomial.** -/
theorem normSq_targetPoly (θ : ℕ → ℝ) (t : ℝ) :
    ((normSq (targetPoly P D θ t) : ℝ) : ℂ) =
      ∑ x ∈ exponentBox P D ×ˢ exponentBox P D, pairCoeff P θ x *
        cexp (((Real.log x.1 - Real.log x.2 : ℝ) : ℂ) * I * (t : ℂ)) := by
  rw [normSq_eq_conj_mul_self, mul_comm, targetPoly, map_sum, sum_mul_sum, sum_product]
  refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
  have h1 : (starRingEnd ℂ) (cexp (-(targetPhase P θ m : ℂ) * I)) = cexp ((targetPhase P θ m : ℂ) * I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  have h2 : (starRingEnd ℂ) (cexp ((Real.log m : ℂ) * I * (t : ℂ))) =
      cexp (-((Real.log m : ℂ) * I * (t : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [map_mul, h1, h2, pairCoeff, show ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) by intros; ring,
    ← Complex.exp_add ((Real.log n : ℂ) * I * (t : ℂ))]
  congr 2
  push_cast
  ring

/-! ### The mean of `|B|²` against a character -/

theorem continuous_targetPoly (θ : ℕ → ℝ) : Continuous (targetPoly P D θ) := by
  unfold targetPoly
  fun_prop

/-- The real density `|B|²`. -/
def boxDensity (P : Finset ℕ) (D : ℕ) (θ : ℕ → ℝ) (t : ℝ) : ℝ := normSq (targetPoly P D θ t)

theorem continuous_boxDensity (θ : ℕ → ℝ) : Continuous (boxDensity P D θ) :=
  Complex.continuous_normSq.comp (continuous_targetPoly D θ)

theorem boxDensity_nonneg (θ : ℕ → ℝ) (t : ℝ) : 0 ≤ boxDensity P D θ t := normSq_nonneg _

/-- **The mean of `|B|²` against a character.** With `k ≥ 1` acting on the targets by the phase `ϑ`, the mean
is the number of `n` in the box with `n k` in the box, up to `2 k R^D |S|²`. -/
theorem abs_integral_boxDensity_mul_cos_sub_le (hP : ∀ p ∈ P, p.Prime) {θ : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    {ϑ : ℝ} (hϕ : ∀ n ∈ exponentBox P D, targetPhase P θ (n * k) = targetPhase P θ n + ϑ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, boxDensity P D θ t * Real.cos (t * Real.log k - ϑ)) -
        T * (((exponentBox P D).filter fun n => n * k ∈ exponentBox P D).card : ℝ)| ≤
      2 * ((k : ℝ) * (radicalOf P : ℝ) ^ D) * ((exponentBox P D).card : ℝ) ^ 2 := by
  classical
  set S := exponentBox P D with hS
  have hR : 0 < radicalOf P := radicalOf_pos hP
  set Q : ℕ := k * radicalOf P ^ D with hQ
  have hQ0 : 0 < Q := Nat.mul_pos hk (pow_pos hR D)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  set lam : ℕ × ℕ → ℝ := fun x => Real.log (x.1 * k : ℕ) - Real.log x.2 with hlam
  set c : ℕ × ℕ → ℂ := fun x => pairCoeff P θ x * cexp (-(ϑ : ℂ) * I) with hc
  have hmemS : ∀ x ∈ S ×ˢ S, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ x.1 * k ≤ Q ∧ x.2 ≤ Q := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_product.mp hx
    have hx1 := mem_exponentBox_pos D h1
    have hx2 := mem_exponentBox_pos D h2
    have hle1 := mem_exponentBox_le D h1
    have hle2 := mem_exponentBox_le D h2
    refine ⟨hx1, hx2, ?_, hle2.trans (Nat.le_mul_of_pos_left _ hk)⟩
    rw [hQ, mul_comm k]
    exact Nat.mul_le_mul_right k hle1
  have hzero_iff : ∀ x ∈ S ×ˢ S, lam x = 0 ↔ x.1 * k = x.2 := by
    intro x hx
    obtain ⟨h1, h2, -, -⟩ := hmemS x hx
    have h1k : (0 : ℝ) < (x.1 * k : ℕ) := by exact_mod_cast Nat.mul_pos h1 hk
    have h2R : (0 : ℝ) < x.2 := by exact_mod_cast h2
    simp only [hlam, sub_eq_zero]
    constructor
    · intro he
      exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr h1k) (Set.mem_Ioi.mpr h2R) he
    · intro he
      rw [he]
  have hsep : ∀ x ∈ S ×ˢ S, lam x = 0 ∨ 1 / (Q : ℝ) ≤ |lam x| := by
    intro x hx
    by_cases he : x.1 * k = x.2
    · exact Or.inl ((hzero_iff x hx).mpr he)
    · obtain ⟨h1, h2, h3, h4⟩ := hmemS x hx
      exact Or.inr (one_div_le_abs_log_sub_log (Nat.mul_pos h1 hk) h2 he h3 h4)
  have hmain := norm_integral_trig_sub_le (S ×ˢ S) c lam (δ := 1 / (Q : ℝ)) (by positivity) hsep T
  have hnormc : ∀ x, ‖c x‖ = 1 := by
    intro x
    rw [hc]
    simp only [norm_mul, norm_pairCoeff, one_mul]
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsumnorm : ∑ x ∈ S ×ˢ S, ‖c x‖ = ((S.card : ℝ)) ^ 2 := by
    simp only [hnormc, sum_const, card_product, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hfilter : ∑ x ∈ S ×ˢ S with lam x = 0, c x =
      ((S.filter fun n => n * k ∈ S).card : ℂ) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_bij' (fun x _ => x.1) (fun n _ => (n, n * k)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨h1, h2⟩ := mem_filter.mp hx
      have he := (hzero_iff x h1).mp h2
      obtain ⟨h3, h4⟩ := mem_product.mp h1
      exact mem_filter.mpr ⟨h3, he ▸ h4⟩
    · intro n hn
      obtain ⟨h1, h2⟩ := mem_filter.mp hn
      have hmem : (n, n * k) ∈ S ×ˢ S := mem_product.mpr ⟨h1, h2⟩
      exact mem_filter.mpr ⟨hmem, (hzero_iff _ hmem).mpr rfl⟩
    · intro x hx
      obtain ⟨h1, h2⟩ := mem_filter.mp hx
      have he := (hzero_iff x h1).mp h2
      exact Prod.ext rfl he
    · intro n _
      rfl
    · intro x hx
      obtain ⟨h1, h2⟩ := mem_filter.mp hx
      have he := (hzero_iff x h1).mp h2
      obtain ⟨h3, -⟩ := mem_product.mp h1
      have hphase := hϕ x.1 h3
      have hval : c x = 1 := by
        simp only [hc, pairCoeff]
        rw [← he, hphase, ← Complex.exp_add, ← Complex.exp_add]
        have : -((targetPhase P θ x.1 : ℝ) : ℂ) * I + (((targetPhase P θ x.1 + ϑ : ℝ) : ℂ)) * I +
            -(ϑ : ℂ) * I = 0 := by
          push_cast
          ring
        rw [this, Complex.exp_zero]
      rw [hval]
      simp
  rw [hfilter, hsumnorm] at hmain
  -- The integrand of the trigonometric polynomial is `|B|²` against the character.
  have hexpand : ∀ t : ℝ, ∑ x ∈ S ×ˢ S, c x * cexp ((lam x : ℂ) * I * (t : ℂ)) =
      ((boxDensity P D θ t : ℝ) : ℂ) * (cexp ((Real.log k : ℂ) * I * (t : ℂ)) * cexp (-(ϑ : ℂ) * I)) := by
    intro t
    rw [boxDensity, normSq_targetPoly, sum_mul]
    refine sum_congr rfl fun x hx => ?_
    obtain ⟨h1, -, -, -⟩ := hmemS x hx
    have hx1 : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : x.1 ≠ 0)
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hlamx : lam x = Real.log x.1 + Real.log k - Real.log x.2 := by
      simp only [hlam]
      rw [Nat.cast_mul, Real.log_mul hx1 hkR]
    simp only [hc]
    rw [hlamx]
    have hsplit : cexp (((Real.log x.1 + Real.log k - Real.log x.2 : ℝ) : ℂ) * I * (t : ℂ)) =
        cexp (((Real.log x.1 - Real.log x.2 : ℝ) : ℂ) * I * (t : ℂ)) *
          cexp ((Real.log k : ℂ) * I * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  have hre : ∀ t : ℝ, (((boxDensity P D θ t : ℝ) : ℂ) *
      (cexp ((Real.log k : ℂ) * I * (t : ℂ)) * cexp (-(ϑ : ℂ) * I))).re =
      boxDensity P D θ t * Real.cos (t * Real.log k - ϑ) := by
    intro t
    rw [Complex.re_ofReal_mul, ← Complex.exp_add]
    have : (Real.log k : ℂ) * I * (t : ℂ) + -(ϑ : ℂ) * I = ((t * Real.log k - ϑ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  have hcont : Continuous fun t : ℝ => ∑ x ∈ S ×ˢ S, c x * cexp ((lam x : ℂ) * I * (t : ℂ)) := by
    fun_prop
  have hreint : (∫ t in (0 : ℝ)..T, boxDensity P D θ t * Real.cos (t * Real.log k - ϑ)) =
      (∫ t in (0 : ℝ)..T, ∑ x ∈ S ×ˢ S, c x * cexp ((lam x : ℂ) * I * (t : ℂ))).re := by
    have h1 := Complex.reCLM.intervalIntegral_comp_comm
      (hcont.intervalIntegrable (μ := volume) 0 T)
    simp only [Complex.reCLM_apply] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hexpand t, hre t]
  rw [hreint]
  have hreal : ((T : ℂ) * (((S.filter fun n => n * k ∈ S).card : ℕ) : ℂ)).re =
      T * (((S.filter fun n => n * k ∈ S).card : ℕ) : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.ofReal_re]
  rw [← hreal, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans (hmain.trans (le_of_eq ?_))
  rw [hQ]
  push_cast
  field_simp

/-! ### The box loses a fraction `1/(D+1)` under multiplication by a prime -/

/-- At most a fraction `1/(D+1)` of the box leaves it under multiplication by a prime of `P`. -/
theorem card_sub_card_filter_le (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) :
    (((exponentBox P D).card : ℝ) - (((exponentBox P D).filter fun n => n * p ∈ exponentBox P D).card : ℝ)) *
        ((D : ℝ) + 1) ≤ ((exponentBox P D).card : ℝ) := by
  classical
  have hpp := hP p hp
  set R' : ℕ := ∏ q ∈ P.erase p, q with hR'
  have hR : radicalOf P = p * R' := (Finset.mul_prod_erase P (fun q => q) hp).symm
  have hcop : p.Coprime R' := Nat.Coprime.prod_right fun q hq =>
    (Nat.coprime_primes hpp (hP q (mem_of_mem_erase hq))).mpr (ne_of_mem_erase hq).symm
  have hRD : radicalOf P ^ D = p ^ D * R' ^ D := by rw [hR, mul_pow]
  set S := exponentBox P D with hS
  have hScard : S.card = (D + 1) * (R' ^ D).divisors.card := by
    rw [hS, exponentBox, hRD, Nat.Coprime.card_divisors_mul (hcop.pow D D),
      Nat.divisors_prime_pow hpp, card_map, card_range]
  have hsplit := card_filter_add_card_filter_not (s := S) (fun n => n * p ∈ S)
  have hcompl : (S.filter fun n => ¬ n * p ∈ S).card ≤ (R' ^ D).divisors.card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := fun y => p ^ D * y))
    intro n hn
    obtain ⟨hnS, hnp⟩ := mem_filter.mp hn
    have hdvd : n ∣ p ^ D * R' ^ D := by
      rw [← hRD]
      exact Nat.dvd_of_mem_divisors hnS
    obtain ⟨x, y, hx, hy, rfl⟩ := Nat.dvd_mul.mp hdvd
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hpp).mp hx
    have hiD : i = D := by
      by_contra hne
      have hlt : i + 1 ≤ D := by omega
      apply hnp
      have hne0 : radicalOf P ^ D ≠ 0 := pow_ne_zero D (radicalOf_pos hP).ne'
      refine Nat.mem_divisors.mpr ⟨?_, hne0⟩
      rw [hRD, show p ^ i * y * p = p ^ (i + 1) * y by ring]
      exact Nat.mul_dvd_mul (pow_dvd_pow p hlt) hy
    subst hiD
    have hR'0 : R' ^ i ≠ 0 := by
      have hR'pos : 0 < R' := prod_pos fun q hq => (hP q (mem_of_mem_erase hq)).pos
      exact pow_ne_zero i hR'pos.ne'
    exact mem_image.mpr ⟨y, Nat.mem_divisors.mpr ⟨hy, hR'0⟩, rfl⟩
  have hD : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
  have h1 : (S.card : ℝ) = ((S.filter fun n => n * p ∈ S).card : ℝ) +
      ((S.filter fun n => ¬ n * p ∈ S).card : ℝ) := by exact_mod_cast hsplit.symm
  have h2 : ((S.filter fun n => ¬ n * p ∈ S).card : ℝ) ≤ ((R' ^ D).divisors.card : ℝ) := by
    exact_mod_cast hcompl
  have h3 : (S.card : ℝ) = ((D : ℝ) + 1) * ((R' ^ D).divisors.card : ℝ) := by
    exact_mod_cast hScard
  calc ((S.card : ℝ) - ((S.filter fun n => n * p ∈ S).card : ℝ)) * ((D : ℝ) + 1)
      = ((S.filter fun n => ¬ n * p ∈ S).card : ℝ) * ((D : ℝ) + 1) := by rw [h1]; ring
    _ ≤ ((R' ^ D).divisors.card : ℝ) * ((D : ℝ) + 1) := mul_le_mul_of_nonneg_right h2 hD
    _ = _ := by rw [h3]; ring

/-! ### Effective Kronecker -/

/-- **Effective Kronecker at arithmetic scale.** For primes `P`, targets `θ`, nonnegative weights `a` and
degree `D`, there is a height `t ∈ [0, T]` with
`Σ_{p∈P} a_p (1 − cos(t log p − θ_p)) ≤ 5 Σ a_p /(D + 1)`, as soon as
`T ≥ 4 (D + 1) R^{D+1} |S|`, with `R = Π_{p∈P} p` and `|S| = (D + 1)^{|P|}`. -/
theorem exists_height_phase_return (hP : ∀ p ∈ P, p.Prime) (θ a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 ≤ a p) {T : ℝ}
    (hT : 4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (D + 1) * ((exponentBox P D).card : ℝ) ≤ T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T, ∑ p ∈ P, a p * (1 - Real.cos (t * Real.log p - θ p)) ≤
      5 * (∑ p ∈ P, a p) / ((D : ℝ) + 1) := by
  classical
  set S := exponentBox P D with hS
  set A := ∑ p ∈ P, a p with hA
  have hA0 : 0 ≤ A := sum_nonneg ha
  have hRpos : 0 < radicalOf P := radicalOf_pos hP
  have hRR : (1 : ℝ) ≤ radicalOf P := by exact_mod_cast hRpos
  have hSpos : 0 < S.card := card_pos.mpr ⟨1, Nat.mem_divisors.mpr
    ⟨one_dvd _, pow_ne_zero D hRpos.ne'⟩⟩
  have hSR : (0 : ℝ) < S.card := by exact_mod_cast hSpos
  have hDpos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  by_cases hAz : A = 0
  · refine ⟨0, ⟨le_rfl, hT0.le⟩, ?_⟩
    have hzero : ∀ p ∈ P, a p = 0 := (sum_eq_zero_iff_of_nonneg ha).mp hAz
    rw [hAz, sum_eq_zero fun p hp => by rw [hzero p hp, zero_mul]]
    simp
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  by_contra hno
  push Not at hno
  set f := boxDensity P D θ with hf
  have hfc : Continuous f := continuous_boxDensity D θ
  have hfn : ∀ t, 0 ≤ f t := boxDensity_nonneg D θ
  set Emax : ℝ := 2 * (radicalOf P : ℝ) ^ (D + 1) * (S.card : ℝ) ^ 2 with hEmax
  have hEpos : 0 ≤ Emax := by positivity
  have hEsmall : 2 * Emax * ((D : ℝ) + 1) ≤ T * S.card := by
    have h := mul_le_mul_of_nonneg_right hT hSR.le
    calc 2 * Emax * ((D : ℝ) + 1)
        = 4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (D + 1) * (S.card : ℝ) * (S.card : ℝ) := by
          rw [hEmax]; ring
      _ ≤ T * S.card := h
  have hE1 : 2 * Emax ≤ T * S.card / ((D : ℝ) + 1) := by
    rw [le_div_iff₀ hDpos]
    exact hEsmall
  have hD1 : (1 : ℝ) ≤ (D : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
  have hdiv : T * S.card / ((D : ℝ) + 1) ≤ T * S.card :=
    div_le_self (by positivity) hD1
  -- The mean of the density itself.
  have hI₀ : |(∫ t in (0 : ℝ)..T, f t) - T * (S.card : ℝ)| ≤ Emax := by
    have h := abs_integral_boxDensity_mul_cos_sub_le (P := P) (D := D) (θ := θ) hP (k := 1) le_rfl
      (ϑ := 0) (fun n _ => by simp) T
    simp only [Nat.cast_one, Real.log_one, mul_zero, sub_zero, Real.cos_zero, mul_one, one_mul] at h
    have hfil : (S.filter fun n => n ∈ S) = S := filter_true_of_mem fun _ h => h
    simp only [← hS, hfil] at h
    refine h.trans ?_
    have hle : (radicalOf P : ℝ) ^ D ≤ (radicalOf P : ℝ) ^ (D + 1) :=
      pow_le_pow_right₀ hRR (Nat.le_succ D)
    rw [hEmax]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) (by positivity)
  -- The mean against each character.
  have hIp : ∀ p ∈ P, (∫ t in (0 : ℝ)..T, f t) -
      (∫ t in (0 : ℝ)..T, f t * Real.cos (t * Real.log p - θ p)) ≤ T * S.card / ((D : ℝ) + 1) * 2 := by
    intro p hp
    have hpp := hP p hp
    have hmul : ∀ n ∈ S, targetPhase P θ (n * p) = targetPhase P θ n + θ p := fun n hn =>
      targetPhase_mul_prime hP (by have := mem_exponentBox_pos D hn; omega) hp
    have h := abs_integral_boxDensity_mul_cos_sub_le (P := P) (D := D) (θ := θ) hP hpp.pos hmul T
    have hple : (p : ℝ) ≤ radicalOf P := by
      exact_mod_cast Nat.le_of_dvd hRpos (Finset.dvd_prod_of_mem (fun q => q) hp)
    have hE : 2 * ((p : ℝ) * (radicalOf P : ℝ) ^ D) * (S.card : ℝ) ^ 2 ≤ Emax := by
      have hpowR : (radicalOf P : ℝ) ^ (D + 1) = (radicalOf P : ℝ) ^ D * (radicalOf P : ℝ) :=
        pow_succ _ _
      have this : (p : ℝ) * (radicalOf P : ℝ) ^ D ≤ (radicalOf P : ℝ) ^ (D + 1) := by
        rw [hpowR, mul_comm]
        exact mul_le_mul_of_nonneg_left hple (by positivity)
      have h2 : 0 ≤ (S.card : ℝ) ^ 2 := by positivity
      rw [hEmax]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) h2
    have hcard := card_sub_card_filter_le (P := P) (D := D) hP hp
    have hcardle : (S.card : ℝ) - ((S.filter fun n => n * p ∈ S).card : ℝ) ≤ S.card / ((D : ℝ) + 1) := by
      rw [le_div_iff₀ hDpos]
      exact hcard
    have h1 := (abs_le.mp hI₀).2
    have h2 := (abs_le.mp (h.trans hE)).1
    have h3 : T * ((S.card : ℝ) - ((S.filter fun n => n * p ∈ S).card : ℝ)) ≤
        T * (S.card / ((D : ℝ) + 1)) := mul_le_mul_of_nonneg_left hcardle hT0.le
    have h4 : T * (S.card / ((D : ℝ) + 1)) = T * S.card / ((D : ℝ) + 1) := by ring
    linarith
  -- Integrate the assumed lower bound against the density.
  set V : ℝ := 5 * A / ((D : ℝ) + 1) with hV
  set G : ℝ → ℝ := fun t => ∑ p ∈ P, a p * (1 - Real.cos (t * Real.log p - θ p)) with hG
  have hGc : Continuous G := by
    simp only [hG]
    fun_prop
  have hmono : (∫ t in (0 : ℝ)..T, f t * V) ≤ ∫ t in (0 : ℝ)..T, f t * G t := by
    refine intervalIntegral.integral_mono_on hT0.le ((hfc.mul continuous_const).intervalIntegrable _ _)
      ((hfc.mul hGc).intervalIntegrable _ _) fun t ht => ?_
    exact mul_le_mul_of_nonneg_left (hno t ht).le (hfn t)
  have hexpand : (∫ t in (0 : ℝ)..T, f t * G t) =
      ∑ p ∈ P, a p * ((∫ t in (0 : ℝ)..T, f t) -
        ∫ t in (0 : ℝ)..T, f t * Real.cos (t * Real.log p - θ p)) := by
    have hfun : ∀ t, f t * G t = ∑ p ∈ P, a p * (f t - f t * Real.cos (t * Real.log p - θ p)) := by
      intro t
      simp only [hG, mul_sum]
      refine sum_congr rfl fun p _ => ?_
      ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_finsetSum fun p _ => Continuous.intervalIntegrable (by fun_prop) _ _]
    refine sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (hfc.intervalIntegrable _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hupper : (∫ t in (0 : ℝ)..T, f t * G t) ≤ A * (T * S.card / ((D : ℝ) + 1) * 2) := by
    rw [hexpand, hA, sum_mul]
    exact sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hIp p hp) (ha p hp)
  have hlower : T * S.card / 2 ≤ ∫ t in (0 : ℝ)..T, f t := by
    have h1 := (abs_le.mp hI₀).1
    nlinarith
  have hVpos : 0 ≤ V := by positivity
  have hconst : (∫ t in (0 : ℝ)..T, f t * V) = (∫ t in (0 : ℝ)..T, f t) * V :=
    intervalIntegral.integral_mul_const _ _
  rw [hconst] at hmono
  have hcontra : V * (T * S.card / 2) ≤ A * (T * S.card / ((D : ℝ) + 1) * 2) := by
    calc V * (T * S.card / 2) ≤ V * ∫ t in (0 : ℝ)..T, f t := mul_le_mul_of_nonneg_left hlower hVpos
      _ = (∫ t in (0 : ℝ)..T, f t) * V := mul_comm _ _
      _ ≤ _ := hmono.trans hupper
  have hTS : 0 < T * (S.card : ℝ) := mul_pos hT0 hSR
  have hval1 : V * (T * S.card / 2) = (5 / 2) * (A * (T * S.card) / ((D : ℝ) + 1)) := by
    rw [hV]
    field_simp
  have hval2 : A * (T * S.card / ((D : ℝ) + 1) * 2) = 2 * (A * (T * S.card) / ((D : ℝ) + 1)) := by
    field_simp
  rw [hval1, hval2] at hcontra
  have hpos : 0 < A * (T * S.card) / ((D : ℝ) + 1) := by positivity
  linarith

/-- The box has size at most `R^D`, so the explicit threshold is at most `4 (D+1) R^{2D+1}`. -/
theorem threshold_le (hP : ∀ p ∈ P, p.Prime) :
    4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (D + 1) * ((exponentBox P D).card : ℝ) ≤
      4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (2 * D + 1) := by
  have hR := radicalOf_pos hP
  have hcard : (exponentBox P D).card ≤ radicalOf P ^ D := by
    have h : (exponentBox P D) ⊆ Finset.Ioc 0 (radicalOf P ^ D) := fun n hn =>
      mem_Ioc.mpr ⟨mem_exponentBox_pos D hn, mem_exponentBox_le D hn⟩
    simpa using card_le_card h
  have hcardR : ((exponentBox P D).card : ℝ) ≤ (radicalOf P : ℝ) ^ D := by exact_mod_cast hcard
  have hpow : (radicalOf P : ℝ) ^ (2 * D + 1) = (radicalOf P : ℝ) ^ (D + 1) * (radicalOf P : ℝ) ^ D := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left hcardR (by positivity)

end GaloisForLFunctions.RigidArithmeticOfCuts
