import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-!
# Zeros of exponential-polynomial sequences at consecutive integers

Let `K` be a field of characteristic zero, `ω_l` pairwise distinct nonzero elements of `K`
(`l ∈ L`), and `Q_l ∈ K[X]` polynomials of degree at most `N`.  If

`u(x) = Σ_{l ∈ L} Q_l(x) ω_l^x`

vanishes at the `(N+1)|L|` integers `x = 0, 1, …, (N+1)|L| − 1`, then every `Q_l` is zero.

The operator `(E − b)v(x) = v(x+1) − b v(x)` maps `Q(x) a^x` to `(a Q(x+1) − b Q(x)) a^x`.  For
`a ≠ b` the polynomial map `Q ↦ a Q(X+1) − b Q` is injective and preserves the degree bound; for
`a = b` it lowers the degree, so `(E − ω_{l₀})^{N+1}` annihilates the `l₀`-term.  Each application
of `E − b` shortens the vanishing window by one, and induction on `|L|` finishes; the last
polynomial has `N+1` zeros.

For the auxiliary polynomials of Fel'dman's construction we use the Lagrange-type basis
`g_k(X) = ∏_{i ≤ N, i ≠ k} (X + i + 1)`, `k ≤ N`: `g_k` does not vanish at `−(k+1)` while every
other `g_{k'}` does, so a vanishing combination has zero coefficients.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Polynomial Finset

variable {K : Type*} [Field K]

/-- The twisted first difference `v(x+1) − b v(x)` of a sequence. -/
def shiftDiff (b : K) (v : ℕ → K) (x : ℕ) : K := v (x + 1) - b * v x

/-- The polynomial `a Q(X+1) − b Q(X)`. -/
def expPolyStep (a b : K) (Q : K[X]) : K[X] := C a * taylor 1 Q - C b * Q

theorem shiftDiff_expPoly (a b : K) (Q : K[X]) :
    shiftDiff b (fun x : ℕ => Q.eval (x : K) * a ^ x) =
      fun x : ℕ => (expPolyStep a b Q).eval (x : K) * a ^ x := by
  funext x
  simp only [shiftDiff, expPolyStep, eval_sub, eval_mul, eval_C, taylor_eval]
  push_cast
  ring

theorem iterate_shiftDiff_expPoly (a b : K) (Q : K[X]) (n : ℕ) :
    (shiftDiff b)^[n] (fun x : ℕ => Q.eval (x : K) * a ^ x) =
      fun x : ℕ => ((expPolyStep a b)^[n] Q).eval (x : K) * a ^ x := by
  induction n generalizing Q with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, shiftDiff_expPoly, ih, Function.iterate_succ_apply]

theorem shiftDiff_sum {ι : Type*} (L : Finset ι) (b : K) (v : ι → ℕ → K) :
    shiftDiff b (fun x => ∑ l ∈ L, v l x) = fun x => ∑ l ∈ L, shiftDiff b (v l) x := by
  funext x
  simp only [shiftDiff, mul_sum, ← sum_sub_distrib]

theorem iterate_shiftDiff_sum {ι : Type*} (L : Finset ι) (b : K) (v : ι → ℕ → K) (n : ℕ) :
    (shiftDiff b)^[n] (fun x => ∑ l ∈ L, v l x) =
      fun x => ∑ l ∈ L, (shiftDiff b)^[n] (v l) x := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, shiftDiff_sum, ih]
      rfl

/-- Each difference shortens the vanishing window by one. -/
theorem iterate_shiftDiff_eq_zero_of_window (b : K) {v : ℕ → K} {m n : ℕ}
    (hv : ∀ x < m + n, v x = 0) : ∀ x < m, (shiftDiff b)^[n] v x = 0 := by
  induction n generalizing v with
  | zero => simpa using hv
  | succ n ih =>
      rw [Function.iterate_succ]
      refine ih fun x hx => ?_
      simp only [shiftDiff]
      rw [hv (x + 1) (by omega), hv x (by omega), mul_zero, sub_zero]

theorem natDegree_expPolyStep_le (a b : K) (Q : K[X]) :
    (expPolyStep a b Q).natDegree ≤ Q.natDegree := by
  unfold expPolyStep
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_taylor Q 1).le
  · exact natDegree_C_mul_le _ _

theorem natDegree_iterate_expPolyStep_le (a b : K) (Q : K[X]) (n : ℕ) :
    ((expPolyStep a b)^[n] Q).natDegree ≤ Q.natDegree := by
  induction n generalizing Q with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih _).trans (natDegree_expPolyStep_le a b Q)

/-- For `a ≠ b` the step is injective. -/
theorem eq_zero_of_expPolyStep_eq_zero {a b : K} (hab : a ≠ b) {Q : K[X]}
    (h : expPolyStep a b Q = 0) : Q = 0 := by
  by_contra hQ
  have hcoeff := congrArg (fun P : K[X] => P.coeff Q.natDegree) h
  simp only [expPolyStep, coeff_sub, coeff_C_mul, coeff_zero] at hcoeff
  have htop : (taylor 1 Q).coeff Q.natDegree = Q.leadingCoeff := by
    rw [← natDegree_taylor Q 1, ← leadingCoeff, leadingCoeff_taylor]
  rw [htop, ← leadingCoeff, ← sub_mul] at hcoeff
  exact (mul_ne_zero (sub_ne_zero.mpr hab) (leadingCoeff_ne_zero.mpr hQ)) hcoeff

theorem eq_zero_of_iterate_expPolyStep_eq_zero {a b : K} (hab : a ≠ b) {Q : K[X]} {n : ℕ}
    (h : (expPolyStep a b)^[n] Q = 0) : Q = 0 := by
  induction n generalizing Q with
  | zero => exact h
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      exact eq_zero_of_expPolyStep_eq_zero hab (ih h)

/-- For `a = b` the step lowers the degree, so `n` steps annihilate a polynomial of degree `< n`. -/
theorem iterate_expPolyStep_self_eq_zero (a : K) {Q : K[X]} {n : ℕ} (hQ : Q.natDegree < n) :
    (expPolyStep a a)^[n] Q = 0 := by
  induction n generalizing Q with
  | zero => omega
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      by_cases hE : expPolyStep a a Q = 0
      · rw [hE]
        clear ih hQ
        induction n with
        | zero => rfl
        | succ n ihn =>
            rw [Function.iterate_succ_apply]
            have h0 : expPolyStep a a (0 : K[X]) = 0 := by simp [expPolyStep]
            rw [h0, ihn]
      · refine ih ?_
        have hstep : expPolyStep a a Q = C a * (taylor 1 Q - Q) := by
          simp only [expPolyStep]
          ring
        have hdiff : taylor 1 Q - Q ≠ 0 := by
          intro h0
          apply hE
          rw [hstep, h0, mul_zero]
        have hQ0 : Q ≠ 0 := by
          intro h0
          apply hdiff
          rw [h0]
          simp
        have hlt : (taylor 1 Q - Q).degree < Q.degree := by
          have := degree_sub_lt (p := taylor 1 Q) (q := Q) (degree_taylor Q 1)
            (by rw [Ne, ← degree_eq_bot, degree_taylor, degree_eq_bot]; exact hQ0)
            (leadingCoeff_taylor 1 Q)
          rwa [degree_taylor] at this
        have hnat : (taylor 1 Q - Q).natDegree < Q.natDegree :=
          natDegree_lt_natDegree hdiff hlt
        calc (expPolyStep a a Q).natDegree
            ≤ (taylor 1 Q - Q).natDegree := by
              rw [hstep]
              exact natDegree_C_mul_le _ _
          _ < Q.natDegree := hnat
          _ ≤ n := by omega

/-- **Zeros of exponential-polynomial sequences.**  If `Σ_{l ∈ L} Q_l(x) ω_l^x` vanishes at
`x = 0, …, (N+1)|L| − 1`, with pairwise distinct nonzero `ω_l` and `deg Q_l ≤ N`, then every
`Q_l = 0`. -/
theorem eq_zero_of_expPoly_eval_eq_zero [CharZero K] {ι : Type*} [DecidableEq ι] (L : Finset ι)
    (ω : ι → K) (hω : ∀ l ∈ L, ∀ l' ∈ L, ω l = ω l' → l = l') (hω0 : ∀ l ∈ L, ω l ≠ 0)
    (N : ℕ) (Q : ι → K[X]) (hQ : ∀ l ∈ L, (Q l).natDegree ≤ N)
    (hvan : ∀ x : ℕ, x < (N + 1) * #L → ∑ l ∈ L, (Q l).eval (x : K) * ω l ^ x = 0) :
    ∀ l ∈ L, Q l = 0 := by
  induction L using Finset.induction_on generalizing Q with
  | empty => simp
  | insert l₀ L hl₀ ih =>
      have hω' : ∀ l ∈ L, ∀ l' ∈ L, ω l = ω l' → l = l' := fun l hl l' hl' =>
        hω l (mem_insert_of_mem hl) l' (mem_insert_of_mem hl')
      have hne : ∀ l ∈ L, ω l ≠ ω l₀ := fun l hl h =>
        hl₀ ((hω l (mem_insert_of_mem hl) l₀ (mem_insert_self l₀ L) h) ▸ hl)
      set v : ℕ → K := fun x => ∑ l ∈ insert l₀ L, (Q l).eval (x : K) * ω l ^ x with hv
      have hcard : #(insert l₀ L) = #L + 1 := card_insert_of_notMem hl₀
      have hwin := iterate_shiftDiff_eq_zero_of_window (ω l₀) (v := v) (m := (N + 1) * #L)
        (n := N + 1) (fun x hx => hvan x (by rw [hcard]; linarith))
      have hW : (shiftDiff (ω l₀))^[N + 1] v = fun x : ℕ =>
          ∑ l ∈ L, ((expPolyStep (ω l) (ω l₀))^[N + 1] (Q l)).eval (x : K) * ω l ^ x := by
        rw [hv, iterate_shiftDiff_sum]
        funext x
        rw [sum_insert hl₀]
        simp only [iterate_shiftDiff_expPoly]
        rw [iterate_expPolyStep_self_eq_zero (ω l₀)
          (Nat.lt_succ_of_le (hQ l₀ (mem_insert_self l₀ L)))]
        simp
      have hQ' := ih hω' (fun l hl => hω0 l (mem_insert_of_mem hl))
        (fun l => (expPolyStep (ω l) (ω l₀))^[N + 1] (Q l))
        (fun l hl => (natDegree_iterate_expPolyStep_le _ _ _ _).trans
          (hQ l (mem_insert_of_mem hl)))
        (fun x hx => by
          have := hwin x hx
          rw [hW] at this
          exact this)
      have hrest : ∀ l ∈ L, Q l = 0 := fun l hl =>
        eq_zero_of_iterate_expPolyStep_eq_zero (hne l hl) (hQ' l hl)
      have hl₀eval : ∀ x : ℕ, x < N + 1 → (Q l₀).eval (x : K) = 0 := by
        intro x hx
        have h := hvan x (by rw [hcard]; nlinarith)
        rw [sum_insert hl₀, sum_eq_zero (fun l hl => by rw [hrest l hl]; simp), add_zero] at h
        exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (hω0 l₀ (mem_insert_self l₀ L)))
      intro l hl
      classical
      rcases mem_insert.mp hl with rfl | hl
      · refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
          ((range (N + 1)).image (fun x : ℕ => (x : K))) ?_ ?_
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
          exact hl₀eval x (mem_range.mp hx)
        · rw [card_image_of_injective _ Nat.cast_injective, card_range]
          exact Nat.lt_succ_of_le (hQ l (mem_insert_self l L))
      · exact hrest l hl

/-! ## The Lagrange-type basis -/

/-- `g_k(X) = ∏_{i ≤ N, i ≠ k} (X + i + 1)`. -/
def lagrangeShift (N k : ℕ) : K[X] := ∏ i ∈ (range (N + 1)).erase k, (X + C ((i : K) + 1))

theorem natDegree_lagrangeShift_le {N k : ℕ} (hk : k ≤ N) :
    (lagrangeShift (K := K) N k).natDegree ≤ N := by
  unfold lagrangeShift
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
  rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
  omega

theorem eval_lagrangeShift_self_ne_zero [CharZero K] {N k : ℕ} :
    (lagrangeShift (K := K) N k).eval (-((k : K) + 1)) ≠ 0 := by
  unfold lagrangeShift
  rw [eval_prod]
  refine prod_ne_zero_iff.mpr fun i hi => ?_
  simp only [eval_add, eval_X, eval_C]
  have hik : i ≠ k := (mem_erase.mp hi).1
  intro h
  apply hik
  have : (i : K) = k := by linear_combination h
  exact_mod_cast this

theorem eval_lagrangeShift_of_ne {N k k' : ℕ} (hk' : k' ≤ N) (hne : k' ≠ k) :
    (lagrangeShift (K := K) N k).eval (-((k' : K) + 1)) = 0 := by
  unfold lagrangeShift
  rw [eval_prod]
  refine prod_eq_zero (i := k') (mem_erase.mpr ⟨hne, mem_range.mpr (by omega)⟩) ?_
  simp

/-- **Independence of the Lagrange-type basis.** -/
theorem eq_zero_of_sum_lagrangeShift_eq_zero [CharZero K] {N : ℕ} (c : ℕ → K)
    (h : ∑ k ∈ range (N + 1), C (c k) * lagrangeShift N k = 0) :
    ∀ k ∈ range (N + 1), c k = 0 := by
  intro k hk
  have hev := congrArg (fun P : K[X] => P.eval (-((k : K) + 1))) h
  simp only [eval_finsetSum, eval_mul, eval_C, eval_zero] at hev
  rw [sum_eq_single k (fun k' _ hne => by
      rw [eval_lagrangeShift_of_ne (k := k') (Nat.lt_succ_iff.mp (mem_range.mp hk))
        (Ne.symm hne), mul_zero])
    (fun hkn => absurd hk hkn)] at hev
  exact (mul_eq_zero.mp hev).resolve_right eval_lagrangeShift_self_ne_zero

end GaloisForLFunctions.RHTower.Matveev
