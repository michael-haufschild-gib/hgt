import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePrimeDebitOfInterleavingSelfIntersections
import Mathlib.Algebra.Order.Chebyshev

/-!
# Additive-Shift Stability of the Archimedean Weil Comb and Divisibility Contact Destruction

Decompose `combForm S c = nonContactCombForm S c - ∑_{n ∈ S} ∑_{m ∈ S \ {n}} c_m c_n contact m n`,
where `nonContactCombForm S c = 2 * degOne S c * degTwo S c + diagRealBudget S c` collects the
poles, diagonal counterterms, and off-diagonal archimedean jets. Under an additive translation
`n ↦ n + h` (`addShiftSet h S`, `addShiftProfile h c`):

1. **Exact singular-jet invariance** (`jetKernel_add_sub_jetKernel`):
   The Hilbert singular part `1 / (2 |m - n|)` of `jetKernel m n` cancels identically under
   `(m, n) ↦ (m + h, n + h)`, leaving only `-h / ((m + n)(m + n + 2h))`.

2. **`O((h / N + |S| h / N²) ∑ c_n²)` stability of the non-contact Weil form**
   (`diagRealBudget_addShift_sub_le`, `degTwo_addShift`, `poleProduct_addShift_sub_le`,
   `nonContactCombForm_addShift_sub_le`):
   Whenever `S ⊆ [N, ∞)` (`N ≥ 1`), translating `S` and `c` by `h` preserves `degTwo` identically
   and perturbs `diagRealBudget`, `2 d₁ d₂`, and `nonContactCombForm` by at most explicit multiples
   of `(h / N + |S| h / N²) ∑_{n ∈ S} c_n²` (`O_Q((h / N) ∑ c_n²)` on windows `S ⊆ [N, Q N]`).

3. **Uniqueness of ratio shifts, single-step `+1` contact destruction, and all-prime ray coupling**
   (`eq_of_add_eq_mul_add`, `not_dvd_add_one_of_dvd_of_le`, `contact_add_one_eq_zero_of_le`,
   `contact_prime_not_dvd_dvd`):
   In contrast to the `O(h / N)`-smooth archimedean and polar pieces, each pair `(m, n)` meets any
   fixed ratio `r ≥ 2` at **at most one** additive shift `h`; on any window `[N, Q N]` with `N ≥ Q`,
   a single `+1` shift destroys every existing contact (`contact m n ≠ 0 → contact (m+1) (n+1) = 0`);
   and for every prime `p`, contacts between `ℕ \ pℕ` and `pℕ` occur solely along `p`-power rays
   `i = p^k m` with weight `log p`.
-/

noncomputable section
set_option autoImplicit false

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open AbsoluteGeometryOfSpecZ (jetKernel jetKernel_comm)
open HodgeTheoryOfAFixedPart

/-! ## 1. Exact singular-jet cancellation under additive shifts -/

/-- Under `(m, n) ↦ (m + h, n + h)`, the singular Hilbert difference `1 / (2 |m - n|)` cancels
identically and `jetKernel` changes by `-h / ((m + n)(m + n + 2h))`. -/
theorem jetKernel_add_sub_jetKernel {m n : ℕ} (hpos : 0 < m + n) (h : ℕ) :
    jetKernel (m + h) (n + h) - jetKernel m n =
      -((h : ℝ) / (((m : ℝ) + n) * ((m : ℝ) + n + 2 * h))) := by
  rw [jetKernel_eq_add_halves, jetKernel_eq_add_halves]
  have habs : ((m + h : ℕ) : ℝ) - (n + h : ℕ) = (m : ℝ) - n := by push_cast; ring
  have hsum : ((m + h : ℕ) : ℝ) + (n + h : ℕ) = (m : ℝ) + n + 2 * h := by push_cast; ring
  have hmn0 : ((m : ℝ) + n) ≠ 0 := by exact_mod_cast hpos.ne'
  have hmnh0 : ((m : ℝ) + n + 2 * h) ≠ 0 := by positivity
  rw [habs, hsum]
  field_simp [hmn0, hmnh0]
  ring

/-! ## 2. Additive shifts of comb supports and quadratic stability of `nonContactCombForm` -/

/-- Support `S` translated additively by `h`: `{n + h | n ∈ S}`. -/
def addShiftSet (h : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.map ⟨fun n => n + h, fun _ _ hab => Nat.add_right_cancel hab⟩

/-- Profile `c` translated additively by `h`: `c_h(k) = c(k - h)` for `k ≥ h`, `0` otherwise. -/
def addShiftProfile (h : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h ≤ k then c (k - h) else 0

/-- Non-contact part of `combForm`: pole product `2 d₁ d₂` plus `diagRealBudget`. -/
def nonContactCombForm (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  2 * (degOne S c * degTwo S c) + diagRealBudget S c

theorem combForm_eq_nonContactCombForm_sub_contacts (S : Finset ℕ) (c : ℕ → ℝ) :
    combForm S c =
      nonContactCombForm S c - ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contact m n := by
  rw [combForm_eq_diagRealBudget_sub_mixedPrimeDebit, mixedPrimeDebit, mixedPrimeDebitW,
    nonContactCombForm]
  have hc : ∀ m n : ℕ, contactW (fun k => (Λ k : ℝ)) m n = contact m n := fun _ _ => rfl
  simp_rw [hc]
  ring

@[simp] theorem addShiftProfile_add (h : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    addShiftProfile h c (n + h) = c n := by
  simp [addShiftProfile]

@[simp] theorem card_addShiftSet (h : ℕ) (S : Finset ℕ) :
    (addShiftSet h S).card = S.card :=
  Finset.card_map _

/-- Exact shift invariance of the second pole degree `degTwo`. -/
theorem degTwo_addShift (h : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) :
    degTwo (addShiftSet h S) (addShiftProfile h c) = degTwo S c := by
  unfold degTwo addShiftSet
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun n _ => addShiftProfile_add h c n

private theorem erase_addShiftSet (h : ℕ) (S : Finset ℕ) (n : ℕ) :
    (addShiftSet h S).erase (n + h) = addShiftSet h (S.erase n) := by
  ext k
  simp only [addShiftSet, Finset.mem_erase, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hk_ne, m, hmS, rfl⟩
    exact ⟨m, ⟨fun hmn => hk_ne (congrArg (· + h) hmn), hmS⟩, rfl⟩
  · rintro ⟨m, ⟨hmn, hmS⟩, rfl⟩
    exact ⟨fun heq => hmn (Nat.add_right_cancel heq), m, hmS, rfl⟩

/-- **Quadratic stability of `diagRealBudget` under additive shift `n ↦ n + h`.**
For `S ⊆ [N, ∞)` (`N ≥ 1`), shifting by `h` changes `diagRealBudget` by at most
`(h / N + |S| h / (4 N²)) ∑_{n ∈ S} c_n²`. -/
theorem diagRealBudget_addShift_sub_le {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hS : ∀ n ∈ S, N ≤ n) (h : ℕ) (c : ℕ → ℝ) :
    |diagRealBudget (addShiftSet h S) (addShiftProfile h c) - diagRealBudget S c| ≤
      ((h : ℝ) / N + (S.card : ℝ) * h / (4 * (N : ℝ) ^ 2)) * ∑ n ∈ S, c n ^ 2 := by
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  -- Rewrite shifted sums back onto `S`.
  have hdiag_shift : ∑ k ∈ addShiftSet h S, (addShiftProfile h c k) ^ 2 * counterterm k =
      ∑ n ∈ S, c n ^ 2 * counterterm (n + h) := by
    unfold addShiftSet
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun n _ => by simp
  have hjet_shift : ∑ k ∈ addShiftSet h S, ∑ j ∈ (addShiftSet h S).erase k,
        addShiftProfile h c j * addShiftProfile h c k * jetKernel j k =
      ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * jetKernel (m + h) (n + h) := by
    unfold addShiftSet
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    change ∑ j ∈ (addShiftSet h S).erase (n + h), _ = _
    rw [erase_addShiftSet, addShiftSet, Finset.sum_map]
    exact Finset.sum_congr rfl fun m _ => by simp
  have hdiff_eq : diagRealBudget (addShiftSet h S) (addShiftProfile h c) - diagRealBudget S c =
      (∑ n ∈ S, c n ^ 2 * (counterterm (n + h) - counterterm n)) -
      (∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (jetKernel (m + h) (n + h) - jetKernel m n)) := by
    unfold diagRealBudget
    rw [hdiag_shift, hjet_shift, sub_sub_sub_comm, ← Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun n _ => by ring
    · rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
  -- Bound the counterterm difference `0 ≤ log((n+h)/2π) - log(n/2π) = log(1 + h/n) ≤ h/N`.
  have hct_bound : |∑ n ∈ S, c n ^ 2 * (counterterm (n + h) - counterterm n)| ≤
      ((h : ℝ) / N) * ∑ n ∈ S, c n ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hS n hn
    have hn_pos : (0 : ℝ) < n := hN_pos.trans_le hnN
    have hnh_pos : (0 : ℝ) < ((n + h : ℕ) : ℝ) := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) h]
    have hct_diff : counterterm (n + h) - counterterm n = Real.log (((n + h : ℕ) : ℝ) / n) := by
      unfold counterterm
      rw [← Real.log_div (div_pos hnh_pos Real.two_pi_pos).ne' (div_pos hn_pos Real.two_pi_pos).ne',
        div_div_div_cancel_right₀ Real.two_pi_pos.ne']
    have hlog_nn : 0 ≤ Real.log (((n + h : ℕ) : ℝ) / n) :=
      Real.log_nonneg ((one_le_div hn_pos).mpr (by push_cast; linarith))
    have hlog_le : Real.log (((n + h : ℕ) : ℝ) / n) ≤ (h : ℝ) / N := by
      calc Real.log (((n + h : ℕ) : ℝ) / n)
          ≤ ((n + h : ℕ) : ℝ) / n - 1 := Real.log_le_sub_one_of_pos (div_pos hnh_pos hn_pos)
        _ = (h : ℝ) / n := by push_cast; field_simp [hn_pos.ne']; ring
        _ ≤ (h : ℝ) / N := div_le_div_of_nonneg_left (Nat.cast_nonneg h) hN_pos hnN
    rw [hct_diff, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hlog_nn, mul_comm]
    exact mul_le_mul_of_nonneg_right hlog_le (sq_nonneg _)
  -- Bound the smooth-jet difference via Cauchy–Schwarz `(∑ |c_n|)² ≤ |S| ∑ c_n²`.
  have hjet_bound : |∑ n ∈ S, ∑ m ∈ S.erase n,
      c m * c n * (jetKernel (m + h) (n + h) - jetKernel m n)| ≤
      ((S.card : ℝ) * h / (4 * (N : ℝ) ^ 2)) * ∑ n ∈ S, c n ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ n ∈ S, |∑ m ∈ S.erase n, c m * c n * (jetKernel (m + h) (n + h) - jetKernel m n)| ≤
        ∑ m ∈ S, |c m| * |c n| * ((h : ℝ) / (4 * (N : ℝ) ^ 2)) := by
      intro n hn
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun m hm => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset n S) fun _ _ _ => by positivity)
      have hmS := Finset.mem_of_mem_erase hm
      have hmN : (N : ℝ) ≤ m := by exact_mod_cast hS m hmS
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast hS n hn
      have hpos_mn : 0 < m + n := by have := hS n hn; omega
      have hmn_pos : 0 < (m : ℝ) + n := by linarith
      have hmnh_pos : 0 < (m : ℝ) + n + 2 * h := by linarith [Nat.cast_nonneg (α := ℝ) h]
      rw [jetKernel_add_sub_jetKernel hpos_mn h, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg (α := ℝ) h) (mul_pos hmn_pos hmnh_pos).le)]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) h)
        (by positivity : 0 < 4 * (N : ℝ) ^ 2) ?_
      have hmn2N : 2 * (N : ℝ) ≤ (m : ℝ) + n := by linarith
      have hmnh2N : 2 * (N : ℝ) ≤ (m : ℝ) + n + 2 * h := by linarith [Nat.cast_nonneg (α := ℝ) h]
      calc 4 * (N : ℝ) ^ 2 = (2 * N) * (2 * N) := by ring
        _ ≤ ((m : ℝ) + n) * ((m : ℝ) + n + 2 * h) :=
            mul_le_mul hmn2N hmnh2N (by positivity) (by positivity)
    have hsum_sq : (∑ n ∈ S, |c n|) ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, c n ^ 2 := by
      simpa [sq_abs] using sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => |c n|)
    calc ∑ n ∈ S, |∑ m ∈ S.erase n, c m * c n * (jetKernel (m + h) (n + h) - jetKernel m n)|
        ≤ ∑ n ∈ S, ∑ m ∈ S, |c m| * |c n| * ((h : ℝ) / (4 * (N : ℝ) ^ 2)) :=
          Finset.sum_le_sum hrow
      _ = ((h : ℝ) / (4 * (N : ℝ) ^ 2)) * (∑ n ∈ S, |c n|) ^ 2 := by
          rw [sq (∑ n ∈ S, |c n|), Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => by ring
      _ ≤ ((h : ℝ) / (4 * (N : ℝ) ^ 2)) * ((S.card : ℝ) * ∑ n ∈ S, c n ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_sq (by positivity)
      _ = ((S.card : ℝ) * h / (4 * (N : ℝ) ^ 2)) * ∑ n ∈ S, c n ^ 2 := by ring
  rw [hdiff_eq]
  exact (abs_sub _ _).trans ((add_le_add hct_bound hjet_bound).trans_eq (by ring))

/-- **Quadratic stability of the pole product `2 d₁ d₂` under additive shift `n ↦ n + h`.** -/
theorem poleProduct_addShift_sub_le {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hS : ∀ n ∈ S, N ≤ n) (h : ℕ) (c : ℕ → ℝ) :
    |2 * (degOne (addShiftSet h S) (addShiftProfile h c) *
        degTwo (addShiftSet h S) (addShiftProfile h c)) -
      2 * (degOne S c * degTwo S c)| ≤
      (2 * (S.card : ℝ) * h / (N : ℝ) ^ 2) * ∑ n ∈ S, c n ^ 2 := by
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [degTwo_addShift]
  have hd1_shift : degOne (addShiftSet h S) (addShiftProfile h c) - degOne S c =
      ∑ n ∈ S, c n * (1 / ((n + h : ℕ) : ℝ) - 1 / (n : ℝ)) := by
    unfold degOne addShiftSet
    rw [Finset.sum_map, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by simp [div_eq_mul_inv, mul_sub]
  have hd1_bound : |degOne (addShiftSet h S) (addShiftProfile h c) - degOne S c| ≤
      ((h : ℝ) / (N : ℝ) ^ 2) * ∑ n ∈ S, |c n| := by
    rw [hd1_shift]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hS n hn
    have hn_pos : (0 : ℝ) < n := hN_pos.trans_le hnN
    have hnh_pos : (0 : ℝ) < ((n + h : ℕ) : ℝ) := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) h]
    have hinv_diff : |1 / ((n + h : ℕ) : ℝ) - 1 / (n : ℝ)| ≤ (h : ℝ) / (N : ℝ) ^ 2 := by
      have heq : 1 / ((n + h : ℕ) : ℝ) - 1 / (n : ℝ) = -((h : ℝ) / (((n + h : ℕ) : ℝ) * n)) := by
        push_cast; field_simp [hn_pos.ne', hnh_pos.ne']; ring
      rw [heq, abs_neg, abs_of_nonneg (by positivity)]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg h) (by positivity) ?_
      have hnhN : (N : ℝ) ≤ ((n + h : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) h]
      calc (N : ℝ) ^ 2 = N * N := sq _
        _ ≤ ((n + h : ℕ) : ℝ) * n := mul_le_mul hnhN hnN hN_pos.le (by positivity)
    rw [abs_mul, mul_comm ((h : ℝ) / _)]
    exact mul_le_mul_of_nonneg_left hinv_diff (abs_nonneg _)
  have hd2_bound : |degTwo S c| ≤ ∑ n ∈ S, |c n| := Finset.abs_sum_le_sum_abs _ _
  have hsum_sq : (∑ n ∈ S, |c n|) ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, c n ^ 2 := by
    simpa [sq_abs] using sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => |c n|)
  have hid : 2 * (degOne (addShiftSet h S) (addShiftProfile h c) * degTwo S c) -
      2 * (degOne S c * degTwo S c) =
      2 * (degOne (addShiftSet h S) (addShiftProfile h c) - degOne S c) * degTwo S c := by ring
  rw [hid, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc 2 * |degOne (addShiftSet h S) (addShiftProfile h c) - degOne S c| * |degTwo S c|
      ≤ 2 * (((h : ℝ) / (N : ℝ) ^ 2) * ∑ n ∈ S, |c n|) * ∑ n ∈ S, |c n| :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd1_bound (by norm_num)) hd2_bound
          (abs_nonneg _) (by positivity)
    _ = (2 * (h : ℝ) / (N : ℝ) ^ 2) * (∑ n ∈ S, |c n|) ^ 2 := by ring
    _ ≤ (2 * (h : ℝ) / (N : ℝ) ^ 2) * ((S.card : ℝ) * ∑ n ∈ S, c n ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_sq (by positivity)
    _ = (2 * (S.card : ℝ) * h / (N : ℝ) ^ 2) * ∑ n ∈ S, c n ^ 2 := by ring

/-- **Combined additive-shift stability of `nonContactCombForm`.** -/
theorem nonContactCombForm_addShift_sub_le {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hS : ∀ n ∈ S, N ≤ n) (h : ℕ) (c : ℕ → ℝ) :
    |nonContactCombForm (addShiftSet h S) (addShiftProfile h c) - nonContactCombForm S c| ≤
      ((h : ℝ) / N + 9 * (S.card : ℝ) * h / (4 * (N : ℝ) ^ 2)) * ∑ n ∈ S, c n ^ 2 := by
  have hid : nonContactCombForm (addShiftSet h S) (addShiftProfile h c) - nonContactCombForm S c =
      (2 * (degOne (addShiftSet h S) (addShiftProfile h c) *
          degTwo (addShiftSet h S) (addShiftProfile h c)) -
        2 * (degOne S c * degTwo S c)) +
      (diagRealBudget (addShiftSet h S) (addShiftProfile h c) - diagRealBudget S c) := by
    unfold nonContactCombForm; ring
  rw [hid]
  exact (abs_add_le _ _).trans
    ((add_le_add (poleProduct_addShift_sub_le hN hS h c)
      (diagRealBudget_addShift_sub_le hN hS h c)).trans_eq (by ring))

/-! ## 3. Ratio-shift uniqueness, `+1` contact destruction, and all-prime ray coupling -/

/-- **Uniqueness of ratio-realizing shift:** for any `m, n : ℕ` and quotient `r ≥ 2`, at most one
additive shift `h ∈ ℕ` satisfies `n + h = r * (m + h)`. -/
theorem eq_of_add_eq_mul_add {m n r h₁ h₂ : ℕ} (hr : 2 ≤ r)
    (h1 : n + h₁ = r * (m + h₁)) (h2 : n + h₂ = r * (m + h₂)) :
    h₁ = h₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith

/-- **Single-step `+1` divisibility destruction:** if `m < n ≤ Q * m` and `Q ≤ m`, then
`m ∣ n → ¬ (m + 1 ∣ n + 1)`. -/
theorem not_dvd_add_one_of_dvd_of_le {m n Q : ℕ} (hmn : m < n) (hnQ : n ≤ Q * m) (hQm : Q ≤ m)
    (hdvd : m ∣ n) : ¬ (m + 1 ∣ n + 1) := by
  obtain ⟨r, rfl⟩ := hdvd
  have hm_pos : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hmn
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have hr1 : r ≤ 1 := by omega
    have : m * r ≤ m * 1 := Nat.mul_le_mul_left m hr1
    omega
  have hrQ : r ≤ Q := by
    have : m * r ≤ m * Q := by linarith
    exact Nat.le_of_mul_le_mul_left this hm_pos
  rintro ⟨q, hq⟩
  rcases le_or_gt r q with hge | hlt
  · have : (m + 1) * r ≤ (m + 1) * q := Nat.mul_le_mul_left (m + 1) hge
    nlinarith
  · have hq_le : q ≤ r - 1 := by omega
    have hmul : (m + 1) * q ≤ (m + 1) * (r - 1) := Nat.mul_le_mul_left (m + 1) hq_le
    have hexp : (m + 1) * (r - 1) + (m + 1 - r) = m * r := by
      have hr1 : 1 ≤ r := by omega
      have hrm1 : r ≤ m + 1 := by omega
      zify [hr1, hrm1]
      ring
    omega

/-- **Single-step `+1` contact destruction on `[Q, ∞)`:** whenever `Q ≤ m < n ≤ Q * m`, a nonzero
contact `contact m n ≠ 0` forces `contact (m + 1) (n + 1) = 0`. -/
theorem contact_add_one_eq_zero_of_le {m n Q : ℕ} (hmn : m < n) (hnQ : n ≤ Q * m) (hQm : Q ≤ m)
    (hc : contact m n ≠ 0) :
    contact (m + 1) (n + 1) = 0 := by
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_eq : m = 0 := by omega
    subst hm_eq
    simp at hnQ
    omega
  have hn_not_dvd : ¬ (n ∣ m) := fun h => absurd (Nat.le_of_dvd hm_pos h) (by omega)
  have hm_dvd_n : m ∣ n := by
    by_contra hnot
    apply hc
    simp [contact, hnot, hn_not_dvd]
  have h1 : ¬ (m + 1 ∣ n + 1) := not_dvd_add_one_of_dvd_of_le hmn hnQ hQm hm_dvd_n
  have h2 : ¬ (n + 1 ∣ m + 1) := fun h =>
    absurd (Nat.le_of_dvd (Nat.succ_pos m) h) (by omega)
  simp [contact, h1, h2]

/-- **All-prime cross-sector contact ray rigidity:** for any prime `p`, a `p`-free integer `m` and a
multiple `i > 0` of `p` have nonzero Weil contact only along the ray `i = p^k m` (`m = ordCompl[p] i`),
with constant weight `log p`. -/
theorem contact_prime_not_dvd_dvd {p m i : ℕ} (hp : p.Prime)
    (hm : ¬ p ∣ m) (hi : p ∣ i) (hi0 : 0 < i) :
    contact m i = if m = ordCompl[p] i then Real.log p else 0 := by
  unfold contact
  have h_not_im : ¬ i ∣ m := fun h => hm (hi.trans h)
  rw [if_neg h_not_im, add_zero]
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hm (h ▸ dvd_zero p)
  by_cases hd : m ∣ i
  · rw [if_pos hd]
    obtain ⟨q, rfl⟩ := hd
    have hq_dvd : p ∣ q := (hp.dvd_mul.mp hi).resolve_left hm
    rw [Nat.mul_div_cancel_left q hm0]
    by_cases hpp : IsPrimePow q
    · obtain ⟨q_p, k, hqp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpp
      have hp_eq : p = q_p := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hq_dvd)
      subst hp_eq
      have hfac : (m * p ^ k).factorization p = k := by
        rw [Nat.factorization_mul hm0.ne' (pow_ne_zero k hp.ne_zero), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hm, Nat.factorization_pow, Finsupp.smul_apply,
          hp.factorization_self, smul_eq_mul, mul_one, zero_add]
      have hoc : m = ordCompl[p] (m * p ^ k) := by
        rw [hfac, Nat.mul_div_cancel _ (pow_pos hp.pos k)]
      rw [if_pos hoc, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, if_neg]
      intro heq
      apply hpp
      have hself := Nat.ordProj_mul_ordCompl_eq_self (m * q) p
      rw [← heq] at hself
      have hq_eq : q = p ^ (m * q).factorization p := by
        apply Nat.eq_of_mul_eq_mul_left hm0
        rw [mul_comm m (p ^ _), hself]
      have hv : (m * q).factorization p ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hq_eq
        rw [hq_eq] at hq_dvd
        exact hp.not_dvd_one hq_dvd
      rw [hq_eq]
      exact hp.isPrimePow.pow hv
  · rw [if_neg hd, if_neg]
    intro heq
    exact hd (heq ▸ Nat.ordCompl_dvd i p)

end GaloisForLFunctions.SignedArithmeticCorrespondences

end
