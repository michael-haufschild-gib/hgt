import Mathlib.NumberTheory.Chebyshev
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Fel'dman's common divisor of bracket-deleted products

Fix `N` and `s`.  For every block `y + 1, …, y + N` of consecutive positive integers and every way
of deleting at most `s` of them, the product of the remaining integers is divisible by

`D(N, s) = ∏_{p^a ≤ N} p^{⌊N/p^a⌋ − s}`   (truncated subtraction):

each prime power `p^a ≤ N` divides at least `⌊N/p^a⌋` members of the block, and at most `s` of them
are deleted.  Legendre's formula in the form `log N! = Σ_{n ≤ N} ⌊N/n⌋ Λ(n)` gives

`log N! − log D(N, s) = Σ_{n ≤ N} min(⌊N/n⌋, s) Λ(n) ≤ (log 4 + 4)(3 + 2 log₂ s) N`,

by Chebyshev's bound `ψ(x) ≤ (log 4 + 4) x` applied on dyadic blocks.  Thus `D(N, s)` is `N!` up to
a factor `e^{O(N log s)}`, uniformly in the block.  This is Fel'dman's Lemma 5, the device that
lets the derivatives of the auxiliary polynomial `∏_{i ≤ N} (z + i)` be normalized at a total cost
`O(N log s)` rather than `O(N)` per derivative.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Chebyshev ArithmeticFunction

/-- The prime underlying a prime power, and `1` otherwise. -/
def primePowBase (n : ℕ) : ℕ := if IsPrimePow n then n.minFac else 1

theorem primePowBase_pos (n : ℕ) : 0 < primePowBase n := by
  unfold primePowBase
  split_ifs with h
  · exact (Nat.minFac_prime h.ne_one).pos
  · exact one_pos

theorem log_primePowBase (n : ℕ) : Real.log (primePowBase n) = Λ n := by
  rw [vonMangoldt_apply, primePowBase]
  split_ifs <;> simp

/-- The factorization of `primePowBase n` at a prime `p`. -/
theorem factorization_primePowBase (n p : ℕ) :
    (primePowBase n).factorization p = if IsPrimePow n ∧ n.minFac = p then 1 else 0 := by
  unfold primePowBase
  by_cases h : IsPrimePow n
  · rw [if_pos h, (Nat.minFac_prime h.ne_one).factorization]
    by_cases hp : n.minFac = p
    · rw [if_pos ⟨h, hp⟩, hp, Finsupp.single_eq_same]
    · rw [if_neg (fun hh => hp hh.2), Finsupp.single_eq_of_ne (Ne.symm hp)]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]
    simp

/-- **Fel'dman's common divisor** `∏_{p^a ≤ N} p^{⌊N/p^a⌋ − s}`. -/
def feldmanDivisor (N s : ℕ) : ℕ := ∏ n ∈ Icc 1 N, primePowBase n ^ (N / n - s)

theorem feldmanDivisor_pos (N s : ℕ) : 0 < feldmanDivisor N s :=
  prod_pos fun n _ => pow_pos (primePowBase_pos n) _

theorem log_feldmanDivisor (N s : ℕ) :
    Real.log (feldmanDivisor N s) = ∑ n ∈ Icc 1 N, ((N / n - s : ℕ) : ℝ) * Λ n := by
  rw [feldmanDivisor, Nat.cast_prod, Real.log_prod]
  · refine sum_congr rfl fun n _ => ?_
    rw [Nat.cast_pow, Real.log_pow, log_primePowBase]
  · intro n _
    have := primePowBase_pos n
    positivity

/-- **Legendre's formula, logarithmic form.** `log N! = Σ_{n ≤ N} ⌊N/n⌋ Λ(n)`. -/
theorem log_factorial_eq_sum_vonMangoldt (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℝ) * Λ n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity)
        (by exact_mod_cast (Nat.factorial_pos N).ne'), ih, ← vonMangoldt_sum]
      have hsplit : ∑ n ∈ Icc 1 (N + 1), (((N + 1) / n : ℕ) : ℝ) * Λ n =
          ∑ n ∈ Icc 1 (N + 1), ((N / n : ℕ) : ℝ) * Λ n +
            ∑ n ∈ Icc 1 (N + 1), (if n ∣ N + 1 then Λ n else 0) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun n _ => ?_
        rw [Nat.succ_div]
        split_ifs <;> push_cast <;> ring
      have hlast : ∑ n ∈ Icc 1 (N + 1), ((N / n : ℕ) : ℝ) * Λ n =
          ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℝ) * Λ n := by
        rw [sum_Icc_succ_top (by omega), Nat.div_eq_of_lt (by omega)]
        simp
      have hdiv : ∑ n ∈ Icc 1 (N + 1), (if n ∣ N + 1 then Λ n else 0) =
          ∑ n ∈ (N + 1).divisors, Λ n := by
        rw [← sum_filter]
        rfl
      rw [hsplit, hlast, hdiv]
      ring

/-! ## Divisibility -/

/-- A block of `N` consecutive integers contains at least `⌊N/n⌋` multiples of `n`. -/
theorem div_le_card_filter_dvd (N n y : ℕ) :
    N / n ≤ #{i ∈ Icc 1 N | n ∣ y + i} := by
  have hmap : #{i ∈ Icc 1 N | n ∣ y + i} =
      #{x ∈ Ioc 0 (y + N) | n ∣ x} - #{x ∈ Ioc 0 y | n ∣ x} := by
    have hsub : {x ∈ Ioc 0 y | n ∣ x} ⊆ {x ∈ Ioc 0 (y + N) | n ∣ x} := by
      intro x hx
      simp only [mem_filter, mem_Ioc] at hx ⊢
      exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
    rw [← card_sdiff_of_subset hsub]
    refine card_bij (fun i _ => y + i) ?_ ?_ ?_
    · intro i hi
      simp only [mem_filter, mem_Icc] at hi
      simp only [mem_sdiff, mem_filter, mem_Ioc]
      exact ⟨⟨⟨by omega, by omega⟩, hi.2⟩, fun h => by omega⟩
    · intro i _ j _ h
      omega
    · intro x hx
      simp only [mem_sdiff, mem_filter, mem_Ioc, not_and] at hx
      refine ⟨x - y, ?_, by omega⟩
      simp only [mem_filter, mem_Icc]
      have hxy : y < x := by
        by_contra hle
        exact hx.2 ⟨by omega, by omega⟩ hx.1.2
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show y + (x - y) = x by omega]
      exact hx.1.2
  rw [hmap, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  have := Nat.add_div_le_add_div y N n
  omega

/-- A prime power `n ≤ N` with base `p` divides at least `⌊N/n⌋ − s` of the kept integers. -/
theorem div_sub_le_card_filter_dvd {N s y n : ℕ} {I : Finset ℕ} (hI : I ⊆ Icc 1 N)
    (hcard : N ≤ #I + s) : N / n - s ≤ #{i ∈ I | n ∣ y + i} := by
  have hfull := div_le_card_filter_dvd N n y
  have hsplit : #{i ∈ Icc 1 N | n ∣ y + i} ≤ #{i ∈ I | n ∣ y + i} + #(Icc 1 N \ I) := by
    calc #{i ∈ Icc 1 N | n ∣ y + i}
        ≤ #({i ∈ I | n ∣ y + i} ∪ (Icc 1 N \ I)) := by
          refine card_le_card fun i hi => ?_
          simp only [mem_filter] at hi
          by_cases hiI : i ∈ I
          · exact mem_union_left _ (mem_filter.mpr ⟨hiI, hi.2⟩)
          · exact mem_union_right _ (mem_sdiff.mpr ⟨hi.1, hiI⟩)
      _ ≤ _ := card_union_le _ _
  have hcompl : #(Icc 1 N \ I) ≤ s := by
    rw [card_sdiff_of_subset hI, Nat.card_Icc]
    omega
  omega

/-- The valuation of a positive integer bounds the number of prime powers with the same base that
divide it. -/
theorem card_filter_primePow_dvd_le {N p x : ℕ} (hp : p.Prime) (hx : x ≠ 0) :
    #{n ∈ Icc 1 N | (IsPrimePow n ∧ n.minFac = p) ∧ n ∣ x} ≤ x.factorization p := by
  have hsub : {n ∈ Icc 1 N | (IsPrimePow n ∧ n.minFac = p) ∧ n ∣ x} ⊆
      (Icc 1 (x.factorization p)).image (fun a => p ^ a) := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨-, ⟨hpp, hmin⟩, hdvd⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hqp : q = p := by rw [← hmin, hq.pow_minFac hk.ne']
    subst hqp
    refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    exact (hq.pow_dvd_iff_le_factorization hx).mp hdvd
  calc #{n ∈ Icc 1 N | (IsPrimePow n ∧ n.minFac = p) ∧ n ∣ x}
      ≤ #((Icc 1 (x.factorization p)).image (fun a => p ^ a)) := card_le_card hsub
    _ ≤ #(Icc 1 (x.factorization p)) := card_image_le
    _ = x.factorization p := by simp

/-- **Fel'dman's divisibility.**  Deleting at most `s` members of a block of `N` consecutive
positive integers leaves a product divisible by `D(N, s)`. -/
theorem feldmanDivisor_dvd_prod {N s : ℕ} (y : ℕ) {I : Finset ℕ} (hI : I ⊆ Icc 1 N)
    (hcard : N ≤ #I + s) : feldmanDivisor N s ∣ ∏ i ∈ I, (y + i) := by
  have hI0 : ∀ i ∈ I, 1 ≤ i := fun i hi => (mem_Icc.mp (hI hi)).1
  have hprod0 : ∏ i ∈ I, (y + i) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i hi => by have := hI0 i hi; omega
  rw [← Nat.factorization_le_iff_dvd (feldmanDivisor_pos N s).ne' hprod0]
  intro p
  rw [feldmanDivisor, Nat.factorization_prod (fun n _ => pow_ne_zero _ (primePowBase_pos n).ne'),
    Nat.factorization_prod (fun i hi => by have := hI0 i hi; omega)]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, factorization_primePowBase]
  by_cases hp : p.Prime
  · calc ∑ n ∈ Icc 1 N, (N / n - s) * (if IsPrimePow n ∧ n.minFac = p then 1 else 0)
        = ∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac = p, (N / n - s) := by
          rw [sum_filter]
          refine sum_congr rfl fun n _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac = p, #{i ∈ I | n ∣ y + i} :=
          sum_le_sum fun n _ => div_sub_le_card_filter_dvd hI hcard
      _ = ∑ i ∈ I, #{n ∈ Icc 1 N | (IsPrimePow n ∧ n.minFac = p) ∧ n ∣ y + i} := by
          have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := (Icc 1 N).filter (fun n : ℕ => IsPrimePow n ∧ n.minFac = p)) (t := I)
            (r := fun n i : ℕ => n ∣ y + i)
          simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, filter_filter] at hdc
          exact hdc
      _ ≤ ∑ i ∈ I, (y + i).factorization p :=
          sum_le_sum fun i hi => card_filter_primePow_dvd_le hp (by have := hI0 i hi; omega)
  · have hzero : ∀ n : ℕ, ¬ (IsPrimePow n ∧ n.minFac = p) := by
      rintro n ⟨hpp, hmin⟩
      exact hp (hmin ▸ Nat.minFac_prime hpp.ne_one)
    simp [hzero]

/-! ## Size -/

/-- The logarithmic defect of Fel'dman's divisor is a weighted Chebyshev sum. -/
theorem log_factorial_sub_log_feldmanDivisor (N s : ℕ) :
    Real.log (N.factorial : ℝ) - Real.log (feldmanDivisor N s) =
      ∑ n ∈ Icc 1 N, ((min (N / n) s : ℕ) : ℝ) * Λ n := by
  rw [log_factorial_eq_sum_vonMangoldt, log_feldmanDivisor, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [← sub_mul, ← Nat.sub_sub_eq_min, Nat.cast_sub (Nat.sub_le _ _)]

/-- Chebyshev's bound for the initial segment `n ≤ ⌊N/2^J⌋`. -/
theorem sum_vonMangoldt_le_of_pow_mul_le (N J : ℕ) :
    ∑ n ∈ Icc 1 N with 2 ^ J * n ≤ N, Λ n ≤ (Real.log 4 + 4) * N / 2 ^ J := by
  have hset : (Icc 1 N).filter (fun n => 2 ^ J * n ≤ N) = Icc 1 (N / 2 ^ J) := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.le_div_iff_mul_le (by positivity)).mp h2
      refine ⟨⟨h1, ?_⟩, by linarith⟩
      have : n ≤ n * 2 ^ J := Nat.le_mul_of_pos_right n (by positivity)
      omega
  rw [hset]
  have hpsi : ψ ((N / 2 ^ J : ℕ) : ℝ) = ∑ n ∈ Icc 1 (N / 2 ^ J), Λ n := by
    rw [psi, Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  rw [← hpsi]
  refine (psi_le_const_mul_self (by positivity)).trans ?_
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [le_div_iff₀ (by positivity)]
  exact_mod_cast Nat.div_mul_le_self N (2 ^ J)

/-- The tail beyond `⌊N/2^J⌋` carries at most `2 (log 4 + 4) N J`. -/
theorem sum_div_mul_vonMangoldt_tail_le (N J : ℕ) :
    ∑ n ∈ Icc 1 N with N < 2 ^ J * n, ((N / n : ℕ) : ℝ) * Λ n ≤
      2 * (Real.log 4 + 4) * N * J := by
  induction J with
  | zero =>
      have hempty : (Icc 1 N).filter (fun n => N < 2 ^ 0 * n) = ∅ := by
        ext n
        simp only [mem_filter, mem_Icc, pow_zero, one_mul, notMem_empty, iff_false, not_and,
          not_lt]
        intro h
        exact h.2
      rw [hempty, sum_empty]
      simp
  | succ J ih =>
      have hsplit : ∑ n ∈ Icc 1 N with N < 2 ^ (J + 1) * n, ((N / n : ℕ) : ℝ) * Λ n =
          ∑ n ∈ Icc 1 N with N < 2 ^ J * n, ((N / n : ℕ) : ℝ) * Λ n +
            ∑ n ∈ Icc 1 N with (2 ^ J * n ≤ N ∧ N < 2 ^ (J + 1) * n),
              ((N / n : ℕ) : ℝ) * Λ n := by
        rw [← sum_union]
        · congr 1
          ext n
          simp only [mem_union, mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases h3 : N < 2 ^ J * n
            · exact Or.inl ⟨h1, h3⟩
            · exact Or.inr ⟨h1, not_lt.mp h3, h2⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, -, h2⟩)
            · refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
              rw [pow_succ, mul_assoc]
              exact Nat.mul_le_mul_left _ (by omega)
            · exact ⟨h1, h2⟩
        · refine Finset.disjoint_left.mpr fun n hn1 hn2 => ?_
          simp only [mem_filter] at hn1 hn2
          have h1 := hn1.2
          have h2 := hn2.2.1
          omega
      rw [hsplit]
      have hblock : ∑ n ∈ Icc 1 N with (2 ^ J * n ≤ N ∧ N < 2 ^ (J + 1) * n),
          ((N / n : ℕ) : ℝ) * Λ n ≤ 2 * (Real.log 4 + 4) * N := by
        calc ∑ n ∈ Icc 1 N with (2 ^ J * n ≤ N ∧ N < 2 ^ (J + 1) * n),
              ((N / n : ℕ) : ℝ) * Λ n
            ≤ ∑ n ∈ Icc 1 N with (2 ^ J * n ≤ N ∧ N < 2 ^ (J + 1) * n),
                (2 : ℝ) ^ (J + 1) * Λ n := by
              refine sum_le_sum fun n hn => ?_
              simp only [mem_filter, mem_Icc] at hn
              refine mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
              have : N / n < 2 ^ (J + 1) := by
                rw [Nat.div_lt_iff_lt_mul (by omega)]
                linarith [hn.2.2]
              exact_mod_cast this.le
          _ = (2 : ℝ) ^ (J + 1) *
                ∑ n ∈ Icc 1 N with (2 ^ J * n ≤ N ∧ N < 2 ^ (J + 1) * n), Λ n := by
              rw [mul_sum]
          _ ≤ (2 : ℝ) ^ (J + 1) * ∑ n ∈ Icc 1 N with 2 ^ J * n ≤ N, Λ n := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
              intro n hn
              simp only [mem_filter] at hn ⊢
              exact ⟨hn.1, hn.2.1⟩
          _ ≤ (2 : ℝ) ^ (J + 1) * ((Real.log 4 + 4) * N / 2 ^ J) :=
              mul_le_mul_of_nonneg_left (sum_vonMangoldt_le_of_pow_mul_le N J) (by positivity)
          _ = 2 * (Real.log 4 + 4) * N := by
              field_simp
              ring
      push_cast
      linarith

/-- **Size of Fel'dman's divisor.**  `log N! − log D(N, s) ≤ (log 4 + 4)(3 + 2 log₂ s) N`. -/
theorem log_factorial_sub_log_feldmanDivisor_le (N s : ℕ) :
    Real.log (N.factorial : ℝ) - Real.log (feldmanDivisor N s) ≤
      (Real.log 4 + 4) * (3 + 2 * Nat.log 2 s) * N := by
  rw [log_factorial_sub_log_feldmanDivisor]
  set J := Nat.log 2 s + 1 with hJ
  have hsJ : s < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) s
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => 2 ^ J * n ≤ N)]
  have hhead : ∑ n ∈ Icc 1 N with 2 ^ J * n ≤ N, ((min (N / n) s : ℕ) : ℝ) * Λ n ≤
      (Real.log 4 + 4) * N := by
    calc ∑ n ∈ Icc 1 N with 2 ^ J * n ≤ N, ((min (N / n) s : ℕ) : ℝ) * Λ n
        ≤ ∑ n ∈ Icc 1 N with 2 ^ J * n ≤ N, (s : ℝ) * Λ n :=
          sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right _ _)
            vonMangoldt_nonneg
      _ = (s : ℝ) * ∑ n ∈ Icc 1 N with 2 ^ J * n ≤ N, Λ n := by rw [mul_sum]
      _ ≤ (s : ℝ) * ((Real.log 4 + 4) * N / 2 ^ J) :=
          mul_le_mul_of_nonneg_left (sum_vonMangoldt_le_of_pow_mul_le N J) (by positivity)
      _ ≤ (Real.log 4 + 4) * N := by
          have hs : (s : ℝ) ≤ 2 ^ J := by exact_mod_cast hsJ.le
          have hpos : (0 : ℝ) < 2 ^ J := by positivity
          have hc : 0 ≤ (Real.log 4 + 4) * (N : ℝ) := by positivity
          calc (s : ℝ) * ((Real.log 4 + 4) * N / 2 ^ J)
              = (s : ℝ) / 2 ^ J * ((Real.log 4 + 4) * N) := by ring
            _ ≤ 1 * ((Real.log 4 + 4) * N) := by
                refine mul_le_mul_of_nonneg_right ?_ hc
                rw [div_le_one hpos]
                exact hs
            _ = (Real.log 4 + 4) * N := one_mul _
  have htail : ∑ n ∈ Icc 1 N with ¬ 2 ^ J * n ≤ N, ((min (N / n) s : ℕ) : ℝ) * Λ n ≤
      2 * (Real.log 4 + 4) * N * J := by
    calc ∑ n ∈ Icc 1 N with ¬ 2 ^ J * n ≤ N, ((min (N / n) s : ℕ) : ℝ) * Λ n
        ≤ ∑ n ∈ Icc 1 N with N < 2 ^ J * n, ((N / n : ℕ) : ℝ) * Λ n := by
          have hfilt : (Icc 1 N).filter (fun n => ¬ 2 ^ J * n ≤ N) =
              (Icc 1 N).filter (fun n => N < 2 ^ J * n) := by
            ext n
            simp only [mem_filter, not_le]
          rw [hfilt]
          exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_right
            (by exact_mod_cast min_le_left _ _) vonMangoldt_nonneg
      _ ≤ 2 * (Real.log 4 + 4) * N * J := sum_div_mul_vonMangoldt_tail_le N J
  have hJcast : (J : ℝ) = Nat.log 2 s + 1 := by rw [hJ]; push_cast; ring
  rw [hJcast] at htail
  nlinarith [hhead, htail]

end GaloisForLFunctions.RHTower.Matveev
