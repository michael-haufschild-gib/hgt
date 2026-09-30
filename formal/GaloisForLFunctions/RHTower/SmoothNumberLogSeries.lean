import Mathlib

/-!
# Logarithmic series over `P`-smooth numbers

Let `P` be a finite set of primes, `r = #P`, and call `n ≥ 2` `P`-smooth if all its prime factors
lie in `P`. Then `log n = Σ_{p∈P} v_p(n) log p` (`log_eq_sum_factorization`), and since each factor
`1 + v_p(n) log p` is at most `1 + log n`,

`(1 + log n)^{−2r} ≤ Π_{p∈P} (1 + v_p(n) log p)^{−2}`.

The map `n ↦ (v_p(n))_{p∈P}` is injective on `P`-smooth numbers, so any finite partial sum is
bounded by the product of the one-dimensional series `Σ_k (1 + k log p)^{−2}`
(`summable_smoothLogSeries`): `Σ_{n P-smooth} (1 + log n)^{−2r} < ∞`.
-/

namespace RHTower.SmoothNumbers

open Finset

/-- `n ≥ 2` and every prime factor of `n` lies in `P`. -/
def IsSmoothOver (P : Finset ℕ) (n : ℕ) : Prop := 2 ≤ n ∧ n.primeFactors ⊆ P

instance (P : Finset ℕ) : DecidablePred (IsSmoothOver P) := fun n =>
  inferInstanceAs (Decidable (2 ≤ n ∧ n.primeFactors ⊆ P))

theorem log_eq_sum_factorization {P : Finset ℕ} {n : ℕ} (hn : n.primeFactors ⊆ P) :
    Real.log n = ∑ p ∈ P, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  exact Finsupp.sum_of_support_subset _ (by rwa [Nat.support_factorization]) _
    (fun p _ => by simp)

theorem factorization_eq_zero_of_notMem {P : Finset ℕ} {n p : ℕ} (hn : n.primeFactors ⊆ P)
    (hp : p ∉ P) : n.factorization p = 0 := by
  rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
  exact fun h => hp (hn h)

/-- The one-dimensional weight `(1 + k log p)^{−2}`. -/
noncomputable def primeLogWeight (p k : ℕ) : ℝ := ((1 + (k : ℝ) * Real.log p) ^ 2)⁻¹

theorem primeLogWeight_nonneg {p : ℕ} (hp : 1 ≤ p) (k : ℕ) : 0 ≤ primeLogWeight p k := by
  unfold primeLogWeight
  have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  positivity

theorem summable_primeLogWeight {p : ℕ} (hp : p.Prime) : Summable (primeLogWeight p) := by
  have hc : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  set m : ℝ := min 1 (Real.log p) with hm
  have hm0 : 0 < m := lt_min one_pos hc
  have hs : Summable (fun k : ℕ => (m ^ 2)⁻¹ * (((k : ℝ) + 1) ^ 2)⁻¹) := by
    have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    exact (by simpa [Function.comp_def] using h :
      Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹)).mul_left _
  refine Summable.of_nonneg_of_le (primeLogWeight_nonneg hp.one_lt.le) (fun k => ?_) hs
  unfold primeLogWeight
  have h1 : m * ((k : ℝ) + 1) ≤ 1 + k * Real.log p := by
    have e1 := min_le_left 1 (Real.log p)
    have e2 := min_le_right 1 (Real.log p)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  rw [← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 2)

/-- **Smooth numbers carry a convergent logarithmic series**: `Σ_{n P-smooth} (1 + log n)^{−2r}`. -/
theorem summable_smoothLogSeries {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Summable (fun n : ℕ => if IsSmoothOver P n then ((1 + Real.log n) ^ (2 * P.card))⁻¹ else 0) := by
  classical
  set w : P → ℕ → ℝ := fun p k => primeLogWeight p k with hw
  have hw0 : ∀ p : P, ∀ k, 0 ≤ w p k := fun p k => primeLogWeight_nonneg (hP p p.2).one_lt.le k
  have hws : ∀ p : P, Summable (w p) := fun p => summable_primeLogWeight (hP p p.2)
  set vec : ℕ → (P → ℕ) := fun n p => n.factorization p with hvec
  have hpt : ∀ n, IsSmoothOver P n →
      ((1 + Real.log n) ^ (2 * P.card))⁻¹ ≤ ∏ p : P, w p (vec n p) := by
    intro n hn
    set x : P → ℝ := fun p => (n.factorization p : ℝ) * Real.log p with hx
    have hx0 : ∀ p, 0 ≤ x p := fun p => mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (hP p p.2).one_lt.le))
    have hlog : Real.log n = ∑ p : P, x p := by
      rw [log_eq_sum_factorization hn.2, ← Finset.sum_coe_sort]
    have hle : ∀ p : P, (1 + x p) ^ 2 ≤ (1 + Real.log n) ^ 2 := by
      intro p
      rw [hlog]
      have : x p ≤ ∑ q : P, x q :=
        Finset.single_le_sum (fun q _ => hx0 q) (Finset.mem_univ p)
      exact pow_le_pow_left₀ (by linarith [hx0 p]) (by linarith) 2
    have hprod : ∏ p : P, (1 + x p) ^ 2 ≤ (1 + Real.log n) ^ (2 * P.card) := by
      calc ∏ p : P, (1 + x p) ^ 2 ≤ ∏ _p : P, (1 + Real.log n) ^ 2 :=
            Finset.prod_le_prod (fun p _ => by have := hx0 p; positivity) (fun p _ => hle p)
        _ = (1 + Real.log n) ^ (2 * P.card) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
    have hpos : 0 < ∏ p : P, (1 + x p) ^ 2 :=
      Finset.prod_pos fun p _ => by have := hx0 p; positivity
    calc ((1 + Real.log n) ^ (2 * P.card))⁻¹ ≤ (∏ p : P, (1 + x p) ^ 2)⁻¹ :=
          inv_anti₀ hpos hprod
      _ = ∏ p : P, w p (vec n p) := by
          rw [← Finset.prod_inv_distrib]
          rfl
  have hinj : Set.InjOn vec {n | IsSmoothOver P n} := by
    intro n hn m hm he
    refine Nat.eq_of_factorization_eq (by have := hn.1; omega) (by have := hm.1; omega)
      fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun he ⟨p, hp⟩
    · rw [factorization_eq_zero_of_notMem hn.2 hp, factorization_eq_zero_of_notMem hm.2 hp]
  refine summable_of_sum_le (c := ∏ p : P, ∑' k, w p k)
    (fun n => by dsimp only; split_ifs <;> positivity) (fun T => ?_)
  set TS := T.filter (IsSmoothOver P) with hTS
  set V := TS.image vec with hV
  calc ∑ n ∈ T, (if IsSmoothOver P n then ((1 + Real.log n) ^ (2 * P.card))⁻¹ else 0)
      = ∑ n ∈ TS, ((1 + Real.log n) ^ (2 * P.card))⁻¹ := (Finset.sum_filter _ _).symm
    _ ≤ ∑ n ∈ TS, ∏ p : P, w p (vec n p) :=
        Finset.sum_le_sum fun n hn => hpt n (Finset.mem_filter.mp hn).2
    _ = ∑ a ∈ V, ∏ p : P, w p (a p) := by
        rw [Finset.sum_image]
        intro n hn m hm he
        exact hinj (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 he
    _ ≤ ∑ a ∈ Fintype.piFinset (fun p : P => V.image (fun a => a p)), ∏ p : P, w p (a p) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.prod_nonneg fun p _ => hw0 p _)
        rw [Fintype.mem_piFinset]
        exact fun p => Finset.mem_image_of_mem _ ha
    _ = ∏ p : P, ∑ k ∈ V.image (fun a => a p), w p k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ p : P, ∑' k, w p k :=
        Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun k _ => hw0 p k)
          (fun p _ => (hws p).sum_le_tsum _ (fun k _ => hw0 p k))

end RHTower.SmoothNumbers
