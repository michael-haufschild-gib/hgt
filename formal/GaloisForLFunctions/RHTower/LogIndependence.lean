/-
The two sides of the principal wall (MWM lane; 10-blind-cone.md §5).

The joint-STRONG universality theorems (Matsumoto Thm 15) require ℚ-linear independence of
the logarithms `log (n + α)` of the shifted parameters. The blind-cone analysis shows this
hypothesis is exactly where the wall for ζ lives, and that its truth value is decided by
unique factorization:

* `log_third_shifts_dependent` — for the Hurwitz pair (1/3, 2/3) the hypothesis FAILS,
  witnessed by the multiplicative relation 2·8 = 4² among integers prime to 3:
  `log (2/3) + log (8/3) = 2·log (4/3)`.
* `log_shifts_independent` — for a transcendental shift α the hypothesis HOLDS: the family
  `{log (n + α)}` admits no nontrivial ℤ-linear relation. Proof: exponentiate the relation
  to a product identity, read it as the vanishing of a rational polynomial at α, promote it
  to a polynomial identity by transcendence, and evaluate at `-n₀`.

Together: rational shifts (= the decompositions that reach ζ) are multiplicatively bound by
the fundamental theorem of arithmetic; generic shifts are free. The wall is arithmetic.
-/
import Mathlib
import GaloisForLFunctions.Hurwitz.ExpIndependence

namespace RHTower

open Polynomial Finset

/-- The explicit ℤ-relation among logs of shifted rationals with denominator 3 that
violates the joint-strong-universality independence hypothesis for the Hurwitz pair
(1/3, 2/3): `(0 + 2/3)·(2 + 2/3) = (1 + 1/3)²`, i.e. `2·8 = 4²`. -/
theorem log_third_shifts_dependent :
    Real.log (2/3) + Real.log (8/3) = 2 * Real.log (4/3) := by
  rw [← Real.log_mul (by norm_num) (by norm_num),
    show (2 : ℝ) * Real.log (4/3) = Real.log ((4/3) ^ (2:ℕ)) by rw [Real.log_pow]; norm_num]
  norm_num

/-- Transcendental shifts are multiplicatively free: for transcendental `α > 0` the
logarithms `log (n + α)`, `n ∈ ℕ`, admit no nontrivial ℤ-linear relation. This is the
independence hypothesis of joint-strong universality, which `log_third_shifts_dependent`
shows fails for the rational shifts that reach ζ. -/
theorem log_shifts_independent {α : ℝ} (h0 : 0 < α) (hα : Transcendental ℚ α)
    (s : Finset ℕ) (ε : ℕ → ℤ)
    (hrel : ∑ n ∈ s, (ε n : ℝ) * Real.log ((n : ℝ) + α) = 0) :
    ∀ n ∈ s, ε n = 0 := by
  classical
  have hx : ∀ n : ℕ, (0:ℝ) < (n : ℝ) + α := fun n => by positivity
  -- Step 1: exponentiate the relation to a product identity over ℝ.
  have hprod : (∏ n ∈ s, ((n : ℝ) + α) ^ (ε n)) = 1 := by
    have hne : ∀ n ∈ s, ((n : ℝ) + α) ^ (ε n) ≠ 0 :=
      fun n _ => zpow_ne_zero _ (hx n).ne'
    have hlog : Real.log (∏ n ∈ s, ((n : ℝ) + α) ^ (ε n)) = 0 := by
      rw [Real.log_prod hne]
      calc ∑ n ∈ s, Real.log (((n : ℝ) + α) ^ (ε n))
          = ∑ n ∈ s, (ε n : ℝ) * Real.log ((n : ℝ) + α) :=
            Finset.sum_congr rfl fun n _ => Real.log_zpow _ _
        _ = 0 := hrel
    have hpos : (0:ℝ) < ∏ n ∈ s, ((n : ℝ) + α) ^ (ε n) :=
      Finset.prod_pos fun n _ => zpow_pos (hx n) _
    calc (∏ n ∈ s, ((n : ℝ) + α) ^ (ε n))
        = Real.exp (Real.log (∏ n ∈ s, ((n : ℝ) + α) ^ (ε n))) := (Real.exp_log hpos).symm
      _ = 1 := by rw [hlog, Real.exp_zero]
  -- Step 2: split off the negative exponents — two ℕ-power products agree at α.
  have hsplit : (∏ n ∈ s.filter (fun n => 0 ≤ ε n), ((n : ℝ) + α) ^ (ε n).toNat)
      = ∏ n ∈ s.filter (fun n => ¬ 0 ≤ ε n), ((n : ℝ) + α) ^ (-ε n).toNat := by
    rw [← Finset.prod_filter_mul_prod_filter_not s (fun n => 0 ≤ ε n)] at hprod
    have h2 : (∏ n ∈ s.filter (fun n => 0 ≤ ε n), ((n : ℝ) + α) ^ (ε n))
        = ∏ n ∈ s.filter (fun n => 0 ≤ ε n), ((n : ℝ) + α) ^ (ε n).toNat :=
      Finset.prod_congr rfl fun n hn => by
        have hn0 : (0:ℤ) ≤ ε n := (Finset.mem_filter.mp hn).2
        rw [← zpow_natCast ((n : ℝ) + α) (ε n).toNat, Int.toNat_of_nonneg hn0]
    have h3 : (∏ n ∈ s.filter (fun n => ¬ 0 ≤ ε n), ((n : ℝ) + α) ^ (ε n))
        = (∏ n ∈ s.filter (fun n => ¬ 0 ≤ ε n), ((n : ℝ) + α) ^ (-ε n).toNat)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun n hn => ?_
      have hεn : ε n = -(((-ε n).toNat : ℕ) : ℤ) := by
        have := (Finset.mem_filter.mp hn).2; omega
      conv_lhs => rw [hεn]
      rw [zpow_neg, zpow_natCast]
    rw [h2, h3] at hprod
    have hNne : (∏ n ∈ s.filter (fun n => ¬ 0 ≤ ε n), ((n : ℝ) + α) ^ (-ε n).toNat) ≠ 0 :=
      (Finset.prod_pos fun n _ => pow_pos (hx n) _).ne'
    exact (mul_inv_eq_one₀ hNne).mp hprod
  -- Step 3: the same identity as vanishing of a rational polynomial at α; promote by
  -- transcendence.
  set A : ℚ[X] := ∏ n ∈ s.filter (fun n => 0 ≤ ε n), (C (n:ℚ) + X) ^ (ε n).toNat with hA_def
  set B : ℚ[X] := ∏ n ∈ s.filter (fun n => ¬ 0 ≤ ε n), (C (n:ℚ) + X) ^ (-ε n).toNat
    with hB_def
  have haevalA : (Polynomial.aeval α) A
      = ∏ n ∈ s.filter (fun n => 0 ≤ ε n), ((n : ℝ) + α) ^ (ε n).toNat := by
    rw [hA_def, map_prod]
    exact Finset.prod_congr rfl fun n _ => by
      rw [map_pow, map_add, Polynomial.aeval_C, Polynomial.aeval_X, map_natCast]
  have haevalB : (Polynomial.aeval α) B
      = ∏ n ∈ s.filter (fun n => ¬ 0 ≤ ε n), ((n : ℝ) + α) ^ (-ε n).toNat := by
    rw [hB_def, map_prod]
    exact Finset.prod_congr rfl fun n _ => by
      rw [map_pow, map_add, Polynomial.aeval_C, Polynomial.aeval_X, map_natCast]
  have hzero : (Polynomial.aeval α) (A - B) = 0 := by
    rw [map_sub, haevalA, haevalB, hsplit, sub_self]
  have hpoly : A = B := by
    by_contra hne
    exact hα ⟨A - B, sub_ne_zero.mpr hne, hzero⟩
  -- Step 4: evaluate the polynomial identity at -n₀ to kill each exponent.
  intro n₀ hn₀
  by_contra hne0
  rcases lt_or_gt_of_ne hne0 with hlt | hgt
  · -- ε n₀ < 0: the B-side vanishes at -n₀, the A-side cannot.
    have hB0 : B.eval (-(n₀:ℚ)) = 0 := by
      rw [hB_def, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hn₀, by omega⟩) ?_
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
        add_neg_cancel]
      exact zero_pow (by omega)
    have hA0 : A.eval (-(n₀:ℚ)) ≠ 0 := by
      rw [hA_def, Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.mpr fun n hn => ?_
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      refine pow_ne_zero _ ?_
      have hnn : (0:ℤ) ≤ ε n := (Finset.mem_filter.mp hn).2
      intro hcontra
      have hnq : (n:ℚ) = (n₀:ℚ) := by linarith
      have heq : n = n₀ := Nat.cast_inj.mp hnq
      subst heq
      omega
    rw [hpoly] at hA0
    exact hA0 hB0
  · -- ε n₀ > 0: the A-side vanishes at -n₀, the B-side cannot.
    have hA0 : A.eval (-(n₀:ℚ)) = 0 := by
      rw [hA_def, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hn₀, hgt.le⟩) ?_
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
        add_neg_cancel]
      exact zero_pow (by omega)
    have hB0 : B.eval (-(n₀:ℚ)) ≠ 0 := by
      rw [hB_def, Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.mpr fun n hn => ?_
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      refine pow_ne_zero _ ?_
      have hnn : ¬ (0:ℤ) ≤ ε n := (Finset.mem_filter.mp hn).2
      intro hcontra
      have hnq : (n:ℚ) = (n₀:ℚ) := by linarith
      have heq : n = n₀ := Nat.cast_inj.mp hnq
      subst heq
      omega
    rw [hpoly] at hA0
    exact hB0 hA0

/-- `padicValRat` is additive along `Finset` products of nonzero rationals. -/
private lemma padicValRat_prod {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [padicValRat.one]
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a t))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `padicValRat.pow` extended to `ℤ` exponents. -/
private lemma padicValRat_zpow {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) (n : ℤ) :
    padicValRat p (q ^ n) = n * padicValRat p q := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [zpow_natCast, padicValRat.pow hq]
  · have h1 : n = -(((-n).toNat : ℕ) : ℤ) := by omega
    conv_lhs => rw [h1]
    rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow hq]
    have h2 : (((-n).toNat : ℕ) : ℤ) = -n := by omega
    rw [h2]
    ring

/-- Prime-supported shifts are free even at RATIONAL denominator: for a prime q the
logarithms `log (p / q)` over primes `p ≠ q` admit no nontrivial ℤ-relation — the FTA
argument that kills composite support leaves prime support untouched (10-blind-cone.md
§7.2, the Beurling-design clause). -/
theorem log_prime_shifts_independent {q : ℕ} (hq : q.Prime) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ q) (ε : ℕ → ℤ)
    (hrel : ∑ p ∈ s, (ε p : ℝ) * Real.log ((p : ℝ) / q) = 0) :
    ∀ p ∈ s, ε p = 0 := by
  classical
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq.pos
  have hx : ∀ p ∈ s, (0:ℝ) < (p : ℝ) / q := fun p hp => by
    have : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hs p hp).1.pos
    positivity
  -- log (p/q) = log p − log q; the relation becomes one among logs of primes and log q.
  have hrw : ∑ p ∈ s, (ε p : ℝ) * (Real.log p - Real.log q) = 0 := by
    calc ∑ p ∈ s, (ε p : ℝ) * (Real.log p - Real.log q)
        = ∑ p ∈ s, (ε p : ℝ) * Real.log ((p : ℝ) / q) :=
          Finset.sum_congr rfl fun p hp => by
            rw [Real.log_div (by exact_mod_cast (hs p hp).1.pos.ne') (by positivity)]
      _ = 0 := hrel
  have hsum : (∑ p ∈ s, (ε p : ℝ) * Real.log p) - (∑ p ∈ s, (ε p : ℝ)) * Real.log q = 0 := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    calc ∑ p ∈ s, ((ε p : ℝ) * Real.log p - (ε p : ℝ) * Real.log q)
        = ∑ p ∈ s, (ε p : ℝ) * (Real.log p - Real.log q) :=
          Finset.sum_congr rfl fun p _ => by ring
      _ = 0 := hrw
  -- Exponentiate: ∏ p^(ε p) = q^(Σ ε p) in ℝ, all bases positive.
  have hppos : ∀ p ∈ s, (0:ℝ) < (p:ℝ) := fun p hp => by
    exact_mod_cast (hs p hp).1.pos
  have hprod : (∏ p ∈ s, (p : ℝ) ^ (ε p)) = (q : ℝ) ^ (∑ p ∈ s, ε p) := by
    have hlhs : Real.log (∏ p ∈ s, (p : ℝ) ^ (ε p)) = ∑ p ∈ s, (ε p : ℝ) * Real.log p := by
      rw [Real.log_prod (fun p hp => zpow_ne_zero _ (hppos p hp).ne')]
      exact Finset.sum_congr rfl fun p _ => Real.log_zpow _ _
    have hrhs : Real.log ((q : ℝ) ^ (∑ p ∈ s, ε p))
        = (∑ p ∈ s, (ε p : ℝ)) * Real.log q := by
      rw [Real.log_zpow]; push_cast; ring
    have hL : (0:ℝ) < ∏ p ∈ s, (p : ℝ) ^ (ε p) :=
      Finset.prod_pos fun p hp => zpow_pos (hppos p hp) _
    have hR : (0:ℝ) < (q : ℝ) ^ (∑ p ∈ s, ε p) := zpow_pos hq0 _
    have : Real.log (∏ p ∈ s, (p : ℝ) ^ (ε p)) = Real.log ((q : ℝ) ^ (∑ p ∈ s, ε p)) := by
      rw [hlhs, hrhs]; linarith [hsum]
    calc (∏ p ∈ s, (p : ℝ) ^ (ε p)) = Real.exp (Real.log (∏ p ∈ s, (p : ℝ) ^ (ε p))) :=
          (Real.exp_log hL).symm
      _ = Real.exp (Real.log ((q : ℝ) ^ (∑ p ∈ s, ε p))) := by rw [this]
      _ = (q : ℝ) ^ (∑ p ∈ s, ε p) := Real.exp_log hR
  -- Fix p₀ ∈ s with ε p₀ ≠ 0; the p₀-adic valuation of the product identity gives the
  -- contradiction with unique factorization.
  intro p₀ hp₀
  by_contra hne0
  -- move to ℚ: the same product identity holds in ℚ (all terms rational).
  have hprodQ : (∏ p ∈ s, (p : ℚ) ^ (ε p)) = (q : ℚ) ^ (∑ p ∈ s, ε p) := by
    have : ((∏ p ∈ s, (p : ℚ) ^ (ε p) : ℚ) : ℝ) = (((q : ℚ) ^ (∑ p ∈ s, ε p) : ℚ) : ℝ) := by
      push_cast
      exact hprod
    exact_mod_cast this
  -- p₀-adic valuation: LHS has valuation ε p₀ (all other bases coprime to p₀),
  -- RHS has valuation (Σ ε)·v_{p₀}(q) = 0 since q ≠ p₀ prime.
  have hp₀p : p₀.Prime := (hs p₀ hp₀).1
  haveI : Fact p₀.Prime := ⟨hp₀p⟩
  have hval := congrArg (padicValRat p₀) hprodQ
  rw [padicValRat_prod (fun p hp => zpow_ne_zero _ (by exact_mod_cast (hs p hp).1.pos.ne'))]
    at hval
  rw [padicValRat_zpow (by exact_mod_cast hq.pos.ne')] at hval
  have hvq : padicValRat p₀ (q : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd
      (fun hdvd => (hs p₀ hp₀).2 ((Nat.prime_dvd_prime_iff_eq hp₀p hq).mp hdvd))
  rw [hvq, mul_zero] at hval
  have hterm : ∀ p ∈ s, padicValRat p₀ ((p : ℚ) ^ (ε p)) = if p = p₀ then ε p else 0 := by
    intro p hp
    rw [padicValRat_zpow (by exact_mod_cast (hs p hp).1.pos.ne')]
    by_cases hpp : p = p₀
    · subst hpp
      rw [padicValRat.self (by exact_mod_cast hp₀p.one_lt), mul_one]
      simp
    · rw [padicValRat.of_nat]
      have : padicValNat p₀ p = 0 :=
        padicValNat.eq_zero_of_not_dvd
          (fun hdvd => hpp ((Nat.prime_dvd_prime_iff_eq hp₀p (hs p hp).1).mp hdvd).symm)
      rw [this]
      simp [hpp]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s p₀ ε] at hval
  simp [hp₀] at hval
  exact hne0 hval

end RHTower

namespace RHTower

open Polynomial Finset
open Complex

/-- Prime-ratio Dirichlet frequencies are analytically independent on any nonempty
open set. This feeds the RHTower prime-support arithmetic into the Hurwitz
Vandermonde exponential-independence engine. -/
theorem prime_shift_exp_packet_eq_zero_on_open {n q : ℕ} (hq : q.Prime) {p : Fin n → ℕ}
    (hp : ∀ k, (p k).Prime ∧ p k ≠ q) (hpinj : Function.Injective p)
    {c : Fin n → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hzero : ∀ z ∈ U,
      ∑ k, c k * Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * z) = 0) :
    c = 0 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hβ : Function.Injective
      (fun k : Fin n => -((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ))) := by
    intro i j hij
    have hreal : Real.log (((p i : ℝ) / (q : ℝ))) =
        Real.log (((p j : ℝ) / (q : ℝ))) := by
      have hre := congrArg Complex.re hij
      simpa using hre
    have hposi : 0 < ((p i : ℝ) / (q : ℝ)) := by
      have : (0 : ℝ) < p i := by exact_mod_cast (hp i).1.pos
      positivity
    have hposj : 0 < ((p j : ℝ) / (q : ℝ)) := by
      have : (0 : ℝ) < p j := by exact_mod_cast (hp j).1.pos
      positivity
    have hratio : ((p i : ℝ) / (q : ℝ)) = ((p j : ℝ) / (q : ℝ)) := by
      have hexp := congrArg Real.exp hreal
      simpa [Real.exp_log hposi, Real.exp_log hposj] using hexp
    have hpijR : (p i : ℝ) = (p j : ℝ) := by
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
      have hmul := congrArg (fun x : ℝ => x * (q : ℝ)) hratio
      field_simp [hqne] at hmul
      exact hmul
    exact hpinj (Nat.cast_inj.mp hpijR)
  exact HurwitzExp.expLin_eq_zero_on_open hβ hUo hUne hzero

end RHTower
