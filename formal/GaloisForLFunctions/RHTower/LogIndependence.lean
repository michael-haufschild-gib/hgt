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
import GaloisForLFunctions.RHTower.SecondMoment

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

namespace RHTower

open Polynomial Finset
open Complex Filter

/-- Prime-ratio Dirichlet frequencies are independent from any local accumulation
of zeros.  This strengthens the open-set packet theorem to the shape used by
window data: a packet that vanishes frequently in a punctured neighbourhood of
one point is identically zero, hence all coefficients vanish. -/
theorem prime_shift_exp_packet_eq_zero_of_frequently {n q : ℕ} (hq : q.Prime)
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime ∧ p k ≠ q) (hpinj : Function.Injective p)
    {c : Fin n → ℂ} {z₀ : ℂ}
    (hfreq : ∃ᶠ z in nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ,
      ∑ k, c k * Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * z) = 0) :
    c = 0 := by
  set β : Fin n → ℂ := fun k => -((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) with hβdef
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hβinj : Function.Injective β := by
    intro i j hij
    have hreal : Real.log (((p i : ℝ) / (q : ℝ))) =
        Real.log (((p j : ℝ) / (q : ℝ))) := by
      have hre := congrArg Complex.re hij
      simpa [β] using hre
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
  set g : ℂ → ℂ := fun z => ∑ k, c k * Complex.exp (β k * z) with hgdef
  have hdiff : Differentiable ℂ g := by
    rw [hgdef]
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_const _).mul
      (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hg_an : AnalyticOnNhd ℂ g Set.univ := hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hfreqg : ∃ᶠ z in nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ, g z = 0 := by
    simpa [g, β] using hfreq
  have hg0 : ∀ z, g z = 0 := fun z =>
    hg_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ z₀)
      hfreqg (Set.mem_univ z)
  have hLI := HurwitzExp.expLin_linearIndependent hβinj
  rw [Fintype.linearIndependent_iff] at hLI
  have hsum : (∑ i, c i • fun z => Complex.exp (β i * z)) = 0 := by
    funext z
    simpa [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hg0 z
  funext k
  exact hLI c hsum k

end RHTower

namespace RHTower

open Polynomial Finset
open Complex Filter Topology

/-- A finite prime-ratio Dirichlet-frequency packet cannot vanish on a nonempty
vertical interval unless every coefficient is zero.  This is the vertical-window
form of `prime_shift_exp_packet_eq_zero_of_frequently`: the interval supplies a
punctured accumulating set at its midpoint. -/
theorem prime_shift_exp_packet_eq_zero_on_vertical_interval {n q : ℕ} (hq : q.Prime)
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime ∧ p k ≠ q) (hpinj : Function.Injective p)
    {c : Fin n → ℂ} {A B : ℝ} (hAB : A < B)
    (hzero : ∀ t ∈ Set.Ioo A B,
      ∑ k, c k * Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) *
        ((t : ℂ) * Complex.I)) = 0) :
    c = 0 := by
  let τ : ℝ := (A + B) / 2
  let δ : ℝ := (B - A) / 4
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  have hτ_mem : τ ∈ Set.Ioo A B := by
    dsimp [τ]
    constructor <;> linarith
  let z₀ : ℂ := (τ : ℂ) * Complex.I
  let φ : ℕ → ℂ := fun j => (((τ + δ / ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
  have hφzero : ∀ j,
      ∑ k, c k * Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * φ j) = 0 := by
    intro j
    have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos j
    have hsmall : δ / ((j + 1 : ℕ) : ℝ) < B - τ := by
      have hden : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      have hdiv_le : δ / ((j + 1 : ℕ) : ℝ) ≤ δ := by
        nlinarith [div_le_self hδpos.le hden]
      have hδlt : δ < B - τ := by
        dsimp [τ, δ]
        linarith
      exact lt_of_le_of_lt hdiv_le hδlt
    have htmem : τ + δ / ((j + 1 : ℕ) : ℝ) ∈ Set.Ioo A B := by
      constructor
      · have : 0 < δ / ((j + 1 : ℕ) : ℝ) := div_pos hδpos hjpos
        linarith [hτ_mem.1]
      · linarith
    simpa [φ] using hzero (τ + δ / ((j + 1 : ℕ) : ℝ)) htmem
  have hφ_ne : ∀ j, φ j ∈ ({z₀} : Set ℂ)ᶜ := by
    intro j hz
    simp only [Set.mem_singleton_iff] at hz
    have hmul := congrArg (fun z : ℂ => z * (-Complex.I)) hz
    simp [φ, z₀, mul_assoc] at hmul
    rcases hmul with hδ0 | hden0
    · exact hδpos.ne' hδ0
    · have hden0R : (j : ℝ) + 1 = 0 := by
        have hre := congrArg Complex.re hden0
        norm_num at hre
        exact hre
      have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      exact (ne_of_gt hjpos) hden0R
  have hseq_real : Tendsto (fun j : ℕ => τ + δ / ((j + 1 : ℕ) : ℝ)) atTop (nhds τ) := by
    have hden : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto (fun j : ℕ => (((j + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
      hden.inv_tendsto_atTop
    have hmul : Tendsto (fun j : ℕ => δ * (((j + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
      simpa using hinv.const_mul δ
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.add hmul :
      Tendsto (fun j : ℕ => τ + δ * (((j + 1 : ℕ) : ℝ))⁻¹) atTop (nhds (τ + 0)))
  have hseq_nhds : Tendsto φ atTop (nhds z₀) := by
    have hofReal : Tendsto
        (fun j : ℕ => ((τ + δ / ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ)) atTop (nhds (τ : ℂ)) :=
      (Complex.continuous_ofReal.tendsto τ).comp hseq_real
    simpa [φ, z₀] using hofReal.mul tendsto_const_nhds
  have hseq : Tendsto φ atTop (nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hseq_nhds, Filter.Eventually.of_forall hφ_ne⟩
  have hfreq : ∃ᶠ z in nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ,
      ∑ k, c k * Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * z) = 0 :=
    hseq.frequently ((Filter.Eventually.of_forall hφzero).frequently)
  exact prime_shift_exp_packet_eq_zero_of_frequently hq hp hpinj hfreq

end RHTower

namespace RHTower

open Polynomial Finset
open Complex Filter Topology

/-- Absolute prime vertical characters are independent on any nonempty interval, once an
auxiliary prime `q` outside the packet is fixed.  Multiplication by the common mode
`q^{it}` converts the packet to the prime-ratio form handled by
`prime_shift_exp_packet_eq_zero_on_vertical_interval`. -/
theorem prime_exp_packet_eq_zero_on_vertical_interval {n q : ℕ} (hq : q.Prime)
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime ∧ p k ≠ q) (hpinj : Function.Injective p)
    {c : Fin n → ℂ} {A B : ℝ} (hAB : A < B)
    (hzero : ∀ t ∈ Set.Ioo A B,
      ∑ k, c k * Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ)) = 0) :
    c = 0 := by
  refine prime_shift_exp_packet_eq_zero_on_vertical_interval hq hp hpinj hAB ?_
  intro t ht
  set E : ℂ := Complex.exp ((t : ℂ) * Complex.I * (Real.log (q : ℝ) : ℂ)) with hE
  have hrewrite : ∀ k : Fin n,
      Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * ((t : ℂ) * Complex.I)) =
        E * Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ)) := by
    intro k
    have hp_pos : (0 : ℝ) < p k := by exact_mod_cast (hp k).1.pos
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlogratio : Real.log (((p k : ℝ) / (q : ℝ))) =
        Real.log (p k : ℝ) - Real.log (q : ℝ) := by
      rw [Real.log_div hp_pos.ne' hq_pos.ne']
    calc
      Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * ((t : ℂ) * Complex.I))
          = Complex.exp (((t : ℂ) * Complex.I * (Real.log (q : ℝ) : ℂ)) +
              (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ))) := by
            congr 1
            rw [hlogratio]
            norm_num
            ring
      _ = E * Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ)) := by
            rw [Complex.exp_add, hE]
  calc
    ∑ k, c k * Complex.exp (-((Real.log (((p k : ℝ) / (q : ℝ))) : ℂ)) * ((t : ℂ) * Complex.I))
        = ∑ k, c k * (E * Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ))) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hrewrite k]
    _ = E * ∑ k, c k * Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
    _ = E * 0 := by rw [hzero t ht]
    _ = 0 := by simp

end RHTower

namespace RHTower

open Polynomial Finset
open Complex Filter Topology

/-- Absolute prime vertical characters are independent on an interval without naming an
auxiliary prime.  Euclid's theorem supplies a prime outside the finite packet, which
then reduces the statement to `prime_exp_packet_eq_zero_on_vertical_interval`. -/
theorem prime_exp_packet_eq_zero_on_vertical_interval_no_aux {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {c : Fin n → ℂ} {A B : ℝ} (hAB : A < B)
    (hzero : ∀ t ∈ Set.Ioo A B,
      ∑ k, c k * Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ)) = 0) :
    c = 0 := by
  classical
  obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (1 + Finset.sup Finset.univ p)
  have hq_avoid : ∀ k, p k ≠ q := by
    intro k hpk
    have hle : p k ≤ Finset.sup Finset.univ p := Finset.le_sup (Finset.mem_univ k)
    have hlt : p k < q := by omega
    exact (ne_of_lt hlt) hpk
  exact prime_exp_packet_eq_zero_on_vertical_interval hqprime
    (fun k => ⟨hp k, hq_avoid k⟩) hpinj hAB hzero

/-- Coefficient recovery for a prime-supported vertical Dirichlet polynomial.  If the
`dpoly` supported on a finite injective prime packet vanishes throughout a nonempty
interval, then every coefficient on that packet is zero. -/
theorem dpoly_prime_packet_coeff_eq_zero_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B)
    (hzero : ∀ t ∈ Set.Ioo A B, dpoly a (Finset.univ.image p) t = 0) :
    ∀ k, a (p k) = 0 := by
  have hc : (fun k : Fin n => (a (p k) : ℂ)) = 0 := by
    refine prime_exp_packet_eq_zero_on_vertical_interval_no_aux hp hpinj hAB ?_
    intro t ht
    have hsum :
        (∑ k, (a (p k) : ℂ) *
          Complex.exp (-(t : ℂ) * Complex.I * (Real.log (p k : ℝ) : ℂ))) =
          dpoly a (Finset.univ.image p) t := by
      rw [dpoly]
      rw [Finset.sum_image]
      · simp [cterm]
      · intro x _ y _ hxy
        exact hpinj hxy
    rw [hsum, hzero t ht]
  intro k
  exact Complex.ofReal_injective (congrFun hc k)

/-- Nonzero prime-packet data has to show up somewhere in every nonempty vertical
interval.  This is the certificate form of
`dpoly_prime_packet_coeff_eq_zero_on_vertical_interval`: the Hurwitz independence
obstruction gives a point where the finite Dirichlet packet is visibly nonzero. -/
theorem dpoly_prime_packet_exists_ne_zero_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B)
    (hnonzero : ∃ k, a (p k) ≠ 0) :
    ∃ t ∈ Set.Ioo A B, dpoly a (Finset.univ.image p) t ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hcoeff : ∀ k, a (p k) = 0 :=
    dpoly_prime_packet_coeff_eq_zero_on_vertical_interval hp hpinj hAB hnone
  obtain ⟨k, hk⟩ := hnonzero
  exact hk (hcoeff k)

/-- Positive second-moment sample forced by nonzero prime-packet data.  The same
Hurwitz obstruction that prevents interval vanishing of the packet also gives a
point where the real cosine covariance kernel is strictly positive. -/
theorem dpoly_prime_packet_cosine_sum_pos_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B)
    (hnonzero : ∃ k, a (p k) ≠ 0) :
    ∃ t ∈ Set.Ioo A B,
      0 < ∑ m ∈ Finset.univ.image p, ∑ n ∈ Finset.univ.image p,
        a m * a n * Real.cos ((Real.log n - Real.log m) * t) := by
  obtain ⟨t, ht, hne⟩ :=
    dpoly_prime_packet_exists_ne_zero_on_vertical_interval hp hpinj hAB hnonzero
  refine ⟨t, ht, ?_⟩
  rw [← normSq_dpoly a (Finset.univ.image p) t]
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

/-- Positive covariance mass forced by nonzero prime-packet data. A packet with a
nonzero coefficient cannot hide on a vertical interval: its real covariance kernel
has strictly positive integral over the whole interval. -/
theorem dpoly_prime_packet_cosine_sum_integral_pos_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B)
    (hnonzero : ∃ k, a (p k) ≠ 0) :
    0 < ∫ t in A..B,
      ∑ m ∈ Finset.univ.image p, ∑ n ∈ Finset.univ.image p,
        a m * a n * Real.cos ((Real.log n - Real.log m) * t) := by
  refine intervalIntegral_pos_of_continuous_nonneg_of_exists_pos ?_ ?_
    (dpoly_prime_packet_cosine_sum_pos_on_vertical_interval hp hpinj hAB hnonzero)
  · apply continuous_finsetSum
    intro m _
    apply continuous_finsetSum
    intro n _
    fun_prop
  · intro t _
    rw [← normSq_dpoly a (Finset.univ.image p) t]
    exact sq_nonneg _

/-- Strict positivity of the finite interval Gram form for prime vertical
characters. The exact second-moment identity turns the positive covariance mass
into a positive `cosInt` matrix sum over the packet. -/
theorem dpoly_prime_packet_cosInt_sum_pos_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B)
    (hnonzero : ∃ k, a (p k) ≠ 0) :
    0 < ∑ m ∈ Finset.univ.image p, ∑ n ∈ Finset.univ.image p,
      a m * a n * cosInt (Real.log n - Real.log m) A (B - A) := by
  have hpos :=
    dpoly_prime_packet_cosine_sum_integral_pos_on_vertical_interval hp hpinj hAB hnonzero
  have hpos_norm : 0 < ∫ t in A..B, ‖dpoly a (Finset.univ.image p) t‖ ^ 2 := by
    rwa [← intervalIntegral.integral_congr
      (fun t _ => normSq_dpoly a (Finset.univ.image p) t)] at hpos
  have hmoment := secondMoment_eq a (Finset.univ.image p) A (B - A)
  have hendpoint : A + (B - A) = B := by ring
  rw [hendpoint] at hmoment
  rwa [hmoment] at hpos_norm

end RHTower

namespace RHTower

open Finset

/-- The finite prime-log `cosInt` Gram form is positive definite on every nonempty
vertical interval: it vanishes exactly when all packet coefficients vanish. -/
theorem dpoly_prime_packet_cosInt_sum_eq_zero_iff_coeff_eq_zero_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∑ m ∈ Finset.univ.image p, ∑ n ∈ Finset.univ.image p,
      a m * a n * cosInt (Real.log n - Real.log m) A (B - A)) = 0 ↔
      ∀ k, a (p k) = 0 := by
  constructor
  · intro hsum
    by_contra hnot
    push Not at hnot
    have hpos := dpoly_prime_packet_cosInt_sum_pos_on_vertical_interval hp hpinj hAB hnot
    linarith
  · intro hzero
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨k, -, rfl⟩
    apply Finset.sum_eq_zero
    intro q _
    rw [hzero k]
    ring

end RHTower

namespace RHTower

/-- The prime-packet interval `L²` mass is positive exactly when the packet has a
nonzero coefficient.  This is the analytic-observable form of the Hurwitz-backed
positive definite Gram criterion. -/
theorem dpoly_prime_packet_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    0 < ∫ t in A..B, ‖dpoly a (Finset.univ.image p) t‖ ^ 2 ↔
      ∃ k, a (p k) ≠ 0 := by
  have hmoment := secondMoment_eq a (Finset.univ.image p) A (B - A)
  have hendpoint : A + (B - A) = B := by ring
  rw [hendpoint] at hmoment
  constructor
  · intro hpos
    by_contra hnone
    push Not at hnone
    have hgramzero :=
      (dpoly_prime_packet_cosInt_sum_eq_zero_iff_coeff_eq_zero_on_vertical_interval hp hpinj hAB).mpr
        hnone
    rw [hmoment, hgramzero] at hpos
    exact lt_irrefl _ hpos
  · intro hnonzero
    have hgrampos := dpoly_prime_packet_cosInt_sum_pos_on_vertical_interval hp hpinj hAB hnonzero
    rwa [hmoment]

end RHTower

namespace RHTower

/-- Exact interval-zero criterion for finite prime packets.  A prime-supported
vertical Dirichlet polynomial vanishes throughout a nonempty interval exactly when
all coefficients on the packet vanish. -/
theorem dpoly_prime_packet_eq_zero_on_vertical_interval_iff_coeff_eq_zero {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∀ t ∈ Set.Ioo A B, dpoly a (Finset.univ.image p) t = 0) ↔
      ∀ k, a (p k) = 0 := by
  constructor
  · exact dpoly_prime_packet_coeff_eq_zero_on_vertical_interval hp hpinj hAB
  · intro hcoeff t _ht
    rw [dpoly]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨k, _, rfl⟩
    unfold cterm
    rw [hcoeff k]
    simp

end RHTower

namespace RHTower

/-- Exact interval `L²` zero criterion for finite injective prime packets.  The
second-moment observable vanishes on a nonempty vertical interval exactly when every
coefficient in the prime packet is zero. -/
theorem dpoly_prime_packet_secondMoment_eq_zero_iff_coeff_eq_zero_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∫ t in A..B, ‖dpoly a (Finset.univ.image p) t‖ ^ 2) = 0 ↔
      ∀ k, a (p k) = 0 := by
  have hmoment := secondMoment_eq a (Finset.univ.image p) A (B - A)
  have hendpoint : A + (B - A) = B := by ring
  rw [hendpoint] at hmoment
  constructor
  · intro hzero
    by_contra hcoeff
    push Not at hcoeff
    have hpos :=
      (dpoly_prime_packet_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval
        hp hpinj hAB).mpr hcoeff
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  · intro hcoeff
    have hgramzero :=
      (dpoly_prime_packet_cosInt_sum_eq_zero_iff_coeff_eq_zero_on_vertical_interval hp hpinj hAB).mpr
        hcoeff
    rw [hmoment, hgramzero]

end RHTower

namespace RHTower

/-- Zero second-moment mass and pointwise interval vanishing are the same finite
prime-packet constraint.  The coefficient criterion is internal: callers can pass
between the observable `L²` certificate and the vertical-window identity directly. -/
theorem dpoly_prime_packet_secondMoment_eq_zero_iff_eq_zero_on_vertical_interval {n : ℕ}
    {p : Fin n → ℕ} (hp : ∀ k, (p k).Prime) (hpinj : Function.Injective p)
    {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∫ t in A..B, ‖dpoly a (Finset.univ.image p) t‖ ^ 2) = 0 ↔
      ∀ t ∈ Set.Ioo A B, dpoly a (Finset.univ.image p) t = 0 := by
  rw [dpoly_prime_packet_secondMoment_eq_zero_iff_coeff_eq_zero_on_vertical_interval hp hpinj hAB,
    dpoly_prime_packet_eq_zero_on_vertical_interval_iff_coeff_eq_zero hp hpinj hAB]

end RHTower

namespace RHTower

open Finset

/-- Finset-facing prime-packet interval-zero criterion. A Dirichlet packet supported
on a finite set of primes vanishes throughout a nonempty vertical interval exactly
when every coefficient on that finite set vanishes. -/
theorem dpoly_prime_finset_eq_zero_on_vertical_interval_iff_coeff_eq_zero
    (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∀ t ∈ Set.Ioo A B, dpoly a s t = 0) ↔ ∀ p ∈ s, a p = 0 := by
  classical
  let enum : Fin s.card → ℕ := fun i => ((s.equivFin.symm i).1 : ℕ)
  have henum_image : Finset.univ.image enum = s := by
    ext n
    constructor
    · intro hn
      rw [Finset.mem_image] at hn
      rcases hn with ⟨i, _hi, hni⟩
      rw [← hni]
      exact (s.equivFin.symm i).2
    · intro hn
      refine Finset.mem_image.mpr ?_
      let x : {n // n ∈ s} := ⟨n, hn⟩
      refine ⟨s.equivFin x, Finset.mem_univ _, ?_⟩
      simp [enum, x]
  have hprime : ∀ k, (enum k).Prime := fun k => hp (enum k) (by
    change ((s.equivFin.symm k).1 : ℕ) ∈ s
    exact (s.equivFin.symm k).2)
  have hinj : Function.Injective enum := by
    intro i j hij
    have hsub : s.equivFin.symm i = s.equivFin.symm j := Subtype.ext hij
    exact s.equivFin.symm.injective hsub
  constructor
  · intro hzero p hpmem
    have hcoeff : ∀ k, a (enum k) = 0 :=
      dpoly_prime_packet_coeff_eq_zero_on_vertical_interval hprime hinj hAB (by
        intro t ht
        rw [henum_image]
        exact hzero t ht)
    let x : {n // n ∈ s} := ⟨p, hpmem⟩
    simpa [enum, x] using hcoeff (s.equivFin x)
  · intro hcoeff t _ht
    rw [dpoly]
    apply Finset.sum_eq_zero
    intro p hpmem
    unfold cterm
    rw [hcoeff p hpmem]
    simp

/-- Finset-facing second-moment zero criterion for prime packets. The interval `L²`
observable vanishes exactly when the finite prime packet vanishes pointwise on the
same vertical interval. -/
theorem dpoly_prime_finset_secondMoment_eq_zero_iff_eq_zero_on_vertical_interval
    (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∫ t in A..B, ‖dpoly a s t‖ ^ 2) = 0 ↔
      ∀ t ∈ Set.Ioo A B, dpoly a s t = 0 := by
  classical
  let enum : Fin s.card → ℕ := fun i => ((s.equivFin.symm i).1 : ℕ)
  have henum_image : Finset.univ.image enum = s := by
    ext n
    constructor
    · intro hn
      rw [Finset.mem_image] at hn
      rcases hn with ⟨i, _hi, hni⟩
      rw [← hni]
      exact (s.equivFin.symm i).2
    · intro hn
      refine Finset.mem_image.mpr ?_
      let x : {n // n ∈ s} := ⟨n, hn⟩
      refine ⟨s.equivFin x, Finset.mem_univ _, ?_⟩
      simp [enum, x]
  have hprime : ∀ k, (enum k).Prime := fun k => hp (enum k) (by
    change ((s.equivFin.symm k).1 : ℕ) ∈ s
    exact (s.equivFin.symm k).2)
  have hinj : Function.Injective enum := by
    intro i j hij
    have hsub : s.equivFin.symm i = s.equivFin.symm j := Subtype.ext hij
    exact s.equivFin.symm.injective hsub
  rw [← henum_image]
  exact dpoly_prime_packet_secondMoment_eq_zero_iff_eq_zero_on_vertical_interval hprime hinj hAB

end RHTower

namespace RHTower

open Finset

/-- Finset-facing second-moment coefficient-zero criterion for finite prime support.
The interval `L²` observable vanishes exactly when every coefficient on the finite
prime set vanishes. -/
theorem dpoly_prime_finset_secondMoment_eq_zero_iff_coeff_eq_zero_on_vertical_interval
    (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∫ t in A..B, ‖dpoly a s t‖ ^ 2) = 0 ↔ ∀ p ∈ s, a p = 0 := by
  rw [dpoly_prime_finset_secondMoment_eq_zero_iff_eq_zero_on_vertical_interval s hp hAB,
    dpoly_prime_finset_eq_zero_on_vertical_interval_iff_coeff_eq_zero s hp hAB]

/-- Finset-facing positive second-moment criterion for finite prime support.  A
finite prime packet has positive interval `L²` mass exactly when one coefficient on
its support is nonzero. -/
theorem dpoly_prime_finset_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval
    (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) {a : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    0 < ∫ t in A..B, ‖dpoly a s t‖ ^ 2 ↔ ∃ p ∈ s, a p ≠ 0 := by
  classical
  let enum : Fin s.card → ℕ := fun i => ((s.equivFin.symm i).1 : ℕ)
  have henum_image : Finset.univ.image enum = s := by
    ext n
    constructor
    · intro hn
      rw [Finset.mem_image] at hn
      rcases hn with ⟨i, _hi, hni⟩
      rw [← hni]
      exact (s.equivFin.symm i).2
    · intro hn
      refine Finset.mem_image.mpr ?_
      let x : {n // n ∈ s} := ⟨n, hn⟩
      refine ⟨s.equivFin x, Finset.mem_univ _, ?_⟩
      simp [enum, x]
  have hprime : ∀ k, (enum k).Prime := fun k => hp (enum k) (by
    change ((s.equivFin.symm k).1 : ℕ) ∈ s
    exact (s.equivFin.symm k).2)
  have hinj : Function.Injective enum := by
    intro i j hij
    have hsub : s.equivFin.symm i = s.equivFin.symm j := Subtype.ext hij
    exact s.equivFin.symm.injective hsub
  constructor
  · intro hpos
    have hpacket : ∃ k, a (enum k) ≠ 0 :=
      (dpoly_prime_packet_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval
        hprime hinj hAB).mp (by simpa [henum_image] using hpos)
    rcases hpacket with ⟨k, hk⟩
    exact ⟨enum k, by
      change ((s.equivFin.symm k).1 : ℕ) ∈ s
      exact (s.equivFin.symm k).2, hk⟩
  · rintro ⟨p, hpmem, hpne⟩
    let x : {n // n ∈ s} := ⟨p, hpmem⟩
    have hpacket : ∃ k, a (enum k) ≠ 0 := by
      refine ⟨s.equivFin x, ?_⟩
      simpa [enum, x] using hpne
    have hpos :=
      (dpoly_prime_packet_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval
        hprime hinj hAB).mpr hpacket
    simpa [henum_image] using hpos

end RHTower
