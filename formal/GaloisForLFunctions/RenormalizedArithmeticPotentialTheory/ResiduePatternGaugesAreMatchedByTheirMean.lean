import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremInResidueClassesWithItsConstant

/-!
# Residue-pattern gauges are matched by their mean

A sign pattern on the primes that depends only on `p mod q` defines a gauge: for `f : ℤ/q → {±1}`,
`ε_f(n) = Π_p f(p)^{v_p(n)}` (`primeClassGauge`). These are the Chebotarev sign patterns of the
subfields of cyclotomic fields, characters being the multiplicative patterns. This file computes
their matching coefficient and finite part.

* **The gauge** (`primeClassGauge_isSignGauge`, `primeClassGauge_prime_pow`): `ε_f` is a sign gauge
  with `ε_f(p^k) = f(p)^k`.
* **Mertens decomposition** (`gaugeMertensSum_primeClassGauge_eq`):
  `A_{ε_f}(y) = Σ_{a ∈ ℤ/q} f(a) A(y; a) + R(y)`, where `R` collects the proper prime powers, on which
  `ε_f(p^k) = f(p)^k` and `f(p^k)` may differ. `R` converges absolutely, by the bound
  `Σ_{n ≤ N, n not prime} Λ(n)/n ≤ 8 + mertensTail`.
* **The non-unit classes** (`tendsto_classMertensSum_of_not_isUnit`): they contain only prime powers
  of `p ∣ q`, and their Mertens sums converge.
* **The matching coefficient and the finite part** (`tendsto_primeClassMertensError`,
  `exists_abs_primeClassGaugeForm_finitePart_le`): with `κ_f = φ(q)^{−1} Σ_{u ∈ (ℤ/q)ˣ} f(u)`,
  `A_{ε_f}(y) − κ_f log y → α_f = Σ_u f(u) c_u + Σ_{a ∉ (ℤ/q)ˣ} f(a) ν_a + R_∞`, and on uniform step
  profiles `P_N(ε_f x) = κ_f ℓ(x)² + 2α_f |x|² + o(mass)`.

So the polar matching coefficient of an abelian Chebotarev pattern is the mean of the pattern over
the units, its density of unflipped minus flipped primes. Its finite part is the pattern applied to
the class Mertens constants of RP34, corrected at the primes dividing `q` and at the proper prime
powers.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ} {f : ZMod q → ℝ}

/-- The **residue-pattern gauge** `ε_f(n) = Π_p f(p mod q)^{v_p(n)}`. -/
def primeClassGauge (q : ℕ) (f : ZMod q → ℝ) (n : ℕ) : ℝ :=
  n.factorization.prod fun p k => f p ^ k

theorem primeClassGauge_isSignGauge (hf : ∀ a, f a * f a = 1) :
    IsSignGauge (primeClassGauge q f) := by
  refine ⟨fun {m n} hm hn => ?_, fun {n} _ => ?_⟩
  · rw [primeClassGauge, primeClassGauge, primeClassGauge, Nat.factorization_mul hm hn,
      Finsupp.prod_add_index']
    · intro p
      rw [pow_zero]
    · intro p a b
      rw [pow_add]
  · rw [primeClassGauge, ← Finsupp.prod_mul, Finsupp.prod]
    exact prod_eq_one fun p _ => by rw [← mul_pow, hf, one_pow]

theorem primeClassGauge_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeClassGauge q f (p ^ k) = f p ^ k := by
  rw [primeClassGauge, hp.factorization_pow, Finsupp.prod_single_index]
  exact pow_zero _

theorem abs_eq_one_of_mul_self {x : ℝ} (h : x * x = 1) : |x| = 1 := by
  have : |x| * |x| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg x]

/-- The correction at `t`: `(ε_f(t) − f(t))Λ(t)/t`, supported on the proper prime powers. -/
def primeClassCorrection (q : ℕ) (f : ZMod q → ℝ) (t : ℕ) : ℝ :=
  (primeClassGauge q f t - f t) * Λ t / t

theorem abs_primeClassCorrection_le (hf : ∀ a, f a * f a = 1) (t : ℕ) :
    |primeClassCorrection q f t| ≤ 2 * (RHTower.Mertens.notPrimeVonMangoldt t / t) := by
  have hnn : 0 ≤ RHTower.Mertens.notPrimeVonMangoldt t / t := by
    rw [RHTower.Mertens.notPrimeVonMangoldt]
    split_ifs
    · simp
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
  by_cases hΛ : Λ t = 0
  · rw [primeClassCorrection, hΛ, mul_zero, zero_div, abs_zero]
    positivity
  by_cases ht : t.Prime
  · rw [primeClassCorrection, show t = t ^ 1 from (pow_one t).symm, primeClassGauge_prime_pow ht,
      pow_one, pow_one, sub_self, zero_mul, zero_div, abs_zero]
    positivity
  -- a proper prime power: both signs are `±1`
  have ht0 : t ≠ 0 := fun h => hΛ (by rw [h]; simp)
  have he : |primeClassGauge q f t| = 1 :=
    abs_eq_one_of_mul_self ((primeClassGauge_isSignGauge hf).mul_self ht0)
  have hf1 : |f t| = 1 := abs_eq_one_of_mul_self (hf _)
  have hdiff : |primeClassGauge q f t - f t| ≤ 2 := by
    have := abs_sub (primeClassGauge q f t) (f t)
    linarith
  have ht' : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht0
  rw [primeClassCorrection, abs_div, abs_mul, abs_of_nonneg vonMangoldt_nonneg, abs_of_pos ht',
    RHTower.Mertens.notPrimeVonMangoldt, if_neg ht, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hdiff (div_nonneg vonMangoldt_nonneg ht'.le)

theorem sum_range_succ_eq_sum_Icc_real {g : ℕ → ℝ} (h0 : g 0 = 0) (y : ℕ) :
    ∑ n ∈ range (y + 1), g n = ∑ n ∈ Icc 1 y, g n := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos y), h0, zero_add]
  rfl

/-- The proper prime powers are absolutely summable against `1/t`. -/
theorem summable_notPrimeVonMangoldt_div :
    Summable fun t : ℕ => RHTower.Mertens.notPrimeVonMangoldt t / t := by
  have hnn : ∀ t : ℕ, 0 ≤ RHTower.Mertens.notPrimeVonMangoldt t / t := fun t => by
    rw [RHTower.Mertens.notPrimeVonMangoldt]
    split_ifs
    · simp
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
  refine summable_of_sum_range_le hnn (c := 8 + RHTower.Mertens.mertensTail) fun n => ?_
  calc ∑ t ∈ range n, RHTower.Mertens.notPrimeVonMangoldt t / t
      ≤ ∑ t ∈ range (n + 1), RHTower.Mertens.notPrimeVonMangoldt t / t :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ n))
          fun t _ _ => hnn t
    _ = ∑ t ∈ Icc 1 n, RHTower.Mertens.notPrimeVonMangoldt t / t :=
        sum_range_succ_eq_sum_Icc_real (by simp) n
    _ ≤ 8 + RHTower.Mertens.mertensTail := RHTower.Mertens.tail_bounded n

theorem summable_primeClassCorrection (hf : ∀ a, f a * f a = 1) :
    Summable (primeClassCorrection q f) :=
  Summable.of_norm_bounded (summable_notPrimeVonMangoldt_div.mul_left 2) fun t => by
    rw [Real.norm_eq_abs]
    exact abs_primeClassCorrection_le hf t

/-- The correction converges: `R(y) → R_∞ = Σ_t (ε_f(t) − f(t))Λ(t)/t`. -/
theorem tendsto_sum_primeClassCorrection (hf : ∀ a, f a * f a = 1) :
    Tendsto (fun y : ℕ => ∑ t ∈ Icc 1 y, primeClassCorrection q f t) atTop
      (𝓝 (∑' t, primeClassCorrection q f t)) := by
  have h := (summable_primeClassCorrection hf).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun y => ?_
  exact sum_range_succ_eq_sum_Icc_real (by simp [primeClassCorrection]) y

/-- **Mertens decomposition**: `A_{ε_f}(y) = Σ_{a ∈ ℤ/q} f(a) A(y; a) + R(y)`. -/
theorem gaugeMertensSum_primeClassGauge_eq [NeZero q] (y : ℕ) :
    gaugeMertensSum (primeClassGauge q f) y =
      ∑ a : ZMod q, f a * classMertensSum q a y + ∑ t ∈ Icc 1 y, primeClassCorrection q f t := by
  have hgroup : ∑ a : ZMod q, f a * classMertensSum q a y =
      ∑ t ∈ Icc 1 y, f t * Λ t / t := by
    simp only [classMertensSum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq]
    simp only [mem_univ, if_true]
    ring
  rw [hgroup, gaugeMertensSum, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [primeClassCorrection]
  ring

/-- **The non-unit classes converge**: they contain only prime powers of `p ∣ q`. -/
theorem tendsto_classMertensSum_of_not_isUnit [NeZero q] {a : ZMod q} (ha : ¬ IsUnit a) :
    Tendsto (classMertensSum q a) atTop (𝓝 (⨆ y, classMertensSum q a y)) := by
  have hterm : ∀ t : ℕ, 0 ≤ (if (t : ZMod q) = a then Λ t / t else 0) := fun t => by
    split_ifs
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
    · exact le_rfl
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun y => ?_)
    ⟨∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1), ?_⟩
  · rw [classMertensSum, classMertensSum, sum_Icc_succ_top (by omega)]
    linarith [hterm (y + 1)]
  · rintro _ ⟨y, rfl⟩
    refine le_trans (sum_le_sum fun t _ => ?_) (nonCoprimeMertens_le y)
    by_cases h1 : (t : ZMod q) = a
    · have h2 : ¬ t.Coprime q := fun h2 =>
        ha (by rw [← h1]; exact (ZMod.isUnit_iff_coprime t q).mpr h2)
      rw [if_pos h1, if_neg h2]
    · rw [if_neg h1]
      exact nonCoprimeMertens_term_nonneg q t

/-- Summing over the residues splits into the units and the non-units. -/
theorem sum_zmod_eq_units_add [NeZero q] (F : ZMod q → ℝ) :
    ∑ a : ZMod q, F a =
      ∑ u : (ZMod q)ˣ, F u + ∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a), F a := by
  have hmap : univ.filter (fun a : ZMod q => IsUnit a) =
      univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩ := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    exact ⟨fun h => ⟨h.unit, h.unit_spec⟩, fun ⟨u, hu⟩ => hu ▸ u.isUnit⟩
  rw [← sum_filter_add_sum_filter_not univ IsUnit, hmap, sum_map]
  rfl

/-- The **matching coefficient** of the pattern: `κ_f = φ(q)^{−1} Σ_{u ∈ (ℤ/q)ˣ} f(u)`. -/
def primeClassKappa (q : ℕ) [NeZero q] (f : ZMod q → ℝ) : ℝ :=
  (∑ u : (ZMod q)ˣ, f u) / q.totient

/-- The **finite-part constant** of the pattern:
`α_f = Σ_u f(u) c_u + Σ_{a ∉ (ℤ/q)ˣ} f(a) ν_a + R_∞`. -/
def primeClassAlpha (q : ℕ) [NeZero q] (f : ZMod q → ℝ) : ℝ :=
  ∑ u : (ZMod q)ˣ, f u * classMertensConstant q u +
    ∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a), f a * ⨆ y, classMertensSum q a y +
    ∑' t, primeClassCorrection q f t

/-- **The Mertens error of a residue pattern converges**: `A_{ε_f}(y) − κ_f log y → α_f`. -/
theorem tendsto_primeClassMertensError [NeZero q] (hf : ∀ a, f a * f a = 1) :
    Tendsto (gaugeMertensError (primeClassGauge q f) (primeClassKappa q f)) atTop
      (𝓝 (primeClassAlpha q f)) := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hU : Tendsto (fun y : ℕ => ∑ u : (ZMod q)ˣ, f u *
      (classMertensSum q u y - Real.log y / q.totient)) atTop
      (𝓝 (∑ u : (ZMod q)ˣ, f u * classMertensConstant q u)) :=
    tendsto_finsetSum _ fun u _ => (tendsto_classMertensSum_sub u.isUnit).const_mul _
  have hN : Tendsto (fun y : ℕ => ∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a),
      f a * classMertensSum q a y) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a),
        f a * ⨆ y, classMertensSum q a y)) :=
    tendsto_finsetSum _ fun a ha =>
      (tendsto_classMertensSum_of_not_isUnit (mem_filter.mp ha).2).const_mul _
  rw [primeClassAlpha]
  refine ((hU.add hN).add (tendsto_sum_primeClassCorrection hf)).congr fun y => ?_
  rw [gaugeMertensError, gaugeMertensSum_primeClassGauge_eq, sum_zmod_eq_units_add, primeClassKappa]
  have hsplit : ∑ u : (ZMod q)ˣ, f u * (classMertensSum q u y - Real.log y / q.totient) =
      ∑ u : (ZMod q)ˣ, f u * classMertensSum q u y -
        (∑ u : (ZMod q)ˣ, f u) / q.totient * Real.log y := by
    rw [sum_div, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun u _ => by ring
  rw [hsplit]
  ring

theorem abs_primeClassKappa_le [NeZero q] (hf : ∀ a, f a * f a = 1) :
    |primeClassKappa q f| ≤ 1 := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [primeClassKappa, abs_div, abs_of_pos hφ, div_le_one hφ]
  calc |∑ u : (ZMod q)ˣ, f u| ≤ ∑ u : (ZMod q)ˣ, |f u| := abs_sum_le_sum_abs _ _
    _ = ∑ _u : (ZMod q)ˣ, (1 : ℝ) := sum_congr rfl fun u _ => abs_eq_one_of_mul_self (hf _)
    _ = q.totient := by rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul,
        mul_one]

/-- **The horizon law of a residue pattern**: for every `±1` pattern `f` on `ℤ/q` and every `η > 0`
there is `C` with `|P_N(ε_f x) − κ_f ℓ(x)² − 2α_f |x|²| ≤ Σ_{i,j} |c_i| |c_j| (η H_{min} + C)` on
uniform step profiles. -/
theorem exists_abs_primeClassGaugeForm_finitePart_le [NeZero q] (hf : ∀ a, f a * f a = 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (fun n => primeClassGauge q f n * stepProfile c M n) -
          primeClassKappa q f * polarFunctional N (stepProfile c M) ^ 2 -
          2 * primeClassAlpha q f * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) :=
  exists_abs_gaugeForm_stepProfile_finitePart_le (primeClassGauge_isSignGauge hf)
    (abs_primeClassKappa_le hf) (tendsto_primeClassMertensError hf) hη

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
