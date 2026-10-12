import GaloisForLFunctions.RHTower.JointAncestryRandomPhasePositivity
import GaloisForLFunctions.RHTower.JointAncestryBudgetZeroFreeLaw
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# RH is JAS positivity at the exceptional phases of dyadic prime sets

**RH side** (`riemannHypothesis_iff_dyadic_jasConstProductPositive`).  RH holds iff, for some `X`,
the level-one JAS tests with a constant vector `z ∈ ℂ` are positive on every set of primes in every
dyadic range `(y, 2y]`, `y ≥ X + 1`.  Every such set has prime budget `Σ p^{−½} < y^{½}`, which is
the RH point `λ = ½` of the budget law.

**Unconditional side** (`card_jasPhaseAggregate_re_neg_le_dyadic`).  For every set `P` of primes
in `(y, 2y]`, every `N ≥ 3` and every modulus `r`, the phase vectors `k : P → ℤ/N` at which the
level-one aggregate with `z_p = r ω^{k_p}` is negative number at most
`N^{|P|}·(W/Φ(0))²·(exp(4a² log 4/log y) − 1)`, `a = r/(1+r²) ≤ ½`.  That is a proportion
`O(1/log y)`, with no hypothesis on the zeros.  The input is the Chebyshev bound
`Σ_{y<p≤2y} 1/p ≤ 2 log 4/log y`, from `primorial n ≤ 4ⁿ`.

So on each dyadic prime set, JAS positivity is unconditional outside a set of phase vectors of
relative size `O(1/log y)`.  RH is the statement that this exceptional set contains none of the
constant vectors `z_p ≡ z`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## Chebyshev's bound on a dyadic range -/

theorem prod_coe_le_primorial {M : ℕ} (P : Finset Nat.Primes) (hP : ∀ p ∈ P, (p : ℕ) ≤ M) :
    ∏ p ∈ P, (p : ℕ) ≤ primorial M := by
  classical
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have e : ∏ p ∈ P, (p : ℕ) = ∏ n ∈ P.map ⟨fun p : Nat.Primes => (p : ℕ), hinj⟩, n := by
    rw [Finset.prod_map]; rfl
  rw [e, primorial]
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
  · intro n hn
    rw [Finset.mem_map] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hP p hp), p.2⟩
  · intro n hn _
    rw [Finset.mem_filter] at hn
    exact hn.2.one_lt.le

/-- `Σ_{p ∈ P} 1/p ≤ 2 log 4 / log y` for any set of primes in `(y, 2y]`, `y > 1`. -/
theorem sum_inv_prime_le_of_dyadic {y : ℝ} (hy : 1 < y) (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) :
    ∑ p ∈ P, 1 / ((p : ℕ) : ℝ) ≤ 2 * Real.log 4 / Real.log y := by
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  -- the cardinality, from `∏_P p ≤ primorial ⌊2y⌋ ≤ 4^{⌊2y⌋}`
  have hprod := prod_coe_le_primorial (M := ⌊2 * y⌋₊) P fun p hp =>
    Nat.le_floor (hP p hp).2
  have hprodR : ∏ p ∈ P, ((p : ℕ) : ℝ) ≤ (4 : ℝ) ^ ⌊2 * y⌋₊ := by
    have := (hprod.trans (primorial_le_four_pow _))
    exact_mod_cast this
  have hpos : ∀ p ∈ P, ((p : ℕ) : ℝ) ≠ 0 := fun p _ => by
    have := p.2.pos; positivity
  have hlog : ∑ p ∈ P, Real.log ((p : ℕ) : ℝ) ≤ ⌊2 * y⌋₊ * Real.log 4 := by
    rw [← Real.log_prod hpos, ← Real.log_pow]
    exact Real.log_le_log (Finset.prod_pos fun p _ => by have := p.2.pos; positivity) hprodR
  have hcard : (P.card : ℝ) * Real.log y ≤ 2 * y * Real.log 4 := by
    have h1 : (P.card : ℝ) * Real.log y ≤ ∑ p ∈ P, Real.log ((p : ℕ) : ℝ) := by
      rw [show (P.card : ℝ) * Real.log y = ∑ _p ∈ P, Real.log y by
        rw [Finset.sum_const, nsmul_eq_mul]]
      exact Finset.sum_le_sum fun p hp => Real.log_le_log hy0 (hP p hp).1.le
    have h2 : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le (by positivity)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hsum : ∑ p ∈ P, 1 / ((p : ℕ) : ℝ) ≤ P.card * (1 / y) := by
    rw [show (P.card : ℝ) * (1 / y) = ∑ _p ∈ P, 1 / y by rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun p hp =>
      one_div_le_one_div_of_le hy0 (hP p hp).1.le
  refine hsum.trans ?_
  rw [le_div_iff₀ hly]
  calc (P.card : ℝ) * (1 / y) * Real.log y = (P.card * Real.log y) / y := by ring
    _ ≤ (2 * y * Real.log 4) / y := div_le_div_of_nonneg_right hcard hy0.le
    _ = 2 * Real.log 4 := by field_simp

/-! ## The unconditional side on dyadic prime sets -/

/-- **Almost every phase vector is positive on a dyadic prime set.**  At level one, on any set `P`
of primes in `(y, 2y]`, at most `N^{|P|}(W/Φ(0))²(exp(4a² log 4/log y) − 1)` of the phase vectors
give a negative aggregate. -/
theorem card_jasPhaseAggregate_re_neg_le_dyadic {r : ℝ} (hr : 0 ≤ r) {N : ℕ} (hN : 3 ≤ N)
    {y : ℝ} (hy : 1 < y) (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) :
    ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) ≤
      (N : ℝ) ^ P.card * (lagWeightTotal / poleSharpConstant) ^ 2 *
        (Real.exp (4 * (r / (1 + r ^ 2)) ^ 2 * Real.log 4 / Real.log y) - 1) := by
  refine (card_jasPhaseAggregate_re_neg_le 1 hr hN P).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  rw [← hadef]
  have hterm : ∀ p ∈ P, 2 * a ^ 2 * Real.exp ((1 - 2 * 1) * Real.log ((p : ℕ) : ℝ)) =
      2 * a ^ 2 * (1 / ((p : ℕ) : ℝ)) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
    rw [show (1 - 2 * 1 : ℝ) * Real.log ((p : ℕ) : ℝ) = -Real.log ((p : ℕ) : ℝ) by ring,
      Real.exp_neg, Real.exp_log hp0, one_div]
  rw [Finset.prod_congr rfl fun p hp => by rw [hterm p hp]]
  have h1 := GaloisForLFunctions.HTGeometry.prod_one_add_le_exp_sum P (fun p => 2 * a ^ 2 * (1 / ((p : ℕ) : ℝ)))
    (fun p _ => by have := p.2.pos; positivity)
  have h2 : ∑ p ∈ P, 2 * a ^ 2 * (1 / ((p : ℕ) : ℝ)) ≤ 4 * a ^ 2 * Real.log 4 / Real.log y := by
    rw [← Finset.mul_sum]
    have := sum_inv_prime_le_of_dyadic hy P hP
    have ha : 0 ≤ 2 * a ^ 2 := by positivity
    calc 2 * a ^ 2 * ∑ p ∈ P, 1 / ((p : ℕ) : ℝ) ≤ 2 * a ^ 2 * (2 * Real.log 4 / Real.log y) :=
          mul_le_mul_of_nonneg_left this ha
      _ = 4 * a ^ 2 * Real.log 4 / Real.log y := by ring
  linarith [Real.exp_le_exp.mpr h2]

/-! ## The RH side -/

/-- **RH ⟺ constant-vector JAS positivity on every dyadic prime set.** -/
theorem riemannHypothesis_iff_dyadic_jasConstProductPositive :
    RiemannHypothesis ↔ ∃ X : ℕ, ∀ (y : ℝ) (P : Finset Nat.Primes), (X : ℝ) + 1 ≤ y →
      (∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) → JasConstProductPositiveOn P 1 := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_one.mp hRH
    refine ⟨X, fun y P hy hP => hX.constOn fun p hp => ?_⟩
    have : (X : ℝ) < ((p : ℕ) : ℝ) := by linarith [(hP p hp).1]
    exact_mod_cast this
  · rintro ⟨X, h⟩
    exact riemannHypothesis_iff_exists_jasBudgetProductPositive_half.mpr
      ⟨X, fun y P hy hP _ => h y P hy hP⟩

end

end RHTower
