import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The adjunction conjecture of the founding review: the cross-prime aggregate is a mean field

The founding review proposed, as the first conjecture of the field, an *arithmetic adjunction
formula* for the cross-prime aggregate of the comb-energy reduction,

    Σ_{p ≠ q} w_p w_q A_F(log(q/p)) = ⟨𝔗_F, 𝔗_F⟩ + Σ_p E_p(F),

with `|E_p(F)|` within the single-prime Euler envelope and `⟨𝔗_F, 𝔗_F⟩ ≤ poly(r) A_F(0) Σ_p w_p²`
for every odd test of aperture `r` (primes below the horizon `e^{2r}`, `w_p = log p/√p`). This file
decides its quantitative clause in the negative (`not_exists_polynomial_adjunction_bound`): no
polynomial `C(1 + r)^k` makes

    aggregate ≤ C(1 + r)^k A_F(0) Σ_p w_p² + (Σ_p 2 log p/(√p − 1)) A_F(0)

hold for all odd `C²` tests, because on wide odd tests the aggregate is of **mean-field order**
`e^{2r}`:

* (*mean field*, `crossAggregate_ge`) if `A(t) ≥ A(0)/4` on `|t| ≤ T` and `A ≥ −A(0)`, the aggregate
  is at least `A(0)((S² − Q)/4 − (5/4) Far_T)` with `S = Σ_p w_p ≥ θ(N)/√N`, `Q = Σ_p w_p²`, and the
  far pairs `|log(q/p)| > T` cost at most `2e^{−T/2}(1 + log N)² θ(N)` (`farPairs_le`);
* (*wide odd tests*, `wideOddTest_resonant`) for every `W ≥ 2` an odd smooth test supported in
  `[−(3W + 2), 3W + 2]` has `A_F(t) ≥ A_F(0)/4` for `|t| ≤ W/2`;
* by Chebyshev `θ(N) ≥ (log 2/2) N` eventually, so `S² ≥ (log² 2/4) N`, while the right side is
  `O(e^{r} poly(r))`.

The exponential part of the aggregate is `S² ≍ N`: the square of the mean of the prime comb, that
is, the pole of `ζ` read through the comb at PNT level. Cauchy–Schwarz loses exactly the linear
cancellation between the prime side and the pole charge, which the ledger keeps. The survivor is the
Kronecker law (`ResonatorKroneckerLaw`): the true prime self-intersection of resonators has no
cross-prime terms at all.
-/

open Finset Real Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The comb weight `w_p = log p/√p`. -/
def combWeight (p : ℕ) : ℝ := Real.log p / Real.sqrt p

theorem combWeight_nonneg (p : ℕ) : 0 ≤ combWeight p :=
  div_nonneg (Real.log_natCast_nonneg p) (Real.sqrt_nonneg _)

/-- The cross-prime aggregate `Σ_{p ≠ q ≤ N} w_p w_q A(log q − log p)`. -/
def crossAggregate (N : ℕ) (A : ℝ → ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, ∑ q ∈ (Nat.primesLE N).erase p,
    combWeight p * combWeight q * A (Real.log q - Real.log p)

/-- The comb mass `S = Σ_{p ≤ N} w_p`. -/
def combMass (N : ℕ) : ℝ := ∑ p ∈ Nat.primesLE N, combWeight p

/-- The comb diagonal `Q = Σ_{p ≤ N} w_p²`. -/
def combDiagonal (N : ℕ) : ℝ := ∑ p ∈ Nat.primesLE N, combWeight p ^ 2

/-- The Euler-envelope budget `Σ_{p ≤ N} 2 log p/(√p − 1)`. -/
def envelopeBudget (N : ℕ) : ℝ := ∑ p ∈ Nat.primesLE N, 2 * (Real.log p / (Real.sqrt p - 1))

/-- The far pairs `|log q − log p| > T`. -/
def farPairs (N : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, ∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => T < |Real.log q - Real.log p|),
    combWeight p * combWeight q

/-- The autocorrelation `A_F(t) = ∫ F(x) F(x + t)` (the `autoCorr` of the criticality theory). -/
def autoCorrelation (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * F (x + t)

/-- `|A_F(t)| ≤ A_F(0)`, from `2|ab| ≤ a² + b²` and translation invariance. -/
theorem abs_autoCorrelation_le {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (t : ℝ) : |autoCorrelation F t| ≤ autoCorrelation F 0 := by
  have hint : ∀ s : ℝ, MeasureTheory.Integrable fun x => F x * F (x + s) := fun s =>
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsq : MeasureTheory.Integrable fun x => F (x + t) * F (x + t) :=
    ((hF.comp (continuous_id.add continuous_const)).mul
      (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      ((hFc.comp_homeomorph (Homeomorph.addRight t)).mul_right)
  have htr : ∫ x, F (x + t) * F (x + t) = ∫ x, F x * F x :=
    MeasureTheory.integral_add_right_eq_self (fun x => F x * F x) t
  have h0 : autoCorrelation F 0 = ∫ x, F x * F x := by simp [autoCorrelation]
  have h00 : MeasureTheory.Integrable fun x => F x * F x :=
    (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hdom : MeasureTheory.Integrable fun x => (F x * F x + F (x + t) * F (x + t)) / 2 :=
    (h00.add hsq).div_const 2
  have hI : ∫ x, (F x * F x + F (x + t) * F (x + t)) / 2 = ∫ x, F x * F x := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add h00 hsq, htr]; ring
  have hneg : MeasureTheory.Integrable fun x => -(F x * F (x + t)) := (hint t).neg
  rw [abs_le]
  constructor
  · have := MeasureTheory.integral_mono hneg hdom fun x => by
      nlinarith [sq_nonneg (F x + F (x + t))]
    rw [MeasureTheory.integral_neg, hI] at this
    rw [h0]; simp only [autoCorrelation]; linarith
  · have := MeasureTheory.integral_mono (hint t) hdom fun x => by
      nlinarith [sq_nonneg (F x - F (x + t))]
    rw [hI] at this
    rw [h0]; simp only [autoCorrelation]; linarith

/-! ### Prime sums -/

theorem sum_inv_Icc_le (Y : ℕ) : ∑ n ∈ Finset.Icc 1 Y, ((n : ℝ))⁻¹ ≤ 1 + Real.log Y := by
  have h := harmonic_le_one_add_log Y
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  exact h

theorem sum_log_div_le (Y : ℕ) :
    ∑ p ∈ Nat.primesLE Y, Real.log p / p ≤ (1 + Real.log Y) ^ 2 := by
  have hsub : Nat.primesLE Y ⊆ Finset.Icc 1 Y := fun p hp => by
    obtain ⟨hpY, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le, hpY⟩
  have hlogY : 0 ≤ Real.log Y := Real.log_natCast_nonneg Y
  calc ∑ p ∈ Nat.primesLE Y, Real.log p / p ≤ ∑ n ∈ Finset.Icc 1 Y, Real.log n / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, Real.log Y * ((n : ℝ))⁻¹ := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by exact_mod_cast h1)
          (by exact_mod_cast h2)) (by positivity)
    _ = Real.log Y * ∑ n ∈ Finset.Icc 1 Y, ((n : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ Real.log Y * (1 + Real.log Y) := mul_le_mul_of_nonneg_left (sum_inv_Icc_le Y) hlogY
    _ ≤ (1 + Real.log Y) ^ 2 := by nlinarith

/-- `w_p ≤ (log p/p) √Y` for `p ≤ Y`. -/
theorem combWeight_le {p Y : ℕ} (hp : 1 ≤ p) (hpY : p ≤ Y) :
    combWeight p ≤ Real.log p / p * Real.sqrt Y := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  rw [combWeight, div_le_iff₀ hsp, mul_assoc]
  have : (p : ℝ) ≤ Real.sqrt Y * Real.sqrt p := by
    calc (p : ℝ) = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp0.le).symm
      _ ≤ Real.sqrt Y * Real.sqrt p := mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (by exact_mod_cast hpY)) hsp.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hp0]
  nlinarith [Real.log_natCast_nonneg p]

theorem combMass_le (Y : ℕ) : combMass Y ≤ Real.sqrt Y * (1 + Real.log Y) ^ 2 := by
  calc combMass Y ≤ ∑ p ∈ Nat.primesLE Y, Real.log p / p * Real.sqrt Y :=
        Finset.sum_le_sum fun p hp => by
          obtain ⟨hpY, hpp⟩ := Nat.mem_primesLE.mp hp
          exact combWeight_le hpp.one_lt.le hpY
    _ = Real.sqrt Y * ∑ p ∈ Nat.primesLE Y, Real.log p / p := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ Real.sqrt Y * (1 + Real.log Y) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_log_div_le Y) (Real.sqrt_nonneg _)

theorem combDiagonal_le (N : ℕ) : combDiagonal N ≤ (1 + Real.log N) ^ 3 := by
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc combDiagonal N ≤ ∑ p ∈ Nat.primesLE N, Real.log N * (Real.log p / p) :=
        Finset.sum_le_sum fun p hp => by
          obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          rw [combWeight, div_pow, Real.sq_sqrt hp0.le, sq, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (Real.log_le_log hp0 (by exact_mod_cast hpN))
            (div_nonneg (Real.log_natCast_nonneg p) hp0.le)
    _ = Real.log N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by rw [Finset.mul_sum]
    _ ≤ (1 + Real.log N) * (1 + Real.log N) ^ 2 :=
        mul_le_mul (by linarith) (sum_log_div_le N) (by positivity) (by positivity)
    _ = (1 + Real.log N) ^ 3 := by ring

/-- `S ≥ θ(N)/√N`. -/
theorem theta_div_sqrt_le_combMass {N : ℕ} (hN : 1 ≤ N) :
    Chebyshev.theta N / Real.sqrt N ≤ combMass N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [combWeight]
  exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (Real.sqrt_pos.mpr hp0)
    (Real.sqrt_le_sqrt (by exact_mod_cast hpN))

/-- The envelope budget is at most `10 S`. -/
theorem envelopeBudget_le (N : ℕ) : envelopeBudget N ≤ 10 * combMass N := by
  rw [envelopeBudget, combMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨-, hpp⟩ := Nat.mem_primesLE.mp hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hs : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt hp2
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt p := by positivity
  have hden : Real.sqrt p / 5 ≤ Real.sqrt p - 1 := by linarith
  have hlog := Real.log_natCast_nonneg p
  rw [combWeight]
  calc 2 * (Real.log p / (Real.sqrt p - 1)) ≤ 2 * (Real.log p / (Real.sqrt p / 5)) := by
        gcongr
    _ = 10 * (Real.log p / Real.sqrt p) := by field_simp; ring

/-! ### The mean-field lower bound -/

/-- The aggregate splits into near and far pairs, with the diagonal removed. -/
theorem crossAggregate_ge {N : ℕ} {T : ℝ} (hT : 0 ≤ T) {A : ℝ → ℝ} (hA0 : 0 ≤ A 0)
    (hlow : ∀ t, -A 0 ≤ A t) (hnear : ∀ t, |t| ≤ T → A 0 / 4 ≤ A t) :
    A 0 * ((combMass N ^ 2 - combDiagonal N) / 4 - 5 / 4 * farPairs N T)
      ≤ crossAggregate N A := by
  set P := Nat.primesLE N
  -- termwise: near pairs carry at least `A(0)/4`, far pairs at least `−A(0)`
  have hterm : ∀ p ∈ P, ∀ q ∈ P.erase p,
      combWeight p * combWeight q * (A 0 / 4)
        - combWeight p * combWeight q * (5 / 4 * A 0) *
          (if T < |Real.log q - Real.log p| then 1 else 0)
        ≤ combWeight p * combWeight q * A (Real.log q - Real.log p) := by
    intro p _ q _
    have hw : 0 ≤ combWeight p * combWeight q := mul_nonneg (combWeight_nonneg p) (combWeight_nonneg q)
    split_ifs with h
    · nlinarith [hlow (Real.log q - Real.log p), mul_le_mul_of_nonneg_left
        (hlow (Real.log q - Real.log p)) hw]
    · push Not at h
      nlinarith [mul_le_mul_of_nonneg_left (hnear _ h) hw]
  have hsum := Finset.sum_le_sum fun p hp => Finset.sum_le_sum (hterm p hp)
  simp only [Finset.sum_sub_distrib] at hsum
  -- the near-pair total over `q ≠ p` is `S² − Q`
  have hall : ∑ p ∈ P, ∑ q ∈ P.erase p, combWeight p * combWeight q
      = combMass N ^ 2 - combDiagonal N := by
    have : ∀ p ∈ P, ∑ q ∈ P.erase p, combWeight p * combWeight q
        = combWeight p * combMass N - combWeight p ^ 2 := by
      intro p hp
      rw [combMass, Finset.mul_sum, ← Finset.sum_erase_add _ _ hp]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul, combDiagonal, sq,
      combMass]
  have hfar : ∑ p ∈ P, ∑ q ∈ P.erase p,
      combWeight p * combWeight q * (5 / 4 * A 0) * (if T < |Real.log q - Real.log p| then 1 else 0)
        ≤ 5 / 4 * A 0 * farPairs N T := by
    rw [farPairs, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
    calc ∑ q ∈ P.erase p, combWeight p * combWeight q * (5 / 4 * A 0) *
          (if T < |Real.log q - Real.log p| then 1 else 0)
        ≤ ∑ q ∈ P, combWeight p * combWeight q * (5 / 4 * A 0) *
          (if T < |Real.log q - Real.log p| then 1 else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p P) fun q _ _ => ?_
          refine mul_nonneg (mul_nonneg (mul_nonneg (combWeight_nonneg p) (combWeight_nonneg q))
            (by positivity)) ?_
          split_ifs <;> norm_num
      _ = ∑ q ∈ P, if T < |Real.log q - Real.log p| then 5 / 4 * A 0 * (combWeight p * combWeight q)
          else 0 := Finset.sum_congr rfl fun q _ => by split_ifs <;> ring
  have hnearsum : ∑ p ∈ P, ∑ q ∈ P.erase p, combWeight p * combWeight q * (A 0 / 4)
      = A 0 / 4 * (combMass N ^ 2 - combDiagonal N) := by
    rw [← hall, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [crossAggregate]
  nlinarith [hsum, hfar, hnearsum]

/-- **The far pairs are exponentially rare**: `Far_T ≤ 2 e^{−T/2}(1 + log N)² θ(N)`. -/
theorem farPairs_le {N : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    farPairs N T ≤ 2 * Real.exp (-T / 2) * (1 + Real.log N) ^ 2 * Chebyshev.theta N := by
  set P := Nat.primesLE N
  -- split `|log q − log p| > T` into `q < p e^{−T}` and `p < q e^{−T}`
  have hsplit : farPairs N T ≤
      ∑ p ∈ P, ∑ q ∈ P.filter (fun q : ℕ => Real.log q < Real.log p - T), combWeight p * combWeight q
      + ∑ p ∈ P, ∑ q ∈ P.filter (fun q : ℕ => Real.log p < Real.log q - T), combWeight p * combWeight q := by
    rw [farPairs, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ => ?_
    have hw := mul_nonneg (combWeight_nonneg p) (combWeight_nonneg q)
    by_cases h : T < |Real.log q - Real.log p|
    · rw [if_pos h]
      rcases lt_abs.mp h with h1 | h1
      · rw [if_neg (by linarith), if_pos (by linarith)]; simp
      · rw [if_pos (by linarith)]
        split_ifs <;> linarith
    · rw [if_neg h]; split_ifs <;> linarith
  have hswap : ∑ p ∈ P, ∑ q ∈ P.filter (fun q : ℕ => Real.log p < Real.log q - T),
      combWeight p * combWeight q
        = ∑ p ∈ P, ∑ q ∈ P.filter (fun q : ℕ => Real.log q < Real.log p - T),
          combWeight p * combWeight q := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm]
  have hinner : ∀ p ∈ P, ∑ q ∈ P.filter (fun q : ℕ => Real.log q < Real.log p - T),
      combWeight p * combWeight q
        ≤ Real.exp (-T / 2) * (1 + Real.log N) ^ 2 * Real.log p := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    set Y : ℕ := ⌊(p : ℝ) * Real.exp (-T)⌋₊
    have hYsub : P.filter (fun q : ℕ => Real.log q < Real.log p - T) ⊆ Nat.primesLE Y := by
      intro q hq
      obtain ⟨hqP, hql⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hqp⟩ := Nat.mem_primesLE.mp hqP
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hle : (q : ℝ) ≤ p * Real.exp (-T) := by
        have := Real.exp_lt_exp.mpr hql
        rw [Real.exp_log hq0, Real.exp_sub, Real.exp_log hp0] at this
        rw [Real.exp_neg, ← div_eq_mul_inv]; exact this.le
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hle, hqp⟩
    have hYle : (Y : ℝ) ≤ p * Real.exp (-T) := Nat.floor_le (by positivity)
    have hYN : (Y : ℝ) ≤ N := hYle.trans (by
      have : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc (p : ℝ) * Real.exp (-T) ≤ p := by nlinarith
        _ ≤ N := by exact_mod_cast hpN)
    have hlogY : Real.log Y ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos Y with h0 | h0
      · rw [h0]; simp [Real.log_natCast_nonneg]
      · exact Real.log_le_log (by exact_mod_cast h0) hYN
    calc ∑ q ∈ P.filter (fun q : ℕ => Real.log q < Real.log p - T), combWeight p * combWeight q
        = combWeight p * ∑ q ∈ P.filter (fun q : ℕ => Real.log q < Real.log p - T), combWeight q := by
          rw [Finset.mul_sum]
      _ ≤ combWeight p * combMass Y := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hYsub fun q _ _ => combWeight_nonneg q)
          (combWeight_nonneg p)
      _ ≤ combWeight p * (Real.sqrt (p * Real.exp (-T)) * (1 + Real.log N) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ((combMass_le Y).trans ?_) (combWeight_nonneg p)
          exact mul_le_mul (Real.sqrt_le_sqrt hYle)
            (pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg _))
              (by linarith [hlogY]) 2) (by positivity) (Real.sqrt_nonneg _)
      _ = Real.exp (-T / 2) * (1 + Real.log N) ^ 2 * Real.log p := by
          rw [Real.sqrt_mul hp0.le, combWeight, show Real.exp (-T) = Real.exp (-T / 2) ^ 2 by
            rw [← Real.exp_nat_mul]; ring_nf, Real.sqrt_sq (Real.exp_pos _).le]
          field_simp
  calc farPairs N T ≤ 2 * ∑ p ∈ P, ∑ q ∈ P.filter (fun q : ℕ => Real.log q < Real.log p - T),
        combWeight p * combWeight q := by rw [hswap] at hsplit; linarith
    _ ≤ 2 * ∑ p ∈ P, Real.exp (-T / 2) * (1 + Real.log N) ^ 2 * Real.log p := by
        gcongr with p hp; exact hinner p hp
    _ = 2 * Real.exp (-T / 2) * (1 + Real.log N) ^ 2 * Chebyshev.theta N := by
        rw [← Finset.mul_sum, Chebyshev.theta_eq_sum_primesLE_log]; ring

/-! ### Chebyshev's lower bound in explicit form -/

/-- `log n ≤ 4 n^{1/4}`, through `√√n`. -/
theorem log_le_four_sqrt_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx.le]; ring
  have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (Real.sqrt x) by positivity)
  linarith

/-- **Chebyshev in explicit form**: `θ(n) ≥ (log 2/2) n` once `n ≥ 38⁴`. -/
theorem theta_ge_half_log_two {n : ℕ} (hn : (38 : ℝ) ^ 4 ≤ n) :
    Real.log 2 / 2 * n ≤ Chebyshev.theta n := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  set s := Real.sqrt (Real.sqrt (n : ℝ)) with hs
  have hs0 : 0 < s := by positivity
  have hsq : Real.sqrt (n : ℝ) = s ^ 2 := by
    rw [hs, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hn4 : (n : ℝ) = s ^ 4 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, ← hsq, Real.sq_sqrt hn0.le]
  have hs38 : (38 : ℝ) ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 4 < 38 ^ 4 := by gcongr
    linarith
  have hlog : Real.log n ≤ 4 * s := log_le_four_sqrt_sqrt hn0
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ 1 + 4 * s := by
    have h2n : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have := Real.log_le_log (by positivity) h2n
    rw [Real.log_mul (by norm_num) hn0.ne'] at this
    have hl2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith
    linarith
  have hθ := Chebyshev.theta_ge n
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h2 : 2 * Real.sqrt (n : ℝ) * Real.log n ≤ 8 * s ^ 3 := by
    rw [hsq]; nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * s ^ 2 by positivity)]
  have h3 : (38 : ℝ) * s ^ 3 ≤ s ^ 4 := by
    have := mul_le_mul_of_nonneg_right hs38 (pow_nonneg hs0.le 3)
    linarith [show s * s ^ 3 = s ^ 4 by ring]
  have h4 : 4 * s + 1 ≤ s ^ 3 := by
    have h38 : (38 : ℝ) * 38 ≤ s * s := mul_le_mul hs38 hs38 (by norm_num) hs0.le
    have : s * (s * s) = s ^ 3 := by ring
    nlinarith
  have h6 : 0.69 * s ^ 4 ≤ Real.log 2 * n := by
    rw [hn4]; exact mul_le_mul_of_nonneg_right hl2.le (by positivity)
  linarith [hθ, hlog1, h2, h3, h4, h6]

/-! ### Wide odd tests -/

/-- The plateau bump: `1` on `[−W, W]`, `0` outside `(−W − 1, W + 1)`. -/
def plateauBump (W : ℝ) (hW : 0 < W) : ContDiffBump (0 : ℝ) := ⟨W, W + 1, hW, by linarith⟩

/-- The wide odd test `F_W(x) = φ(x − c) − φ(−x − c)`, `c = 2W + 1`. -/
def wideOddTest (W : ℝ) (hW : 0 < W) (x : ℝ) : ℝ :=
  plateauBump W hW (x - (2 * W + 1)) - plateauBump W hW (-x - (2 * W + 1))

theorem plateauBump_eq_zero {W : ℝ} (hW : 0 < W) {y : ℝ} (hy : W + 1 ≤ |y|) :
    plateauBump W hW y = 0 :=
  (plateauBump W hW).zero_of_le_dist (by simpa [plateauBump, Real.dist_eq] using hy)

theorem plateauBump_eq_one {W : ℝ} (hW : 0 < W) {y : ℝ} (hy : |y| ≤ W) :
    plateauBump W hW y = 1 :=
  (plateauBump W hW).one_of_mem_closedBall (by simpa [plateauBump, Real.dist_eq] using hy)

theorem wideOddTest_odd {W : ℝ} (hW : 0 < W) (x : ℝ) :
    wideOddTest W hW (-x) = -wideOddTest W hW x := by
  simp only [wideOddTest, neg_neg]; ring

theorem wideOddTest_contDiff {W : ℝ} (hW : 0 < W) : ContDiff ℝ 2 (wideOddTest W hW) :=
  ((plateauBump W hW).contDiff.comp (contDiff_id.sub contDiff_const)).sub
    ((plateauBump W hW).contDiff.comp (contDiff_id.neg.sub contDiff_const))

/-- Outside `[−(3W + 2), 3W + 2]` the test vanishes. -/
theorem wideOddTest_eq_zero {W : ℝ} (hW : 0 < W) {x : ℝ} (hx : 3 * W + 2 < |x|) :
    wideOddTest W hW x = 0 := by
  have h1 : W + 1 ≤ |x - (2 * W + 1)| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg h] at hx; rw [abs_of_neg (by linarith)]; linarith
  have h2 : W + 1 ≤ |-x - (2 * W + 1)| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg h] at hx; rw [abs_of_pos (by linarith)]; linarith
  rw [wideOddTest, plateauBump_eq_zero hW h1, plateauBump_eq_zero hW h2, sub_self]

theorem tsupport_wideOddTest {W : ℝ} (hW : 0 < W) :
    tsupport (wideOddTest W hW) ⊆ Set.Icc (-(3 * W + 2)) (3 * W + 2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  apply wideOddTest_eq_zero hW
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h <;> push Not at h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem wideOddTest_hasCompactSupport {W : ℝ} (hW : 0 < W) : HasCompactSupport (wideOddTest W hW) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (tsupport_wideOddTest hW))

theorem abs_wideOddTest_le {W : ℝ} (hW : 0 < W) (x : ℝ) : |wideOddTest W hW x| ≤ 1 := by
  rw [wideOddTest, abs_le]
  have h1 := (plateauBump W hW).nonneg (x := x - (2 * W + 1))
  have h2 := (plateauBump W hW).le_one (x := x - (2 * W + 1))
  have h3 := (plateauBump W hW).nonneg (x := -x - (2 * W + 1))
  have h4 := (plateauBump W hW).le_one (x := -x - (2 * W + 1))
  constructor <;> linarith

/-- The test is `≥ 0` on `x ≥ 0`. -/
theorem wideOddTest_nonneg {W : ℝ} (hW : 0 < W) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ wideOddTest W hW x := by
  have h : W + 1 ≤ |-x - (2 * W + 1)| := by rw [abs_of_neg (by linarith)]; linarith
  rw [wideOddTest, plateauBump_eq_zero hW h, sub_zero]
  exact (plateauBump W hW).nonneg

/-- The test is `≤ 0` on `x ≤ 0`. -/
theorem wideOddTest_nonpos {W : ℝ} (hW : 0 < W) {x : ℝ} (hx : x ≤ 0) : wideOddTest W hW x ≤ 0 := by
  have h : W + 1 ≤ |x - (2 * W + 1)| := by rw [abs_of_neg (by linarith)]; linarith
  rw [wideOddTest, plateauBump_eq_zero hW h, zero_sub, neg_nonpos]
  exact (plateauBump W hW).nonneg

/-- The test vanishes on `[−W, W]`. -/
theorem wideOddTest_eq_zero_of_abs_le {W : ℝ} (hW : 0 < W) {x : ℝ} (hx : |x| ≤ W) :
    wideOddTest W hW x = 0 := by
  rw [abs_le] at hx
  have h1 : W + 1 ≤ |x - (2 * W + 1)| := by rw [abs_of_neg (by linarith)]; linarith
  have h2 : W + 1 ≤ |-x - (2 * W + 1)| := by rw [abs_of_neg (by linarith)]; linarith
  rw [wideOddTest, plateauBump_eq_zero hW h1, plateauBump_eq_zero hW h2, sub_self]

/-- The plateau `F = 1` on `[W + 1, 3W + 1]`. -/
theorem wideOddTest_eq_one {W : ℝ} (hW : 0 < W) {x : ℝ} (h1 : W + 1 ≤ x) (h2 : x ≤ 3 * W + 1) :
    wideOddTest W hW x = 1 := by
  have e1 : |x - (2 * W + 1)| ≤ W := by rw [abs_le]; constructor <;> linarith
  have e2 : W + 1 ≤ |-x - (2 * W + 1)| := by rw [abs_of_neg (by linarith)]; linarith
  rw [wideOddTest, plateauBump_eq_one hW e1, plateauBump_eq_zero hW e2, sub_zero]

/-- The plateau `F = −1` on `[−(3W + 1), −(W + 1)]`. -/
theorem wideOddTest_eq_neg_one {W : ℝ} (hW : 0 < W) {x : ℝ} (h1 : -(3 * W + 1) ≤ x)
    (h2 : x ≤ -(W + 1)) : wideOddTest W hW x = -1 := by
  have := wideOddTest_eq_one hW (x := -x) (by linarith) (by linarith)
  rw [wideOddTest_odd] at this; linarith

/-- For `|t| ≤ W` the product `F(x)F(x + t)` is never negative. -/
theorem wideOddTest_mul_shift_nonneg {W : ℝ} (hW : 0 < W) {t : ℝ} (ht : |t| ≤ W) (x : ℝ) :
    0 ≤ wideOddTest W hW x * wideOddTest W hW (x + t) := by
  rw [abs_le] at ht
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 (x + t) with hy | hy
  · exact mul_nonneg (wideOddTest_nonneg hW hx) (wideOddTest_nonneg hW hy)
  · rw [wideOddTest_eq_zero_of_abs_le hW (by rw [abs_le]; constructor <;> linarith), zero_mul]
  · rw [wideOddTest_eq_zero_of_abs_le hW (by rw [abs_le]; constructor <;> linarith), zero_mul]
  · exact mul_nonneg_of_nonpos_of_nonpos (wideOddTest_nonpos hW hx) (wideOddTest_nonpos hW hy)

theorem continuous_wideOddTest {W : ℝ} (hW : 0 < W) : Continuous (wideOddTest W hW) :=
  (wideOddTest_contDiff hW).continuous

theorem integrable_wideOddTest_mul_shift {W : ℝ} (hW : 0 < W) (t : ℝ) :
    MeasureTheory.Integrable fun x => wideOddTest W hW x * wideOddTest W hW (x + t) :=
  ((continuous_wideOddTest hW).mul ((continuous_wideOddTest hW).comp
    (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
    (wideOddTest_hasCompactSupport hW).mul_right

/-- **The wide odd test is resonant at short lags**: `A_F(t) ≥ 2(2W − 2|t|)` for `|t| ≤ W`. -/
theorem autoCorrelation_wideOddTest_ge {W : ℝ} (hW : 0 < W) {t : ℝ} (ht : |t| ≤ W) :
    2 * (2 * W - 2 * |t|) ≤ autoCorrelation (wideOddTest W hW) t := by
  set Jp := Set.Icc (W + 1 + |t|) (3 * W + 1 - |t|)
  set Jm := Set.Icc (-(3 * W + 1) + |t|) (-(W + 1) - |t|)
  have hdisj : Disjoint Jp Jm := by
    rw [Set.disjoint_left]; intro x h1 h2
    have := h1.1; have := h2.2; linarith [abs_nonneg t]
  have hpt : ∀ x, (Jp ∪ Jm).indicator (fun _ => (1 : ℝ)) x
      ≤ wideOddTest W hW x * wideOddTest W hW (x + t) := by
    intro x
    by_cases hx : x ∈ Jp ∪ Jm
    · rw [Set.indicator_of_mem hx]
      rcases hx with hx | hx
      · obtain ⟨h1, h2⟩ := hx
        rw [wideOddTest_eq_one hW (by linarith [abs_nonneg t]) (by linarith [abs_nonneg t]),
          wideOddTest_eq_one hW (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])]
        norm_num
      · obtain ⟨h1, h2⟩ := hx
        rw [wideOddTest_eq_neg_one hW (by linarith [abs_nonneg t]) (by linarith [abs_nonneg t]),
          wideOddTest_eq_neg_one hW (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])]
        norm_num
    · rw [Set.indicator_of_notMem hx]
      exact wideOddTest_mul_shift_nonneg hW ht x
  have hmeas : MeasurableSet (Jp ∪ Jm) := measurableSet_Icc.union measurableSet_Icc
  have hint1 : MeasureTheory.Integrable ((Jp ∪ Jm).indicator fun _ => (1 : ℝ)) :=
    (MeasureTheory.integrable_indicator_iff hmeas).mpr
      ((MeasureTheory.integrableOn_const (by simp [Jp, Jm, Real.volume_Icc])).mono_set le_rfl)
  have hint := MeasureTheory.integral_mono hint1 (integrable_wideOddTest_mul_shift hW t) hpt
  have hval : ∫ x, (Jp ∪ Jm).indicator (fun _ => (1 : ℝ)) x = 2 * (2 * W - 2 * |t|) := by
    show ∫ x, (Jp ∪ Jm).indicator 1 x = _
    rw [MeasureTheory.integral_indicator_one hmeas, MeasureTheory.measureReal_union hdisj
      measurableSet_Icc (h₁ := measure_Icc_lt_top.ne) (h₂ := measure_Icc_lt_top.ne)]
    simp only [Jp, Jm, MeasureTheory.measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hval] at hint
  exact hint

/-- The mass of the wide odd test is at most `2(3W + 2)`. -/
theorem autoCorrelation_wideOddTest_zero_le {W : ℝ} (hW : 0 < W) :
    autoCorrelation (wideOddTest W hW) 0 ≤ 2 * (3 * W + 2) := by
  set J := Set.Icc (-(3 * W + 2)) (3 * W + 2)
  have hpt : ∀ x, wideOddTest W hW x * wideOddTest W hW (x + 0)
      ≤ J.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    rw [add_zero]
    by_cases hx : x ∈ J
    · rw [Set.indicator_of_mem hx]
      have h := abs_le.mp (abs_wideOddTest_le hW x)
      nlinarith [h.1, h.2]
    · rw [Set.indicator_of_notMem hx]
      have : 3 * W + 2 < |x| := by
        simp only [J, Set.mem_Icc, not_and_or] at hx
        rcases hx with h | h <;> push Not at h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [wideOddTest_eq_zero hW this]; simp
  have hint1 : MeasureTheory.Integrable (J.indicator fun _ => (1 : ℝ)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (MeasureTheory.integrableOn_const (by simp [J, Real.volume_Icc]))
  have hint := MeasureTheory.integral_mono (integrable_wideOddTest_mul_shift hW 0) hint1 hpt
  have hval : ∫ x, J.indicator (fun _ => (1 : ℝ)) x = 2 * (3 * W + 2) := by
    show ∫ x, J.indicator 1 x = _
    rw [MeasureTheory.integral_indicator_one measurableSet_Icc]
    simp only [J, MeasureTheory.measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [autoCorrelation]
  linarith

/-- **Wide odd tests.** For `W ≥ 2` the wide odd test has positive mass and
`A_F(t) ≥ A_F(0)/4` at every lag `|t| ≤ W/2`. -/
theorem wideOddTest_resonant {W : ℝ} (hW : 2 ≤ W) :
    0 < autoCorrelation (wideOddTest W (by linarith)) 0 ∧
      ∀ t, |t| ≤ W / 2 →
        autoCorrelation (wideOddTest W (by linarith)) 0 / 4
          ≤ autoCorrelation (wideOddTest W (by linarith)) t := by
  have hW0 : 0 < W := by linarith
  have h0 := autoCorrelation_wideOddTest_ge hW0 (t := 0) (by simp; linarith)
  have hle := autoCorrelation_wideOddTest_zero_le hW0
  simp only [abs_zero, mul_zero, sub_zero] at h0
  refine ⟨by linarith, fun t ht => ?_⟩
  have := autoCorrelation_wideOddTest_ge hW0 (t := t) (by linarith)
  linarith

/-! ### The refutation -/

/-- `r^m e^{−r/12} → 0`. -/
theorem tendsto_pow_mul_exp_neg_twelfth (m : ℕ) :
    Tendsto (fun r : ℝ => r ^ m * Real.exp (-(r / 12))) atTop (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 12))
  have h2 := h.const_mul ((12 : ℝ) ^ m)
  rw [mul_zero] at h2
  refine h2.congr fun r => ?_
  simp only [Function.comp, id]
  rw [div_pow, ← mul_assoc, mul_div_cancel₀ _ (by positivity)]

/-- The horizon `N = ⌊e^{2r}⌋` lies between `e^{2r}/2` and `e^{2r}` once `r ≥ 1`. -/
theorem horizon_bounds {r : ℝ} (hr : 1 ≤ r) :
    Real.exp (2 * r) / 2 ≤ ⌊Real.exp (2 * r)⌋₊ ∧ (⌊Real.exp (2 * r)⌋₊ : ℝ) ≤ Real.exp (2 * r) := by
  have h2 : 2 ≤ Real.exp (2 * r) := by
    have := Real.add_one_le_exp (2 * r); linarith
  have := Nat.lt_floor_add_one (Real.exp (2 * r))
  exact ⟨by linarith, Nat.floor_le (Real.exp_pos _).le⟩

/-- **The mean-field inequality for the wide odd test.** With `r = 3W + 2`, `N = ⌊e^{2r}⌋` and
`W ≥ 38⁴`, the normalized aggregate exceeds `(log² 2/16) N` minus explicit lower-order terms. -/
theorem crossAggregate_wideOddTest_ge {W : ℝ} (hW : (38 : ℝ) ^ 4 ≤ W) :
    let r := 3 * W + 2
    let N := ⌊Real.exp (2 * r)⌋₊
    let A0 := autoCorrelation (wideOddTest W (by linarith [show (0:ℝ) < 38 ^ 4 by positivity])) 0
    A0 * (Real.log 2 ^ 2 / 16 * N - (1 + 2 * r) ^ 3 / 4 - 5 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * N)
      ≤ crossAggregate N (autoCorrelation (wideOddTest W
          (by linarith [show (0:ℝ) < 38 ^ 4 by positivity]))) := by
  intro r N A0
  have hW2 : 2 ≤ W := le_trans (by norm_num) hW
  have hW0 : 0 < W := by linarith
  obtain ⟨hA0, hnear⟩ := wideOddTest_resonant hW2
  have hr1 : 1 ≤ r := by simp only [r]; linarith
  obtain ⟨hNge, hNle⟩ := horizon_bounds hr1
  have hN1 : (1 : ℝ) ≤ N := by
    have : (2 : ℝ) ≤ Real.exp (2 * r) := by have := Real.add_one_le_exp (2 * r); linarith
    linarith
  have hN38 : (38 : ℝ) ^ 4 ≤ N := by
    have : 2 * (38 : ℝ) ^ 4 ≤ Real.exp (2 * r) := by
      have := Real.add_one_le_exp (2 * r); simp only [r] at this ⊢; linarith
    linarith
  have hlogN : Real.log N ≤ 2 * r := by
    rw [← Real.log_exp (2 * r)]; exact Real.log_le_log (by linarith) hNle
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hagg := crossAggregate_ge (N := N) (T := W / 2) (by linarith) (A := autoCorrelation
    (wideOddTest W hW0)) hA0.le (fun t => by
      have := abs_autoCorrelation_le (continuous_wideOddTest hW0) (wideOddTest_hasCompactSupport hW0) t
      linarith [neg_abs_le (autoCorrelation (wideOddTest W hW0) t)]) hnear
  have hfar := farPairs_le (N := N) (T := W / 2) (by linarith)
  have hS := theta_div_sqrt_le_combMass (N := N) (by exact_mod_cast hN1)
  have hθ := theta_ge_half_log_two hN38
  have hθle : Chebyshev.theta N ≤ 2 * N := by
    have h4 := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by linarith)
    have hl4 : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num); linarith
    have := mul_le_mul_of_nonneg_right hl4.le (show (0 : ℝ) ≤ N by linarith)
    linarith
  have hQ := combDiagonal_le N
  -- `S² ≥ (log² 2/4) N`
  have hS2 : Real.log 2 ^ 2 / 4 * N ≤ combMass N ^ 2 := by
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
    have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
    have hl : Real.log 2 / 2 * Real.sqrt N ≤ combMass N := by
      refine le_trans ?_ hS
      rw [le_div_iff₀ hsN, mul_assoc, ← sq, hsqN]; exact hθ
    have hl0 : 0 ≤ Real.log 2 / 2 * Real.sqrt N := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
    have := mul_le_mul hl hl hl0 (le_trans hl0 hl)
    have e : (Real.log 2 / 2 * Real.sqrt N) * (Real.log 2 / 2 * Real.sqrt N)
        = Real.log 2 ^ 2 / 4 * N := by
      rw [show (Real.log 2 / 2 * Real.sqrt N) * (Real.log 2 / 2 * Real.sqrt N)
        = Real.log 2 ^ 2 / 4 * Real.sqrt N ^ 2 by ring, hsqN]
    rw [sq]; linarith
  -- the far pairs and the diagonal are of lower order
  have hfar' : farPairs N (W / 2) ≤ 4 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * N := by
    have hexp : Real.exp (-(W / 2) / 2) = Real.exp (-(W / 4)) := by congr 1; ring
    have hpow : (1 + Real.log N) ^ 2 ≤ (1 + 2 * r) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [hexp] at hfar
    have he : 0 ≤ Real.exp (-(W / 4)) := (Real.exp_pos _).le
    calc farPairs N (W / 2) ≤ 2 * Real.exp (-(W / 4)) * (1 + Real.log N) ^ 2 * Chebyshev.theta N :=
          hfar
      _ ≤ 2 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * (2 * N) := by
          gcongr
      _ = 4 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * N := by ring
  have hQ' : combDiagonal N ≤ (1 + 2 * r) ^ 3 :=
    hQ.trans (pow_le_pow_left₀ (by linarith) (by linarith) 3)
  have hgoal : Real.log 2 ^ 2 / 16 * N - (1 + 2 * r) ^ 3 / 4 - 5 * Real.exp (-(W / 4)) *
      (1 + 2 * r) ^ 2 * N ≤ (combMass N ^ 2 - combDiagonal N) / 4 - 5 / 4 * farPairs N (W / 2) := by
    linarith
  calc A0 * (Real.log 2 ^ 2 / 16 * N - (1 + 2 * r) ^ 3 / 4 - 5 * Real.exp (-(W / 4)) *
        (1 + 2 * r) ^ 2 * N)
      ≤ A0 * ((combMass N ^ 2 - combDiagonal N) / 4 - 5 / 4 * farPairs N (W / 2)) :=
        mul_le_mul_of_nonneg_left hgoal hA0.le
    _ ≤ _ := hagg

/-- **The quantitative clause of the adjunction conjecture is false.** No polynomial bound
`C(1 + r)^k A_F(0) Σ w_p² + (Σ_p 2 log p/(√p − 1)) A_F(0)` controls the cross-prime aggregate of
all odd `C²` tests of aperture `r` below the horizon `e^{2r}`. -/
theorem not_exists_polynomial_adjunction_bound :
    ¬ ∃ (C : ℝ) (k : ℕ), ∀ r : ℝ, 1 ≤ r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) →
      tsupport F ⊆ Set.Icc (-r) r →
        crossAggregate ⌊Real.exp (2 * r)⌋₊ (autoCorrelation F)
          ≤ C * (1 + r) ^ k * autoCorrelation F 0 * combDiagonal ⌊Real.exp (2 * r)⌋₊
            + envelopeBudget ⌊Real.exp (2 * r)⌋₊ * autoCorrelation F 0 := by
  rintro ⟨C, k, h⟩
  set C' := |C|
  set K : ℝ := 27 * (1 / 4 + C' * 2 ^ k) * 2 + 45 * Real.exp (1 / 6) + 90 * 2
  have hK : 0 < K := by positivity
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set ε : ℝ := Real.log 2 ^ 2 / 16
  have hε : 0 < ε := by positivity
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_mul_exp_neg_twelfth (k + 3)).eventually (gt_mem_nhds (div_pos hε hK)))
  set W : ℝ := max r₀ ((38 : ℝ) ^ 4)
  have hW38 : (38 : ℝ) ^ 4 ≤ W := le_max_right _ _
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW38
  set r := 3 * W + 2
  have hr1 : 1 ≤ r := by simp only [r]; linarith
  have hrr₀ : r₀ ≤ r := by simp only [r, W]; linarith [le_max_left r₀ ((38 : ℝ) ^ 4)]
  set N := ⌊Real.exp (2 * r)⌋₊
  set A0 := autoCorrelation (wideOddTest W hW0) 0
  have hlow := crossAggregate_wideOddTest_ge hW38
  have hup := h r hr1 (wideOddTest W hW0) (wideOddTest_contDiff hW0) (wideOddTest_odd hW0)
    (tsupport_wideOddTest hW0)
  obtain ⟨hA0, -⟩ := wideOddTest_resonant (le_trans (by norm_num) hW38)
  obtain ⟨hNge, hNle⟩ := horizon_bounds hr1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNge
  have hlogN : Real.log N ≤ 2 * r := by
    rw [← Real.log_exp (2 * r)]; exact Real.log_le_log hN0 hNle
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by
    have : (2 : ℝ) ≤ Real.exp (2 * r) := by have := Real.add_one_le_exp (2 * r); linarith
    linarith)
  -- upper side, normalized by `A0`
  have hQ : combDiagonal N ≤ (1 + 2 * r) ^ 3 :=
    (combDiagonal_le N).trans (pow_le_pow_left₀ (by linarith) (by linarith) 3)
  have hQ0 : 0 ≤ combDiagonal N := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hsqrtN : Real.sqrt N ≤ Real.exp r := by
    have he2 : Real.exp (2 * r) = Real.exp r ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    calc Real.sqrt N ≤ Real.sqrt (Real.exp (2 * r)) := Real.sqrt_le_sqrt hNle
      _ = Real.exp r := by rw [he2, Real.sqrt_sq (Real.exp_pos r).le]
  have hS : combMass N ≤ Real.exp r * (1 + 2 * r) ^ 2 :=
    (combMass_le N).trans (mul_le_mul hsqrtN (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (by positivity) (Real.exp_pos r).le)
  have hE := envelopeBudget_le N
  have hCQ : C * (1 + r) ^ k * combDiagonal N ≤ C' * (1 + r) ^ k * (1 + 2 * r) ^ 3 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      hQ0).trans (mul_le_mul_of_nonneg_left hQ (by positivity))
  have hupN : Real.log 2 ^ 2 / 16 * N - (1 + 2 * r) ^ 3 / 4 - 5 * Real.exp (-(W / 4)) *
      (1 + 2 * r) ^ 2 * N ≤ C' * (1 + r) ^ k * (1 + 2 * r) ^ 3 + 10 * (Real.exp r * (1 + 2 * r) ^ 2) := by
    have h1 : A0 * (Real.log 2 ^ 2 / 16 * N - (1 + 2 * r) ^ 3 / 4 - 5 * Real.exp (-(W / 4)) *
        (1 + 2 * r) ^ 2 * N) ≤ A0 * (C' * (1 + r) ^ k * (1 + 2 * r) ^ 3 +
          10 * (Real.exp r * (1 + 2 * r) ^ 2)) := by
      refine le_trans hlow (le_trans hup ?_)
      show C * (1 + r) ^ k * A0 * combDiagonal N + envelopeBudget N * A0 ≤ _
      have e1 : C * (1 + r) ^ k * A0 * combDiagonal N = A0 * (C * (1 + r) ^ k * combDiagonal N) := by
        ring
      have h1' : A0 * (C * (1 + r) ^ k * combDiagonal N) ≤ A0 * (C' * (1 + r) ^ k * (1 + 2 * r) ^ 3) :=
        mul_le_mul_of_nonneg_left hCQ hA0.le
      have h2' : envelopeBudget N * A0 ≤ A0 * (10 * (Real.exp r * (1 + 2 * r) ^ 2)) := by
        calc envelopeBudget N * A0 ≤ 10 * combMass N * A0 :=
              mul_le_mul_of_nonneg_right hE hA0.le
          _ ≤ 10 * (Real.exp r * (1 + 2 * r) ^ 2) * A0 :=
              mul_le_mul_of_nonneg_right (by linarith) hA0.le
          _ = A0 * (10 * (Real.exp r * (1 + 2 * r) ^ 2)) := by ring
      rw [e1, mul_add]
      linarith
    exact le_of_mul_le_mul_left h1 hA0
  -- normalize by `N ≥ e^{2r}/2` and compare with `K r^{k+3} e^{−r/12}`
  set R := r ^ (k + 3)
  set E := Real.exp (-(r / 12)) * N
  have hE0 : 0 ≤ E := by positivity
  have hE1 : 1 ≤ 2 * E := by
    have he : Real.exp (-(r / 12)) * (Real.exp (2 * r) / 2) = Real.exp (2 * r - r / 12) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]; ring_nf
    have h1 : 1 ≤ Real.exp (2 * r - r / 12) := Real.one_le_exp (by linarith)
    have h2 : Real.exp (-(r / 12)) * (Real.exp (2 * r) / 2) ≤ E :=
      mul_le_mul_of_nonneg_left hNge (Real.exp_pos _).le
    linarith
  have hE2 : Real.exp r ≤ E := by
    have he : Real.exp (-(r / 12)) * (Real.exp (2 * r) / 2)
        = Real.exp r * Real.exp (11 * r / 12) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have h1 : 2 ≤ Real.exp (11 * r / 12) := by
      have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 11 * r / 12 by linarith)
      have : 0 ≤ (11 * r / 12) ^ 2 / 2 := by positivity
      linarith
    have h2 : Real.exp (-(r / 12)) * (Real.exp (2 * r) / 2) ≤ E :=
      mul_le_mul_of_nonneg_left hNge (Real.exp_pos _).le
    have h3 : Real.exp r * 2 ≤ Real.exp r * Real.exp (11 * r / 12) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos r).le
    linarith
  have hpoly : 1 + 2 * r ≤ 3 * r := by linarith
  have hR2 : r ^ 2 ≤ R := pow_le_pow_right₀ hr1 (by omega)
  have hr2 : (1 + 2 * r) ^ 2 ≤ 9 * R := by
    have h1 : (1 + 2 * r) ^ 2 ≤ (3 * r) ^ 2 := pow_le_pow_left₀ (by linarith) hpoly 2
    have e : (3 * r) ^ 2 = 9 * r ^ 2 := by ring
    linarith
  have hr3 : (1 + 2 * r) ^ 3 ≤ 27 * r ^ 3 := by
    have h1 : (1 + 2 * r) ^ 3 ≤ (3 * r) ^ 3 := pow_le_pow_left₀ (by linarith) hpoly 3
    have e : (3 * r) ^ 3 = 27 * r ^ 3 := by ring
    linarith
  have hRk : r ^ k * r ^ 3 = R := by rw [← pow_add]
  have hrk : (1 + r) ^ k ≤ 2 ^ k * r ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) k
  have hrk1 : 1 ≤ r ^ k := one_le_pow₀ hr1
  have hR3 : r ^ 3 ≤ R := by
    rw [← hRk]; exact le_mul_of_one_le_left (pow_nonneg (by linarith) 3) hrk1
  have hW4 : Real.exp (-(W / 4)) = Real.exp (1 / 6) * Real.exp (-(r / 12)) := by
    rw [← Real.exp_add]; congr 1; simp only [r]; ring
  have hC' : 0 ≤ C' := abs_nonneg C
  -- the three error terms
  have ha : (1 + 2 * r) ^ 3 / 4 + C' * (1 + r) ^ k * (1 + 2 * r) ^ 3
      ≤ 27 * (1 / 4 + C' * 2 ^ k) * 2 * R * E := by
    have h1 : (1 + 2 * r) ^ 3 / 4 ≤ 27 / 4 * R := by linarith
    have h2 : C' * (1 + r) ^ k * (1 + 2 * r) ^ 3 ≤ 27 * C' * 2 ^ k * R := by
      calc C' * (1 + r) ^ k * (1 + 2 * r) ^ 3 ≤ C' * (2 ^ k * r ^ k) * (27 * r ^ 3) := by gcongr
        _ = 27 * C' * 2 ^ k * (r ^ k * r ^ 3) := by ring
        _ = 27 * C' * 2 ^ k * R := by rw [hRk]
    have h3 : 0 ≤ 27 * (1 / 4 + C' * 2 ^ k) * R := by positivity
    have h4 := mul_le_mul_of_nonneg_left hE1 h3
    have e : 27 * (1 / 4 + C' * 2 ^ k) * R * (2 * E) = 27 * (1 / 4 + C' * 2 ^ k) * 2 * R * E := by
      ring
    have e2 : 27 * (1 / 4 + C' * 2 ^ k) * R = 27 / 4 * R + 27 * C' * 2 ^ k * R := by ring
    linarith
  have hb : 5 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * N ≤ 45 * Real.exp (1 / 6) * R * E := by
    have he6 : 0 ≤ 5 * Real.exp (1 / 6) * E := by positivity
    have h1 := mul_le_mul_of_nonneg_left hr2 he6
    have e1 : 5 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * N
        = 5 * Real.exp (1 / 6) * E * (1 + 2 * r) ^ 2 := by rw [hW4]; simp only [E]; ring
    have e2 : 5 * Real.exp (1 / 6) * E * (9 * R) = 45 * Real.exp (1 / 6) * R * E := by ring
    linarith
  have hc : 10 * (Real.exp r * (1 + 2 * r) ^ 2) ≤ 90 * 2 * R * E := by
    have h1 := mul_le_mul hE2 hr2 (by positivity) hE0
    have h2 : 0 ≤ R * E := by positivity
    have e : E * (9 * R) = 9 * (R * E) := by ring
    have e2 : 90 * 2 * R * E = 180 * (R * E) := by ring
    linarith
  have hfinal : ε * N ≤ K * R * E := by
    have hsum : Real.log 2 ^ 2 / 16 * N ≤ ((1 + 2 * r) ^ 3 / 4 + C' * (1 + r) ^ k * (1 + 2 * r) ^ 3)
        + 5 * Real.exp (-(W / 4)) * (1 + 2 * r) ^ 2 * N + 10 * (Real.exp r * (1 + 2 * r) ^ 2) := by
      linarith [hupN]
    calc ε * N = Real.log 2 ^ 2 / 16 * N := rfl
      _ ≤ _ := hsum
      _ ≤ 27 * (1 / 4 + C' * 2 ^ k) * 2 * R * E + 45 * Real.exp (1 / 6) * R * E
          + 90 * 2 * R * E := add_le_add (add_le_add ha hb) hc
      _ = K * R * E := by simp only [K]; ring
  have hsmall := hr₀ r hrr₀
  have hKE : K * R * E = K * (R * Real.exp (-(r / 12))) * N := by simp only [E]; ring
  rw [hKE] at hfinal
  have hlt : K * (R * Real.exp (-(r / 12))) < ε := by
    have := mul_lt_mul_of_pos_left hsmall hK
    rwa [mul_div_cancel₀ _ hK.ne'] at this
  have := mul_lt_mul_of_pos_right hlt hN0
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
