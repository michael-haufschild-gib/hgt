import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSignedEditRemaindersContinueBelowOneHalf
import GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall

/-!
# The signed edit factors through the tempered model

Let `e` be the signed grouped edit (`SignedEdit.sEdit`) with target `c(p) = e(p) + 2 p^{β-1}
cos(γ log p)` above `2^{k₀}`, and `ρ = β + iγ`.  The tempered model with the zero pair `ρ, ρ̄` is
`F(s) = ζ(s) M(s)`, `M(s) = ζ(s+1-ρ)⁻¹ ζ(s+1-ρ̄)⁻¹ ∏_{q < 2^{k₀}} (1 - q^{ρ-1-s})⁻¹ (1 - q^{ρ̄-1-s})⁻¹`
(`ArithmeticPositiveDuality.posCofactor` with cutoff `2^{k₀} - 1`).

**Factorization** (`sub_one_mul_zetaSeriesC_eq`).  On `Re s > 1`

`(s - 1) ζ_B(s) = (s - 1) ζ(s) · M(s) · exp(H₁(s) + Q(s) + R(s))`,

with `H₁` the edit series, `Q` the edit remainder and `R` the pair remainder.  The Euler product
of `ζ` gives `M = exp(-V)`, `V(s) = Σ_{p ≥ 2^{k₀}} (-log(1 - p^{ρ-1-s}) - log(1 - p^{ρ̄-1-s}))`
(`posCofactor_eq_exp`); the Euler product of the edit gives `exp(E + Q)`, `E = Σ e(p) p^{-s}`;
and `E + V = H₁ + R` termwise, since `2 p^{β-1} cos(γ log p) p^{-s} = p^{ρ-1-s} + p^{ρ̄-1-s}`.

**Continuation** (`differentiableOn_editContinuation`).  The right side is holomorphic on
`Re s > max(α/2, β - 1/2, Θ + β - 1)` whenever `ζ` has no zero right of `Θ`.
-/

open Complex Finset Filter Topology
open RHTower RHTower.Sieve RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit

variable {α β : ℝ}

/-! ## The cofactor as an exponential -/

/-- `V(s) = Σ_{p ≥ 2^{k₀}} (-log(1 - p^{-(s+1-ρ)}) - log(1 - p^{-(s+1-ρ̄)}))`. -/
def pairLog (β γ : ℝ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n.Prime ∧ 2 ^ k₀ ≤ n then
    -Complex.log (1 - (n : ℂ) ^ (-(s + (1 - zeroPt β γ)))) -
      Complex.log (1 - (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ))))) else 0

/-- A sum over the primes as a sum over `ℕ`. -/
theorem tsum_primes_eq (f : ℕ → ℂ) :
    ∑' p : Nat.Primes, f p = ∑' n : ℕ, if n.Prime then f n else 0 := by
  have h := _root_.tsum_subtype {n : ℕ | n.Prime} f
  rw [show (∑' n : ℕ, if n.Prime then f n else 0) = ∑' n : ℕ, {n : ℕ | n.Prime}.indicator f n from
    tsum_congr fun n => by rw [Set.indicator_apply]; rfl, ← h]
  rfl

/-- `ζ(w)⁻¹ = exp(Σ_p log(1 - p^{-w}))` on `Re w > 1`, as a sum over `ℕ`. -/
theorem invZeta_eq_exp {w : ℂ} (hw : 1 < w.re) :
    invZeta w = cexp (-∑' n : ℕ, if n.Prime then -Complex.log (1 - (n : ℂ) ^ (-w)) else 0) := by
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
  rw [invZeta_eq_inv hw1, ← riemannZeta_eulerProduct_exp_log hw, ← Complex.exp_neg,
    tsum_primes_eq (fun n => -Complex.log (1 - (n : ℂ) ^ (-w)))]

theorem norm_natCast_cpow_le_half {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : 1 ≤ w.re) :
    ‖(n : ℂ) ^ (-w)‖ ≤ 1 / 2 := by
  rw [norm_natCast_cpow_neg n (by omega)]
  calc (n : ℝ) ^ (-w.re) ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_neg_le_two hn (by norm_num) hw
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The logarithms `-log(1 - n^{-w})` over the primes are summable on `Re w > 1`. -/
theorem summable_primeLog {w : ℂ} (hw : 1 < w.re) (P : ℕ → Prop) [DecidablePred P] :
    Summable fun n : ℕ => if n.Prime ∧ P n then -Complex.log (1 - (n : ℂ) ^ (-w)) else 0 := by
  refine Summable.of_norm_bounded ((Real.summable_nat_rpow.mpr
    (show -w.re < -1 by linarith)).mul_left (3 / 2)) fun n => ?_
  split_ifs with h
  · rw [norm_neg]
    refine (norm_log_one_sub_le (norm_natCast_cpow_le_half h.1.two_le hw.le)).trans ?_
    rw [norm_natCast_cpow_neg n h.1.pos]
  · rw [norm_zero]; positivity

theorem one_sub_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, norm_one] at hz
  exact lt_irrefl _ hz

/-- The finite factor as an exponential of a sum over the primes below `2^{k₀}`. -/
theorem posFiniteFactor_eq_exp (β γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) (hβ : β < 1) :
    posFiniteFactor (2 ^ k₀ - 1) (zeroPt β γ) s = cexp (∑' n : ℕ, if n.Prime ∧ n < 2 ^ k₀ then
      -Complex.log (1 - (n : ℂ) ^ (-(s + (1 - zeroPt β γ)))) -
        Complex.log (1 - (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ))))) else 0) := by
  classical
  set g : ℕ → ℂ := fun n => -Complex.log (1 - (n : ℂ) ^ (-(s + (1 - zeroPt β γ)))) -
    Complex.log (1 - (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ))))) with hg
  have hre1 : 1 ≤ (s + (1 - zeroPt β γ)).re := by rw [re_add_one_sub_zeroPt]; linarith
  have hre2 : 1 ≤ (s + (1 - (starRingEnd ℂ) (zeroPt β γ))).re := by
    rw [re_add_one_sub_conj_zeroPt]; linarith
  -- each local factor is `exp(g q)`
  have hloc : ∀ q : Nat.Primes, (1 - ((q : ℕ) : ℂ) ^ (zeroPt β γ - 1 - s))⁻¹ *
      (1 - ((q : ℕ) : ℂ) ^ ((starRingEnd ℂ) (zeroPt β γ) - 1 - s))⁻¹ = cexp (g q) := by
    intro q
    have e1 : zeroPt β γ - 1 - s = -(s + (1 - zeroPt β γ)) := by ring
    have e2 : (starRingEnd ℂ) (zeroPt β γ) - 1 - s =
        -(s + (1 - (starRingEnd ℂ) (zeroPt β γ))) := by ring
    have h1 := norm_natCast_cpow_le_half q.2.two_le hre1
    have h2 := norm_natCast_cpow_le_half q.2.two_le hre2
    have hgq : g q = -Complex.log (1 - ((q : ℕ) : ℂ) ^ (-(s + (1 - zeroPt β γ)))) +
        -Complex.log (1 - ((q : ℕ) : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ))))) := by
      simp only [hg]; ring
    rw [e1, e2, hgq, Complex.exp_add, Complex.exp_neg, Complex.exp_neg,
      Complex.exp_log (one_sub_ne_zero_of_norm_lt (by linarith)),
      Complex.exp_log (one_sub_ne_zero_of_norm_lt (by linarith))]
  unfold posFiniteFactor
  rw [Finset.prod_congr rfl fun q _ => hloc q, ← Complex.exp_sum]
  congr 1
  -- the finite sum over `smallPrimes` as a sum over `ℕ`
  rw [tsum_eq_sum (s := (Finset.range (2 ^ k₀)).filter Nat.Prime) fun n hn => by
    rw [if_neg]; intro h; exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.2, h.1⟩)]
  rw [Finset.sum_congr rfl fun n hn => if_pos ⟨(Finset.mem_filter.mp hn).2,
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1⟩]
  have hsm : ∀ q : Nat.Primes, q ∈ smallPrimes (2 ^ k₀ - 1) ↔ (q : ℕ) ∈ (Finset.range (2 ^ k₀)).filter Nat.Prime := by
    intro q
    rw [mem_smallPrimes, Finset.mem_filter, Finset.mem_range]
    have := Nat.one_le_two_pow (n := k₀)
    exact ⟨fun h => ⟨by omega, q.2⟩, fun h => by omega⟩
  refine Finset.sum_nbij (fun q => (q : ℕ)) (fun q hq => (hsm q).mp hq)
    (fun q _ q' _ h => Subtype.ext h) (fun n hn => ?_) (fun q _ => rfl)
  exact ⟨⟨n, (Finset.mem_filter.mp hn).2⟩, (hsm _).mpr hn, rfl⟩

/-- **The cofactor is `exp(-V)`** on `Re s > 1`. -/
theorem posCofactor_eq_exp (β γ : ℝ) (k₀ : ℕ) (hβ : β < 1) {s : ℂ} (hs : 1 < s.re) :
    posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s = cexp (-pairLog β γ k₀ s) := by
  classical
  set w₁ : ℂ := s + (1 - zeroPt β γ) with hw₁
  set w₂ : ℂ := s + (1 - (starRingEnd ℂ) (zeroPt β γ)) with hw₂
  have h1 : 1 < w₁.re := by rw [hw₁, re_add_one_sub_zeroPt]; linarith
  have h2 : 1 < w₂.re := by rw [hw₂, re_add_one_sub_conj_zeroPt]; linarith
  have hinv1 : invZeta (s + 1 - zeroPt β γ) = cexp (-∑' n : ℕ, if n.Prime then
      -Complex.log (1 - (n : ℂ) ^ (-w₁)) else 0) := by
    rw [show s + 1 - zeroPt β γ = w₁ by rw [hw₁]; ring]; exact invZeta_eq_exp h1
  have hinv2 : invZeta (s + 1 - (starRingEnd ℂ) (zeroPt β γ)) = cexp (-∑' n : ℕ, if n.Prime then
      -Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0) := by
    rw [show s + 1 - (starRingEnd ℂ) (zeroPt β γ) = w₂ by rw [hw₂]; ring]; exact invZeta_eq_exp h2
  unfold posCofactor
  rw [hinv1, hinv2, posFiniteFactor_eq_exp β γ k₀ hs hβ, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  -- split the primes at `2^{k₀}`
  have hs1 := summable_primeLog h1 (fun _ => True)
  have hs2 := summable_primeLog h2 (fun _ => True)
  have hlo1 := summable_primeLog h1 (fun n => n < 2 ^ k₀)
  have hlo2 := summable_primeLog h2 (fun n => n < 2 ^ k₀)
  have hhi1 := summable_primeLog h1 (fun n => 2 ^ k₀ ≤ n)
  have hhi2 := summable_primeLog h2 (fun n => 2 ^ k₀ ≤ n)
  have hsplit : ∀ w : ℂ, ∀ n : ℕ, (if n.Prime then -Complex.log (1 - (n : ℂ) ^ (-w)) else 0) =
      (if n.Prime ∧ n < 2 ^ k₀ then -Complex.log (1 - (n : ℂ) ^ (-w)) else 0) +
        (if n.Prime ∧ 2 ^ k₀ ≤ n then -Complex.log (1 - (n : ℂ) ^ (-w)) else 0) := by
    intro w n
    by_cases hp : n.Prime
    · by_cases hn : n < 2 ^ k₀
      · rw [if_pos hp, if_pos ⟨hp, hn⟩, if_neg fun h => absurd h.2 (not_le.mpr hn), add_zero]
      · rw [if_pos hp, if_neg fun h => hn h.2, if_pos ⟨hp, not_lt.mp hn⟩, zero_add]
    · rw [if_neg hp, if_neg fun h => hp h.1, if_neg fun h => hp h.1, add_zero]
  have hT1 : (∑' n : ℕ, if n.Prime then -Complex.log (1 - (n : ℂ) ^ (-w₁)) else 0) =
      (∑' n : ℕ, if n.Prime ∧ n < 2 ^ k₀ then -Complex.log (1 - (n : ℂ) ^ (-w₁)) else 0) +
        ∑' n : ℕ, if n.Prime ∧ 2 ^ k₀ ≤ n then -Complex.log (1 - (n : ℂ) ^ (-w₁)) else 0 := by
    rw [← hlo1.tsum_add hhi1]; exact tsum_congr (hsplit w₁)
  have hT2 : (∑' n : ℕ, if n.Prime then -Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0) =
      (∑' n : ℕ, if n.Prime ∧ n < 2 ^ k₀ then -Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0) +
        ∑' n : ℕ, if n.Prime ∧ 2 ^ k₀ ≤ n then -Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0 := by
    rw [← hlo2.tsum_add hhi2]; exact tsum_congr (hsplit w₂)
  have hcomb : ∀ (P : ℕ → Prop) [DecidablePred P],
      (Summable fun n : ℕ => if n.Prime ∧ P n then -Complex.log (1 - (n : ℂ) ^ (-w₁)) else 0) →
      (Summable fun n : ℕ => if n.Prime ∧ P n then -Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0) →
      (∑' n : ℕ, if n.Prime ∧ P n then -Complex.log (1 - (n : ℂ) ^ (-w₁)) -
          Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0) =
        (∑' n : ℕ, if n.Prime ∧ P n then -Complex.log (1 - (n : ℂ) ^ (-w₁)) else 0) +
          ∑' n : ℕ, if n.Prime ∧ P n then -Complex.log (1 - (n : ℂ) ^ (-w₂)) else 0 := by
    intro P _ ha hb
    rw [← ha.tsum_add hb]
    refine tsum_congr fun n => ?_
    split_ifs <;> ring
  have hlo := hcomb (fun n => n < 2 ^ k₀) hlo1 hlo2
  have hhi := hcomb (fun n => 2 ^ k₀ ≤ n) hhi1 hhi2
  unfold pairLog
  rw [← hw₁, ← hw₂] at *
  rw [hT1, hT2, hlo, hhi]
  ring

/-! ## The exponent -/

theorem conj_zeroPt (β γ : ℝ) : (starRingEnd ℂ) (zeroPt β γ) = (β : ℂ) - (γ : ℂ) * I := by
  apply Complex.ext <;> simp [zeroPt]

/-- `2 n^{β-1} cos(γ log n) n^{-s} = n^{-(s+1-ρ)} + n^{-(s+1-ρ̄)}`. -/
theorem cos_term_eq (β γ : ℝ) {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ((2 * (n : ℝ) ^ (β - 1) * Real.cos (γ * Real.log n) : ℝ) : ℂ) * (n : ℂ) ^ (-s) =
      (n : ℂ) ^ (-(s + (1 - zeroPt β γ))) +
        (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ)))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hL : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hn0, hL]
  have e1 : ((Real.log n : ℝ) : ℂ) * -(s + (1 - zeroPt β γ)) =
      ((Real.log n : ℝ) : ℂ) * -s + ((Real.log n * (β - 1) : ℝ) : ℂ) +
        ((γ * Real.log n : ℝ) : ℂ) * I := by
    simp only [zeroPt]; push_cast; ring
  have e2 : ((Real.log n : ℝ) : ℂ) * -(s + (1 - (starRingEnd ℂ) (zeroPt β γ))) =
      ((Real.log n : ℝ) : ℂ) * -s + ((Real.log n * (β - 1) : ℝ) : ℂ) +
        ((-(γ * Real.log n) : ℝ) : ℂ) * I := by
    rw [conj_zeroPt]; push_cast; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
    Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp,
    Real.cos_neg, Real.sin_neg, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  push_cast
  ring

theorem summable_pairLin (β γ : ℝ) (k₀ : ℕ) (hβ : β < 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => if n.Prime ∧ 2 ^ k₀ ≤ n then
      (n : ℂ) ^ (-(s + (1 - zeroPt β γ))) +
        (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ)))) else 0 := by
  refine Summable.of_norm_bounded ((Real.summable_nat_rpow.mpr
    (show -(s.re + 1 - β) < -1 by linarith)).mul_left 2) fun n => ?_
  split_ifs with h
  · refine (norm_add_le _ _).trans ?_
    rw [norm_natCast_cpow_neg n h.1.pos, norm_natCast_cpow_neg n h.1.pos,
      re_add_one_sub_zeroPt, re_add_one_sub_conj_zeroPt]
    linarith
  · rw [norm_zero]; positivity

/-- **`E + W₁ = H₁`.**  On `Re s > 1` the edit series is the edit's Dirichlet series plus the
first-order part of the pair. -/
theorem LSeries_add_pairLin_eq_editSeries (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun k => (sEdit α β γ k₀ k : ℂ)) s +
      (∑' n : ℕ, if n.Prime ∧ 2 ^ k₀ ≤ n then
        (n : ℂ) ^ (-(s + (1 - zeroPt β γ))) +
          (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ)))) else 0) =
      editSeries α β γ k₀ s := by
  classical
  have hE : ∀ n : ℕ, LSeries.term (fun k => (sEdit α β γ k₀ k : ℂ)) s n =
      if n.Prime ∧ 2 ^ k₀ ≤ n then (sEdit α β γ k₀ n : ℂ) * (n : ℂ) ^ (-s) else 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [Nat.not_prime_zero]
    · rw [LSeries.term_of_ne_zero hpos.ne', Complex.cpow_neg, div_eq_mul_inv]
      split_ifs with h
      · rfl
      · have : sEdit α β γ k₀ n = 0 := by
          by_cases hp : n.Prime
          · exact sEdit_eq_zero_of_lt γ (not_le.mp fun h' => h ⟨hp, h'⟩)
          · exact (isEdit_sEdit α β γ k₀).prime n hp
        rw [this]; simp
  have hsumE : Summable fun n : ℕ =>
      if n.Prime ∧ 2 ^ k₀ ≤ n then (sEdit α β γ k₀ n : ℂ) * (n : ℂ) ^ (-s) else 0 := by
    refine Summable.of_norm_bounded (Real.summable_nat_rpow.mpr
      (show -s.re < -1 by linarith)) fun n => ?_
    split_ifs with h
    · rw [norm_mul, norm_natCast_cpow_neg n h.1.pos]
      exact mul_le_of_le_one_left (by positivity) ((isEdit_sEdit α β γ k₀).norm_le_one n)
    · rw [norm_zero]; positivity
  rw [editSeries_eq_tsum hβ.le γ k₀ hs, LSeries, tsum_congr hE,
    ← hsumE.tsum_add (summable_pairLin β γ k₀ hβ hs)]
  refine tsum_congr fun n => ?_
  unfold primeTerm target
  split_ifs with h
  · rw [add_mul, cos_term_eq β γ h.1.pos s]
  · rw [add_zero]

/-- **`V = W₁ + R`.** -/
theorem pairLog_eq (β γ : ℝ) (k₀ : ℕ) (hβ : β < 1) {s : ℂ} (hs : 1 < s.re) :
    pairLog β γ k₀ s = (∑' n : ℕ, if n.Prime ∧ 2 ^ k₀ ≤ n then
      (n : ℂ) ^ (-(s + (1 - zeroPt β γ))) +
        (n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ)))) else 0) + pairRem β γ k₀ s := by
  set a : ℝ := s.re + 1 - β with ha
  have ha1 : 1 / 2 < a := by rw [ha]; linarith
  have hR : Summable fun n : ℕ => if n.Prime ∧ 2 ^ k₀ ≤ n then
      logRem ((n : ℂ) ^ (-(s + (1 - zeroPt β γ)))) +
        logRem ((n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ))))) else 0 :=
    Summable.of_norm_bounded (summable_pairRem_majorant ha1) fun n =>
      norm_pairRem_term_le β γ k₀ n (by linarith) (le_of_eq (by rw [ha]))
  unfold pairLog pairRem
  rw [← (summable_pairLin β γ k₀ hβ hs).tsum_add hR]
  refine tsum_congr fun n => ?_
  split_ifs
  · unfold logRem; ring
  · ring

/-! ## The factorization and the continuation -/

theorem zetaResidueUnit_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnit s = (s - 1) * riemannZeta s := by
  simp [zetaResidueUnit, Function.update_of_ne hs]

/-- The continued exponent `H₁ + Q + R`. -/
def editExponent (α β γ : ℝ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  editSeries α β γ k₀ s + editRem (sEdit α β γ k₀) s + pairRem β γ k₀ s

/-- The cofactor `M_B = M · exp(H₁ + Q + R)` of the signed edit. -/
def editCofactor (α β γ : ℝ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s * cexp (editExponent α β γ k₀ s)

/-- **The factorization.**  On `Re s > 1`,
`(s - 1) ζ_B(s) = (s - 1) ζ(s) · M(s) · exp(H₁(s) + Q(s) + R(s))`. -/
theorem sub_one_mul_zetaSeriesC_eq (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * (editSystem (sEdit α β γ k₀)).zetaSeriesC s =
      zetaResidueUnit s * editCofactor α β γ k₀ s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hexp : LSeries (fun k => (sEdit α β γ k₀ k : ℂ)) s + editRem (sEdit α β γ k₀) s =
      -pairLog β γ k₀ s + editExponent α β γ k₀ s := by
    rw [pairLog_eq β γ k₀ hβ hs, editExponent, ← LSeries_add_pairLin_eq_editSeries hβ γ k₀ hs]
    ring
  rw [editSystem_zetaSeriesC (isEdit_sEdit α β γ k₀) hs, editCofactor,
    posCofactor_eq_exp β γ k₀ hβ hs, zetaResidueUnit_eq_of_ne hs1, hexp, Complex.exp_add]
  ring

theorem differentiableOn_editExponent (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) :
    DifferentiableOn ℂ (editExponent α β γ k₀) {s : ℂ | α / 2 < s.re ∧ β - 1 / 2 < s.re} :=
  (((differentiableOn_editSeries hα0 hα hβ γ hk₀).mono fun _ h => h.1).add
    ((differentiableOn_editRem_sparse hα0 hα γ k₀).mono fun _ h => h.1)).add
    ((differentiableOn_pairRem β γ k₀).mono fun _ h => h.2)

/-- **The cofactor continues** to `Re s > max(α/2, β - 1/2, Θ + β - 1)` when `ζ` has no zero right
of `Θ`. -/
theorem differentiableOn_editCofactor (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) :
    DifferentiableOn ℂ (editCofactor α β γ k₀)
      {s : ℂ | α / 2 < s.re ∧ β - 1 / 2 < s.re ∧ Θ + β - 1 < s.re} := by
  intro s hs
  have hM : DifferentiableAt ℂ (posCofactor (2 ^ k₀ - 1) (zeroPt β γ)) s :=
    differentiableAt_posCofactor_of_re_gt γ hΘ hzf (2 ^ k₀ - 1) hs.2.2
  exact (hM.differentiableWithinAt.mul (((differentiableOn_editExponent hα0 hα hβ γ hk₀).cexp.mono
    fun _ h => ⟨h.1, h.2.1⟩) s hs))

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
