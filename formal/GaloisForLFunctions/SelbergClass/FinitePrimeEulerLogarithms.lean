import GaloisForLFunctions.SelbergClass.FiniteEulerLogarithmicPositivity

/-! # Logarithmic positivity separates finitely many prime edits

The canonical logarithm of a finite Euler polynomial is a sum of corrections
supported on distinct prime-power sets. Uniqueness of logarithmic Dirichlet
coefficients therefore applies the local unit-disk root criterion at every prime.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Topology
open scoped Classical BigOperators
namespace GaloisForLFunctions.SelbergClass.FiniteEuler
open PositiveFiniteEuler

/-- Polynomial Euler edits at a finite set of primes. -/
def finiteMultiplier (S : Finset ℕ) (W : ℕ → Multiset ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, multiplier (W p) ((p : ℂ) ^ (-s))

/-- Their canonical logarithmic Dirichlet coefficients. -/
def finiteLogCoeff (S : Finset ℕ) (W : ℕ → Multiset ℂ) (n : ℕ) : ℂ :=
  RHTower.eulerLogDirichletCoeff n + ∑ p ∈ S, rootLogCoeff p (W p) n

/-- A different prime contributes nothing to a positive prime power. -/
theorem rootLogCoeff_other_prime_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (W : Multiset ℂ) {k : ℕ} (hk : k ≠ 0) :
    rootLogCoeff q W (p ^ k) = 0 := by
  have hnot : p ^ k ∉ Set.range (fun j : ℕ => q ^ j) := by
    rintro ⟨j, hj⟩
    have hpdiv : p ∣ p ^ k := by
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      exact ⟨p ^ l, by rw [pow_succ']⟩
    rw [← hj] at hpdiv
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdiv))
  unfold rootLogCoeff
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx
  exact Function.extend_apply' _ _ _ hnot

/-- Distinct-prime corrections leave the local repeated-prime coefficients unchanged. -/
theorem finiteLogCoeff_prime_pow (S : Finset ℕ) (W : ℕ → Multiset ℂ)
    (hS : ∀ p ∈ S, p.Prime) {p : ℕ} (hp : p ∈ S) {k : ℕ} (hk : k ≠ 0) :
    finiteLogCoeff S W (p ^ k) = logCoeff p (W p) (p ^ k) := by
  unfold finiteLogCoeff logCoeff
  congr 1
  apply Finset.sum_eq_single p
  · intro q hq hqp
    exact rootLogCoeff_other_prime_pow (hS p hp) (hS q hq) hqp.symm (W q) hk
  · exact fun h => (h hp).elim

/-- The correction logarithm is summable and exponentiates to its local polynomial. -/
theorem rootLogCoeff_summable_exp {p : ℕ} (hp : p.Prime) (W : Multiset ℂ) {s : ℂ}
    (hs : 1 < s.re) (hsmall : ∀ a ∈ W, ‖a * (p : ℂ) ^ (-s)‖ < 1) :
    LSeriesSummable (rootLogCoeff p W) s ∧
      Complex.exp (LSeries (rootLogCoeff p W) s) = multiplier W ((p : ℂ) ^ (-s)) := by
  obtain ⟨hL, he⟩ := logCoeff_summable_exp hp W hs hsmall
  have hζ := RHTower.canonicalEulerLogZeta_summable hs
  have hr : LSeriesSummable (rootLogCoeff p W) s := by
    have h := hL.sub hζ
    convert h using 1
    funext n
    simp only [Pi.sub_apply, logCoeff, add_sub_cancel_left]
  refine ⟨hr, ?_⟩
  have hsum : LSeries (logCoeff p W) s =
      LSeries RHTower.eulerLogDirichletCoeff s + LSeries (rootLogCoeff p W) s :=
    (hζ.LSeriesHasSum.add hr.LSeriesHasSum).LSeries_eq
  rw [hsum, Complex.exp_add] at he
  have hze : Complex.exp (LSeries RHTower.eulerLogDirichletCoeff s) = riemannZeta s :=
    RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hs
  rw [← hze] at he
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) he

/-- A finite family has an absolutely convergent canonical logarithm in its small-factor region. -/
theorem finiteLogCoeff_summable_exp (S : Finset ℕ) (W : ℕ → Multiset ℂ)
    (hS : ∀ p ∈ S, p.Prime) {s : ℂ} (hs : 1 < s.re)
    (hsmall : ∀ p ∈ S, ∀ a ∈ W p, ‖a * (p : ℂ) ^ (-s)‖ < 1) :
    LSeriesSummable (finiteLogCoeff S W) s ∧
      Complex.exp (LSeries (finiteLogCoeff S W) s) = riemannZeta s * finiteMultiplier S W s := by
  induction S using Finset.induction_on with
  | empty =>
    have hzero : finiteLogCoeff ∅ W = RHTower.eulerLogDirichletCoeff := by
      funext n
      simp only [finiteLogCoeff, Finset.sum_empty, add_zero]
    rw [hzero]
    simpa only [finiteMultiplier, Finset.prod_empty, mul_one, RHTower.canonicalEulerLogZeta] using
      And.intro (RHTower.canonicalEulerLogZeta_summable hs)
        (RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hs)
  | @insert p S hp ih =>
    obtain ⟨hL, he⟩ := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      (fun q hq => hsmall q (Finset.mem_insert_of_mem hq))
    obtain ⟨hr, her⟩ := rootLogCoeff_summable_exp (hS p (Finset.mem_insert_self _ _)) (W p)
      hs (hsmall p (Finset.mem_insert_self _ _))
    have hc : finiteLogCoeff (insert p S) W = finiteLogCoeff S W + rootLogCoeff p (W p) := by
      funext n
      simp only [finiteLogCoeff, Finset.sum_insert hp, Pi.add_apply]
      ring
    rw [hc]
    refine ⟨hL.add hr, ?_⟩
    rw [(hL.LSeriesHasSum.add hr.LSeriesHasSum).LSeries_eq, Complex.exp_add, he, her]
    simp only [finiteMultiplier, Finset.prod_insert hp]
    ring

/-- All local Taylor logarithms converge on one common right half-plane. -/
theorem exists_finite_log_halfplane (S : Finset ℕ) (W : ℕ → Multiset ℂ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, B < s.re →
      ∀ p ∈ S, ∀ a ∈ W p, ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, le_rfl, fun _ _ p hp => by simp only [Finset.notMem_empty] at hp⟩
  | @insert p S hp ih =>
    obtain ⟨B, hB, hb⟩ := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    obtain ⟨C, hC, hc⟩ := exists_log_halfplane (hS p (Finset.mem_insert_self _ _)).one_lt (W p)
    refine ⟨max B C, hB.trans (le_max_left _ _), fun s hs q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hc s ((le_max_right _ _).trans_lt hs)
    · exact hb s ((le_max_left _ _).trans_lt hs) q hq

/-- Any absolutely convergent logarithm of finite prime edits has the canonical
coefficients at each edited prime power. -/
theorem finite_coeff_prime_pow_eq (S : Finset ℕ) (W : ℕ → Multiset ℂ)
    (hS : ∀ p ∈ S, p.Prime) {b : ℕ → ℂ} {B : ℝ}
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * finiteMultiplier S W s)
    {p : ℕ} (hp : p ∈ S) {k : ℕ} (hk : k ≠ 0) :
    b (p ^ k) = logCoeff p (W p) (p ^ k) := by
  rw [← finiteLogCoeff_prime_pow S W hS hp hk]
  obtain ⟨C, hC, hc⟩ := exists_finite_log_halfplane S W hS
  apply DirichletSeries.coeff_eq_of_exp_lSeries_eq (B := max B C)
  · exact fun s hs => (hb s ((le_max_left _ _).trans_lt hs)).1
  · intro s hs
    have hCs := (le_max_right B C).trans_lt hs
    exact (finiteLogCoeff_summable_exp S W hS (hC.trans_lt hCs) (hc s hCs)).1
  · intro s hs
    have hCs := (le_max_right B C).trans_lt hs
    exact (hb s ((le_max_left _ _).trans_lt hs)).2.trans
      (finiteLogCoeff_summable_exp S W hS (hC.trans_lt hCs) (hc s hCs)).2.symm
  · exact one_lt_pow₀ (hS p hp).one_lt hk

/-- Logarithmic positivity confines every local root of a finite prime edit to the unit disk. -/
theorem finite_norm_le_one_of_nonnegative_logarithm (S : Finset ℕ) (W : ℕ → Multiset ℂ)
    (hS : ∀ p ∈ S, p.Prime) {b : ℕ → ℂ} (hpos : ∀ n : ℕ, 0 ≤ (b n).re) {B : ℝ}
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * finiteMultiplier S W s) :
    ∀ p ∈ S, ∀ a ∈ W p, ‖a‖ ≤ 1 := by
  intro p hp
  apply norm_le_one_of_eventually_logCoeff_nonneg (hS p hp) (W p)
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [← finite_coeff_prime_pow_eq S W hS hb hp (by omega : k ≠ 0)]
  exact hpos _

end GaloisForLFunctions.SelbergClass.FiniteEuler
