import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Positive prime-tail translations and failure of continuation limits

Restore every Euler factor through `N` after replacing `s` by `s+t`. The resulting ordinary
Dirichlet coefficients are completely multiplicative, strictly positive, bounded by one for
`t >= 0`, and exactly one through `N`. Their weighted squared distance to the all-one source
tends to zero for every weight exponent above one-half, even for varying nonnegative shifts.

At shift two, every continued function is analytic and zero-free on `Re(s)>0`. Nevertheless,
these continuations do not converge to zeta at any real point in `(0,1)`: their values are
positive there, whereas zeta is negative. This is an explicit audit of a coefficient-only
continuation principle, derived from classical Euler products and the existing eta identity.
It supplies no new RH architecture and makes no novelty claim.
-/

open Complex Filter Finset
open scoped Topology

noncomputable section
namespace RHTower.PrimeTailTranslation

def primeWeight (N : ℕ) (t : ℝ) (p : ℕ) : ℝ :=
  if p ≤ N then 1 else (p : ℝ) ^ (-t)

def coefficient (N : ℕ) (t : ℝ) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else
    n.factorization.prod fun p k => primeWeight N t p ^ k
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
      Nat.factorization_mul hm hn,
      Finsupp.prod_add_index' (fun _ => by simp) (fun _ _ _ => by rw [pow_add])]

theorem coefficient_apply (N : ℕ) (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    coefficient N t n = n.factorization.prod fun p k => primeWeight N t p ^ k :=
  if_neg hn

theorem coefficient_prime (N : ℕ) (t : ℝ) {p : ℕ} (hp : p.Prime) :
    coefficient N t p = primeWeight N t p := by
  rw [coefficient_apply N t hp.ne_zero, hp.factorization,
    Finsupp.prod_single_index (by simp), pow_one]

theorem primeWeight_pos (N : ℕ) (t : ℝ) {p : ℕ} (hp : 0 < p) :
    0 < primeWeight N t p := by
  unfold primeWeight
  split_ifs
  · exact zero_lt_one
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hp) _

theorem primeWeight_le_one (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : 0 < p) :
    primeWeight N t p ≤ 1 := by
  unfold primeWeight
  split_ifs
  · exact le_rfl
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (neg_nonpos.mpr ht)

theorem coefficient_pos (N : ℕ) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < coefficient N t n := by
  rw [coefficient_apply N t hn.ne', Finsupp.prod]
  apply Finset.prod_pos
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors (by
    rwa [Nat.support_factorization] at hp)
  exact pow_pos (primeWeight_pos N t hprime.pos) _

theorem coefficient_le_one (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    coefficient N t n ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [coefficient_apply N t hn, Finsupp.prod]
  apply Finset.prod_le_one
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp)
    exact pow_nonneg (primeWeight_pos N t hprime.pos).le _
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp)
    exact pow_le_one₀ (primeWeight_pos N t hprime.pos).le (primeWeight_le_one N ht hprime.pos)

theorem coefficient_nonneg (N : ℕ) (t : ℝ) (n : ℕ) : 0 ≤ coefficient N t n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (coefficient_pos N t (Nat.pos_of_ne_zero hn)).le

theorem coefficient_prefix (N : ℕ) (t : ℝ) {n : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    coefficient N t n = 1 := by
  rw [coefficient_apply N t hn.ne', Finsupp.prod]
  apply Finset.prod_eq_one
  intro p hp
  have hpf : p ∈ n.primeFactors := by rwa [Nat.support_factorization] at hp
  have hpN := (Nat.le_of_mem_primeFactors hpf).trans hN
  simp [primeWeight, hpN]

def smallPrimes (N : ℕ) : Finset Nat.Primes :=
  ((Set.finite_Iic N).preimage
    (f := fun p : Nat.Primes => (p : ℕ))
    (Set.injOn_of_injective (fun _ _ h => Subtype.ext h))).toFinset

@[simp] theorem mem_smallPrimes (N : ℕ) (p : Nat.Primes) :
    p ∈ smallPrimes N ↔ (p : ℕ) ≤ N := by simp [smallPrimes]

def correction (N : ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ smallPrimes N,
    (1 - ((p : ℕ) : ℂ) ^ (-(s + t))) / (1 - ((p : ℕ) : ℂ) ^ (-s))

def continued (N : ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + t) * correction N t s

theorem eulerDenominator_ne_zero {p : Nat.Primes} {s : ℂ} (hs : 0 < s.re) :
    1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (neg_neg_of_pos hs)
  intro h
  have heq : ((p : ℕ) : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  simp [heq] at hnorm

theorem correction_ne_zero (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 0 < s.re) : correction N t s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact div_ne_zero (eulerDenominator_ne_zero (by simpa using add_pos_of_pos_of_nonneg hs ht))
    (eulerDenominator_ne_zero hs)

theorem continued_zero_iff (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 0 < s.re) : continued N t s = 0 ↔ riemannZeta (s + t) = 0 := by
  rw [continued, mul_eq_zero]
  exact or_iff_left (correction_ne_zero N ht hs)

def summand (N : ℕ) (t : ℝ) {s : ℂ} (_hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (coefficient N t n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← Complex.ofReal_natCast]
    simp only [map_mul, Complex.ofReal_mul, Nat.cast_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

theorem summand_summable (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖summand N t (ne_zero_of_one_lt_re hs) n‖) := by
  apply (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  change ‖(coefficient N t n : ℂ) * (n : ℂ) ^ (-s)‖ ≤ ‖(n : ℂ) ^ (-s)‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coefficient_nonneg N t n)]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_le_one N ht n)

theorem term_eq_summand (N : ℕ) (t : ℝ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (fun n => (coefficient N t n : ℂ)) s n = summand N t hs n := by
  simp [LSeries.term_of_ne_zero' hs, summand, Complex.cpow_neg, div_eq_mul_inv]

theorem lSeriesSummable (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coefficient N t n : ℂ)) s := by
  unfold LSeriesSummable
  change Summable (fun n => LSeries.term (fun n => (coefficient N t n : ℂ)) s n)
  simp_rw [term_eq_summand N t (ne_zero_of_one_lt_re hs)]
  exact (summand_summable N ht hs).of_norm

theorem hasProd_coefficients (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1 - (primeWeight N t p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => (coefficient N t n : ℂ)) s) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (f := summand N t (ne_zero_of_one_lt_re hs)) (summand_summable N ht hs)
  have heq : ∀ p : Nat.Primes,
      summand N t (ne_zero_of_one_lt_re hs) p =
        (primeWeight N t p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) := by
    intro p
    change (coefficient N t p : ℂ) * _ = _
    rw [coefficient_prime N t p.2]
  simpa only [LSeries, term_eq_summand N t (ne_zero_of_one_lt_re hs), heq] using h

theorem primeWeight_mul_cpow (N : ℕ) (t : ℝ) (p : Nat.Primes) (s : ℂ) :
    (primeWeight N t p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) =
      if (p : ℕ) ≤ N then ((p : ℕ) : ℂ) ^ (-s) else ((p : ℕ) : ℂ) ^ (-(s + t)) := by
  unfold primeWeight
  split_ifs with h
  · simp
  · rw [Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
    push_cast
    rw [← Complex.cpow_add _ _ (by exact_mod_cast p.2.ne_zero)]
    congr 1
    ring

theorem lSeries_eq_continued (N : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (coefficient N t n : ℂ)) s = continued N t s := by
  have hst : 1 < (s + t).re := by simpa using add_lt_add_of_lt_of_le hs ht
  let g : Nat.Primes → ℂ := fun p => if (p : ℕ) ≤ N then
    (1 - ((p : ℕ) : ℂ) ^ (-(s + t))) / (1 - ((p : ℕ) : ℂ) ^ (-s)) else 1
  have hg : HasProd g (correction N t s) := by
    have hg' : HasProd g (∏ p ∈ smallPrimes N, g p) :=
      hasProd_prod_of_ne_finset_one (by
        intro p hp
        have hpN : ¬ (p : ℕ) ≤ N := by simpa using hp
        simp [g, hpN])
    convert hg' using 1
    apply Finset.prod_congr rfl
    intro p hp
    simp [g, (mem_smallPrimes N p).mp hp]
  have hprod := (riemannZeta_eulerProduct_hasProd hst).mul hg
  have hshape : (fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-(s + t)))⁻¹ * g p) =
      (fun p : Nat.Primes => (1 - (primeWeight N t p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
    funext p
    rw [primeWeight_mul_cpow]
    dsimp [g]
    split_ifs
    · have hn := eulerDenominator_ne_zero (p := p) (lt_trans (by norm_num) hst)
      field_simp
    · simp
  rw [hshape] at hprod
  exact (hasProd_coefficients N ht hs).unique hprod

def squaredDistance (N : ℕ) (t sigma : ℝ) : ℝ :=
  ∑' k : ℕ, (coefficient N t (k + 1) - 1) ^ 2 / ((k + 1 : ℕ) : ℝ) ^ (2 * sigma)

theorem errorTerm_bounds (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (sigma : ℝ) (k : ℕ) :
    0 ≤ (coefficient N t (k + 1) - 1) ^ 2 / ((k + 1 : ℕ) : ℝ) ^ (2 * sigma) ∧
    (coefficient N t (k + 1) - 1) ^ 2 / ((k + 1 : ℕ) : ℝ) ^ (2 * sigma) ≤
      1 / ((k + 1 : ℕ) : ℝ) ^ (2 * sigma) := by
  have h0 := coefficient_nonneg N t (k + 1)
  have h1 := coefficient_le_one N ht (k + 1)
  have hs : (coefficient N t (k + 1) - 1) ^ 2 ≤ 1 := by nlinarith
  constructor
  · positivity
  · exact div_le_div_of_nonneg_right hs (Real.rpow_nonneg (by positivity) _)

/-- Weighted squared coefficient errors vanish even for arbitrary nonnegative shift schedules.
This is a coefficient statement; it does not assert convergence of the continued functions. -/
theorem squaredDistance_tendsto_zero (t : ℕ → ℝ) (ht : ∀ N, 0 ≤ t N)
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Tendsto (fun N => squaredDistance N (t N) sigma) atTop (𝓝 0) := by
  have hb : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ (2 * sigma)) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * sigma)).comp_injective
      (fun _ _ h => by omega)
  have hp : ∀ k : ℕ, Tendsto (fun N =>
      (coefficient N (t N) (k + 1) - 1) ^ 2 / ((k + 1 : ℕ) : ℝ) ^ (2 * sigma))
      atTop (𝓝 (0 : ℝ)) := by
    intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k + 1)] with N hN
    simp [coefficient_prefix N (t N) (Nat.succ_pos k) hN]
  have h := tendsto_tsum_of_dominated_convergence hb hp (Filter.Eventually.of_forall (by
    intro N k
    rw [Real.norm_eq_abs, abs_of_nonneg (errorTerm_bounds N (ht N) sigma k).1]
    exact (errorTerm_bounds N (ht N) sigma k).2))
  simpa [squaredDistance] using h

theorem correction_differentiableAt (N : ℕ) (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (correction N t) s := by
  apply DifferentiableAt.fun_finsetProd
  intro p _
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hnum : DifferentiableAt ℂ
      (fun z : ℂ => 1 - ((p : ℕ) : ℂ) ^ (-(z + t))) s :=
    (differentiableAt_const (1 : ℂ)).sub
      ((differentiableAt_id.add_const (t : ℂ)).neg.const_cpow (Or.inl hp))
  have hden : DifferentiableAt ℂ
      (fun z : ℂ => 1 - ((p : ℕ) : ℂ) ^ (-z)) s :=
    (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.neg.const_cpow (Or.inl hp))
  exact hnum.div hden (eulerDenominator_ne_zero hs)

theorem continued_two_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (continued N 2) {s : ℂ | 0 < s.re} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have hs2 : s + (2 : ℝ) ≠ (1 : ℂ) := by
    intro heq
    have := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at this
    dsimp at hs
    linarith
  exact ((differentiableAt_riemannZeta hs2).comp s
    (differentiableAt_id.add_const (2 : ℂ))).mul (correction_differentiableAt N 2 hs)

/-- Restoring any finite Euler prefix after shifting by two leaves no positive-half-plane zero. -/
theorem continued_two_ne_zero (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    continued N 2 s ≠ 0 := by
  rw [continued]
  refine mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re ?_) (correction_ne_zero N (by norm_num) hs)
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

private theorem nat_cpow_neg_real (p : ℕ) (a : ℝ) :
    (p : ℂ) ^ (-(a : ℂ)) = (((p : ℝ) ^ (-a) : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow (Nat.cast_nonneg p) (-a)).symm

theorem continued_two_real_pos (N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < (continued N 2 (sigma : ℂ)).re := by
  let g : ℝ := ∏ p ∈ smallPrimes N,
    (1 - ((p : ℕ) : ℝ) ^ (-(sigma + 2))) / (1 - ((p : ℕ) : ℝ) ^ (-sigma))
  have hg : correction N 2 (sigma : ℂ) = (g : ℂ) := by
    unfold correction g
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro p _
    rw [show (sigma : ℂ) + (2 : ℝ) = ((sigma + 2 : ℝ) : ℂ) by push_cast; rfl,
      nat_cpow_neg_real, nat_cpow_neg_real]
    push_cast
    rfl
  have hgpos : 0 < g := by
    apply Finset.prod_pos
    intro p _
    have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    apply div_pos
    · exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))
    · exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))
  rw [continued, hg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply mul_pos _ hgpos
  have hz := riemannZeta_re_pos_of_one_lt (by linarith : 1 < sigma + 2)
  simpa only [Complex.ofReal_add, Complex.ofReal_ofNat] using hz

/-- The continuation limit fails even at every nonzero real strip value of zeta. Thus the
failure is not a detector for zeta zeros or for their horizontal location. -/
theorem continued_not_tendsto_real_strip {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    ¬ Tendsto (fun N => continued N 2 (sigma : ℂ)) atTop (𝓝 (riemannZeta (sigma : ℂ))) := by
  intro h
  have hre := (Complex.continuous_re.tendsto (riemannZeta (sigma : ℂ))).comp h
  have hnonneg : 0 ≤ (riemannZeta (sigma : ℂ)).re :=
    ge_of_tendsto hre (Filter.Eventually.of_forall (fun N => (continued_two_real_pos N h0).le))
  obtain ⟨x, hx, hxeq⟩ := RHTower.riemannZeta_real_strip_neg h0 h1
  rw [hxeq, Complex.ofReal_re] at hnonneg
  exact (not_lt_of_ge hnonneg) hx

/-- A closed positive arithmetic approximation with zero-free analytic continuations.
The approximants retain every finite prefix and converge in every indicated weighted coefficient
norm. No convergence of their analytic continuations in the strip is asserted. -/
theorem positive_zero_free_tail_approximation :
    (∀ N n : ℕ, 0 < n → 0 < coefficient N 2 n ∧ coefficient N 2 n ≤ 1) ∧
    (∀ N n : ℕ, 0 < n → n ≤ N → coefficient N 2 n = 1) ∧
    (∀ N : ℕ, DifferentiableOn ℂ (continued N 2) {s : ℂ | 0 < s.re}) ∧
    (∀ (N : ℕ) (s : ℂ), 0 < s.re → continued N 2 s ≠ 0) ∧
    (∀ (N : ℕ) (s : ℂ), 1 < s.re →
      LSeriesSummable (fun n => (coefficient N 2 n : ℂ)) s ∧
      LSeries (fun n => (coefficient N 2 n : ℂ)) s = continued N 2 s) ∧
    (∀ sigma : ℝ, 1 / 2 < sigma →
      Tendsto (fun N => squaredDistance N 2 sigma) atTop (𝓝 0)) ∧
    (∀ sigma : ℝ, 0 < sigma → sigma < 1 →
      ¬ Tendsto (fun N => continued N 2 (sigma : ℂ)) atTop (𝓝 (riemannZeta (sigma : ℂ)))) := by
  refine ⟨?_, ?_, continued_two_differentiableOn, ?_, ?_, ?_, ?_⟩
  · intro N n hn
    exact ⟨coefficient_pos N 2 hn, coefficient_le_one N (by norm_num) n⟩
  · intro N n hn hN
    exact coefficient_prefix N 2 hn hN
  · intro N s hs
    exact continued_two_ne_zero N hs
  · intro N s hs
    exact ⟨lSeriesSummable N (by norm_num) hs, lSeries_eq_continued N (by norm_num) hs⟩
  · intro sigma hsigma
    exact squaredDistance_tendsto_zero (fun _ => 2) (fun _ => by norm_num) hsigma
  · intro sigma h0 h1
    exact continued_not_tendsto_real_strip h0 h1

end RHTower.PrimeTailTranslation
