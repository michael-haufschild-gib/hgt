import GaloisForLFunctions.RHTower.EulerDeletionPrimeCountAmplification
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Prime-count endpoint variance in the physical carrier

The exact divisor convolution of count-damped Möbius coefficients is
`(1-u)^omega(n)`. Its derivative at one is the negative prime-power
indicator. Thus the physical endpoint derivative has cell numerator
`k * jetHarmonic N + primePowerCount k` for every `k <= N`.

Completing the finite square eliminates the harmonic scalar and exposes a
nonnegative, monotone prime-power variance. This variance bounds the actual
full carrier energy from below and has an exact pairwise determinant formula.
The complete infinite tail remains in the carrier energy.

These theorems are unconditional finite identities and inequalities. The
asymptotic variance evaluation and endpoint energy-curvature argument in the
research card are not formalized here. This module does not prove RH.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction Filter Topology
open scoped BigOperators
namespace RHTower.PrimeCountDamping
open Sieve

/-- The literal coefficient derivative at the arithmetic endpoint. -/
def jetCoeff (n : ℕ) : ℝ := (moebius n : ℝ) * n.primeFactors.card

/-- The derivative in the original physical carrier. -/
def endpointJet (N : ℕ) : BDCarrier :=
  ∑ n ∈ Icc 1 N, (jetCoeff n : ℂ) • bdGen (1 / (n : ℝ))

/-- The harmonic scalar of the endpoint derivative. -/
def jetHarmonic (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, jetCoeff n / n

/-- Prime powers are counted once, independently of their exponent. -/
def primePowerCount (k : ℕ) : ℝ := ∑ n ∈ Icc 1 k, if IsPrimePow n then 1 else 0

private theorem prime_pow_sum (u : ℝ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (∑ j ∈ range (i+2), fullPrimeDampedMoebius u (p^j)) = 1-u := by
  induction i with
  | zero => simp [Finset.sum_range_succ,fullPrimeDampedMoebius,moebius_apply_prime hp,hp.primeFactors,sub_eq_add_neg]
  | succ i ih =>
    rw [show i+1+2=(i+2)+1 by omega,Finset.sum_range_succ,ih]
    simp [fullPrimeDampedMoebius,moebius_apply_prime_pow hp (by omega : i+2 ≠ 0),
      show i+2 ≠ 1 by omega]

/-- Complete divisor convolution turns prime-count damping into a positive power. -/
theorem sum_divisors_damped (u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, fullPrimeDampedMoebius u d) = (1-u)^n.primeFactors.card := by
  let f : ArithmeticFunction ℝ := ⟨fullPrimeDampedMoebius u, by simp [fullPrimeDampedMoebius]⟩
  have hf : f.IsMultiplicative := ⟨by simp [f,fullPrimeDampedMoebius],
    fun {m n} h => fullPrimeDampedMoebius_mul h⟩
  have hz : ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).IsMultiplicative :=
    isMultiplicative_zeta.natCast
  have he := (hz.mul hf).multiplicative_factorization _ hn
  rw [coe_zeta_mul_apply,Finsupp.prod,Nat.support_factorization] at he
  change (∑ d ∈ n.divisors,fullPrimeDampedMoebius u d) = _ at he
  rw [he]
  calc
    _ = ∏ _p ∈ n.primeFactors,(1-u) := by
      apply prod_congr rfl
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hk := Nat.Prime.factorization_pos_of_dvd hprime hn (Nat.dvd_of_mem_primeFactors hp)
      rw [coe_zeta_mul_apply,Nat.sum_divisors_prime_pow hprime]
      change (∑ j ∈ range (n.factorization p+1),fullPrimeDampedMoebius u (p^j)) = _
      obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.factorization p ≠ 0)
      rw [hi]
      exact prime_pow_sum u hprime i
    _ = _ := by simp

private theorem damped_deriv (n : ℕ) :
    HasDerivAt (fun u : ℝ => fullPrimeDampedMoebius u n) (jetCoeff n) 1 := by
  simpa [fullPrimeDampedMoebius,jetCoeff,Pi.pow_apply,id_eq] using
    ((hasDerivAt_id (1 : ℝ)).pow n.primeFactors.card).const_mul (moebius n : ℝ)

/-- The endpoint divisor derivative is supported exactly on prime powers. -/
theorem sum_divisors_jet {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,jetCoeff d) = if IsPrimePow n then -1 else 0 := by
  have hl := HasDerivAt.fun_sum (u := n.divisors) (fun d _ => damped_deriv d)
  have hr : HasDerivAt (fun u : ℝ => (1-u)^n.primeFactors.card)
      (if n.primeFactors.card=1 then -1 else 0) 1 := by
    have h := ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 1)).pow n.primeFactors.card
    by_cases h0 : n.primeFactors.card=0
    · simpa [h0,Pi.one_def] using h
    by_cases h1 : n.primeFactors.card=1
    · convert! h using 1
      simp [h1]
    · have h2 : n.primeFactors.card-1 ≠ 0 := by omega
      convert! h using 1
      simp [h1,h2]
  have he : (fun u => ∑ d ∈ n.divisors,fullPrimeDampedMoebius u d) =
      (fun u : ℝ => (1-u)^n.primeFactors.card) := funext fun u => sum_divisors_damped u hn
  rw [he] at hl
  simpa only [isPrimePow_iff_card_primeFactors_eq_one] using hl.unique hr

/-- The entire completed floor column is the negative prime-power count. -/
theorem jet_floor_sum (k : ℕ) :
    (∑ n ∈ Icc 1 k,jetCoeff n * (k/n : ℕ)) = -primePowerCount k := by
  have h := sum_divisors_swap k (fun d _ => jetCoeff d)
  have hl : (∑ m ∈ Icc 1 k,∑ d ∈ m.divisors,jetCoeff d) = -primePowerCount k := by
    rw [primePowerCount,← sum_neg_distrib]
    apply sum_congr rfl
    intro m hm
    rw [sum_divisors_jet (by have := (mem_Icc.mp hm).1; omega)]
    split_ifs <;> ring
  rw [hl] at h
  simpa [mul_comm] using h.symm

/-- Exact cell numerator of the full endpoint derivative. -/
def jetCell (N k : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N,jetCoeff n * ((k%n : ℕ) : ℝ) / n

/-- Below the coefficient cutoff, one scalar and one prime-power count remain. -/
theorem jetCell_eq {N k : ℕ} (hk : k ≤ N) :
    jetCell N k = (k : ℝ)*jetHarmonic N+primePowerCount k := by
  have hfloor : (∑ n ∈ Icc 1 N,jetCoeff n*(k/n : ℕ)) = -primePowerCount k := by
    rw [← jet_floor_sum]
    symm
    apply sum_subset (fun n hn => mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hk⟩)
    intro n hn hnk
    have hkn : k<n := by have := (mem_Icc.mp hn).1; simp only [mem_Icc,not_and] at hnk; omega
    simp [Nat.div_eq_of_lt hkn]
  have hcell (n : ℕ) (hn : n ∈ Icc 1 N) :
      jetCoeff n*((k%n : ℕ) : ℝ)/n = (k : ℝ)*(jetCoeff n/n)-jetCoeff n*(k/n : ℕ) := by
    have hn0 : (n : ℝ) ≠ 0 := by have := (mem_Icc.mp hn).1; exact_mod_cast (show n≠0 by omega)
    have hmod := congrArg (fun x : ℕ => (x : ℝ)) (Nat.div_add_mod k n)
    push_cast at hmod
    rw [show ((k%n : ℕ) : ℝ)=(k : ℝ)-(n : ℝ)*(k/n : ℕ) by linarith]
    field_simp
  rw [jetCell,sum_congr rfl hcell,sum_sub_distrib,← mul_sum,show
    (∑ n ∈ Icc 1 N,jetCoeff n/n)=jetHarmonic N from rfl,hfloor]
  ring


/-- The finite coefficient derivative is the derivative in the unchanged carrier norm. -/
theorem hasDerivAt_source_one (N : ℕ) :
    HasDerivAt (source N) (endpointJet N) 1 := by
  have h := HasDerivAt.fun_sum (u := Icc 1 N) (fun n _ =>
    (damped_deriv n).smul_const (bdGen (1/(n : ℝ))))
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
  convert! h using 1

/-- Every physical cell, including the infinite tail, contributes its signed square. -/
theorem hasSum_endpointJet_energy (N : ℕ) :
    HasSum (fun j : ℕ => jetCell N (j+1)^(2 : ℕ)/(((j : ℝ)+1)*((j : ℝ)+2)))
      (‖endpointJet N‖^(2 : ℕ)) := by
  have h := hasSum_sum (s := Icc 1 N) (fun m hm =>
    hasSum_sum (s := Icc 1 N) (fun n hn =>
      (hasSum_bdGram_discrete (mem_Icc.mp hm).1 (mem_Icc.mp hn).1).mul_left
        (jetCoeff m*jetCoeff n)))
  rw [bdGram_quadraticForm_eq_norm_sq] at h
  change HasSum _ (‖endpointJet N‖^(2 : ℕ)) at h
  convert h using 1
  funext j
  simp only [jetCell,pow_two,sum_mul,mul_sum,sum_div]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The endpoint derivative dominates its entire initial prime-power fluctuation. -/
theorem endpointJet_prefix_lower (N : ℕ) :
    (∑ k ∈ Icc 1 N,((k : ℝ)*jetHarmonic N+primePowerCount k)^(2 : ℕ)/
      ((k : ℝ)*((k : ℝ)+1))) ≤ ‖endpointJet N‖^(2 : ℕ) := by
  have hb := sum_le_hasSum (range N) (fun j _ => by positivity)
    (hasSum_endpointJet_energy N)
  have he : (∑ j ∈ range N,jetCell N (j+1)^(2 : ℕ)/(((j : ℝ)+1)*((j : ℝ)+2))) =
      ∑ k ∈ Icc 1 N,((k : ℝ)*jetHarmonic N+primePowerCount k)^(2 : ℕ)/
        ((k : ℝ)*((k : ℝ)+1)) := by
    apply sum_bij (fun j _ => j+1)
    · intro j hj
      exact mem_Icc.mpr ⟨by omega,by have := mem_range.mp hj; omega⟩
    · intro i _ j _ hij
      omega
    · intro k hk
      refine ⟨k-1,mem_range.mpr (by have := mem_Icc.mp hk; omega),?_⟩
      have := mem_Icc.mp hk
      omega
    · intro j hj
      rw [jetCell_eq (by have := mem_range.mp hj; omega : j+1 ≤ N)]
      push_cast
      ring
  rwa [he] at hb

/-- Quadratic coefficient of the removable harmonic scalar. -/
def jetVarianceA (N : ℕ) : ℝ := ∑ k ∈ Icc 1 N,(k : ℝ)/((k : ℝ)+1)

/-- Linear coefficient of the removable harmonic scalar. -/
def jetVarianceB (N : ℕ) : ℝ := ∑ k ∈ Icc 1 N,primePowerCount k/((k : ℝ)+1)

/-- Uncentered prime-power square mass. -/
def jetVarianceC (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N,primePowerCount k^(2 : ℕ)/((k : ℝ)*((k : ℝ)+1))

/-- Spatial prime-power variance after removing the best possible scalar. -/
def jetVariance (N : ℕ) : ℝ := jetVarianceC N-jetVarianceB N^(2 : ℕ)/jetVarianceA N

private theorem prefix_quadratic (N : ℕ) (h : ℝ) :
    (∑ k ∈ Icc 1 N,((k : ℝ)*h+primePowerCount k)^(2 : ℕ)/((k : ℝ)*((k : ℝ)+1))) =
      jetVarianceA N*h^(2 : ℕ)+2*jetVarianceB N*h+jetVarianceC N := by
  simp only [jetVarianceA,jetVarianceB,jetVarianceC,sum_mul,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hk0 : (k : ℝ) ≠ 0 := by have := (mem_Icc.mp hk).1; exact_mod_cast (show k≠0 by omega)
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

private theorem varianceA_pos {N : ℕ} (hN : 1 ≤ N) : 0<jetVarianceA N := by
  apply sum_pos' (fun k _ => by positivity)
  exact ⟨1,mem_Icc.mpr ⟨le_rfl,hN⟩,by norm_num⟩

/-- Exact square completion, retaining every physical cell up to the cutoff. -/
theorem jet_prefix_square_completion {N : ℕ} (hN : 1 ≤ N) (h : ℝ) :
    (∑ k ∈ Icc 1 N,((k : ℝ)*h+primePowerCount k)^(2 : ℕ)/((k : ℝ)*((k : ℝ)+1))) =
      jetVariance N+jetVarianceA N*(h+jetVarianceB N/jetVarianceA N)^(2 : ℕ) := by
  rw [prefix_quadratic,jetVariance]
  have hA := ne_of_gt (varianceA_pos hN)
  field_simp
  ring

/-- A scalar-independent lower bound on the actual endpoint derivative energy. -/
theorem jetVariance_le_endpointJet_energy (N : ℕ) : jetVariance N ≤ ‖endpointJet N‖^(2 : ℕ) := by
  by_cases hN : 1 ≤ N
  · have h := endpointJet_prefix_lower N
    rw [jet_prefix_square_completion hN] at h
    exact le_trans (le_add_of_nonneg_right (mul_nonneg (varianceA_pos hN).le (sq_nonneg _))) h
  · have h0 : N=0 := by omega
    simp [h0,jetVariance,jetVarianceA,jetVarianceB,jetVarianceC,endpointJet]

/-- The lower bound is sharp among all choices of the finite harmonic scalar. -/
theorem jetVariance_eq_minimum (N : ℕ) :
    jetVariance N = ∑ k ∈ Icc 1 N,
      ((k : ℝ)*(-jetVarianceB N/jetVarianceA N)+primePowerCount k)^(2 : ℕ)/
        ((k : ℝ)*((k : ℝ)+1)) := by
  by_cases hN : 1 ≤ N
  · rw [jet_prefix_square_completion hN]
    simp [neg_div]
  · have h0 : N=0 := by omega
    simp [h0,jetVariance,jetVarianceA,jetVarianceB,jetVarianceC]

/-- The new invariant is a nonnegative finite prime-power variance. -/
theorem jetVariance_nonneg (N : ℕ) : 0 ≤ jetVariance N := by
  rw [jetVariance_eq_minimum]
  apply sum_nonneg
  intro k hk
  positivity


/-- The optimal finite variance increases when more physical cells are retained. -/
theorem jetVariance_monotone : Monotone jetVariance := by
  intro N M hNM
  let h : ℝ := -jetVarianceB M/jetVarianceA M
  have hmin : jetVariance N ≤ ∑ k ∈ Icc 1 N,
      ((k : ℝ)*h+primePowerCount k)^(2 : ℕ)/((k : ℝ)*((k : ℝ)+1)) := by
    by_cases hN : 1 ≤ N
    · rw [jet_prefix_square_completion hN]
      exact le_add_of_nonneg_right (mul_nonneg (varianceA_pos hN).le (sq_nonneg _))
    · have h0 : N=0 := by omega
      simp [h0,jetVariance,jetVarianceA,jetVarianceB,jetVarianceC]
  calc
    jetVariance N ≤ _ := hmin
    _ ≤ ∑ k ∈ Icc 1 M,((k : ℝ)*h+primePowerCount k)^(2 : ℕ)/((k : ℝ)*((k : ℝ)+1)) := by
      apply sum_le_sum_of_subset_of_nonneg (fun k hk =>
        mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hNM⟩)
      intro k _ _
      positivity
    _ = jetVariance M := (jetVariance_eq_minimum M).symm

/-- Pairwise spatial mismatch is exactly the variance after scalar elimination. -/
theorem jetVariance_pairwise (N : ℕ) :
    2*jetVarianceA N*jetVariance N = ∑ i ∈ Icc 1 N,∑ j ∈ Icc 1 N,
      ((i : ℝ)*primePowerCount j-(j : ℝ)*primePowerCount i)^(2 : ℕ)/
        ((i : ℝ)*((i : ℝ)+1)*(j : ℝ)*((j : ℝ)+1)) := by
  have hpair : (∑ i ∈ Icc 1 N,∑ j ∈ Icc 1 N,
      ((i : ℝ)*primePowerCount j-(j : ℝ)*primePowerCount i)^(2 : ℕ)/
        ((i : ℝ)*((i : ℝ)+1)*(j : ℝ)*((j : ℝ)+1))) =
      2*jetVarianceA N*jetVarianceC N-2*jetVarianceB N^(2 : ℕ) := by
    rw [show 2*jetVarianceA N*jetVarianceC N-2*jetVarianceB N^(2 : ℕ) =
      jetVarianceA N*jetVarianceC N+jetVarianceC N*jetVarianceA N-
        2*(jetVarianceB N*jetVarianceB N) by ring]
    simp only [jetVarianceA,jetVarianceB,jetVarianceC,sum_mul,mul_sum,
      ← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    have hi0 : (i : ℝ) ≠ 0 := by have := (mem_Icc.mp hi).1; exact_mod_cast (show i≠0 by omega)
    have hj0 : (j : ℝ) ≠ 0 := by have := (mem_Icc.mp hj).1; exact_mod_cast (show j≠0 by omega)
    have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
    have hj1 : (j : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hpair,jetVariance]
  by_cases hN : 1 ≤ N
  · have hA := ne_of_gt (varianceA_pos hN)
    field_simp
  · have h0 : N=0 := by omega
    simp [h0,jetVarianceA,jetVarianceB,jetVarianceC]

end RHTower.PrimeCountDamping
