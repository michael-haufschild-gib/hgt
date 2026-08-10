import Mathlib
import GaloisForLFunctions.HTGeometry.QPochhammer

/-!
# The global Euler q-Gamma random-integer law

At every prime the local q-Gamma occupation law has nome `q_p = p^{-σ}`.  Composing the primes by
independence and reading the outcome through unique factorisation gives an explicit probability law
on the positive integers:

`P_σ(m) = C_σ · m^{-σ} / ∏_p (q_p;q_p)_{v_p(m)}`,  `C_σ = ∏_p (q_p;q_p)_∞ > 0`.

The arithmetic weight is multiplicative with local Euler factor `(q_p;q_p)_∞⁻¹`, so mathlib's Euler
product turns the local normalisations into the global one.  Summability comes from the uniform
denominator bound `(q;q)_n ≥ exp(−4q)`, valid because every nome is at most `1/2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The convergence parameter and the local nomes -/

/-- The convergence parameter of the global Euler q-Gamma process. -/
structure EulerSigma where
  val : ℝ
  one_lt : 1 < val

namespace EulerSigma

theorem pos (σ : EulerSigma) : 0 < σ.val := lt_trans zero_lt_one σ.one_lt

end EulerSigma

/-- The local nome `q_n = n^{-σ}`. -/
def eqgQ (σ : EulerSigma) (n : ℕ) : ℝ := (n : ℝ) ^ (-σ.val)

theorem eqgQ_pos (σ : EulerSigma) {n : ℕ} (hn : 0 < n) : 0 < eqgQ σ n :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem eqgQ_lt_one (σ : EulerSigma) {n : ℕ} (hn : 2 ≤ n) : eqgQ σ n < 1 := by
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith [σ.pos])
  exact_mod_cast lt_of_lt_of_le one_lt_two hn

theorem eqgQ_le_half (σ : EulerSigma) {n : ℕ} (hn : 2 ≤ n) : eqgQ σ n ≤ 1 / 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hstep : eqgQ σ n ≤ (n : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith [σ.one_lt])
  rw [Real.rpow_neg_one] at hstep
  have hinv : ((n : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left one_pos.le (by linarith) hn2
  linarith

/-- The local nome at a prime, as a `RealEulerNome`. -/
def eqgNome (σ : EulerSigma) (p : Nat.Primes) : RealEulerNome where
  val := eqgQ σ (p : ℕ)
  pos := eqgQ_pos σ p.2.pos
  lt_one := eqgQ_lt_one σ p.2.two_le

@[simp] theorem eqgNome_val (σ : EulerSigma) (p : Nat.Primes) :
    (eqgNome σ p).val = eqgQ σ (p : ℕ) := rfl

/-! ## The uniform denominator bound -/

theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h2 : (0 : ℝ) < 1 + 2 * x := by linarith
  have h1 : (1 : ℝ) + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x)
    linarith
  rw [Real.exp_neg]
  refine le_trans (by exact inv_anti₀ h2 h1) ?_
  rw [inv_eq_one_div, div_le_iff₀ h2]
  nlinarith

/-- The local q-factorial as a function of a plain natural number. -/
def eqgLocalFactorial (σ : EulerSigma) (p n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - eqgQ σ p ^ (j + 1))

theorem eqgLocalFactorial_eq (σ : EulerSigma) (p : Nat.Primes) (n : ℕ) :
    eqgLocalFactorial σ (p : ℕ) n = realQFactorial (eqgNome σ p) n := rfl

theorem eqgLocalFactorial_pos (σ : EulerSigma) {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    0 < eqgLocalFactorial σ p n := by
  refine Finset.prod_pos fun j _ => ?_
  have hq1 : eqgQ σ p < 1 := eqgQ_lt_one σ hp
  have hq0 : 0 < eqgQ σ p := eqgQ_pos σ (by omega)
  have : eqgQ σ p ^ (j + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  linarith

/-- **The uniform denominator bound** `(q;q)_n ≥ exp(−4q)` for a nome at most `1/2`. -/
theorem exp_le_eqgLocalFactorial (σ : EulerSigma) {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    Real.exp (-(4 * eqgQ σ p)) ≤ eqgLocalFactorial σ p n := by
  set q : ℝ := eqgQ σ p with hq
  have hq0 : 0 < q := eqgQ_pos σ (by omega)
  have hqh : q ≤ 1 / 2 := eqgQ_le_half σ hp
  have hstep : ∀ j ∈ Finset.range n, Real.exp (-(2 * q ^ (j + 1))) ≤ 1 - q ^ (j + 1) := by
    intro j _
    refine exp_neg_two_mul_le_one_sub (by positivity) ?_
    calc q ^ (j + 1) ≤ q ^ 1 := pow_le_pow_of_le_one hq0.le (by linarith) (by omega)
      _ = q := pow_one q
      _ ≤ 1 / 2 := hqh
  have hprod : ∏ j ∈ Finset.range n, Real.exp (-(2 * q ^ (j + 1)))
      ≤ ∏ j ∈ Finset.range n, (1 - q ^ (j + 1)) := by
    refine Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) hstep
  refine le_trans ?_ hprod
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hsum : ∑ j ∈ Finset.range n, q ^ (j + 1) ≤ 2 * q := by
    have hgeo : ∑ j ∈ Finset.range n, q ^ (j + 1) = q * ∑ j ∈ Finset.range n, q ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_succ, mul_comm]
    have hbound : ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ := by
      have hsummable : Summable fun j : ℕ => q ^ j :=
        summable_geometric_of_lt_one hq0.le (by linarith)
      have h1 := hsummable.sum_le_tsum (Finset.range n) (fun j _ => by positivity)
      rwa [tsum_geometric_of_lt_one hq0.le (by linarith)] at h1
    have hle : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ∑ j ∈ Finset.range n, q ^ (j + 1) = q * ∑ j ∈ Finset.range n, q ^ j := hgeo
      _ ≤ q * 2 := by nlinarith
      _ = 2 * q := by ring
  have hneg : ∑ j ∈ Finset.range n, -(2 * q ^ (j + 1))
      = -(2 * ∑ j ∈ Finset.range n, q ^ (j + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hneg]
  linarith

/-! ## The arithmetic weight -/

/-- The denominator `∏_{p ∣ m} (q_p;q_p)_{v_p(m)}` of the arithmetic weight. -/
def eqgDenom (σ : EulerSigma) (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors, eqgLocalFactorial σ p (m.factorization p)

theorem eqgDenom_pos (σ : EulerSigma) (m : ℕ) : 0 < eqgDenom σ m := by
  refine Finset.prod_pos fun p hp => ?_
  exact eqgLocalFactorial_pos σ (Nat.prime_of_mem_primeFactors hp).two_le _

theorem eqgDenom_one (σ : EulerSigma) : eqgDenom σ 1 = 1 := by
  rw [eqgDenom, Nat.primeFactors_one, Finset.prod_empty]

/-- **Equation (EQG.6), unnormalised.**  The arithmetic weight
`m^{-σ} / ∏_p (q_p;q_p)_{v_p(m)}`. -/
def eqgWeight (σ : EulerSigma) (m : ℕ) : ℝ :=
  if m = 0 then 0 else (m : ℝ) ^ (-σ.val) / eqgDenom σ m

@[simp] theorem eqgWeight_zero (σ : EulerSigma) : eqgWeight σ 0 = 0 := if_pos rfl

@[simp] theorem eqgWeight_one (σ : EulerSigma) : eqgWeight σ 1 = 1 := by
  rw [eqgWeight, if_neg one_ne_zero, eqgDenom_one, Nat.cast_one, Real.one_rpow, div_one]

theorem eqgWeight_nonneg (σ : EulerSigma) (m : ℕ) : 0 ≤ eqgWeight σ m := by
  rw [eqgWeight]
  split
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (eqgDenom_pos σ m).le

theorem eqgDenom_mul (σ : EulerSigma) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Nat.Coprime a b) : eqgDenom σ (a * b) = eqgDenom σ a * eqgDenom σ b := by
  rw [eqgDenom, eqgDenom, eqgDenom, Nat.primeFactors_mul ha hb,
    Finset.prod_union hab.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hzero : b.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun hdvd => ?_
      have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
      have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hdvd
      rw [hab] at hg
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.eq_one_of_dvd_one hg)
    rw [Nat.factorization_mul ha hb]
    simp only [Finsupp.coe_add, Pi.add_apply, hzero, Nat.add_zero]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hzero : a.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun hdvd => ?_
      have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
      have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hdvd hpb
      rw [hab] at hg
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.eq_one_of_dvd_one hg)
    rw [Nat.factorization_mul ha hb]
    simp only [Finsupp.coe_add, Pi.add_apply, hzero, Nat.zero_add]

theorem eqgWeight_mul (σ : EulerSigma) {a b : ℕ} (hab : Nat.Coprime a b) :
    eqgWeight σ (a * b) = eqgWeight σ a * eqgWeight σ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rw [eqgWeight, eqgWeight, eqgWeight, if_neg hab0, if_neg ha, if_neg hb,
    eqgDenom_mul σ ha hb hab, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  field_simp

theorem eqgWeight_prime_pow (σ : EulerSigma) (p : Nat.Primes) (e : ℕ) :
    eqgWeight σ ((p : ℕ) ^ e) = qGeometricCoefficient (eqgNome σ p) e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, eqgWeight_one, qGeometricCoefficient, realQFactorial]
    simp
  have hne : ((p : ℕ)) ^ e ≠ 0 := pow_ne_zero _ p.2.pos.ne'
  rw [eqgWeight, if_neg hne, eqgDenom, Nat.primeFactors_prime_pow he.ne' p.2,
    Finset.prod_singleton, p.2.factorization_pow]
  simp only [Finsupp.single_eq_same]
  rw [eqgLocalFactorial_eq, qGeometricCoefficient]
  congr 1
  rw [eqgNome_val, eqgQ, Nat.cast_pow,
    ← Real.rpow_natCast (((p : ℕ) : ℝ)) e,
    ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ.val)) e,
    ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_mul (Nat.cast_nonneg _)]
  ring_nf

/-! ## Summability -/

/-- The uniform tail constant `∑_n n^{-σ}`. -/
def eqgTail (σ : EulerSigma) : ℝ := ∑' n : ℕ, eqgQ σ n

theorem eqgQ_nonneg (σ : EulerSigma) (n : ℕ) : 0 ≤ eqgQ σ n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem summable_eqgQ (σ : EulerSigma) : Summable (eqgQ σ) := by
  have h : Summable fun n : ℕ => (((n : ℝ)) ^ σ.val)⁻¹ :=
    Real.summable_nat_rpow_inv.mpr σ.one_lt
  refine h.congr fun n => ?_
  rw [eqgQ, Real.rpow_neg (Nat.cast_nonneg n)]

theorem sum_eqgQ_le_tail (σ : EulerSigma) (S : Finset ℕ) :
    ∑ p ∈ S, eqgQ σ p ≤ eqgTail σ :=
  (summable_eqgQ σ).sum_le_tsum S (fun n _ => eqgQ_nonneg σ n)

/-- **The uniform denominator bound.** -/
theorem eqgDenom_lower (σ : EulerSigma) (m : ℕ) :
    Real.exp (-(4 * eqgTail σ)) ≤ eqgDenom σ m := by
  have hstep : ∀ p ∈ m.primeFactors,
      Real.exp (-(4 * eqgQ σ p)) ≤ eqgLocalFactorial σ p (m.factorization p) := by
    intro p hp
    exact exp_le_eqgLocalFactorial σ (Nat.prime_of_mem_primeFactors hp).two_le _
  have hprod : ∏ p ∈ m.primeFactors, Real.exp (-(4 * eqgQ σ p)) ≤ eqgDenom σ m :=
    Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) hstep
  refine le_trans ?_ hprod
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hneg : ∑ p ∈ m.primeFactors, -(4 * eqgQ σ p)
      = -(4 * ∑ p ∈ m.primeFactors, eqgQ σ p) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hneg]
  have := sum_eqgQ_le_tail σ m.primeFactors
  linarith

theorem eqgWeight_le (σ : EulerSigma) (m : ℕ) :
    eqgWeight σ m ≤ Real.exp (4 * eqgTail σ) * eqgQ σ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgWeight_zero]
    exact mul_nonneg (Real.exp_pos _).le (eqgQ_nonneg σ 0)
  rw [eqgWeight, if_neg hm]
  have hlow := eqgDenom_lower σ m
  have hpos := eqgDenom_pos σ m
  rw [div_le_iff₀ hpos]
  have hq : (0 : ℝ) ≤ eqgQ σ m := eqgQ_nonneg σ m
  have hexp : Real.exp (4 * eqgTail σ) * Real.exp (-(4 * eqgTail σ)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc (m : ℝ) ^ (-σ.val) = eqgQ σ m := rfl
    _ = eqgQ σ m * (Real.exp (4 * eqgTail σ) * Real.exp (-(4 * eqgTail σ))) := by
        rw [hexp, mul_one]
    _ ≤ eqgQ σ m * (Real.exp (4 * eqgTail σ) * eqgDenom σ m) := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        exact mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    _ = Real.exp (4 * eqgTail σ) * eqgQ σ m * eqgDenom σ m := by ring

theorem summable_eqgWeight (σ : EulerSigma) : Summable (eqgWeight σ) := by
  refine Summable.of_nonneg_of_le (eqgWeight_nonneg σ) (eqgWeight_le σ) ?_
  exact (summable_eqgQ σ).mul_left _

/-! ## The Euler product -/

/-- The prime product of the local normalisations converges to the total mass of the arithmetic
weight. -/
theorem eqgEulerProduct (σ : EulerSigma) :
    HasProd (fun p : Nat.Primes => (realQFactorialInf (eqgNome σ p))⁻¹)
      (∑' m : ℕ, eqgWeight σ m) := by
  have hloc : ∀ p : Nat.Primes, HasSum (fun e : ℕ => eqgWeight σ ((p : ℕ) ^ e))
      (realQFactorialInf (eqgNome σ p))⁻¹ := by
    intro p
    have hf : (fun e : ℕ => eqgWeight σ ((p : ℕ) ^ e))
        = qGeometricCoefficient (eqgNome σ p) := by
      funext e
      exact eqgWeight_prime_pow σ p e
    rw [hf]
    exact qGeometricCoefficient_hasSum (eqgNome σ p)
  have hbase := EulerProduct.eulerProduct_hasProd (f := eqgWeight σ) (eqgWeight_one σ)
    (fun {m n} h => eqgWeight_mul σ h)
    ((summable_eqgWeight σ).congr fun n => (Real.norm_of_nonneg (eqgWeight_nonneg σ n)).symm)
    (eqgWeight_zero σ)
  have hfun : (fun p : Nat.Primes => ∑' e : ℕ, eqgWeight σ ((p : ℕ) ^ e))
      = fun p : Nat.Primes => (realQFactorialInf (eqgNome σ p))⁻¹ := by
    funext p
    exact (hloc p).tsum_eq
  rw [hfun] at hbase
  exact hbase

/-- The total mass of the arithmetic weight. -/
def eqgTotal (σ : EulerSigma) : ℝ := ∑' m : ℕ, eqgWeight σ m

theorem eqgTotal_pos (σ : EulerSigma) : 0 < eqgTotal σ := by
  have h1 : ∑ n ∈ ({1} : Finset ℕ), eqgWeight σ n ≤ eqgTotal σ :=
    (summable_eqgWeight σ).sum_le_tsum {1} (fun n _ => eqgWeight_nonneg σ n)
  rw [Finset.sum_singleton, eqgWeight_one] at h1
  linarith

/-- **Equation (EQG.7).**  The normalising constant `C_σ = ∏_p (q_p;q_p)_∞ > 0`. -/
def eqgConst (σ : EulerSigma) : ℝ := (eqgTotal σ)⁻¹

theorem eqgConst_pos (σ : EulerSigma) : 0 < eqgConst σ := inv_pos.mpr (eqgTotal_pos σ)

theorem eqgConst_hasProd (σ : EulerSigma) :
    HasProd (fun p : Nat.Primes => realQFactorialInf (eqgNome σ p)) (eqgConst σ) := by
  have hne : (∑' m : ℕ, eqgWeight σ m) ≠ 0 := (eqgTotal_pos σ).ne'
  have h : Filter.Tendsto (fun s : Finset Nat.Primes =>
      ∏ p ∈ s, (realQFactorialInf (eqgNome σ p))⁻¹) atTop
      (nhds (∑' m : ℕ, eqgWeight σ m)) := eqgEulerProduct σ
  have h2 := h.inv₀ hne
  refine Filter.Tendsto.congr (fun s => ?_) h2
  rw [Finset.prod_inv_distrib, inv_inv]

/-- **Equation (EQG.6).**  The normalised random-integer law. -/
def eqgMass (σ : EulerSigma) (m : ℕ) : ℝ := eqgConst σ * eqgWeight σ m

theorem eqgMass_nonneg (σ : EulerSigma) (m : ℕ) : 0 ≤ eqgMass σ m :=
  mul_nonneg (eqgConst_pos σ).le (eqgWeight_nonneg σ m)

theorem eqgMass_pos (σ : EulerSigma) {m : ℕ} (hm : m ≠ 0) : 0 < eqgMass σ m := by
  refine mul_pos (eqgConst_pos σ) ?_
  rw [eqgWeight, if_neg hm]
  exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) _)
    (eqgDenom_pos σ m)

/-- **Theorem 3.1.**  The arithmetic law is a probability law on the positive integers. -/
theorem eqgMass_hasSum_one (σ : EulerSigma) : HasSum (eqgMass σ) 1 := by
  have h := (summable_eqgWeight σ).hasSum.mul_left (eqgConst σ)
  rw [← eqgTotal] at h
  have hval : eqgConst σ * eqgTotal σ = 1 :=
    inv_mul_cancel₀ (eqgTotal_pos σ).ne'
  rw [hval] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
