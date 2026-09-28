import GaloisForLFunctions.RHTower.MobiusCoprimeHarmonicUniform

/-!
# Sign law for the divisor-comparable Möbius Hilbert section

For a squarefree `n ≥ 2`, the Hilbert-matrix Möbius entries joining `n` to its proper divisors
sum to `A_n / n`, where

`A_n = ∑_{d ∣ n, d > 1} μ(d) · d/(d+1) = -φ(n)/n + V_n`,  `V_n = ∑_{d ∣ n, d > 1} μ(d)/(d(d+1))`.

Expanding `1/(d(d+1)) = ∑_k (-1)^k d^{-(k+2)}` and using
`∑_{d ∣ n} μ(d) d^{-s} = ∏_{p ∣ n} (1 - p^{-s})` gives
`V_n = -∑_k (-1)^k t_k` with `t_k = 1 - ∏_{p ∣ n}(1 - p^{-(k+2)})` antitone and tending to zero, so
`V_n ≤ 0` by the alternating series bound.  Hence every row is at most `-φ(n)/n²`, and the complete
divisor-comparable section satisfies

`∑_{n ≤ X} ∑_{m ∣ n, m < n} μ(m)μ(n)/(m+n) ≤ -∑_{2 ≤ n ≤ X} μ(n)² φ(n)/n²`.

The only arithmetic input is the exact cancellation `∑_{d ∣ n} μ(d) = 0` inside each row.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-- `d ↦ d^{-(k+1)}` as a completely multiplicative real arithmetic function. -/
def invPowArith (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => ((d : ℝ) ^ (k + 1))⁻¹, by simp⟩

theorem invPowArith_apply (k d : ℕ) : invPowArith k d = ((d : ℝ) ^ (k + 1))⁻¹ := rfl

theorem isMultiplicative_invPowArith (k : ℕ) : (invPowArith k).IsMultiplicative := by
  refine ⟨by simp [invPowArith_apply], ?_⟩
  intro m n _
  simp only [invPowArith_apply]
  push_cast
  rw [mul_pow, mul_inv]

/-- Euler product for the Möbius-weighted divisor power sum of a squarefree integer. -/
theorem sum_divisors_moebius_invPow {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    (∑ d ∈ n.divisors, mobiusRealCoefficient d * ((d : ℝ) ^ (k + 1))⁻¹) =
      ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (k + 1))⁻¹) := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (invPowArith k) (isMultiplicative_invPowArith k) hn
  simp only [invPowArith_apply] at h
  rw [h]
  rfl

/-- The divisor sum of the Möbius function vanishes above one. -/
theorem sum_divisors_mobiusRealCoefficient_eq_zero {n : ℕ} (hn : n ≠ 1) :
    (∑ d ∈ n.divisors, mobiusRealCoefficient d) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne hn] at h
  simpa [mobiusRealCoefficient] using h

/-- The tail defect `t_k = 1 - ∏_{p ∣ n} (1 - p^{-(k+2)})`. -/
def divisorTailDefect (n k : ℕ) : ℝ :=
  1 - ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (k + 2))⁻¹)

private theorem inv_pow_le_quarter {p k : ℕ} (hp : p.Prime) :
    ((p : ℝ) ^ (k + 2))⁻¹ ≤ 1 / 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h4 : (4 : ℝ) ≤ (p : ℝ) ^ (k + 2) := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hp2 2
      _ ≤ (p : ℝ) ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
  rw [one_div]
  exact inv_anti₀ (by norm_num) h4

theorem divisorTailDefect_antitone (n : ℕ) : Antitone (divisorTailDefect n) := by
  apply antitone_nat_of_succ_le
  intro k
  unfold divisorTailDefect
  apply sub_le_sub_left
  apply Finset.prod_le_prod
  · intro p hp
    have hq := inv_pow_le_quarter (k := k) (Nat.prime_of_mem_primeFactors hp)
    linarith
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    have hle : ((p : ℝ) ^ (k + 1 + 2))⁻¹ ≤ ((p : ℝ) ^ (k + 2))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hp1 (by omega))
    linarith

/-- Geometric expansion `1/(x(x+1)) = ∑_k (-1)^k x^{-(k+2)}` for `x ≥ 2`. -/
theorem hasSum_inv_mul_succ {x : ℝ} (hx : 2 ≤ x) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (x ^ (k + 2))⁻¹) (1 / (x * (x + 1))) := by
  have hx0 : 0 < x := by linarith
  have habs : |(-x⁻¹ : ℝ)| < 1 := by
    rw [abs_neg, abs_of_pos (inv_pos.mpr hx0)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hgeo := (hasSum_geometric_of_abs_lt_one habs).mul_left ((x ^ 2)⁻¹)
  have hfun : (fun k : ℕ => (-1 : ℝ) ^ k * (x ^ (k + 2))⁻¹) =
      (fun i : ℕ => (x ^ 2)⁻¹ * (-x⁻¹) ^ i) := by
    funext k
    rw [show (-x⁻¹ : ℝ) = (-1) * x⁻¹ by ring, mul_pow, inv_pow, pow_add, mul_inv]
    ring
  have hden : (1 : ℝ) - -x⁻¹ = (x + 1) / x := by
    field_simp
    ring
  have hval : 1 / (x * (x + 1)) = (x ^ 2)⁻¹ * (1 - -x⁻¹)⁻¹ := by
    rw [hden, inv_div]
    field_simp
  rw [hfun, hval]
  exact hgeo

/-- The negative-curvature part `V_n = ∑_{d ∣ n, d > 1} μ(d)/(d(d+1))`. -/
def divisorCurvatureSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.erase 1, mobiusRealCoefficient d * (1 / ((d : ℝ) * ((d : ℝ) + 1)))

/-- `V_n` is minus an alternating series with antitone terms, hence nonpositive. -/
theorem divisorCurvatureSum_nonpos {n : ℕ} (hn : Squarefree n) :
    divisorCurvatureSum n ≤ 0 := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hterm : ∀ d ∈ n.divisors.erase 1,
      HasSum (fun k : ℕ => mobiusRealCoefficient d * ((-1 : ℝ) ^ k * ((d : ℝ) ^ (k + 2))⁻¹))
        (mobiusRealCoefficient d * (1 / ((d : ℝ) * ((d : ℝ) + 1)))) := by
    intro d hd
    have hd1 : d ≠ 1 := (Finset.mem_erase.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
    exact (hasSum_inv_mul_succ hd2).mul_left _
  have hsum := hasSum_sum hterm
  have hrewrite : ∀ k : ℕ,
      (∑ d ∈ n.divisors.erase 1,
          mobiusRealCoefficient d * ((-1 : ℝ) ^ k * ((d : ℝ) ^ (k + 2))⁻¹)) =
        -((-1 : ℝ) ^ k * divisorTailDefect n k) := by
    intro k
    have hprod := sum_divisors_moebius_invPow hn (k + 1)
    have hone : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
    have herase := Finset.sum_erase_eq_sub (f := fun d : ℕ =>
      mobiusRealCoefficient d * ((d : ℝ) ^ (k + 1 + 1))⁻¹) hone
    simp only [Nat.cast_one, one_pow, inv_one, mul_one] at herase
    have hμ1 : mobiusRealCoefficient 1 = 1 := by simp [mobiusRealCoefficient]
    rw [hμ1] at herase
    unfold divisorTailDefect
    calc
      (∑ d ∈ n.divisors.erase 1,
          mobiusRealCoefficient d * ((-1 : ℝ) ^ k * ((d : ℝ) ^ (k + 2))⁻¹)) =
        (-1 : ℝ) ^ k * ∑ d ∈ n.divisors.erase 1,
          mobiusRealCoefficient d * ((d : ℝ) ^ (k + 1 + 1))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = (-1 : ℝ) ^ k * ((∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (k + 1 + 1))⁻¹)) - 1) := by
        rw [herase, hprod]
      _ = -((-1 : ℝ) ^ k * (1 - ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (k + 2))⁻¹))) := by
        ring
  simp_rw [hrewrite] at hsum
  have hneg : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * divisorTailDefect n k)
      (-divisorCurvatureSum n) := by
    have := hsum.neg
    simpa [divisorCurvatureSum] using this
  have htend := hneg.tendsto_sum_nat
  have hbound := Antitone.alternating_series_le_tendsto htend
    (divisorTailDefect_antitone n) 0
  simp only [mul_zero, Finset.range_zero, Finset.sum_empty] at hbound
  linarith

/-- `∑_{d ∣ n} μ(d)/d = φ(n)/n`. -/
theorem prod_one_sub_inv_primeFactors_eq_totient_div {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (0 + 1))⁻¹)) = (n.totient : ℝ) / n := by
  have hkey := Nat.totient_mul_prod_primeFactors n
  have hcast : (n.totient : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hkey
    push_cast at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [hp1]
    ring
  have hprodpos : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hfactor : (∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (0 + 1))⁻¹)) =
      (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) / ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    simp only [zero_add, pow_one]
    field_simp
  rw [hfactor, div_eq_div_iff hprodpos.ne' hnpos.ne']
  linarith

/-- The row weight `A_n = ∑_{d ∣ n, d > 1} μ(d) d/(d+1)`. -/
def divisorRowWeight (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.erase 1, mobiusRealCoefficient d * ((d : ℝ) / ((d : ℝ) + 1))

/-- **Row decomposition.**  `A_n = -φ(n)/n + V_n` for squarefree `n ≥ 2`. -/
theorem divisorRowWeight_eq {n : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1) :
    divisorRowWeight n = -((n.totient : ℝ) / n) + divisorCurvatureSum n := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hone : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have hμ1 : mobiusRealCoefficient 1 = 1 := by simp [mobiusRealCoefficient]
  have hsplit : ∀ d ∈ n.divisors.erase 1,
      mobiusRealCoefficient d * ((d : ℝ) / ((d : ℝ) + 1)) =
        mobiusRealCoefficient d - mobiusRealCoefficient d * ((d : ℝ) ^ (0 + 1))⁻¹ +
          mobiusRealCoefficient d * (1 / ((d : ℝ) * ((d : ℝ) + 1))) := by
    intro d hd
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
    field_simp
    ring
  have hzero := sum_divisors_mobiusRealCoefficient_eq_zero hn1
  have hsum0 : (∑ d ∈ n.divisors.erase 1, mobiusRealCoefficient d) = -1 := by
    rw [Finset.sum_erase_eq_sub hone, hzero, hμ1]
    ring
  have hsum1 : (∑ d ∈ n.divisors.erase 1,
      mobiusRealCoefficient d * ((d : ℝ) ^ (0 + 1))⁻¹) = (n.totient : ℝ) / n - 1 := by
    rw [Finset.sum_erase_eq_sub (f := fun d : ℕ =>
        mobiusRealCoefficient d * ((d : ℝ) ^ (0 + 1))⁻¹) hone,
      sum_divisors_moebius_invPow hn 0, prod_one_sub_inv_primeFactors_eq_totient_div hn0, hμ1]
    simp
  unfold divisorRowWeight divisorCurvatureSum
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hsum0, hsum1]
  ring

/-- **Row sign law.**  `A_n ≤ -φ(n)/n` for squarefree `n ≥ 2`. -/
theorem divisorRowWeight_le {n : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1) :
    divisorRowWeight n ≤ -((n.totient : ℝ) / n) := by
  rw [divisorRowWeight_eq hn hn1]
  linarith [divisorCurvatureSum_nonpos hn]

/-- The literal Hilbert-matrix Möbius entries joining `n` to its proper divisors. -/
def mobiusDivisorHilbertRow (n : ℕ) : ℝ :=
  ∑ m ∈ n.properDivisors,
    mobiusRealCoefficient m * mobiusRealCoefficient n / ((m : ℝ) + n)

/-- For squarefree `n`, the complementary-divisor reindexing `m = n/d` gives `row = A_n / n`. -/
theorem mobiusDivisorHilbertRow_eq {n : ℕ} (hn : Squarefree n) :
    mobiusDivisorHilbertRow n = divisorRowWeight n / n := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  let F : ℕ → ℝ := fun m =>
    mobiusRealCoefficient m * mobiusRealCoefficient n / ((m : ℝ) + n)
  have hproper : mobiusDivisorHilbertRow n = ∑ m ∈ n.divisors, F m - F n := by
    unfold mobiusDivisorHilbertRow
    rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons]
    ring
  have hflip : ∑ m ∈ n.divisors, F m = ∑ d ∈ n.divisors, F (n / d) :=
    (Nat.sum_div_divisors n F).symm
  have hone : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have herase := Finset.sum_erase_eq_sub (f := fun d : ℕ => F (n / d)) hone
  simp only [Nat.div_one] at herase
  rw [hproper, hflip, ← herase]
  unfold divisorRowWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_erase.mp hd).2
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
  obtain ⟨e, he⟩ := hdvd
  have hsq : Squarefree (d * e) := he ▸ hn
  have hcop : d.Coprime e := (Nat.squarefree_mul_iff.mp hsq).1
  have hsqe : Squarefree e := (Nat.squarefree_mul_iff.mp hsq).2.2
  have hdiv : n / d = e := by rw [he, Nat.mul_div_cancel_left e hdpos]
  have hμe : mobiusRealCoefficient e ^ 2 = 1 := by
    have hne : moebius e ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsqe
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
      simp [mobiusRealCoefficient, hm]
  have hμn : mobiusRealCoefficient n = mobiusRealCoefficient d * mobiusRealCoefficient e := by
    rw [he]
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hcop]
    push_cast
    ring
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at he; exact absurd he hn0
    · exact h0
  have heR : (0 : ℝ) < e := by exact_mod_cast hepos
  have hnR : (n : ℝ) = d * e := by rw [he]; push_cast; ring
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  calc
    F (n / d) = mobiusRealCoefficient e * (mobiusRealCoefficient d * mobiusRealCoefficient e) /
        ((e : ℝ) * ((d : ℝ) + 1)) := by
      simp only [F, hdiv]
      rw [hμn, hnR, show (e : ℝ) + (d : ℝ) * e = e * ((d : ℝ) + 1) by ring]
    _ = mobiusRealCoefficient e ^ 2 * mobiusRealCoefficient d /
        ((e : ℝ) * ((d : ℝ) + 1)) := by ring
    _ = mobiusRealCoefficient d / ((e : ℝ) * ((d : ℝ) + 1)) := by rw [hμe, one_mul]
    _ = mobiusRealCoefficient d * ((d : ℝ) / ((d : ℝ) + 1)) / n := by
      rw [hnR]
      field_simp

/-- **Row law.**  Every divisor row of the Möbius Hilbert form is at most `-μ(n)² φ(n)/n²`. -/
theorem mobiusDivisorHilbertRow_le {n : ℕ} (hn1 : 2 ≤ n) :
    mobiusDivisorHilbertRow n ≤
      -(mobiusRealCoefficient n ^ 2 * ((n.totient : ℝ) / n) / n) := by
  by_cases hsf : Squarefree n
  · have hne : moebius n ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    have hμ2 : mobiusRealCoefficient n ^ 2 = 1 := by
      rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
        simp [mobiusRealCoefficient, hm]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [mobiusDivisorHilbertRow_eq hsf, hμ2, one_mul]
    rw [div_le_iff₀ hnpos]
    have := divisorRowWeight_le hsf (by omega)
    rw [neg_mul, div_mul_cancel₀ _ hnpos.ne']
    exact this
  · have hzero : mobiusRealCoefficient n = 0 := by
      simp [mobiusRealCoefficient, moebius_eq_zero_of_not_squarefree hsf]
    have hrow : mobiusDivisorHilbertRow n = 0 := by
      unfold mobiusDivisorHilbertRow
      simp [hzero]
    rw [hrow, hzero]
    simp

/-- **Divisor-comparable section law.**  The complete section of the Möbius Hilbert form over
pairs `m ∣ n`, `m < n ≤ X`, is at most `-∑_{2 ≤ n ≤ X} μ(n)² φ(n)/n²`. -/
theorem sum_mobiusDivisorHilbertRow_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, mobiusDivisorHilbertRow n) ≤
      -∑ n ∈ Finset.Icc 2 X, mobiusRealCoefficient n ^ 2 * ((n.totient : ℝ) / n) / n := by
  rcases Nat.lt_or_ge X 1 with hX | hX
  · have hX0 : X = 0 := by omega
    subst hX0
    simp
  have hsplit : Finset.Icc 1 X = insert 1 (Finset.Icc 2 X) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 X := by simp
  have hrow1 : mobiusDivisorHilbertRow 1 = 0 := by
    simp [mobiusDivisorHilbertRow]
  rw [hsplit, Finset.sum_insert hnot, hrow1, zero_add, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n hn
  exact mobiusDivisorHilbertRow_le (Finset.mem_Icc.mp hn).1

/-- Reindexing multiples as divisors: `(d, q) ↦ (d q, d)`. -/
theorem sum_Icc_sum_Icc_div_eq_sum_divisors (X : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ q ∈ Finset.Icc 1 (X / d), f d (d * q)) =
      ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d n := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij' (fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ))
    (fun p _ => (⟨p.2, p.1 / p.2⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hd1, hdX⟩, hq1, hqX⟩ := hp
    have hmul : p.1 * p.2 ≤ X := by
      calc
        p.1 * p.2 ≤ p.1 * (X / p.1) := Nat.mul_le_mul_left _ hqX
        _ ≤ X := Nat.mul_div_le X p.1
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hmul⟩, ?_⟩
    exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, Nat.mul_ne_zero (by omega) (by omega)⟩
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hn1, hnX⟩, hdn⟩ := hp
    have hdvd := Nat.dvd_of_mem_divisors hdn
    have hdpos := Nat.pos_of_mem_divisors hdn
    have hdle : p.2 ≤ p.1 := Nat.le_of_dvd (by omega) hdvd
    refine ⟨⟨hdpos, hdle.trans hnX⟩, ?_, Nat.div_le_div_right hnX⟩
    exact (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdle)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    have hd : 0 < p.1 := by omega
    ext
    · rfl
    · simp [Nat.mul_div_cancel_left _ hd]
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    have hdvd := Nat.dvd_of_mem_divisors hp.2
    ext
    · simp [Nat.mul_div_cancel' hdvd]
    · rfl
  · intro p _
    rfl

/-- The corpus integer-ratio sub-energy is the diagonal plus twice the divisor rows. -/
theorem integerDilationGammaSection_eq_rows (X : ℕ) :
    integerDilationGammaSection X =
      ∑ n ∈ Finset.Icc 1 X,
        (mobiusRealCoefficient n ^ 2 / n + 2 * mobiusDivisorHilbertRow n) := by
  let f : ℕ → ℕ → ℝ := fun d n =>
    2 * mobiusRealCoefficient d * mobiusRealCoefficient n / ((n : ℝ) + d)
  have hray : ∀ d ∈ Finset.Icc 1 X,
      fixedCofactorGammaRay d (X / d) = ∑ q ∈ Finset.Icc 1 (X / d), f d (d * q) := by
    intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    unfold fixedCofactorGammaRay
    apply Finset.sum_congr rfl
    intro q _
    simp only [f]
    congr 1
    push_cast
    ring
  unfold integerDilationGammaSection
  rw [Finset.sum_congr rfl hray, sum_Icc_sum_Icc_div_eq_sum_divisors]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons]
  unfold mobiusDivisorHilbertRow
  rw [Finset.mul_sum]
  congr 1
  · simp only [f]
    field_simp
    ring
  · apply Finset.sum_congr rfl
    intro m _
    simp only [f]
    ring

/-- **Signed integer-ratio law.**  The corpus integer-ratio Gamma--Hankel sub-energy at exponent
one is at most its diagonal minus `2 ∑_{2 ≤ n ≤ X} μ(n)² φ(n)/n²`. -/
theorem integerDilationGammaSection_le (X : ℕ) :
    integerDilationGammaSection X ≤
      (∑ n ∈ Finset.Icc 1 X, mobiusRealCoefficient n ^ 2 / n) -
        2 * ∑ n ∈ Finset.Icc 2 X,
          mobiusRealCoefficient n ^ 2 * ((n.totient : ℝ) / n) / n := by
  rw [integerDilationGammaSection_eq_rows, Finset.sum_add_distrib, ← Finset.mul_sum]
  have := sum_mobiusDivisorHilbertRow_le X
  linarith

end
end RHTower
