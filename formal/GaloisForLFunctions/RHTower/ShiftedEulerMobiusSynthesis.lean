import GaloisForLFunctions.RHTower.DampedComplementaryPacketConnection
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Signed Möbius synthesis of the shifted-Euler source

Weighting the atomic part of the packet connection equation by `μ(d) d^(-1-2ω)` at the divisor
clock `h = log d` and summing over `d` produces the positive shifted-Euler source exactly.  The
arithmetic content is the coefficient identity

```text
∑_{dm=n} μ(d) d^(-1-2ω) m^(-1) = c_ω(n) n^(-1-ω) ,
     c_ω(n) = ∑_{dm=n} μ(d) d^(-ω) m^ω = n^ω ∑_{d ∣ n} μ(d) d^(-2ω) ,
```

which converts the double divisor sum into a single sum over `n = dm`.  Since the atom of the
connection equation at `h = log d` sits at `t = log d + log m = log n` with weight
`d^(-δ) m^(-1-δ)`, this is precisely the statement that the signed Möbius superposition of the
packet connections is the centered shifted-Euler atomic connection.

The continuous term of the connection equation carries the factor
`∑_d μ(d) d^(-1-2ω) = 1/ζ(1+2ω)`, which is `tsum_moebius_rpow_eq_inv_riemannZeta`.
-/

open Filter

namespace RHTower

noncomputable section

/-! ### The shifted-Euler coefficient -/

/-- The shifted-Euler coefficient `c_ω(n) = ∑_{dm=n} μ(d) d^(-ω) m^ω`. -/
def shiftedEulerCoefficient (ω : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal,
    (ArithmeticFunction.moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-ω) * (p.2 : ℝ) ^ ω

private theorem cast_div_of_mem_divisors {n d : ℕ} (hd : d ∈ n.divisors) :
    ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdvd (by exact_mod_cast hd0)]

/-- **The shifted-Euler coefficient is the `ω`-weighted Möbius divisor sum.** -/
theorem shiftedEulerCoefficient_eq (ω : ℝ) (n : ℕ) :
    shiftedEulerCoefficient ω n
      = (n : ℝ) ^ ω * ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω)) := by
  rw [shiftedEulerCoefficient, Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * (a : ℝ) ^ (-ω) * (b : ℝ) ^ ω),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)
    exact_mod_cast this
  rw [cast_div_of_mem_divisors hd, Real.div_rpow hn0.le hd0.le]
  have hsplit : (d : ℝ) ^ (-ω) * ((n : ℝ) ^ ω / (d : ℝ) ^ ω)
      = (n : ℝ) ^ ω * (d : ℝ) ^ (-(2 * ω)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hd0.le, ← mul_assoc, mul_comm ((d : ℝ) ^ (-ω)),
      mul_assoc, ← Real.rpow_add hd0]
    congr 2
    ring
  calc (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ω) * ((n : ℝ) ^ ω / (d : ℝ) ^ ω)
      = (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ω) * ((n : ℝ) ^ ω / (d : ℝ) ^ ω)) := by
        ring
    _ = (n : ℝ) ^ ω * ((ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω))) := by
        rw [hsplit]; ring

/-- **The exact atomic coefficient of the signed Möbius synthesis.** -/
theorem sum_divisorsAntidiagonal_shifted (ω δ : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-1 - 2 * ω - δ)
          * (p.2 : ℝ) ^ (-1 - δ)
      = shiftedEulerCoefficient ω n * (n : ℝ) ^ (-1 - ω - δ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * (a : ℝ) ^ (-1 - 2 * ω - δ)
      * (b : ℝ) ^ (-1 - δ)),
    shiftedEulerCoefficient_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [cast_div_of_mem_divisors hd, Real.div_rpow hn0.le hd0.le]
  have hnpow : (n : ℝ) ^ ω * (n : ℝ) ^ (-1 - ω - δ) = (n : ℝ) ^ (-1 - δ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hdpow : (d : ℝ) ^ (-1 - 2 * ω - δ) / (d : ℝ) ^ (-1 - δ) = (d : ℝ) ^ (-(2 * ω)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hd0.le, ← Real.rpow_add hd0]
    congr 1
    ring
  calc (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-1 - 2 * ω - δ)
        * ((n : ℝ) ^ (-1 - δ) / (d : ℝ) ^ (-1 - δ))
      = (ArithmeticFunction.moebius d : ℝ)
          * ((d : ℝ) ^ (-1 - 2 * ω - δ) / (d : ℝ) ^ (-1 - δ)) * (n : ℝ) ^ (-1 - δ) := by ring
    _ = (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω))
          * ((n : ℝ) ^ ω * (n : ℝ) ^ (-1 - ω - δ)) := by rw [hdpow, hnpow]
    _ = (n : ℝ) ^ ω * ((ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω)))
          * (n : ℝ) ^ (-1 - ω - δ) := by ring

/-! ### The synthesis of the atomic connection -/

private theorem summable_pnat_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun d : ℕ+ => ((d : ℕ) : ℝ) ^ (-p)) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hcongr : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := by
    refine hbase.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  exact hcongr.comp_injective PNat.coe_injective

/-- The two-parameter atomic weight of the signed Möbius synthesis. -/
private def synthesisWeight (ω δ : ℝ) (f : ℝ → ℝ) (p : ℕ+ × ℕ+) : ℝ :=
  (ArithmeticFunction.moebius ((p.1 : ℕ)) : ℝ) * (((p.1 : ℕ)) : ℝ) ^ (-1 - 2 * ω - δ)
    * (((p.2 : ℕ)) : ℝ) ^ (-1 - δ) * f (Real.log ((p.1 : ℕ) * (p.2 : ℕ)))

private theorem abs_moebius_cast_le_one (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  by_cases hsq : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    norm_num

private theorem summable_synthesisWeight (ω δ : ℝ) (hω : 0 < ω) (hδ : 0 < δ) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) : Summable (synthesisWeight ω δ f) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hf 0)
  have h1 : Summable (fun d : ℕ+ => C * ((d : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ))) :=
    (summable_pnat_rpow (by linarith)).mul_left C
  have h2 : Summable (fun m : ℕ+ => ((m : ℕ) : ℝ) ^ (-(1 + δ))) :=
    summable_pnat_rpow (by linarith)
  have hnn1 : ∀ d : ℕ+, 0 ≤ C * ((d : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) := fun d =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hnn2 : ∀ m : ℕ+, 0 ≤ ((m : ℕ) : ℝ) ^ (-(1 + δ)) := fun m =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hdom : Summable (fun p : ℕ+ × ℕ+ =>
      (C * ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ))) * (((p.2 : ℕ) : ℝ) ^ (-(1 + δ)))) :=
    Summable.mul_of_nonneg h1 h2 hnn1 hnn2
  refine Summable.of_norm_bounded hdom fun p => ?_
  have hd0 : (0 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((p.2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp1 : ((p.1 : ℕ) : ℝ) ^ (-1 - 2 * ω - δ) = ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) := by
    congr 1
    ring
  have hexp2 : ((p.2 : ℕ) : ℝ) ^ (-1 - δ) = ((p.2 : ℕ) : ℝ) ^ (-(1 + δ)) := by
    congr 1
    ring
  rw [synthesisWeight, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, hexp1, hexp2,
    abs_of_nonneg (Real.rpow_nonneg hd0 _), abs_of_nonneg (Real.rpow_nonneg hm0 _)]
  have hmu := abs_moebius_cast_le_one ((p.1 : ℕ))
  have hpow1 : (0 : ℝ) ≤ ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) := Real.rpow_nonneg hd0 _
  have hpow2 : (0 : ℝ) ≤ ((p.2 : ℕ) : ℝ) ^ (-(1 + δ)) := Real.rpow_nonneg hm0 _
  have hphi := hf (Real.log ((p.1 : ℕ) * (p.2 : ℕ)))
  have hstep : |(ArithmeticFunction.moebius ((p.1 : ℕ)) : ℝ)|
      * ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) * ((p.2 : ℕ) : ℝ) ^ (-(1 + δ))
      ≤ 1 * ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) * ((p.2 : ℕ) : ℝ) ^ (-(1 + δ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu hpow1) hpow2
  calc |(ArithmeticFunction.moebius ((p.1 : ℕ)) : ℝ)| * ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ))
        * ((p.2 : ℕ) : ℝ) ^ (-(1 + δ)) * |f (Real.log ((p.1 : ℕ) * (p.2 : ℕ)))|
      ≤ 1 * ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) * ((p.2 : ℕ) : ℝ) ^ (-(1 + δ)) * C :=
        mul_le_mul hstep hphi (abs_nonneg _) (by positivity)
    _ = C * ((p.1 : ℕ) : ℝ) ^ (-(1 + 2 * ω + δ)) * ((p.2 : ℕ) : ℝ) ^ (-(1 + δ)) := by ring

/-- **Signed Möbius synthesis of the connection atoms.**  Weighting the packet connection atoms by
`μ(d) d^(-1-2ω)` at the divisor clock `h = log d` and summing over `d` gives exactly the
shifted-Euler atomic source `c_ω(n) n^(-1-ω-δ)` at `t = log n`. -/
theorem mobiusSynthesis_atoms (ω δ : ℝ) (hω : 0 < ω) (hδ : 0 < δ) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) :
    (∑' d : ℕ+, ∑' m : ℕ+,
        (ArithmeticFunction.moebius (d : ℕ) : ℝ) * ((d : ℕ) : ℝ) ^ (-1 - 2 * ω)
          * (((d : ℕ) : ℝ) ^ (-δ) * ((m : ℕ) : ℝ) ^ (-1 - δ))
          * f (Real.log ((d : ℕ) * (m : ℕ))))
      = ∑' n : ℕ+, shiftedEulerCoefficient ω (n : ℕ) * ((n : ℕ) : ℝ) ^ (-1 - ω - δ)
          * f (Real.log (n : ℕ)) := by
  have hsum := summable_synthesisWeight ω δ hω hδ hf
  have hleft : (∑' d : ℕ+, ∑' m : ℕ+,
      (ArithmeticFunction.moebius (d : ℕ) : ℝ) * ((d : ℕ) : ℝ) ^ (-1 - 2 * ω)
        * (((d : ℕ) : ℝ) ^ (-δ) * ((m : ℕ) : ℝ) ^ (-1 - δ))
        * f (Real.log ((d : ℕ) * (m : ℕ))))
      = ∑' p : ℕ+ × ℕ+, synthesisWeight ω δ f p := by
    rw [hsum.tsum_prod]
    refine tsum_congr fun d => tsum_congr fun m => ?_
    have hd0 : (0 : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast d.2
    have hsplit : ((d : ℕ) : ℝ) ^ (-1 - 2 * ω) * ((d : ℕ) : ℝ) ^ (-δ)
        = ((d : ℕ) : ℝ) ^ (-1 - 2 * ω - δ) := by
      rw [← Real.rpow_add hd0]
      congr 1
    have hval : synthesisWeight ω δ f (d, m)
        = (ArithmeticFunction.moebius (d : ℕ) : ℝ)
            * (((d : ℕ) : ℝ) ^ (-1 - 2 * ω) * ((d : ℕ) : ℝ) ^ (-δ))
            * ((m : ℕ) : ℝ) ^ (-1 - δ) * f (Real.log ((d : ℕ) * (m : ℕ))) := by
      rw [synthesisWeight, hsplit]
    rw [hval]
    ring
  rw [hleft]
  have hsigma : Summable (fun x : (n : ℕ+) × ((n : ℕ).divisorsAntidiagonal) =>
      synthesisWeight ω δ f (sigmaAntidiagonalEquivProd x)) :=
    (sigmaAntidiagonalEquivProd.summable_iff (f := synthesisWeight ω δ f)).mpr hsum
  rw [← sigmaAntidiagonalEquivProd.tsum_eq (synthesisWeight ω δ f), hsigma.tsum_sigma]
  refine tsum_congr fun n => ?_
  have hnpos : 0 < (n : ℕ) := n.2
  rw [tsum_fintype]
  have hattach : ∑ x : ((n : ℕ).divisorsAntidiagonal),
      synthesisWeight ω δ f (sigmaAntidiagonalEquivProd ⟨n, x⟩)
      = ∑ p ∈ (n : ℕ).divisorsAntidiagonal,
          ((ArithmeticFunction.moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-1 - 2 * ω - δ)
            * (p.2 : ℝ) ^ (-1 - δ)) * f (Real.log (n : ℕ)) := by
    rw [← Finset.sum_attach (n : ℕ).divisorsAntidiagonal
      (fun p => ((ArithmeticFunction.moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-1 - 2 * ω - δ)
        * (p.2 : ℝ) ^ (-1 - δ)) * f (Real.log (n : ℕ)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hprod : (x : ℕ × ℕ).1 * (x : ℕ × ℕ).2 = (n : ℕ) :=
      (Nat.mem_divisorsAntidiagonal.mp x.2).1
    have hprodR : (((x : ℕ × ℕ).1 : ℕ) : ℝ) * (((x : ℕ × ℕ).2 : ℕ) : ℝ) = (((n : ℕ)) : ℝ) := by
      exact_mod_cast hprod
    show (ArithmeticFunction.moebius ((x : ℕ × ℕ).1) : ℝ) * (((x : ℕ × ℕ).1 : ℕ) : ℝ) ^ (-1 - 2 * ω - δ)
        * (((x : ℕ × ℕ).2 : ℕ) : ℝ) ^ (-1 - δ)
        * f (Real.log ((x : ℕ × ℕ).1 * (x : ℕ × ℕ).2)) = _
    rw [hprodR]
  rw [hattach, ← Finset.sum_mul, sum_divisorsAntidiagonal_shifted ω δ hnpos]

/-! ### The Euler product form of the coefficient -/

/-- The Möbius-weighted power as an arithmetic function. -/
private def moebiusRpow (ω : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω)), by simp⟩

private theorem moebiusRpow_apply (ω : ℝ) (d : ℕ) :
    moebiusRpow ω d = (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω)) := rfl

private theorem isMultiplicative_moebiusRpow (ω : ℝ) :
    (moebiusRpow ω).IsMultiplicative := by
  constructor
  · rw [moebiusRpow_apply]
    simp
  · intro m n hmn
    rw [moebiusRpow_apply, moebiusRpow_apply, moebiusRpow_apply,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private theorem sum_divisors_prime_pow_moebiusRpow (ω : ℝ) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) :
    ∑ d ∈ (p ^ k).divisors, moebiusRpow ω d = 1 - (p : ℝ) ^ (-(2 * ω)) := by
  rw [Nat.sum_divisors_prime_pow hp]
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (k + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> (simp only [Finset.mem_range]; omega)
  have hzero : ∀ i ∈ Finset.range (k + 1), i ∉ ({0, 1} : Finset ℕ) →
      moebiusRpow ω (p ^ i) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hi2 : 2 ≤ i := by omega
    rw [moebiusRpow_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
      if_neg (by omega)]
    norm_num
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton, moebiusRpow_apply,
    moebiusRpow_apply, pow_zero, pow_one, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.isMultiplicative_moebius.1]
  push_cast
  rw [Real.one_rpow]
  ring

/-- **The Euler product form of the shifted-Euler coefficient.** -/
theorem sum_divisors_moebius_rpow (ω : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω))
      = ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-(2 * ω))) := by
  have hzeta : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.natCast ArithmeticFunction.isMultiplicative_zeta
  have hmul : ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ))
      * moebiusRpow ω).IsMultiplicative := hzeta.mul (isMultiplicative_moebiusRpow ω)
  have hfact := hmul.multiplicative_factorization _ hn
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hfact
  have hsum : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(2 * ω))
      = ∑ d ∈ n.divisors, moebiusRpow ω d := by
    refine Finset.sum_congr rfl fun d _ => (moebiusRpow_apply ω d).symm
  rw [hsum, hfact, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : n.factorization p ≠ 0 := by
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpos : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd hprime hn hdvd
    omega
  rw [ArithmeticFunction.coe_zeta_mul_apply, sum_divisors_prime_pow_moebiusRpow ω hprime hk]

/-- **The shifted-Euler coefficient in Euler product form.** -/
theorem shiftedEulerCoefficient_eq_prod (ω : ℝ) {n : ℕ} (hn : n ≠ 0) :
    shiftedEulerCoefficient ω n
      = (n : ℝ) ^ ω * ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-(2 * ω))) := by
  rw [shiftedEulerCoefficient_eq, sum_divisors_moebius_rpow ω hn]

/-! ### The Euler main density of the synthesis -/

private theorem summable_moebius_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-s)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) :=
      Real.summable_one_div_nat_rpow.mpr hs
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  refine Summable.of_norm_bounded hbase fun n => ?_
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  nlinarith [abs_moebius_cast_le_one n, abs_nonneg (ArithmeticFunction.moebius n : ℝ)]

/-- **The Euler main density of the signed Möbius synthesis.**  The continuous term of the packet
connection is weighted by the reciprocal zeta value. -/
theorem ofReal_tsum_moebius_rpow {s : ℝ} (hs : 1 < s) :
    ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ)
      = (riemannZeta (s : ℂ))⁻¹ := by
  have hre : (1 : ℝ) < ((s : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hs
  rw [← LSeries_moebius_eq_inv_riemannZeta hre, LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn.ne', Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n) s, Complex.ofReal_natCast,
      div_eq_mul_inv]
    push_cast
    ring

end

end RHTower
