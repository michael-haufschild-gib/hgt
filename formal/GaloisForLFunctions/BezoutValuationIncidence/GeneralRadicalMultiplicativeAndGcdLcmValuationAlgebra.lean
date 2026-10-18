import GaloisForLFunctions.BezoutValuationIncidence.SummationByPartsActivePairAndUncenteredShiftedReduction

/-!
# Pillar XXIX: Autonomous GCD–LCM Modular Valuation Algebra & General Radical-Multiplicative Functions

A hallmark of an independent mathematical field is that its core algebraic structures, conservation
laws, and incidence inequalities hold for **general classes of objects** defined by intrinsic axioms
rather than only for a single specialized 1-parameter family.

In this twenty-ninth pillar of **Bézout–Valuation Incidence Mechanics**, we abstract the structural
mechanisms of Pillars X, XV, XVI, XXI, XXV, and XXVI to the general class of **GCD–LCM Modular
Valuation Functions** (`IsGcdLcmModular F`) and **Radical-Multiplicative Prime-Factor Functionals**
(`radicalPrimeProd w`):

1. **The Abstract Class `IsGcdLcmModular` & Universal Pronic–Gradient Conservation Laws
   (`IsGcdLcmModular`,
   `IsGcdLcmModular.map_mul_of_coprime`,
   `IsGcdLcmModular.mul_succ_eq_pronicSeq`,
   `IsGcdLcmModular.mul_add_of_coprime`,
   `IsGcdLcmModular.addDiff_sq_add_two_mul_pronicSeq`,
   `IsGcdLcmModular.sum_Icc_pronicSeq_add_addDiff_sq_eq`)**:
   - A function $F : \mathbb{N} \to \mathbb{R}$ is **GCD–LCM modular** if $F(1) = 1$ and
     $$F(j)\,F(k) = F(\operatorname{lcm}(j, k))\,F(\gcd(j, k)) \qquad (\forall j, k \in \mathbb{N}).$$
   - Every GCD–LCM modular function $F$ is automatically coprime-multiplicative, satisfies the
     **Pronic Bézout Multiplicativity Law** $F(k)\,F(k + 1) = F(\operatorname{pronicSeq}\,k)$ and
     the **Shifted Bézout Law** $F(k)\,F(k + h) = F(k(k + h))$ whenever $\gcd(k, h) = 1$, and obeys
     the **Universal Pronic–Diagonal–Gradient Conservation Law**:
     $$\bigl(\operatorname{addDiff}\,F\,n\bigr)^2 + 2\,F(\operatorname{pronicSeq}\,n)
       = F(n)^2 + F(n + 1)^2,$$
     $$2\sum_{n=1}^N F(\operatorname{pronicSeq}\,n) + \sum_{n=1}^N \bigl(\operatorname{addDiff}\,F\,n\bigr)^2
       = 2\sum_{n=1}^N F(n)^2 + F(N + 1)^2 - 1.$$

2. **The General Radical Prime-Factor Functional (`radicalPrimeProd`) & Its Valuation Algebra
   (`radicalPrimeProd`,
   `radicalPrimeProd_eq_of_primeFactors_eq`,
   `radicalPrimeProd_pow`,
   `radicalPrimeProd_mul_of_dvd_right`,
   `radicalPrimeProd_mul_eq_mul_gcd`,
   `radicalPrimeProd_lcm_eq_mul`,
   `isGcdLcmModular_radicalPrimeProd`,
   `pmPowerDampedDivisorCoeff_eq_radicalPrimeProd`)**:
   - For **any** prime valuation weight $w : \mathbb{N} \to \mathbb{R}$,
     $$\operatorname{radicalPrimeProd}\,w\,n := \begin{cases} 0 & \text{if } n = 0, \\ \prod_{p \in n.\text{primeFactors}} (1 - w(p)) & \text{if } n \ne 0 \end{cases}$$
     is radical-invariant, power-invariant, divisor-absorbing ($d \mid m \implies F(d m) = F(m)$),
     product–GCD modular ($F(j)F(k) = F(jk)F(\gcd(j, k))$), and GCD–LCM modular
     (`isGcdLcmModular_radicalPrimeProd w`), recovering Euler's totient ratio $\varphi(n)/n$ at
     $w(p) = 1/p$ and Route PM's `pmPowerDampedDivisorCoeff ε` at $w(p) = p^{-\varepsilon}$.

3. **Universal Divisor-Ordering Antitonicity, Submultiplicativity & Primorial Bézout Ceilings
   (`radicalPrimeProd_le_of_dvd`,
   `radicalPrimeProd_mul_le`,
   `radicalPrimeProd_pronicSeq_le_two`,
   `radicalPrimeProd_pronicSeq_le_six_of_three_dvd`,
   `radicalPrimeProd_three_step_mul_le_six`)**:
   - For **every** prime valuation weight $w : \mathbb{N} \to \mathbb{R}$ taking values in $[0, 1]$
     on primes:
     - $0 \le \operatorname{radicalPrimeProd}\,w\,n \le 1$,
     - $d \mid m \implies m \ne 0 \implies \operatorname{radicalPrimeProd}\,w\,m \le \operatorname{radicalPrimeProd}\,w\,d$,
     - $\operatorname{radicalPrimeProd}\,w\,a \cdot \operatorname{radicalPrimeProd}\,w\,b \le \operatorname{radicalPrimeProd}\,w\,(a b)$ for all $a, b \in \mathbb{N}$,
     - $\operatorname{radicalPrimeProd}\,w\,(\operatorname{pronicSeq}\,k) \le 1 - w(2)$ for all $k \ge 1$,
     - $\operatorname{radicalPrimeProd}\,w\,k \cdot \operatorname{radicalPrimeProd}\,w\,(k + 1) \cdot \operatorname{radicalPrimeProd}\,w\,(k + 2) \le (1 - w(2))(1 - w(3))$ for all $k \ge 1$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The Abstract Class `IsGcdLcmModular` & Universal Pronic–Gradient Conservation Laws -/

/-- A function `F : ℕ → ℝ` is **GCD–LCM modular** on the divisibility lattice `(ℕ, gcd, lcm)` if
`F 1 = 1` and `F j * F k = F (Nat.lcm j k) * F (Nat.gcd j k)` for all `j, k : ℕ`. -/
def IsGcdLcmModular (F : ℕ → ℝ) : Prop :=
  F 1 = 1 ∧ ∀ j k : ℕ, F j * F k = F (Nat.lcm j k) * F (Nat.gcd j k)

namespace IsGcdLcmModular

/-- Every GCD–LCM modular function satisfies `F 1 = 1`. -/
theorem map_one {F : ℕ → ℝ} (hF : IsGcdLcmModular F) : F 1 = 1 :=
  hF.1

/-- Every GCD–LCM modular function satisfies `F j * F k = F (Nat.lcm j k) * F (Nat.gcd j k)`. -/
theorem mul_eq_lcm_mul_gcd {F : ℕ → ℝ} (hF : IsGcdLcmModular F) (j k : ℕ) :
    F j * F k = F (Nat.lcm j k) * F (Nat.gcd j k) :=
  hF.2 j k

/-- **Coprime Multiplicativity of GCD–LCM Modular Functions (`IsGcdLcmModular.map_mul_of_coprime`):**
For every `hF : IsGcdLcmModular F` and coprime `j, k : ℕ`, `F (j * k) = F j * F k`. -/
theorem map_mul_of_coprime {F : ℕ → ℝ} (hF : IsGcdLcmModular F) {j k : ℕ}
    (hcop : Nat.Coprime j k) :
    F (j * k) = F j * F k := by
  have hlcm : Nat.lcm j k = j * k := Nat.Coprime.lcm_eq_mul hcop
  have hgcd : Nat.gcd j k = 1 := hcop
  rw [hF.mul_eq_lcm_mul_gcd j k, hlcm, hgcd, hF.map_one, mul_one]

/-- **Universal Pronic Bézout Multiplicativity Law (`IsGcdLcmModular.mul_succ_eq_pronicSeq`):**
For every `hF : IsGcdLcmModular F` and `k : ℕ`:
`F k * F (k + 1) = F (pronicSeq k)`. -/
theorem mul_succ_eq_pronicSeq {F : ℕ → ℝ} (hF : IsGcdLcmModular F) (k : ℕ) :
    F k * F (k + 1) = F (pronicSeq k) := by
  unfold pronicSeq
  exact (hF.map_mul_of_coprime (coprime_self_succ k)).symm

/-- **Shifted Bézout Multiplicativity Law (`IsGcdLcmModular.mul_add_of_coprime`):**
For every `hF : IsGcdLcmModular F` and coprime `k, h : ℕ`:
`F k * F (k + h) = F (k * (k + h))`. -/
theorem mul_add_of_coprime {F : ℕ → ℝ} (hF : IsGcdLcmModular F) {k h : ℕ}
    (hcop : Nat.Coprime k h) :
    F k * F (k + h) = F (k * (k + h)) := by
  have hcop' : Nat.Coprime k (k + h) := by simpa using hcop
  exact (hF.map_mul_of_coprime hcop').symm

/-- **Universal Pointwise Pronic–Diagonal–Gradient Conservation Law
(`IsGcdLcmModular.addDiff_sq_add_two_mul_pronicSeq`):**
For every `hF : IsGcdLcmModular F` and `n : ℕ`:
`(addDiff F n)² + 2 * F (pronicSeq n) = F n ^ 2 + F (n + 1) ^ 2`. -/
theorem addDiff_sq_add_two_mul_pronicSeq {F : ℕ → ℝ} (hF : IsGcdLcmModular F) (n : ℕ) :
    addDiff F n ^ (2 : ℕ) + 2 * F (pronicSeq n) =
      F n ^ (2 : ℕ) + F (n + 1) ^ (2 : ℕ) := by
  rw [← hF.mul_succ_eq_pronicSeq n]
  unfold addDiff
  ring

/-- **Universal Finite Pronic–Diagonal–Gradient Conservation Identity
(`IsGcdLcmModular.sum_Icc_pronicSeq_add_addDiff_sq_eq`):**
For every `hF : IsGcdLcmModular F` and `N : ℕ`:
`2 * ∑_{n=1}^N F(pronicSeq n) + ∑_{n=1}^N (addDiff F n)² = 2 * ∑_{n=1}^N F(n)² + F(N + 1)² - 1`. -/
theorem sum_Icc_pronicSeq_add_addDiff_sq_eq {F : ℕ → ℝ} (hF : IsGcdLcmModular F) (N : ℕ) :
    2 * (∑ n ∈ Finset.Icc 1 N, F (pronicSeq n)) +
      (∑ n ∈ Finset.Icc 1 N, addDiff F n ^ (2 : ℕ)) =
      2 * (∑ n ∈ Finset.Icc 1 N, F n ^ (2 : ℕ)) + F (N + 1) ^ (2 : ℕ) - 1 := by
  have hsum :
      2 * (∑ n ∈ Finset.Icc 1 N, F (pronicSeq n)) +
        (∑ n ∈ Finset.Icc 1 N, addDiff F n ^ (2 : ℕ)) =
      ∑ n ∈ Finset.Icc 1 N, (F n ^ (2 : ℕ) + F (n + 1) ^ (2 : ℕ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    linarith [hF.addDiff_sq_add_two_mul_pronicSeq n]
  rw [hsum, sum_Icc_add_succ (fun n => F n ^ (2 : ℕ)) N, hF.map_one]
  ring

end IsGcdLcmModular

/-! ## §2. The General Radical Prime-Factor Functional (`radicalPrimeProd`) & Its Valuation Algebra -/

/-- The **general radical prime-factor product** associated to an arbitrary prime valuation weight
`w : ℕ → ℝ`:
`radicalPrimeProd w n = if n = 0 then 0 else ∏ p ∈ n.primeFactors, (1 - w p)`. -/
def radicalPrimeProd (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, (1 - w p)

@[simp]
theorem radicalPrimeProd_zero (w : ℕ → ℝ) :
    radicalPrimeProd w 0 = 0 := rfl

@[simp]
theorem radicalPrimeProd_one (w : ℕ → ℝ) :
    radicalPrimeProd w 1 = 1 := by
  unfold radicalPrimeProd
  simp

theorem radicalPrimeProd_eq_prod (w : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    radicalPrimeProd w n = ∏ p ∈ n.primeFactors, (1 - w p) :=
  if_neg hn

/-- **Radical Invariance of `radicalPrimeProd` (`radicalPrimeProd_eq_of_primeFactors_eq`):**
For every `w : ℕ → ℝ` and nonzero `m, n : ℕ` with `m.primeFactors = n.primeFactors`:
`radicalPrimeProd w m = radicalPrimeProd w n`. -/
theorem radicalPrimeProd_eq_of_primeFactors_eq (w : ℕ → ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hpf : m.primeFactors = n.primeFactors) :
    radicalPrimeProd w m = radicalPrimeProd w n := by
  rw [radicalPrimeProd_eq_prod w hm, radicalPrimeProd_eq_prod w hn, hpf]

/-- **Power Invariance of `radicalPrimeProd` (`radicalPrimeProd_pow`):**
For every `w : ℕ → ℝ`, `m : ℕ`, and `k ≠ 0`:
`radicalPrimeProd w (m ^ k) = radicalPrimeProd w m`. -/
theorem radicalPrimeProd_pow (w : ℕ → ℝ) (m : ℕ) {k : ℕ} (hk : k ≠ 0) :
    radicalPrimeProd w (m ^ k) = radicalPrimeProd w m := by
  by_cases hm : m = 0
  · subst hm; rw [zero_pow hk]
  · exact radicalPrimeProd_eq_of_primeFactors_eq w (pow_ne_zero k hm) hm
      (Nat.primeFactors_pow m hk)

@[simp]
theorem radicalPrimeProd_sq (w : ℕ → ℝ) (m : ℕ) :
    radicalPrimeProd w (m ^ (2 : ℕ)) = radicalPrimeProd w m :=
  radicalPrimeProd_pow w m (by decide : (2 : ℕ) ≠ 0)

@[simp]
theorem radicalPrimeProd_mul_self (w : ℕ → ℝ) (m : ℕ) :
    radicalPrimeProd w (m * m) = radicalPrimeProd w m := by
  rw [← sq, radicalPrimeProd_sq]

/-- **Divisor-Multiplication Absorption Law (`radicalPrimeProd_mul_of_dvd_right`):**
For every `w : ℕ → ℝ`, `d ≠ 0`, and `m : ℕ` with `d ∣ m`:
`radicalPrimeProd w (d * m) = radicalPrimeProd w m`. -/
theorem radicalPrimeProd_mul_of_dvd_right (w : ℕ → ℝ) {d m : ℕ}
    (hd : d ≠ 0) (hdvd : d ∣ m) :
    radicalPrimeProd w (d * m) = radicalPrimeProd w m := by
  by_cases hm : m = 0
  · subst hm; simp
  · apply radicalPrimeProd_eq_of_primeFactors_eq w (mul_ne_zero hd hm) hm
    rw [Nat.primeFactors_mul hd hm, Finset.union_eq_right]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hp.2.1.trans hdvd, hm⟩

theorem radicalPrimeProd_mul_of_dvd_left (w : ℕ → ℝ) {d m : ℕ}
    (hd : d ≠ 0) (hdvd : d ∣ m) :
    radicalPrimeProd w (m * d) = radicalPrimeProd w m := by
  rw [mul_comm, radicalPrimeProd_mul_of_dvd_right w hd hdvd]

/-- **Universal Product–GCD Multiplicativity Law for `radicalPrimeProd`
(`radicalPrimeProd_mul_eq_mul_gcd`):**
For every `w : ℕ → ℝ` and all `j, k : ℕ`:
`radicalPrimeProd w j * radicalPrimeProd w k = radicalPrimeProd w (j * k) * radicalPrimeProd w (Nat.gcd j k)`. -/
theorem radicalPrimeProd_mul_eq_mul_gcd (w : ℕ → ℝ) (j k : ℕ) :
    radicalPrimeProd w j * radicalPrimeProd w k =
      radicalPrimeProd w (j * k) * radicalPrimeProd w (Nat.gcd j k) := by
  by_cases hj : j = 0
  · subst hj; simp
  by_cases hk : k = 0
  · subst hk; simp
  have hjk : j * k ≠ 0 := mul_ne_zero hj hk
  have hgcd : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left hj
  rw [radicalPrimeProd_eq_prod w hj,
    radicalPrimeProd_eq_prod w hk,
    radicalPrimeProd_eq_prod w hjk,
    radicalPrimeProd_eq_prod w hgcd,
    ← Finset.prod_union_inter,
    Nat.primeFactors_mul hj hk,
    primeFactors_inter_eq_gcd hj hk]

/-- **LCM–Product Radical Equivalence for `radicalPrimeProd` (`radicalPrimeProd_lcm_eq_mul`):**
For every `w : ℕ → ℝ` and all `j, k : ℕ`:
`radicalPrimeProd w (Nat.lcm j k) = radicalPrimeProd w (j * k)`. -/
theorem radicalPrimeProd_lcm_eq_mul (w : ℕ → ℝ) (j k : ℕ) :
    radicalPrimeProd w (Nat.lcm j k) = radicalPrimeProd w (j * k) := by
  by_cases hj : j = 0
  · subst hj; simp
  by_cases hk : k = 0
  · subst hk; simp
  have hgcd : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left hj
  have hdvd : Nat.gcd j k ∣ Nat.lcm j k :=
    (Nat.gcd_dvd_left j k).trans (Nat.dvd_lcm_left j k)
  rw [← Nat.gcd_mul_lcm j k,
    radicalPrimeProd_mul_of_dvd_right w hgcd hdvd]

/-- **Universal GCD–LCM Modularity of `radicalPrimeProd` (`isGcdLcmModular_radicalPrimeProd`):**
For every prime valuation weight `w : ℕ → ℝ`, `radicalPrimeProd w` is GCD–LCM modular. -/
theorem isGcdLcmModular_radicalPrimeProd (w : ℕ → ℝ) :
    IsGcdLcmModular (radicalPrimeProd w) := by
  refine ⟨radicalPrimeProd_one w, fun j k => ?_⟩
  rw [radicalPrimeProd_lcm_eq_mul, radicalPrimeProd_mul_eq_mul_gcd]

/-- For every `w : ℕ → ℝ` and prime `p`, `radicalPrimeProd w p = 1 - w p`. -/
theorem radicalPrimeProd_prime (w : ℕ → ℝ) {p : ℕ} (hp : Nat.Prime p) :
    radicalPrimeProd w p = 1 - w p := by
  rw [radicalPrimeProd_eq_prod w hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

/-- For every `w : ℕ → ℝ`, prime `p`, and `k ≠ 0`, `radicalPrimeProd w (p ^ k) = 1 - w p`. -/
theorem radicalPrimeProd_prime_pow (w : ℕ → ℝ) {p k : ℕ}
    (hp : Nat.Prime p) (hk : k ≠ 0) :
    radicalPrimeProd w (p ^ k) = 1 - w p := by
  rw [radicalPrimeProd_pow w p hk, radicalPrimeProd_prime w hp]

/-- **Wall 11 Evaluation for `radicalPrimeProd` (`radicalPrimeProd_four_and_six`):**
For every prime valuation weight `w : ℕ → ℝ`:
`radicalPrimeProd w 4 = 1 - w 2` and `radicalPrimeProd w 6 = (1 - w 2) * (1 - w 3)`. -/
theorem radicalPrimeProd_four_and_six (w : ℕ → ℝ) :
    radicalPrimeProd w 4 = 1 - w 2 ∧
      radicalPrimeProd w 6 = (1 - w 2) * (1 - w 3) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [h4, radicalPrimeProd_sq, radicalPrimeProd_prime w Nat.prime_two]
  · rw [h6, (isGcdLcmModular_radicalPrimeProd w).map_mul_of_coprime (by decide),
      radicalPrimeProd_prime w Nat.prime_two, radicalPrimeProd_prime w Nat.prime_three]

/-- **Divisor-Quotient Factorization of `radicalPrimeProd`
(`radicalPrimeProd_eq_mul_sdiff_of_dvd`):**
For every `w : ℕ → ℝ` and `d, m : ℕ` with `d ∣ m` and `m ≠ 0`:
`radicalPrimeProd w m = radicalPrimeProd w d * ∏ p ∈ m.primeFactors \ d.primeFactors, (1 - w p)`. -/
theorem radicalPrimeProd_eq_mul_sdiff_of_dvd (w : ℕ → ℝ) {d m : ℕ}
    (hdvd : d ∣ m) (hm : m ≠ 0) :
    radicalPrimeProd w m =
      radicalPrimeProd w d * ∏ p ∈ m.primeFactors \ d.primeFactors, (1 - w p) := by
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hm hdvd
  have hsub : d.primeFactors ⊆ m.primeFactors := Nat.primeFactors_mono hdvd hm
  rw [radicalPrimeProd_eq_prod w hm,
    radicalPrimeProd_eq_prod w hd,
    ← Finset.prod_union disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset hsub]

/-- **Exact Identification of `pmPowerDampedDivisorCoeff ε` as a `radicalPrimeProd`
(`pmPowerDampedDivisorCoeff_eq_radicalPrimeProd`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedDivisorCoeff ε n = radicalPrimeProd (fun p => (p : ℝ) ^ (-ε)) n`. -/
theorem pmPowerDampedDivisorCoeff_eq_radicalPrimeProd (ε : ℝ) (n : ℕ) :
    pmPowerDampedDivisorCoeff ε n =
      radicalPrimeProd (fun p => (p : ℝ) ^ (-ε)) n := by
  by_cases hn : n = 0
  · subst hn; simp [pmPowerDampedDivisorCoeff_zero]
  · rw [pmPowerDampedDivisorCoeff_eq_prod ε hn, radicalPrimeProd_eq_prod _ hn]

/-! ## §3. Universal Antitonicity, Submultiplicativity & Primorial Bézout Ceilings -/

/-- For every valuation weight `w : ℕ → ℝ` satisfying `w p ≤ 1` on primes and every `n : ℕ`,
`0 ≤ radicalPrimeProd w n`. -/
theorem radicalPrimeProd_nonneg {w : ℕ → ℝ}
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1) (n : ℕ) :
    0 ≤ radicalPrimeProd w n := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [radicalPrimeProd_eq_prod w hn]
    exact Finset.prod_nonneg fun p hp =>
      sub_nonneg.mpr (hw1 p (Nat.prime_of_mem_primeFactors hp))

/-- For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and every `n : ℕ`,
`radicalPrimeProd w n ≤ 1`. -/
theorem radicalPrimeProd_le_one {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1) (n : ℕ) :
    radicalPrimeProd w n ≤ 1 := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [radicalPrimeProd_eq_prod w hn]
    apply Finset.prod_le_one
    · intro p hp
      exact sub_nonneg.mpr (hw1 p (Nat.prime_of_mem_primeFactors hp))
    · intro p hp
      linarith [hw0 p (Nat.prime_of_mem_primeFactors hp)]

/-- **Universal Divisor-Ordering Antitonicity of `radicalPrimeProd`
(`radicalPrimeProd_le_of_dvd`):**
For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and `d, m : ℕ` with
`d ∣ m` and `m ≠ 0`:
`radicalPrimeProd w m ≤ radicalPrimeProd w d`. -/
theorem radicalPrimeProd_le_of_dvd {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1)
    {d m : ℕ} (hdvd : d ∣ m) (hm : m ≠ 0) :
    radicalPrimeProd w m ≤ radicalPrimeProd w d := by
  rw [radicalPrimeProd_eq_mul_sdiff_of_dvd w hdvd hm]
  have hd0 : 0 ≤ radicalPrimeProd w d := radicalPrimeProd_nonneg hw1 d
  have hprod : (∏ p ∈ m.primeFactors \ d.primeFactors, (1 - w p)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      exact sub_nonneg.mpr (hw1 p (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1))
    · intro p hp
      linarith [hw0 p (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)]
  calc
    radicalPrimeProd w d * ∏ p ∈ m.primeFactors \ d.primeFactors, (1 - w p)
      ≤ radicalPrimeProd w d * 1 := mul_le_mul_of_nonneg_left hprod hd0
    _ = radicalPrimeProd w d := mul_one _

/-- **Universal Submultiplicativity of `radicalPrimeProd` (`radicalPrimeProd_mul_le`):**
For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and all `a, b : ℕ`:
`radicalPrimeProd w a * radicalPrimeProd w b ≤ radicalPrimeProd w (a * b)`. -/
theorem radicalPrimeProd_mul_le {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1) (a b : ℕ) :
    radicalPrimeProd w a * radicalPrimeProd w b ≤ radicalPrimeProd w (a * b) := by
  rw [radicalPrimeProd_mul_eq_mul_gcd]
  have hab0 := radicalPrimeProd_nonneg hw1 (a * b)
  have hgcd1 := radicalPrimeProd_le_one hw0 hw1 (Nat.gcd a b)
  nlinarith

/-- **Universal `2`-Adic Pronic Ceiling for `radicalPrimeProd`
(`radicalPrimeProd_pronicSeq_le_two`):**
For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and every `k ≥ 1`:
`radicalPrimeProd w k * radicalPrimeProd w (k + 1) = radicalPrimeProd w (pronicSeq k) ≤ 1 - w 2`. -/
theorem radicalPrimeProd_pronicSeq_le_two {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    radicalPrimeProd w (pronicSeq k) ≤ 1 - w 2 := by
  have hle := radicalPrimeProd_le_of_dvd hw0 hw1 (two_dvd_pronicSeq k) (pronicSeq_ne_zero hk)
  rwa [radicalPrimeProd_prime w Nat.prime_two] at hle

/-- **Universal `6`-Adic Pronic Ceiling on `3`-Divisible Bézout Nodes
(`radicalPrimeProd_pronicSeq_le_six_of_three_dvd`):**
For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and every `k ≥ 1` with
`3 ∣ k ∨ 3 ∣ (k + 1)`:
`radicalPrimeProd w (pronicSeq k) ≤ (1 - w 2) * (1 - w 3)`. -/
theorem radicalPrimeProd_pronicSeq_le_six_of_three_dvd {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) (h3 : 3 ∣ k ∨ 3 ∣ (k + 1)) :
    radicalPrimeProd w (pronicSeq k) ≤ (1 - w 2) * (1 - w 3) := by
  have hle := radicalPrimeProd_le_of_dvd hw0 hw1
    (six_dvd_pronicSeq_of_three_dvd h3) (pronicSeq_ne_zero hk)
  rwa [(radicalPrimeProd_four_and_six w).2] at hle

/-- **Universal Three-Step `6`-Adic Bézout Product Ceiling for `radicalPrimeProd`
(`radicalPrimeProd_three_step_mul_le_six`):**
For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and every `k ≥ 1`:
`radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2) ≤ (1 - w 2) * (1 - w 3)`. -/
theorem radicalPrimeProd_three_step_mul_le_six {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2) ≤
      (1 - w 2) * (1 - w 3) := by
  have h12 : radicalPrimeProd w k * radicalPrimeProd w (k + 1) =
      radicalPrimeProd w (k * (k + 1)) :=
    (isGcdLcmModular_radicalPrimeProd w).mul_succ_eq_pronicSeq k
  have h123 : radicalPrimeProd w (k * (k + 1)) * radicalPrimeProd w (k + 2) ≤
      radicalPrimeProd w (k * (k + 1) * (k + 2)) :=
    radicalPrimeProd_mul_le hw0 hw1 (k * (k + 1)) (k + 2)
  have hne : k * (k + 1) * (k + 2) ≠ 0 := by positivity
  have h6 := radicalPrimeProd_le_of_dvd hw0 hw1 (six_dvd_mul_succ_mul_add_two k) hne
  rw [(radicalPrimeProd_four_and_six w).2] at h6
  rw [h12]
  exact h123.trans h6

end
end GaloisForLFunctions.BezoutValuationIncidence
