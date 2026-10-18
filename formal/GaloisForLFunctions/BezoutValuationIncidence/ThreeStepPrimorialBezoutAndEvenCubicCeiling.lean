import GaloisForLFunctions.BezoutValuationIncidence.GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra

/-!
# Pillar XXX: Three-Step Primorial Bézout Hierarchy, `24`-Divisibility & Sharp Even-Start Cubic Ceilings

In Pillar XXIX (`GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra`), we established the
autonomous algebra of GCD–LCM modular and radical-multiplicative functions (`radicalPrimeProd w`)
and proved the universal three-step $6$-adic ceiling
$$\operatorname{radicalPrimeProd}\,w\,k \cdot \operatorname{radicalPrimeProd}\,w\,(k + 1) \cdot
  \operatorname{radicalPrimeProd}\,w\,(k + 2) \le (1 - w(2))(1 - w(3)).$$

In this thirtieth pillar of **Bézout–Valuation Incidence Mechanics**, we ascend the primorial
Bézout hierarchy from 2-step pronic pairs $(k, k + 1)$ to 3-step consecutive triples
$(k, k + 1, k + 2)$, establishing three new foundational mechanisms:

1. **Arithmetic Structure & `24`-Divisibility of Even-Start Three-Step Triples
   (`gcd_self_add_two_eq_gcd_two`,
   `coprime_mul_add_two_succ`,
   `eight_dvd_mul_add_two_of_two_dvd`,
   `twenty_four_dvd_mul_succ_mul_add_two_of_two_dvd`)**:
   - For every $k \in \mathbb{N}$, $\gcd(k, k + 2) = \gcd(k, 2) \in \{1, 2\}$, while $k(k + 2)$ is
     always coprime to the middle integer $k + 1$: $\gcd\bigl(k(k + 2),\,k + 1\bigr) = 1$.
   - Whenever $k$ is even ($2 \mid k$, $k = 2m$), $k(k + 2) = 4\,\operatorname{pronicSeq}\,m$ is
     divisible by $8$, so the 3-step product $k(k + 1)(k + 2)$ is divisible by **$24 = 2^3 \cdot 3$**
     for every even $k \in \mathbb{N}$.

2. **Exact Three-Step Bézout Factorization Law for `radicalPrimeProd` & `pmPowerDampedDivisorCoeff`
   (`radicalPrimeProd_three_step_mul_eq`,
   `pmPowerDampedDivisorCoeff_three_step_mul_eq`)**:
   - Combining `radicalPrimeProd_mul_eq_mul_gcd w k (k + 2)` with $\gcd\bigl(k(k + 2), k + 1\bigr) = 1$
     gives the **Exact Three-Step Bézout Factorization Identity** for all $w : \mathbb{N} \to \mathbb{R}$
     and all $k \in \mathbb{N}$:
     $$\operatorname{radicalPrimeProd}\,w\,k \cdot \operatorname{radicalPrimeProd}\,w\,(k + 1) \cdot \operatorname{radicalPrimeProd}\,w\,(k + 2)
       = \bigl(\text{if } 2 \mid k \text{ then } 1 - w(2) \text{ else } 1\bigr) \cdot
         \operatorname{radicalPrimeProd}\,w\,\bigl(k(k + 1)(k + 2)\bigr).$$
   - When $k$ is odd, $(k, k + 1, k + 2)$ are pairwise coprime and the 3-step product factors
     purely as $\operatorname{radicalPrimeProd}\,w\,\bigl(k(k + 1)(k + 2)\bigr)$; when $k$ is even,
     the shared $2$-adic valuation between $k$ and $k + 2$ contributes an **extra factor of
     $1 - w(2)$**.

3. **Sharp Cubic $(1 - w(2))^2(1 - w(3))$ Ceiling on Even-Start Triples & Exact Extremal Realizations
   (`radicalPrimeProd_three_step_mul_le_cubic_of_two_dvd`,
   `pmPowerDampedDivisorCoeff_three_step_mul_le_cubic_of_two_dvd`,
   `pmPowerDampedDivisorCoeff_one_mul_two_mul_three`,
   `pmPowerDampedDivisorCoeff_two_mul_three_mul_four`)**:
   - For every valuation weight $w$ taking values in $[0, 1]$ on primes and every even $k \ge 1$
     ($2 \mid k$), the 3-step product obeys the **cubic ceiling**:
     $$\operatorname{radicalPrimeProd}\,w\,k \cdot \operatorname{radicalPrimeProd}\,w\,(k + 1) \cdot \operatorname{radicalPrimeProd}\,w\,(k + 2)
       \le (1 - w(2))^2 (1 - w(3)).$$
   - Both ceilings are **sharp**: at $k = 1$ (odd start), $\tau_\varepsilon(1)\,\tau_\varepsilon(2)\,\tau_\varepsilon(3) = (1 - 2^{-\varepsilon})(1 - 3^{-\varepsilon})$,
     and at $k = 2$ (even start, $2 \cdot 3 \cdot 4 = 24$),
     $\tau_\varepsilon(2)\,\tau_\varepsilon(3)\,\tau_\varepsilon(4) = (1 - 2^{-\varepsilon})^2 (1 - 3^{-\varepsilon})$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Arithmetic Structure & `24`-Divisibility of Three-Step Consecutive Triples -/

/-- For every `k : ℕ`, `Nat.gcd k (k + 2) = Nat.gcd k 2`. -/
theorem gcd_self_add_two_eq_gcd_two (k : ℕ) :
    Nat.gcd k (k + 2) = Nat.gcd k 2 :=
  Nat.gcd_self_add_right k 2

/-- Whenever `2 ∣ k`, `Nat.gcd k (k + 2) = 2`. -/
theorem gcd_self_add_two_eq_two_of_two_dvd {k : ℕ} (h2 : 2 ∣ k) :
    Nat.gcd k (k + 2) = 2 := by
  rw [gcd_self_add_two_eq_gcd_two]
  exact Nat.gcd_eq_right h2

/-- Whenever `¬ (2 ∣ k)`, `Nat.Coprime k (k + 2)`. -/
theorem coprime_self_add_two_of_not_two_dvd {k : ℕ} (h2 : ¬ (2 ∣ k)) :
    Nat.Coprime k (k + 2) := by
  unfold Nat.Coprime
  rw [gcd_self_add_two_eq_gcd_two, Nat.gcd_comm]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2

/-- For **every** `k : ℕ`, the outer product `k * (k + 2)` is coprime to the middle integer `k + 1`. -/
theorem coprime_mul_add_two_succ (k : ℕ) :
    Nat.Coprime (k * (k + 2)) (k + 1) :=
  Nat.Coprime.mul_left (coprime_self_succ k) (coprime_self_succ (k + 1)).symm

/-- For every even integer `2 * m`, `(2 * m) * (2 * m + 2) = 4 * pronicSeq m`. -/
theorem two_mul_mul_two_mul_add_two_eq_four_mul_pronicSeq (m : ℕ) :
    (2 * m) * (2 * m + 2) = 4 * pronicSeq m := by
  unfold pronicSeq
  ring

/-- Whenever `2 ∣ k`, `8 ∣ k * (k + 2)`. -/
theorem eight_dvd_mul_add_two_of_two_dvd {k : ℕ} (h2 : 2 ∣ k) :
    8 ∣ k * (k + 2) := by
  rcases h2 with ⟨m, rfl⟩
  rw [two_mul_mul_two_mul_add_two_eq_four_mul_pronicSeq]
  rcases two_dvd_pronicSeq m with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq]
  ring

/-- **Universal `24`-Divisibility of Even-Start Three-Step Products
(`twenty_four_dvd_mul_succ_mul_add_two_of_two_dvd`):**
Whenever `2 ∣ k`, `24 ∣ k * (k + 1) * (k + 2)`. -/
theorem twenty_four_dvd_mul_succ_mul_add_two_of_two_dvd {k : ℕ} (h2 : 2 ∣ k) :
    24 ∣ k * (k + 1) * (k + 2) := by
  have h8 : 8 ∣ k * (k + 1) * (k + 2) := by
    rw [mul_right_comm]
    exact dvd_mul_of_dvd_left (eight_dvd_mul_add_two_of_two_dvd h2) (k + 1)
  have h3 : 3 ∣ k * (k + 1) * (k + 2) := three_dvd_mul_succ_mul_add_two k
  exact (show Nat.Coprime 8 3 by decide).mul_dvd_of_dvd_of_dvd h8 h3

/-! ## §2. Exact Three-Step Bézout Factorization Law for `radicalPrimeProd` & `pmPowerDampedDivisorCoeff` -/

/-- **Outer-Pair Bézout Factorization Law (`radicalPrimeProd_mul_add_two_eq`):**
For every `w : ℕ → ℝ` and `k : ℕ`:
`radicalPrimeProd w k * radicalPrimeProd w (k + 2) = (if 2 ∣ k then 1 - w 2 else 1) * radicalPrimeProd w (k * (k + 2))`. -/
theorem radicalPrimeProd_mul_add_two_eq (w : ℕ → ℝ) (k : ℕ) :
    radicalPrimeProd w k * radicalPrimeProd w (k + 2) =
      (if 2 ∣ k then 1 - w 2 else 1) * radicalPrimeProd w (k * (k + 2)) := by
  rw [radicalPrimeProd_mul_eq_mul_gcd, mul_comm]
  congr 1
  split_ifs with h2
  · rw [gcd_self_add_two_eq_two_of_two_dvd h2, radicalPrimeProd_prime w Nat.prime_two]
  · rw [coprime_self_add_two_of_not_two_dvd h2, radicalPrimeProd_one]

/-- **Exact Three-Step Bézout Factorization Law for `radicalPrimeProd`
(`radicalPrimeProd_three_step_mul_eq`):**
For every prime valuation weight `w : ℕ → ℝ` and every `k : ℕ`:
`radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2) = (if 2 ∣ k then 1 - w 2 else 1) * radicalPrimeProd w (k * (k + 1) * (k + 2))`. -/
theorem radicalPrimeProd_three_step_mul_eq (w : ℕ → ℝ) (k : ℕ) :
    radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2) =
      (if 2 ∣ k then 1 - w 2 else 1) *
        radicalPrimeProd w (k * (k + 1) * (k + 2)) := by
  have houter := radicalPrimeProd_mul_add_two_eq w k
  have hcop := (isGcdLcmModular_radicalPrimeProd w).map_mul_of_coprime (coprime_mul_add_two_succ k)
  rw [mul_right_comm (k : ℕ) (k + 2) (k + 1)] at hcop
  calc
    radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2)
      = (radicalPrimeProd w k * radicalPrimeProd w (k + 2)) * radicalPrimeProd w (k + 1) := by ring
    _ = (if 2 ∣ k then 1 - w 2 else 1) *
          (radicalPrimeProd w (k * (k + 2)) * radicalPrimeProd w (k + 1)) := by
        rw [houter, mul_assoc]
    _ = (if 2 ∣ k then 1 - w 2 else 1) *
          radicalPrimeProd w (k * (k + 1) * (k + 2)) := by rw [← hcop]

/-- **Exact Three-Step Bézout Factorization Law for `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_three_step_mul_eq`):**
For every `ε : ℝ` and `k : ℕ`:
`τ_ε(k) * τ_ε(k + 1) * τ_ε(k + 2) = (if 2 ∣ k then 1 - 2^{-ε} else 1) * τ_ε(k * (k + 1) * (k + 2))`. -/
theorem pmPowerDampedDivisorCoeff_three_step_mul_eq (ε : ℝ) (k : ℕ) :
    pmPowerDampedDivisorCoeff ε k *
      pmPowerDampedDivisorCoeff ε (k + 1) *
      pmPowerDampedDivisorCoeff ε (k + 2) =
      (if 2 ∣ k then 1 - (2 : ℝ) ^ (-ε) else 1) *
        pmPowerDampedDivisorCoeff ε (k * (k + 1) * (k + 2)) := by
  simp_rw [pmPowerDampedDivisorCoeff_eq_radicalPrimeProd]
  exact radicalPrimeProd_three_step_mul_eq (fun p => (p : ℝ) ^ (-ε)) k

/-! ## §3. Sharp Cubic Ceiling on Even-Start Triples & Exact Extremal Realizations -/

/-- **Sharp Cubic `(1 - w 2)² * (1 - w 3)` Ceiling on Even-Start Three-Step Products
(`radicalPrimeProd_three_step_mul_le_cubic_of_two_dvd`):**
For every valuation weight `w : ℕ → ℝ` taking values in `[0, 1]` on primes and every `k ≥ 1` with
`2 ∣ k`:
`radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2) ≤ (1 - w 2) ^ 2 * (1 - w 3)`. -/
theorem radicalPrimeProd_three_step_mul_le_cubic_of_two_dvd {w : ℕ → ℝ}
    (hw0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ w p)
    (hw1 : ∀ p : ℕ, Nat.Prime p → w p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) (h2 : 2 ∣ k) :
    radicalPrimeProd w k * radicalPrimeProd w (k + 1) * radicalPrimeProd w (k + 2) ≤
      (1 - w 2) ^ (2 : ℕ) * (1 - w 3) := by
  rw [radicalPrimeProd_three_step_mul_eq, if_pos h2]
  have hne : k * (k + 1) * (k + 2) ≠ 0 := by positivity
  have h6 := radicalPrimeProd_le_of_dvd hw0 hw1 (six_dvd_mul_succ_mul_add_two k) hne
  rw [(radicalPrimeProd_four_and_six w).2] at h6
  have hw2 : 0 ≤ 1 - w 2 := sub_nonneg.mpr (hw1 2 Nat.prime_two)
  calc
    (1 - w 2) * radicalPrimeProd w (k * (k + 1) * (k + 2))
      ≤ (1 - w 2) * ((1 - w 2) * (1 - w 3)) := mul_le_mul_of_nonneg_left h6 hw2
    _ = (1 - w 2) ^ (2 : ℕ) * (1 - w 3) := by ring

/-- **Sharp Cubic `(1 - 2^{-ε})² * (1 - 3^{-ε})` Ceiling on Even-Start Three-Step Products for `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_three_step_mul_le_cubic_of_two_dvd`):**
For every `ε ≥ 0` and every `k ≥ 1` with `2 ∣ k`:
`τ_ε(k) * τ_ε(k + 1) * τ_ε(k + 2) ≤ (1 - 2^{-ε}) ^ 2 * (1 - 3^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_three_step_mul_le_cubic_of_two_dvd
    {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} (hk : 1 ≤ k) (h2 : 2 ∣ k) :
    pmPowerDampedDivisorCoeff ε k *
      pmPowerDampedDivisorCoeff ε (k + 1) *
      pmPowerDampedDivisorCoeff ε (k + 2) ≤
      (1 - (2 : ℝ) ^ (-ε)) ^ (2 : ℕ) * (1 - (3 : ℝ) ^ (-ε)) := by
  rw [pmPowerDampedDivisorCoeff_three_step_mul_eq, if_pos h2]
  have hne : k * (k + 1) * (k + 2) ≠ 0 := by positivity
  have h6 := pmPowerDampedDivisorCoeff_le_of_dvd hε (six_dvd_mul_succ_mul_add_two k) hne
  rw [(pmPowerDampedDivisorCoeff_four_and_six ε).2.1] at h6
  have hw2 : 0 ≤ 1 - (2 : ℝ) ^ (-ε) :=
    sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
  calc
    (1 - (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε (k * (k + 1) * (k + 2))
      ≤ (1 - (2 : ℝ) ^ (-ε)) * ((1 - (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε))) :=
        mul_le_mul_of_nonneg_left h6 hw2
    _ = (1 - (2 : ℝ) ^ (-ε)) ^ (2 : ℕ) * (1 - (3 : ℝ) ^ (-ε)) := by ring

/-- **Exact Odd-Start Attainment at `k = 1` (`pmPowerDampedDivisorCoeff_one_mul_two_mul_three`):**
For every `ε : ℝ`, `τ_ε(1) * τ_ε(2) * τ_ε(3) = (1 - 2^{-ε}) * (1 - 3^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_one_mul_two_mul_three (ε : ℝ) :
    pmPowerDampedDivisorCoeff ε 1 *
      pmPowerDampedDivisorCoeff ε 2 *
      pmPowerDampedDivisorCoeff ε 3 =
      (1 - (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε)) := by
  have h := pmPowerDampedDivisorCoeff_three_step_mul_eq ε 1
  norm_num at h
  rw [h, (pmPowerDampedDivisorCoeff_four_and_six ε).2.1]

/-- **Exact Even-Start Cubic Attainment at `k = 2` (`pmPowerDampedDivisorCoeff_two_mul_three_mul_four`):**
For every `ε : ℝ`, `τ_ε(2) * τ_ε(3) * τ_ε(4) = (1 - 2^{-ε}) ^ 2 * (1 - 3^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_two_mul_three_mul_four (ε : ℝ) :
    pmPowerDampedDivisorCoeff ε 2 *
      pmPowerDampedDivisorCoeff ε 3 *
      pmPowerDampedDivisorCoeff ε 4 =
      (1 - (2 : ℝ) ^ (-ε)) ^ (2 : ℕ) * (1 - (3 : ℝ) ^ (-ε)) := by
  rw [pmPowerDampedDivisorCoeff_prime ε Nat.prime_two,
    pmPowerDampedDivisorCoeff_prime ε Nat.prime_three,
    (pmPowerDampedDivisorCoeff_four_and_six ε).1]
  push_cast
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
