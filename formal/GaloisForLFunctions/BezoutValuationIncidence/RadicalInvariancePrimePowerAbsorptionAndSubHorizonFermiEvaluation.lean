import GaloisForLFunctions.BezoutValuationIncidence.AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization

/-!
# Pillar XV: Radical Invariance, Divisor Absorption, & Sub-Horizon Fermi–Nyman Jump Dichotomy

In this fifteenth pillar of **Bézout–Valuation Incidence Mechanics**, we establish the **Radical
Invariance and Divisor Absorption Laws** of `pmPowerDampedDivisorCoeff ε` and their exact impact on
the sub-horizon cellular dynamics of `fermiCellResponse N (pmPowerDampedRealWeight ε)`:

## Core Main Theorems (100% Unconditional)

1. **Radical Invariance, Power Invariance, & Divisor-Multiplication Absorption
   (`pmPowerDampedDivisorCoeff_eq_of_primeFactors_eq`,
   `pmPowerDampedDivisorCoeff_pow`,
   `pmPowerDampedDivisorCoeff_sq`,
   `pmPowerDampedDivisorCoeff_mul_of_dvd_right`)**:
   Because `pmPowerDampedRealWeight ε d = μ(d) d^{-ε}` is supported on squarefree divisors,
   `pmPowerDampedDivisorCoeff ε n = ∏_{p ∈ n.primeFactors} (1 - p^{-ε})` depends on `n ≠ 0`
   **only through its radical (`n.primeFactors`)**. Consequently:
   - For every `k ≠ 0` and every `m : ℕ`, `pmPowerDampedDivisorCoeff ε (m ^ k) = pmPowerDampedDivisorCoeff ε m`.
   - For every `d ≠ 0` and `m : ℕ` with `d ∣ m`, multiplying `m` by `d` adds no new prime factors:
     $$\operatorname{pmPowerDampedDivisorCoeff}\,\varepsilon\,(d \cdot m) =
       \operatorname{pmPowerDampedDivisorCoeff}\,\varepsilon\,m.$$

2. **Prime-Multiplication & Dyadic Doubling Dichotomy
   (`pmPowerDampedDivisorCoeff_prime_mul`,
   `pmPowerDampedDivisorCoeff_two_mul`,
   `two_mul_pmPowerDampedDivisorCoeff_sub_two_mul`)**:
   For every prime `p` and every `m : ℕ`:
   $$\operatorname{pmPowerDampedDivisorCoeff}\,\varepsilon\,(p \cdot m) =
     \bigl(\text{if } p \mid m \text{ then } 1 \text{ else } 1 - p^{-\varepsilon}\bigr) \cdot
     \operatorname{pmPowerDampedDivisorCoeff}\,\varepsilon\,m.$$
   Specializing to `p = 2`, the dyadic parent-child combination `2 τ_ε(m) - τ_ε(2m)` splits by the
   parity of `m`:
   $$2\,\tau_\varepsilon(m) - \tau_\varepsilon(2m) =
     \bigl(\text{if } 2 \mid m \text{ then } 1 \text{ else } 1 + 2^{-\varepsilon}\bigr)\,\tau_\varepsilon(m).$$

3. **Sub-Horizon Fermi–Nyman Jump Dichotomy & Wall 11 Jump Contrast (`4 = 2²` vs. `6 = 2 · 3`)
   (`fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_sub_two_mul`,
   `fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul_add_one`,
   `fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul`,
   `fermiCellResponse_pmPowerDampedRealWeight_jump_four_and_six`)**:
   In the sub-horizon bulk (`2m + 2 ≤ N`):
   - Every even-to-odd sibling step `2m ↦ 2m + 1` jumps by `-τ_ε(2m + 1)`.
   - Every odd-to-even boundary step `2m + 1 ↦ 2m + 2` jumps by
     `(if 2 ∣ (m + 1) then 1 else 1 + 2^{-ε}) * τ_ε(m + 1)`.
   - At `4 = 2²` (`m + 1 = 2`, even, `log 4`), the odd-to-even jump is `1 - 2^{-ε}`, whereas at
     `6 = 2 · 3` (`m + 1 = 3`, odd, `log 6`), the odd-to-even jump is amplified by `1 + 2^{-ε}` to
     `(1 + 2^{-ε})(1 - 3^{-ε})`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Radical Invariance, Power Invariance, & Divisor-Multiplication Absorption -/

/-- **Radical Invariance of `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_eq_of_primeFactors_eq`):**
For every `ε : ℝ` and nonzero `m, n : ℕ` with the same prime factors (`m.primeFactors = n.primeFactors`),
`pmPowerDampedDivisorCoeff ε m = pmPowerDampedDivisorCoeff ε n`. -/
theorem pmPowerDampedDivisorCoeff_eq_of_primeFactors_eq (ε : ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hpf : m.primeFactors = n.primeFactors) :
    pmPowerDampedDivisorCoeff ε m = pmPowerDampedDivisorCoeff ε n := by
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hm, pmPowerDampedDivisorCoeff_eq_prod ε hn, hpf]

/-- **Power Invariance of `pmPowerDampedDivisorCoeff` (`pmPowerDampedDivisorCoeff_pow`):**
For every `ε : ℝ`, `m : ℕ`, and nonzero exponent `k ≠ 0`:
`pmPowerDampedDivisorCoeff ε (m ^ k) = pmPowerDampedDivisorCoeff ε m`. -/
theorem pmPowerDampedDivisorCoeff_pow (ε : ℝ) (m : ℕ) {k : ℕ} (hk : k ≠ 0) :
    pmPowerDampedDivisorCoeff ε (m ^ k) = pmPowerDampedDivisorCoeff ε m := by
  by_cases hm : m = 0
  · subst hm
    rw [zero_pow hk]
  · exact pmPowerDampedDivisorCoeff_eq_of_primeFactors_eq ε (pow_ne_zero k hm) hm
      (Nat.primeFactors_pow m hk)

/-- **Square Invariance of `pmPowerDampedDivisorCoeff` (`pmPowerDampedDivisorCoeff_sq`):**
For every `ε : ℝ` and `m : ℕ`, `pmPowerDampedDivisorCoeff ε (m ^ 2) = pmPowerDampedDivisorCoeff ε m`. -/
@[simp]
theorem pmPowerDampedDivisorCoeff_sq (ε : ℝ) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε (m ^ (2 : ℕ)) = pmPowerDampedDivisorCoeff ε m :=
  pmPowerDampedDivisorCoeff_pow ε m (by decide : (2 : ℕ) ≠ 0)

/-- **Self-Multiplication Invariance of `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_mul_self`):**
For every `ε : ℝ` and `m : ℕ`, `pmPowerDampedDivisorCoeff ε (m * m) = pmPowerDampedDivisorCoeff ε m`. -/
@[simp]
theorem pmPowerDampedDivisorCoeff_mul_self (ε : ℝ) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε (m * m) = pmPowerDampedDivisorCoeff ε m := by
  rw [← sq, pmPowerDampedDivisorCoeff_sq]

/-- **Divisor-Multiplication Absorption Law (`pmPowerDampedDivisorCoeff_mul_of_dvd_right`):**
For every `ε : ℝ`, nonzero `d ≠ 0`, and `m : ℕ` such that `d ∣ m`, multiplying `m` by `d` leaves
`pmPowerDampedDivisorCoeff ε` unchanged:
`pmPowerDampedDivisorCoeff ε (d * m) = pmPowerDampedDivisorCoeff ε m`. -/
theorem pmPowerDampedDivisorCoeff_mul_of_dvd_right (ε : ℝ) {d m : ℕ}
    (hd : d ≠ 0) (hdvd : d ∣ m) :
    pmPowerDampedDivisorCoeff ε (d * m) = pmPowerDampedDivisorCoeff ε m := by
  by_cases hm : m = 0
  · subst hm
    simp
  · apply pmPowerDampedDivisorCoeff_eq_of_primeFactors_eq ε (mul_ne_zero hd hm) hm
    rw [Nat.primeFactors_mul hd hm, Finset.union_eq_right]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hp.2.1.trans hdvd, hm⟩

/-- Symmetric right-divisor absorption: if `d ≠ 0` and `d ∣ m`, then
`pmPowerDampedDivisorCoeff ε (m * d) = pmPowerDampedDivisorCoeff ε m`. -/
theorem pmPowerDampedDivisorCoeff_mul_of_dvd_left (ε : ℝ) {d m : ℕ}
    (hd : d ≠ 0) (hdvd : d ∣ m) :
    pmPowerDampedDivisorCoeff ε (m * d) = pmPowerDampedDivisorCoeff ε m := by
  rw [mul_comm, pmPowerDampedDivisorCoeff_mul_of_dvd_right ε hd hdvd]

/-! ## §2. Prime-Multiplication & Dyadic Doubling Dichotomy -/

/-- For every `ε : ℝ` and prime `p`, `pmPowerDampedDivisorCoeff ε p = 1 - (p : ℝ) ^ (-ε)`. -/
theorem pmPowerDampedDivisorCoeff_prime (ε : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    pmPowerDampedDivisorCoeff ε p = 1 - (p : ℝ) ^ (-ε) := by
  simpa only [pow_one] using pmPowerDampedDivisorCoeff_prime_pow ε hp one_ne_zero

/-- If `p` is prime and `¬ (p ∣ m)`, then
`pmPowerDampedDivisorCoeff ε (p * m) = (1 - (p : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m`. -/
theorem pmPowerDampedDivisorCoeff_prime_mul_of_not_dvd (ε : ℝ) {p m : ℕ}
    (hp : Nat.Prime p) (hndvd : ¬ (p ∣ m)) :
    pmPowerDampedDivisorCoeff ε (p * m) =
      (1 - (p : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m := by
  have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hndvd
  rw [pmPowerDampedDivisorCoeff_mul_of_coprime ε hcop, pmPowerDampedDivisorCoeff_prime ε hp]

/-- **Prime-Multiplication Dichotomy for `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_prime_mul`):**
For every `ε : ℝ`, prime `p`, and `m : ℕ`:
`pmPowerDampedDivisorCoeff ε (p * m) = (if p ∣ m then 1 else 1 - (p : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m`. -/
theorem pmPowerDampedDivisorCoeff_prime_mul (ε : ℝ) {p : ℕ} (hp : Nat.Prime p) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε (p * m) =
      (if p ∣ m then 1 else 1 - (p : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m := by
  split_ifs with hdvd
  · rw [one_mul, pmPowerDampedDivisorCoeff_mul_of_dvd_right ε hp.ne_zero hdvd]
  · exact pmPowerDampedDivisorCoeff_prime_mul_of_not_dvd ε hp hdvd

/-- **Dyadic Doubling Dichotomy for `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_two_mul`):**
For every `ε : ℝ` and `m : ℕ`:
`pmPowerDampedDivisorCoeff ε (2 * m) = (if 2 ∣ m then 1 else 1 - (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m`. -/
theorem pmPowerDampedDivisorCoeff_two_mul (ε : ℝ) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε (2 * m) =
      (if 2 ∣ m then 1 else 1 - (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m :=
  pmPowerDampedDivisorCoeff_prime_mul ε Nat.prime_two m

/-- **Dyadic Parent-Child Difference (`pmPowerDampedDivisorCoeff_sub_two_mul`):**
For every `ε : ℝ` and `m : ℕ`, `τ_ε(m) - τ_ε(2m)` vanishes when `2 ∣ m` and equals
`2^{-ε} * τ_ε(m)` when `2 ∤ m`. -/
theorem pmPowerDampedDivisorCoeff_sub_two_mul (ε : ℝ) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε m - pmPowerDampedDivisorCoeff ε (2 * m) =
      (if 2 ∣ m then 0 else (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m := by
  rw [pmPowerDampedDivisorCoeff_two_mul]
  split_ifs <;> ring

/-- **Dyadic Fermi Combination (`two_mul_pmPowerDampedDivisorCoeff_sub_two_mul`):**
For every `ε : ℝ` and `m : ℕ`:
`2 * pmPowerDampedDivisorCoeff ε m - pmPowerDampedDivisorCoeff ε (2 * m) = (if 2 ∣ m then 1 else 1 + (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m`. -/
theorem two_mul_pmPowerDampedDivisorCoeff_sub_two_mul (ε : ℝ) (m : ℕ) :
    2 * pmPowerDampedDivisorCoeff ε m - pmPowerDampedDivisorCoeff ε (2 * m) =
      (if 2 ∣ m then 1 else 1 + (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε m := by
  rw [pmPowerDampedDivisorCoeff_two_mul]
  split_ifs <;> ring

/-! ## §3. Sub-Horizon Fermi–Nyman Jump Dichotomy & Wall 11 Jump Contrast -/

/-- **Sub-Horizon Even-to-Odd Sibling Step for `pmPowerDampedRealWeight`
(`fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_sub_two_mul`):**
For every `ε : ℝ` and `2 * m + 1 ≤ N`:
`fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 1) - fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m) = -pmPowerDampedDivisorCoeff ε (2 * m + 1)`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_sub_two_mul
    (ε : ℝ) {N m : ℕ} (hmN : 2 * m + 1 ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 1) -
      fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m) =
      -pmPowerDampedDivisorCoeff ε (2 * m + 1) := by
  rw [fermiCellResponse_two_mul_add_one_sub_two_mul,
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega : 1 ≤ 2 * m + 1) hmN]

/-- **Sub-Horizon Odd-to-Even Boundary Step Dichotomy for `pmPowerDampedRealWeight`
(`fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul_add_one`):**
For every `ε : ℝ` and `2 * m + 2 ≤ N`, the odd-to-even cell jump at `2(m + 1)` is governed by
the parity of `m + 1`:
`fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 2) - fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 1) = (if 2 ∣ (m + 1) then 1 else 1 + (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε (m + 1)`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul_add_one
    (ε : ℝ) {N m : ℕ} (hmN : 2 * m + 2 ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 2) -
      fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 1) =
      (if 2 ∣ (m + 1) then 1 else 1 + (2 : ℝ) ^ (-ε)) *
        pmPowerDampedDivisorCoeff ε (m + 1) := by
  rw [fermiCellResponse_two_mul_add_two_sub_two_mul_add_one,
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega : 1 ≤ m + 1) (by omega),
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega : 1 ≤ 2 * m + 2) hmN,
    show 2 * m + 2 = 2 * (m + 1) by omega,
    two_mul_pmPowerDampedDivisorCoeff_sub_two_mul]

/-- **Sub-Horizon Two-Step Even-to-Even Jump Law for `pmPowerDampedRealWeight`
(`fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul`):**
For every `ε : ℝ` and `2 * m + 2 ≤ N`:
`fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 2) - fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m) = (if 2 ∣ (m + 1) then 1 else 1 + (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε (m + 1) - pmPowerDampedDivisorCoeff ε (2 * m + 1)`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul
    (ε : ℝ) {N m : ℕ} (hmN : 2 * m + 2 ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 2) -
      fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m) =
      (if 2 ∣ (m + 1) then 1 else 1 + (2 : ℝ) ^ (-ε)) *
        pmPowerDampedDivisorCoeff ε (m + 1) -
        pmPowerDampedDivisorCoeff ε (2 * m + 1) := by
  have h1 := fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_sub_two_mul ε (by omega : 2 * m + 1 ≤ N)
  have h2 := fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul_add_one ε hmN
  linarith

/-- **Wall 11 Sub-Horizon Odd-to-Even Jump Contrast (`4 = 2²` vs. `6 = 2 · 3`)
(`fermiCellResponse_pmPowerDampedRealWeight_jump_four_and_six`):**
For every `ε : ℝ` and `N ≥ 6`:
1. At the pure prime power `4 = 2²` (`m = 1`, `2 ∣ (m + 1)`, `log 4`), the odd-to-even cell jump is
   `1 - 2^{-ε}`.
2. At the composite pronic node `6 = 2 · 3` (`m = 2`, `2 ∤ (m + 1)`, `log 6`), radical absorption
   fails and the odd-to-even cell jump is amplified by `1 + 2^{-ε}` to
   `(1 + 2^{-ε}) * (1 - 3^{-ε})`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_jump_four_and_six
    (ε : ℝ) {N : ℕ} (hN : 6 ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) 4 -
      fermiCellResponse N (pmPowerDampedRealWeight ε) 3 =
      1 - (2 : ℝ) ^ (-ε) ∧
    fermiCellResponse N (pmPowerDampedRealWeight ε) 6 -
      fermiCellResponse N (pmPowerDampedRealWeight ε) 5 =
      (1 + (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε)) := by
  have hjump4 := fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul_add_one
    ε (m := 1) (by omega : 2 * 1 + 2 ≤ N)
  have hjump6 := fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_two_sub_two_mul_add_one
    ε (m := 2) (by omega : 2 * 2 + 2 ≤ N)
  simp only [show 2 * 1 + 2 = 4 by rfl, show 2 * 1 + 1 = 3 by rfl,
    show 1 + 1 = 2 by rfl, dvd_refl, ↓reduceIte, one_mul] at hjump4
  simp only [show 2 * 2 + 2 = 6 by rfl, show 2 * 2 + 1 = 5 by rfl,
    show 2 + 1 = 3 by rfl, show ¬ (2 ∣ 3) by decide, ↓reduceIte] at hjump6
  rw [pmPowerDampedDivisorCoeff_prime ε Nat.prime_two] at hjump4
  rw [pmPowerDampedDivisorCoeff_prime ε Nat.prime_three] at hjump6
  norm_num at hjump4 hjump6
  exact ⟨hjump4, hjump6⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
