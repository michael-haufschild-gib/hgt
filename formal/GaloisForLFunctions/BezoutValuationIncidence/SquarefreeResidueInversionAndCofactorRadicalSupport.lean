import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation
import GaloisForLFunctions.BezoutValuationIncidence.RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation
import GaloisForLFunctions.BiScaleUncertainty.RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge

/-!
# Squarefree Residue Inversion and Route PM Cofactor Radical Support

This module proves that the finite Ramanujan multiples inverse `pmRamanujanResidueCoeff` preserves
both multiple-vanishing (`k ∣ d`) and strict squarefree support (`Squarefree d`), and establishes
that the actual Route PM cofactor divisor weight
`d ↦ (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re` vanishes identically outside squarefree
integers.

## Main Results

1. **Multiples & Squarefree Support Preservation under `pmRamanujanResidueCoeff`**:
   - `pmRamanujanResidueCoeff_eq_zero_of_dvd_support`: if a Ramanujan profile `a : ℕ → ℝ` vanishes
     on all multiples of `k`, then `pmRamanujanResidueCoeff a Q d = 0` whenever `k ∣ d`.
   - `pmRamanujanResidueCoeff_eq_zero_of_not_squarefree`: if `a` is supported on squarefree
     integers (`∀ q, ¬ Squarefree q → a q = 0`), then `pmRamanujanResidueCoeff a Q d = 0` whenever
     `¬ Squarefree d`.
   - `eq_moebiusReal_mul_self_of_squarefree_support`: every squarefree-supported divisor weight
     `c : ℕ → ℝ` admits the canonical Möbius-twist factorization
     `c d = moebiusReal d * (moebiusReal d * c d)`.

2. **Strict Squarefree Support of `pmPowerDampedRamanujanCofactor` & Its Real Divisor Weight**:
   - `pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree` and
     `re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree`: for every `ε : ℝ`, cutoff
     `N : ℕ`, and non-squarefree `d : ℕ`, `pmPowerDampedRamanujanCofactor ε N d = 0` and
     `(pmPowerDampedRamanujanCofactor ε N d).re = 0`.
   - `re_pmPowerDampedRamanujanCofactor_eq_zero_of_four_dvd` and
     `re_pmPowerDampedRamanujanCofactor_four_mul_eq_zero`: in particular, the real cofactor weight
     vanishes whenever `4 ∣ d`.
   - `re_pmPowerDampedRamanujanCofactor_eq_moebiusReal_mul`: the real cofactor weight lies in the
     canonical Möbius-twisted class `d ↦ moebiusReal d * w d`.

3. **All-Horizon Radical, Divisor-Multiplication, & Power Invariance of the Cofactor Sieve**:
   - `sieveSeq_pmRamanujanResidueCoeff_mul_of_dvd`,
     `sieveSeq_pmRamanujanResidueCoeff_pow`,
     `sieveSeq_re_pmPowerDampedRamanujanCofactor_mul_of_dvd`,
     `sieveSeq_re_pmPowerDampedRamanujanCofactor_pow`,
     `sieveSeq_re_pmPowerDampedRamanujanCofactor_prime_pow_mul`, and
     `sieveSeq_re_pmPowerDampedRamanujanCofactor_eq_of_primeFactors_eq`: at every observation
     horizon `N : ℕ` and cofactor cutoff `Q : ℕ`, the cofactor sieve sequence depends on `k` only
     through its squarefree prime support.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## §1. Multiples & Squarefree Support Preservation under `pmRamanujanResidueCoeff` -/

/-- **Multiples Support Preservation (`pmRamanujanResidueCoeff_eq_zero_of_dvd_support`):**
If `a : ℕ → ℝ` vanishes on all multiples of `k` (`∀ q, k ∣ q → a q = 0`), then for every cutoff
`Q : ℕ` and divisor `d : ℕ` with `k ∣ d`, `pmRamanujanResidueCoeff a Q d = 0`. -/
theorem pmRamanujanResidueCoeff_eq_zero_of_dvd_support {a : ℕ → ℝ} {k : ℕ}
    (ha : ∀ q : ℕ, k ∣ q → a q = 0) (Q : ℕ) {d : ℕ} (hkd : k ∣ d) :
    pmRamanujanResidueCoeff a Q d = 0 := by
  unfold pmRamanujanResidueCoeff
  rw [Finset.sum_eq_zero, mul_zero]
  intro m _
  rw [ha (d * m) (dvd_mul_of_dvd_left hkd m), mul_zero]

/-- **Squarefree Support Preservation (`pmRamanujanResidueCoeff_eq_zero_of_not_squarefree`):**
If `a : ℕ → ℝ` vanishes outside squarefree numbers (`∀ q, ¬ Squarefree q → a q = 0`), then for
every cutoff `Q : ℕ` and non-squarefree `d : ℕ` (`¬ Squarefree d`),
`pmRamanujanResidueCoeff a Q d = 0`. -/
theorem pmRamanujanResidueCoeff_eq_zero_of_not_squarefree {a : ℕ → ℝ}
    (ha : ∀ q : ℕ, ¬ Squarefree q → a q = 0) (Q : ℕ) {d : ℕ} (hd : ¬ Squarefree d) :
    pmRamanujanResidueCoeff a Q d = 0 := by
  unfold pmRamanujanResidueCoeff
  rw [Finset.sum_eq_zero, mul_zero]
  intro m _
  have hdm : ¬ Squarefree (d * m) := fun hs => hd hs.of_mul_left
  rw [ha (d * m) hdm, mul_zero]

/-- For every squarefree integer `d`, `moebiusReal d * moebiusReal d = 1`. -/
theorem moebiusReal_mul_self_of_squarefree {d : ℕ} (hd : Squarefree d) :
    moebiusReal d * moebiusReal d = 1 := by
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd]
  push_cast
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- **Canonical Möbius-Twist Factorization of Squarefree-Supported Weights
(`eq_moebiusReal_mul_self_of_squarefree_support`):**
Every divisor weight `c : ℕ → ℝ` vanishing outside squarefree integers satisfies
`c d = moebiusReal d * (moebiusReal d * c d)` for all `d : ℕ`. -/
theorem eq_moebiusReal_mul_self_of_squarefree_support {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) (d : ℕ) :
    c d = moebiusReal d * (moebiusReal d * c d) := by
  by_cases hd : Squarefree d
  · rw [← mul_assoc, moebiusReal_mul_self_of_squarefree hd, one_mul]
  · rw [hc d hd, mul_zero, mul_zero]

/-- For any squarefree-supported profile `a : ℕ → ℝ`, `pmRamanujanResidueCoeff a Q` is canonically
a Möbius-twisted weight. -/
theorem pmRamanujanResidueCoeff_eq_moebiusReal_mul {a : ℕ → ℝ}
    (ha : ∀ q : ℕ, ¬ Squarefree q → a q = 0) (Q d : ℕ) :
    pmRamanujanResidueCoeff a Q d =
      moebiusReal d * (moebiusReal d * pmRamanujanResidueCoeff a Q d) :=
  eq_moebiusReal_mul_self_of_squarefree_support
    (fun _ hs => pmRamanujanResidueCoeff_eq_zero_of_not_squarefree ha Q hs) d

/-! ## §2. Strict Squarefree Support of `pmPowerDampedRamanujanCofactor` & Its Real Weight -/

/-- The real part of `pmPowerDampedRamanujanWeight ε q` vanishes whenever `¬ Squarefree q`. -/
theorem re_pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree (ε : ℝ) {q : ℕ}
    (hq : ¬ Squarefree q) :
    (pmPowerDampedRamanujanWeight ε q).re = 0 := by
  rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hq, Complex.zero_re]

/-- **Strict Squarefree Support of `pmPowerDampedRamanujanCofactor`
(`pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree`):**
For every `ε : ℝ`, `N : ℕ`, and non-squarefree `d : ℕ`,
`pmPowerDampedRamanujanCofactor ε N d = 0`. -/
theorem pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree (ε : ℝ) (N : ℕ) {d : ℕ}
    (hd : ¬ Squarefree d) :
    pmPowerDampedRamanujanCofactor ε N d = 0 := by
  unfold pmPowerDampedRamanujanCofactor
  rw [Finset.sum_eq_zero, mul_zero]
  intro m _
  have hdm : ¬ Squarefree (d * m) := fun hs => hd hs.of_mul_left
  rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hdm, mul_zero]

/-- **Strict Squarefree Support of the Real Cofactor Weight
(`re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree`):**
For every `ε : ℝ`, cutoff `N : ℕ`, and non-squarefree `d : ℕ` (`¬ Squarefree d`),
`(pmPowerDampedRamanujanCofactor ε N d).re = 0`. -/
theorem re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree (ε : ℝ) (N : ℕ) {d : ℕ}
    (hd : ¬ Squarefree d) :
    (pmPowerDampedRamanujanCofactor ε N d).re = 0 := by
  rw [pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree ε N hd, Complex.zero_re]

/-- For any prime `p`, if `p ^ 2 ∣ d`, then `¬ Squarefree d`. -/
theorem not_squarefree_of_prime_sq_dvd {p d : ℕ} (hp : Nat.Prime p) (hdvd : p ^ 2 ∣ d) :
    ¬ Squarefree d := by
  intro hsq
  have hp2 : p * p ∣ d := by simpa [sq] using hdvd
  exact hp.not_isUnit (hsq p hp2)

/-- **Prime-Square Annihilation of the Real Cofactor Weight
(`re_pmPowerDampedRamanujanCofactor_eq_zero_of_prime_sq_dvd`):**
For every prime `p` and every `d : ℕ` divisible by `p ^ 2`,
`(pmPowerDampedRamanujanCofactor ε N d).re = 0`. -/
theorem re_pmPowerDampedRamanujanCofactor_eq_zero_of_prime_sq_dvd (ε : ℝ) (N : ℕ) {p d : ℕ}
    (hp : Nat.Prime p) (hdvd : p ^ 2 ∣ d) :
    (pmPowerDampedRamanujanCofactor ε N d).re = 0 :=
  re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree ε N
    (not_squarefree_of_prime_sq_dvd hp hdvd)

/-- **Four-Divisible Annihilation of the Real Cofactor Weight
(`re_pmPowerDampedRamanujanCofactor_eq_zero_of_four_dvd`):**
For every `ε : ℝ`, `N : ℕ`, and `d : ℕ` with `4 ∣ d`,
`(pmPowerDampedRamanujanCofactor ε N d).re = 0`. -/
theorem re_pmPowerDampedRamanujanCofactor_eq_zero_of_four_dvd (ε : ℝ) (N : ℕ) {d : ℕ}
    (h4 : 4 ∣ d) :
    (pmPowerDampedRamanujanCofactor ε N d).re = 0 :=
  re_pmPowerDampedRamanujanCofactor_eq_zero_of_prime_sq_dvd ε N Nat.prime_two (by simpa using h4)

/-- For every `ε : ℝ` and `N, m : ℕ`, `(pmPowerDampedRamanujanCofactor ε N (4 * m)).re = 0`. -/
@[simp]
theorem re_pmPowerDampedRamanujanCofactor_four_mul_eq_zero (ε : ℝ) (N m : ℕ) :
    (pmPowerDampedRamanujanCofactor ε N (4 * m)).re = 0 :=
  re_pmPowerDampedRamanujanCofactor_eq_zero_of_four_dvd ε N (dvd_mul_right 4 m)

/-- **Canonical Möbius-Twist Factorization of the Real Cofactor Weight
(`re_pmPowerDampedRamanujanCofactor_eq_moebiusReal_mul`):**
For every `ε : ℝ` and `N, d : ℕ`:
`(pmPowerDampedRamanujanCofactor ε N d).re = moebiusReal d * (moebiusReal d * (pmPowerDampedRamanujanCofactor ε N d).re)`. -/
theorem re_pmPowerDampedRamanujanCofactor_eq_moebiusReal_mul (ε : ℝ) (N d : ℕ) :
    (pmPowerDampedRamanujanCofactor ε N d).re =
      moebiusReal d * (moebiusReal d * (pmPowerDampedRamanujanCofactor ε N d).re) :=
  eq_moebiusReal_mul_self_of_squarefree_support
    (fun _ hs => re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree ε N hs) d

/-! ## §3. All-Horizon Radical & Power Invariance of the Cofactor Sieve Sequence -/

/-- Helper: if `s` is squarefree and `s ∣ k * k`, then `s ∣ k`. -/
private theorem dvd_of_dvd_mul_self_of_squarefree' {s k : ℕ} (hs : Squarefree s)
    (hdvd : s ∣ k * k) : s ∣ k := by
  by_cases hk0 : k = 0
  · subst hk0; exact dvd_zero s
  · have hs_pos : 0 < s := hs.ne_zero.bot_lt
    let g := Nat.gcd s k
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k hs_pos
    have hgd_s : g ∣ s := Nat.gcd_dvd_left s k
    have hgd_k : g ∣ k := Nat.gcd_dvd_right s k
    have hs_eq : g * (s / g) = s := Nat.mul_div_cancel' hgd_s
    have hk_eq : g * (k / g) = k := Nat.mul_div_cancel' hgd_k
    have hsq_mul : Squarefree (g * (s / g)) := by rw [hs_eq]; exact hs
    have hcop_g : Nat.Coprime (s / g) g := (Nat.coprime_of_squarefree_mul hsq_mul).symm
    have hcop_kg : Nat.Coprime (s / g) (k / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    have hcop_k : Nat.Coprime (s / g) k := by rw [← hk_eq]; exact hcop_g.mul_right hcop_kg
    have hcop_kk : Nat.Coprime (s / g) (k * k) := hcop_k.mul_right hcop_k
    have hdiv_kk : (s / g) ∣ k * k := (Nat.div_dvd_of_dvd hgd_s).trans hdvd
    have hsg_one : s / g = 1 := Nat.eq_one_of_dvd_coprimes hcop_kk (dvd_refl _) hdiv_kk
    rw [← hs_eq, hsg_one, mul_one]
    exact hgd_k

/-- Helper: for squarefree `s` and `d ∣ k`, `s ∣ d * k ↔ s ∣ k`. -/
private theorem dvd_of_dvd_mul_of_dvd_of_squarefree' {s d k : ℕ} (hs : Squarefree s)
    (hdk : d ∣ k) : s ∣ d * k ↔ s ∣ k :=
  ⟨fun hsd => dvd_of_dvd_mul_self_of_squarefree' hs (hsd.trans (Nat.mul_dvd_mul_right hdk k)),
   fun hsk => dvd_mul_of_dvd_right hsk d⟩

/-- **All-Horizon Divisor-Multiplication Absorption for Squarefree `pmRamanujanResidueCoeff`
(`sieveSeq_pmRamanujanResidueCoeff_mul_of_dvd`):**
If `a : ℕ → ℝ` vanishes outside squarefree numbers, then for every horizon `N`, cutoff `Q`, and
`d ∣ k`:
`sieveSeq N (pmRamanujanResidueCoeff a Q) (d * k) = sieveSeq N (pmRamanujanResidueCoeff a Q) k`. -/
theorem sieveSeq_pmRamanujanResidueCoeff_mul_of_dvd {a : ℕ → ℝ}
    (ha : ∀ q : ℕ, ¬ Squarefree q → a q = 0) (N Q : ℕ) {d k : ℕ} (hdk : d ∣ k) :
    sieveSeq N (pmRamanujanResidueCoeff a Q) (d * k) =
      sieveSeq N (pmRamanujanResidueCoeff a Q) k := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hsq : Squarefree s
  · simp only [dvd_of_dvd_mul_of_dvd_of_squarefree' hsq hdk]
  · rw [pmRamanujanResidueCoeff_eq_zero_of_not_squarefree ha Q hsq]
    split_ifs <;> rfl

/-- **All-Horizon Power Invariance for Squarefree `pmRamanujanResidueCoeff`
(`sieveSeq_pmRamanujanResidueCoeff_pow`):**
If `a : ℕ → ℝ` vanishes outside squarefree numbers, then for every `N, Q, k : ℕ` and `m ≥ 1`:
`sieveSeq N (pmRamanujanResidueCoeff a Q) (k ^ m) = sieveSeq N (pmRamanujanResidueCoeff a Q) k`. -/
theorem sieveSeq_pmRamanujanResidueCoeff_pow {a : ℕ → ℝ}
    (ha : ∀ q : ℕ, ¬ Squarefree q → a q = 0) (N Q k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    sieveSeq N (pmRamanujanResidueCoeff a Q) (k ^ m) =
      sieveSeq N (pmRamanujanResidueCoeff a Q) k := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp
    · rw [pow_succ, mul_comm,
        sieveSeq_pmRamanujanResidueCoeff_mul_of_dvd ha N Q (dvd_pow_self k (by omega)),
        ih (by omega)]

/-- **All-Horizon Divisor-Multiplication Absorption for the Real Cofactor Weight
(`sieveSeq_re_pmPowerDampedRamanujanCofactor_mul_of_dvd`):**
For every `ε : ℝ`, horizon `N : ℕ`, cofactor cutoff `Q : ℕ`, and `d, k : ℕ` with `d ∣ k`:
`sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (d * k) = sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) k`. -/
theorem sieveSeq_re_pmPowerDampedRamanujanCofactor_mul_of_dvd (ε : ℝ) (N Q : ℕ) {d k : ℕ}
    (hdk : d ∣ k) :
    sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (d * k) =
      sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) k := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hsq : Squarefree s
  · simp only [dvd_of_dvd_mul_of_dvd_of_squarefree' hsq hdk]
  · rw [re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree ε Q hsq]
    split_ifs <;> rfl

/-- **All-Horizon Power Invariance for the Real Cofactor Weight
(`sieveSeq_re_pmPowerDampedRamanujanCofactor_pow`):**
For every `ε : ℝ`, horizon `N : ℕ`, cutoff `Q : ℕ`, `k : ℕ`, and exponent `m ≥ 1`:
`sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (k ^ m) = sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) k`. -/
theorem sieveSeq_re_pmPowerDampedRamanujanCofactor_pow (ε : ℝ) (N Q k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (k ^ m) =
      sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) k := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp
    · rw [pow_succ, mul_comm,
        sieveSeq_re_pmPowerDampedRamanujanCofactor_mul_of_dvd ε N Q (dvd_pow_self k (by omega)),
        ih (by omega)]

/-- **All-Horizon Prime-Power Chain Constancy for the Real Cofactor Weight
(`sieveSeq_re_pmPowerDampedRamanujanCofactor_prime_pow_mul`):**
For every `ε : ℝ`, `N, Q, p, u, a : ℕ`:
`sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (p ^ (a + 1) * u) = sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (p * u)`. -/
theorem sieveSeq_re_pmPowerDampedRamanujanCofactor_prime_pow_mul (ε : ℝ) (N Q p u a : ℕ) :
    sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (p ^ (a + 1) * u) =
      sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) (p * u) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hrew : p ^ (a + 1 + 1) * u = p * (p ^ (a + 1) * u) := by rw [pow_succ', mul_assoc]
    have hdvd : p ∣ p ^ (a + 1) * u :=
      dvd_mul_of_dvd_left (dvd_pow_self p (by omega : a + 1 ≠ 0)) u
    rw [hrew, sieveSeq_re_pmPowerDampedRamanujanCofactor_mul_of_dvd ε N Q hdvd, ih]

/-- Helper: if `s` is squarefree and every prime dividing `s` divides `l`, then `s ∣ l`. -/
private theorem dvd_of_squarefree_of_prime_dvd {s l : ℕ} (hs : Squarefree s)
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ s → p ∣ l) : s ∣ l := by
  induction s using induction_on_primes with
  | zero => exact (hs.ne_zero rfl).elim
  | one => exact one_dvd l
  | prime_mul p q hp ih =>
    have hsq_q : Squarefree q := hs.of_mul_right
    have hpq : ¬ p ∣ q := fun hdvd => hp.not_isUnit (hs p (mul_dvd_mul_left p hdvd))
    have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hpq
    exact hcop.mul_dvd_of_dvd_of_dvd (h p hp (dvd_mul_right p q))
      (ih hsq_q fun r hr hrq => h r hr (dvd_mul_of_dvd_right hrq p))

/-- **All-Horizon Radical Invariance for the Real Cofactor Weight
(`sieveSeq_re_pmPowerDampedRamanujanCofactor_eq_of_primeFactors_eq`):**
If `k, l ≠ 0` have the same prime factors (`k.primeFactors = l.primeFactors`), then for every
`ε : ℝ` and `N, Q : ℕ`:
`sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) k = sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) l`. -/
theorem sieveSeq_re_pmPowerDampedRamanujanCofactor_eq_of_primeFactors_eq (ε : ℝ) (N Q : ℕ)
    {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (hpf : k.primeFactors = l.primeFactors) :
    sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) k =
      sieveSeq N (fun s => (pmPowerDampedRamanujanCofactor ε Q s).re) l := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hsq : Squarefree s
  · have hdvd : s ∣ k ↔ s ∣ l := by
      constructor
      · intro hsk
        refine dvd_of_squarefree_of_prime_dvd hsq fun p hp hps => ?_
        have hpmem : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps.trans hsk, hk⟩
        rw [hpf] at hpmem
        exact (Nat.mem_primeFactors.mp hpmem).2.1
      · intro hsl
        refine dvd_of_squarefree_of_prime_dvd hsq fun p hp hps => ?_
        have hpmem : p ∈ l.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps.trans hsl, hl⟩
        rw [← hpf] at hpmem
        exact (Nat.mem_primeFactors.mp hpmem).2.1
    simp only [hdvd]
  · rw [re_pmPowerDampedRamanujanCofactor_eq_zero_of_not_squarefree ε Q hsq]
    split_ifs <;> rfl

end GaloisForLFunctions.BezoutValuationIncidence
