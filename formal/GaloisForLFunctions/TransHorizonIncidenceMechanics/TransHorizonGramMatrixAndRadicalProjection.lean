import GaloisForLFunctions.BezoutValuationIncidence.RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling

/-!
# Pillar IX: Buchstab `L²` Gram Band Decomposition & Universal Trans-Horizon Radical Invariance (`TransHorizonGramMatrixAndRadicalProjection`)

In `BezoutValuationIncidence` (`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation`),
radical invariance and divisor-multiplication absorption
$$\tau_\varepsilon(d \cdot k) = \tau_\varepsilon(k) \quad (d \mid k), \qquad
  \tau_\varepsilon(k^m) = \tau_\varepsilon(k) \quad (m \ge 1)$$
were proved only for the **untruncated** Dirichlet convolution `pmPowerDampedDivisorCoeff ε`
(which coincides with `sieveSeq N (pmPowerDampedRealWeight ε)` only below the horizon `k ≤ N`).

In this ninth foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**,
we discover that because the horizon cutoff `s ≤ N` restricts the **divisor `s`** rather than the
target integer `k`, and because every squarefree divisor `s` of `d * k` (`d ∣ k`) already divides
`k`, **the truncated sieve `sieveSeq N c` itself is 100% radical-invariant and power-invariant at
every horizon `N` and across all trans-horizon scales `k ≫ N`** for every squarefree-supported
weight `c : ℕ → ℝ` (including `moebiusReal`, `pmPowerDampedRealWeight ε`, and any logarithmic or
Dirichlet twist of `μ`). We simultaneously establish the **Buchstab `L²` Gram Energy Band
Decomposition** across horizon bands `N₁ ≤ N₂`:

## Core Main Theorems (100% Unconditional)

1. **Squarefree Divisor Collapse Under Divisor Multiplication (`dvd_of_dvd_mul_of_dvd_of_squarefree`,
   `sieveSeq_mul_of_dvd_of_squarefree_support`, `sieveSeq_sq_of_squarefree_support`,
   `sieveSeq_pow_of_squarefree_support`)**:
   - For any squarefree integer `s` and any `d, k : ℕ` with `d ∣ k`, `s ∣ d * k ↔ s ∣ k`.
   - Consequently, for **every** cutoff `N : ℕ` (with **no** sub-horizon restriction on `k`), every
     weight `c : ℕ → ℝ` supported on squarefree numbers (`∀ s, ¬ Squarefree s → c s = 0`), every
     `d, k : ℕ` with `d ∣ k`, and every exponent `m ≥ 1`:
     $$\operatorname{sieveSeq}(N, c, d \cdot k) = \operatorname{sieveSeq}(N, c, k),$$
     $$\operatorname{sieveSeq}(N, c, k^2) = \operatorname{sieveSeq}(N, c, k), \qquad
       \operatorname{sieveSeq}(N, c, k^m) = \operatorname{sieveSeq}(N, c, k).$$

2. **All-Horizon Radical & Power Invariance for `moebiusReal` and `pmPowerDampedRealWeight ε`
   (`sieveSeq_moebiusReal_mul_of_dvd`, `sieveSeq_moebiusReal_pow`,
   `sieveSeq_pmPowerDampedRealWeight_mul_of_dvd`, `sieveSeq_pmPowerDampedRealWeight_pow`)**:
   For **every** horizon `N : ℕ`, `k : ℕ`, `d ∣ k`, `m ≥ 1`, and `ε : ℝ`:
   $$\operatorname{sieveSeq}(N, \mu, d \cdot k) = \operatorname{sieveSeq}(N, \mu, k), \qquad
     \operatorname{sieveSeq}(N, \mu, k^m) = \operatorname{sieveSeq}(N, \mu, k),$$
   $$\operatorname{sieveSeq}(N, c_\varepsilon, d \cdot k) = \operatorname{sieveSeq}(N, c_\varepsilon, k), \qquad
     \operatorname{sieveSeq}(N, c_\varepsilon, k^m) = \operatorname{sieveSeq}(N, c_\varepsilon, k).$$
   In particular, along every `p`-adic prime-power chain `p^(a+1) * u` (`a ≥ 0`), the truncated
   sieve is **strictly constant for all `a ≥ 0`** (`sieveSeq N c (p^(a+1) * u) = sieveSeq N c (p * u)`)
   even when `p^(a+1) * u ≫ N`!

3. **Buchstab `L²` Gram Energy Band Decomposition (`sieveBandSeq`, `sieveL2PrefixEnergy`,
   `sieveL2PrefixEnergy_horizon_band_sub`, `sieveL2PrefixEnergy_ge_add_band_of_cov_nonneg`)**:
   Across any horizon band `N₁ ≤ N₂` and prefix window `M : ℕ`:
   $$\mathcal{E}_{N_2}(M; c) - \mathcal{E}_{N_1}(M; c) =
     \sum_{k=1}^M \bigl(\Delta_{N_1, N_2}s_c(k)\bigr)^2 +
       2 \sum_{k=1}^M s_{N_1, c}(k)\,\Delta_{N_1, N_2}s_c(k).$$
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Squarefree Divisor Collapse & Universal Trans-Horizon Radical Invariance -/

/-- **Fundamental Squarefree Self-Square Divisibility Lemma (`dvd_of_dvd_mul_self_of_squarefree`):**
If `s` is squarefree and `s ∣ k * k`, then `s ∣ k`. -/
theorem dvd_of_dvd_mul_self_of_squarefree {s k : ℕ} (hs : Squarefree s) (hdvd : s ∣ k * k) :
    s ∣ k := by
  by_cases hk0 : k = 0
  · subst hk0
    exact dvd_zero s
  · have hs_pos : 0 < s := hs.ne_zero.bot_lt
    let g := Nat.gcd s k
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k hs_pos
    have hgd_s : g ∣ s := Nat.gcd_dvd_left s k
    have hgd_k : g ∣ k := Nat.gcd_dvd_right s k
    have hs_eq : g * (s / g) = s := Nat.mul_div_cancel' hgd_s
    have hk_eq : g * (k / g) = k := Nat.mul_div_cancel' hgd_k
    have hsq_mul : Squarefree (g * (s / g)) := by rw [hs_eq]; exact hs
    have hcop_g : Nat.Coprime (s / g) g := (Nat.coprime_of_squarefree_mul hsq_mul).symm
    have hcop_kg : Nat.Coprime (s / g) (k / g) :=
      Nat.coprime_div_gcd_div_gcd hg_pos
    have hcop_k : Nat.Coprime (s / g) k := by
      rw [← hk_eq]
      exact hcop_g.mul_right hcop_kg
    have hcop_kk : Nat.Coprime (s / g) (k * k) := hcop_k.mul_right hcop_k
    have hdiv_s : (s / g) ∣ s := Nat.div_dvd_of_dvd hgd_s
    have hdiv_kk : (s / g) ∣ k * k := hdiv_s.trans hdvd
    have hsg_one : s / g = 1 := Nat.eq_one_of_dvd_coprimes hcop_kk (dvd_refl (s / g)) hdiv_kk
    rw [← hs_eq, hsg_one, mul_one]
    exact hgd_k

/-- **Squarefree Divisor Collapse Under Divisor Multiplication
(`dvd_of_dvd_mul_of_dvd_of_squarefree`):**
For any squarefree integer `s` and any `d, k : ℕ` with `d ∣ k`, `s ∣ d * k ↔ s ∣ k`. -/
theorem dvd_of_dvd_mul_of_dvd_of_squarefree {s d k : ℕ} (hs : Squarefree s) (hdk : d ∣ k) :
    s ∣ d * k ↔ s ∣ k := by
  constructor
  · intro hsd
    have hskk : s ∣ k * k := hsd.trans (Nat.mul_dvd_mul_right hdk k)
    exact dvd_of_dvd_mul_self_of_squarefree hs hskk
  · intro hsk
    exact dvd_mul_of_dvd_right hsk d

/-- **Universal All-Horizon Divisor-Multiplication Absorption for Squarefree-Supported Weights
(`sieveSeq_mul_of_dvd_of_squarefree_support`):**
For **every** cutoff `N : ℕ`, weight `c : ℕ → ℝ` vanishing outside squarefree integers
(`∀ s, ¬ Squarefree s → c s = 0`), and `d, k : ℕ` with `d ∣ k`:
`sieveSeq N c (d * k) = sieveSeq N c k`. -/
theorem sieveSeq_mul_of_dvd_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {d k : ℕ} (hdk : d ∣ k) :
    sieveSeq N c (d * k) = sieveSeq N c k := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hsq : Squarefree s
  · simp only [dvd_of_dvd_mul_of_dvd_of_squarefree hsq hdk]
  · rw [hc s hsq]
    split_ifs <;> rfl

/-- Right-multiplication form of `sieveSeq_mul_of_dvd_of_squarefree_support`: if `d ∣ k`, then
`sieveSeq N c (k * d) = sieveSeq N c k`. -/
theorem sieveSeq_mul_right_of_dvd_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {d k : ℕ} (hdk : d ∣ k) :
    sieveSeq N c (k * d) = sieveSeq N c k := by
  rw [mul_comm, sieveSeq_mul_of_dvd_of_squarefree_support N hc hdk]

/-- **Universal All-Horizon Square Invariance for Squarefree-Supported Weights
(`sieveSeq_sq_of_squarefree_support`):**
For every `N : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, and `k : ℕ`:
`sieveSeq N c (k ^ 2) = sieveSeq N c k`. -/
theorem sieveSeq_sq_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (k : ℕ) :
    sieveSeq N c (k ^ (2 : ℕ)) = sieveSeq N c k := by
  rw [sq]
  exact sieveSeq_mul_of_dvd_of_squarefree_support N hc (dvd_refl k)

/-- **Universal All-Horizon Power Invariance for Squarefree-Supported Weights
(`sieveSeq_pow_of_squarefree_support`):**
For every `N : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, `k : ℕ`, and `m ≥ 1`:
`sieveSeq N c (k ^ m) = sieveSeq N c k`. -/
theorem sieveSeq_pow_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    sieveSeq N c (k ^ m) = sieveSeq N c k := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp
    · rw [pow_succ, sieveSeq_mul_right_of_dvd_of_squarefree_support N hc (dvd_pow_self k (by omega)),
        ih (by omega)]

/-- **Universal Trans-Horizon Prime-Power Chain Constancy for Squarefree-Supported Weights
(`sieveSeq_prime_pow_mul_eq_prime_mul_of_squarefree_support`):**
For every `N : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, `p, u : ℕ`, and `a : ℕ`:
`sieveSeq N c (p ^ (a + 1) * u) = sieveSeq N c (p * u)`. -/
theorem sieveSeq_prime_pow_mul_eq_prime_mul_of_squarefree_support (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (p u a : ℕ) :
    sieveSeq N c (p ^ (a + 1) * u) = sieveSeq N c (p * u) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hrew : p ^ (a + 1 + 1) * u = p * (p ^ (a + 1) * u) := by
      rw [pow_succ', mul_assoc]
    have hdvd : p ∣ p ^ (a + 1) * u :=
      dvd_mul_of_dvd_left (dvd_pow_self p (by omega : a + 1 ≠ 0)) u
    rw [hrew, sieveSeq_mul_of_dvd_of_squarefree_support N hc hdvd, ih]

/-! ## §2. All-Horizon Radical & Power Invariance for `moebiusReal` and `pmPowerDampedRealWeight ε` -/

/-- `moebiusReal` vanishes outside squarefree numbers. -/
theorem moebiusReal_eq_zero_of_not_squarefree (s : ℕ) (hs : ¬ Squarefree s) :
    moebiusReal s = 0 := by
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  simp

/-- `pmPowerDampedRealWeight ε` vanishes outside squarefree numbers. -/
theorem pmPowerDampedRealWeight_eq_zero_of_not_squarefree (ε : ℝ) (s : ℕ) (hs : ¬ Squarefree s) :
    pmPowerDampedRealWeight ε s = 0 := by
  unfold pmPowerDampedRealWeight
  rw [moebiusReal_eq_zero_of_not_squarefree s hs, zero_mul]

/-- **All-Horizon Divisor-Multiplication & Power Invariance for `moebiusReal`
(`sieveSeq_moebiusReal_mul_of_dvd`, `sieveSeq_moebiusReal_pow`):**
For every horizon `N : ℕ`, `k : ℕ`, `d ∣ k`, and `m ≥ 1`:
`sieveSeq N moebiusReal (d * k) = sieveSeq N moebiusReal k` and
`sieveSeq N moebiusReal (k ^ m) = sieveSeq N moebiusReal k`. -/
theorem sieveSeq_moebiusReal_mul_of_dvd (N : ℕ) {d k : ℕ} (hdk : d ∣ k) :
    sieveSeq N moebiusReal (d * k) = sieveSeq N moebiusReal k :=
  sieveSeq_mul_of_dvd_of_squarefree_support N moebiusReal_eq_zero_of_not_squarefree hdk

theorem sieveSeq_moebiusReal_pow (N k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    sieveSeq N moebiusReal (k ^ m) = sieveSeq N moebiusReal k :=
  sieveSeq_pow_of_squarefree_support N moebiusReal_eq_zero_of_not_squarefree k hm

/-- **All-Horizon Divisor-Multiplication & Power Invariance for `pmPowerDampedRealWeight ε`
(`sieveSeq_pmPowerDampedRealWeight_mul_of_dvd`, `sieveSeq_pmPowerDampedRealWeight_pow`):**
For every `ε : ℝ`, horizon `N : ℕ`, `k : ℕ`, `d ∣ k`, and `m ≥ 1`:
`sieveSeq N (pmPowerDampedRealWeight ε) (d * k) = sieveSeq N (pmPowerDampedRealWeight ε) k` and
`sieveSeq N (pmPowerDampedRealWeight ε) (k ^ m) = sieveSeq N (pmPowerDampedRealWeight ε) k`. -/
theorem sieveSeq_pmPowerDampedRealWeight_mul_of_dvd (ε : ℝ) (N : ℕ) {d k : ℕ} (hdk : d ∣ k) :
    sieveSeq N (pmPowerDampedRealWeight ε) (d * k) =
      sieveSeq N (pmPowerDampedRealWeight ε) k :=
  sieveSeq_mul_of_dvd_of_squarefree_support N
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε) hdk

theorem sieveSeq_pmPowerDampedRealWeight_pow (ε : ℝ) (N k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    sieveSeq N (pmPowerDampedRealWeight ε) (k ^ m) =
      sieveSeq N (pmPowerDampedRealWeight ε) k :=
  sieveSeq_pow_of_squarefree_support N
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε) k hm

/-! ## §3. Buchstab `L²` Gram Energy Band Decomposition -/

/-- **Buchstab Horizon-Band Sieve Operator (`sieveBandSeq`):**
The difference `sieveSeq N₂ c k - sieveSeq N₁ c k` across the horizon band `(N₁, N₂]`. -/
def sieveBandSeq (N₁ N₂ : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  sieveSeq N₂ c k - sieveSeq N₁ c k

/-- **Prefix `L²` Gram Energy of `sieveSeq` (`sieveL2PrefixEnergy`):**
`sieveL2PrefixEnergy N M c = ∑ k ∈ Finset.Icc 1 M, sieveSeq N c k ^ 2`. -/
def sieveL2PrefixEnergy (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 M, sieveSeq N c k ^ (2 : ℕ)

/-- **Buchstab `L²` Gram Energy Band Decomposition (`sieveL2PrefixEnergy_horizon_band_sub`):**
For every `N₁, N₂, M : ℕ` and weight `c : ℕ → ℝ`:
`sieveL2PrefixEnergy N₂ M c - sieveL2PrefixEnergy N₁ M c` equals the non-negative band self-energy
plus twice the cross-band inner product. -/
theorem sieveL2PrefixEnergy_horizon_band_sub (N₁ N₂ M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy N₂ M c - sieveL2PrefixEnergy N₁ M c =
      (∑ k ∈ Finset.Icc 1 M, sieveBandSeq N₁ N₂ c k ^ (2 : ℕ)) +
        2 * ∑ k ∈ Finset.Icc 1 M, sieveSeq N₁ c k * sieveBandSeq N₁ N₂ c k := by
  unfold sieveL2PrefixEnergy sieveBandSeq
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **Pythagorean Horizon Energy Monotonicity Under Non-Negative Cross-Band Covariance
(`sieveL2PrefixEnergy_ge_add_band_of_cov_nonneg`):**
Whenever the cross-band inner product `∑_{k=1}^M s_{N₁,c}(k) Δ_{N₁,N₂}s_c(k)` is non-negative,
`sieveL2PrefixEnergy N₂ M c ≥ sieveL2PrefixEnergy N₁ M c + ∑_{k=1}^M Δ_{N₁,N₂}s_c(k)² ≥ sieveL2PrefixEnergy N₁ M c`. -/
theorem sieveL2PrefixEnergy_ge_add_band_of_cov_nonneg (N₁ N₂ M : ℕ) (c : ℕ → ℝ)
    (hcov : 0 ≤ ∑ k ∈ Finset.Icc 1 M, sieveSeq N₁ c k * sieveBandSeq N₁ N₂ c k) :
    sieveL2PrefixEnergy N₁ M c +
        (∑ k ∈ Finset.Icc 1 M, sieveBandSeq N₁ N₂ c k ^ (2 : ℕ)) ≤
      sieveL2PrefixEnergy N₂ M c ∧
      sieveL2PrefixEnergy N₁ M c ≤ sieveL2PrefixEnergy N₂ M c := by
  have hband := sieveL2PrefixEnergy_horizon_band_sub N₁ N₂ M c
  have hsq : 0 ≤ ∑ k ∈ Finset.Icc 1 M, sieveBandSeq N₁ N₂ c k ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor <;> linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
