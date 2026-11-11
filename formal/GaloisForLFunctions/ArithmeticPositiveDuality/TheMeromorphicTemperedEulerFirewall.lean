import GaloisForLFunctions.ArithmeticPositiveDuality.TheCriticalLineFirewall
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator

/-!
# The meromorphic tempered positive Euler-product firewall and left-strip pole obstruction

Given a zero-free frontier `Θ₀ ∈ [1/2, 1)` of `ζ` (`∀ z, Θ₀ < Re z → ζ(z) ≠ 0`), any off-line
ordinate `γ₀ ≠ 0`, any abscissa `β ∈ (Θ₀, 1)`, and a prime cutoff `P₀ ≥ 2` with
`2 (P₀ + 1)^{β − 1} ≤ 1`, set `ρ₀ = β + i γ₀` and define the truncated shifted-zeta quotient

`posTruncatedZeta P₀ ρ₀ s = ζ(s) · invZeta(s + 1 − ρ₀) · invZeta(s + 1 − conj ρ₀)`
`  · ∏_{p ≤ P₀} (1 − p^{ρ₀ − 1 − s})⁻¹ (1 − p^{conj ρ₀ − 1 − s})⁻¹`.

Unlike rounded Beurling or repeated-prime Euler countermodels, `posTruncatedZeta P₀ ρ₀`:
1. is globally meromorphic on `ℂ`, holomorphic on `{Re s > Θ₀ + β − 1} \ {1}` (strictly crossing
   `Θ₀` to the left since `β < 1`), with a simple pole of positive real residue at `s = 1`;
2. expands on `Re s > 1` into a multiplicative `LSeries` with real nonnegative Ramanujan-bounded
   coefficients (`0 ≤ a(n) ≤ C_ε n^ε`), a convergent distinct-prime Euler product over `Nat.Primes`,
   and a prime-power logarithmic derivative `0 ≤ Λ̃(n) ≤ 2 Λ(n)`;
3. satisfies polynomial vertical bounds on both `F` and `1/F` on closed strips right of `Θ₀`;
4. violates `HalfPlaneAbscissaLaw · Θ₀` with exact off-line zero set `{ρ₀, conj ρ₀}` in
   `{Re s > Θ₀} \ {1}`;
5. when `Θ₀ = Θ = zetaZeroAbscissa < 1`, develops a genuine pole (`‖F(s)‖ → +∞`) inside the left
   critical strip `0 < Re s < 1 − Θ ≤ 1/2` at `s_* = (1 − ρ_*) − 1 + ρ₀ = ρ₀ − ρ_*` for a
   near-frontier zero `ρ_*` of `ζ` (where `ζ(s_*) ≠ 0` by functional-equation reflection across the
   zero-free region `Re z > Θ`), and under `RiemannHypothesis` develops infinitely many poles along
   `Re s = β − 1/2 ∈ (0, 1/2)` from Hardy's critical-line zeros.

Combining this with `Θ = 1 → AsymptoticAbscissaLaw` yields the unconditional dichotomy
`asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff`.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality.CriticalLineFirewall

/-! ## 1. Frontier saturation implies `AsymptoticAbscissaLaw` -/

/-- If `Θ = zetaZeroAbscissa = 1`, no bilateral spectral gap can isolate a top zero layer left of
`Re s = 1`, so `AsymptoticAbscissaLaw` holds unconditionally from `Θ = 1`. -/
theorem asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one
    (hΘ : zetaZeroAbscissa = 1) : _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨_, β_star, _, _, _, hβ1, _, hzf, _⟩ :=
    not_asymptoticAbscissaLaw_iff_bilateral_spectralGap.mp hnot
  have hle : zetaZeroAbscissa ≤ β_star :=
    csSup_le zetaZeroReSet_nonempty fun x ⟨ρ, h0, hre⟩ => by
      rw [← hre]
      exact not_lt.mp fun hgt => hzf ρ hgt h0
  linarith

/-! ## 2. Prime cutoff, truncated Euler factors, and local prime-power coefficients -/

/-- Explicit prime cutoff `P₀ ≥ 2` satisfying `2 (P₀ + 1)^{β − 1} ≤ 1` for `β < 1`. -/
def posCutoff (β : ℝ) : ℕ :=
  max 2 ⌈(2 : ℝ) ^ (1 / (1 - β))⌉₊

theorem two_le_posCutoff (β : ℝ) : 2 ≤ posCutoff β :=
  le_max_left _ _

theorem two_mul_posCutoff_rpow_le_one {β : ℝ} (hβ1 : β < 1) :
    2 * ((posCutoff β : ℝ) + 1) ^ (β - 1) ≤ 1 := by
  have hsub : 0 < 1 - β := sub_pos.mpr hβ1
  have hbase_le : (2 : ℝ) ^ (1 / (1 - β)) ≤ (posCutoff β : ℝ) + 1 := by
    have h1 : (2 : ℝ) ^ (1 / (1 - β)) ≤ (⌈(2 : ℝ) ^ (1 / (1 - β))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(2 : ℝ) ^ (1 / (1 - β))⌉₊ : ℝ) ≤ (posCutoff β : ℝ) := by
      exact_mod_cast le_max_right 2 ⌈(2 : ℝ) ^ (1 / (1 - β))⌉₊
    linarith
  have hpos : (0 : ℝ) < (posCutoff β : ℝ) + 1 := by positivity
  have h2le : (2 : ℝ) ≤ ((posCutoff β : ℝ) + 1) ^ (1 - β) := by
    have hr := Real.rpow_le_rpow (by positivity) hbase_le hsub.le
    rw [← Real.rpow_mul two_pos.le, one_div_mul_cancel hsub.ne', Real.rpow_one] at hr
    exact hr
  rw [show β - 1 = -(1 - β) by ring, Real.rpow_neg hpos.le]
  exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos hpos _)).mpr (by linarith)

/-- Finite set of rational primes `p ≤ P₀` as a `Finset Nat.Primes`. -/
def smallPrimes (P₀ : ℕ) : Finset Nat.Primes :=
  (Finset.range (P₀ + 1)).subtype Nat.Prime

@[simp] theorem mem_smallPrimes {P₀ : ℕ} {q : Nat.Primes} :
    q ∈ smallPrimes P₀ ↔ (q : ℕ) ≤ P₀ := by
  simp [smallPrimes, Finset.mem_subtype, Finset.mem_range, Nat.lt_succ_iff]

/-- Finite prime-cutoff factor clearing the shifted `1/ζ` Euler factors at primes `p ≤ P₀`. -/
def posFiniteFactor (P₀ : ℕ) (ρ₀ s : ℂ) : ℂ :=
  ∏ q ∈ smallPrimes P₀,
    (1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s))⁻¹ *
      (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))⁻¹

/-- Regularized cofactor `F_pos(s) / ζ(s)` across `s = 1`. -/
def posCofactor (P₀ : ℕ) (ρ₀ s : ℂ) : ℂ :=
  invZeta (s + 1 - ρ₀) * invZeta (s + 1 - conj ρ₀) * posFiniteFactor P₀ ρ₀ s

/-- **The meromorphic tempered positive Euler-product model** with off-line zero pair `{ρ₀, conj ρ₀}`. -/
def posTruncatedZeta (P₀ : ℕ) (ρ₀ s : ℂ) : ℂ :=
  riemannZeta s * posCofactor P₀ ρ₀ s

/-- Distinct-prime local Euler factor of `posTruncatedZeta P₀ ρ₀` at `q : Nat.Primes`. -/
def posEulerFactor (P₀ : ℕ) (ρ₀ : ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if (q : ℕ) ≤ P₀ then
    (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹
  else
    (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹ *
      (1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s)) *
      (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))

/-- Explicit real prime-power coefficient of `posTruncatedZeta` at `(p, k)`. -/
def posLocalCoeff (P₀ : ℕ) (β γ₀ : ℝ) (p k : ℕ) : ℝ :=
  if k = 0 then 1
  else if p ≤ P₀ then 1
  else if k = 1 then 1 - 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log p)
  else ‖1 - (p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖ ^ 2

/-- Multiplicative real arithmetic coefficients of `posTruncatedZeta`. -/
def posTruncatedCoeff (P₀ : ℕ) (β γ₀ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, posLocalCoeff P₀ β γ₀ p (n.factorization p), by simp⟩

/-- Prime-power logarithmic-derivative weight of `posTruncatedZeta`. -/
def posTruncatedVonMangoldt (P₀ : ℕ) (β γ₀ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n =>
    if n.minFac ≤ P₀ then Λ n
    else Λ n * (1 - 2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n)), by simp⟩

/-! ## 3. Multiplicativity, nonnegativity, Ramanujan bound, and Euler product -/

theorem isMultiplicative_posTruncatedCoeff (P₀ : ℕ) (β γ₀ : ℝ) :
    (posTruncatedCoeff P₀ β γ₀).IsMultiplicative :=
  DampedMobius.isMultiplicative_of_prod (posLocalCoeff P₀ β γ₀) (posTruncatedCoeff P₀ β γ₀)
    fun n hn => dif_neg hn

theorem posTruncatedCoeff_one (P₀ : ℕ) (β γ₀ : ℝ) :
    posTruncatedCoeff P₀ β γ₀ 1 = 1 :=
  (isMultiplicative_posTruncatedCoeff P₀ β γ₀).1

theorem posTruncatedCoeff_prime_pow (P₀ : ℕ) (β γ₀ : ℝ) {p k : ℕ} (hp : p.Prime) :
    posTruncatedCoeff P₀ β γ₀ (p ^ k) = posLocalCoeff P₀ β γ₀ p k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [posTruncatedCoeff_one, posLocalCoeff]
  · have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
    change (if p ^ k = 0 then 0 else _) = _
    rw [if_neg hpk, DampedMobius.prod_prime_pow (posLocalCoeff P₀ β γ₀) hp hk]

private theorem rpow_neg_mono_antitone {a b e : ℝ} (ha : 0 < a) (hab : a ≤ b) (he : e < 0) :
    b ^ e ≤ a ^ e := by
  have hneg : 0 < -e := neg_pos.mpr he
  rw [show e = -(-e) by ring, Real.rpow_neg (ha.trans_le hab).le, Real.rpow_neg ha.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hab hneg.le)

theorem posLocalCoeff_nonneg {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    (hP₀ : 2 * ((P₀ : ℝ) + 1) ^ (β - 1) ≤ 1) (p k : ℕ) :
    0 ≤ posLocalCoeff P₀ β γ₀ p k := by
  unfold posLocalCoeff
  split_ifs with hk0 hpP hk1
  · norm_num
  · norm_num
  · have hp_ge : (P₀ : ℝ) + 1 ≤ (p : ℝ) := by
      have : P₀ + 1 ≤ p := Nat.succ_le_of_lt (not_le.mp hpP)
      exact_mod_cast this
    have hrpow : (p : ℝ) ^ (β - 1) ≤ ((P₀ : ℝ) + 1) ^ (β - 1) :=
      rpow_neg_mono_antitone (by positivity) hp_ge (by linarith)
    have hrpos : 0 ≤ (p : ℝ) ^ (β - 1) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hcos : Real.cos (γ₀ * Real.log p) ≤ 1 := Real.cos_le_one _
    nlinarith
  · positivity

theorem posTruncatedCoeff_nonneg {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    (hP₀ : 2 * ((P₀ : ℝ) + 1) ^ (β - 1) ≤ 1) (n : ℕ) :
    0 ≤ posTruncatedCoeff P₀ β γ₀ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · change 0 ≤ if n = 0 then 0 else _
    rw [if_neg hn]
    exact Finset.prod_nonneg fun p _ => posLocalCoeff_nonneg γ₀ hβ1 hP₀ p (n.factorization p)

theorem posLocalCoeff_le_four (P₀ : ℕ) {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    posLocalCoeff P₀ β γ₀ p k ≤ 4 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hrle1 : (p : ℝ) ^ (β - 1) ≤ 1 := by
    have h := rpow_neg_mono_antitone zero_lt_one hp1 (by linarith : β - 1 < 0)
    simpa using h
  have hrpos : 0 ≤ (p : ℝ) ^ (β - 1) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  unfold posLocalCoeff
  split_ifs with hk0 hpP hk1
  · norm_num
  · norm_num
  · have hcos : -1 ≤ Real.cos (γ₀ * Real.log p) := Real.neg_one_le_cos _
    nlinarith
  · have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hnorm_cpow : ‖(p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖ = (p : ℝ) ^ (β - 1) := by
      rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hppos]
      simp
    have htri : ‖1 - (p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖ ≤ 2 := by
      calc ‖1 - (p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖
          ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖ := norm_sub_le _ _
        _ = 1 + (p : ℝ) ^ (β - 1) := by rw [norm_one, hnorm_cpow]
        _ ≤ 2 := by linarith
    have hn0 : 0 ≤ ‖1 - (p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖ := norm_nonneg _
    nlinarith

/-- **Ramanujan growth bound:** for every `ε > 0`, `posTruncatedCoeff P₀ β γ₀ n ≤ C_ε n^ε`. -/
theorem exists_posTruncatedCoeff_le_rpow (P₀ : ℕ) {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    (hP₀ : 2 * ((P₀ : ℝ) + 1) ^ (β - 1) ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → posTruncatedCoeff P₀ β γ₀ n ≤ C * (n : ℝ) ^ ε := by
  classical
  let M : ℕ := ⌈(4 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨(4 : ℝ) ^ (M + 1), by positivity, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  change (if n = 0 then 0 else _) ≤ _
  rw [if_neg hn0]
  have hfactor : ∀ p ∈ n.primeFactors,
      posLocalCoeff P₀ β γ₀ p (n.factorization p) ≤
        (if p ≤ M then (4 : ℝ) else 1) * ((p ^ n.factorization p : ℕ) : ℝ) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfk : 1 ≤ n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hpp hn0 (Nat.dvd_of_mem_primeFactors hp)
    have hle4 := posLocalCoeff_le_four P₀ γ₀ hβ1 hpp (n.factorization p)
    have hpk1 : (1 : ℝ) ≤ ((p ^ n.factorization p : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ hpp.pos
    split_ifs with hpM
    · have hr1 : (1 : ℝ) ≤ ((p ^ n.factorization p : ℕ) : ℝ) ^ ε :=
        Real.one_le_rpow hpk1 hε.le
      nlinarith
    · rw [one_mul]
      have hp_gt : (4 : ℝ) ^ (1 / ε) < (p : ℝ) := by
        have h1 : (4 : ℝ) ^ (1 / ε) ≤ (M : ℝ) := Nat.le_ceil _
        have h2 : (M : ℝ) < (p : ℝ) := by exact_mod_cast not_le.mp hpM
        linarith
      have h4le : (4 : ℝ) ≤ (p : ℝ) ^ ε := by
        have hr := Real.rpow_le_rpow (by positivity) hp_gt.le hε.le
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), one_div_mul_cancel hε.ne',
          Real.rpow_one] at hr
        exact hr
      have hp_le_pk : (p : ℝ) ≤ ((p ^ n.factorization p : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_self_pow hfk.ne' p
      exact hle4.trans (h4le.trans (Real.rpow_le_rpow (Nat.cast_nonneg p) hp_le_pk hε.le))
  have hprod_le :
      ∏ p ∈ n.primeFactors, posLocalCoeff P₀ β γ₀ p (n.factorization p) ≤
        ∏ p ∈ n.primeFactors,
          (if p ≤ M then (4 : ℝ) else 1) * ((p ^ n.factorization p : ℕ) : ℝ) ^ ε :=
    Finset.prod_le_prod
      (fun p _ => posLocalCoeff_nonneg γ₀ hβ1 hP₀ p (n.factorization p)) hfactor
  rw [Finset.prod_mul_distrib] at hprod_le
  have hprod_n :
      (∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ) ^ ε) = (n : ℝ) ^ ε := by
    have hcast : ∀ s : Finset ℕ,
        (∏ p ∈ s, ((p ^ n.factorization p : ℕ) : ℝ) ^ ε) =
          ((∏ p ∈ s, p ^ n.factorization p : ℕ) : ℝ) ^ ε := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [Real.one_rpow]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
          Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ih]
    rw [hcast]
    have hself : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
      Nat.factorization_prod_pow_eq_self hn0
    rw [hself]
  have hprod_M :
      (∏ p ∈ n.primeFactors, if p ≤ M then (4 : ℝ) else 1) ≤ (4 : ℝ) ^ (M + 1) := by
    rw [← Finset.prod_filter]
    have hsub : n.primeFactors.filter (fun p => p ≤ M) ⊆ Finset.range (M + 1) := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    calc (∏ _p ∈ n.primeFactors.filter (fun p => p ≤ M), (4 : ℝ))
        = (4 : ℝ) ^ (n.primeFactors.filter (fun p => p ≤ M)).card := Finset.prod_const _
      _ ≤ (4 : ℝ) ^ (Finset.range (M + 1)).card :=
          pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hsub)
      _ = (4 : ℝ) ^ (M + 1) := by rw [Finset.card_range]
  rw [hprod_n] at hprod_le
  exact hprod_le.trans (mul_le_mul_of_nonneg_right hprod_M (by positivity))

/-- Weighted multiplicative arithmetic function `a(n) n^{-s}` for the Euler product on `Re s > 1`. -/
private def posWeightedArith (P₀ : ℕ) (β γ₀ : ℝ) (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ) * (n : ℂ) ^ (-s), by simp⟩

private theorem isMultiplicative_posWeightedArith (P₀ : ℕ) (β γ₀ : ℝ) (s : ℂ) :
    (posWeightedArith P₀ β γ₀ s).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · change (posTruncatedCoeff P₀ β γ₀ 1 : ℂ) * (1 : ℂ) ^ (-s) = 1
    simp [posTruncatedCoeff_one]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    change (posTruncatedCoeff P₀ β γ₀ (m * n) : ℂ) * ((m * n : ℕ) : ℂ) ^ (-s) =
      ((posTruncatedCoeff P₀ β γ₀ m : ℂ) * (m : ℂ) ^ (-s)) *
        ((posTruncatedCoeff P₀ β γ₀ n : ℂ) * (n : ℂ) ^ (-s))
    rw [(isMultiplicative_posTruncatedCoeff P₀ β γ₀).2 hmn, ofReal_mul,
      Nat.cast_mul, ← ofReal_natCast m, ← ofReal_natCast n,
      mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private theorem summable_norm_posWeightedArith {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    (hP₀ : 2 * ((P₀ : ℝ) + 1) ^ (β - 1) ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖posWeightedArith P₀ β γ₀ s n‖) := by
  set ε : ℝ := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_posTruncatedCoeff_le_rpow P₀ γ₀ hβ1 hP₀ hε
  have hsum : Summable (fun n : ℕ => C * ((n : ℝ) ^ (1 + ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + ε)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum
  rcases eq_or_ne n 0 with rfl | hn
  · have h1e : 1 + ε ≠ 0 := by linarith
    simp [Real.zero_rpow h1e]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    change ‖(posTruncatedCoeff P₀ β γ₀ n : ℂ) * (n : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (posTruncatedCoeff_nonneg γ₀ hβ1 hP₀ n),
      ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hnpos, neg_re]
    have hpow : (n : ℝ) ^ ε * (n : ℝ) ^ (-s.re) ≤ ((n : ℝ) ^ (1 + ε))⁻¹ := by
      rw [← Real.rpow_add hnpos, ← Real.rpow_neg hnpos.le]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by dsimp [ε]; linarith)
    calc posTruncatedCoeff P₀ β γ₀ n * (n : ℝ) ^ (-s.re)
        ≤ C * (n : ℝ) ^ ε * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hC n hn1) (Real.rpow_nonneg hnpos.le _)
      _ = C * ((n : ℝ) ^ ε * (n : ℝ) ^ (-s.re)) := by ring
      _ ≤ C * ((n : ℝ) ^ (1 + ε))⁻¹ := mul_le_mul_of_nonneg_left hpow hC0.le

private theorem tsum_posWeightedArith_eq_LSeries (P₀ : ℕ) (β γ₀ : ℝ) (s : ℂ) :
    (∑' n : ℕ, posWeightedArith P₀ β γ₀ s n) =
      LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s := by
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · change (posTruncatedCoeff P₀ β γ₀ n : ℂ) * (n : ℂ) ^ (-s) = LSeries.term _ s n
    rw [LSeries.term_of_ne_zero hn, cpow_neg, div_eq_mul_inv]

private theorem natCast_pow_cpow_neg (p k : ℕ) (s : ℂ) :
    (((p ^ k : ℕ) : ℂ) ^ (-s)) = ((p : ℂ) ^ (-s)) ^ k := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Nat.cast_mul, ← ofReal_natCast (p ^ m), ← ofReal_natCast p,
      mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_natCast, ih]

private theorem prime_cpow_add_conj (p : ℕ) (hp : 0 < p) (β γ₀ : ℝ) :
    (p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1) +
        (p : ℂ) ^ (conj ((β : ℂ) + (γ₀ : ℂ) * I) - 1) =
      ((2 * (p : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log p) : ℝ) : ℂ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((β : ℂ) + (γ₀ : ℂ) * I) - 1 = ((β - 1 : ℝ) : ℂ) + (γ₀ : ℂ) * I := by
    push_cast; ring
  have h2 : conj ((β : ℂ) + (γ₀ : ℂ) * I) - 1 = ((β - 1 : ℝ) : ℂ) + -((γ₀ : ℂ) * I) := by
    simp [sub_eq_add_neg]; ring
  rw [h1, h2, cpow_add _ _ hp0, cpow_add _ _ hp0, cpow_neg]
  have hcos : (p : ℂ) ^ ((γ₀ : ℂ) * I) + ((p : ℂ) ^ ((γ₀ : ℂ) * I))⁻¹ =
      ((2 * Real.cos (γ₀ * Real.log p) : ℝ) : ℂ) := by
    rw [← cpow_neg, cpow_def_of_ne_zero hp0, cpow_def_of_ne_zero hp0, ← natCast_log]
    have h := Complex.two_cos ((γ₀ * Real.log p : ℝ) : ℂ)
    rw [show ((2 * Real.cos (γ₀ * Real.log p) : ℝ) : ℂ) =
        2 * Complex.cos ((γ₀ * Real.log p : ℝ) : ℂ) by push_cast; rfl, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  have hr : (p : ℂ) ^ ((β - 1 : ℝ) : ℂ) = (((p : ℝ) ^ (β - 1) : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ofReal_cpow hpR.le]
  rw [ ← mul_add, hcos, hr]
  push_cast
  ring

private theorem prime_cpow_conj_eq (p : ℕ) (hp : 0 < p) (w : ℂ) :
    (p : ℂ) ^ (conj w) = conj ((p : ℂ) ^ w) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [cpow_def_of_ne_zero hp0, cpow_def_of_ne_zero hp0, ← Complex.exp_conj, map_mul,
    ← natCast_log, conj_ofReal]

private theorem tsum_posWeightedArith_prime_pow {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    {s : ℂ} (hs : 1 < s.re) (q : Nat.Primes) :
    (∑' k : ℕ, posWeightedArith P₀ β γ₀ s ((q : ℕ) ^ k)) =
      posEulerFactor P₀ ((β : ℂ) + (γ₀ : ℂ) * I) q s := by
  set p : ℕ := (q : ℕ)
  have hp : p.Prime := q.prop
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set x : ℂ := (p : ℂ) ^ (-s)
  have hx_norm : ‖x‖ < 1 := by
    dsimp [x]
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by linarith), neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  have hx1 : 1 - x ≠ 0 := fun h => by
    have : ‖(1 : ℂ)‖ ≤ ‖x‖ := by rw [sub_eq_zero.mp h]
    rw [norm_one] at this
    linarith
  have hterm : ∀ k : ℕ,
      posWeightedArith P₀ β γ₀ s (p ^ k) = (posLocalCoeff P₀ β γ₀ p k : ℂ) * x ^ k := by
    intro k
    have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
    change (posTruncatedCoeff P₀ β γ₀ (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-s) = _
    rw [posTruncatedCoeff_prime_pow P₀ β γ₀ hp, natCast_pow_cpow_neg]
  simp_rw [hterm]
  unfold posEulerFactor
  split_ifs with hpP
  · have hc1 : ∀ k : ℕ, (posLocalCoeff P₀ β γ₀ p k : ℂ) * x ^ k = x ^ k := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk0
      · simp [posLocalCoeff]
      · simp [posLocalCoeff, hk0, hpP]
    simp_rw [hc1]
    exact tsum_geometric_of_norm_lt_one hx_norm
  · set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
    set α : ℂ := (p : ℂ) ^ (ρ₀ - 1)
    set α' : ℂ := (p : ℂ) ^ (conj ρ₀ - 1)
    have hsum_loc : Summable (fun k : ℕ => (posLocalCoeff P₀ β γ₀ p k : ℂ) * x ^ k) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg x) hx_norm).mul_left 4)
        fun k => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have habs : |posLocalCoeff P₀ β γ₀ p k| ≤ 4 := by
        rw [abs_le]
        refine ⟨?_, posLocalCoeff_le_four P₀ γ₀ hβ1 hp k⟩
        unfold posLocalCoeff
        split_ifs with hk0 _ hk1
        · norm_num
        · norm_num
        · have hr1 : (p : ℝ) ^ (β - 1) ≤ 1 := by
            have h := rpow_neg_mono_antitone zero_lt_one hpR.le (by linarith : β - 1 < 0)
            simpa using h
          have hr0 : 0 ≤ (p : ℝ) ^ (β - 1) := Real.rpow_nonneg (by positivity) _
          have hc : Real.cos (γ₀ * Real.log p) ≤ 1 := Real.cos_le_one _
          nlinarith
        · linarith [sq_nonneg ‖1 - (p : ℂ) ^ (((β : ℂ) + (γ₀ : ℂ) * I) - 1)‖]
      exact mul_le_mul_of_nonneg_right habs (pow_nonneg (norm_nonneg x) k)
    have hsum_shift : Summable (fun k : ℕ => (posLocalCoeff P₀ β γ₀ p (k + 1) : ℂ) * x ^ (k + 1)) :=
      (summable_nat_add_iff 1).mpr hsum_loc
    rw [hsum_loc.tsum_eq_zero_add, hsum_shift.tsum_eq_zero_add]
    have hc0 : (posLocalCoeff P₀ β γ₀ p 0 : ℂ) * x ^ 0 = 1 := by simp [posLocalCoeff]
    have hc1 : (posLocalCoeff P₀ β γ₀ p 1 : ℂ) * x ^ 1 = (1 - (α + α')) * x := by
      have hloc : posLocalCoeff P₀ β γ₀ p 1 =
          1 - 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log p) := by
        simp [posLocalCoeff, hpP]
      rw [hloc, pow_one, ofReal_sub, ofReal_one, ← prime_cpow_add_conj p hp.pos β γ₀]
    have hc2 : ∀ k : ℕ,
        (posLocalCoeff P₀ β γ₀ p (k + 2) : ℂ) * x ^ (k + 2) =
          (1 - α) * (1 - α') * x ^ 2 * x ^ k := by
      intro k
      have hloc : posLocalCoeff P₀ β γ₀ p (k + 2) = ‖1 - α‖ ^ 2 := by
        simp [posLocalCoeff, hpP, α, ρ₀]
      have hconj : 1 - α' = conj (1 - α) := by
        dsimp [α, α']
        rw [map_sub, map_one, ← prime_cpow_conj_eq p hp.pos (ρ₀ - 1), map_sub, map_one]
      have hnorm_sq : ((‖1 - α‖ ^ 2 : ℝ) : ℂ) = (1 - α) * (1 - α') := by
        rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hloc, hnorm_sq, pow_add x k 2]
      ring
    simp_rw [hc0, hc1, hc2]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hx_norm]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hax : α * x = (p : ℂ) ^ (ρ₀ - 1 - s) := by
      dsimp [α, x]
      rw [← cpow_add _ _ hp0, sub_eq_add_neg]
    have ha'x : α' * x = (p : ℂ) ^ (conj ρ₀ - 1 - s) := by
      dsimp [α', x]
      rw [← cpow_add _ _ hp0, sub_eq_add_neg]
    rw [← hax, ← ha'x]
    apply mul_right_cancel₀ hx1
    calc (1 + ((1 - (α + α')) * x + (1 - α) * (1 - α') * x ^ 2 * (1 - x)⁻¹)) * (1 - x)
        = (1 + (1 - (α + α')) * x) * (1 - x) +
            (1 - α) * (1 - α') * x ^ 2 * ((1 - x)⁻¹ * (1 - x)) := by ring
      _ = (1 + (1 - (α + α')) * x) * (1 - x) + (1 - α) * (1 - α') * x ^ 2 := by
          rw [inv_mul_cancel₀ hx1, mul_one]
      _ = (1 - α * x) * (1 - α' * x) := by ring
      _ = (1 - x)⁻¹ * (1 - α * x) * (1 - α' * x) * (1 - x) := by
          rw [mul_right_comm _ (1 - α' * x) (1 - x),
            mul_right_comm _ (1 - α * x) (1 - x), inv_mul_cancel₀ hx1, one_mul]

private theorem one_sub_prime_cpow_ne_zero {w : ℂ} (hw : w.re < 0) (q : Nat.Primes) :
    1 - ((q : ℕ) : ℂ) ^ w ≠ 0 := by
  intro h
  have hp1 : (1 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.one_lt
  have hnorm : ‖((q : ℕ) : ℂ) ^ w‖ < 1 := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hw
  have heq : ((q : ℕ) : ℂ) ^ w = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- **Euler product and `LSeries` identity on `Re s > 1`:** the multiplicative `LSeries` of
`posTruncatedCoeff` and the distinct-prime Euler product of `posEulerFactor` both converge to
`posTruncatedZeta P₀ (β + i γ₀) s`. -/
theorem hasProd_and_LSeries_posTruncatedZeta {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    (hP₀ : 2 * ((P₀ : ℝ) + 1) ^ (β - 1) ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q : Nat.Primes => posEulerFactor P₀ ((β : ℂ) + (γ₀ : ℂ) * I) q s)
        (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s) ∧
      LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s =
        posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s := by
  classical
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  have hLprod : HasProd (fun q : Nat.Primes => posEulerFactor P₀ ρ₀ q s)
      (LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s) := by
    have h := (isMultiplicative_posWeightedArith P₀ β γ₀ s).eulerProduct_hasProd
      (summable_norm_posWeightedArith γ₀ hβ1 hP₀ hs)
    rw [tsum_posWeightedArith_eq_LSeries] at h
    simpa only [tsum_posWeightedArith_prime_pow γ₀ hβ1 hs] using h
  have hw1_re : 1 < (s + 1 - ρ₀).re := by
    have : (s + 1 - ρ₀).re = s.re + 1 - β := by simp [ρ₀]
    linarith
  have hw2_re : 1 < (s + 1 - conj ρ₀).re := by
    have : (s + 1 - conj ρ₀).re = s.re + 1 - β := by simp [ρ₀]
    linarith
  have hZ0 := riemannZeta_eulerProduct_hasProd hs
  have hZ1 := riemannZeta_eulerProduct_hasProd hw1_re
  have hZ2 := riemannZeta_eulerProduct_hasProd hw2_re
  set e : Nat.Primes → ℂ := fun q =>
    if q ∈ smallPrimes P₀ then
      (1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))⁻¹
    else 1 with he
  have hE : HasProd e (posFiniteFactor P₀ ρ₀ s) := by
    have hp := hasProd_prod_of_ne_finset_one (f := e) (s := smallPrimes P₀) fun q hq => by
      rw [he, if_neg hq]
    have hpeq : (∏ q ∈ smallPrimes P₀, e q) = posFiniteFactor P₀ ρ₀ s :=
      Finset.prod_congr rfl fun q hq => by rw [he, if_pos hq]
    rwa [hpeq] at hp
  have hprod_lhs := (hLprod.mul hZ1).mul hZ2
  have hprod_rhs := hZ0.mul hE
  have hfun : (fun q : Nat.Primes =>
      posEulerFactor P₀ ρ₀ q s * (1 - ((q : ℕ) : ℂ) ^ (-(s + 1 - ρ₀)))⁻¹ *
        (1 - ((q : ℕ) : ℂ) ^ (-(s + 1 - conj ρ₀)))⁻¹) =
      fun q : Nat.Primes => (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹ * e q := by
    funext q
    have he1 : -(s + 1 - ρ₀) = ρ₀ - 1 - s := by ring
    have he2 : -(s + 1 - conj ρ₀) = conj ρ₀ - 1 - s := by ring
    rw [he1, he2, he, mem_smallPrimes]
    unfold posEulerFactor
    split_ifs with hq
    · ring
    · have hne1 : 1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s) ≠ 0 :=
        one_sub_prime_cpow_ne_zero (by rw [← he1, neg_re]; linarith) q
      have hne2 : 1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s) ≠ 0 :=
        one_sub_prime_cpow_ne_zero (by rw [← he2, neg_re]; linarith) q
      rw [mul_one, mul_assoc _ (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s)),
        mul_inv_cancel_right₀ hne2, mul_inv_cancel_right₀ hne1]
  rw [hfun] at hprod_lhs
  have heq_mul :
      LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s *
        riemannZeta (s + 1 - ρ₀) * riemannZeta (s + 1 - conj ρ₀) =
      riemannZeta s * posFiniteFactor P₀ ρ₀ s :=
    hprod_lhs.unique hprod_rhs
  have hw1_ne1 : s + 1 - ρ₀ ≠ 1 := fun h => by rw [h] at hw1_re; simp at hw1_re
  have hw2_ne1 : s + 1 - conj ρ₀ ≠ 1 := fun h => by rw [h] at hw2_re; simp at hw2_re
  have hz1_ne : riemannZeta (s + 1 - ρ₀) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw1_re
  have hz2_ne : riemannZeta (s + 1 - conj ρ₀) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw2_re
  have hLeq : LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s = posTruncatedZeta P₀ ρ₀ s := by
    unfold posTruncatedZeta posCofactor
    rw [invZeta_eq_inv hw1_ne1, invZeta_eq_inv hw2_ne1]
    apply mul_right_cancel₀ hz2_ne
    apply mul_right_cancel₀ hz1_ne
    calc LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s *
            riemannZeta (s + 1 - conj ρ₀) * riemannZeta (s + 1 - ρ₀)
        = LSeries (fun n => (posTruncatedCoeff P₀ β γ₀ n : ℂ)) s *
            riemannZeta (s + 1 - ρ₀) * riemannZeta (s + 1 - conj ρ₀) := by ring
      _ = riemannZeta s * posFiniteFactor P₀ ρ₀ s := heq_mul
      _ = riemannZeta s *
            ((riemannZeta (s + 1 - ρ₀))⁻¹ * (riemannZeta (s + 1 - conj ρ₀))⁻¹ *
              posFiniteFactor P₀ ρ₀ s) *
            riemannZeta (s + 1 - conj ρ₀) * riemannZeta (s + 1 - ρ₀) := by
          field_simp [hz1_ne, hz2_ne]
  exact ⟨hLeq ▸ hLprod, hLeq⟩

/-! ## 4. Prime-power logarithmic derivative `0 ≤ Λ̃(n) ≤ 2 Λ(n)` -/

theorem posTruncatedVonMangoldt_bounds {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    (hP₀ : 2 * ((P₀ : ℝ) + 1) ^ (β - 1) ≤ 1) (n : ℕ) :
    0 ≤ posTruncatedVonMangoldt P₀ β γ₀ n ∧ posTruncatedVonMangoldt P₀ β γ₀ n ≤ 2 * Λ n := by
  have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rcases eq_or_ne (Λ n) 0 with hzero | hne
  · change (0 ≤ if n.minFac ≤ P₀ then Λ n else _) ∧ (if n.minFac ≤ P₀ then Λ n else _) ≤ 2 * Λ n
    simp [hzero]
  · have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
    change (0 ≤ if n.minFac ≤ P₀ then Λ n else _) ∧ (if n.minFac ≤ P₀ then Λ n else _) ≤ 2 * Λ n
    split_ifs with hmin
    · exact ⟨hΛ0, by linarith⟩
    · have hn_ge : (P₀ : ℝ) + 1 ≤ (n : ℝ) := by
        have h1 : P₀ + 1 ≤ n.minFac := Nat.succ_le_of_lt (not_le.mp hmin)
        have h2 : n.minFac ≤ n := Nat.minFac_le hpp.pos
        exact_mod_cast h1.trans h2
      have hr : (n : ℝ) ^ (β - 1) ≤ ((P₀ : ℝ) + 1) ^ (β - 1) :=
        rpow_neg_mono_antitone (by positivity) hn_ge (by linarith)
      have hr0 : 0 ≤ (n : ℝ) ^ (β - 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hc1 : Real.cos (γ₀ * Real.log n) ≤ 1 := Real.cos_le_one _
      have hc2 : -1 ≤ Real.cos (γ₀ * Real.log n) := Real.neg_one_le_cos _
      have hw0 : 0 ≤ 1 - 2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n) := by nlinarith
      have hw2 : 1 - 2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n) ≤ 2 := by nlinarith
      exact ⟨mul_nonneg hΛ0 hw0, by nlinarith⟩

private def primePowVonMangoldt (q : Nat.Primes) (n : ℕ) : ℂ :=
  if ∃ k : ℕ, n = (q : ℕ) ^ (k + 1) then (Real.log (q : ℕ) : ℂ) else 0

private theorem sum_smallPrimes_primePowVonMangoldt (P₀ n : ℕ) :
    (∑ q ∈ smallPrimes P₀, primePowVonMangoldt q n) =
      if n.minFac ≤ P₀ then (Λ n : ℂ) else 0 := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff.mp hpp
    have hk' : k ≠ 0 := hk.ne'
    have hmin : (p ^ k).minFac = p := hp.pow_minFac hk'
    let q₀ : Nat.Primes := ⟨p, hp⟩
    have hsingle : ∀ q ∈ smallPrimes P₀, q ≠ q₀ → primePowVonMangoldt q (p ^ k) = 0 := by
      intro q _ hqne
      unfold primePowVonMangoldt
      rw [if_neg]
      rintro ⟨m, hm⟩
      apply hqne
      ext
      have := congrArg Nat.minFac hm
      rwa [hmin, q.prop.pow_minFac (Nat.succ_ne_zero m)] at this
    have hval : primePowVonMangoldt q₀ (p ^ k) = (Λ (p ^ k) : ℂ) := by
      unfold primePowVonMangoldt
      rw [if_pos ⟨k - 1, by omega⟩, ArithmeticFunction.vonMangoldt_apply_pow hk',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    rw [hmin]
    by_cases hpP : p ≤ P₀
    · have hmem : q₀ ∈ smallPrimes P₀ := mem_smallPrimes.mpr hpP
      rw [if_pos hpP, Finset.sum_eq_single q₀ hsingle (fun h => absurd hmem h), hval]
    · rw [if_neg hpP]
      refine Finset.sum_eq_zero fun q hq => hsingle q hq fun h => hpP ?_
      rw [← h]
      exact mem_smallPrimes.mp hq
  · have hΛ0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    rw [hΛ0]
    simp only [ofReal_zero, ite_self]
    refine Finset.sum_eq_zero fun q _ => ?_
    unfold primePowVonMangoldt
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hpp (q.prop.prime.isPrimePow.pow (Nat.succ_ne_zero k))

private theorem LSeriesSummable_primePowVonMangoldt (q : Nat.Primes) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (primePowVonMangoldt q) w := by
  refine LSeriesSummable.of_nonneg_of_le (f := fun n => Λ n) ?_ ?_
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hw)
  · intro n; positivity
  · intro n
    unfold primePowVonMangoldt
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by exact_mod_cast q.prop.one_lt.le)),
        ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
        ArithmeticFunction.vonMangoldt_apply_prime q.prop]
    · simp [ArithmeticFunction.vonMangoldt_nonneg]

private theorem logDeriv_inv_one_sub_prime_cpow (q : Nat.Primes) {c s : ℂ}
    (hw : 1 < (s - c).re) :
    logDeriv (fun z => (1 - ((q : ℕ) : ℂ) ^ (c - z))⁻¹) s =
      -LSeries (primePowVonMangoldt q) (s - c) := by
  set p : ℕ := (q : ℕ)
  have hp : p.Prime := q.prop
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw' : (c - s).re < 0 := by
    have : (c - s).re = -(s - c).re := by simp
    linarith
  have h1sub : 1 - (p : ℂ) ^ (c - s) ≠ 0 := one_sub_prime_cpow_ne_zero hw' q
  have hhas_g : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (c - z))
      ((Real.log p : ℂ) * (p : ℂ) ^ (c - s)) s := by
    have heq : (fun z : ℂ => 1 - (p : ℂ) ^ (c - z)) =
        fun z : ℂ => 1 - Complex.exp (Complex.log (p : ℂ) * (c - z)) := by
      funext z
      rw [cpow_def_of_ne_zero hp0]
    rw [heq]
    have hd1 : HasDerivAt (fun z : ℂ => Complex.log (p : ℂ) * (c - z)) (-Complex.log (p : ℂ)) s := by
      simpa using ((hasDerivAt_const s c).sub (hasDerivAt_id s)).const_mul (Complex.log (p : ℂ))
    have hd2 := HasDerivAt.const_sub 1 hd1.cexp
    convert hd2 using 1
    rw [← cpow_def_of_ne_zero hp0, ← natCast_log]
    ring
  have hhas_inv : HasDerivAt (fun z : ℂ => (1 - (p : ℂ) ^ (c - z))⁻¹)
      (-((Real.log p : ℂ) * (p : ℂ) ^ (c - s)) / (1 - (p : ℂ) ^ (c - s)) ^ 2) s :=
    hhas_g.inv h1sub
  have hld : logDeriv (fun z => (1 - (p : ℂ) ^ (c - z))⁻¹) s =
      -(Real.log p : ℂ) * (p : ℂ) ^ (c - s) * (1 - (p : ℂ) ^ (c - s))⁻¹ := by
    rw [logDeriv_apply, hhas_inv.deriv]
    field_simp [h1sub]
  set x : ℂ := (p : ℂ) ^ (-(s - c))
  have hx_eq : x = (p : ℂ) ^ (c - s) := by
    dsimp [x]; congr 1; ring
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hx_norm : ‖x‖ < 1 := by
    rw [hx_eq, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hw'
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := fun a b hab =>
    Nat.succ.inj (Nat.pow_right_injective hp.one_lt hab)
  have hsupp : Function.support (LSeries.term (primePowVonMangoldt q) (s - c)) ⊆
      Set.range (fun k : ℕ => p ^ (k + 1)) := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hn
    · rw [Function.mem_support, LSeries.term_of_ne_zero hn0] at hn
      by_contra hnot
      apply hn
      have hpv : primePowVonMangoldt q n = 0 := by
        unfold primePowVonMangoldt
        exact if_neg fun ⟨k, hk⟩ => hnot ⟨k, hk.symm⟩
      simp [hpv]
  have hL : LSeries (primePowVonMangoldt q) (s - c) =
      (Real.log p : ℂ) * x * (1 - x)⁻¹ := by
    unfold LSeries
    rw [← hinj.tsum_eq hsupp]
    have hterm : ∀ k : ℕ, LSeries.term (primePowVonMangoldt q) (s - c) (p ^ (k + 1)) =
        (Real.log p : ℂ) * x * x ^ k := by
      intro k
      have hpk0 : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [LSeries.term_of_ne_zero hpk0, ← cpow_neg,
        show primePowVonMangoldt q (p ^ (k + 1)) = (Real.log p : ℂ) by
          unfold primePowVonMangoldt; exact if_pos ⟨k, rfl⟩,
        natCast_pow_cpow_neg p (k + 1) (s - c), pow_succ']
      dsimp [x]
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hx_norm]
  rw [hld, hL, hx_eq]
  ring

private theorem differentiableAt_inv_one_sub_prime_cpow (q : Nat.Primes) {c s : ℂ}
    (hw : (c - s).re < 0) :
    DifferentiableAt ℂ (fun z => (1 - ((q : ℕ) : ℂ) ^ (c - z))⁻¹) s := by
  have hp0 : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  have heq : (fun z : ℂ => 1 - ((q : ℕ) : ℂ) ^ (c - z)) =
      fun z : ℂ => 1 - Complex.exp (Complex.log ((q : ℕ) : ℂ) * (c - z)) := by
    funext z; rw [cpow_def_of_ne_zero hp0]
  have hd : DifferentiableAt ℂ (fun z : ℂ => 1 - ((q : ℕ) : ℂ) ^ (c - z)) s := by
    rw [heq]
    exact differentiableAt_const _ |>.sub
      ((differentiableAt_const _ |>.mul (differentiableAt_const _ |>.sub differentiableAt_id)).cexp)
  exact hd.inv (one_sub_prime_cpow_ne_zero hw q)

private theorem logDeriv_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (hne : ∀ i ∈ S, f i s ≠ 0) (hd : ∀ i ∈ S, DifferentiableAt ℂ (f i) s) :
    logDeriv (fun z => ∏ i ∈ S, f i z) s = ∑ i ∈ S, logDeriv (f i) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [logDeriv_const]
  | insert a S ha ih =>
    have hfn : (fun z => ∏ i ∈ insert a S, f i z) =
        fun z => f a z * ∏ i ∈ S, f i z := by
      funext z; exact Finset.prod_insert ha
    have hprod_ne : (∏ i ∈ S, f i s) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hne i (Finset.mem_insert_of_mem hi)
    have hprod_d : DifferentiableAt ℂ (fun z => ∏ i ∈ S, f i z) s := by
      have hp : (fun z => ∏ i ∈ S, f i z) = ∏ i ∈ S, f i := by funext z; simp
      rw [hp]
      exact Finset.prod_induction f (fun g => DifferentiableAt ℂ g s)
        (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) (differentiableAt_const 1)
        fun i hi => hd i (Finset.mem_insert_of_mem hi)
    rw [hfn, Finset.sum_insert ha,
      logDeriv_mul s (hne a (Finset.mem_insert_self a S)) hprod_ne
        (hd a (Finset.mem_insert_self a S)) hprod_d,
      ih (fun i hi => hne i (Finset.mem_insert_of_mem hi))
        (fun i hi => hd i (Finset.mem_insert_of_mem hi))]

private theorem LSeries_sum_smallPrimes_primePowVonMangoldt (P₀ : ℕ) {w : ℂ} (hw : 1 < w.re) :
    (∑ q ∈ smallPrimes P₀, LSeries (primePowVonMangoldt q) w) =
      LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) w := by
  classical
  have hsum : ∀ q ∈ smallPrimes P₀, Summable (LSeries.term (primePowVonMangoldt q) w) :=
    fun q _ => LSeriesSummable_primePowVonMangoldt q hw
  unfold LSeries
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · simp only [LSeries.term_of_ne_zero hn0, ← Finset.sum_div,
      sum_smallPrimes_primePowVonMangoldt]

/-- **Logarithmic derivative `LSeries` identity on `Re s > 1`:**
`−(posTruncatedZeta P₀ ρ₀)'(s) / posTruncatedZeta P₀ ρ₀ s = LSeries posTruncatedVonMangoldt s`. -/
theorem neg_logDeriv_posTruncatedZeta_eq_LSeries {P₀ : ℕ} {β : ℝ} (γ₀ : ℝ) (hβ1 : β < 1)
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) s =
      LSeries (fun n => (posTruncatedVonMangoldt P₀ β γ₀ n : ℂ)) s := by
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  set c₁ : ℂ := ρ₀ - 1
  set c₂ : ℂ := conj ρ₀ - 1
  have hw₁ : 1 < (s - c₁).re := by
    have : (s - c₁).re = s.re + 1 - β := by simp [c₁, ρ₀]
    linarith
  have hw₂ : 1 < (s - c₂).re := by
    have : (s - c₂).re = s.re + 1 - β := by simp [c₂, ρ₀]
    linarith
  have hne1 : ∀ w : ℂ, 1 < w.re → w ≠ 1 := fun w hw h => by rw [h] at hw; simp at hw
  have hz_ne : ∀ w : ℂ, 1 < w.re → riemannZeta w ≠ 0 := fun w hw =>
    riemannZeta_ne_zero_of_one_lt_re hw
  have hz_d : ∀ w : ℂ, 1 < w.re → DifferentiableAt ℂ riemannZeta w := fun w hw =>
    differentiableAt_riemannZeta (hne1 w hw)
  have hlogζ : ∀ w : ℂ, 1 < w.re →
      logDeriv riemannZeta w = -LSeries (fun n => (Λ n : ℂ)) w := by
    intro w hw
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw, logDeriv_apply]
    ring
  have hev : posTruncatedZeta P₀ ρ₀ =ᶠ[𝓝 s] fun z =>
      riemannZeta z * (riemannZeta (z - c₁))⁻¹ * (riemannZeta (z - c₂))⁻¹ *
        posFiniteFactor P₀ ρ₀ z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz₁ : z + 1 - ρ₀ ≠ 1 := by
      refine hne1 _ ?_
      have : (z + 1 - ρ₀).re = z.re + 1 - β := by simp [ρ₀]
      linarith
    have hz₂ : z + 1 - conj ρ₀ ≠ 1 := by
      refine hne1 _ ?_
      have : (z + 1 - conj ρ₀).re = z.re + 1 - β := by simp [ρ₀]
      linarith
    have he1 : z + 1 - ρ₀ = z - c₁ := by dsimp [c₁]; ring
    have he2 : z + 1 - conj ρ₀ = z - c₂ := by dsimp [c₂]; ring
    unfold posTruncatedZeta posCofactor
    rw [invZeta_eq_inv hz₁, invZeta_eq_inv hz₂, he1, he2]
    ring
  have hld_eq : logDeriv (posTruncatedZeta P₀ ρ₀) s =
      logDeriv (fun z => riemannZeta z * (riemannZeta (z - c₁))⁻¹ *
        (riemannZeta (z - c₂))⁻¹ * posFiniteFactor P₀ ρ₀ z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hd_shift : ∀ c : ℂ, 1 < (s - c).re →
      DifferentiableAt ℂ (fun z => (riemannZeta (z - c))⁻¹) s ∧
        logDeriv (fun z => (riemannZeta (z - c))⁻¹) s = -logDeriv riemannZeta (s - c) := by
    intro c hwc
    have hd_sub : DifferentiableAt ℂ (fun z : ℂ => z - c) s := differentiableAt_id.sub_const c
    have hd_z : DifferentiableAt ℂ (fun z => riemannZeta (z - c)) s :=
      (hz_d _ hwc).comp s hd_sub
    refine ⟨hd_z.inv (hz_ne _ hwc), ?_⟩
    rw [logDeriv_inv, show (fun z => riemannZeta (z - c)) = riemannZeta ∘ (fun z => z - c) from rfl,
      logDeriv_comp (hz_d _ hwc) hd_sub, deriv_sub_const, deriv_id'', mul_one]
  have hfin_ne : posFiniteFactor P₀ ρ₀ s ≠ 0 := by
    unfold posFiniteFactor
    refine Finset.prod_ne_zero_iff.mpr fun q _ => mul_ne_zero
      (inv_ne_zero (one_sub_prime_cpow_ne_zero ?_ q))
      (inv_ne_zero (one_sub_prime_cpow_ne_zero ?_ q))
    · have : (ρ₀ - 1 - s).re = -(s - c₁).re := by dsimp [c₁]; simp; ring
      linarith
    · have : (conj ρ₀ - 1 - s).re = -(s - c₂).re := by dsimp [c₂]; simp; ring
      linarith
  have hfin_d_and_ld : DifferentiableAt ℂ (posFiniteFactor P₀ ρ₀) s ∧
      logDeriv (posFiniteFactor P₀ ρ₀) s =
        -(LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₁) +
          LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₂)) := by
    have hq_ne : ∀ q ∈ smallPrimes P₀,
        (1 - ((q : ℕ) : ℂ) ^ (c₁ - s))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (c₂ - s))⁻¹ ≠ 0 := by
      intro q _
      refine mul_ne_zero (inv_ne_zero (one_sub_prime_cpow_ne_zero ?_ q))
        (inv_ne_zero (one_sub_prime_cpow_ne_zero ?_ q))
      · have : (c₁ - s).re = -(s - c₁).re := by simp
        linarith
      · have : (c₂ - s).re = -(s - c₂).re := by simp
        linarith
    have hq_d : ∀ q ∈ smallPrimes P₀,
        DifferentiableAt ℂ (fun z =>
          (1 - ((q : ℕ) : ℂ) ^ (c₁ - z))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (c₂ - z))⁻¹) s := by
      intro q _
      refine (differentiableAt_inv_one_sub_prime_cpow q ?_).mul
        (differentiableAt_inv_one_sub_prime_cpow q ?_)
      · have : (c₁ - s).re = -(s - c₁).re := by simp
        linarith
      · have : (c₂ - s).re = -(s - c₂).re := by simp
        linarith
    have hpf_eq : posFiniteFactor P₀ ρ₀ = fun z => ∏ q ∈ smallPrimes P₀,
        (1 - ((q : ℕ) : ℂ) ^ (c₁ - z))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (c₂ - z))⁻¹ := rfl
    refine ⟨?_, ?_⟩
    · rw [hpf_eq]
      have hp : (fun z => ∏ q ∈ smallPrimes P₀,
          (1 - ((q : ℕ) : ℂ) ^ (c₁ - z))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (c₂ - z))⁻¹) =
        ∏ q ∈ smallPrimes P₀, fun z =>
          (1 - ((q : ℕ) : ℂ) ^ (c₁ - z))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (c₂ - z))⁻¹ := by
        funext z; simp
      rw [hp]
      exact Finset.prod_induction _ (fun g => DifferentiableAt ℂ g s)
        (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) (differentiableAt_const 1) hq_d
    · rw [hpf_eq, logDeriv_finset_prod (smallPrimes P₀) _ s hq_ne hq_d]
      have hterm : ∀ q ∈ smallPrimes P₀,
          logDeriv (fun z =>
            (1 - ((q : ℕ) : ℂ) ^ (c₁ - z))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (c₂ - z))⁻¹) s =
          -(LSeries (primePowVonMangoldt q) (s - c₁) +
            LSeries (primePowVonMangoldt q) (s - c₂)) := by
        intro q _
        have hc1_neg : (c₁ - s).re < 0 := by
          have : (c₁ - s).re = -(s - c₁).re := by simp
          linarith
        have hc2_neg : (c₂ - s).re < 0 := by
          have : (c₂ - s).re = -(s - c₂).re := by simp
          linarith
        rw [logDeriv_mul s (inv_ne_zero (one_sub_prime_cpow_ne_zero hc1_neg q))
            (inv_ne_zero (one_sub_prime_cpow_ne_zero hc2_neg q))
            (differentiableAt_inv_one_sub_prime_cpow q hc1_neg)
            (differentiableAt_inv_one_sub_prime_cpow q hc2_neg),
          logDeriv_inv_one_sub_prime_cpow q hw₁, logDeriv_inv_one_sub_prime_cpow q hw₂]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.sum_add_distrib,
        LSeries_sum_smallPrimes_primePowVonMangoldt P₀ hw₁,
        LSeries_sum_smallPrimes_primePowVonMangoldt P₀ hw₂]
  have hd1 := hd_shift c₁ hw₁
  have hd2 := hd_shift c₂ hw₂
  have hz0_ne := hz_ne s hs
  have hz1_inv_ne : (riemannZeta (s - c₁))⁻¹ ≠ 0 := inv_ne_zero (hz_ne _ hw₁)
  have hz2_inv_ne : (riemannZeta (s - c₂))⁻¹ ≠ 0 := inv_ne_zero (hz_ne _ hw₂)
  rw [hld_eq,
    logDeriv_mul s (mul_ne_zero (mul_ne_zero hz0_ne hz1_inv_ne) hz2_inv_ne) hfin_ne
      (((hz_d s hs).mul hd1.1).mul hd2.1) hfin_d_and_ld.1,
    logDeriv_mul s (mul_ne_zero hz0_ne hz1_inv_ne) hz2_inv_ne ((hz_d s hs).mul hd1.1) hd2.1,
    logDeriv_mul s hz0_ne hz1_inv_ne (hz_d s hs) hd1.1,
    hd1.2, hd2.2, hlogζ s hs, hlogζ _ hw₁, hlogζ _ hw₂, hfin_d_and_ld.2]
  have hS0 : LSeriesSummable (fun n => (Λ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hS1 : LSeriesSummable (fun n => (Λ n : ℂ)) (s - c₁) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hw₁
  have hS2 : LSeriesSummable (fun n => (Λ n : ℂ)) (s - c₂) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hw₂
  have hSm1 : LSeriesSummable (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₁) := by
    refine LSeriesSummable.of_nonneg_of_le (f := fun n => Λ n) (fun _ => by positivity) (fun n => ?_)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hw₁)
    split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  have hSm2 : LSeriesSummable (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₂) := by
    refine LSeriesSummable.of_nonneg_of_le (f := fun n => Λ n) (fun _ => by positivity) (fun n => ?_)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hw₂)
    split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  have hdiff1 : LSeries (fun n => (Λ n : ℂ)) (s - c₁) -
      LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₁) =
      ∑' n : ℕ, (LSeries.term (fun n => (Λ n : ℂ)) (s - c₁) n -
        LSeries.term (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₁) n) :=
    (Summable.tsum_sub hS1 hSm1).symm
  have hdiff2 : LSeries (fun n => (Λ n : ℂ)) (s - c₂) -
      LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₂) =
      ∑' n : ℕ, (LSeries.term (fun n => (Λ n : ℂ)) (s - c₂) n -
        LSeries.term (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₂) n) :=
    (Summable.tsum_sub hS2 hSm2).symm
  have halg : -(-LSeries (fun n => (Λ n : ℂ)) s + --LSeries (fun n => (Λ n : ℂ)) (s - c₁) +
      --LSeries (fun n => (Λ n : ℂ)) (s - c₂) +
      -(LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₁) +
        LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₂))) =
      LSeries (fun n => (Λ n : ℂ)) s -
        (LSeries (fun n => (Λ n : ℂ)) (s - c₁) -
          LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₁)) -
        (LSeries (fun n => (Λ n : ℂ)) (s - c₂) -
          LSeries (fun n => if n.minFac ≤ P₀ then (Λ n : ℂ) else 0) (s - c₂)) := by ring
  rw [halg, hdiff1, hdiff2]
  unfold LSeries
  rw [← Summable.tsum_sub hS0 (hS1.sub hSm1), ← Summable.tsum_sub (hS0.sub (hS1.sub hSm1)) (hS2.sub hSm2)]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · simp only [LSeries.term_of_ne_zero hn0]
    change _ = (if n.minFac ≤ P₀ then (Λ n : ℝ) else
      Λ n * (1 - 2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n)) : ℂ) / (n : ℂ) ^ s
    split_ifs with hmin
    · ring
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnc0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hns0 : (n : ℂ) ^ s ≠ 0 := by
        rw [cpow_def_of_ne_zero hnc0]; exact Complex.exp_ne_zero _
      have hsub1 : ((n : ℂ) ^ (s - c₁))⁻¹ = (n : ℂ) ^ c₁ / (n : ℂ) ^ s := by
        rw [sub_eq_add_neg, cpow_add _ _ hnc0, cpow_neg, mul_inv, inv_inv, mul_comm, div_eq_mul_inv]
      have hsub2 : ((n : ℂ) ^ (s - c₂))⁻¹ = (n : ℂ) ^ c₂ / (n : ℂ) ^ s := by
        rw [sub_eq_add_neg, cpow_add _ _ hnc0, cpow_neg, mul_inv, inv_inv, mul_comm, div_eq_mul_inv]
      have hsum_c : (n : ℂ) ^ c₁ + (n : ℂ) ^ c₂ =
          ((2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n) : ℝ) : ℂ) :=
        prime_cpow_add_conj n hn_pos β γ₀
      rw [zero_div, sub_zero, sub_zero, div_eq_mul_inv (Λ n : ℂ) ((n : ℂ) ^ (s - c₁)),
        div_eq_mul_inv (Λ n : ℂ) ((n : ℂ) ^ (s - c₂)), hsub1, hsub2, ofReal_mul, ofReal_sub,
        ofReal_one, ← hsum_c]
      field_simp [hns0]
      ring

/-! ## 5. Meromorphicity, holomorphy, simple pole at `s = 1`, zero set, and vertical bounds -/

theorem meromorphicAt_riemannZeta_all (z : ℂ) : MeromorphicAt riemannZeta z := by
  have hev : (fun w : ℂ => zetaResidueUnit w * (w - 1)⁻¹) =ᶠ[𝓝[≠] z] riemannZeta := by
    by_cases hz : z = 1
    · subst hz
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w ≠ 1 := hw
      simp only [zetaResidueUnit, Function.update_of_ne hw1]
      rw [mul_right_comm, mul_inv_cancel₀ (sub_ne_zero.mpr hw1), one_mul]
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (isOpen_compl_singleton.mem_nhds hz)] with w hw
      have hw1 : w ≠ 1 := hw
      simp only [zetaResidueUnit, Function.update_of_ne hw1]
      rw [mul_right_comm, mul_inv_cancel₀ (sub_ne_zero.mpr hw1), one_mul]
  exact ((analyticAt_zetaResidueUnit z).meromorphicAt.mul
    (analyticAt_id.sub analyticAt_const).meromorphicAt.inv).congr hev

theorem meromorphicOn_posTruncatedZeta (P₀ : ℕ) (ρ₀ : ℂ) :
    MeromorphicOn (posTruncatedZeta P₀ ρ₀) univ := by
  intro z _
  have hinv : ∀ w₀ : ℂ, MeromorphicAt (fun w => invZeta (w + 1 - w₀)) z := by
    intro w₀
    have hfn : (fun w => invZeta (w + 1 - w₀)) =
        fun w => (w - w₀) * (zetaResidueUnit (w + 1 - w₀))⁻¹ := by
      funext w; unfold invZeta; congr 1; ring
    rw [hfn]
    have hcomp : AnalyticAt ℂ (fun w => zetaResidueUnit (w + 1 - w₀)) z :=
      (analyticAt_zetaResidueUnit (z + 1 - w₀)).comp
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const)
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul hcomp.meromorphicAt.inv
  have hfin : MeromorphicAt (posFiniteFactor P₀ ρ₀) z := by
    have hpf : posFiniteFactor P₀ ρ₀ = ∏ q ∈ smallPrimes P₀, fun w =>
        (1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - w))⁻¹ *
          (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - w))⁻¹ := by
      funext w; simp [posFiniteFactor]
    rw [hpf]
    refine Finset.prod_induction _ (fun g => MeromorphicAt g z)
      (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) (.const 1 z) fun q _ => ?_
    have hq_an : ∀ c : ℂ, AnalyticAt ℂ (fun w => 1 - ((q : ℕ) : ℂ) ^ (c - w)) z := by
      intro c
      have hp0 : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
      have heq : (fun w => 1 - ((q : ℕ) : ℂ) ^ (c - w)) =
          fun w => 1 - Complex.exp (Complex.log ((q : ℕ) : ℂ) * (c - w)) := by
        funext w; rw [cpow_def_of_ne_zero hp0]
      rw [heq]
      exact analyticAt_const.sub
        (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp
    exact (hq_an (ρ₀ - 1)).meromorphicAt.inv.mul (hq_an (conj ρ₀ - 1)).meromorphicAt.inv
  exact (meromorphicAt_riemannZeta_all z).mul (((hinv ρ₀).mul (hinv (conj ρ₀))).mul hfin)

private theorem zetaResidueUnit_ne_zero_of_frontier {Θ₀ : ℝ}
    (hzf : ∀ z : ℂ, Θ₀ < z.re → riemannZeta z ≠ 0) {w : ℂ} (hw : Θ₀ < w.re) :
    zetaResidueUnit w ≠ 0 := by
  rcases eq_or_ne w 1 with rfl | hne
  · rw [zetaResidueUnit_one]; norm_num
  · exact (zetaResidueUnit_ne_zero_iff hne).mpr (hzf w hw)

theorem differentiableAt_posCofactor_of_re_gt {Θ₀ β : ℝ} (γ₀ : ℝ)
    (hΘ : 1 / 2 ≤ Θ₀) (hzf : ∀ z : ℂ, Θ₀ < z.re → riemannZeta z ≠ 0)
    (P₀ : ℕ) {s : ℂ} (hs : Θ₀ + β - 1 < s.re) :
    DifferentiableAt ℂ (posCofactor P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) s := by
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  have hw₁ : Θ₀ < (s + 1 - ρ₀).re := by
    have : (s + 1 - ρ₀).re = s.re + 1 - β := by simp [ρ₀]
    linarith
  have hw₂ : Θ₀ < (s + 1 - conj ρ₀).re := by
    have : (s + 1 - conj ρ₀).re = s.re + 1 - β := by simp [ρ₀]
    linarith
  have hd₁ : DifferentiableAt ℂ (fun z => invZeta (z + 1 - ρ₀)) s :=
    (differentiableAt_invZeta (zetaResidueUnit_ne_zero_of_frontier hzf hw₁)).comp s
      ((differentiableAt_id.add_const 1).sub_const ρ₀)
  have hd₂ : DifferentiableAt ℂ (fun z => invZeta (z + 1 - conj ρ₀)) s :=
    (differentiableAt_invZeta (zetaResidueUnit_ne_zero_of_frontier hzf hw₂)).comp s
      ((differentiableAt_id.add_const 1).sub_const (conj ρ₀))
  have hdf : DifferentiableAt ℂ (posFiniteFactor P₀ ρ₀) s := by
    have hpf : posFiniteFactor P₀ ρ₀ = ∏ q ∈ smallPrimes P₀, fun z =>
        (1 - ((q : ℕ) : ℂ) ^ ((ρ₀ - 1) - z))⁻¹ *
          (1 - ((q : ℕ) : ℂ) ^ ((conj ρ₀ - 1) - z))⁻¹ := rfl
    rw [hpf]
    refine Finset.prod_induction _ (fun g => DifferentiableAt ℂ g s)
      (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) (differentiableAt_const 1) fun q _ => ?_
    refine (differentiableAt_inv_one_sub_prime_cpow q ?_).mul
      (differentiableAt_inv_one_sub_prime_cpow q ?_)
    · have : ((ρ₀ - 1) - s).re = β - 1 - s.re := by simp [ρ₀]
      linarith
    · have : ((conj ρ₀ - 1) - s).re = β - 1 - s.re := by simp [ρ₀]
      linarith
  exact (hd₁.mul hd₂).mul hdf

/-- **Extended right-half-plane holomorphy:** `posTruncatedZeta` is holomorphic on
`{Re s > Θ₀ + β − 1} \ {1}`, strictly crossing `Θ₀` to the left since `β < 1`. -/
theorem differentiableOn_posTruncatedZeta {Θ₀ β : ℝ} (γ₀ : ℝ)
    (hΘ : 1 / 2 ≤ Θ₀) (hzf : ∀ z : ℂ, Θ₀ < z.re → riemannZeta z ≠ 0) (P₀ : ℕ) :
    DifferentiableOn ℂ (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I))
      {s : ℂ | Θ₀ + β - 1 < s.re ∧ s ≠ 1} := by
  intro s ⟨hsre, hs1⟩
  exact ((differentiableAt_riemannZeta hs1).mul
    (differentiableAt_posCofactor_of_re_gt γ₀ hΘ hzf P₀ hsre)).differentiableWithinAt

/-- **Simple pole at `s = 1` with positive real residue.** -/
theorem exists_pos_residue_posTruncatedZeta_one (P₀ : ℕ) {β γ₀ : ℝ}
    (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      Tendsto (fun s : ℂ => (s - 1) * posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s)
        (𝓝[≠] 1) (𝓝 (R : ℂ)) := by
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  set w₀ : ℂ := 2 - ρ₀
  have hw₀_re : 1 < w₀.re := by
    have : w₀.re = 2 - β := by simp [w₀, ρ₀]
    linarith
  have hw₀_ne1 : w₀ ≠ 1 := fun h => by
    have := congrArg Complex.im h
    simp [w₀, ρ₀] at this
    exact hγ₀ this
  have hw₀'_ne1 : 2 - conj ρ₀ ≠ 1 := fun h => by
    have := congrArg Complex.im h
    simp [ρ₀] at this
    exact hγ₀ this
  have hζ_ne : riemannZeta w₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw₀_re
  set R : ℝ := ‖(riemannZeta w₀)⁻¹‖ ^ 2 *
    ∏ q ∈ smallPrimes P₀, (‖1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 2)‖ ^ 2)⁻¹
  have hR_pos : 0 < R := by
    dsimp [R]
    refine mul_pos (pow_pos (norm_pos_iff.mpr (inv_ne_zero hζ_ne)) 2)
      (Finset.prod_pos fun q _ => inv_pos.mpr (pow_pos (norm_pos_iff.mpr ?_) 2))
    refine one_sub_prime_cpow_ne_zero ?_ q
    have : (ρ₀ - 2).re = β - 2 := by simp [ρ₀]
    linarith
  have hcof1 : posCofactor P₀ ρ₀ 1 = (R : ℂ) := by
    unfold posCofactor posFiniteFactor
    have he1 : (1 : ℂ) + 1 - ρ₀ = w₀ := by dsimp [w₀]; ring
    have he2 : (1 : ℂ) + 1 - conj ρ₀ = conj w₀ := by dsimp [w₀]; simp
    have hw₀c_ne1 : conj w₀ ≠ 1 := by rwa [← he2]
    rw [he1, he2, invZeta_eq_inv hw₀_ne1, invZeta_eq_inv hw₀c_ne1, _root_.riemannZeta_conj,
      ← map_inv₀, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hprod : (∏ q ∈ smallPrimes P₀,
        (1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - 1))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - 1))⁻¹) =
        ((∏ q ∈ smallPrimes P₀, (‖1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 2)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [ofReal_prod]
      refine Finset.prod_congr rfl fun q _ => ?_
      have hp1 : ρ₀ - 1 - 1 = ρ₀ - 2 := by ring
      have hp2 : conj ρ₀ - 1 - 1 = conj (ρ₀ - 2) := by simp; ring
      rw [hp1, hp2, prime_cpow_conj_eq (q : ℕ) q.prop.pos (ρ₀ - 2), ← map_one (conj),
        ← map_sub, ← map_inv₀, Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_inv,
        ofReal_pow, norm_inv, inv_pow]
    rw [hprod]
    push_cast
    rfl
  have hcont : ContinuousAt (posCofactor P₀ ρ₀) 1 := by
    refine (differentiableAt_posCofactor_of_re_gt (Θ₀ := 1) γ₀ (by norm_num)
      (fun z hz => riemannZeta_ne_zero_of_one_lt_re hz) P₀ ?_).continuousAt
    simp; linarith
  refine ⟨R, hR_pos, ?_⟩
  have hlim : Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s) * posCofactor P₀ ρ₀ s)
      (𝓝[≠] 1) (𝓝 ((1 : ℂ) * posCofactor P₀ ρ₀ 1)) :=
    riemannZeta_residue_one.mul hcont.continuousWithinAt.tendsto
  rw [one_mul, hcof1] at hlim
  exact hlim.congr fun s => by unfold posTruncatedZeta; ring

/-- **Exact off-line zero set in `{Re s > Θ₀} \ {1}`:** `posTruncatedZeta` vanishes at and only at
the conjugate pair `{ρ₀, conj ρ₀}`. -/
theorem zeroSet_posTruncatedZeta_eq_pair {Θ₀ β γ₀ : ℝ}
    (hΘ : 1 / 2 ≤ Θ₀) (hΘβ : Θ₀ < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0)
    (hzf : ∀ z : ℂ, Θ₀ < z.re → riemannZeta z ≠ 0) (P₀ : ℕ) :
    {s : ℂ | Θ₀ < s.re ∧ s ≠ 1 ∧
        posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s = 0} =
      {(β : ℂ) + (γ₀ : ℂ) * I, conj ((β : ℂ) + (γ₀ : ℂ) * I)} := by
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  ext s
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hsre, hs1, hF0⟩
    have hζ_ne : riemannZeta s ≠ 0 := hzf s hsre
    have hfin_ne : posFiniteFactor P₀ ρ₀ s ≠ 0 := by
      unfold posFiniteFactor
      refine Finset.prod_ne_zero_iff.mpr fun q _ => mul_ne_zero
        (inv_ne_zero (one_sub_prime_cpow_ne_zero ?_ q))
        (inv_ne_zero (one_sub_prime_cpow_ne_zero ?_ q))
      · have : (ρ₀ - 1 - s).re = β - 1 - s.re := by simp [ρ₀]
        linarith
      · have : (conj ρ₀ - 1 - s).re = β - 1 - s.re := by simp [ρ₀]
        linarith
    unfold posTruncatedZeta posCofactor at hF0
    have hinv_mul : invZeta (s + 1 - ρ₀) * invZeta (s + 1 - conj ρ₀) = 0 :=
      ((mul_eq_zero.mp hF0).resolve_left hζ_ne).resolve_right hfin_ne
    have hw₁ : Θ₀ < (s + 1 - ρ₀).re := by
      have : (s + 1 - ρ₀).re = s.re + 1 - β := by simp [ρ₀]
      linarith
    have hw₂ : Θ₀ < (s + 1 - conj ρ₀).re := by
      have : (s + 1 - conj ρ₀).re = s.re + 1 - β := by simp [ρ₀]
      linarith
    rcases mul_eq_zero.mp hinv_mul with hi1 | hi2
    · unfold invZeta at hi1
      have hru_ne := inv_ne_zero (zetaResidueUnit_ne_zero_of_frontier hzf hw₁)
      have hs1_eq := sub_eq_zero.mp ((mul_eq_zero.mp hi1).resolve_right hru_ne)
      left; linear_combination hs1_eq
    · unfold invZeta at hi2
      have hru_ne := inv_ne_zero (zetaResidueUnit_ne_zero_of_frontier hzf hw₂)
      have hs2_eq := sub_eq_zero.mp ((mul_eq_zero.mp hi2).resolve_right hru_ne)
      right; linear_combination hs2_eq
  · rintro (rfl | rfl)
    · refine ⟨by simp [ρ₀]; exact hΘβ, fun h => hγ₀ (by have := congrArg Complex.im h; simp [ρ₀] at this; exact this), ?_⟩
      unfold posTruncatedZeta posCofactor
      have : ρ₀ + 1 - ρ₀ = 1 := by ring
      rw [this, invZeta_one]
      ring
    · refine ⟨by simp [ρ₀]; exact hΘβ, fun h => hγ₀ (by have := congrArg Complex.im h; simp [ρ₀] at this; exact this), ?_⟩
      unfold posTruncatedZeta posCofactor
      have : conj ρ₀ + 1 - conj ρ₀ = 1 := by ring
      rw [this, invZeta_one]
      ring

theorem not_halfPlaneAbscissaLaw_posTruncatedZeta {Θ₀ β γ₀ : ℝ}
    (hΘ : 1 / 2 ≤ Θ₀) (hΘβ : Θ₀ < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0)
    (hzf : ∀ z : ℂ, Θ₀ < z.re → riemannZeta z ≠ 0) (P₀ : ℕ) :
    ¬ HalfPlaneAbscissaLaw (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) Θ₀ := by
  have hset := zeroSet_posTruncatedZeta_eq_pair hΘ hΘβ hβ1 hγ₀ hzf P₀
  refine not_halfPlaneAbscissaLaw_of_finite_nonempty ?_ ?_ <;> rw [hset]
  · exact (finite_singleton _).insert _
  · exact insert_nonempty _ _

/-- **Polynomial vertical bounds on `posTruncatedZeta` and `(posTruncatedZeta)⁻¹`** on every closed
vertical strip `[Θ₀ + δ, d]` strictly right of the zero-free frontier `Θ₀`. -/
theorem exists_poly_bounds_posTruncatedZeta {Θ₀ β γ₀ : ℝ}
    (hΘ : 1 / 2 ≤ Θ₀) (hΘ1 : Θ₀ < 1) (hΘβ : Θ₀ < β) (hβ1 : β < 1)
    (hzf : ∀ z : ℂ, Θ₀ < z.re → riemannZeta z ≠ 0) (P₀ : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (d : ℝ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ s : ℂ, Θ₀ + δ ≤ s.re → s.re ≤ d → |γ₀| + 6 ≤ |s.im| →
        ‖posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s‖ ≤ C * |s.im| ^ N ∧
          ‖(posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s)⁻¹‖ ≤ C * |s.im| ^ N := by
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  set M₀ : ℝ := |Θ₀ + δ| + |d| + 2 + |β|
  obtain ⟨Cζ, Nζ, hCζ0, hζ_bd⟩ := exists_bound_norm_riemannZeta_strip M₀
  obtain ⟨K₀, hK₀0, -, hinv₀⟩ := exists_invZeta_shift_data_of_zeroFree hΘ hΘ1.le hzf
    (δ := min δ (1 / 2)) (lt_min hδ (by norm_num)) (by linarith [min_le_right δ (1 / 2)])
    one_pos d
  obtain ⟨K₁, hK₁0, -, hinv₁⟩ := exists_invZeta_shift_data_of_zeroFree hΘ hΘ1.le hzf
    (δ := min (δ + 1 - β) (1 / 2)) (lt_min (by linarith) (by norm_num))
    (by linarith [min_le_right (δ + 1 - β) (1 / 2)]) one_pos (d + 1 - β)
  set η₀ : ℝ := 1 - (2 : ℝ) ^ (β - 1 - Θ₀)
  have hη₀ : 0 < η₀ := by
    dsimp [η₀]
    have hrlt : (2 : ℝ) ^ (β - 1 - Θ₀) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  set Bf : ℝ := (η₀⁻¹ * η₀⁻¹) ^ (smallPrimes P₀).card
  set Bg : ℝ := (4 : ℝ) ^ (smallPrimes P₀).card
  have hBf_pos : 0 < Bf := by dsimp [Bf]; positivity
  have hBg_pos : 0 < Bg := by dsimp [Bg]; positivity
  set C_up : ℝ := (Cζ + 1) * (4 * K₁ + 1) * (4 * K₁ + 1) * Bf
  set C_dn : ℝ := (2 * K₀ + 1) * ((Cζ + 1) * 2 ^ Nζ) * ((Cζ + 1) * 2 ^ Nζ) * Bg
  refine ⟨max C_up C_dn + 1, max (Nζ + 2) (2 * Nζ + 1), by positivity,
    fun s hs0 hs1 hsim => ?_⟩
  have ht1 : 1 ≤ |s.im| := by linarith [abs_nonneg γ₀]
  have ht2 : 2 ≤ |s.im| := by linarith [abs_nonneg γ₀]
  have hs_ne1 : s ≠ 1 := fun h => by rw [h] at ht1; simp at ht1; linarith
  have hs_decomp : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := (Complex.re_add_im s).symm
  have hsre_M₀ : |s.re| ≤ M₀ := by
    dsimp [M₀]
    rcases le_total 0 s.re with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self d, abs_nonneg (Θ₀ + δ), abs_nonneg β]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le (Θ₀ + δ), abs_nonneg d, abs_nonneg β]
  have hζ_s : ‖riemannZeta s‖ ≤ (Cζ + 1) * |s.im| ^ Nζ := by
    have hb := hζ_bd s.re s.im hsre_M₀ ht1
    rw [← hs_decomp] at hb
    calc ‖riemannZeta s‖ ≤ Cζ * |s.im| ^ Nζ := hb
      _ ≤ (Cζ + 1) * |s.im| ^ Nζ := by gcongr; linarith
  have hinv_ζ_s : ‖(riemannZeta s)⁻¹‖ ≤ (2 * K₀ + 1) * |s.im| := by
    have hmem : s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (Θ₀ + min δ (1 / 2)) d :=
      ⟨by linarith [min_le_left δ (1 / 2)], hs1⟩
    have hb := hinv₀ s hmem
    rw [invZeta_eq_inv hs_ne1, Real.rpow_one] at hb
    calc ‖(riemannZeta s)⁻¹‖ ≤ K₀ * (2 + |s.im|) := hb
      _ ≤ K₀ * (2 * |s.im|) := by gcongr; linarith
      _ = 2 * K₀ * |s.im| := by ring
      _ ≤ (2 * K₀ + 1) * |s.im| := by nlinarith [ht1]
  have hshift_bounds : ∀ εs : ℝ, |εs| = |γ₀| →
      let w := s + 1 - ((β : ℂ) + (εs : ℂ) * I)
      ‖invZeta w‖ ≤ (4 * K₁ + 1) * |s.im| ∧
        ‖(invZeta w)⁻¹‖ ≤ (Cζ + 1) * 2 ^ Nζ * |s.im| ^ Nζ := by
    intro εs hεs w
    have hw_re : w.re = s.re + 1 - β := by simp [w]
    have hw_im : w.im = s.im - εs := by simp [w]
    have hw_im_lo : 6 ≤ |w.im| := by
      have htri : |s.im| - |εs| ≤ |s.im - εs| := abs_sub_abs_le_abs_sub s.im εs
      rw [hw_im, hεs] at *
      linarith
    have hw_im_hi : |w.im| ≤ 2 * |s.im| := by
      have htri : |s.im - εs| ≤ |s.im| + |εs| := abs_sub s.im εs
      rw [hw_im]
      linarith
    have hw_ne1 : w ≠ 1 := fun h => by rw [h] at hw_im_lo; simp at hw_im_lo; linarith
    have hw_mem : w ∈ GaloisForLFunctions.HTGeometry.verticalStrip
        (Θ₀ + min (δ + 1 - β) (1 / 2)) (d + 1 - β) :=
      ⟨by rw [hw_re]; linarith [min_le_left (δ + 1 - β) (1 / 2)], by rw [hw_re]; linarith⟩
    have hb1 := hinv₁ w hw_mem
    rw [Real.rpow_one] at hb1
    have hup_w : ‖invZeta w‖ ≤ (4 * K₁ + 1) * |s.im| := by
      calc ‖invZeta w‖ ≤ K₁ * (2 + |w.im|) := hb1
        _ ≤ K₁ * (4 * |s.im|) := by gcongr; linarith
        _ = 4 * K₁ * |s.im| := by ring
        _ ≤ (4 * K₁ + 1) * |s.im| := by nlinarith [ht1]
    have hwre_M₀ : |w.re| ≤ M₀ := by
      rw [hw_re]; dsimp [M₀]
      rcases le_total 0 (s.re + 1 - β) with h | h
      · rw [abs_of_nonneg h]
        linarith [le_abs_self d, neg_abs_le β, abs_nonneg (Θ₀ + δ)]
      · rw [abs_of_nonpos h]
        linarith [neg_abs_le (Θ₀ + δ), le_abs_self β, abs_nonneg d]
    have hw_decomp : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * I := (Complex.re_add_im w).symm
    have hζ_w := hζ_bd w.re w.im hwre_M₀ (by linarith)
    rw [← hw_decomp] at hζ_w
    have hdn_w : ‖(invZeta w)⁻¹‖ ≤ (Cζ + 1) * 2 ^ Nζ * |s.im| ^ Nζ := by
      rw [invZeta_eq_inv hw_ne1, inv_inv]
      calc ‖riemannZeta w‖ ≤ Cζ * |w.im| ^ Nζ := hζ_w
        _ ≤ (Cζ + 1) * (2 * |s.im|) ^ Nζ := by
            refine mul_le_mul (by linarith) (pow_le_pow_left₀ (abs_nonneg _) hw_im_hi Nζ)
              (by positivity) (by positivity)
        _ = (Cζ + 1) * 2 ^ Nζ * |s.im| ^ Nζ := by rw [mul_pow]; ring
    exact ⟨hup_w, hdn_w⟩
  have hb_w1 := hshift_bounds γ₀ rfl
  have hb_w2 : ‖invZeta (s + 1 - conj ρ₀)‖ ≤ (4 * K₁ + 1) * |s.im| ∧
      ‖(invZeta (s + 1 - conj ρ₀))⁻¹‖ ≤ (Cζ + 1) * 2 ^ Nζ * |s.im| ^ Nζ := by
    have hconj_eq : conj ρ₀ = (β : ℂ) + ((-γ₀ : ℝ) : ℂ) * I := by simp [ρ₀, sub_eq_add_neg]
    rw [hconj_eq]
    exact hshift_bounds (-γ₀) (abs_neg γ₀)
  have hfin_bounds : ‖posFiniteFactor P₀ ρ₀ s‖ ≤ Bf ∧ ‖(posFiniteFactor P₀ ρ₀ s)⁻¹‖ ≤ Bg := by
    have hq_bd : ∀ q ∈ smallPrimes P₀, ∀ c : ℂ, c.re = β - 1 →
        η₀ ≤ ‖1 - ((q : ℕ) : ℂ) ^ (c - s)‖ ∧ ‖1 - ((q : ℕ) : ℂ) ^ (c - s)‖ ≤ 2 := by
      intro q _ c hcre
      have hp2 : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.two_le
      have hexp_re : (c - s).re = β - 1 - s.re := by simp [hcre]
      have hexp_le : (c - s).re ≤ β - 1 - Θ₀ := by linarith
      have hexp_neg : (c - s).re < 0 := by linarith
      have hnorm_q : ‖((q : ℕ) : ℂ) ^ (c - s)‖ ≤ (2 : ℝ) ^ (β - 1 - Θ₀) := by
        rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by linarith)]
        calc ((q : ℕ) : ℝ) ^ (c - s).re
            ≤ (2 : ℝ) ^ (c - s).re := rpow_neg_mono_antitone two_pos hp2 hexp_neg
          _ ≤ (2 : ℝ) ^ (β - 1 - Θ₀) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp_le
      have hlo : η₀ ≤ ‖1 - ((q : ℕ) : ℂ) ^ (c - s)‖ := by
        have htri := norm_sub_norm_le (1 : ℂ) (((q : ℕ) : ℂ) ^ (c - s))
        rw [norm_one] at htri
        dsimp [η₀]; linarith
      have hhi : ‖1 - ((q : ℕ) : ℂ) ^ (c - s)‖ ≤ 2 := by
        have htri := norm_sub_le (1 : ℂ) (((q : ℕ) : ℂ) ^ (c - s))
        rw [norm_one] at htri
        have hr1 : (2 : ℝ) ^ (β - 1 - Θ₀) ≤ 1 :=
          (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)).le
        linarith
      exact ⟨hlo, hhi⟩
    unfold posFiniteFactor
    rw [Finset.prod_inv_distrib]
    constructor
    · calc ‖∏ q ∈ smallPrimes P₀,
            (1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))⁻¹‖
          ≤ ∏ q ∈ smallPrimes P₀,
            ‖(1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))⁻¹‖ :=
            norm_prod_le _ _
        _ ≤ ∏ _q ∈ smallPrimes P₀, (η₀⁻¹ * η₀⁻¹) := by
            refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun q hq => ?_
            rw [norm_mul, norm_inv, norm_inv]
            exact mul_le_mul
              (inv_anti₀ hη₀ (hq_bd q hq (ρ₀ - 1) (by simp [ρ₀])).1)
              (inv_anti₀ hη₀ (hq_bd q hq (conj ρ₀ - 1) (by simp [ρ₀])).1)
              (by positivity) (by positivity)
        _ = Bf := Finset.prod_const _
    · calc ‖∏ q ∈ smallPrimes P₀,
            ((1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))⁻¹)⁻¹‖
          ≤ ∏ q ∈ smallPrimes P₀,
            ‖((1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s))⁻¹ * (1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s))⁻¹)⁻¹‖ :=
            norm_prod_le _ _
        _ ≤ ∏ _q ∈ smallPrimes P₀, (4 : ℝ) := by
            refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun q hq => ?_
            rw [mul_inv, inv_inv, inv_inv, norm_mul]
            have h1 := (hq_bd q hq (ρ₀ - 1) (by simp [ρ₀])).2
            have h2 := (hq_bd q hq (conj ρ₀ - 1) (by simp [ρ₀])).2
            calc ‖1 - ((q : ℕ) : ℂ) ^ (ρ₀ - 1 - s)‖ * ‖1 - ((q : ℕ) : ℂ) ^ (conj ρ₀ - 1 - s)‖
                ≤ 2 * 2 := mul_le_mul h1 h2 (norm_nonneg _) two_pos.le
              _ = 4 := by norm_num
        _ = Bg := Finset.prod_const _
  set N := max (Nζ + 2) (2 * Nζ + 1)
  constructor
  · unfold posTruncatedZeta posCofactor
    rw [norm_mul, norm_mul, norm_mul]
    have hmul : ‖riemannZeta s‖ * (‖invZeta (s + 1 - ρ₀)‖ * ‖invZeta (s + 1 - conj ρ₀)‖ *
        ‖posFiniteFactor P₀ ρ₀ s‖) ≤ C_up * |s.im| ^ (Nζ + 2) := by
      calc ‖riemannZeta s‖ * (‖invZeta (s + 1 - ρ₀)‖ * ‖invZeta (s + 1 - conj ρ₀)‖ *
              ‖posFiniteFactor P₀ ρ₀ s‖)
          ≤ ((Cζ + 1) * |s.im| ^ Nζ) * (((4 * K₁ + 1) * |s.im|) * ((4 * K₁ + 1) * |s.im|) * Bf) := by
            gcongr
            exact hζ_s
            exact hb_w1.1
            exact hb_w2.1
            exact hfin_bounds.1
        _ = C_up * |s.im| ^ (Nζ + 2) := by dsimp [C_up]; rw [pow_add, pow_two]; ring
    exact hmul.trans (mul_le_mul (by linarith [le_max_left C_up C_dn])
      (pow_le_pow_right₀ ht1 (le_max_left _ _)) (by positivity) (by positivity))
  · unfold posTruncatedZeta posCofactor
    rw [mul_inv, mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]
    have hmul : ‖(riemannZeta s)⁻¹‖ * (‖(invZeta (s + 1 - ρ₀))⁻¹‖ *
        ‖(invZeta (s + 1 - conj ρ₀))⁻¹‖ * ‖(posFiniteFactor P₀ ρ₀ s)⁻¹‖) ≤
        C_dn * |s.im| ^ (2 * Nζ + 1) := by
      calc ‖(riemannZeta s)⁻¹‖ * (‖(invZeta (s + 1 - ρ₀))⁻¹‖ *
              ‖(invZeta (s + 1 - conj ρ₀))⁻¹‖ * ‖(posFiniteFactor P₀ ρ₀ s)⁻¹‖)
          ≤ ((2 * K₀ + 1) * |s.im|) * (((Cζ + 1) * 2 ^ Nζ * |s.im| ^ Nζ) *
              ((Cζ + 1) * 2 ^ Nζ * |s.im| ^ Nζ) * Bg) := by
            gcongr
            exact hinv_ζ_s
            exact hb_w1.2
            exact hb_w2.2
            exact hfin_bounds.2
        _ = C_dn * |s.im| ^ (2 * Nζ + 1) := by
            dsimp [C_dn]; rw [two_mul, pow_add, pow_add, pow_one]; ring
    exact hmul.trans (mul_le_mul (by linarith [le_max_right C_up C_dn])
      (pow_le_pow_right₀ ht1 (le_max_right _ _)) (by positivity) (by positivity))

/-! ## 6. Left-strip pole obstruction and infinite critical-line poles under `RH` -/

private theorem eventually_zetaResidueUnit_ne_zero (w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, zetaResidueUnit z ≠ 0 := by
  have han : AnalyticOnNhd ℂ zetaResidueUnit univ := fun z _ => analyticAt_zetaResidueUnit z
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hfreq : ∃ᶠ z in 𝓝[≠] w, zetaResidueUnit z = (fun _ : ℂ => (0 : ℂ)) z := by
    simpa using hnot
  have heq := han.eq_of_frequently_eq (fun _ _ => analyticAt_const) hfreq
  have h1 := congrFun heq 1
  rw [zetaResidueUnit_one] at h1
  norm_num at h1

private theorem tendsto_norm_invZeta_atTop_of_zeta_zero {w : ℂ} (hw1 : w ≠ 1)
    (hζ0 : riemannZeta w = 0) :
    Tendsto (fun z => ‖invZeta z‖) (𝓝[≠] w) atTop := by
  have hru0 : zetaResidueUnit w = 0 := by
    simp [zetaResidueUnit, Function.update_of_ne hw1, hζ0]
  have hru_gt : Tendsto (fun z => ‖zetaResidueUnit z‖) (𝓝[≠] w) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc := (analyticAt_zetaResidueUnit w).continuousAt.continuousWithinAt (s := {w}ᶜ).tendsto.norm
      rwa [hru0, norm_zero] at hc
    · filter_upwards [eventually_zetaResidueUnit_ne_zero w] with z hz
      exact norm_pos_iff.mpr hz
  have hinv_top : Tendsto (fun z => ‖zetaResidueUnit z‖⁻¹) (𝓝[≠] w) atTop :=
    tendsto_inv_nhdsGT_zero.comp hru_gt
  have hsub_lim : Tendsto (fun z : ℂ => ‖z - 1‖) (𝓝[≠] w) (𝓝 ‖w - 1‖) :=
    ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt).tendsto.norm
  have hw_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  have hmul := Filter.Tendsto.pos_mul_atTop hw_pos hsub_lim hinv_top
  refine hmul.congr fun z => ?_
  unfold invZeta
  rw [norm_mul, norm_inv]

private theorem exists_eventually_lower_bound_norm_invZeta {w : ℂ} (hw1 : w ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝[≠] w, c ≤ ‖invZeta z‖ := by
  rcases eq_or_ne (riemannZeta w) 0 with h0 | hne
  · exact ⟨1, one_pos, (tendsto_norm_invZeta_atTop_of_zeta_zero hw1 h0).eventually
      (eventually_ge_atTop 1)⟩
  · have hc : ContinuousAt (fun z => ‖invZeta z‖) w :=
      (differentiableAt_invZeta_of_zeta_ne_zero hw1 hne).continuousAt.norm
    have hpos : 0 < ‖invZeta w‖ := by
      rw [invZeta_eq_inv hw1]
      exact norm_pos_iff.mpr (inv_ne_zero hne)
    refine ⟨‖invZeta w‖ / 2, by positivity, eventually_nhdsWithin_of_eventually_nhds ?_⟩
    exact hc.eventually (ge_mem_nhds (by linarith))

private theorem tendsto_shift_nhdsNE (s₀ d : ℂ) :
    Tendsto (fun s : ℂ => s + d) (𝓝[≠] s₀) (𝓝[≠] (s₀ + d)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_id.add continuous_const).continuousAt).continuousWithinAt.tendsto
  · filter_upwards [self_mem_nhdsWithin] with s hs
    intro h
    exact hs (add_right_cancel h)

/-- Core pole criterion: whenever `s_* ≠ 1`, `ζ(s_*) ≠ 0`, `(ρ₀ − 1 − s_*).re < 0`,
`s_* + 1 − ρ₀ ≠ 1`, `s_* + 1 − conj ρ₀ ≠ 1`, and `ζ(s_* + 1 − ρ₀) = 0`, `posTruncatedZeta P₀ ρ₀`
blows up in norm (`→ +∞`) on the punctured neighborhood `𝓝[≠] s_*` and is not analytic at `s_*`. -/
theorem tendsto_norm_posTruncatedZeta_atTop_of_shifted_zero (P₀ : ℕ) {ρ₀ s_* : ℂ}
    (hs1 : s_* ≠ 1) (hζ_ne : riemannZeta s_* ≠ 0)
    (hfin_re : (ρ₀ - 1 - s_*).re < 0) (hfin_re_conj : (conj ρ₀ - 1 - s_*).re < 0)
    (hw1_ne1 : s_* + 1 - ρ₀ ≠ 1) (hw2_ne1 : s_* + 1 - conj ρ₀ ≠ 1)
    (hw1_zero : riemannZeta (s_* + 1 - ρ₀) = 0) :
    Tendsto (fun s => ‖posTruncatedZeta P₀ ρ₀ s‖) (𝓝[≠] s_*) atTop ∧
      ¬ AnalyticAt ℂ (posTruncatedZeta P₀ ρ₀) s_* := by
  have hshift1 : Tendsto (fun s => s + (1 - ρ₀)) (𝓝[≠] s_*) (𝓝[≠] (s_* + (1 - ρ₀))) :=
    tendsto_shift_nhdsNE s_* (1 - ρ₀)
  have hshift2 : Tendsto (fun s => s + (1 - conj ρ₀)) (𝓝[≠] s_*) (𝓝[≠] (s_* + (1 - conj ρ₀))) :=
    tendsto_shift_nhdsNE s_* (1 - conj ρ₀)
  have htop1 : Tendsto (fun s => ‖invZeta (s + 1 - ρ₀)‖) (𝓝[≠] s_*) atTop := by
    have ht := (tendsto_norm_invZeta_atTop_of_zeta_zero
      (by simpa [add_sub_assoc] using hw1_ne1)
      (by simpa [add_sub_assoc] using hw1_zero)).comp hshift1
    exact ht.congr fun s => by simp [add_sub_assoc]
  obtain ⟨c₂, hc₂_pos, hc₂_ev⟩ := exists_eventually_lower_bound_norm_invZeta
    (by simpa [add_sub_assoc] using hw2_ne1)
  have hev2 : ∀ᶠ s in 𝓝[≠] s_*, c₂ ≤ ‖invZeta (s + 1 - conj ρ₀)‖ := by
    filter_upwards [hshift2.eventually hc₂_ev] with s hs
    simpa [add_sub_assoc] using hs
  have hζ_pos : 0 < ‖riemannZeta s_*‖ := norm_pos_iff.mpr hζ_ne
  have hev_ζ : ∀ᶠ s in 𝓝[≠] s_*, ‖riemannZeta s_*‖ / 2 ≤ ‖riemannZeta s‖ :=
    eventually_nhdsWithin_of_eventually_nhds
      ((differentiableAt_riemannZeta hs1).continuousAt.norm.eventually (ge_mem_nhds (by linarith)))
  have hfin_ne : posFiniteFactor P₀ ρ₀ s_* ≠ 0 := by
    unfold posFiniteFactor
    exact Finset.prod_ne_zero_iff.mpr fun q _ => mul_ne_zero
      (inv_ne_zero (one_sub_prime_cpow_ne_zero hfin_re q))
      (inv_ne_zero (one_sub_prime_cpow_ne_zero hfin_re_conj q))
  have hfin_cont : ContinuousAt (posFiniteFactor P₀ ρ₀) s_* := by
    have hpf : posFiniteFactor P₀ ρ₀ = ∏ q ∈ smallPrimes P₀, fun z =>
        (1 - ((q : ℕ) : ℂ) ^ ((ρ₀ - 1) - z))⁻¹ *
          (1 - ((q : ℕ) : ℂ) ^ ((conj ρ₀ - 1) - z))⁻¹ := rfl
    rw [hpf]
    exact (Finset.prod_induction _ (fun g => DifferentiableAt ℂ g s_*)
      (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) (differentiableAt_const 1) fun q _ =>
        (differentiableAt_inv_one_sub_prime_cpow q hfin_re).mul
          (differentiableAt_inv_one_sub_prime_cpow q hfin_re_conj)).continuousAt
  have hfin_pos : 0 < ‖posFiniteFactor P₀ ρ₀ s_*‖ := norm_pos_iff.mpr hfin_ne
  have hev_fin : ∀ᶠ s in 𝓝[≠] s_*, ‖posFiniteFactor P₀ ρ₀ s_*‖ / 2 ≤ ‖posFiniteFactor P₀ ρ₀ s‖ :=
    eventually_nhdsWithin_of_eventually_nhds
      (hfin_cont.norm.eventually (ge_mem_nhds (by linarith)))
  set κ : ℝ := (‖riemannZeta s_*‖ / 2) * c₂ * (‖posFiniteFactor P₀ ρ₀ s_*‖ / 2)
  have hκ_pos : 0 < κ := by dsimp [κ]; positivity
  have hκ_top : Tendsto (fun s => κ * ‖invZeta (s + 1 - ρ₀)‖) (𝓝[≠] s_*) atTop :=
    Filter.Tendsto.const_mul_atTop hκ_pos htop1
  have htop : Tendsto (fun s => ‖posTruncatedZeta P₀ ρ₀ s‖) (𝓝[≠] s_*) atTop := by
    refine tendsto_atTop_mono' _ ?_ hκ_top
    filter_upwards [hev_ζ, hev2, hev_fin] with s hsζ hs2 hsf
    unfold posTruncatedZeta posCofactor
    rw [norm_mul, norm_mul, norm_mul]
    calc κ * ‖invZeta (s + 1 - ρ₀)‖
        = (‖riemannZeta s_*‖ / 2) * (‖invZeta (s + 1 - ρ₀)‖ * c₂ *
            (‖posFiniteFactor P₀ ρ₀ s_*‖ / 2)) := by dsimp [κ]; ring
      _ ≤ ‖riemannZeta s‖ * (‖invZeta (s + 1 - ρ₀)‖ * ‖invZeta (s + 1 - conj ρ₀)‖ *
            ‖posFiniteFactor P₀ ρ₀ s‖) := by
          refine mul_le_mul hsζ ?_ (by positivity) (norm_nonneg _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hs2 (norm_nonneg _)) hsf
            (by positivity) (by positivity)
  refine ⟨htop, fun hana => ?_⟩
  exact not_tendsto_atTop_of_tendsto_nhds hana.continuousAt.continuousWithinAt.tendsto.norm htop

/-- **Left-strip pole obstruction (`Θ < 1`):** when `Θ = zetaZeroAbscissa < 1`, for every
`β ∈ (Θ, 1)` and `γ₀ ≠ 0`, `posTruncatedZeta P₀ (β + i γ₀)` has a genuine pole (`‖F(s)‖ → +∞`)
strictly inside the left critical strip `0 < Re s < 1 − Θ ≤ 1/2`. -/
theorem exists_left_strip_pole_posTruncatedZeta (hΘ1 : zetaZeroAbscissa < 1)
    {β γ₀ : ℝ} (hΘβ : zetaZeroAbscissa < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0) (P₀ : ℕ) :
    ∃ s_* : ℂ, 0 < s_*.re ∧ s_*.re < 1 - zetaZeroAbscissa ∧
      Tendsto (fun s => ‖posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s‖) (𝓝[≠] s_*) atTop ∧
      ¬ AnalyticAt ℂ (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) s_* := by
  have hΘ_half : 1 / 2 ≤ zetaZeroAbscissa := half_le_zetaZeroAbscissa
  obtain ⟨ρ_*, hζ_ρ, hρ_lt1, hρ_gt⟩ :=
    exists_zetaZero_mem_openStrip_lt_re (b := zetaZeroAbscissa - (1 - β) / 2) (by linarith)
  have hρ_pos : 0 < ρ_*.re := by linarith
  have hρ_leΘ : ρ_*.re ≤ zetaZeroAbscissa := re_le_zetaZeroAbscissa hζ_ρ
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  set w_* : ℂ := 1 - ρ_*
  set s_* : ℂ := ρ₀ - ρ_*
  have hs_re_eq : s_*.re = β - ρ_*.re := by simp [s_*, ρ₀]
  have hs_pos : 0 < s_*.re := by linarith
  have hs_lt_left : s_*.re < 1 - zetaZeroAbscissa := by linarith
  have hs_lt1 : s_*.re < 1 := by linarith
  have hs_ne1 : s_* ≠ 1 := fun h => by rw [h] at hs_lt1; simp at hs_lt1
  have hζ_s_ne : riemannZeta s_* ≠ 0 := by
    intro h0
    have hrefl := riemannZeta_one_sub_eq_zero_of_mem_openStrip h0 hs_pos hs_lt1
    have hre1 : (1 - s_*).re > zetaZeroAbscissa := by simp; linarith
    exact riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hre1 hrefl
  have hfin1 : (ρ₀ - 1 - s_*).re < 0 := by
    have : (ρ₀ - 1 - s_*).re = ρ_*.re - 1 := by dsimp [s_*]; simp; ring
    linarith
  have hfin2 : (conj ρ₀ - 1 - s_*).re < 0 := by
    have : (conj ρ₀ - 1 - s_*).re = ρ_*.re - 1 := by dsimp [s_*, ρ₀]; simp; ring
    linarith
  have hw1_eq : s_* + 1 - ρ₀ = 1 - ρ_* := by dsimp [s_*]; ring
  have hw1_ne1 : s_* + 1 - ρ₀ ≠ 1 := by
    rw [hw1_eq]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw2_ne1 : s_* + 1 - conj ρ₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    have hre : (s_* + 1 - conj ρ₀).re = 1 - ρ_*.re := by dsimp [s_*, ρ₀]; simp; ring
    rw [hre] at this
    simp at this
    linarith
  have hw1_zero : riemannZeta (s_* + 1 - ρ₀) = 0 := by
    rw [hw1_eq]
    exact riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ_ρ hρ_pos hρ_lt1
  obtain ⟨htop, hnot_an⟩ := tendsto_norm_posTruncatedZeta_atTop_of_shifted_zero P₀
    hs_ne1 hζ_s_ne hfin1 hfin2 hw1_ne1 hw2_ne1 hw1_zero
  exact ⟨s_*, hs_pos, hs_lt_left, htop, hnot_an⟩

/-- **Under `RiemannHypothesis`, infinitely many left-strip poles on `Re s = β − 1/2`:** for every
height `T`, Hardy's critical-line zeros produce a genuine pole of `posTruncatedZeta` on
`Re s = β − 1/2 ∈ (0, 1/2)` with `|Im s| > T`. -/
theorem exists_left_strip_pole_above_of_riemannHypothesis (hRH : RiemannHypothesis)
    {β γ₀ : ℝ} (hβ_half : 1 / 2 < β) (hβ1 : β < 1) (P₀ : ℕ) (T : ℝ) :
    ∃ s_* : ℂ, s_*.re = β - 1 / 2 ∧ T < |s_*.im| ∧
      Tendsto (fun s => ‖posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s‖) (𝓝[≠] s_*) atTop ∧
      ¬ AnalyticAt ℂ (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) s_* := by
  have hzf_half : ∀ z : ℂ, 1 / 2 < z.re → riemannZeta z ≠ 0 :=
    riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH
  obtain ⟨t, ht, hXi⟩ := exists_Xi_zero_gt (|T| + |γ₀| + 1)
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht
  set w_* : ℂ := 1 / 2 + (t : ℂ) * I
  have hw_ne0 : w_* ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [w_*] at this
  have hΛ : completedRiemannZeta w_* = 0 := by
    rw [completedRiemannZeta_critical_eq_Xi t, hXi]; simp
  have hζ_w : riemannZeta w_* = 0 := by
    rw [riemannZeta_def_of_ne_zero hw_ne0, hΛ, zero_div]
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  set s_* : ℂ := w_* - 1 + ρ₀
  have hs_re : s_*.re = β - 1 / 2 := by simp [s_*, w_*, ρ₀]; ring
  have hs_im : s_*.im = t + γ₀ := by simp [s_*, w_*, ρ₀]
  have hs_im_gt : T < |s_*.im| := by
    have htri : t - |γ₀| ≤ |t + γ₀| := by
      have h := abs_sub_abs_le_abs_sub t (-γ₀)
      simpa [abs_of_pos ht_pos, sub_neg_eq_add] using h
    rw [hs_im]
    linarith [le_abs_self T]
  have hs_pos : 0 < s_*.re := by linarith
  have hs_lt_half : s_*.re < 1 / 2 := by linarith
  have hs_lt1 : s_*.re < 1 := by linarith
  have hs_ne1 : s_* ≠ 1 := fun h => by rw [h] at hs_lt1; simp at hs_lt1
  have hζ_s_ne : riemannZeta s_* ≠ 0 := by
    intro h0
    have hrefl := riemannZeta_one_sub_eq_zero_of_mem_openStrip h0 hs_pos hs_lt1
    exact hzf_half (1 - s_*) (by simp; linarith) hrefl
  have hfin1 : (ρ₀ - 1 - s_*).re < 0 := by
    have : (ρ₀ - 1 - s_*).re = -1 / 2 := by dsimp [s_*, w_*, ρ₀]; simp; ring
    linarith
  have hfin2 : (conj ρ₀ - 1 - s_*).re < 0 := by
    have : (conj ρ₀ - 1 - s_*).re = -1 / 2 := by dsimp [s_*, w_*, ρ₀]; simp; ring
    linarith
  have hw1_eq : s_* + 1 - ρ₀ = w_* := by dsimp [s_*]; ring
  have hw1_ne1 : s_* + 1 - ρ₀ ≠ 1 := by
    rw [hw1_eq]; intro h; have := congrArg Complex.re h; simp [w_*] at this; norm_num at this
  have hw2_ne1 : s_* + 1 - conj ρ₀ ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [s_*, w_*, ρ₀] at this; norm_num at this
  have hw1_zero : riemannZeta (s_* + 1 - ρ₀) = 0 := by rw [hw1_eq]; exact hζ_w
  obtain ⟨htop, hnot_an⟩ := tendsto_norm_posTruncatedZeta_atTop_of_shifted_zero P₀
    hs_ne1 hζ_s_ne hfin1 hfin2 hw1_ne1 hw2_ne1 hw1_zero
  exact ⟨s_*, hs_re, hs_im_gt, htop, hnot_an⟩

/-! ## 7. Unconditional meromorphic tempered Euler-product firewall dichotomy -/

/-- **Unconditional meromorphic tempered Euler-product firewall:** either `AsymptoticAbscissaLaw`
holds unconditionally, or `Θ = zetaZeroAbscissa < 1` and for every `β ∈ (Θ, 1)` and `γ₀ ≠ 0`
there exist a meromorphic function `F` on `ℂ`, a multiplicative real nonnegative Ramanujan-bounded
coefficient sequence `a`, and a prime-power logarithmic-derivative weight `0 ≤ Λ̃ ≤ 2 Λ` such that
`F` is holomorphic across `Θ` on `{Re s > Θ + β − 1} \ {1}` with a positive-residue simple pole at
`1`, has a convergent distinct-prime Euler product and polynomial vertical bounds on `F` and `1/F`
right of `Θ`, violates `HalfPlaneAbscissaLaw F Θ` with exact zero pair `{β ± i γ₀}`, and has a
genuine pole strictly inside the left critical strip `0 < Re s < 1 − Θ ≤ 1/2`. -/
theorem asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff :
    _root_.RHTower.AsymptoticAbscissaLaw ∨
      (zetaZeroAbscissa < 1 ∧
        ∀ β γ₀ : ℝ, zetaZeroAbscissa < β → β < 1 → γ₀ ≠ 0 →
          let P₀ := posCutoff β
          let ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
          let F := posTruncatedZeta P₀ ρ₀
          let a := posTruncatedCoeff P₀ β γ₀
          let Λ' := posTruncatedVonMangoldt P₀ β γ₀
          MeromorphicOn F univ ∧
          DifferentiableOn ℂ F {s : ℂ | zetaZeroAbscissa + β - 1 < s.re ∧ s ≠ 1} ∧
          (∃ R : ℝ, 0 < R ∧ Tendsto (fun s => (s - 1) * F s) (𝓝[≠] 1) (𝓝 (R : ℂ))) ∧
          a.IsMultiplicative ∧
          (∀ n : ℕ, 0 ≤ a n) ∧
          (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → a n ≤ C * (n : ℝ) ^ ε) ∧
          (∀ n : ℕ, 0 ≤ Λ' n ∧ Λ' n ≤ 2 * Λ n) ∧
          (∀ s : ℂ, 1 < s.re →
            HasProd (fun q : Nat.Primes => posEulerFactor P₀ ρ₀ q s) (F s) ∧
            LSeries (fun n => (a n : ℂ)) s = F s ∧
            -logDeriv F s = LSeries (fun n => (Λ' n : ℂ)) s) ∧
          (∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
            ∀ s : ℂ, zetaZeroAbscissa + δ ≤ s.re → s.re ≤ d → |γ₀| + 6 ≤ |s.im| →
              ‖F s‖ ≤ C * |s.im| ^ N ∧ ‖(F s)⁻¹‖ ≤ C * |s.im| ^ N) ∧
          {s : ℂ | zetaZeroAbscissa < s.re ∧ s ≠ 1 ∧ F s = 0} = {ρ₀, conj ρ₀} ∧
          ¬ HalfPlaneAbscissaLaw F zetaZeroAbscissa ∧
          (∃ s_* : ℂ, 0 < s_*.re ∧ s_*.re < 1 - zetaZeroAbscissa ∧
            Tendsto (fun s => ‖F s‖) (𝓝[≠] s_*) atTop ∧ ¬ AnalyticAt ℂ F s_*)) := by
  rcases eq_or_lt_of_le zetaZeroAbscissa_le_one with hΘ_eq | hΘ_lt
  · exact Or.inl (asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one hΘ_eq.symm)
  · refine Or.inr ⟨hΘ_lt, fun β γ₀ hΘβ hβ1 hγ₀ => ?_⟩
    have hΘ_half : 1 / 2 ≤ zetaZeroAbscissa := half_le_zetaZeroAbscissa
    have hzf : ∀ z : ℂ, zetaZeroAbscissa < z.re → riemannZeta z ≠ 0 :=
      fun _ hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz
    have hP₀ : 2 * ((posCutoff β : ℝ) + 1) ^ (β - 1) ≤ 1 := two_mul_posCutoff_rpow_le_one hβ1
    refine ⟨meromorphicOn_posTruncatedZeta _ _,
      differentiableOn_posTruncatedZeta γ₀ hΘ_half hzf _,
      exists_pos_residue_posTruncatedZeta_one _ hβ1 hγ₀,
      isMultiplicative_posTruncatedCoeff _ _ _,
      posTruncatedCoeff_nonneg γ₀ hβ1 hP₀,
      fun ε hε => exists_posTruncatedCoeff_le_rpow _ γ₀ hβ1 hP₀ hε,
      posTruncatedVonMangoldt_bounds γ₀ hβ1 hP₀,
      fun s hs => ⟨(hasProd_and_LSeries_posTruncatedZeta γ₀ hβ1 hP₀ hs).1,
        (hasProd_and_LSeries_posTruncatedZeta γ₀ hβ1 hP₀ hs).2,
        neg_logDeriv_posTruncatedZeta_eq_LSeries γ₀ hβ1 hs⟩,
      fun δ hδ d => exists_poly_bounds_posTruncatedZeta hΘ_half hΘ_lt hΘβ hβ1 hzf _ hδ d,
      zeroSet_posTruncatedZeta_eq_pair hΘ_half hΘβ hβ1 hγ₀ hzf _,
      not_halfPlaneAbscissaLaw_posTruncatedZeta hΘ_half hΘβ hβ1 hγ₀ hzf _,
      exists_left_strip_pole_posTruncatedZeta hΘ_lt hΘβ hβ1 hγ₀ _⟩

#print axioms asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one
#print axioms hasProd_and_LSeries_posTruncatedZeta
#print axioms neg_logDeriv_posTruncatedZeta_eq_LSeries
#print axioms exists_poly_bounds_posTruncatedZeta
#print axioms exists_left_strip_pole_posTruncatedZeta
#print axioms exists_left_strip_pole_above_of_riemannHypothesis
#print axioms asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff

end GaloisForLFunctions.ArithmeticPositiveDuality
