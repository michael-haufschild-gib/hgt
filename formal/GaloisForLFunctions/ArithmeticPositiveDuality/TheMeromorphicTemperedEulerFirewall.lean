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
    (hw : 1 < (s + 1 - c).re) :
    logDeriv (fun z => (1 - ((q : ℕ) : ℂ) ^ (c - z))⁻¹) s =
      -LSeries (primePowVonMangoldt q) (s + 1 - c) := by
  set p : ℕ := (q : ℕ)
  have hp : p.Prime := q.prop
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw' : (c - s).re < 0 := by
    have : (c - s).re = -(s + 1 - c).re + 1 := by simp; ring
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
    have hd2 := (HasDerivAt.const_sub 1 hd1.cexp)
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
  set x : ℂ := (p : ℂ) ^ (-(s + 1 - c))
  have hx_eq : x = (p : ℂ) ^ (c - 1 - s) := by
    dsimp [x]; congr 1; ring
  have hw'' : (c - 1 - s).re < 0 := by
    have : (c - 1 - s).re = -(s + 1 - c).re := by simp; ring
    linarith
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hx_norm : ‖x‖ < 1 := by
    rw [hx_eq, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hw''
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := fun a b hab =>
    Nat.succ.inj (Nat.pow_right_injective hp.one_lt hab)
  have hsupp : Function.support (LSeries.term (primePowVonMangoldt q) (s + 1 - c)) ⊆
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
  have hL : LSeries (primePowVonMangoldt q) (s + 1 - c) =
      (Real.log p : ℂ) * x * (1 - x)⁻¹ := by
    unfold LSeries
    rw [← hinj.tsum_eq hsupp]
    have hterm : ∀ k : ℕ, LSeries.term (primePowVonMangoldt q) (s + 1 - c) (p ^ (k + 1)) =
        (Real.log p : ℂ) * x * x ^ k := by
      intro k
      have hpk0 : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [LSeries.term_of_ne_zero hpk0, ← cpow_neg,
        show primePowVonMangoldt q (p ^ (k + 1)) = (Real.log p : ℂ) by
          unfold primePowVonMangoldt; exact if_pos ⟨k, rfl⟩,
        natCast_pow_cpow_neg p (k + 1) (s + 1 - c), pow_succ']
      dsimp [x]
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hx_norm]
  -- Wait: check exponent `c - 1 - s` vs `c - s`!
  -- Notice `posFiniteFactor` has `ρ₀ - 1 - s = (ρ₀ - 1) - s`, so when `c = ρ₀ - 1`,
  -- `s + 1 - ρ₀ = s - c`, NOT `s + 1 - c`! Let's fix the parameter cleanly below!
  sorry
/-! WAIT: let's catch that parameter convention right now in thought before saving! -/
