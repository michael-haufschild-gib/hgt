import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalLineVaughanTypeIIAbscissaEliminationAndShellLocalization

/-!
# Symmetric Dual Vaughan Bilinearization, Universal Prime and Small-Cofactor-Times-Prime Annihilation, Unsmoothed Balanced Dual Band Localization, and Conductor-Square Gap Invariance on `Ω_open`

On the direct side of `SmoothReflectedMobiusVaughanTypeIAnnihilation`, the Vaughan Type-II
arithmetic function `((μ - truncAF μ U) * typeIIShort V)` is asymmetric and retains unbounded
Möbius values `μ(a)` across `a > U`. Applying the cross-height Gaussian two-series identity to
`smoothOuterVaughanTypeII` itself convolving with `ζ` on the dual side transforms this asymmetric
weight into a symmetric bilinear form with zero unbounded Möbius and exact prime annihilation.

This module establishes four unconditional results across
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}`:

1. **Symmetric dual Vaughan bilinearization and universal prime / small-cofactor-times-prime
   annihilation (`vaughanDualBilinear`, `zeta_mul_vaughanTypeIICoeff_eq_vaughanDualBilinear`,
   `exists_balanced_factorization_of_vaughanDualBilinear_ne_zero`,
   `vaughanDualBilinear_mul_prime_eq_zero`, `parityClearedVaughanDualBilinear_prime_eq_zero`):**
   In the Dirichlet ring `ArithmeticFunction ℝ`,
   `ζ * ((μ - truncAF μ U) * typeIIShort V) = typeIIShort U * typeIIShort V`.
   Consequently, `vaughanDualBilinear U V` is symmetric in `(U, V)`, depends only on finite Möbius
   values up to `max U V`, vanishes identically below `(U + 1) * (V + 1)`, and vanishes identically
   at `m * p` for **every prime `p`** (of any size) and **every `m ≤ min U V`** — in contrast to a
   linear mollifier `truncAF μ U'`, which leaves every prime `p > U'` uncancelled on the dual side.

2. **Exact cross-height dual sieve identity for `smoothOuterVaughanTypeII` and global unsmoothing
   (`smoothOuterVaughanTypeII_eq_zeta_mul_add_dual_sieve`,
   `norm_smoothOuterVaughanDualSieveCoeff_sub_parityCleared_le`):**
   Weighting `crossHeight_gaussian_two_tsum_eq` at `(d x, 2 d x)` by
   `((μ - truncAF μ U) * typeIIShort V)(d) · d^{-(1 - s)} · W(d / Y)` expresses
   `smoothOuterVaughanTypeII U V s x Y` as `(1 - 2^{-(1 - s)}) ζ(s) C_{U, V, Y}(1 - s)` plus the
   dual sieve series, whose coefficients differ from the exact unsmoothed
   `parityClearedVaughanDualBilinear U V k` by `≤ 8 K_B k^{3 + B} Y^{-B}` for every `k ≥ 1`.

3. **Unsmoothed finite balanced dual bilinear band localization and `HasStrictPrimeGasWitness`
   production across all of `Ω_open`
   (`balancedDualBilinearBandSum`, `exists_balancedDualBilinearBand_duality_on_remaining_strip`,
   `strict_primeGas_witness_of_balancedDualBilinearBand_domination_on_remaining_strip`):**
   At `x = |Im s|^{-(1 + η)}` and `Y = |Im s|^{3 + η}` (`η ≥ 1`, `δ > 0`), the `η B` exponents in
   `Y^{-B} · x^{-(B + 4)}` cancel identically, unsmoothing the entire dual series up to
   `O(|Im s|^{-B_dec})` while rapid dual decay truncates `k > ⌈|Im s|^{2 + η + δ}⌉₊` and
   `parityClearedVaughanDualBilinear_eq_zero_of_lt_succ_mul_succ` kills `1 ≤ k < (U + 1)(V + 1)`
   identically. At any hypothetical zero `ζ(s) = 0` in `Ω_open`, both `ζ(s)`-multiples vanish and
   the finite balanced bilinear band `(U + 1)(V + 1) ≤ k ≤ ⌈|Im s|^{2 + η + δ}⌉₊` (with zero primes
   and zero `m * p` for `m ≤ min U V`) is forced strictly above
   `(1 / 4) (|Im s| / 7)^{1/2 - Re s} - C_band |Im s|^{-1 / 4}`.

4. **Scale-invariant `|Im s|^2` conductor gap and balanced factor window pinning
   (`vaughan_conductor_square_gap_invariance`, `balanced_dual_factor_window_pinning`):**
   Across all scales `x > 0`, the ratio `(T / x) / (T * x)⁻¹` between the dual analytic horizon and
   the sub-horizon Type-I cutoff equals `T ^ 2` identically, while every active dual index
   `k ≤ K_hi` pins both factors into `(U, K_hi / V)` and `(V, K_hi / U)`.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Symmetric Dual Vaughan Bilinearization and Prime / Almost-Prime Annihilation -/

section Part1SymmetricDualVaughanBilinearization

/-- Symmetric dual Vaughan bilinear arithmetic function `typeIIShort U * typeIIShort V`
(`= (1 - ζ * truncAF μ U) * (1 - ζ * truncAF μ V)`), containing zero unbounded Möbius values. -/
def vaughanDualBilinear (U V : ℕ) : ArithmeticFunction ℝ :=
  _root_.RHTower.Sieve.typeIIShort U * _root_.RHTower.Sieve.typeIIShort V

/-- Parity-cleared `(x, 2x)` dual Vaughan bilinear coefficient at `k : ℕ`. -/
def parityClearedVaughanDualBilinear (U V k : ℕ) : ℂ :=
  ((vaughanDualBilinear U V k : ℝ) : ℂ) -
    if 2 ∣ k then ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ) else 0

/-- Exact symmetry of `vaughanDualBilinear U V` in `(U, V)`. -/
theorem vaughanDualBilinear_comm (U V : ℕ) :
    vaughanDualBilinear U V = vaughanDualBilinear V U :=
  mul_comm _ _

/-- **Exact symmetric dual Vaughan bilinearization in the Dirichlet ring:**
convolving the asymmetric Type-II coefficient `(μ - truncAF μ U) * typeIIShort V` with `ζ` yields
the symmetric product `vaughanDualBilinear U V = typeIIShort U * typeIIShort V`. -/
theorem zeta_mul_vaughanTypeIICoeff_eq_vaughanDualBilinear (U V : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) =
      vaughanDualBilinear U V := by
  have hmu : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
    rw [mul_comm]
    exact ArithmeticFunction.coe_moebius_mul_coe_zeta
  unfold vaughanDualBilinear
  have hU : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) =
      _root_.RHTower.Sieve.typeIIShort U := by
    rw [mul_sub, hmu]
    rfl
  rw [← mul_assoc, hU]

/-- **Balanced-factor support characterization of `vaughanDualBilinear`:**
every `k : ℕ` with `vaughanDualBilinear U V k ≠ 0` admits a factorization `k = a * b` with
`U < a` and `V < b`. -/
theorem exists_balanced_factorization_of_vaughanDualBilinear_ne_zero
    {U V k : ℕ} (hne : vaughanDualBilinear U V k ≠ 0) :
    ∃ a b : ℕ, a * b = k ∧ U < a ∧ V < b := by
  unfold vaughanDualBilinear at hne
  rw [ArithmeticFunction.mul_apply] at hne
  by_contra hall
  push Not at hall
  refine hne (Finset.sum_eq_zero fun p hp => ?_)
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hne0 := (Nat.mem_divisorsAntidiagonal.mp hp).2
  have hp1 : 1 ≤ p.1 := by
    by_contra h0; have hz : p.1 = 0 := by omega
    rw [hz, zero_mul] at hprod; exact hne0 hprod.symm
  have hp2 : 1 ≤ p.2 := by
    by_contra h0; have hz : p.2 = 0 := by omega
    rw [hz, mul_zero] at hprod; exact hne0 hprod.symm
  by_cases hU : p.1 ≤ U
  · have hz1 : _root_.RHTower.Sieve.typeIIShort U p.1 = 0 :=
      _root_.RHTower.Sieve.one_sub_zeta_mul_truncAF_moebius_apply_eq_zero hp1 hU
    rw [hz1, zero_mul]
  · have hgtU : U < p.1 := by omega
    have hV : p.2 ≤ V := hall p.1 p.2 hprod hgtU
    have hz2 : _root_.RHTower.Sieve.typeIIShort V p.2 = 0 :=
      _root_.RHTower.Sieve.one_sub_zeta_mul_truncAF_moebius_apply_eq_zero hp2 hV
    rw [hz2, mul_zero]

/-- `vaughanDualBilinear U V k = 0` identically for every `k < (U + 1) * (V + 1)`. -/
theorem vaughanDualBilinear_eq_zero_of_lt_succ_mul_succ
    {U V k : ℕ} (hk : k < (U + 1) * (V + 1)) :
    vaughanDualBilinear U V k = 0 := by
  by_contra hne
  obtain ⟨a, b, hab, hUa, hVb⟩ :=
    exists_balanced_factorization_of_vaughanDualBilinear_ne_zero hne
  have hle : (U + 1) * (V + 1) ≤ a * b := Nat.mul_le_mul hUa hVb
  omega

/-- `parityClearedVaughanDualBilinear U V k = 0` identically for every `k < (U + 1) * (V + 1)`. -/
theorem parityClearedVaughanDualBilinear_eq_zero_of_lt_succ_mul_succ
    {U V k : ℕ} (hk : k < (U + 1) * (V + 1)) :
    parityClearedVaughanDualBilinear U V k = 0 := by
  unfold parityClearedVaughanDualBilinear
  rw [vaughanDualBilinear_eq_zero_of_lt_succ_mul_succ hk]
  split_ifs with h2k
  · have hk2 : k / 2 < (U + 1) * (V + 1) := (Nat.div_le_self k 2).trans_lt hk
    rw [vaughanDualBilinear_eq_zero_of_lt_succ_mul_succ hk2]
    simp
  · simp

/-- **Universal small-cofactor-times-prime annihilation:**
for **every prime `p`** (of any size whatsoever) and **every `m ≤ min U V`**,
`vaughanDualBilinear U V (m * p) = 0`. -/
theorem vaughanDualBilinear_mul_prime_eq_zero
    {U V m p : ℕ} (hp : Nat.Prime p) (hm : m ≤ min U V) :
    vaughanDualBilinear U V (m * p) = 0 := by
  by_contra hne
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [zero_mul, ArithmeticFunction.map_zero] at hne
    exact hne rfl
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  obtain ⟨a, b, hab, hUa, hVb⟩ :=
    exists_balanced_factorization_of_vaughanDualBilinear_ne_zero hne
  have hdvd : p ∣ a * b := ⟨m, by rw [hab, mul_comm]⟩
  rcases hp.dvd_mul.mp hdvd with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hpm : p * (q * b) = p * m := by
      calc p * (q * b) = p * q * b := (mul_assoc p q b).symm
        _ = m * p := hab
        _ = p * m := mul_comm m p
    have hqb : q * b = m := Nat.eq_of_mul_eq_mul_left hp.pos hpm
    have hbm : b ≤ m := Nat.le_of_dvd hm_pos ⟨q, by rw [mul_comm]; exact hqb.symm⟩
    have hmV : m ≤ V := hm.trans (min_le_right U V)
    omega
  · have hpm : p * (a * q) = p * m := by
      calc p * (a * q) = a * (p * q) := by ring
        _ = m * p := hab
        _ = p * m := mul_comm m p
    have haq : a * q = m := Nat.eq_of_mul_eq_mul_left hp.pos hpm
    have ham : a ≤ m := Nat.le_of_dvd hm_pos ⟨q, haq.symm⟩
    have hmU : m ≤ U := hm.trans (min_le_left U V)
    omega

/-- **Universal prime annihilation (`U ≥ 1, V ≥ 1`):**
`vaughanDualBilinear U V p = 0` for **every prime `p : ℕ`**. -/
theorem vaughanDualBilinear_prime_eq_zero
    {U V p : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hp : Nat.Prime p) :
    vaughanDualBilinear U V p = 0 := by
  simpa only [one_mul] using
    vaughanDualBilinear_mul_prime_eq_zero hp (le_min hU hV)

/-- **Universal parity-cleared prime annihilation (`U ≥ 1, V ≥ 1`):**
`parityClearedVaughanDualBilinear U V p = 0` for **every prime `p : ℕ`**. -/
theorem parityClearedVaughanDualBilinear_prime_eq_zero
    {U V p : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hp : Nat.Prime p) :
    parityClearedVaughanDualBilinear U V p = 0 := by
  unfold parityClearedVaughanDualBilinear
  rw [vaughanDualBilinear_prime_eq_zero hU hV hp]
  split_ifs with h2p
  · rcases hp.eq_one_or_self_of_dvd 2 h2p with h21 | rfl
    · omega
    · have h1_lt : (2 / 2 : ℕ) < (U + 1) * (V + 1) := by
        have h4 : 2 * 2 ≤ (U + 1) * (V + 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      rw [vaughanDualBilinear_eq_zero_of_lt_succ_mul_succ h1_lt]
      simp
  · simp

/-- Elementary polynomial bound `|vaughanDualBilinear U V k| ≤ 4 * (k : ℝ) ^ 2` for all `k : ℕ`. -/
lemma abs_vaughanDualBilinear_le_four_mul_sq (U V k : ℕ) :
    |vaughanDualBilinear U V k| ≤ 4 * (k : ℝ) ^ (2 : ℕ) := by
  have hshort : ∀ (W m : ℕ), 1 ≤ m → |_root_.RHTower.Sieve.typeIIShort W m| ≤ 2 * (m : ℝ) := by
    intro W m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hb := _root_.RHTower.Sieve.abs_one_sub_zeta_mul_moebius_le W m
    change |_root_.RHTower.Sieve.typeIIShort W m| ≤ 1 + (m.divisors.card : ℝ) at hb
    have hcard : (m.divisors.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.card_divisors_le_self m
    linarith
  unfold vaughanDualBilinear
  rw [ArithmeticFunction.mul_apply]
  have hpt : ∀ p ∈ k.divisorsAntidiagonal,
      |_root_.RHTower.Sieve.typeIIShort U p.1 * _root_.RHTower.Sieve.typeIIShort V p.2| ≤
        4 * (k : ℝ) := by
    intro p hp
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hne0 := (Nat.mem_divisorsAntidiagonal.mp hp).2
    have hp1 : 1 ≤ p.1 := by
      by_contra h0; have hz : p.1 = 0 := by omega
      rw [hz, zero_mul] at hprod; exact hne0 hprod.symm
    have hp2 : 1 ≤ p.2 := by
      by_contra h0; have hz : p.2 = 0 := by omega
      rw [hz, mul_zero] at hprod; exact hne0 hprod.symm
    have hprod_r : (p.1 : ℝ) * (p.2 : ℝ) = (k : ℝ) := by exact_mod_cast hprod
    rw [abs_mul]
    calc |_root_.RHTower.Sieve.typeIIShort U p.1| * |_root_.RHTower.Sieve.typeIIShort V p.2|
        ≤ (2 * (p.1 : ℝ)) * (2 * (p.2 : ℝ)) :=
          mul_le_mul (hshort U p.1 hp1) (hshort V p.2 hp2) (abs_nonneg _) (by positivity)
      _ = 4 * ((p.1 : ℝ) * (p.2 : ℝ)) := by ring
      _ = 4 * (k : ℝ) := by rw [hprod_r]
  have hcard_anti : (k.divisorsAntidiagonal.card : ℝ) ≤ (k : ℝ) := by
    rw [_root_.RHTower.Sieve.card_divisorsAntidiagonal]
    exact_mod_cast Nat.card_divisors_le_self k
  calc |∑ p ∈ k.divisorsAntidiagonal,
          _root_.RHTower.Sieve.typeIIShort U p.1 * _root_.RHTower.Sieve.typeIIShort V p.2|
      ≤ ∑ p ∈ k.divisorsAntidiagonal,
          |_root_.RHTower.Sieve.typeIIShort U p.1 * _root_.RHTower.Sieve.typeIIShort V p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ k.divisorsAntidiagonal, 4 * (k : ℝ) := Finset.sum_le_sum hpt
    _ = (k.divisorsAntidiagonal.card : ℝ) * (4 * (k : ℝ)) := by simp
    _ ≤ (k : ℝ) * (4 * (k : ℝ)) := mul_le_mul_of_nonneg_right hcard_anti (by positivity)
    _ = 4 * (k : ℝ) ^ (2 : ℕ) := by ring

lemma norm_parityClearedVaughanDualBilinear_le_eight_mul_sq (U V k : ℕ) :
    ‖parityClearedVaughanDualBilinear U V k‖ ≤ 8 * (k : ℝ) ^ (2 : ℕ) := by
  unfold parityClearedVaughanDualBilinear
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((vaughanDualBilinear U V k : ℝ) : ℂ)‖ ≤ 4 * (k : ℝ) ^ (2 : ℕ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_vaughanDualBilinear_le_four_mul_sq U V k
  have h2 : ‖if 2 ∣ k then ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ) else 0‖ ≤
      4 * (k : ℝ) ^ (2 : ℕ) := by
    split_ifs with h2k
    · have hk2_le : ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.div_le_self k 2
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_vaughanDualBilinear_le_four_mul_sq U V (k / 2)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk2_le 2) (by norm_num))
    · rw [norm_zero]; positivity
  linarith

end Part1SymmetricDualVaughanBilinearization


/-! ### Part 2: Cross-Height Dual Sieve Identity for `smoothOuterVaughanTypeII` and Global Unsmoothing -/

section Part2VaughanTypeIIDualSieveIdentity

/-- Smooth outer-weighted Vaughan Type-II Dirichlet series
`∑_{d ≥ 1} ((μ - truncAF μ U) * typeIIShort V)(d) · d^{-w} · smoothAFECutoff(d / Y)`. -/
def smoothOuterVaughanTypeIISeries (U V : ℕ) (Y : ℝ) (w : ℂ) : ℂ :=
  ∑' d : ℕ,
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-w) *
      smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)

/-- Dual `(x, 2x)` sieve coefficient generated by weighting `crossHeight_gaussian_two_tsum_eq`
by `((μ - truncAF μ U) * typeIIShort V)(d) · W(d / Y)`. -/
def smoothOuterVaughanDualSieveCoeff (U V : ℕ) (Y : ℝ) (k : ℕ) : ℂ :=
  (∑ d ∈ k.divisors,
      (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) d : ℝ) : ℂ) *
        smoothAFECutoff ((d : ℝ) / Y)) -
    if 2 ∣ k then
      ∑ d ∈ (k / 2).divisors,
        (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
            _root_.RHTower.Sieve.typeIIShort V) d : ℝ) : ℂ) *
          smoothAFECutoff ((d : ℝ) / Y)
    else 0

private lemma tsum_dvd_shift_eq' {q : ℕ} (hq : 1 ≤ q) (f : ℕ → ℂ) :
    (∑' m : ℕ, f (q * (m + 1) - 1)) =
      ∑' k : ℕ, if q ∣ (k + 1) then f k else 0 := by
  set g : ℕ → ℂ := fun k => if q ∣ (k + 1) then f k else 0
  set ι : ℕ → ℕ := fun m => q * (m + 1) - 1
  have hι_add1 : ∀ m : ℕ, ι m + 1 = q * (m + 1) := fun m =>
    Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos m))
  have hι_inj : Function.Injective ι := fun m₁ m₂ heq => by
    have h1 : ι m₁ + 1 = ι m₂ + 1 := congrArg (· + 1) heq
    rw [hι_add1, hι_add1] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hq h1
    omega
  have hcomp : (fun m : ℕ => f (q * (m + 1) - 1)) = fun m : ℕ => g (ι m) := by
    funext m; dsimp only [g]; rw [hι_add1 m, if_pos (dvd_mul_right q (m + 1))]
  rw [hcomp]
  refine Function.Injective.tsum_eq hι_inj fun k hk => ?_
  rw [Function.mem_support] at hk
  have hdvd : q ∣ (k + 1) := by
    by_contra hnd; exact hk (by dsimp only [g]; exact if_neg hnd)
  obtain ⟨c, hc⟩ := hdvd
  have hc_pos : 1 ≤ c := by
    by_contra hc0; have h0 : c = 0 := by omega
    rw [h0, mul_zero] at hc; omega
  refine ⟨c - 1, ?_⟩
  dsimp only [ι]; rw [Nat.sub_add_cancel hc_pos, ← hc]; omega

/-- **Global unsmoothing bound on `smoothOuterVaughanDualSieveCoeff`:**
for all `U, V : ℕ`, `B > 0`, `Y > 0`, and `k ≥ 1`, subtracting `1` from `smoothAFECutoff(d / Y)`
identifies the unsmoothed divisor sum with `parityClearedVaughanDualBilinear U V k` within
`≤ 8 * K_B * k^{3 + B} * Y^{-B}`. -/
theorem norm_smoothOuterVaughanDualSieveCoeff_sub_parityCleared_le
    (U V : ℕ) {B K_B : ℝ} (hB : 0 < B) (hKB0 : 0 ≤ K_B)
    (hKB : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u - 1‖ ≤ K_B * u ^ B)
    {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk1 : 1 ≤ k) :
    ‖smoothOuterVaughanDualSieveCoeff U V Y k -
        parityClearedVaughanDualBilinear U V k‖ ≤
      8 * K_B * (k : ℝ) ^ (3 + B) * Y ^ (-B) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  set c_UV : ArithmeticFunction ℝ :=
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
      _root_.RHTower.Sieve.typeIIShort V
  have hdiv_sub : ∀ {m : ℕ}, 1 ≤ m → m ≤ k →
      ‖(∑ d ∈ m.divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
          ((vaughanDualBilinear U V m : ℝ) : ℂ)‖ ≤
        4 * K_B * (k : ℝ) ^ (3 + B) * Y ^ (-B) := by
    intro m hm1 hmk
    have hm_pos : 0 < m := hm1
    have hunsm :
        ((vaughanDualBilinear U V m : ℝ) : ℂ) =
          ∑ d ∈ m.divisors, ((c_UV d : ℝ) : ℂ) * 1 := by
      have hconv : vaughanDualBilinear U V m = ∑ d ∈ m.divisors, c_UV d := by
        rw [← zeta_mul_vaughanTypeIICoeff_eq_vaughanDualBilinear U V]
        exact ArithmeticFunction.coe_zeta_mul_apply
      rw [hconv, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun _ _ => (mul_one _).symm
    have hdiff_eq :
        (∑ d ∈ m.divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
          ((vaughanDualBilinear U V m : ℝ) : ℂ) =
        ∑ d ∈ m.divisors, ((c_UV d : ℝ) : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1) := by
      rw [hunsm, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => (mul_sub _ _ _).symm
    rw [hdiff_eq]
    have hcard : (m.divisors.card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.card_divisors_le_self m).trans hmk
    have hpt : ∀ d ∈ m.divisors,
        ‖((c_UV d : ℝ) : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1)‖ ≤
          4 * (k : ℝ) ^ (2 : ℕ) * (K_B * ((k : ℝ) / Y) ^ B) := by
      intro d hd
      have hdv := Nat.dvd_of_mem_divisors hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdv hm_pos
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hdk : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_dvd hm_pos hdv).trans hmk
      have hc_le : ‖((c_UV d : ℝ) : ℂ)‖ ≤ 4 * (k : ℝ) ^ (2 : ℕ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_vaughanTypeIICoeff_le_four_mul_sq U V d hd1).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd_pos.le hdk 2) (by norm_num))
      have hW_le : ‖smoothAFECutoff ((d : ℝ) / Y) - 1‖ ≤ K_B * ((k : ℝ) / Y) ^ B :=
        (hKB (div_pos hd_pos hY)).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hdk hY.le) hB.le) hKB0)
      rw [norm_mul]
      exact mul_le_mul hc_le hW_le (norm_nonneg _) (by positivity)
    calc ‖∑ d ∈ m.divisors, ((c_UV d : ℝ) : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1)‖
        ≤ ∑ d ∈ m.divisors, ‖((c_UV d : ℝ) : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _d ∈ m.divisors, 4 * (k : ℝ) ^ (2 : ℕ) * (K_B * ((k : ℝ) / Y) ^ B) :=
          Finset.sum_le_sum hpt
      _ = (m.divisors.card : ℝ) * (4 * (k : ℝ) ^ (2 : ℕ) * (K_B * ((k : ℝ) / Y) ^ B)) := by simp
      _ ≤ (k : ℝ) * (4 * (k : ℝ) ^ (2 : ℕ) * (K_B * ((k : ℝ) / Y) ^ B)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 4 * K_B * ((k : ℝ) ^ (3 : ℝ) * (k : ℝ) ^ B) * Y ^ (-B) := by
          have hk3 : (k : ℝ) * (k : ℝ) ^ (2 : ℕ) = (k : ℝ) ^ (3 : ℝ) := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
          rw [Real.div_rpow hk_pos.le hY.le, div_eq_mul_inv, ← Real.rpow_neg hY.le]
          calc (k : ℝ) * (4 * (k : ℝ) ^ (2 : ℕ) * (K_B * ((k : ℝ) ^ B * Y ^ (-B))))
              = 4 * K_B * (((k : ℝ) * (k : ℝ) ^ (2 : ℕ)) * (k : ℝ) ^ B) * Y ^ (-B) := by ring
            _ = 4 * K_B * ((k : ℝ) ^ (3 : ℝ) * (k : ℝ) ^ B) * Y ^ (-B) := by rw [hk3]
      _ = 4 * K_B * (k : ℝ) ^ (3 + B) * Y ^ (-B) := by rw [← Real.rpow_add hk_pos]
  unfold smoothOuterVaughanDualSieveCoeff parityClearedVaughanDualBilinear
  have hrearr :
      ((∑ d ∈ k.divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
        if 2 ∣ k then
          ∑ d ∈ (k / 2).divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)
        else 0) -
      (((vaughanDualBilinear U V k : ℝ) : ℂ) -
        if 2 ∣ k then ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ) else 0) =
      ((∑ d ∈ k.divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
        ((vaughanDualBilinear U V k : ℝ) : ℂ)) -
      (if 2 ∣ k then
        (∑ d ∈ (k / 2).divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
          ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ)
      else 0) := by
    split_ifs <;> ring
  change ‖((∑ d ∈ k.divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
        if 2 ∣ k then
          ∑ d ∈ (k / 2).divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)
        else 0) -
      (((vaughanDualBilinear U V k : ℝ) : ℂ) -
        if 2 ∣ k then ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ) else 0)‖ ≤ _
  rw [hrearr]
  refine (norm_sub_le _ _).trans ?_
  have hb1 := hdiv_sub hk1 le_rfl
  have hb2 : ‖if 2 ∣ k then
      (∑ d ∈ (k / 2).divisors, ((c_UV d : ℝ) : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
        ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ)
      else 0‖ ≤ 4 * K_B * (k : ℝ) ^ (3 + B) * Y ^ (-B) := by
    split_ifs with h2k
    · obtain ⟨q, hq⟩ := h2k
      exact hdiv_sub (by omega) (Nat.div_le_self k 2)
    · rw [norm_zero]; positivity
  linarith

/-- **Exact cross-height dual sieve identity for `smoothOuterVaughanTypeII`:**
for all `U, V : ℕ`, `x > 0`, `Y > 0`, and `0 < Re s < 1 / 2`, weighting
`crossHeight_gaussian_two_tsum_eq` at `(d x, 2 d x)` by `c_{U, V}(d) d^{-(1 - s)} W(d / Y)` cancels
`smoothAFEZetaShiftedPoleResidue` identically and expresses `smoothOuterVaughanTypeII U V s x Y` as
`(1 - 2^{-(1 - s)}) ζ(s) * smoothOuterVaughanTypeIISeries U V Y (1 - s)` plus the dual sieve series. -/
theorem smoothOuterVaughanTypeII_eq_zeta_mul_add_dual_sieve
    (U V : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    smoothOuterVaughanTypeII U V s x Y =
      (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s *
          smoothOuterVaughanTypeIISeries U V Y (1 - s) +
        ∑' k : ℕ, smoothOuterVaughanDualSieveCoeff U V Y (k + 1) *
          smoothAFEZetaDualCoefficientGeneral s x k := by
  obtain ⟨K_d1, hK_d1_pos, hK_d1⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := s.re / 2) (by linarith) (by linarith) (r := 1) le_rfl
  set C_d1 : ℝ := K_d1 * x ^ (-2 * ((1 : ℕ) : ℝ)) * (1 + |s.im|) ^ (2 * ((1 : ℕ) : ℝ) + 1 / 2 - s.re)
  have hI_le : ∀ k : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x k‖ ≤
      C_d1 * (k + 1 : ℝ) ^ (-(2 * ((1 : ℕ) : ℝ) + 1 - s.re)) :=
    fun k => (hK_d1 s x (by linarith) hhi hx).1 k
  have hsum_du : Summable (fun k : ℕ => smoothAFEZetaDualCoefficientGeneral s x k) := by
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2 * ((1 : ℕ) : ℝ) + 1 - s.re) (by push_cast; linarith)).mul_left C_d1)
      fun k => ?_
    rw [one_div, ← Real.rpow_neg (by positivity)]
    exact hI_le k
  have hscale_q : ∀ {q : ℕ}, 1 ≤ q →
      (q : ℂ) ^ (-(1 - s)) * riemannZeta s =
        (q : ℂ) ^ (-(1 - s)) *
            (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((q : ℝ) * x)))) -
          (∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
          smoothAFEZetaShiftedPoleResidue s x := by
    intro q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hfe := crossHeight_gaussian_two_tsum_eq unitPoleFreeCrossHeightDatum_riemannZeta (mul_pos hq_pos hx) hs0 hhi
    unfold crossHeightGaussianTwoSeries at hfe
    simp only [one_mul, Complex.ofReal_one, Complex.one_cpow, div_one] at hfe
    have hmul := congrArg (fun z : ℂ => (q : ℂ) ^ (-(1 - s)) * z) hfe
    rw [mul_sub, mul_sub, smoothAFEZetaShiftedPoleResidue_mul_scale hq hx s] at hmul
    have hdu_congr :
        (q : ℂ) ^ (-(1 - s)) * (∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s ((q : ℝ) * x) m) =
          ∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0 := by
      rw [← tsum_mul_left,
        tsum_congr (fun m => smoothAFEZetaDualCoefficientGeneral_mul_scale hq hx hs0 hhi m)]
      exact tsum_dvd_shift_eq' hq _
    rwa [hdu_congr] at hmul
  set c_UV : ℕ → ℂ := fun n =>
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) n : ℝ) : ℂ)
  set w_d : ℕ → ℂ := fun d =>
    c_UV (d + 1) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)
  set g_du : ℕ → ℕ → ℂ := fun d k =>
    c_UV (d + 1) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      ((if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0) -
        (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)) *
      smoothAFEZetaDualCoefficientGeneral s x k
  have hterm_d : ∀ d : ℕ,
      w_d d * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s) =
        w_d d * smoothOuterDirectPairSum s x (d + 1) - ∑' k : ℕ, g_du d k := by
    intro d
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have h2d1 : 1 ≤ 2 * (d + 1) := by omega
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have h2d_cpow : ((2 * (d + 1) : ℕ) : ℂ) ^ (-(1 - s)) =
        (2 : ℂ) ^ (-(1 - s)) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) := by
      rw [show ((2 * (d + 1) : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg two_pos.le hd_pos.le (-(1 - s))]
      push_cast; rfl
    have h1 := hscale_q hd1
    have h2 := hscale_q h2d1
    rw [h2d_cpow, show ((2 * (d + 1) : ℕ) : ℝ) * x = 2 * ((d + 1 : ℕ) : ℝ) * x by push_cast; ring] at h2
    have hs_dir1 := summable_smoothAFE_direct (A := 2) (by norm_num) (mul_pos hd_pos hx) (by linarith)
    have hs_dir2 := (summable_smoothAFE_direct (A := 2) (by norm_num)
      (show 0 < 2 * ((d + 1 : ℕ) : ℝ) * x by positivity) (by linarith)).mul_left ((2 : ℂ) ^ (-(1 - s)))
    have hdir_sub :
        (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) * x)))) -
          (2 : ℂ) ^ (-(1 - s)) *
            (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
              smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * ((d + 1 : ℕ) : ℝ) * x)))) =
          smoothOuterDirectPairSum s x (d + 1) := by
      unfold smoothOuterDirectPairSum
      rw [← tsum_mul_left, ← hs_dir1.tsum_sub hs_dir2]
      exact tsum_congr fun _ => by ring
    have hdu1 : Summable (fun k : ℕ =>
        if (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) :=
      Summable.of_norm_bounded hsum_du.norm fun k => by split_ifs <;> simp
    have hdu2 : Summable (fun k : ℕ =>
        if 2 * (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) :=
      Summable.of_norm_bounded hsum_du.norm fun k => by split_ifs <;> simp
    have hdu_sub :
        c_UV (d + 1) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          ((∑' k : ℕ, if (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
            (∑' k : ℕ, if 2 * (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0)) =
          ∑' k : ℕ, g_du d k := by
      rw [← hdu1.tsum_sub hdu2, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      dsimp only [g_du]; split_ifs <;> ring
    have hdiff : ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s) =
        ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * riemannZeta s -
          (2 : ℂ) ^ (-(1 - s)) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * riemannZeta s := by ring
    dsimp only [w_d]
    calc c_UV (d + 1) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
            smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)
        = c_UV (d + 1) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
            (((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)) := by ring
      _ = c_UV (d + 1) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
            (((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
                ((∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
                    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) * x)))) -
                  (2 : ℂ) ^ (-(1 - s)) *
                    (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
                      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * ((d + 1 : ℕ) : ℝ) * x))))) -
              ((∑' k : ℕ, if (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
                (∑' k : ℕ, if 2 * (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0))) := by
          rw [hdiff, h1, h2]; ring
      _ = c_UV (d + 1) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
            smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) * smoothOuterDirectPairSum s x (d + 1) -
          ∑' k : ℕ, g_du d k := by rw [hdir_sub, mul_sub, ← hdu_sub]; ring
  obtain ⟨K₆, hK₆0, hK₆⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 6) (by norm_num)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  have hcW_le : ∀ d : ℕ,
      ‖c_UV (d + 1)‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ ≤
        (4 * K₆ * Y ^ (6 : ℝ)) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ := by
    intro d
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have hc_bd : ‖c_UV (d + 1)‖ ≤ 4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      dsimp only [c_UV]
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
      exact abs_vaughanTypeIICoeff_le_four_mul_sq U V (d + 1) hd1
    have hW := norm_smoothAFECutoff_div_le' hK₆ hd_pos hY
    have hrp : ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ =
        (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos,
        show (2 : ℝ) + (-6 : ℝ) = -4 by norm_num, Real.rpow_neg hd_pos.le]
    calc ‖c_UV (d + 1)‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
        ≤ (4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) *
            (K₆ * ((((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ))) :=
          mul_le_mul hc_bd hW (norm_nonneg _) (by positivity)
      _ = (4 * K₆ * Y ^ (6 : ℝ)) *
            (((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹) := by ring
      _ = (4 * K₆ * Y ^ (6 : ℝ)) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ := by rw [hrp]
  have hdir_sum : Summable (fun d : ℕ => w_d d * smoothOuterDirectPairSum s x (d + 1)) := by
    set C_p : ℝ := (1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2 * x ^ (2 : ℝ)
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (4 * K₆ * Y ^ (6 : ℝ) * C_p))
      fun d => ?_
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have hd1_le : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
      rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by simp; linarith)
    have hp := norm_smoothOuterDirectPairSum_le (le_refl 2) hK₂0 hK₂ hs0 hhi hx hd1
    rw [Real.mul_rpow hd_pos.le hx.le] at hp
    have hp' : ‖smoothOuterDirectPairSum s x (d + 1)‖ ≤ C_p * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      dsimp only [C_p]; linarith
    have hrpow_cancel : (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos,
        show (-4 : ℝ) + 2 = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
      push_cast; rfl
    dsimp only [w_d]
    rw [norm_mul, norm_mul, norm_mul,
      show ‖c_UV (d + 1)‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ *
          ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ =
        (‖c_UV (d + 1)‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖) *
          ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ by ring]
    calc ((‖c_UV (d + 1)‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖) *
            ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖) * ‖smoothOuterDirectPairSum s x (d + 1)‖
        ≤ (((4 * K₆ * Y ^ (6 : ℝ)) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹) * 1) *
            (C_p * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
          mul_le_mul
            (mul_le_mul (hcW_le d) hd1_le (norm_nonneg _) (by positivity))
            hp' (norm_nonneg _) (by positivity)
      _ = (4 * K₆ * Y ^ (6 : ℝ) * C_p) *
            ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) := by ring
      _ = (4 * K₆ * Y ^ (6 : ℝ) * C_p) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]
  set A_d : ℕ → ℝ := fun d => (4 * K₆ * Y ^ (6 : ℝ)) * (1 / (d + 1 : ℝ) ^ (4 : ℝ))
  set B_k : ℕ → ℝ := fun k => 2 * ‖smoothAFEZetaDualCoefficientGeneral s x k‖
  have hA_sum : Summable A_d :=
    (summable_smoothAFEZetaMajorant (p := 4) (by norm_num)).mul_left (4 * K₆ * Y ^ (6 : ℝ))
  have hB_sum : Summable B_k := hsum_du.norm.mul_left 2
  have hg_maj : ∀ d k : ℕ, ‖g_du d k‖ ≤ A_d d * B_k k := fun d k => by
    have hite : ‖(if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0) -
        (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
      have h2 : ‖if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
      linarith
    dsimp only [g_du, A_d, B_k]
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖c_UV (d + 1)‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ *
            ‖(if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0) -
              (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)‖ *
            ‖smoothAFEZetaDualCoefficientGeneral s x k‖
        ≤ ((4 * K₆ * Y ^ (6 : ℝ)) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹) * 2 *
            ‖smoothAFEZetaDualCoefficientGeneral s x k‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (hcW_le d) hite (norm_nonneg _) (by positivity))
            (norm_nonneg _)
      _ = ((4 * K₆ * Y ^ (6 : ℝ)) * (1 / (d + 1 : ℝ) ^ (4 : ℝ))) *
            (2 * ‖smoothAFEZetaDualCoefficientGeneral s x k‖) := by push_cast; ring
  have hg_uncurry : Summable (Function.uncurry g_du) :=
    Summable.of_norm_bounded
      (hA_sum.mul_of_nonneg hB_sum (fun _ => by dsimp only [A_d]; positivity)
        (fun _ => by dsimp only [B_k]; positivity))
      fun p => hg_maj p.1 p.2
  have hg_row : ∀ d : ℕ, Summable (fun k : ℕ => g_du d k) := fun d =>
    Summable.of_norm_bounded (hB_sum.mul_left (A_d d)) (fun k => hg_maj d k)
  have hg_col : ∀ k : ℕ, Summable (fun d : ℕ => g_du d k) := fun k =>
    Summable.of_norm_bounded (hA_sum.mul_right (B_k k)) (fun d => hg_maj d k)
  have hg_d_sum : Summable (fun d : ℕ => ∑' k : ℕ, g_du d k) := by
    refine Summable.of_norm_bounded (hA_sum.mul_right (∑' k : ℕ, B_k k)) fun d => ?_
    calc ‖∑' k : ℕ, g_du d k‖
        ≤ ∑' k : ℕ, ‖g_du d k‖ := norm_tsum_le_tsum_norm (hg_row d).norm
      _ ≤ ∑' k : ℕ, A_d d * B_k k :=
          Summable.tsum_le_tsum (fun k => hg_maj d k) (hg_row d).norm (hB_sum.mul_left (A_d d))
      _ = A_d d * ∑' k : ℕ, B_k k := tsum_mul_left
  have hcol_eq : ∀ k : ℕ,
      (∑' d : ℕ, g_du d k) =
        smoothOuterVaughanDualSieveCoeff U V Y (k + 1) *
          smoothAFEZetaDualCoefficientGeneral s x k := by
    intro k
    have hfin : ∀ d : ℕ, k + 1 ≤ d → g_du d k = 0 := fun d hkd => by
      have hnd1 : ¬ ((d + 1) ∣ (k + 1)) := fun h => by
        have := Nat.le_of_dvd (Nat.succ_pos k) h; omega
      have hnd2 : ¬ (2 * (d + 1) ∣ (k + 1)) := fun h => by
        have := Nat.le_of_dvd (Nat.succ_pos k) h; omega
      dsimp only [g_du]; rw [if_neg hnd1, if_neg hnd2]; ring
    rw [tsum_eq_sum (s := Finset.range (k + 1)) fun d hd =>
      hfin d (Nat.le_of_not_lt (Finset.mem_range.not.mp hd))]
    dsimp only [g_du]
    rw [← Finset.sum_mul]
    congr 1
    unfold smoothOuterVaughanDualSieveCoeff
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    · have h1 :
          (∑ d ∈ Finset.range (k + 1),
            c_UV (d + 1) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
              (if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)) =
          ∑ q ∈ Finset.Icc 1 (k + 1),
            if q ∣ (k + 1) then c_UV q * smoothAFECutoff ((q : ℝ) / Y) else 0 := by
        refine Finset.sum_bij (fun d _ => d + 1)
          (fun d hd => Finset.mem_Icc.mpr ⟨Nat.succ_pos d, by have := Finset.mem_range.mp hd; omega⟩)
          (fun _ _ _ _ h => by omega)
          (fun q hq => ⟨q - 1, Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hq; omega),
            by have := Finset.mem_Icc.mp hq; omega⟩)
          (fun d _ => by split_ifs <;> ring)
      rw [h1, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨fun ⟨⟨_, _⟩, hdv⟩ => ⟨hdv, Nat.succ_ne_zero k⟩,
        fun ⟨hdv, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hdv (Nat.succ_pos k),
          Nat.le_of_dvd (Nat.succ_pos k) hdv⟩, hdv⟩⟩
    · by_cases h2k : 2 ∣ (k + 1)
      · rw [if_pos h2k]
        have hm_pos : 0 < (k + 1) / 2 := by obtain ⟨c, hc⟩ := h2k; omega
        have h2 :
            (∑ d ∈ Finset.range (k + 1),
              c_UV (d + 1) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
                (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)) =
            ∑ q ∈ Finset.Icc 1 (k + 1),
              if q ∣ ((k + 1) / 2) then c_UV q * smoothAFECutoff ((q : ℝ) / Y) else 0 := by
          refine Finset.sum_bij (fun d _ => d + 1)
            (fun d hd => Finset.mem_Icc.mpr ⟨Nat.succ_pos d, by have := Finset.mem_range.mp hd; omega⟩)
            (fun _ _ _ _ h => by omega)
            (fun q hq => ⟨q - 1, Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hq; omega),
              by have := Finset.mem_Icc.mp hq; omega⟩)
            (fun d _ => ?_)
          have hdvd_iff : (2 * (d + 1) ∣ (k + 1)) ↔ ((d + 1) ∣ ((k + 1) / 2)) := by
            obtain ⟨m, hm⟩ := h2k
            rw [hm, Nat.mul_div_cancel_left m two_pos]
            exact ⟨fun h => (mul_dvd_mul_iff_left (by omega : 2 ≠ 0)).mp h,
              fun h => mul_dvd_mul_left 2 h⟩
          by_cases hd2 : 2 * (d + 1) ∣ (k + 1)
          · rw [if_pos hd2, if_pos (hdvd_iff.mp hd2), mul_one]
          · rw [if_neg hd2, if_neg (mt hdvd_iff.mpr hd2), mul_zero]
        rw [h2, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨fun ⟨⟨_, _⟩, hdv⟩ => ⟨hdv, hm_pos.ne'⟩,
          fun ⟨hdv, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hdv hm_pos,
            (Nat.le_of_dvd hm_pos hdv).trans (Nat.div_le_self (k + 1) 2)⟩, hdv⟩⟩
      · rw [if_neg h2k]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hnd : ¬ (2 * (d + 1) ∣ (k + 1)) := fun h => h2k (dvd_of_mul_right_dvd h)
        rw [if_neg hnd, mul_zero]
  have hsum_lhs :
      (∑' d : ℕ, w_d d * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)) =
        (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s *
          smoothOuterVaughanTypeIISeries U V Y (1 - s) := by
    rw [tsum_mul_right]
    unfold smoothOuterVaughanTypeIISeries
    dsimp only [w_d, c_UV]; ring
  have hsum_all :
      (∑' d : ℕ, w_d d * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)) =
        ∑' d : ℕ, (w_d d * smoothOuterDirectPairSum s x (d + 1) - ∑' k : ℕ, g_du d k) :=
    tsum_congr hterm_d
  rw [hsum_lhs, hdir_sum.tsum_sub hg_d_sum,
    (hg_uncurry.tsum_comm' hg_row hg_col).symm, tsum_congr hcol_eq] at hsum_all
  have hII_eq :
      (∑' d : ℕ, w_d d * smoothOuterDirectPairSum s x (d + 1)) =
        smoothOuterVaughanTypeII U V s x Y := rfl
  rw [hII_eq] at hsum_all
  linear_combination -hsum_all

end Part2VaughanTypeIIDualSieveIdentity


/-! ### Part 3: Unsmoothed Balanced Dual Bilinear Band Localization and Witness Production on `Ω_open` -/

section Part3BalancedDualBilinearBand

/-- Finite unsmoothed balanced dual bilinear band sum on `(U + 1) * (V + 1) ≤ k ≤ K_hi`,
whose coefficients `parityClearedVaughanDualBilinear U V k` contain zero unbounded Möbius and
annihilate every prime `p` and every `m * p` (`m ≤ min U V`) identically. -/
def balancedDualBilinearBandSum (U V K_hi : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi,
    parityClearedVaughanDualBilinear U V k *
      smoothAFEZetaDualCoefficientGeneral s x (k - 1)

/-- Uniform global unsmoothing bound across all `k ≥ 1` simultaneously on `Ω_open`:
choosing `2 * r = B + 4` cancels `-(3 + η) B` against `(1 + η) (2 r)` in `|Im s|`, leaving
`(-B + 4 η + 9 / 2) ≤ -B_dec`. -/
private lemma exists_vaughanDual_unsmoothing_error_le {η B_dec : ℝ} (hη1 : 1 ≤ η) (hB_pos : 0 < B_dec) :
    ∃ C_unsm : ℝ, 0 < C_unsm ∧
      ∀ {s : ℂ}, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∀ (U V : ℕ),
          ‖∑' k : ℕ,
              (smoothOuterVaughanDualSieveCoeff U V (|s.im| ^ (3 + η)) (k + 1) -
                parityClearedVaughanDualBilinear U V (k + 1)) *
              smoothAFEZetaDualCoefficientGeneral s (|s.im| ^ (-(1 + η))) k‖ ≤
            C_unsm * |s.im| ^ (-B_dec) := by
  have hnum_pos : 0 < (4 * η + 17 / 2 + B_dec) / 2 := by linarith
  set r₀ : ℕ := Nat.ceil ((4 * η + 17 / 2 + B_dec) / 2)
  have hr₀_pos : (0 : ℝ) < (r₀ : ℝ) := hnum_pos.trans_le (Nat.le_ceil _)
  have hr₀_bd : 4 * η + 17 / 2 + B_dec ≤ 2 * (r₀ : ℝ) := by
    have hc : (4 * η + 17 / 2 + B_dec) / 2 ≤ (r₀ : ℝ) := Nat.le_ceil _
    linarith [(div_le_iff₀ two_pos).mp hc]
  set B : ℝ := 2 * (r₀ : ℝ)
  set r : ℕ := r₀ + 2
  have hB0 : 0 < B := mul_pos two_pos hr₀_pos
  obtain ⟨K_B, hKB0, hKB⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow hB0
  obtain ⟨K_dual, hKdual_pos, hKdual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := r) (by omega)
  set S_32 : ℝ := smoothAFEZetaMajorant (3 / 2)
  have hS32_nn : 0 ≤ S_32 := tsum_nonneg fun _ => by positivity
  set C_unsm : ℝ := 8 * K_B * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_32 + 1
  refine ⟨C_unsm, by dsimp only [C_unsm]; positivity, fun {s} hlo hhi him U V => ?_⟩
  set τ : ℝ := |s.im|
  have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  set x : ℝ := τ ^ (-(1 + η))
  set Y : ℝ := τ ^ (3 + η)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hτ_pos _
  set P_fac : ℝ := 8 * K_B * K_dual * Y ^ (-B) * x ^ (-2 * (r : ℝ)) *
    (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
  have hP_nn : 0 ≤ P_fac := by dsimp only [P_fac]; positivity
  have hpt_k : ∀ k : ℕ,
      ‖(smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
          parityClearedVaughanDualBilinear U V (k + 1)) *
        smoothAFEZetaDualCoefficientGeneral s x k‖ ≤
        P_fac * (1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
    intro k
    have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
    have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    have hsub := norm_smoothOuterVaughanDualSieveCoeff_sub_parityCleared_le
      U V hB0 hKB0 hKB hY_pos hk1
    have hId := (hKdual s x hlo hhi hx_pos).1 k
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl] at hId
    have hk_comb : ((k + 1 : ℕ) : ℝ) ^ (3 + B) *
        ((k + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) ≤ 1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hk_pos,
        show 3 + B + -(2 * (r : ℝ) + 1 - s.re) = s.re - 2 by
          dsimp only [B, r]; push_cast; ring]
      calc ((k + 1 : ℕ) : ℝ) ^ (s.re - 2)
          ≤ ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) (by linarith)
        _ = 1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ) := by
            rw [Real.rpow_neg hk_pos.le, one_div]; push_cast; rfl
    rw [norm_mul]
    calc ‖smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
            parityClearedVaughanDualBilinear U V (k + 1)‖ *
          ‖smoothAFEZetaDualCoefficientGeneral s x k‖
        ≤ (8 * K_B * ((k + 1 : ℕ) : ℝ) ^ (3 + B) * Y ^ (-B)) *
            (K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              ((k + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) :=
          mul_le_mul hsub hId (norm_nonneg _) (by positivity)
      _ = P_fac * (((k + 1 : ℕ) : ℝ) ^ (3 + B) *
            ((k + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) := by dsimp only [P_fac]; ring
      _ ≤ P_fac * (1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hk_comb hP_nn
  have hmaj_sum := (summable_smoothAFEZetaMajorant (p := 3 / 2) (by norm_num)).mul_left P_fac
  have hs_diff : Summable (fun k : ℕ =>
      (smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
        parityClearedVaughanDualBilinear U V (k + 1)) *
        smoothAFEZetaDualCoefficientGeneral s x k) :=
    Summable.of_norm_bounded hmaj_sum hpt_k
  have hts_le :
      ‖∑' k : ℕ, (smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
          parityClearedVaughanDualBilinear U V (k + 1)) *
        smoothAFEZetaDualCoefficientGeneral s x k‖ ≤ P_fac * S_32 :=
    (norm_tsum_le_tsum_norm hs_diff.norm).trans
      ((Summable.tsum_le_tsum hpt_k hs_diff.norm hmaj_sum).trans_eq tsum_mul_left)
  have h1τ_pow : (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) ≤
      (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2) := by
    have hexp_le : (2 * r : ℝ) + 1 / 2 - s.re ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
        ≤ (2 * τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (2 : ℝ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.mul_rpow two_pos.le hτ_pos.le
      _ ≤ (2 : ℝ) ^ (((2 * r + 1 : ℕ) : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le one_lt_two.le hexp_le)
            (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2) := by rw [Real.rpow_natCast]
  have hτ_exp :
      Y ^ (-B) * x ^ (-2 * (r : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) ≤ τ ^ (-B_dec) := by
    dsimp only [Y, x, B, r]
    rw [← Real.rpow_mul hτ_pos.le, ← Real.rpow_mul hτ_pos.le,
      ← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
    refine Real.rpow_le_rpow_of_exponent_le hτ1 ?_
    have hid : (3 + η) * -(2 * (r₀ : ℝ)) + -(1 + η) * (-2 * ((r₀ + 2 : ℕ) : ℝ)) +
        (2 * ((r₀ + 2 : ℕ) : ℝ) + 1 / 2) =
        4 * η + 17 / 2 - 2 * (r₀ : ℝ) := by push_cast; ring
    dsimp only [B] at hr₀_bd
    rw [hid]
    linarith
  calc ‖∑' k : ℕ, (smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
          parityClearedVaughanDualBilinear U V (k + 1)) *
        smoothAFEZetaDualCoefficientGeneral s x k‖
      ≤ P_fac * S_32 := hts_le
    _ ≤ (8 * K_B * K_dual * Y ^ (-B) * x ^ (-2 * (r : ℝ)) *
          ((2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2))) * S_32 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1τ_pow (by positivity)) hS32_nn
    _ = (8 * K_B * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_32) *
          (Y ^ (-B) * x ^ (-2 * (r : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2)) := by ring
    _ ≤ C_unsm * τ ^ (-B_dec) := by
        have h1 := mul_le_mul_of_nonneg_left hτ_exp
          (show 0 ≤ 8 * K_B * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_32 by positivity)
        have hnn : 0 ≤ τ ^ (-B_dec) := Real.rpow_nonneg hτ_pos.le _
        dsimp only [C_unsm]; linarith

/-- Uniform rapid dual tail bound beyond `K_hi = ⌈|Im s|^{2 + η + δ}⌉₊` across `Ω_open`. -/
private lemma exists_parityClearedVaughanDual_tail_le
    {η δ B_dec : ℝ} (_hη1 : 1 ≤ η) (hδ_pos : 0 < δ) (_hB_pos : 0 < B_dec) :
    ∃ C_tail_hi : ℝ, 0 < C_tail_hi ∧
      ∀ {s : ℂ}, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        let K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
        ∀ (U V : ℕ),
          ‖∑' j : ℕ,
              parityClearedVaughanDualBilinear U V (j + K_hi + 1) *
                smoothAFEZetaDualCoefficientGeneral s (|s.im| ^ (-(1 + η))) (j + K_hi)‖ ≤
            C_tail_hi * |s.im| ^ (-B_dec) := by
  set r₁ : ℕ := Nat.ceil ((6 * (2 + η) + 7 / 2 + B_dec) / (2 * δ))
  have hr₁_bd : 6 * (2 + η) + 7 / 2 + B_dec ≤ 2 * δ * (r₁ : ℝ) := by
    have hc : (6 * (2 + η) + 7 / 2 + B_dec) / (2 * δ) ≤ (r₁ : ℝ) := Nat.le_ceil _
    linarith [(div_le_iff₀ (by positivity : 0 < 2 * δ)).mp hc]
  set r : ℕ := r₁ + 3
  obtain ⟨K_dual, hKdual_pos, hKdual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := r) (by omega)
  set S_2 : ℝ := smoothAFEZetaMajorant 2
  have hS2_nn : 0 ≤ S_2 := tsum_nonneg fun _ => by positivity
  set C_tail_hi : ℝ := 8 * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_2 + 1
  refine ⟨C_tail_hi, by dsimp only [C_tail_hi]; positivity, fun {s} hlo hhi him => ?_⟩
  dsimp only
  intro U V
  set τ : ℝ := |s.im|
  have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  set x : ℝ := τ ^ (-(1 + η))
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  set K_hi : ℕ := Nat.ceil (τ ^ (2 + η + δ))
  set P_hi : ℝ := 8 * K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
    τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ))
  have hP_nn : 0 ≤ P_hi := by dsimp only [P_hi]; positivity
  have hpt_j : ∀ j : ℕ,
      ‖parityClearedVaughanDualBilinear U V (j + K_hi + 1) *
          smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)‖ ≤
        P_hi * (1 / (j + 1 : ℝ) ^ (2 : ℝ)) := by
    intro j
    set q : ℕ := j + K_hi + 1
    have hq1 : 1 ≤ q := by dsimp only [q]; omega
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hq_ge : τ ^ (2 + η + δ) ≤ (q : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by dsimp only [q]; omega : K_hi ≤ q))
    have hc_bd : ‖parityClearedVaughanDualBilinear U V q‖ ≤ 8 * (q : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      exact norm_parityClearedVaughanDualBilinear_le_eight_mul_sq U V q
    have hId := (hKdual s x hlo hhi hx_pos).1 (j + K_hi)
    rw [show ((j + K_hi : ℕ) : ℝ) + 1 = (q : ℝ) by dsimp only [q]; push_cast; ring] at hId
    have hq_comb : (q : ℝ) ^ (2 : ℝ) * (q : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) ≤
        τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ)) * (1 / (j + 1 : ℝ) ^ (2 : ℝ)) := by
      rw [← Real.rpow_add hq_pos,
        show (2 : ℝ) + -(2 * (r : ℝ) + 1 - s.re) = (-(2 * (r₁ : ℝ))) + (s.re - 5) by
          dsimp only [r]; push_cast; ring,
        Real.rpow_add hq_pos]
      have h1 : (q : ℝ) ^ (-(2 * (r₁ : ℝ))) ≤ τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ)) :=
        (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτ_pos _) hq_ge
          (neg_nonpos.mpr (by positivity))).trans_eq
          (by rw [← Real.rpow_mul hτ_pos.le]; congr 1; ring)
      have hjq : (j + 1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by dsimp only [q]; omega : j + 1 ≤ q)
      have h2 : (q : ℝ) ^ (s.re - 5) ≤ 1 / (j + 1 : ℝ) ^ (2 : ℝ) := by
        have ha : (q : ℝ) ^ (s.re - 5) ≤ (q : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1) (by linarith)
        have hb : (q : ℝ) ^ (-2 : ℝ) ≤ (j + 1 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hjq (by norm_num)
        exact (ha.trans hb).trans_eq (by rw [Real.rpow_neg (by positivity), one_div])
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    change ‖parityClearedVaughanDualBilinear U V q *
      smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)‖ ≤ _
    rw [norm_mul]
    calc ‖parityClearedVaughanDualBilinear U V q‖ *
            ‖smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)‖
        ≤ (8 * (q : ℝ) ^ (2 : ℝ)) *
            (K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              (q : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) :=
          mul_le_mul hc_bd hId (norm_nonneg _) (by positivity)
      _ = (8 * K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)) *
            ((q : ℝ) ^ (2 : ℝ) * (q : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) := by ring
      _ ≤ (8 * K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)) *
            (τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ)) * (1 / (j + 1 : ℝ) ^ (2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hq_comb (by positivity)
      _ = P_hi * (1 / (j + 1 : ℝ) ^ (2 : ℝ)) := by dsimp only [P_hi]; ring
  have hmaj_hi := (summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left P_hi
  have hs_tail : Summable (fun j : ℕ =>
      parityClearedVaughanDualBilinear U V (j + K_hi + 1) *
        smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)) :=
    Summable.of_norm_bounded hmaj_hi hpt_j
  have hts_le :
      ‖∑' j : ℕ, parityClearedVaughanDualBilinear U V (j + K_hi + 1) *
          smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)‖ ≤ P_hi * S_2 :=
    (norm_tsum_le_tsum_norm hs_tail.norm).trans
      ((Summable.tsum_le_tsum hpt_j hs_tail.norm hmaj_hi).trans_eq tsum_mul_left)
  have h1τ_pow : (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) ≤
      (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2) := by
    have hexp_le : (2 * r : ℝ) + 1 / 2 - s.re ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
        ≤ (2 * τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (2 : ℝ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.mul_rpow two_pos.le hτ_pos.le
      _ ≤ (2 : ℝ) ^ (((2 * r + 1 : ℕ) : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le one_lt_two.le hexp_le)
            (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2) := by rw [Real.rpow_natCast]
  have hτ_exp :
      x ^ (-2 * (r : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) *
        τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ)) ≤ τ ^ (-B_dec) := by
    dsimp only [x, r]
    rw [← Real.rpow_mul hτ_pos.le, ← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
    refine Real.rpow_le_rpow_of_exponent_le hτ1 ?_
    have hid : -(1 + η) * (-2 * ((r₁ + 3 : ℕ) : ℝ)) + (2 * ((r₁ + 3 : ℕ) : ℝ) + 1 / 2) +
        -(2 * (r₁ : ℝ)) * (2 + η + δ) =
        6 * (2 + η) + 1 / 2 - 2 * δ * (r₁ : ℝ) := by push_cast; ring
    rw [hid]
    linarith
  calc ‖∑' j : ℕ, parityClearedVaughanDualBilinear U V (j + K_hi + 1) *
          smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)‖
      ≤ P_hi * S_2 := hts_le
    _ ≤ (8 * K_dual * x ^ (-2 * (r : ℝ)) *
          ((2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2)) *
          τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ))) * S_2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1τ_pow (by positivity)) (by positivity))
          hS2_nn
    _ = (8 * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_2) *
          (x ^ (-2 * (r : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) *
            τ ^ (-(2 * (r₁ : ℝ)) * (2 + η + δ))) := by ring
    _ ≤ C_tail_hi * τ ^ (-B_dec) := by
        have h1 := mul_le_mul_of_nonneg_left hτ_exp
          (show 0 ≤ 8 * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_2 by positivity)
        have hnn : 0 ≤ τ ^ (-B_dec) := Real.rpow_nonneg hτ_pos.le _
        dsimp only [C_tail_hi]; linarith

/-- **Unsmoothed finite balanced dual bilinear band localization across ALL of `Ω_open`:**
for every `η ≥ 1` and `δ > 0`, setting `x(s) = |Im s|^{-(1 + η)}`, `Y(s) = |Im s|^{3 + η}`, and
`K_hi(s) = ⌈|Im s|^{2 + η + δ}⌉₊`, there exists `C_band > 0` such that at **every** point
`s ∈ Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`) and for **all** `1 ≤ U, V` with
`U * V ≤ |Im s|^{η - 1 / 2}`, the `ζ(s)`-multiples
`ζ(s) * smoothOuterMoebiusSeries Y (1 - s) - (1 - 2^{-(1 - s)}) ζ(s) * smoothOuterVaughanTypeIISeries U V Y (1 - s)`
equal `(1 - 2^{-(1 - s)}) zetaChi(s) + balancedDualBilinearBandSum U V K_hi s x` within
`≤ C_band * |Im s|^{-1 / 4}`. -/
theorem exists_balancedDualBilinearBand_duality_on_remaining_strip
    {η δ : ℝ} (hη1 : 1 ≤ η) (hδ_pos : 0 < δ) :
    ∃ C_band : ℝ, 0 < C_band ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        let x : ℝ := |s.im| ^ (-(1 + η))
        let Y : ℝ := |s.im| ^ (3 + η)
        let K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
        ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
          ‖(riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
              (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s *
                smoothOuterVaughanTypeIISeries U V Y (1 - s)) -
            ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s +
              balancedDualBilinearBandSum U V K_hi s x)‖ ≤
            C_band * |s.im| ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C_du, hCdu_pos, hCdu⟩ :=
    exists_pure_vaughanTypeII_crossHeight_duality_on_remaining_strip hη1
  obtain ⟨C_unsm, hCunsm_pos, hCunsm⟩ :=
    exists_vaughanDual_unsmoothing_error_le hη1 (B_dec := 1 / 4) (by norm_num)
  obtain ⟨C_tail_hi, hCtail_hi_pos, hCtail_hi⟩ :=
    exists_parityClearedVaughanDual_tail_le hη1 hδ_pos (B_dec := 1 / 4) (by norm_num)
  set C_band : ℝ := C_du + C_unsm + C_tail_hi + 1
  refine ⟨C_band, by dsimp only [C_band]; positivity, ?_⟩
  intro s hlo hhi him
  dsimp only
  intro U V hU1 hV1 hUV_bd
  set τ : ℝ := |s.im|
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  have hs0 : 0 < s.re := by linarith
  set x : ℝ := τ ^ (-(1 + η))
  set Y : ℝ := τ ^ (3 + η)
  set K_hi : ℕ := Nat.ceil (τ ^ (2 + η + δ))
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hτ_pos _
  -- Summability of both the smoothed and unsmoothed dual series at `(s, x)`.
  obtain ⟨K_d2, hKd2_pos, hK_d2⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := 2) (by omega)
  set C_d2 : ℝ := K_d2 * x ^ (-2 * ((2 : ℕ) : ℝ)) * (1 + τ) ^ (2 * ((2 : ℕ) : ℝ) + 1 / 2 - s.re)
  have hs_unsm : Summable (fun k : ℕ =>
      parityClearedVaughanDualBilinear U V (k + 1) *
        smoothAFEZetaDualCoefficientGeneral s x k) := by
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 3 / 2) (by norm_num)).mul_left (8 * C_d2))
      fun k => ?_
    have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
    have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    have hc := norm_parityClearedVaughanDualBilinear_le_eight_mul_sq U V (k + 1)
    rw [← Real.rpow_two] at hc
    have hId := (hK_d2 s x hlo hhi hx_pos).1 k
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl] at hId
    have hk_comb : ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) *
        ((k + 1 : ℕ) : ℝ) ^ (-(2 * ((2 : ℕ) : ℝ) + 1 - s.re)) ≤
        1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hk_pos,
        show (2 : ℝ) + -(2 * ((2 : ℕ) : ℝ) + 1 - s.re) = s.re - 3 by push_cast; ring]
      calc ((k + 1 : ℕ) : ℝ) ^ (s.re - 3)
          ≤ ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) (by linarith)
        _ = 1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ) := by
            rw [Real.rpow_neg hk_pos.le, one_div]; push_cast; rfl
    rw [norm_mul]
    calc ‖parityClearedVaughanDualBilinear U V (k + 1)‖ *
            ‖smoothAFEZetaDualCoefficientGeneral s x k‖
        ≤ (8 * ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ)) *
            (C_d2 * ((k + 1 : ℕ) : ℝ) ^ (-(2 * ((2 : ℕ) : ℝ) + 1 - s.re))) :=
          mul_le_mul hc hId (norm_nonneg _) (by positivity)
      _ = (8 * C_d2) * (((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) *
            ((k + 1 : ℕ) : ℝ) ^ (-(2 * ((2 : ℕ) : ℝ) + 1 - s.re))) := by ring
      _ ≤ (8 * C_d2) * (1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hk_comb (by dsimp only [C_d2]; positivity)
  have hs_diff : Summable (fun k : ℕ =>
      (smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
        parityClearedVaughanDualBilinear U V (k + 1)) *
        smoothAFEZetaDualCoefficientGeneral s x k) := by
    obtain ⟨K_B1, hKB10, hKB1⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1) one_pos
    obtain ⟨K_d3, hKd3_pos, hK_d3⟩ :=
      exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
        (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := 3) (by omega)
    set C_d3 : ℝ := K_d3 * x ^ (-2 * ((3 : ℕ) : ℝ)) * (1 + τ) ^ (2 * ((3 : ℕ) : ℝ) + 1 / 2 - s.re)
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 3 / 2) (by norm_num)).mul_left
        (8 * K_B1 * Y ^ (-1 : ℝ) * C_d3))
      fun k => ?_
    have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
    have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    have hsub := norm_smoothOuterVaughanDualSieveCoeff_sub_parityCleared_le
      U V one_pos hKB10 hKB1 hY_pos hk1
    have hId := (hK_d3 s x hlo hhi hx_pos).1 k
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl] at hId
    have hk_comb : ((k + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1) *
        ((k + 1 : ℕ) : ℝ) ^ (-(2 * ((3 : ℕ) : ℝ) + 1 - s.re)) ≤
        1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hk_pos,
        show (3 : ℝ) + 1 + -(2 * ((3 : ℕ) : ℝ) + 1 - s.re) = s.re - 3 by push_cast; ring]
      calc ((k + 1 : ℕ) : ℝ) ^ (s.re - 3)
          ≤ ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) (by linarith)
        _ = 1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ) := by
            rw [Real.rpow_neg hk_pos.le, one_div]; push_cast; rfl
    rw [norm_mul]
    calc ‖smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
            parityClearedVaughanDualBilinear U V (k + 1)‖ *
          ‖smoothAFEZetaDualCoefficientGeneral s x k‖
        ≤ (8 * K_B1 * ((k + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1) * Y ^ (-1 : ℝ)) *
            (C_d3 * ((k + 1 : ℕ) : ℝ) ^ (-(2 * ((3 : ℕ) : ℝ) + 1 - s.re))) :=
          mul_le_mul hsub hId (norm_nonneg _) (by positivity)
      _ = (8 * K_B1 * Y ^ (-1 : ℝ) * C_d3) * (((k + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1) *
            ((k + 1 : ℕ) : ℝ) ^ (-(2 * ((3 : ℕ) : ℝ) + 1 - s.re))) := by ring
      _ ≤ (8 * K_B1 * Y ^ (-1 : ℝ) * C_d3) * (1 / (k + 1 : ℝ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hk_comb (by dsimp only [C_d3]; positivity)
  have hsm_split :
      (∑' k : ℕ, smoothOuterVaughanDualSieveCoeff U V Y (k + 1) *
          smoothAFEZetaDualCoefficientGeneral s x k) =
        (∑' k : ℕ, (smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
            parityClearedVaughanDualBilinear U V (k + 1)) *
          smoothAFEZetaDualCoefficientGeneral s x k) +
        ∑' k : ℕ, parityClearedVaughanDualBilinear U V (k + 1) *
          smoothAFEZetaDualCoefficientGeneral s x k := by
    rw [← hs_diff.tsum_add hs_unsm]
    exact tsum_congr fun k => by ring
  -- Identify `∑ k ∈ range K_hi, parityClearedVaughanDualBilinear U V (k + 1) * I(s, x, k)` with `balancedDualBilinearBandSum`
  -- because `parityClearedVaughanDualBilinear U V q = 0` for all `q < (U + 1) * (V + 1)`.
  have hrange_eq_band :
      (∑ k ∈ Finset.range K_hi,
          parityClearedVaughanDualBilinear U V (k + 1) *
            smoothAFEZetaDualCoefficientGeneral s x k) =
        balancedDualBilinearBandSum U V K_hi s x := by
    have hbij :
        (∑ k ∈ Finset.range K_hi,
            parityClearedVaughanDualBilinear U V (k + 1) *
              smoothAFEZetaDualCoefficientGeneral s x k) =
          ∑ q ∈ Finset.Icc 1 K_hi,
            parityClearedVaughanDualBilinear U V q *
              smoothAFEZetaDualCoefficientGeneral s x (q - 1) := by
      refine Finset.sum_bij (fun k _ => k + 1)
        (fun k hk => Finset.mem_Icc.mpr ⟨Nat.succ_pos k, by have := Finset.mem_range.mp hk; omega⟩)
        (fun _ _ _ _ h => by omega)
        (fun q hq => ⟨q - 1, Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hq; omega),
          by have := Finset.mem_Icc.mp hq; omega⟩)
        (fun _ _ => rfl)
    rw [hbij]
    unfold balancedDualBilinearBandSum
    symm
    refine Finset.sum_subset
      (fun q hq => Finset.mem_Icc.mpr
        ⟨(Nat.mul_pos (Nat.succ_pos U) (Nat.succ_pos V)).trans_le (Finset.mem_Icc.mp hq).1,
          (Finset.mem_Icc.mp hq).2⟩)
      fun q hq1 hnot => ?_
    have hlt : q < (U + 1) * (V + 1) := by
      by_contra hge
      exact hnot (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hq1).2⟩)
    rw [parityClearedVaughanDualBilinear_eq_zero_of_lt_succ_mul_succ hlt, zero_mul]
  have hunsm_split := (hs_unsm.sum_add_tsum_nat_add K_hi).symm
  rw [hrange_eq_band] at hunsm_split
  have hII_dual := smoothOuterVaughanTypeII_eq_zeta_mul_add_dual_sieve U V hx_pos hY_pos hs0 hhi
  set E_du : ℂ := riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
    ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + smoothOuterVaughanTypeII U V s x Y)
  set E_unsm : ℂ := ∑' k : ℕ,
    (smoothOuterVaughanDualSieveCoeff U V Y (k + 1) -
      parityClearedVaughanDualBilinear U V (k + 1)) *
      smoothAFEZetaDualCoefficientGeneral s x k
  set E_tail : ℂ := ∑' j : ℕ,
    parityClearedVaughanDualBilinear U V (j + K_hi + 1) *
      smoothAFEZetaDualCoefficientGeneral s x (j + K_hi)
  have halg :
      (riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
        (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s *
          smoothOuterVaughanTypeIISeries U V Y (1 - s)) -
      ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s +
        balancedDualBilinearBandSum U V K_hi s x) =
      E_du + E_unsm + E_tail := by
    dsimp only [E_du, E_unsm, E_tail]
    rw [hII_dual, hsm_split, hunsm_split]
    ring
  rw [halg]
  have hb_du := hCdu s hlo hhi him hU1 hV1 hUV_bd
  have hb_unsm := hCunsm hlo hhi him U V
  have hb_tail := hCtail_hi hlo hhi him U V
  have ht1 := norm_add_le (E_du + E_unsm) E_tail
  have ht2 := norm_add_le E_du E_unsm
  have hnn : 0 ≤ τ ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hτ_pos.le _
  have hring :
      C_du * τ ^ (-(1 / 4 : ℝ)) + C_unsm * τ ^ (-(1 / 4 : ℝ)) +
        C_tail_hi * τ ^ (-(1 / 4 : ℝ)) ≤ C_band * τ ^ (-(1 / 4 : ℝ)) := by
    dsimp only [C_band]
    have h1 :
        C_du * τ ^ (-(1 / 4 : ℝ)) + C_unsm * τ ^ (-(1 / 4 : ℝ)) +
          C_tail_hi * τ ^ (-(1 / 4 : ℝ)) + τ ^ (-(1 / 4 : ℝ)) =
        (C_du + C_unsm + C_tail_hi + 1) * τ ^ (-(1 / 4 : ℝ)) := by ring
    linarith
  linarith

/-- **Pointwise `HasStrictPrimeGasWitness` production from finite balanced dual bilinear band
domination across ALL of `Ω_open`:**
at **every** point `s ∈ Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`) and for **all**
`1 ≤ U, V` with `U * V ≤ |Im s|^{η - 1 / 2}`:
1. If `ζ(s) = 0`, the finite unsmoothed balanced dual bilinear band sum on
   `(U + 1)(V + 1) ≤ k ≤ ⌈|Im s|^{2 + η + δ}⌉₊` (which annihilates every prime `p` and every
   `m * p` for `m ≤ min U V` identically) is forced strictly above
   `(1 / 4) * (|Im s| / 7)^{1/2 - Re s} - C_band * |Im s|^{-1 / 4}`.
2. Conversely, whenever that finite balanced dual bilinear band sum does not exceed that bound,
   `s` admits an unconditional `HasStrictPrimeGasWitness`. -/
theorem strict_primeGas_witness_of_balancedDualBilinearBand_domination_on_remaining_strip
    {η δ C_band : ℝ}
    (hband : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      let x : ℝ := |s.im| ^ (-(1 + η))
      let Y : ℝ := |s.im| ^ (3 + η)
      let K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
      ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
        ‖(riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
            (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s *
              smoothOuterVaughanTypeIISeries U V Y (1 - s)) -
          ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s +
            balancedDualBilinearBandSum U V K_hi s x)‖ ≤
          C_band * |s.im| ^ (-(1 / 4 : ℝ)))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {U V : ℕ} (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hUV_bd : ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2)) :
    let x : ℝ := |s.im| ^ (-(1 + η))
    let K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
    (riemannZeta s = 0 →
      (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_band * |s.im| ^ (-(1 / 4 : ℝ)) <
        ‖balancedDualBilinearBandSum U V K_hi s x‖) ∧
    (∀ {L_hor : ℝ}, 0 < L_hor →
      ‖balancedDualBilinearBandSum U V K_hi s x‖ ≤
        (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_band * |s.im| ^ (-(1 / 4 : ℝ)) →
      HasStrictPrimeGasWitness s (by linarith) L_hor) := by
  dsimp only
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  have hpref := one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi
  obtain ⟨_, _, hchi_ge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour hs0 hhi him
  have hchi_pos : 0 < ‖zetaChi s‖ := lt_of_lt_of_le (by positivity) hchi_ge
  have hvac_gt : (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) <
      ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ := by
    rw [norm_mul]
    calc (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re)
        ≤ (1 / 4 : ℝ) * ‖zetaChi s‖ := mul_le_mul_of_nonneg_left hchi_ge (by norm_num)
      _ < ‖1 - (2 : ℂ) ^ (-(1 - s))‖ * ‖zetaChi s‖ := mul_lt_mul_of_pos_right hpref hchi_pos
  have hforced : riemannZeta s = 0 →
      (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_band * |s.im| ^ (-(1 / 4 : ℝ)) <
        ‖balancedDualBilinearBandSum U V (Nat.ceil (|s.im| ^ (2 + η + δ))) s (|s.im| ^ (-(1 + η)))‖ := by
    intro hζ0
    have herr := hband s hlo hhi him hU1 hV1 hUV_bd
    rw [hζ0, zero_mul, mul_zero, zero_mul, sub_zero, zero_sub, norm_neg] at herr
    have htri :
        ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ -
          ‖balancedDualBilinearBandSum U V (Nat.ceil (|s.im| ^ (2 + η + δ))) s (|s.im| ^ (-(1 + η)))‖ ≤
        ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s +
          balancedDualBilinearBandSum U V (Nat.ceil (|s.im| ^ (2 + η + δ))) s (|s.im| ^ (-(1 + η)))‖ := by
      have h := norm_sub_norm_le ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s)
        (-balancedDualBilinearBandSum U V (Nat.ceil (|s.im| ^ (2 + η + δ))) s (|s.im| ^ (-(1 + η))))
      rwa [sub_neg_eq_add, norm_neg] at h
    linarith
  refine ⟨hforced, fun {L_hor} hL_hor hdom => ?_⟩
  refine (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hL_hor).mpr fun hζ0 => ?_
  linarith [hforced hζ0]

/-- **Scale-invariant `T ^ 2` conductor gap law:**
for every `T ≠ 0` and every direct scale `x ≠ 0`, the multiplicative ratio `(T / x) / (T * x)⁻¹`
between the dual analytic horizon `T / x` and the sub-horizon Vaughan Type-I cutoff `(T * x)⁻¹`
equals `T ^ 2` identically, independent of `x`. -/
theorem vaughan_conductor_square_gap_invariance {T x : ℝ} (hT : T ≠ 0) (hx : x ≠ 0) :
    (T / x) / (T * x)⁻¹ = T ^ (2 : ℕ) := by
  field_simp [hT, hx]

/-- **Balanced dual factor window pinning:**
for all `1 ≤ U`, `1 ≤ V`, and every `k ≤ K_hi` with `vaughanDualBilinear U V k ≠ 0`, `k` factors
as `k = a * b` with `(U : ℝ) < (a : ℝ) < (K_hi : ℝ) / (V : ℝ)` and
`(V : ℝ) < (b : ℝ) < (K_hi : ℝ) / (U : ℝ)`. -/
theorem balanced_dual_factor_window_pinning
    {U V K_hi k : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hk_le : k ≤ K_hi)
    (hne : vaughanDualBilinear U V k ≠ 0) :
    ∃ a b : ℕ, a * b = k ∧
      ((U : ℝ) < (a : ℝ) ∧ (a : ℝ) < (K_hi : ℝ) / (V : ℝ)) ∧
      ((V : ℝ) < (b : ℝ) ∧ (b : ℝ) < (K_hi : ℝ) / (U : ℝ)) := by
  obtain ⟨a, b, hab, hUa, hVb⟩ :=
    exists_balanced_factorization_of_vaughanDualBilinear_ne_zero hne
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hV_pos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast (by omega : 0 < V)
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hab_le : (a : ℝ) * (b : ℝ) ≤ (K_hi : ℝ) := by exact_mod_cast hab.trans_le hk_le
  have hUa_r : (U : ℝ) < (a : ℝ) := by exact_mod_cast hUa
  have hVb_r : (V : ℝ) < (b : ℝ) := by exact_mod_cast hVb
  refine ⟨a, b, hab, ⟨hUa_r, ?_⟩, ⟨hVb_r, ?_⟩⟩
  · rw [lt_div_iff₀ hV_pos]
    exact (mul_lt_mul_of_pos_left hVb_r ha_pos).trans_le hab_le
  · rw [lt_div_iff₀ hU_pos]
    exact (mul_lt_mul_of_pos_left hUa_r hb_pos).trans_le (by rw [mul_comm]; exact hab_le)

end Part3BalancedDualBilinearBand

#print axioms vaughanDualBilinear_comm
#print axioms zeta_mul_vaughanTypeIICoeff_eq_vaughanDualBilinear
#print axioms exists_balanced_factorization_of_vaughanDualBilinear_ne_zero
#print axioms vaughanDualBilinear_eq_zero_of_lt_succ_mul_succ
#print axioms parityClearedVaughanDualBilinear_eq_zero_of_lt_succ_mul_succ
#print axioms vaughanDualBilinear_mul_prime_eq_zero
#print axioms vaughanDualBilinear_prime_eq_zero
#print axioms parityClearedVaughanDualBilinear_prime_eq_zero
#print axioms norm_smoothOuterVaughanDualSieveCoeff_sub_parityCleared_le
#print axioms smoothOuterVaughanTypeII_eq_zeta_mul_add_dual_sieve
#print axioms exists_balancedDualBilinearBand_duality_on_remaining_strip
#print axioms strict_primeGas_witness_of_balancedDualBilinearBand_domination_on_remaining_strip
#print axioms vaughan_conductor_square_gap_invariance
#print axioms balanced_dual_factor_window_pinning

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
