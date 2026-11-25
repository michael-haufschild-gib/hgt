import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ZetaFreeBalancedBilinearDirichletReductionAndDivisorBoundedForcing
import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues
import GaloisForLFunctions.ArithmeticProduction.BilinearFormsAreParityBlind

/-!
# Rough-Semigroup `d(k) - 2` Divisor Rigidity, Mollifier-Square Generating Identity, Antipodal Firewall Separation, and Dyadic Huxley Large-Values Dispersion on `Ω_open`

`ZetaFreeBalancedBilinearDirichletReductionAndDivisorBoundedForcing` reduced unconditional
`HasStrictPrimeGasWitness` certification across all of
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}` to bounding the pure
unweighted finite Dirichlet polynomial `balancedBilinearDirichletPoly U V K_hi` at `1 - s` and
along the critical line `conj (linePt (Im s + v))`.

This module establishes four structural laws governing `vaughanDualBilinear`,
`parityClearedVaughanDualBilinear`, and `balancedBilinearDirichletPoly`:

1. **Exact rough-semigroup `d(k) - 2` divisor rigidity and Liouville parity-breaking
   (`typeIIShort_eq_neg_one_of_rough`, `vaughanDualBilinear_eq_divisors_sub_two_of_rough`,
   `parityClearedVaughanDualBilinear_eq_divisors_sub_two_of_rough`,
   `one_le_vaughanDualBilinear_of_composite_rough`,
   `parityClearedVaughanDualBilinear_breaks_liouvilleTwist_parity`):**
   On the `max U V`-rough multiplicative subsemigroup `{k ≥ 2 | ∀ p prime, p ∣ k → max U V < p}`:
   - `typeIIShort W a = -1` identically for every `W ≥ 1` and `W`-rough `a ≥ 2`;
   - `vaughanDualBilinear U V k = d(k) - 2` identically (`U, V ≥ 1`), and when `2 ≤ max U V`
     every such `k` is odd so `parityClearedVaughanDualBilinear U V k = d(k) - 2` identically;
   - consequently, `parityClearedVaughanDualBilinear U V` vanishes on the `Ω(k) = 1` prime layer
     (`λ(p) = -1`) while taking strictly positive integer values `≥ 1` across **both** the `Ω = 2`
     semiprime layer (`λ(p q) = +1`, value `1` or `2`) and the `Ω = 3` rough cube layer
     (`λ(p^3) = -1`, value `2`), breaking the `λ`-twist symmetry of general Type-II box norms
     (`ArithmeticProduction.bilinearConstants_liouvilleTwist`).

2. **Exact `LSeries` mollifier-square generating identity on `Re w > 1`
   (`truncMoebiusDirichletPoly`, `analyticDualBilinearGen`,
   `LSeries_typeIIShort_eq_one_sub_zeta_mul_truncMoebius`,
   `LSeries_vaughanDualBilinear_eq_mollifier_product`,
   `LSeries_parityClearedVaughanDualBilinear_eq_analyticDualBilinearGen`):**
   On `{w : ℂ | 1 < Re w}`, `LSeries (parityClearedVaughanDualBilinear U V) w` converges
   unconditionally and equals the exact mollifier-product generating function
   `analyticDualBilinearGen U V w = (1 - 2^{-w}) (1 - ζ(w) M_U(w)) (1 - ζ(w) M_V(w))`.

3. **Antipodal functional-equation dichotomy at `1 - s` and failure on `posTruncatedZeta`
   (`analyticDualBilinearGen_dichotomy_and_posTruncatedZeta_separation`):**
   At any hypothetical off-line zero `ζ(s) = 0` (`0 < Re s < 1 / 2`), functional-equation zero
   symmetry forces `ζ(1 - s) = 0` and hence `‖analyticDualBilinearGen U V (1 - s)‖ > 1 / 4`
   uniformly in `(U, V)`, whereas whenever `‖1 - ζ(1 - s) M_U(1 - s)‖ ≤ ε_U` and
   `‖1 - ζ(1 - s) M_V(1 - s)‖ ≤ ε_V`, `analyticDualBilinearGen U V (1 - s)` suffers quadratic
   mollifier suppression `≤ 2 ε_U ε_V`; by contrast, `posTruncatedZeta P₀ ρ₀` vanishes at `ρ₀`
   while remaining nonzero or singular at `1 - ρ₀ ∈ {0 < Re s < 1 / 2}`.

4. **Critical-line dyadic block identification and Huxley sixth-moment large-values dispersion on
   `balancedBilinearDirichletPoly`
   (`balancedBilinearDyadicBlock`, `blockPoly_balancedBilinearCritCoeff_eq`,
   `huxley_large_values_balancedBilinearDyadicBlock`):**
   Every dyadic slice `N ≤ k < 2 N` of `balancedBilinearDirichletPoly U V K_hi (conj (linePt t))`
   equals `RHTower.Sieve.blockPoly N (balancedBilinearCritCoeff U V K_hi) 1 (-t)` identically,
   combining `norm_parityClearedVaughanDualBilinear_le_eight_mul_divisors_cube` (`8 · d(k)^3`)
   with `RHTower.Sieve.huxley_block_large_values` across any `δ_sep`-separated ordinate set.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction LSeries.notation

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Rough-Semigroup `d(k) - 2` Divisor Rigidity and Liouville Parity-Breaking -/

section Part1RoughSemigroupDivisorRigidity

/-- An integer `n : ℕ` is `W`-rough if every prime divisor `p ∣ n` satisfies `W < p`. -/
def IsRoughAbove (W n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → W < p

lemma IsRoughAbove.mono {W₁ W₂ n : ℕ} (hW : W₁ ≤ W₂) (h : IsRoughAbove W₂ n) :
    IsRoughAbove W₁ n :=
  fun p hp hpn => lt_of_le_of_lt hW (h p hp hpn)

lemma IsRoughAbove.of_dvd {W d k : ℕ} (h : IsRoughAbove W k) (hdk : d ∣ k) :
    IsRoughAbove W d :=
  fun p hp hpd => h p hp (dvd_trans hpd hdk)

lemma gt_of_isRoughAbove_of_two_le {W d : ℕ} (hd : 2 ≤ d) (h : IsRoughAbove W d) :
    W < d := by
  have hp : Nat.Prime d.minFac := Nat.minFac_prime (by omega)
  have hdvd : d.minFac ∣ d := Nat.minFac_dvd d
  have hle : d.minFac ≤ d := Nat.minFac_le (by omega)
  exact (h d.minFac hp hdvd).trans_le hle

/-- **Constant `-1` law for `typeIIShort` on the rough semigroup:**
for every `W ≥ 1` and every `W`-rough integer `a ≥ 2`, `typeIIShort W a = -1` identically. -/
theorem typeIIShort_eq_neg_one_of_rough
    {W a : ℕ} (hW : 1 ≤ W) (ha : 2 ≤ a) (hrough : IsRoughAbove W a) :
    _root_.RHTower.Sieve.typeIIShort W a = -1 := by
  have hsub :
      ((1 : ArithmeticFunction ℝ) -
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) a =
      (1 : ArithmeticFunction ℝ) a -
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) a := rfl
  change ((1 : ArithmeticFunction ℝ) -
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) a = -1
  rw [hsub, ArithmeticFunction.one_apply, if_neg (by omega : ¬ a = 1),
    ArithmeticFunction.coe_zeta_mul_apply]
  have h1_mem : 1 ∈ a.divisors := Nat.mem_divisors.mpr ⟨one_dvd a, by omega⟩
  have hsum :
      (∑ d ∈ a.divisors,
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W d) = 1 := by
    rw [Finset.sum_eq_single 1]
    · rw [_root_.RHTower.Sieve.truncAF_apply, if_pos hW]
      simp
    · intro d hd hd_ne1
      have hda : d ∣ a := Nat.dvd_of_mem_divisors hd
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hda (by omega)
      have hd2 : 2 ≤ d := by omega
      have hWd : W < d := gt_of_isRoughAbove_of_two_le hd2 (hrough.of_dvd hda)
      rw [_root_.RHTower.Sieve.truncAF_apply, if_neg (by omega : ¬ d ≤ W)]
    · intro hnot
      exact False.elim (hnot h1_mem)
  linarith

/-- **Exact `d(k) - 2` divisor rigidity law on the `max U V`-rough semigroup:**
for all `U ≥ 1`, `V ≥ 1`, and every `max U V`-rough integer `k ≥ 2`,
`vaughanDualBilinear U V k = (k.divisors.card : ℝ) - 2`. -/
theorem vaughanDualBilinear_eq_divisors_sub_two_of_rough
    {U V k : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hk : 2 ≤ k)
    (hrough : IsRoughAbove (max U V) k) :
    vaughanDualBilinear U V k = (k.divisors.card : ℝ) - 2 := by
  unfold vaughanDualBilinear
  rw [ArithmeticFunction.mul_apply]
  set E : Finset (ℕ × ℕ) := {(1, k), (k, 1)}
  have hpair_ne : ((1 : ℕ), k) ≠ (k, 1) := by
    intro h
    have h1 := congrArg Prod.fst h
    dsimp only at h1
    omega
  have hE_sub : E ⊆ k.divisorsAntidiagonal := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul k, by omega⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one k, by omega⟩
  have hsum_E :
      (∑ p ∈ E, _root_.RHTower.Sieve.typeIIShort U p.1 *
        _root_.RHTower.Sieve.typeIIShort V p.2) = 0 := by
    dsimp only [E]
    rw [Finset.sum_pair hpair_ne]
    have hzU : _root_.RHTower.Sieve.typeIIShort U 1 = 0 :=
      _root_.RHTower.Sieve.one_sub_zeta_mul_truncAF_moebius_apply_eq_zero le_rfl hU
    have hzV : _root_.RHTower.Sieve.typeIIShort V 1 = 0 :=
      _root_.RHTower.Sieve.one_sub_zeta_mul_truncAF_moebius_apply_eq_zero le_rfl hV
    rw [hzU, hzV, zero_mul, mul_zero, add_zero]
  have hpt_sdiff : ∀ p ∈ k.divisorsAntidiagonal \ E,
      _root_.RHTower.Sieve.typeIIShort U p.1 *
        _root_.RHTower.Sieve.typeIIShort V p.2 = (1 : ℝ) := by
    intro p hp
    obtain ⟨hp_mem, hp_notE⟩ := Finset.mem_sdiff.mp hp
    have hprod : p.1 * p.2 = k := (Nat.mem_divisorsAntidiagonal.mp hp_mem).1
    have hp1_ne0 : p.1 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; omega
    have hp2_ne0 : p.2 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hprod; omega
    have hp1_ne1 : p.1 ≠ 1 := fun h1 => by
      have hp2_eq : p.2 = k := by rw [h1, one_mul] at hprod; exact hprod
      apply hp_notE
      simp only [E, Finset.mem_insert, Finset.mem_singleton]
      left
      exact Prod.ext h1 hp2_eq
    have hp2_ne1 : p.2 ≠ 1 := fun h1 => by
      have hp1_eq : p.1 = k := by rw [h1, mul_one] at hprod; exact hprod
      apply hp_notE
      simp only [E, Finset.mem_insert, Finset.mem_singleton]
      right
      exact Prod.ext hp1_eq h1
    have hp1_ge2 : 2 ≤ p.1 := by omega
    have hp2_ge2 : 2 ≤ p.2 := by omega
    have hd1 : p.1 ∣ k := ⟨p.2, hprod.symm⟩
    have hd2 : p.2 ∣ k := ⟨p.1, by rw [mul_comm]; exact hprod.symm⟩
    have hr1 : IsRoughAbove U p.1 := (hrough.of_dvd hd1).mono (le_max_left U V)
    have hr2 : IsRoughAbove V p.2 := (hrough.of_dvd hd2).mono (le_max_right U V)
    rw [typeIIShort_eq_neg_one_of_rough hU hp1_ge2 hr1,
      typeIIShort_eq_neg_one_of_rough hV hp2_ge2 hr2]
    ring
  have hcount_split :
      (∑ _p ∈ k.divisorsAntidiagonal \ E, (1 : ℝ)) + (∑ _p ∈ E, (1 : ℝ)) =
        ∑ _p ∈ k.divisorsAntidiagonal, (1 : ℝ) :=
    Finset.sum_sdiff hE_sub
  have hcount_E : (∑ _p ∈ E, (1 : ℝ)) = 2 := by
    dsimp only [E]
    rw [Finset.sum_pair hpair_ne]
    norm_num
  have hcount_all : (∑ _p ∈ k.divisorsAntidiagonal, (1 : ℝ)) = (k.divisors.card : ℝ) := by
    simp [_root_.RHTower.Sieve.card_divisorsAntidiagonal]
  rw [← Finset.sum_sdiff hE_sub, hsum_E, add_zero, Finset.sum_congr rfl hpt_sdiff]
  linarith

/-- **Exact `d(k) - 2` parity-cleared divisor rigidity law (`2 ≤ max U V`):**
when `2 ≤ max U V`, every `max U V`-rough integer `k ≥ 2` is odd (`¬ 2 ∣ k`), so
`parityClearedVaughanDualBilinear U V k = ((k.divisors.card : ℝ) - 2 : ℂ)` identically. -/
theorem parityClearedVaughanDualBilinear_eq_divisors_sub_two_of_rough
    {U V k : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hmax2 : 2 ≤ max U V) (hk : 2 ≤ k)
    (hrough : IsRoughAbove (max U V) k) :
    parityClearedVaughanDualBilinear U V k = (((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) := by
  have hnot2 : ¬ (2 ∣ k) := fun h2k => by
    have hlt := hrough 2 Nat.prime_two h2k
    omega
  unfold parityClearedVaughanDualBilinear
  rw [if_neg hnot2, sub_zero, vaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hk hrough]

/-- **Strict composite positivity on the rough semigroup:**
for every composite `max U V`-rough integer `k ≥ 2` (`¬ Nat.Prime k`), `d(k) ≥ 3` and hence
`1 ≤ vaughanDualBilinear U V k`. -/
theorem one_le_vaughanDualBilinear_of_composite_rough
    {U V k : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hk : 2 ≤ k) (hcomp : ¬ Nat.Prime k)
    (hrough : IsRoughAbove (max U V) k) :
    1 ≤ vaughanDualBilinear U V k := by
  rw [vaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hk hrough]
  set p : ℕ := k.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ k := Nat.minFac_dvd k
  have hp_gt1 : 1 < p := hp_prime.one_lt
  have hp_le : p ≤ k := Nat.minFac_le (by omega)
  have hp_ne_k : p ≠ k := fun heq => hcomp (heq ▸ hp_prime)
  have hp_lt_k : p < k := lt_of_le_of_ne hp_le hp_ne_k
  set T : Finset ℕ := {1, p, k}
  have hT_sub : T ⊆ k.divisors := by
    intro d hd
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | hd_eq
    · exact Nat.mem_divisors.mpr ⟨one_dvd k, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨hp_dvd, by omega⟩
    · rw [hd_eq]; exact Nat.mem_divisors.mpr ⟨dvd_refl k, by omega⟩
  have h1_not : (1 : ℕ) ∉ ({p, k} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hp_not : p ∉ ({k} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have hT_card : T.card = 3 := by
    dsimp only [T]
    rw [Finset.card_insert_of_notMem h1_not, Finset.card_insert_of_notMem hp_not,
      Finset.card_singleton]
  have hcard3 : 3 ≤ k.divisors.card := hT_card ▸ Finset.card_le_card hT_sub
  have hcard3_r : (3 : ℝ) ≤ (k.divisors.card : ℝ) := by exact_mod_cast hcard3
  linarith

/-- **Explicit Liouville parity-breaking across `Ω = 1, 2, 3` on the rough semigroup:**
while `ArithmeticProduction.bilinearConstants_liouvilleTwist` proves general Type-II box constants
are blind to `λ(n) = (-1)^{Ω(n)}`, for `2 ≤ max U V` and every prime `p > max U V`:
1. at `p` (`λ(p) = -1`), `parityClearedVaughanDualBilinear U V p = 0`;
2. at `p ^ 2` (`λ(p ^ 2) = +1`), `parityClearedVaughanDualBilinear U V (p ^ 2) = 1`;
3. at `p ^ 3` (`λ(p ^ 3) = -1`), `parityClearedVaughanDualBilinear U V (p ^ 3) = 2`. -/
theorem parityClearedVaughanDualBilinear_breaks_liouvilleTwist_parity
    {U V p : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hmax2 : 2 ≤ max U V)
    (hp : Nat.Prime p) (hp_gt : max U V < p) :
    parityClearedVaughanDualBilinear U V p = 0 ∧
    parityClearedVaughanDualBilinear U V (p ^ (2 : ℕ)) = 1 ∧
    parityClearedVaughanDualBilinear U V (p ^ (3 : ℕ)) = 2 := by
  have hrough_pow : ∀ {m : ℕ}, IsRoughAbove (max U V) (p ^ m) := fun q hq hq_dvd => by
    have hpq : p = q := (Nat.Prime.dvd_iff_eq hp hq.ne_one).mp (hq.dvd_of_dvd_pow hq_dvd)
    rwa [← hpq]
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hp2_ge2 : 2 ≤ p ^ (2 : ℕ) := by nlinarith
  have hp3_ge2 : 2 ≤ p ^ (3 : ℕ) := by nlinarith
  refine ⟨parityClearedVaughanDualBilinear_prime_eq_zero hU hV hp, ?_, ?_⟩
  · rw [parityClearedVaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hmax2 hp2_ge2 hrough_pow,
      Nat.divisors_prime_pow hp 2, Finset.card_map, Finset.card_range]
    norm_num
  · rw [parityClearedVaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hmax2 hp3_ge2 hrough_pow,
      Nat.divisors_prime_pow hp 3, Finset.card_map, Finset.card_range]
    norm_num

end Part1RoughSemigroupDivisorRigidity


/-! ### Part 2: Exact `LSeries` Mollifier-Square Generating Identity and Antipodal Firewall Separation -/

section Part2MollifierSquareAndFirewallSeparation

/-- Truncated Möbius Dirichlet polynomial `M_U(w) = ∑_{1 ≤ d ≤ U} μ(d) d^{-w}`. -/
def truncMoebiusDirichletPoly (U : ℕ) (w : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-w)

/-- Analytic generating function `(1 - 2^{-w}) (1 - ζ(w) M_U(w)) (1 - ζ(w) M_V(w))` of
`parityClearedVaughanDualBilinear U V` across `w ≠ 1`. -/
def analyticDualBilinearGen (U V : ℕ) (w : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-w)) *
    (1 - riemannZeta w * truncMoebiusDirichletPoly U w) *
    (1 - riemannZeta w * truncMoebiusDirichletPoly V w)

private lemma lSeriesSummable_truncMoebius (U : ℕ) (w : ℂ) :
    LSeriesSummable
      (fun n : ℕ => ((_root_.RHTower.Sieve.truncAF
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U n : ℝ) : ℂ)) w := by
  refine summable_of_ne_finset_zero (s := Finset.Icc 1 U) fun n hn => ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hgt : U < n := by
      by_contra hle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, by omega⟩)
    rw [LSeries.term_of_ne_zero hn0, _root_.RHTower.Sieve.truncAF_apply, if_neg (by omega),
      Complex.ofReal_zero, zero_div]

private lemma lSeries_truncMoebius_eq (U : ℕ) (w : ℂ) :
    LSeries
      (fun n : ℕ => ((_root_.RHTower.Sieve.truncAF
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U n : ℝ) : ℂ)) w =
      truncMoebiusDirichletPoly U w := by
  unfold LSeries truncMoebiusDirichletPoly
  rw [tsum_eq_sum (s := Finset.Icc 1 U)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    rw [LSeries.term_of_ne_zero (by omega : d ≠ 0), _root_.RHTower.Sieve.truncAF_apply,
      if_pos hdU, div_eq_mul_inv, Complex.cpow_neg]
    simp
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hgt : U < n := by
        by_contra hle
        exact hn (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, by omega⟩)
      rw [LSeries.term_of_ne_zero hn0, _root_.RHTower.Sieve.truncAF_apply, if_neg (by omega),
        Complex.ofReal_zero, zero_div]

/-- **Exact `LSeries` identity for `typeIIShort U` on `Re w > 1`:**
for every `U : ℕ` and `w ∈ ℂ` with `1 < Re w`, `LSeries ↗(typeIIShort U) w` converges and equals
`1 - riemannZeta w * truncMoebiusDirichletPoly U w`. -/
theorem LSeries_typeIIShort_eq_one_sub_zeta_mul_truncMoebius
    (U : ℕ) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n : ℕ => ((_root_.RHTower.Sieve.typeIIShort U n : ℝ) : ℂ)) w ∧
    LSeries (fun n : ℕ => ((_root_.RHTower.Sieve.typeIIShort U n : ℝ) : ℂ)) w =
      1 - riemannZeta w * truncMoebiusDirichletPoly U w := by
  set f_one : ℕ → ℂ := LSeries.delta
  set f_z : ℕ → ℂ := fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℝ) : ℂ)
  set f_muU : ℕ → ℂ := fun n =>
    ((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U n : ℝ) : ℂ)
  have hsum_one : LSeriesSummable f_one w :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      have hn1 : n ≠ 1 := Finset.notMem_singleton.mp hn
      rw [LSeries.term_delta, if_neg hn1]
  have hf_z_eq : ∀ {n : ℕ}, n ≠ 0 → f_z n = (1 : ℕ → ℂ) n := fun {n} hn => by
    dsimp only [f_z]
    simp [ArithmeticFunction.zeta_apply, hn]
  have hsum_z : LSeriesSummable f_z w :=
    (LSeriesSummable_congr w hf_z_eq).mpr (LSeriesSummable_one_iff.mpr hw)
  have hl_z : LSeries f_z w = riemannZeta w := by
    rw [LSeries_congr hf_z_eq w, LSeries_one_eq_riemannZeta hw]
  have hsum_muU : LSeriesSummable f_muU w := lSeriesSummable_truncMoebius U w
  have hsum_conv : LSeriesSummable (f_z ⍟ f_muU) w := hsum_z.convolution hsum_muU
  have hfun_eq :
      (fun n : ℕ => ((_root_.RHTower.Sieve.typeIIShort U n : ℝ) : ℂ)) =
        f_one - (f_z ⍟ f_muU) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [f_one, LSeries.delta]
    · change (((1 : ArithmeticFunction ℝ) n -
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) n : ℝ) : ℂ) =
        f_one n - (f_z ⍟ f_muU) n
      rw [Complex.ofReal_sub, LSeries.convolution_def, ArithmeticFunction.mul_apply,
        Complex.ofReal_sum]
      congr 1
      · dsimp only [f_one, LSeries.delta]
        rw [ArithmeticFunction.one_apply]
        split_ifs <;> simp
      · exact Finset.sum_congr rfl fun _ _ => Complex.ofReal_mul _ _
  rw [hfun_eq]
  refine ⟨hsum_one.sub hsum_conv, ?_⟩
  rw [LSeries_sub hsum_one hsum_conv, LSeries_convolution' hsum_z hsum_muU,
    show LSeries f_one w = 1 by simpa [f_one] using congrFun LSeries_delta w,
    hl_z, lSeries_truncMoebius_eq]

/-- **Exact `LSeries` mollifier-product identity for `vaughanDualBilinear U V` on `Re w > 1`:**
for all `U, V : ℕ` and `1 < Re w`, `LSeries ↗(vaughanDualBilinear U V) w` converges and equals
`(1 - riemannZeta w * truncMoebiusDirichletPoly U w) * (1 - riemannZeta w * truncMoebiusDirichletPoly V w)`. -/
theorem LSeries_vaughanDualBilinear_eq_mollifier_product
    (U V : ℕ) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun k : ℕ => ((vaughanDualBilinear U V k : ℝ) : ℂ)) w ∧
    LSeries (fun k : ℕ => ((vaughanDualBilinear U V k : ℝ) : ℂ)) w =
      (1 - riemannZeta w * truncMoebiusDirichletPoly U w) *
        (1 - riemannZeta w * truncMoebiusDirichletPoly V w) := by
  obtain ⟨hsU, hlU⟩ := LSeries_typeIIShort_eq_one_sub_zeta_mul_truncMoebius U hw
  obtain ⟨hsV, hlV⟩ := LSeries_typeIIShort_eq_one_sub_zeta_mul_truncMoebius V hw
  have hconv_eq :
      (fun k : ℕ => ((vaughanDualBilinear U V k : ℝ) : ℂ)) =
        (fun a : ℕ => ((_root_.RHTower.Sieve.typeIIShort U a : ℝ) : ℂ)) ⍟
          (fun b : ℕ => ((_root_.RHTower.Sieve.typeIIShort V b : ℝ) : ℂ)) := by
    ext k
    unfold vaughanDualBilinear
    rw [ArithmeticFunction.mul_apply, LSeries.convolution_def, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp
  rw [hconv_eq]
  exact ⟨hsU.convolution hsV, by rw [LSeries_convolution' hsU hsV, hlU, hlV]⟩

/-- **Exact `LSeries` generating identity for `parityClearedVaughanDualBilinear U V` on `Re w > 1`:**
for all `U, V : ℕ` and `1 < Re w`, `LSeries (parityClearedVaughanDualBilinear U V) w` converges and
equals `analyticDualBilinearGen U V w = (1 - 2^{-w}) (1 - ζ(w) M_U(w)) (1 - ζ(w) M_V(w))`. -/
theorem LSeries_parityClearedVaughanDualBilinear_eq_analyticDualBilinearGen
    (U V : ℕ) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (parityClearedVaughanDualBilinear U V) w ∧
    LSeries (parityClearedVaughanDualBilinear U V) w = analyticDualBilinearGen U V w := by
  obtain ⟨hsB, hlB⟩ := LSeries_vaughanDualBilinear_eq_mollifier_product U V hw
  set f_par : ℕ → ℂ := fun n => if n = 1 then 1 else if n = 2 then -1 else 0
  have hsum_par : LSeriesSummable f_par w := by
    refine summable_of_ne_finset_zero (s := {1, 2}) fun n hn => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [LSeries.term_of_ne_zero hn0]
      dsimp only [f_par]
      rw [if_neg hn.1, if_neg hn.2, zero_div]
  have hl_par : LSeries f_par w = 1 - (2 : ℂ) ^ (-w) := by
    unfold LSeries
    rw [tsum_eq_sum (s := ({1, 2} : Finset ℕ))]
    · rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ 2),
        LSeries.term_of_ne_zero one_ne_zero, LSeries.term_of_ne_zero two_ne_zero]
      dsimp only [f_par]
      simp [div_eq_mul_inv, Complex.cpow_neg, sub_eq_add_neg]
    · intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rw [LSeries.term_of_ne_zero hn0]
        dsimp only [f_par]
        rw [if_neg hn.1, if_neg hn.2, zero_div]
  have hconv_par :
      ∀ {k : ℕ}, k ≠ 0 →
        parityClearedVaughanDualBilinear U V k =
          (f_par ⍟ (fun m : ℕ => ((vaughanDualBilinear U V m : ℝ) : ℂ))) k := by
    intro k hk0
    unfold parityClearedVaughanDualBilinear
    rw [LSeries.convolution_def]
    dsimp only
    by_cases h2k : 2 ∣ k
    · rw [if_pos h2k]
      have hpair_ne : ((1 : ℕ), k) ≠ (2, k / 2) := fun h => by
        have h1 := congrArg Prod.fst h; dsimp only at h1; omega
      have hsub : ({(1, k), (2, k / 2)} : Finset (ℕ × ℕ)) ⊆ k.divisorsAntidiagonal := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul k, hk0⟩
        · exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' h2k, hk0⟩
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair hpair_ne]
        dsimp only [f_par]
        norm_num
        ring
      · intro x hx hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
        have hx1_ne1 : x.1 ≠ 1 := fun h1 => hnot.1 (Prod.ext h1 (by rw [h1, one_mul] at hprod; exact hprod))
        have hx1_ne2 : x.1 ≠ 2 := fun h2 => hnot.2 (Prod.ext h2 (by rw [h2] at hprod; omega))
        dsimp only [f_par]
        rw [if_neg hx1_ne1, if_neg hx1_ne2, zero_mul]
    · rw [if_neg h2k, sub_zero]
      have h1_mem : (1, k) ∈ k.divisorsAntidiagonal :=
        Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul k, hk0⟩
      rw [Finset.sum_eq_single (1, k)]
      · dsimp only [f_par]; simp
      · intro x hx hx_ne
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
        have hx1_ne1 : x.1 ≠ 1 := fun h1 => hx_ne (Prod.ext h1 (by rw [h1, one_mul] at hprod; exact hprod))
        have hx1_ne2 : x.1 ≠ 2 := fun h2 => h2k ⟨x.2, by rw [← hprod, h2]⟩
        dsimp only [f_par]
        rw [if_neg hx1_ne1, if_neg hx1_ne2, zero_mul]
      · intro hnot; exact False.elim (hnot h1_mem)
  refine ⟨(LSeriesSummable_congr w hconv_par).mpr (hsum_par.convolution hsB), ?_⟩
  rw [LSeries_congr hconv_par w, LSeries_convolution' hsum_par hsB, hl_par, hlB]
  unfold analyticDualBilinearGen
  ring

/-- **Antipodal functional-equation dichotomy of `analyticDualBilinearGen` vs. `posTruncatedZeta`:**
1. At any hypothetical off-line zero `ζ(s) = 0` (`0 < Re s < 1 / 2`), functional-equation zero
   symmetry forces `ζ(1 - s) = 0` and hence `1 / 4 < ‖analyticDualBilinearGen U V (1 - s)‖`
   uniformly across all `U, V : ℕ`.
2. Conversely, whenever `0 < Re s < 1 / 2` satisfies `‖1 - ζ(1 - s) M_U(1 - s)‖ ≤ ε_U` and
   `‖1 - ζ(1 - s) M_V(1 - s)‖ ≤ ε_V` (`ε_U, ε_V ≥ 0`), `analyticDualBilinearGen U V (1 - s)`
   exhibits quadratic mollifier suppression `‖analyticDualBilinearGen U V (1 - s)‖ ≤ 2 * ε_U * ε_V`.
3. By contrast, for `posTruncatedZeta P₀ ρ₀` (`β ∈ (zetaZeroAbscissa, 1)`, `γ₀ ≠ 0`,
   `ρ₀ = β + i γ₀`), `posTruncatedZeta P₀ ρ₀ ρ₀ = 0` whereas at its reflected partner
   `1 - ρ₀ ∈ {0 < Re s < 1 / 2}` either `posTruncatedZeta P₀ ρ₀ (1 - ρ₀) ≠ 0` or its norm diverges
   to `+∞` on `𝓝[≠] (1 - ρ₀)`. -/
theorem analyticDualBilinearGen_dichotomy_and_posTruncatedZeta_separation :
    (∀ {s : ℂ} (U V : ℕ), 0 < s.re → s.re < 1 / 2 → riemannZeta s = 0 →
      (1 / 4 : ℝ) < ‖analyticDualBilinearGen U V (1 - s)‖) ∧
    (∀ {s : ℂ} {U V : ℕ} {ε_U ε_V : ℝ}, 0 < s.re → s.re < 1 / 2 →
      0 ≤ ε_U → 0 ≤ ε_V →
      ‖1 - riemannZeta (1 - s) * truncMoebiusDirichletPoly U (1 - s)‖ ≤ ε_U →
      ‖1 - riemannZeta (1 - s) * truncMoebiusDirichletPoly V (1 - s)‖ ≤ ε_V →
      ‖analyticDualBilinearGen U V (1 - s)‖ ≤ 2 * ε_U * ε_V) ∧
    (∀ {β γ₀ : ℝ}, zetaZeroAbscissa < β → β < 1 → γ₀ ≠ 0 → ∀ P₀ : ℕ,
      let ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
      posTruncatedZeta P₀ ρ₀ ρ₀ = 0 ∧
      ((DifferentiableAt ℂ (posTruncatedZeta P₀ ρ₀) (1 - ρ₀) ∧
          posTruncatedZeta P₀ ρ₀ (1 - ρ₀) ≠ 0) ∨
        Tendsto (fun z => ‖posTruncatedZeta P₀ ρ₀ z‖) (𝓝[≠] (1 - ρ₀)) atTop)) := by
  refine ⟨?_, ?_, fun hΘβ hβ1 hγ₀ P₀ => posTruncatedZeta_antipodal_asymmetry_at_planted_zero hΘβ hβ1 hγ₀ P₀⟩
  · intro s U V hs0 hhi hζ0
    have hs1 : s.re < 1 := by linarith
    have hζ1s : riemannZeta (1 - s) = 0 :=
      riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ0 hs0 hs1
    unfold analyticDualBilinearGen
    simp only [hζ1s, zero_mul, sub_zero, mul_one]
    exact one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi
  · intro s U V ε_U ε_V hs0 hhi _hεU _hεV hbU hbV
    have hpref_le2 : ‖1 - (2 : ℂ) ^ (-(1 - s))‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
      have hre_neg : (-(1 - s)).re ≤ 0 := by simp; linarith
      have hrp : (2 : ℝ) ^ (-(1 - s)).re ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le hre_neg
      linarith
    unfold analyticDualBilinearGen
    rw [norm_mul, norm_mul]
    calc ‖1 - (2 : ℂ) ^ (-(1 - s))‖ *
            ‖1 - riemannZeta (1 - s) * truncMoebiusDirichletPoly U (1 - s)‖ *
            ‖1 - riemannZeta (1 - s) * truncMoebiusDirichletPoly V (1 - s)‖
        ≤ (2 * ε_U) * ε_V :=
          mul_le_mul
            (mul_le_mul hpref_le2 hbU (norm_nonneg _) (by norm_num))
            hbV (norm_nonneg _) (by positivity)
      _ = 2 * ε_U * ε_V := by ring

end Part2MollifierSquareAndFirewallSeparation


/-! ### Part 3: Critical-Line Dyadic Block Identification and Huxley Large-Values Dispersion -/

section Part3HuxleyDyadicDispersion

/-- Dyadic slice `N ≤ k < 2 N` of `balancedBilinearDirichletPoly U V K_hi z`. -/
def balancedBilinearDyadicBlock (U V K_hi N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ico N (2 * N),
    (if (U + 1) * (V + 1) ≤ k ∧ k ≤ K_hi then parityClearedVaughanDualBilinear U V k else 0) *
      (k : ℂ) ^ (-z)

/-- Critical-line rescaled coefficient `1_{(U+1)(V+1) ≤ k ≤ K_hi} · b_{U,V}(k) · k^{1/2}`
interfacing `balancedBilinearDyadicBlock` at `conj (linePt t)` with `RHTower.Sieve.blockPoly N · 1 (-t)`. -/
def balancedBilinearCritCoeff (U V K_hi : ℕ) (k : ℕ) : ℂ :=
  (if (U + 1) * (V + 1) ≤ k ∧ k ≤ K_hi then parityClearedVaughanDualBilinear U V k else 0) *
    (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

/-- **Exact critical-line identification of `balancedBilinearDyadicBlock` with `RHTower.Sieve.blockPoly`:**
for all `U, V, K_hi : ℕ`, every `N ≥ 1`, and every ordinate `t : ℝ`,
`balancedBilinearDyadicBlock U V K_hi N (conj (linePt t))` equals
`RHTower.Sieve.blockPoly N (balancedBilinearCritCoeff U V K_hi) 1 (-t)` identically. -/
theorem blockPoly_balancedBilinearCritCoeff_eq
    (U V K_hi : ℕ) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    _root_.RHTower.Sieve.blockPoly N (balancedBilinearCritCoeff U V K_hi) 1 (-t) =
      balancedBilinearDyadicBlock U V K_hi N (conj (linePt t)) := by
  unfold _root_.RHTower.Sieve.blockPoly balancedBilinearDyadicBlock balancedBilinearCritCoeff
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : N ≤ k := (Finset.mem_Ico.mp hk).1
  have hk1 : 1 ≤ k := hN.trans hkN
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkR_ne0 : ((k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_pos.ne'
  have hrpow : (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (-(1 : ℝ)) = (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hk_pos]
    congr 1
    norm_num
  have hcpow :
      (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (((-((-t) * Real.log (k : ℝ)) : ℝ) : ℂ) * I) =
        (k : ℂ) ^ (-conj (linePt t)) := by
    rw [← Complex.ofReal_mul, hrpow, Real.rpow_def_of_pos hk_pos, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.ofReal_natCast k,
      Complex.cpow_def_of_ne_zero hkR_ne0, ← Complex.ofReal_log hk_pos.le]
    congr 1
    rw [conj_linePt]
    unfold linePt
    apply Complex.ext <;> simp <;> ring
  calc (if (U + 1) * (V + 1) ≤ k ∧ k ≤ K_hi then parityClearedVaughanDualBilinear U V k else 0) *
          (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (((-((-t) * Real.log (k : ℝ)) : ℝ) : ℂ) * I)
      = (if (U + 1) * (V + 1) ≤ k ∧ k ≤ K_hi then parityClearedVaughanDualBilinear U V k else 0) *
          ((((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (((-((-t) * Real.log (k : ℝ)) : ℝ) : ℂ) * I)) := by ring
    _ = (if (U + 1) * (V + 1) ≤ k ∧ k ≤ K_hi then parityClearedVaughanDualBilinear U V k else 0) *
          (k : ℂ) ^ (-conj (linePt t)) := by rw [hcpow]

/-- **Divisor-cube amplitude bound on `balancedBilinearCritCoeff` across `[N, 2 N)`:**
if `d(k) ≤ M_div` on `[N, 2 N)` (`N ≥ 1`), then
`‖balancedBilinearCritCoeff U V K_hi k‖ ≤ 8 * M_div ^ 3 * (2 * N)^{1 / 2}` for all `k ∈ [N, 2 N)`. -/
theorem norm_balancedBilinearCritCoeff_le
    (U V K_hi : ℕ) {N : ℕ} (hN : 1 ≤ N) {M_div : ℝ} (hM_nn : 0 ≤ M_div)
    (hdiv : ∀ k ∈ Finset.Ico N (2 * N), (k.divisors.card : ℝ) ≤ M_div) :
    ∀ k ∈ Finset.Ico N (2 * N),
      ‖balancedBilinearCritCoeff U V K_hi k‖ ≤
        8 * M_div ^ (3 : ℕ) * ((2 * N : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  intro k hk
  have hk1 : 1 ≤ k := hN.trans (Finset.mem_Ico.mp hk).1
  have hk_lt : k < 2 * N := (Finset.mem_Ico.mp hk).2
  have hk_le_2N : (k : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hk_lt.le
  unfold balancedBilinearCritCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
  have hb :
      ‖if (U + 1) * (V + 1) ≤ k ∧ k ≤ K_hi then parityClearedVaughanDualBilinear U V k else 0‖ ≤
        8 * M_div ^ (3 : ℕ) := by
    split_ifs
    · exact (norm_parityClearedVaughanDualBilinear_le_eight_mul_divisors_cube U V hk1).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv k hk) 3) (by norm_num))
    · rw [norm_zero]; positivity
  have hrp : (k : ℝ) ^ (1 / 2 : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg k) hk_le_2N (by norm_num)
  exact mul_le_mul hb hrp (by positivity) (by positivity)

/-- **Huxley sixth-moment large-values dispersion on `balancedBilinearDyadicBlock` along `Re = 1 / 2`:**
for any `N ≥ 1`, `M_div ≥ 0` bounding `d(k)` on `[N, 2 N)`, and any `δ_sep`-separated finite set `S`
of ordinates of diameter `≤ Ttot` on which `‖balancedBilinearDyadicBlock U V K_hi N (conj (linePt t))‖ ≥ V_lv`
above Huxley's threshold, `|S| · V_lv^2` obeys Huxley's published large-values bound with
`D = 8 * M_div ^ 3 * (2 * N)^{1 / 2}`. -/
theorem huxley_large_values_balancedBilinearDyadicBlock
    (U V K_hi : ℕ) {N : ℕ} (hN : 1 ≤ N)
    {δ_sep Ttot V_lv M_div : ℝ}
    (hδ : 0 < δ_sep) (hV_lv : 0 < V_lv) (hTtot : 0 ≤ Ttot) (hM_nn : 0 ≤ M_div)
    (hdiv : ∀ k ∈ Finset.Ico N (2 * N), (k.divisors.card : ℝ) ≤ M_div)
    (S : Finset ℝ)
    (hsep : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → δ_sep ≤ |t₁ - t₂|)
    (hspread : ∀ t₁ ∈ S, ∀ t₂ ∈ S, |t₁ - t₂| ≤ Ttot)
    (hbig : ∀ t ∈ S, V_lv ≤ ‖balancedBilinearDyadicBlock U V K_hi N (conj (linePt t))‖)
    (hthresh :
      let D : ℝ := 8 * M_div ^ (3 : ℕ) * ((2 * N : ℕ) : ℝ) ^ (1 / 2 : ℝ)
      (D ^ 2 / (N : ℝ)) * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))) ≤ V_lv ^ 2 / 3) :
    let D : ℝ := 8 * M_div ^ (3 : ℕ) * ((2 * N : ℕ) : ℝ) ^ (1 / 2 : ℝ)
    (S.card : ℝ) * V_lv ^ 2 ≤
      (1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V_lv ^ 4) + 1) *
        (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (S.card : ℝ)) / δ_sep)) := by
  dsimp only at hthresh ⊢
  set D : ℝ := 8 * M_div ^ (3 : ℕ) * ((2 * N : ℕ) : ℝ) ^ (1 / 2 : ℝ)
  have hD_nn : 0 ≤ D := by dsimp only [D]; positivity
  set negEmb : ℝ ↪ ℝ := (Equiv.neg ℝ).toEmbedding
  have hneg_apply : ∀ t : ℝ, negEmb t = -t := fun _ => rfl
  set S_neg : Finset ℝ := S.map negEmb
  have hcard_eq : S_neg.card = S.card := Finset.card_map negEmb
  have hsep' : ∀ x ∈ S_neg, ∀ y ∈ S_neg, x ≠ y → δ_sep ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨t₂, ht₂, rfl⟩ := Finset.mem_map.mp hy
    have hne : t₁ ≠ t₂ := fun h => hxy (by rw [h])
    have habs : |(-t₁) - (-t₂)| = |t₁ - t₂| := by
      rw [show (-t₁) - (-t₂) = -(t₁ - t₂) by ring, abs_neg]
    rw [hneg_apply, hneg_apply, habs]
    exact hsep t₁ ht₁ t₂ ht₂ hne
  have hspread' : ∀ x ∈ S_neg, ∀ y ∈ S_neg, |x - y| ≤ Ttot := by
    intro x hx y hy
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨t₂, ht₂, rfl⟩ := Finset.mem_map.mp hy
    have habs : |(-t₁) - (-t₂)| = |t₁ - t₂| := by
      rw [show (-t₁) - (-t₂) = -(t₁ - t₂) by ring, abs_neg]
    rw [hneg_apply, hneg_apply, habs]
    exact hspread t₁ ht₁ t₂ ht₂
  have hbig' : ∀ x ∈ S_neg,
      V_lv ≤ ‖_root_.RHTower.Sieve.blockPoly N (balancedBilinearCritCoeff U V K_hi) 1 x‖ := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hx
    rw [hneg_apply, blockPoly_balancedBilinearCritCoeff_eq U V K_hi hN t]
    exact hbig t ht
  have hhux := _root_.RHTower.Sieve.huxley_block_large_values hN
    (balancedBilinearCritCoeff U V K_hi) hδ hV_lv hTtot hD_nn
    (norm_balancedBilinearCritCoeff_le U V K_hi hN hM_nn hdiv)
    S_neg hsep' hspread' hbig' hthresh
  rwa [hcard_eq] at hhux

end Part3HuxleyDyadicDispersion

#print axioms typeIIShort_eq_neg_one_of_rough
#print axioms vaughanDualBilinear_eq_divisors_sub_two_of_rough
#print axioms parityClearedVaughanDualBilinear_eq_divisors_sub_two_of_rough
#print axioms one_le_vaughanDualBilinear_of_composite_rough
#print axioms parityClearedVaughanDualBilinear_breaks_liouvilleTwist_parity
#print axioms LSeries_typeIIShort_eq_one_sub_zeta_mul_truncMoebius
#print axioms LSeries_vaughanDualBilinear_eq_mollifier_product
#print axioms LSeries_parityClearedVaughanDualBilinear_eq_analyticDualBilinearGen
#print axioms analyticDualBilinearGen_dichotomy_and_posTruncatedZeta_separation
#print axioms blockPoly_balancedBilinearCritCoeff_eq
#print axioms norm_balancedBilinearCritCoeff_le
#print axioms huxley_large_values_balancedBilinearDyadicBlock

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
