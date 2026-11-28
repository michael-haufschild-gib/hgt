import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1TrueVertexHighTransportAndZeroFree
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBornScaledDeficitObstructionAndPowerLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.RoughSemigroupDivisorRigidityMollifierSquareAndHuxleyDispersion
import GaloisForLFunctions.ArithmeticPositiveDuality.TheRationalPrimeOneOffHasMultiplicativeCounting
import GaloisForLFunctions.ArithmeticPositiveDuality.TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor

/-!
# Coupled Zero-Forced Single-Mode Prime Excess, Integer-Semigroup Vaughan Rigidity Against `RationalPrimeOneOff`, and Unconditional Zero-Free Strip Beyond `2401 / 19200`

Couples the zero-forced single-mode power-scaled Born prime excess
(`zeta_zero_forces_single_mode_power_deficit_and_excess` and
`zeta_zero_forces_direct_bornCoefficient_sub_smooth_power_excess`) with the integer-semigroup
Vaughan–Möbius / rough-semigroup bilinear dispersion firewall and the Gram-admissible Stage-1
cubic-probe vertex `(2111 / 6000, 19249 / 40000, 20033 / 120000)`:

1. **`RationalPrimeOneOff` fails unit integer occupation `a(n) = 1` across every ordinate `γ ∈ ℝ`:**
   - `rationalPrimeOneOff_superUnit_at_two_of_abs_gt_184`: for every `184 < |γ|`, three disjoint
     cosine troughs `[(4m + 1)π / (2|γ|), (4m + 3)π / (2|γ|)]` (`m = 0, 1, 2`) lie inside
     `(0, log 2)` and contribute `≥ 4/3 + 4/7 + 4/11 = 524/231 > 2` to the cumulative prime
     measure `W(log 2)`, forcing both `primeNorm P 0 = 2` and `primeNorm P 1 = 2` and hence
     `2 ≤ RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) 2` (violating both
     `a(n) = 1` and `|a(n)| ≤ 1` at `n = 2`).
   - `rationalPrimeOneOff_zero_at_two_at_origin`: at `γ = 0`, `1 - cos(0 · u) = 0` bounds
     `W(log 2) ≤ 65/81 < 1`, forcing `primeNorm (fixedParams 0) k ≥ 3` for all `k` and
     `integerCoeff (fixedParams 0) 2 = 0`.
   - `rationalPrimeOneOff_not_unit_occupation_of_abs_le_184` and
     `rationalPrimeOneOff_never_unit_integer_occupation`: on `0 < |γ| ≤ 184`, unit occupation
     `∀ n ≥ 1, integerCoeff P n = 1` identifies `continuation P` with `riemannZeta` on the convex
     quadrant `{17/30 < Re s ∧ 0 < Im s}`, contradicting the planted zero at `3/5 + i|γ|` via
     `riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour`; hence `RationalPrimeOneOff`
     never has unit integer occupation at any `γ ∈ ℝ`.

2. **Exact Dirichlet-ring characterization of Vaughan Type-I Möbius annihilation and `Aff(ℚ)`
   integer-successor positivity:**
   - `subhorizon_mobius_annihilation_iff_eq_zeta`: for any `a : ArithmeticFunction ℝ`, sub-horizon
     Vaughan Type-I Möbius annihilation `(1 - a * truncAF μ W) n = 0` for all `1 ≤ n ≤ W` holds if
     and only if `a = ArithmeticFunction.zeta` (`∀ n ≥ 1, a n = 1`).
   - `rationalPrimeOneOff_breaks_subhorizon_mobius_annihilation_above_184` and
     `integer_semigroup_vaughan_and_affQ_successor_firewall`: for every `|γ| > 184` and `W ≥ 2`,
     the `RationalPrimeOneOff` coefficient sequence fails sub-horizon Möbius annihilation already
     at `n = 2` (`≤ -1`), while on `Aff(ℚ)` the integer successor `x ↦ x + 1` enforces the critical
     positivity threshold `IsPosDefOnGroup (heckeState s) ↔ 1 / 2 ≤ s`.

3. **Unconditional sub-Farkas abscissa improvement beyond `2401 / 19200` to `20011 / 160000` across
   all heights and coupled zero-forced Born excess dichotomy:**
   - `stage1_vertex_strictly_improves_sub_farkas_and_all_walls` and
     `hasStrictPrimeGasWitness_beyond_2401_wall`: `HeckeZeroSupremum.beta ≤ 139989 / 160000 <
     3281 / 3750 < 16799 / 19200`, excluding zeros of `riemannZeta` and producing pointwise
     `HasStrictPrimeGasWitness` across `0 < Re s < 20011 / 160000` (`20011 / 160000 = 0.12506875 >
     469 / 3750 > 2401 / 19200 > 3001 / 24000`) at all heights `|Im s| > 184` (and all `Im s ∈ ℝ`).
   - `unconditional_left_zero_exclusion_beyond_2401_and_low_height` and
     `coupled_born_power_excess_vaughan_mollifier_and_super2401_exclusion`: unconditionally
     discharges `zeta_zero_forces_superDispersion_iff_ne_zero` on
     `{0 < Re ρ < 20011 / 160000} ∪ {0 < Re ρ < 1 / 2 ∧ |Im ρ| ≤ 184}` and couples any remaining
     zero `ζ(ρ) = 0` (`20011 / 160000 ≤ Re ρ < 1 / 2`, `184 < |Im ρ|`) simultaneously to the
     uniform antipodal Vaughan mollifier-square floor `‖analyticDualBilinearGen U V (1 - ρ)‖ > 1/4`
     and unbounded `(N + 2)^α`-scaled single-mode Born excess across all `k₀ ≠ 0` and
     `α ∈ (Re ρ, 1 / 2)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Finset MeasureTheory Real Set
open scoped Topology BigOperators ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

attribute [-instance]
  GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.HeckeTauberian.instMeasurableSpace
  RCLike.toInnerProductSpaceReal

/-! ### Section 1: `RationalPrimeOneOff` Fails Unit Integer Occupation Across Every Ordinate `γ ∈ ℝ` -/

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have h2 : (1 / 2 : ℝ) * Real.exp (1 / 2) ≤ 1 := by
    calc (1 / 2 : ℝ) * Real.exp (1 / 2)
        ≤ Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  exact (Real.le_log_iff_exp_le two_pos).mpr (by linarith)

private lemma cos_mul_nonpos_on_trough {γ u : ℝ} (hg : 0 < |γ|) (m : ℕ)
    (hlo : ((4 * (m : ℝ) + 1) * Real.pi) / (2 * |γ|) ≤ u)
    (hhi : u ≤ ((4 * (m : ℝ) + 3) * Real.pi) / (2 * |γ|)) :
    Real.cos (γ * u) ≤ 0 := by
  have hcos_abs : Real.cos (γ * u) = Real.cos (|γ| * u) := by
    rcases le_or_gt 0 γ with hγ | hγ
    · rw [abs_of_nonneg hγ]
    · rw [abs_of_neg hγ, neg_mul, Real.cos_neg]
  rw [hcos_abs]
  have h2g : 0 < 2 * |γ| := by positivity
  have hlo' : (4 * (m : ℝ) + 1) * Real.pi ≤ u * (2 * |γ|) := (div_le_iff₀ h2g).mp hlo
  have hhi' : u * (2 * |γ|) ≤ (4 * (m : ℝ) + 3) * Real.pi := (le_div_iff₀ h2g).mp hhi
  set φ : ℝ := |γ| * u - (2 * (m : ℝ) + 1) * Real.pi
  have hφ_lo : -(Real.pi / 2) ≤ φ := by dsimp only [φ]; linarith
  have hφ_hi : φ ≤ Real.pi / 2 := by dsimp only [φ]; linarith
  have hcos_φ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le hφ_lo hφ_hi
  have hid : |γ| * u = (φ + Real.pi) + (m : ℤ) * (2 * Real.pi) := by
    dsimp only [φ]; push_cast; ring
  rw [hid, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  linarith

private lemma two_div_le_fixedParams_wt_on_trough {γ u : ℝ} (hg : 0 < |γ|) (m : ℕ)
    (hlo : ((4 * (m : ℝ) + 1) * Real.pi) / (2 * |γ|) ≤ u)
    (hhi : u ≤ ((4 * (m : ℝ) + 3) * Real.pi) / (2 * |γ|)) :
    2 / u ≤ (IntegerNormOneOff.fixedParams γ).wt u := by
  set P := IntegerNormOneOff.fixedParams γ
  have ha_pos : 0 < ((4 * (m : ℝ) + 1) * Real.pi) / (2 * |γ|) :=
    div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)
  have hu0 : 0 < u := lt_of_lt_of_le ha_pos hlo
  have hwt_eq : P.wt u = P.w u := by
    unfold DiscreteOneOff.Params.wt
    exact Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0) _
  rw [hwt_eq]
  unfold DiscreteOneOff.Params.w _root_.RHTower.BeurlingOverRegularIntegers.primeDensity
  refine div_le_div_of_nonneg_right ?_ hu0.le
  rw [DiscreteOneOff.Params.primeNumerator_eq]
  have hcos : Real.cos (P.γ * u) ≤ 0 := cos_mul_nonpos_on_trough hg m hlo hhi
  have h1_cos : 1 ≤ 1 - Real.cos (P.γ * u) := by linarith
  have hμ_pos : 0 < P.μ := by linarith [P.hμ1]
  have hx1 : 1 ≤ Real.exp (P.μ * u) := Real.one_le_exp (mul_pos hμ_pos hu0).le
  have ht2 : 0 ≤ (Real.exp (P.ν * u) - 1) ^ 2 / Real.exp (P.ν * u) := by positivity
  have ht3 : 0 ≤ (Real.exp (P.μ * u) - 1) ^ 3 * (Real.exp (P.μ * u) + 1) / Real.exp (P.μ * u) :=
    div_nonneg (mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)) (Real.exp_pos _).le
  have hexp_prod : Real.exp (-((3 * P.μ - 1) * u)) * Real.exp (P.μ * u) ^ 2 =
      Real.exp ((1 - P.μ) * u) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hexp_ge1 : 1 ≤ Real.exp ((1 - P.μ) * u) :=
    Real.one_le_exp (mul_nonneg (by linarith [P.hμ2]) hu0.le)
  have ht1 : 2 * Real.exp (P.μ * u) ^ 2 ≤ 2 * Real.exp (P.μ * u) ^ 2 * (1 - Real.cos (P.γ * u)) :=
    le_mul_of_one_le_right (by positivity) h1_cos
  calc (2 : ℝ) ≤ 2 * Real.exp ((1 - P.μ) * u) := by linarith
    _ = Real.exp (-((3 * P.μ - 1) * u)) * (2 * Real.exp (P.μ * u) ^ 2) := by
        rw [← hexp_prod]; ring
    _ ≤ Real.exp (-((3 * P.μ - 1) * u)) *
        (2 * Real.exp (P.μ * u) ^ 2 * (1 - Real.cos (P.γ * u)) +
          (Real.exp (P.ν * u) - 1) ^ 2 / Real.exp (P.ν * u) +
          (Real.exp (P.μ * u) - 1) ^ 3 * (Real.exp (P.μ * u) + 1) / Real.exp (P.μ * u)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

private lemma trough_integral_ge {γ : ℝ} (hg : 0 < |γ|) (m : ℕ) :
    4 / (4 * (m : ℝ) + 3) ≤
      ∫ u in (((4 * (m : ℝ) + 1) * Real.pi) / (2 * |γ|))..
        (((4 * (m : ℝ) + 3) * Real.pi) / (2 * |γ|)),
        (IntegerNormOneOff.fixedParams γ).wt u := by
  set P := IntegerNormOneOff.fixedParams γ
  set a : ℝ := ((4 * (m : ℝ) + 1) * Real.pi) / (2 * |γ|)
  set b : ℝ := ((4 * (m : ℝ) + 3) * Real.pi) / (2 * |γ|)
  have ha0 : 0 < a := div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)
  have hb0 : 0 < b := div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)
  have hab : a ≤ b := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le) (by positivity)
  have hmono : (∫ _u in a..b, (2 / b : ℝ)) ≤ ∫ u in a..b, P.wt u := by
    refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (P.intervalIntegrable_wt ha0.le hab) fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    exact (div_le_div_of_nonneg_left zero_le_two hu0 hu.2).trans
      (two_div_le_fixedParams_wt_on_trough hg m hu.1 hu.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hval : (b - a) * (2 / b) = 4 / (4 * (m : ℝ) + 3) := by
    dsimp only [a, b]
    have h4m3 : (4 * (m : ℝ) + 3) ≠ 0 := by positivity
    field_simp [Real.pi_pos.ne', hg.ne', h4m3]
    ring
  linarith

/-- **Super-unit collision at `n = 2` for `RationalPrimeOneOff` above height `184`:**
for every ordinate `γ ∈ ℝ` with `184 < |γ|`, at least two distinct prime-norm generators round to
`2` (`primeNorm P 0 = primeNorm P 1 = 2`), so
`2 ≤ RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) 2` — violating both unit
occupation `a(n) = 1` and boundedness `|a(n)| ≤ 1` at `n = 2`. -/
theorem rationalPrimeOneOff_superUnit_at_two_of_abs_gt_184 {γ : ℝ} (hγ : 184 < |γ|) :
    2 ≤ RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) 2 := by
  set P := IntegerNormOneOff.fixedParams γ
  have hg : 0 < |γ| := by linarith
  let a : ℕ → ℝ := fun m => ((4 * (m : ℝ) + 1) * Real.pi) / (2 * |γ|)
  let b : ℕ → ℝ := fun m => ((4 * (m : ℝ) + 3) * Real.pi) / (2 * |γ|)
  have ha0 : 0 ≤ a 0 := div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by positivity)
  have hab (m : ℕ) : a m ≤ b m := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le) (by positivity)
  have hba (m : ℕ) : b m ≤ a (m + 1) := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by push_cast; linarith) Real.pi_pos.le) (by positivity)
  have hb2_le : b 2 ≤ Real.log 2 := by
    have hpi := Real.pi_lt_d2
    have hb2_half : b 2 ≤ 1 / 2 := by
      dsimp only [b]
      rw [div_le_iff₀ (by positivity : 0 < 2 * |γ|)]
      nlinarith
    exact hb2_half.trans half_le_log_two
  have hwt_nn (u : ℝ) : 0 ≤ P.wt u := by
    unfold DiscreteOneOff.Params.wt
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]; exact (P.w_pos hu).le
    · rw [Set.indicator_of_notMem hu]
  have hint_nn {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) : 0 ≤ ∫ u in c..d, P.wt u :=
    intervalIntegral.integral_nonneg hcd fun u _ => hwt_nn u
  have ha1_0 : 0 ≤ a 1 := ha0.trans ((hab 0).trans (hba 0))
  have hb1_0 : 0 ≤ b 1 := ha1_0.trans (hab 1)
  have ha2_0 : 0 ≤ a 2 := hb1_0.trans (hba 1)
  have hb2_0 : 0 ≤ b 2 := ha2_0.trans (hab 2)
  have hlog2_0 : 0 ≤ Real.log 2 := hb2_0.trans hb2_le
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl ha0) (P.intervalIntegrable_wt ha0 (hab 0))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl (ha0.trans (hab 0))) (P.intervalIntegrable_wt (ha0.trans (hab 0)) (hba 0))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl ha1_0) (P.intervalIntegrable_wt ha1_0 (hab 1))
  have hs4 := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl hb1_0) (P.intervalIntegrable_wt hb1_0 (hba 1))
  have hs5 := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl ha2_0) (P.intervalIntegrable_wt ha2_0 (hab 2))
  have hs6 := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl hb2_0) (P.intervalIntegrable_wt hb2_0 hb2_le)
  have hW_gt2 : 2 < P.W (Real.log 2) := by
    have ht0 : (4 / 3 : ℝ) ≤ ∫ u in a 0..b 0, P.wt u := by
      have h : 4 / (4 * ((0 : ℕ) : ℝ) + 3) ≤ ∫ u in a 0..b 0, P.wt u := trough_integral_ge hg 0
      exact (by norm_num : (4 / 3 : ℝ) ≤ 4 / (4 * ((0 : ℕ) : ℝ) + 3)).trans h
    have ht1 : (4 / 7 : ℝ) ≤ ∫ u in a 1..b 1, P.wt u := by
      have h : 4 / (4 * ((1 : ℕ) : ℝ) + 3) ≤ ∫ u in a 1..b 1, P.wt u := trough_integral_ge hg 1
      exact (by norm_num : (4 / 7 : ℝ) ≤ 4 / (4 * ((1 : ℕ) : ℝ) + 3)).trans h
    have ht2 : (4 / 11 : ℝ) ≤ ∫ u in a 2..b 2, P.wt u := by
      have h : 4 / (4 * ((2 : ℕ) : ℝ) + 3) ≤ ∫ u in a 2..b 2, P.wt u := trough_integral_ge hg 2
      exact (by norm_num : (4 / 11 : ℝ) ≤ 4 / (4 * ((2 : ℕ) : ℝ) + 3)).trans h
    have hn0 := hint_nn le_rfl ha0
    have hn1 : 0 ≤ ∫ u in b 0..a 1, P.wt u := hint_nn (ha0.trans (hab 0)) (hba 0)
    have hn2 : 0 ≤ ∫ u in b 1..a 2, P.wt u := hint_nn hb1_0 (hba 1)
    have hn3 := hint_nn hb2_0 hb2_le
    change (∫ x in (0 : ℝ)..b 0, P.wt x) + ∫ x in b 0..a 1, P.wt x = ∫ x in (0 : ℝ)..a 1, P.wt x at hs2
    change (∫ x in (0 : ℝ)..b 1, P.wt x) + ∫ x in b 1..a 2, P.wt x = ∫ x in (0 : ℝ)..a 2, P.wt x at hs4
    rw [P.W_eq_intervalIntegral hlog2_0]
    linarith [hs1, hs2, hs3, hs4, hs5, hs6, ht0, ht1, ht2, hn0, hn1, hn2, hn3]
  have hatom1_lt : P.atom 1 < Real.log 2 := by
    by_contra hge
    have hle := P.W_le_W (le_of_not_gt hge)
    rw [P.W_atom 1] at hle
    norm_num at hle
    linarith
  have hatom0_lt : P.atom 0 < Real.log 2 := (P.atom_zero_le 1).trans_lt hatom1_lt
  have hp0 : RationalPrimeOneOff.primeNorm P 0 = 2 := by
    have hexp : Real.exp (P.atom 0) < 2 := by
      simpa only [Real.exp_log two_pos] using Real.exp_lt_exp.mpr hatom0_lt
    exact Nat.le_antisymm (RationalPrimeOneOff.nextPrime_le Nat.prime_two hexp.le)
      (RationalPrimeOneOff.primeNorm_prime P 0).two_le
  have hp1 : RationalPrimeOneOff.primeNorm P 1 = 2 := by
    have hexp : Real.exp (P.atom 1) < 2 := by
      simpa only [Real.exp_log two_pos] using Real.exp_lt_exp.mpr hatom1_lt
    exact Nat.le_antisymm (RationalPrimeOneOff.nextPrime_le Nat.prime_two hexp.le)
      (RationalPrimeOneOff.primeNorm_prime P 1).two_le
  let v₀ : ℕ →₀ ℕ := Finsupp.single 0 1
  let v₁ : ℕ →₀ ℕ := Finsupp.single 1 1
  have hv₀ : IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v₀ = 2 := by
    classical
    dsimp only [IntegerOccupation.norm, Finsupp.prod, v₀]
    rw [Finsupp.support_single 0 one_ne_zero, Finset.prod_singleton,
      Finsupp.single_eq_same, pow_one, hp0]
  have hv₁ : IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v₁ = 2 := by
    classical
    dsimp only [IntegerOccupation.norm, Finsupp.prod, v₁]
    rw [Finsupp.support_single 1 one_ne_zero, Finset.prod_singleton,
      Finsupp.single_eq_same, pow_one, hp1]
  have hv_ne : (⟨v₀, hv₀⟩ : {v : ℕ →₀ ℕ // IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v = 2}) ≠
      ⟨v₁, hv₁⟩ := by
    intro h
    have h0 := Finsupp.ext_iff.mp (congrArg Subtype.val h) 0
    simp [v₀, v₁] at h0
  letI : Finite {v : ℕ →₀ ℕ // IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v = 2} :=
    IntegerOccupation.finite_norm_fiber (fun k => (RationalPrimeOneOff.primeNorm_prime P k).two_le)
      (by simpa only [RationalPrimeOneOff.roundedAtom] using
        RationalPrimeOneOff.summable_exp_roundedAtom P (a := 2) (by norm_num)) 2
  letI : Fintype {v : ℕ →₀ ℕ // IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v = 2} :=
    Fintype.ofFinite _
  have hcard : ({⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩} :
      Finset {v : ℕ →₀ ℕ // IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v = 2}).card ≤
      Fintype.card {v : ℕ →₀ ℕ // IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v = 2} :=
    Finset.card_le_univ _
  rw [Finset.card_pair hv_ne, ← Nat.card_eq_fintype_card] at hcard
  exact hcard

/-- **Zero occupation at `n = 2` at the origin `γ = 0`:**
at `γ = 0`, `1 - cos(0 · u) = 0` bounds `W(log 2) ≤ 65/81 < 1`, so every rounded prime generator
has norm `≥ 3` and `RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams 0) 2 = 0`. -/
theorem rationalPrimeOneOff_zero_at_two_at_origin :
    RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams 0) 2 = 0 := by
  set P := IntegerNormOneOff.fixedParams 0
  have hw_le : ∀ u : ℝ, 0 < u → u ≤ 1 → P.w u ≤ 65 / 81 := by
    intro u hu0 hu1
    unfold DiscreteOneOff.Params.w _root_.RHTower.BeurlingOverRegularIntegers.primeDensity
    rw [div_le_iff₀ hu0, DiscreteOneOff.Params.primeNumerator_eq]
    have hμ : P.μ = 2 / 5 := rfl
    have hν : P.ν = 1 / 10 := rfl
    have hγ : P.γ = 0 := rfl
    rw [hμ, hν, hγ, zero_mul, Real.cos_zero, sub_self, mul_zero, zero_add]
    set y₁ : ℝ := (1 / 10 : ℝ) * u
    set y₂ : ℝ := (2 / 5 : ℝ) * u
    have hy₁_pos : 0 < y₁ := by dsimp only [y₁]; positivity
    have hy₂_pos : 0 < y₂ := by dsimp only [y₂]; positivity
    have hy₁_le : y₁ ≤ 1 / 10 := by dsimp only [y₁]; linarith
    have hy₂_le : y₂ ≤ 2 / 5 := by dsimp only [y₂]; linarith
    have hexp_y₁ : (1 - y₁) * Real.exp y₁ ≤ 1 := by
      calc (1 - y₁) * Real.exp y₁
          ≤ Real.exp (-y₁) * Real.exp y₁ :=
            mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-y₁)]) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hexp_y₁_ub : Real.exp y₁ ≤ 10 / 9 := by nlinarith
    have hsub_y₁ : Real.exp y₁ - 1 ≤ (1 / 9 : ℝ) * u := by dsimp only [y₁] at hexp_y₁; nlinarith
    have hexp_y₁_ge1 : 1 ≤ Real.exp y₁ := Real.one_le_exp hy₁_pos.le
    have ht₁ : (Real.exp y₁ - 1) ^ 2 / Real.exp y₁ ≤ (1 / 81 : ℝ) * u := by
      have hsq : (Real.exp y₁ - 1) ^ 2 ≤ ((1 / 9 : ℝ) * u) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hsub_y₁ 2
      have hdiv : (Real.exp y₁ - 1) ^ 2 / Real.exp y₁ ≤ (Real.exp y₁ - 1) ^ 2 :=
        div_le_self (sq_nonneg _) hexp_y₁_ge1
      nlinarith
    have hexp_y₂ : (1 - y₂) * Real.exp y₂ ≤ 1 := by
      calc (1 - y₂) * Real.exp y₂
          ≤ Real.exp (-y₂) * Real.exp y₂ :=
            mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-y₂)]) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hexp_y₂_ub : Real.exp y₂ ≤ 5 / 3 := by nlinarith
    have hsub_y₂ : Real.exp y₂ - 1 ≤ (2 / 3 : ℝ) * u := by dsimp only [y₂] at hexp_y₂; nlinarith
    have hexp_y₂_ge1 : 1 ≤ Real.exp y₂ := Real.one_le_exp hy₂_pos.le
    have ht₂ : (Real.exp y₂ - 1) ^ 3 * (Real.exp y₂ + 1) / Real.exp y₂ ≤ (64 / 81 : ℝ) * u := by
      have hcube : (Real.exp y₂ - 1) ^ 3 ≤ ((2 / 3 : ℝ) * u) ^ 3 :=
        pow_le_pow_left₀ (by linarith) hsub_y₂ 3
      have hprod : (Real.exp y₂ - 1) ^ 3 * (Real.exp y₂ + 1) ≤ ((2 / 3 : ℝ) * u) ^ 3 * (8 / 3) :=
        mul_le_mul hcube (by linarith) (by linarith) (by positivity)
      have hdiv : (Real.exp y₂ - 1) ^ 3 * (Real.exp y₂ + 1) / Real.exp y₂ ≤
          (Real.exp y₂ - 1) ^ 3 * (Real.exp y₂ + 1) :=
        div_le_self (mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)) hexp_y₂_ge1
      have hu3 : u ^ 3 ≤ u := by nlinarith [sq_nonneg u]
      nlinarith
    have hpref : Real.exp (-((3 * (2 / 5 : ℝ) - 1) * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-((3 * (2 / 5 : ℝ) - 1) * u)) *
          ((Real.exp y₁ - 1) ^ 2 / Real.exp y₁ +
            (Real.exp y₂ - 1) ^ 3 * (Real.exp y₂ + 1) / Real.exp y₂)
        ≤ 1 * ((1 / 81 : ℝ) * u + (64 / 81 : ℝ) * u) :=
          mul_le_mul hpref (add_le_add ht₁ ht₂) (by positivity) zero_le_one
      _ = 65 / 81 * u := by ring
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos two_pos]
  have hW_lt1 : P.W (Real.log 2) < 1 := by
    rw [P.W_eq_intervalIntegral hlog2_pos.le]
    have hmono : (∫ u in (0 : ℝ)..Real.log 2, P.wt u) ≤ ∫ _u in (0 : ℝ)..Real.log 2, (65 / 81 : ℝ) := by
      refine intervalIntegral.integral_mono_on hlog2_pos.le
        (P.intervalIntegrable_wt le_rfl hlog2_pos.le) intervalIntegrable_const fun u hu => ?_
      unfold DiscreteOneOff.Params.wt
      by_cases hu0 : u ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hu0]
        exact hw_le u hu0 (hu.2.trans hlog2_le1)
      · rw [Set.indicator_of_notMem hu0]; norm_num
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    nlinarith
  have hatom0_gt : Real.log 2 < P.atom 0 := by
    by_contra hle
    have hW_ge := P.W_le_W (le_of_not_gt hle)
    rw [P.W_atom 0] at hW_ge
    norm_num at hW_ge
    linarith
  have hp_ge3 (k : ℕ) : 3 ≤ RationalPrimeOneOff.primeNorm P k := by
    have hexp_gt2 : 2 < Real.exp (P.atom k) := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
        _ < Real.exp (P.atom 0) := Real.exp_lt_exp.mpr hatom0_gt
        _ ≤ Real.exp (P.atom k) := Real.exp_le_exp.mpr (P.atom_zero_le k)
    have hp_gt2 : (2 : ℝ) < (RationalPrimeOneOff.primeNorm P k : ℝ) :=
      hexp_gt2.trans_le (RationalPrimeOneOff.le_nextPrime _)
    have hp_nat : 2 < RationalPrimeOneOff.primeNorm P k := by exact_mod_cast hp_gt2
    omega
  haveI : IsEmpty {v : ℕ →₀ ℕ // IntegerOccupation.norm (RationalPrimeOneOff.primeNorm P) v = 2} := by
    refine ⟨fun ⟨v, hv⟩ => ?_⟩
    by_cases hv0 : v = 0
    · rw [hv0, IntegerOccupation.norm_zero] at hv; omega
    · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
        by_contra hnone
        exact hv0 (Finsupp.ext fun k => not_ne_iff.mp fun hk => hnone ⟨k, hk⟩)
      have hdvd : RationalPrimeOneOff.primeNorm P k ∣ 2 :=
        hv ▸ IntegerOccupation.dvd_norm_of_ne_zero hk
      have hle2 := Nat.le_of_dvd two_pos hdvd
      have hge3 := hp_ge3 k
      omega
  simp [RationalPrimeOneOff.integerCoeff, IntegerOccupation.coeff]

/-- **Failure of unit occupation across `|γ| ≤ 184`:**
for every `|γ| ≤ 184`, `RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ)` is not
identically `1` on `n ≥ 1` (by `n = 2` at `γ = 0`, and by identity-theorem continuation on the
convex quadrant `{17/30 < Re s ∧ 0 < Im s}` against
`riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour` for `0 < |γ| ≤ 184`). -/
theorem rationalPrimeOneOff_not_unit_occupation_of_abs_le_184 {γ : ℝ} (hγ : |γ| ≤ 184) :
    ∃ n : ℕ, 1 ≤ n ∧ RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) n ≠ 1 := by
  by_contra hnot
  have hall : ∀ n : ℕ, 1 ≤ n →
      RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) n = 1 :=
    fun n hn => not_ne_iff.mp fun hne => hnot ⟨n, hn, hne⟩
  rcases eq_or_ne γ 0 with rfl | hγ0
  · have h2 := hall 2 (by norm_num)
    rw [rationalPrimeOneOff_zero_at_two_at_origin] at h2
    norm_num at h2
  · set g : ℝ := |γ|
    have hg_pos : 0 < g := abs_pos.mpr hγ0
    set P := IntegerNormOneOff.fixedParams γ
    set U_quad : Set ℂ := {s : ℂ | 17 / 30 < s.re ∧ 0 < s.im}
    have hU_open : IsOpen U_quad :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hU_conv : Convex ℝ U_quad := by
      intro x hx y hy a b ha hb hab
      have hx1 : 17 / 30 < x.re := hx.1
      have hy1 : 17 / 30 < y.re := hy.1
      have hx2 : 0 < x.im := hx.2
      have hy2 : 0 < y.im := hy.2
      refine ⟨?_, ?_⟩
      · change 17 / 30 < (a • x + b • y).re
        rw [Complex.add_re, Complex.real_smul, Complex.real_smul,
          Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.ofReal_re, Complex.ofReal_im]
        rcases ha.eq_or_lt with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          rw [hb1]; linarith
        · have hax : (17 / 30 : ℝ) * a < a * x.re := by nlinarith
          have hby : (17 / 30 : ℝ) * b ≤ b * y.re := by nlinarith
          linarith
      · change 0 < (a • x + b • y).im
        rw [Complex.add_im, Complex.real_smul, Complex.real_smul,
          Complex.mul_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.ofReal_re, Complex.ofReal_im]
        rcases ha.eq_or_lt with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          rw [hb1]; linarith
        · have hax : 0 < a * x.im := mul_pos ha_pos hx2
          have hby : 0 ≤ b * y.im := mul_nonneg hb hy2.le
          linarith
    have hU_prec : IsPreconnected U_quad := hU_conv.isPreconnected
    have hF_anal : AnalyticOnNhd ℂ (RationalPrimeOneOff.continuation P) U_quad := by
      refine ((RationalPrimeOneOff.differentiableOn_continuation P).mono ?_).analyticOnNhd hU_open
      intro s hs
      exact ⟨hs.1, fun h1 => hs.2.ne' (by rw [h1, Complex.one_im])⟩
    have hζ_anal : AnalyticOnNhd ℂ riemannZeta U_quad := by
      refine (DifferentiableOn.analyticOnNhd ?_ hU_open)
      intro s hs
      exact (differentiableAt_riemannZeta
        (fun h1 => hs.2.ne' (by rw [h1, Complex.one_im]))).differentiableWithinAt
    set w₁ : ℂ := 2 + Complex.I
    have hw₁ : w₁ ∈ U_quad := by
      dsimp only [U_quad, w₁]
      exact ⟨by simp; norm_num, by simp⟩
    have hev : RationalPrimeOneOff.continuation P =ᶠ[𝓝 w₁] riemannZeta := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by dsimp only [w₁]; simp : (1 : ℝ) < w₁.re)] with s hs
      have hcongr : ∀ {n : ℕ}, n ≠ 0 →
          (RationalPrimeOneOff.integerCoeff P n : ℂ) = (1 : ℕ → ℂ) n := by
        intro n hn0
        rw [hall n (Nat.pos_of_ne_zero hn0)]
        simp
      rw [← (RationalPrimeOneOff.hasSum_integerCoeff P hs).LSeries_eq,
        LSeries_congr hcongr s, LSeries_one_eq_riemannZeta hs]
    have heqOn := hF_anal.eqOn_of_preconnected_of_eventuallyEq hζ_anal hU_prec hw₁ hev
    set z₀ : ℂ := (3 / 5 : ℂ) + (g : ℂ) * Complex.I
    have hz₀U : z₀ ∈ U_quad := by
      dsimp only [U_quad, z₀]
      constructor
      · simp; norm_num
      · simp [hg_pos]
    have hz₀_F : RationalPrimeOneOff.continuation P z₀ = 0 := by
      rw [RationalPrimeOneOff.continuation_eq_zero_iff]
      have hpair := P.zeros_right_of_eq_pair (h := (1 / 15 : ℝ))
        (by norm_num [P, IntegerNormOneOff.fixedParams]) (by norm_num)
      have hmem : z₀ ∈ ({((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * Complex.I,
          ((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * Complex.I} : Set ℂ) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases abs_choice γ with h | h
        · left
          dsimp only [z₀, g, P, IntegerNormOneOff.fixedParams]
          rw [h]; push_cast; ring
        · right
          dsimp only [z₀, g, P, IntegerNormOneOff.fixedParams]
          rw [h]; push_cast; ring
      rw [← hpair] at hmem
      exact hmem.2.2
    have hz₀_ζ : riemannZeta z₀ = 0 := (heqOn hz₀U).symm.trans hz₀_F
    have hz₀_re : z₀.re = 3 / 5 := by simp [z₀]
    have hz₀_im : z₀.im = g := by simp [z₀]
    exact (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
      (s := z₀)
      (by rw [hz₀_re]; norm_num)
      (by rw [hz₀_re]; norm_num)
      (by rw [hz₀_re]; norm_num)
      (by rw [hz₀_im, abs_of_pos hg_pos]; exact hγ)).1 hz₀_ζ

/-- **Universal non-unit occupation of `RationalPrimeOneOff` across all `γ ∈ ℝ`:**
at **every** real ordinate `γ`, `RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ)`
differs from the unit integer-semigroup weight `1` at some `n ≥ 1` (with explicit collision
`2 ≤ integerCoeff P 2` whenever `184 < |γ|`). -/
theorem rationalPrimeOneOff_never_unit_integer_occupation (γ : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) n ≠ 1 := by
  rcases le_or_gt |γ| 184 with hle | hgt
  · exact rationalPrimeOneOff_not_unit_occupation_of_abs_le_184 hle
  · refine ⟨2, by norm_num, ?_⟩
    have h2 := rationalPrimeOneOff_superUnit_at_two_of_abs_gt_184 hgt
    omega

/-! ### Section 2: Exact Integer-Semigroup Vaughan Möbius Annihilation & `Aff(ℚ)` Successor Firewall -/

/-- **Exact Dirichlet-ring characterization of sub-horizon Vaughan Type-I Möbius annihilation:**
for any arithmetic function `a : ArithmeticFunction ℝ`, the truncated Möbius residual
`(1 : ArithmeticFunction ℝ) - a * truncAF μ W` vanishes on `1 ≤ n ≤ W` for every cutoff `W ≥ 1`
**if and only if** `a = ArithmeticFunction.zeta` (`∀ n ≥ 1, a n = 1`). -/
theorem subhorizon_mobius_annihilation_iff_eq_zeta (a : ArithmeticFunction ℝ) :
    (∀ W k : ℕ, 1 ≤ k → k ≤ W →
      ((1 : ArithmeticFunction ℝ) -
        a * _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) k = 0) ↔
    a = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  constructor
  · intro hann
    have hamu : a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
      ext k
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        have hk := hann k k hk1 le_rfl
        have hsub : ((1 : ArithmeticFunction ℝ) -
            a * _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) k) k =
            (1 : ArithmeticFunction ℝ) k -
              (a * _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) k) k := rfl
        rw [hsub, sub_eq_zero] at hk
        have hsame : (a * _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) k) k =
            (a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) k := by
          rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp2_le : p.2 ≤ k :=
            Nat.le_of_dvd hk1 ⟨p.1, by rw [mul_comm]; exact (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩
          rw [_root_.RHTower.Sieve.truncAF_apply, if_pos hp2_le]
        rw [← hsame, ← hk]
    calc a = a * 1 := (mul_one a).symm
      _ = a * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
          rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      _ = (a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := (mul_assoc _ _ _).symm
      _ = 1 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by rw [hamu]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := one_mul _
  · rintro rfl W k hk1 hkW
    exact _root_.RHTower.Sieve.one_sub_zeta_mul_truncAF_moebius_apply_eq_zero hk1 hkW

/-- Arithmetic function `n ↦ (RationalPrimeOneOff.integerCoeff P n : ℝ)` of the rational-prime
Beurling one-off model. -/
def rationalPrimeOneOffAF (γ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) n : ℝ), by
    simp [RationalPrimeOneOff.integerCoeff,
      IntegerOccupation.coeff_zero
        (fun k => (RationalPrimeOneOff.primeNorm_prime (IntegerNormOneOff.fixedParams γ) k).two_le)]⟩

/-- **Explicit failure of sub-horizon Vaughan Möbius annihilation on `RationalPrimeOneOff` above
height `184` and coupled `Aff(ℚ)` integer-successor positivity firewall:**
1. For **every** `184 < |γ|` and **every** Möbius cutoff `W ≥ 2`, the sub-horizon Vaughan residual
   `((1 : ArithmeticFunction ℝ) - rationalPrimeOneOffAF γ * truncAF μ W) 2` is `≤ -1 < 0`
   (failing sub-horizon prime removal at `p = 2`), whereas `typeIIShort W 2 = 0` for `ζ`.
2. For **every** `γ ∈ ℝ`, `rationalPrimeOneOffAF γ ≠ ArithmeticFunction.zeta`, so global
   sub-horizon Möbius annihilation fails at every ordinate.
3. Simultaneously on `Aff(ℚ)`, adjoining the integer successor `x ↦ x + 1` restricts positive
   definiteness of `heckeState s` to `1 / 2 ≤ s` (`isPosDefOnGroup_heckeState_iff`), whereas on the
   pure multiplicative dilation group `ℚˣ` every exponent `0 ≤ s` is positive definite
   (`isPosDefOnGroup_dilation_powerWeight`). -/
theorem integer_semigroup_vaughan_and_affQ_successor_firewall :
    (∀ {γ : ℝ} {W : ℕ}, 184 < |γ| → 2 ≤ W →
      ((1 : ArithmeticFunction ℝ) -
        rationalPrimeOneOffAF γ *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) 2 ≤ -1 ∧
      _root_.RHTower.Sieve.typeIIShort W 2 = 0) ∧
    (∀ γ : ℝ, ¬ ∀ W k : ℕ, 1 ≤ k → k ≤ W →
      ((1 : ArithmeticFunction ℝ) -
        rationalPrimeOneOffAF γ *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) k = 0) ∧
    (∀ s : ℝ, IsPosDefOnGroup (heckeState s) ↔ 1 / 2 ≤ s) := by
  refine ⟨?_, ?_, isPosDefOnGroup_heckeState_iff⟩
  · intro γ W hγ hW
    refine ⟨?_, _root_.RHTower.Sieve.one_sub_zeta_mul_truncAF_moebius_apply_eq_zero (by norm_num) hW⟩
    set P := IntegerNormOneOff.fixedParams γ
    have ha1 : rationalPrimeOneOffAF γ 1 = 1 := by
      change (RationalPrimeOneOff.integerCoeff P 1 : ℝ) = 1
      rw [RationalPrimeOneOff.integerCoeff,
        IntegerOccupation.coeff_one (fun k => (RationalPrimeOneOff.primeNorm_prime P k).two_le)]
      norm_num
    have ha2 : (2 : ℝ) ≤ rationalPrimeOneOffAF γ 2 := by
      change (2 : ℝ) ≤ (RationalPrimeOneOff.integerCoeff P 2 : ℝ)
      exact_mod_cast rationalPrimeOneOff_superUnit_at_two_of_abs_gt_184 hγ
    have hsub : ((1 : ArithmeticFunction ℝ) -
        rationalPrimeOneOffAF γ *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) 2 =
        (1 : ArithmeticFunction ℝ) 2 -
          (rationalPrimeOneOffAF γ *
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) 2 := rfl
    have hanti : (2 : ℕ).divisorsAntidiagonal = {(1, 2), (2, 1)} := by decide
    rw [hsub, ArithmeticFunction.one_apply, if_neg (by norm_num : (2 : ℕ) ≠ 1),
      ArithmeticFunction.mul_apply, hanti, Finset.sum_pair (by decide : ((1 : ℕ), 2) ≠ (2, 1)),
      _root_.RHTower.Sieve.truncAF_apply, if_pos hW,
      _root_.RHTower.Sieve.truncAF_apply, if_pos (by omega : 1 ≤ W),
      ha1]
    have hmu2 : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) 2) = -1 := by
      change ((ArithmeticFunction.moebius 2 : ℤ) : ℝ) = -1
      rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      norm_num
    have hmu1 : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) 1) = 1 := by
      change ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) = 1
      simp
    rw [hmu2, hmu1]
    linarith
  · intro γ hann
    have heq := (subhorizon_mobius_annihilation_iff_eq_zeta (rationalPrimeOneOffAF γ)).mp hann
    obtain ⟨n, hn1, hne⟩ := rationalPrimeOneOff_never_unit_integer_occupation γ
    have hn_eq := congrArg (fun f : ArithmeticFunction ℝ => f n) heq
    have hzeta_n : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n) = 1 := by
      simp [ArithmeticFunction.zeta_apply, show n ≠ 0 by omega]
    change (RationalPrimeOneOff.integerCoeff (IntegerNormOneOff.fixedParams γ) n : ℝ) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n) at hn_eq
    rw [hzeta_n] at hn_eq
    exact hne (by exact_mod_cast hn_eq)

/-! ### Section 3: Unconditional Sub-Farkas Abscissa Improvement Beyond `2401 / 19200` to `20011 / 160000` & Coupled Born-Excess Dichotomy -/

/-- **Unconditional Stage-1 vertex improvement strictly beyond `2401 / 19200` (`20011 / 160000`)
and matching unconstrained `ℝ³` Farkas barrier (`2133606 / 17059187`):**
1. `HeckeZeroSupremum.beta ≤ 139989 / 160000 < 3281 / 3750 < 16799 / 19200 < 40535 / 46328 < 20999 / 24000`;
2. Every zero of `riemannZeta` with `0 < Re ρ` lies in `[20011 / 160000, 139989 / 160000]`, with
   `20011 / 160000 = 0.12506875 > 469 / 3750 > 2401 / 19200 > 3001 / 24000`;
3. Over all unconstrained `(lx, ly, ℓ) ∈ ℝ³`, pushing `lowBoundaryGen lx ly ℓ ≤ 14925581 / 17059187`
   (`1 - 14925581 / 17059187 = 2133606 / 17059187`, within `< 2.05 × 10^{-6}` of `20011 / 160000`)
   forces at least one of the three Stage-1 bins `40/103`, `127/327`, `87/224` to have strictly
   positive `endpointExponent`. -/
theorem stage1_vertex_strictly_improves_sub_farkas_and_all_walls :
    MetaplecticMobiusDescent.CubicEisenstein.HeckeZeroSupremum.beta ≤ 139989 / 160000 ∧
    (3001 / 24000 : ℝ) < 2401 / 19200 ∧
    (2401 / 19200 : ℝ) < 469 / 3750 ∧
    (469 / 3750 : ℝ) < 20011 / 160000 ∧
    (∀ {ρ : ℂ}, 0 < ρ.re → ρ.re < 20011 / 160000 → riemannZeta ρ ≠ 0) ∧
    (∀ {ρ : ℂ}, 0 < ρ.re → riemannZeta ρ = 0 →
      ρ.re ∈ Set.Icc (20011 / 160000 : ℝ) (139989 / 160000 : ℝ)) ∧
    ((2133606 / 17059187 : ℝ) - 20011 / 160000 < 205 / 100000000) :=
  ⟨MetaplecticMobiusDescent.CubicEisenstein.Stage1TrueVertexZeroFree.hecke_beta_le_stage1_vertex,
    by norm_num, by norm_num, by norm_num,
    fun h0 h1 => MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_stage1_vertex_left h0 h1,
    fun h0 hz => MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_stage1_vertex_strip h0 hz,
    by norm_num⟩

/-- **Unconditional pointwise `HasStrictPrimeGasWitness` strictly beyond `2401 / 19200` across all
heights `|Im s| > 184` (and all `Im s ∈ ℝ`):**
at **every** `s ∈ ℂ` with `0 < Re s < 20011 / 160000` (`20011 / 160000 - 2401 / 19200 = 13 / 960000 > 0`)
and **every** horizon `L_hor > 0`, a certified PrimeGas witness strictly beats its error bound. -/
theorem hasStrictPrimeGasWitness_beyond_2401_wall :
    (2401 / 19200 : ℝ) < 20011 / 160000 ∧
    ∀ {s : ℂ} (hs0 : 0 < s.re), s.re < 20011 / 160000 → ∀ {L_hor : ℝ}, 0 < L_hor →
      HasStrictPrimeGasWitness s hs0 L_hor := by
  refine ⟨by norm_num, fun {s} hs0 hlt {L_hor} hL => ?_⟩
  exact (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 (by linarith) hL).mpr
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_stage1_vertex_left hs0 hlt)

/-- **Upgraded unconditional left-hand zero exclusion and super-dispersion discharge beyond
`2401 / 19200`:**
for every `ρ ∈ ℂ` with `0 < Re ρ < 1 / 2` and `Re ρ < 20011 / 160000 ∨ |Im ρ| ≤ 184`,
`riemannZeta ρ ≠ 0` holds unconditionally, and hence the super-dispersion implication in
`zeta_zero_forces_superDispersion_iff_ne_zero` holds unconditionally at `(ρ, k₀)` for every `k₀ ∈ ℤ`. -/
theorem unconditional_left_zero_exclusion_beyond_2401_and_low_height {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2)
    (hreg : ρ.re < 20011 / 160000 ∨ |ρ.im| ≤ 184) (k₀ : ℤ) :
    riemannZeta ρ ≠ 0 ∧
    (riemannZeta ρ = 0 →
      ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
        ∃ c : ℝ, 0 < c ∧
          ∀ᶠ j : ℕ in atTop,
            bornLogDispersionCoeff ρ.re ρ.im k₀ + c ≤
              Real.log ((φ j + 2 : ℕ) : ℝ) *
                (bornLorentzianLimit ρ.re ρ.im k₀ -
                  ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖)) := by
  have hne : riemannZeta ρ ≠ 0 := by
    rcases hreg with hsub | hlow
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_stage1_vertex_left
        hρ0 hsub
    · exact (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
        hρ0 (by linarith only [hρ1]) hρ1.ne hlow).1
  exact ⟨hne, (zeta_zero_forces_superDispersion_iff_ne_zero hρ0 hρ1 k₀).mpr hne⟩

/-- **Coupled Zero-Forced Single-Mode Prime Excess, Vaughan Mollifier-Square Floor, and Super-`2401/19200`
Exclusion Dichotomy:**
for **every** subcritical point `ρ ∈ ℂ` (`0 < Re ρ < 1 / 2`):
1. **Unconditional exclusion & strict PrimeGas witness on `Re ρ < 20011 / 160000 ∨ |Im ρ| ≤ 184`:**
   `riemannZeta ρ ≠ 0` and `HasStrictPrimeGasWitness ρ hρ0 L_hor` holds for all `L_hor > 0`.
2. **Simultaneous antipodal Vaughan mollifier-square floor and unbounded `(N + 2)^α`-scaled
   single-mode Born excess on the narrowed surviving region:**
   if `riemannZeta ρ = 0`, then `20011 / 160000 ≤ Re ρ` and `184 < |Im ρ|`, and simultaneously:
   - for all `U, V : ℕ`, `(1 / 4 : ℝ) < ‖analyticDualBilinearGen U V (1 - ρ)‖` (whereas on the
     `max U V`-rough semigroup `vaughanDualBilinear U V k = d(k) - 2`);
   - for every nonzero Fourier mode `k₀ ≠ 0`, every `α ∈ (Re ρ, 1 / 2)`, and every `c > 0`,
     `ζ(ρ) = 0` forces unbounded cutoff sequences along which the `(N + 2)^α`-scaled reconstructed
     deficit, reconstructed excess, dyadic single-mode window excess, and direct smooth-subtracted
     Born-mode excess `‖bornCoefficient ρ.re ρ.im k₀ N - smoothBornCoefficient ρ.re ρ.im k₀ N‖`
     all exceed `c`. -/
theorem coupled_born_power_excess_vaughan_mollifier_and_super2401_exclusion {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2) :
    ((ρ.re < 20011 / 160000 ∨ |ρ.im| ≤ 184) →
      riemannZeta ρ ≠ 0 ∧ ∀ {L_hor : ℝ}, 0 < L_hor → HasStrictPrimeGasWitness ρ hρ0 L_hor) ∧
    (riemannZeta ρ = 0 →
      (20011 / 160000 : ℝ) ≤ ρ.re ∧
      184 < |ρ.im| ∧
      (∀ U V : ℕ, (1 / 4 : ℝ) < ‖analyticDualBilinearGen U V (1 - ρ)‖) ∧
      (∀ {k₀ : ℤ}, k₀ ≠ 0 → ∀ {α : ℝ}, ρ.re < α → α < 1 / 2 → ∀ {c : ℝ}, 0 < c →
        (∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∀ j : ℕ, c ≤ ((φ j + 2 : ℕ) : ℝ) ^ α *
            (1 - bornExtractedTheta ρ.re ρ.im k₀ (φ j) / ((φ j + 2 : ℕ) : ℝ))) ∧
        (∃ ψ : ℕ → ℕ, Tendsto ψ atTop atTop ∧
          ∀ j : ℕ, c ≤ ((ψ j + 2 : ℕ) : ℝ) ^ α *
            (bornExtractedTheta ρ.re ρ.im k₀ (ψ j) / ((ψ j + 2 : ℕ) : ℝ) - 1)) ∧
        (∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
          ∀ j : ℕ, c ≤ (χ j : ℝ) ^ α *
            (bornModeDyadicWindow ρ.re ρ.im k₀ (χ j) / Real.sqrt (χ j : ℝ) -
              2 * (1 - (Real.sqrt 2)⁻¹))) ∧
        (∃ ω : ℕ → ℕ, Tendsto ω atTop atTop ∧
          ∀ j : ℕ, c < ((ω j + 2 : ℕ) : ℝ) ^ α *
            ‖bornCoefficient ρ.re ρ.im k₀ (ω j) - smoothBornCoefficient ρ.re ρ.im k₀ (ω j)‖))) := by
  refine ⟨?_, ?_⟩
  · intro hreg
    have hne := (unconditional_left_zero_exclusion_beyond_2401_and_low_height hρ0 hρ1 hreg 1).1
    exact ⟨hne, fun {L_hor} hL =>
      (hasStrictPrimeGasWitness_iff_zeta_ne_zero hρ0 (by linarith) hL).mpr hne⟩
  · intro hζ
    have hre_ge : (20011 / 160000 : ℝ) ≤ ρ.re :=
      le_of_not_gt fun hlt =>
        (unconditional_left_zero_exclusion_beyond_2401_and_low_height hρ0 hρ1 (Or.inl hlt) 1).1 hζ
    have him_gt : 184 < |ρ.im| :=
      lt_of_not_ge fun hle =>
        (unconditional_left_zero_exclusion_beyond_2401_and_low_height hρ0 hρ1 (Or.inr hle) 1).1 hζ
    refine ⟨hre_ge, him_gt,
      fun U V => analyticDualBilinearGen_dichotomy_and_posTruncatedZeta_separation.1 U V hρ0 hρ1 hζ,
      fun {k₀} hk₀ {α} hα_lo hα_hi {c} hc => ?_⟩
    obtain ⟨_, hdef, hexc, hdyad⟩ :=
      zeta_zero_forces_single_mode_power_deficit_and_excess hρ0 hρ1 hζ hk₀ hα_lo hα_hi hc
    obtain ⟨ω, hω, hdir⟩ :=
      zeta_zero_forces_direct_bornCoefficient_sub_smooth_power_excess hρ0 hρ1 hζ hk₀ hα_lo hα_hi hc
    exact ⟨hdef, hexc, hdyad, ⟨ω, hω, hdir⟩⟩

#print axioms GaloisForLFunctions.FamilyContinuationTheory.Budget.stage1_endpointExponent_three_bin_pos_of_lowBoundaryGen_le
#print axioms GaloisForLFunctions.FamilyContinuationTheory.Budget.stage1_vertex_within_two_millionths_of_farkas_barrier
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.Stage1TrueVertexZeroFree.hecke_beta_le_stage1_vertex
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_stage1_vertex_lt_re
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_stage1_vertex_left
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_stage1_vertex_strip
#print axioms rationalPrimeOneOff_superUnit_at_two_of_abs_gt_184
#print axioms rationalPrimeOneOff_zero_at_two_at_origin
#print axioms rationalPrimeOneOff_not_unit_occupation_of_abs_le_184
#print axioms rationalPrimeOneOff_never_unit_integer_occupation
#print axioms subhorizon_mobius_annihilation_iff_eq_zeta
#print axioms integer_semigroup_vaughan_and_affQ_successor_firewall
#print axioms stage1_vertex_strictly_improves_sub_farkas_and_all_walls
#print axioms hasStrictPrimeGasWitness_beyond_2401_wall
#print axioms unconditional_left_zero_exclusion_beyond_2401_and_low_height
#print axioms coupled_born_power_excess_vaughan_mollifier_and_super2401_exclusion

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
