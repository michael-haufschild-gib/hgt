import GaloisForLFunctions.RHTower.PMPowerDampedMobiusNymanSeries
import GaloisForLFunctions.RHTower.StepFunctionCarrier
import GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance

/-!
# Discrete energy criterion for the power-damped Möbius Fermi source

Centering the divisor coefficients `c_ε(n) = ∑_{d ∣ n} μ(d) d^{-ε}` at their mean density
`Re(1/ζ(1+ε))` gives centered prefixes `P_ε(n) = ∑_{j ≤ n} (c_ε(j) - Re(1/ζ(1+ε)))`, and the
divisor remainder becomes `R_ε(x) = P_ε(⌊x⌋) - {x}/ζ(1+ε)`. Since a step function `s(⌊x⌋)/x`
lies in `L²(1, ∞)` iff `∑ s(n+1)²/((n+1)(n+2))` converges, the continuous divisor-energy
criterion becomes a discrete one: for `ε > 0`, the Fermi source `F_ε` lies in `L²(0, ∞)` iff
the discrete energies `E_ε(T) = ∑_{n ≤ T} P_ε(n)²/(n(n+1))` are bounded in `T`. The energy is
also written as the covariance form `∑_{j,k ≤ T} c̃_j c̃_k (1/max(j,k) - 1/(T+1))`.

## Main results

- `memLp_stepFun_iff_summable`: `s(⌊x⌋)/x ∈ L²(1, ∞)` iff `∑ s(n+1)²/((n+1)(n+2)) < ∞`.
- `pmPowerDampedDivisorRemainder_eq_centered_prefix`: `R_ε(x) = P_ε(⌊x⌋) - {x}/ζ(1+ε)` for
  `ε > 0`, `x ≥ 0`.
- `pmPowerDampedFermiSource_memLp_iff_discrete_energy`: for `ε > 0`, `F_ε ∈ L²(0, ∞)` iff
  `∑ P_ε(n+1)²/((n+1)(n+2))` converges.
- `pmPowerDampedDivisorDiscreteEnergy_eq_covariance`: covariance form of `E_ε(T)`.
- `pmPowerDampedFermiSource_memLp_iff_discrete_budget`: for `ε > 0`, `F_ε ∈ L²(0, ∞)` iff
  `E_ε(T)` is bounded above uniformly in `T`.
- `exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le`: `E_ε(T)` is bounded for `ε ≥ 1/2`.
- `riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget`: bounded discrete energy at
  arbitrarily small `ε > 0` implies the Riemann hypothesis.

## Hypotheses

The equivalences and the `ε ≥ 1/2` bound are unconditional, given the stated ranges `0 < ε`
or `1/2 ≤ ε`. `riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget` is conditional on the
unproved cofinal premise that for every `δ > 0` some `ε ∈ (0, δ)` has `E_ε(T)` bounded in `T`.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

theorem integrableOn_tailCell_stepEnergy (s : ℕ → ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2) (tailCell n) := by
  rw [tailCell, integrableOn_Ioc_iff_integrableOn_Ioo]
  have hconst := integrableOn_stepGramIntegrand
    (s₁ := fun _ => s (n + 1)) (s₂ := fun _ => s (n + 1))
    (fun _ => le_refl |s (n + 1)|) (fun _ => le_refl |s (n + 1)|)
  have hsub : Ioo ((n : ℝ) + 1) ((n : ℝ) + 2) ⊆ Ioi (1 : ℝ) := by
    intro x hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact lt_of_le_of_lt (by linarith) hx.1
  refine (hconst.mono_set hsub).congr_fun ?_ measurableSet_Ioo
  intro x hx
  have hx0 : 0 ≤ x := by have := Nat.cast_nonneg (α := ℝ) n; linarith [hx.1]
  have hfloor : ⌊x⌋₊ = n + 1 := (Nat.floor_eq_iff hx0).mpr (by
    constructor <;> push_cast <;> linarith [hx.1, hx.2])
  simp only [hfloor]

/-- `s(⌊x⌋)² / x²` is integrable on `(1, ∞)` iff `∑_n s(n+1)²/((n+1)(n+2))` converges
(cell-by-cell integration over `(n+1, n+2]`). -/
theorem integrableOn_stepEnergy_iff_summable (s : ℕ → ℝ) :
    IntegrableOn (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2) (Ioi 1) ↔
      Summable (fun n : ℕ => s (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  constructor
  · intro hi
    have hu : IntegrableOn (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2)
        (⋃ n : ℕ, tailCell n) := by simpa only [iUnion_tailCell] using hi
    have hh := (hasSum_integral_iUnion measurableSet_tailCell pairwise_disjoint_tailCell hu).summable
    simp_rw [integral_tailCell_stepGramIntegrand] at hh
    simpa only [sq] using hh
  · intro hs
    have hn : Summable (fun n : ℕ => ∫ x in tailCell n,
        ‖s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2‖) := by
      have hnorm : (fun x : ℝ => ‖s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2‖) =
          (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2) := by
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_self_nonneg _) (sq_nonneg _))]
      rw [hnorm]
      simp_rw [integral_tailCell_stepGramIntegrand]
      simpa only [sq] using hs
    simpa only [iUnion_tailCell] using
      integrableOn_iUnion_of_summable_integral_norm (integrableOn_tailCell_stepEnergy s) hn

/-- The step function `s(⌊x⌋)/x` lies in `L²(1, ∞)` iff `∑_n s(n+1)²/((n+1)(n+2))` converges. -/
theorem memLp_stepFun_iff_summable (s : ℕ → ℝ) :
    MemLp (stepFun s) 2 bdMeasure ↔
      Summable (fun n : ℕ => s (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_stepFun s).aestronglyMeasurable]
  have he : (fun x : ℝ => ‖stepFun s x‖ ^ 2) =
      (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2) := by
    funext x
    simp only [stepFun, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, inv_pow, sq_abs, sq_abs, inv_pow, sq]
  rw [he]
  exact integrableOn_stepEnergy_iff_summable s

/-- The centered divisor coefficient `c̃_ε(n) = c_ε(n) - Re(1/ζ(1+ε))`. -/
def pmPowerDampedCenteredDivisorCoeff (ε : ℝ) (n : ℕ) : ℝ :=
  pmPowerDampedDivisorCoeff ε n - (pmPowerDampedDivisorDensity ε).re

/-- The centered prefix `P_ε(n) = ∑_{1 ≤ j ≤ n} c̃_ε(j)`. -/
def pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, pmPowerDampedCenteredDivisorCoeff ε j

theorem pmPowerDampedCenteredDivisorPrefix_eq (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      (∑ j ∈ Finset.Icc 1 n, pmPowerDampedDivisorCoeff ε j) -
        (pmPowerDampedDivisorDensity ε).re * (n : ℝ) := by
  simp [pmPowerDampedCenteredDivisorPrefix, pmPowerDampedCenteredDivisorCoeff,
    Finset.sum_sub_distrib, mul_comm]

/-- For `ε > 0` and `x ≥ 0`, `R_ε(x) = P_ε(⌊x⌋) - {x}/ζ(1+ε)`. -/
theorem pmPowerDampedDivisorRemainder_eq_centered_prefix {ε : ℝ} (hε : 0 < ε)
    {x : ℝ} (hx : 0 ≤ x) :
    pmPowerDampedDivisorRemainder ε x =
      (pmPowerDampedCenteredDivisorPrefix ε ⌊x⌋₊ : ℂ) -
        pmPowerDampedDivisorDensity ε * ((Int.fract x : ℝ) : ℂ) := by
  rw [pmPowerDampedDivisorRemainder, pmPowerDampedCenteredDivisorPrefix_eq,
    pmPowerDampedDivisorDensity_eq_ofReal_re hε]
  have hfloor := Int.natCast_floor_eq_floor hx
  have hfract : (⌊x⌋₊ : ℝ) + Int.fract x = x := by
    rw [Int.fract, ← hfloor]
    push_cast
    ring
  dsimp only [pmPowerDampedDivisorSum]
  push_cast
  have hfractC := congrArg (fun y : ℝ => (y : ℂ)) hfract
  push_cast at hfractC
  rw [← hfractC]
  simp only [Complex.ofReal_re]
  ring

/-- The function `{x}/x` lies in `L²(1, ∞)`. -/
theorem memLp_fract_div_bdMeasure :
    MemLp (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) / (x : ℂ)) 2 bdMeasure := by
  have hm : Measurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) / (x : ℂ)) :=
    (Complex.measurable_ofReal.comp measurable_fract).div Complex.measurable_ofReal
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  have he : (fun x : ℝ => ‖((Int.fract x : ℝ) : ℂ) / (x : ℂ)‖ ^ 2) = fractSqInvSq := by
    funext x
    simp only [fractSqInvSq, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    rw [div_eq_mul_inv, inv_pow]
  rw [he]
  exact integrableOn_fractSqInvSq_Ioi one_pos

/-- For `ε > 0`, `R_ε(x)/x ∈ L²(1, ∞)` iff the step function `P_ε(⌊x⌋)/x ∈ L²(1, ∞)`. -/
theorem pmPowerDampedDivisorRemainder_tail_memLp_iff {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun x : ℝ => pmPowerDampedDivisorRemainder ε x / (x : ℂ)) 2 bdMeasure ↔
      MemLp (stepFun (pmPowerDampedCenteredDivisorPrefix ε)) 2 bdMeasure := by
  have hc := memLp_fract_div_bdMeasure.const_mul (pmPowerDampedDivisorDensity ε)
  have he (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      pmPowerDampedDivisorRemainder ε x / (x : ℂ) =
        stepFun (pmPowerDampedCenteredDivisorPrefix ε) x -
          pmPowerDampedDivisorDensity ε * (((Int.fract x : ℝ) : ℂ) / (x : ℂ)) := by
    rw [pmPowerDampedDivisorRemainder_eq_centered_prefix hε
      (le_trans zero_le_one (le_of_lt hx))]
    simp only [stepFun, div_eq_mul_inv]
    ring
  constructor
  · intro hi
    apply (memLp_congr_ae ?_).mp (hi.add hc)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.add_apply, he x hx]
    ring
  · intro hi
    apply (memLp_congr_ae ?_).mp (hi.sub hc)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (he x hx).symm

theorem pm_norm_div_real_sq (z : ℂ) (x : ℝ) :
    ‖z / (x : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / x ^ 2 := by
  simp only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The divisor energy `|R_ε(x)|²/x²` is integrable on `(0, 1]`: on `(0, 1)` it equals the
constant `|1/ζ(1+ε)|²`. -/
theorem integrableOn_pmPowerDampedDivisorEnergy_head (ε : ℝ) :
    IntegrableOn (fun x => ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2)
      (Ioc (0 : ℝ) 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hc : IntegrableOn (fun _ : ℝ => ‖pmPowerDampedDivisorDensity ε‖ ^ 2) (Ioo 0 1) :=
    integrable_const _
  refine hc.congr_fun ?_ measurableSet_Ioo
  intro x hx
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx.1)
  have he : pmPowerDampedDivisorRemainder ε x / (x : ℂ) =
      -pmPowerDampedDivisorDensity ε := by
    simp only [pmPowerDampedDivisorRemainder, pmPowerDampedDivisorSum,
      Nat.floor_eq_zero.mpr hx.2]
    simp
    field_simp
  change ‖pmPowerDampedDivisorDensity ε‖ ^ 2 = ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2
  rw [← pm_norm_div_real_sq, he, norm_neg]

/-- For `ε > 0`, `F_ε ∈ L²(0, ∞)` iff `∑_n P_ε(n+1)²/((n+1)(n+2))` converges. -/
theorem pmPowerDampedFermiSource_memLp_iff_discrete_energy {ε : ℝ} (hε : 0 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      Summable (fun n : ℕ => pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  rw [pmPowerDampedFermiSource_memLp_iff_divisor_energy hε,
    ← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union,
    and_iff_right (integrableOn_pmPowerDampedDivisorEnergy_head ε)]
  have hm : Measurable (fun x : ℝ => pmPowerDampedDivisorRemainder ε x / (x : ℂ)) :=
    (measurable_pmPowerDampedDivisorRemainder ε).div Complex.measurable_ofReal
  have he : (fun x : ℝ => ‖pmPowerDampedDivisorRemainder ε x / (x : ℂ)‖ ^ 2) =
      (fun x : ℝ => ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2) := by
    funext x
    exact pm_norm_div_real_sq _ _
  rw [← he, IntegrableOn, ← memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  exact (pmPowerDampedDivisorRemainder_tail_memLp_iff hε).trans
    (memLp_stepFun_iff_summable _)

/-- The discrete divisor energy `E_ε(T) = ∑_{1 ≤ n ≤ T} P_ε(n)²/(n(n+1))`. -/
def pmPowerDampedDivisorDiscreteEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

/-- Covariance form: `E_ε(T) = ∑_{j,k ≤ T} c̃_ε(j) c̃_ε(k) (1/max(j,k) - 1/(T+1))`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_covariance (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      ∑ j ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 T,
        pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k *
          (1 / (max j k : ℕ) - 1 / ((T : ℝ) + 1)) :=
  DeletionAveragedDivisor.cumulativeEnergy_eq_covariance
    (pmPowerDampedCenteredDivisorCoeff ε) T

theorem pmPowerDampedDivisorDiscreteEnergy_eq_range (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      ∑ n ∈ Finset.range T, pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold pmPowerDampedDivisorDiscreteEnergy
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

/-- For `ε > 0`, `F_ε ∈ L²(0, ∞)` iff there is `B` with `E_ε(T) ≤ B` for every `T`. -/
theorem pmPowerDampedFermiSource_memLp_iff_discrete_budget {ε : ℝ} (hε : 0 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B := by
  rw [pmPowerDampedFermiSource_memLp_iff_discrete_energy hε]
  have hn (n : ℕ) : 0 ≤ pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by positivity
  constructor
  · intro hs
    refine ⟨∑' n : ℕ, pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)), ?_⟩
    intro T
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_range]
    exact hs.sum_le_tsum _ (fun n _ => hn n)
  · rintro ⟨B, hB⟩
    apply summable_of_sum_range_le hn
    intro T
    simpa only [pmPowerDampedDivisorDiscreteEnergy_eq_range] using hB T

/-- Unconditionally, for `ε ≥ 1/2` the discrete energies `E_ε(T)` are bounded uniformly in `T`. -/
theorem exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le {ε : ℝ}
    (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  (pmPowerDampedFermiSource_memLp_iff_discrete_budget (by linarith : 0 < ε)).mp
    (memLp_pmPowerDampedFermiSource_of_half_le hε)

/-- Conditional RH criterion: assuming `h`, that for every `δ > 0` some `ε ∈ (0, δ)` has
`E_ε(T)` bounded uniformly in `T`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_admission
  intro δ hδ
  rcases h δ hδ with ⟨ε, hε, hεδ, hB⟩
  exact ⟨ε, hε, hεδ, (pmPowerDampedFermiSource_memLp_iff_discrete_budget hε).mpr hB⟩

end RHTower
