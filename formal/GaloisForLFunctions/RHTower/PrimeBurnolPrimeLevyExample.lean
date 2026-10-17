import GaloisForLFunctions.RHTower.PrimeBurnolPrimeLevyMeasure
import GaloisForLFunctions.RHTower.PrimeBurnolLevyAsymptotics
import GaloisForLFunctions.RHTower.PrimeBurnolLevyPrimeAction

/-! A positive infinite-prime clock with an injective evolution and unbounded closed backward action. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ENNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def primeLevyRealTerm (x : ℝ) (p : Nat.Primes) : ℝ :=
  (1 - Real.exp (-(x / (p : ℝ)))) / (p : ℝ)

theorem primeLevyRealTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) :
    0 ≤ primeLevyRealTerm x p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  apply div_nonneg _ hp.le
  apply sub_nonneg.mpr
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hx hp.le))

theorem integral_primeLevyAtom_kernel_re (x : ℝ) (p : Nat.Primes) :
    (∫ h : ℝ≥0, (levyLaplaceKernel (x : ℂ) h).re
      ∂((primeLevyControlWeight p : ℝ≥0∞) • Measure.dirac (primeLevyJumpSize p))) =
      primeLevyRealTerm x p := by
  rw [integral_smul_measure, integral_dirac, ENNReal.coe_toReal, smul_eq_mul,
    levyLaplaceKernel_ofReal, Complex.ofReal_re, ← mul_assoc, primeLevy_control_coefficient]
  change (1 / (p : ℝ)) * (1 - Real.exp (-(x * (1 / (p : ℝ))))) = _
  simp only [primeLevyRealTerm, div_eq_mul_inv, one_mul]
  ring

theorem hasSum_primeLevyRealTerm {x : ℝ} (hx : 0 ≤ x) :
    HasSum (primeLevyRealTerm x) (primeLevyData.exponent (x : ℂ)).re := by
  have hi : Integrable (fun h => (levyLaplaceKernel (x : ℂ) h).re) primeLevyControlMeasure :=
    (integrable_levyLaplaceKernel primeLevyControlMeasure hx).re
  have he : (∫ h, (levyLaplaceKernel (x : ℂ) h).re ∂primeLevyControlMeasure) =
      (primeLevyData.exponent (x : ℂ)).re := by
    have hr : (∫ h, (levyLaplaceKernel (x : ℂ) h).re ∂primeLevyControlMeasure) =
        (levyLaplaceJump primeLevyControlMeasure (x : ℂ)).re :=
      integral_re (integrable_levyLaplaceKernel primeLevyControlMeasure hx)
    simpa only [BurnolLevyData.exponent, primeLevyData, NNReal.coe_zero,
      Complex.ofReal_zero, zero_mul, zero_add] using hr
  have hs : HasSum
      (fun p : Nat.Primes => ∫ h : ℝ≥0, (levyLaplaceKernel (x : ℂ) h).re
        ∂((primeLevyControlWeight p : ℝ≥0∞) • Measure.dirac (primeLevyJumpSize p)))
      (primeLevyData.exponent (x : ℂ)).re := by
    rw [← he]
    exact hasSum_integral_measure hi
  simpa only [integral_primeLevyAtom_kernel_re] using hs

theorem tendsto_primeLevyRealTerm (p : Nat.Primes) :
    Tendsto (fun x : ℝ => primeLevyRealTerm x p) atTop (𝓝 (1 / (p : ℝ))) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.Tendsto.atTop_div_const hp tendsto_id)
  simpa only [primeLevyRealTerm, Function.comp_def, sub_zero] using!
    ((tendsto_const_nhds (x := (1 : ℝ))).sub he).div_const (p : ℝ)

/-- Euler's divergent prime harmonic mass forces the actual admitted exponent to infinity. -/
theorem tendsto_primeLevyExponent_atTop :
    Tendsto (fun x : ℝ => (primeLevyData.exponent (x : ℂ)).re) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro M
  have hex : ∃ s : Finset Nat.Primes, M < ∑ p ∈ s, 1 / (p : ℝ) := by
    by_contra h
    apply Nat.Primes.not_summable_one_div
    apply summable_of_sum_le (c := M) (fun p => by positivity)
    intro s
    exact le_of_not_gt fun hs => h ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hex
  have hl : Tendsto (fun x : ℝ => ∑ p ∈ s, primeLevyRealTerm x p) atTop
      (𝓝 (∑ p ∈ s, 1 / (p : ℝ))) :=
    tendsto_finsetSum s (fun p _ => tendsto_primeLevyRealTerm p)
  have he : ∀ᶠ x : ℝ in atTop, M < ∑ p ∈ s, primeLevyRealTerm x p :=
    hl.eventually (Ioi_mem_nhds hs)
  filter_upwards [he, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hsum := hasSum_primeLevyRealTerm hx0
  have hb := hsum.summable.sum_le_tsum s (fun p _ => primeLevyRealTerm_nonneg hx0 p)
  rw [hsum.tsum_eq] at hb
  exact hx.le.trans hb

theorem primeLevyEvolution_injective (t : ℝ≥0) : Function.Injective (primeLevyData.evolution t) :=
  (primeLevyData.evolution_injective_iff t).mpr (by simp [primeLevyData])

theorem primeLevyEvolution_norm (t : ℝ≥0) : ‖primeLevyData.evolution t‖ = 1 := by
  rw [primeLevyData.norm_evolution]
  simp only [primeLevyData, NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero]

theorem primeLevyInverse_graph_eq_backward (t : ℝ≥0) :
    (primeLevyData.minimumNormInverse t).graph = primeLevyData.backwardPrimeGraph t := by
  ext uv
  obtain ⟨u, v⟩ := uv
  rw [primeLevyData.minimumNormInverse_graph_iff_backward]
  apply and_iff_left_of_imp
  intro _
  apply (Submodule.mem_orthogonal _ _).mpr
  intro w hw
  have hz : w = 0 := primeLevyEvolution_injective t (hw.trans (map_zero _).symm)
  rw [hz, inner_zero_left]

/-- The inverse has its original dense physical domain and is not realizable by any bounded map. -/
theorem primeLevyInverse_unbounded {t : ℝ≥0} (ht : 0 < t) :
    ¬ ∃ B : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2,
      ∀ u : (primeLevyData.minimumNormInverse t).domain,
        B u = primeLevyData.minimumNormInverse t u :=
  primeLevyData.minimumNormInverse_not_bounded tendsto_primeLevyExponent_atTop ht
    (by simp [primeLevyData])

end RHTower
