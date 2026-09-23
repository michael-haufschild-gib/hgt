import GaloisForLFunctions.RHTower.MobiusCenteredMertensLimit
import GaloisForLFunctions.RHTower.MobiusPowerSumBoundaryLaplace

/-!
# The causal source limit and the Dirichlet form of the centered limit

`mobius-schur-centered-boundary-limit-law.md` `(11)` and
`mobius-schur-causal-critical-graph-limit-law.md` `(16)`.

The critical centered limit is the reciprocal-zeta Dirichlet series divided by `z`, and any causal
`L¹ ∩ L²` realization of the coupled source converges in `L²(0,∞)` to the incoming pole vector
`e^{-t}`.
-/

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators Topology LSeries.notation Moebius

noncomputable section
namespace RHTower

/-! ### Card `(11)`: the Dirichlet form of the centered limit -/

theorem centeredSchurLimit_eq_lseries {z : ℂ} (hz : 0 < z.re) (hz0 : z ≠ 0) :
    centeredSchurLimit z = (1 / z) * ∑' n : ℕ, LSeries.term (↗μ) (1 + z) n := by
  have hre : 1 < ((1 : ℂ) + z).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hzeta : riemannZeta (1 + z) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  rw [show (∑' n : ℕ, LSeries.term (↗μ) (1 + z) n) = (riemannZeta (1 + z))⁻¹ from
    LSeries_moebius_eq_inv_riemannZeta hre]
  rw [centeredSchurLimit]
  field_simp

/-! ### The incoming causal pole vector -/

/-- The incoming causal pole source `e^{-t}` on the positive ray. -/
def causalPoleVector (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ)) (fun s : ℝ => Complex.exp (-(s : ℂ))) t

theorem measurable_causalPoleVector : Measurable causalPoleVector := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  fun_prop

theorem integrable_causalPoleVector : Integrable causalPoleVector := by
  have hdef : causalPoleVector
      = Set.indicator (Set.Ioi (0 : ℝ)) (fun s : ℝ => Complex.exp (-(s : ℂ))) := rfl
  rw [hdef]
  refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
  have hbase : IntegrableOn (fun s : ℝ => Complex.exp (-((1 : ℂ) * (s : ℂ))))
      (Set.Ioi (0 : ℝ)) volume :=
    GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul (by norm_num)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro s _
  push_cast
  ring_nf

theorem memLp_causalPoleVector : MemLp causalPoleVector 2 volume := by
  have hsq : Integrable (fun t : ℝ => ‖causalPoleVector t‖ ^ (2 : ℕ)) := by
    have hbase : Integrable
        (Set.indicator (Set.Ioi (0 : ℝ)) (fun s : ℝ => Real.exp (-2 * s))) := by
      rw [integrable_indicator_iff measurableSet_Ioi]
      exact exp_neg_integrableOn_Ioi 0 (by norm_num)
    refine Integrable.mono' hbase
      ((measurable_causalPoleVector.norm.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [] with t
    simp only [causalPoleVector]
    rcases le_or_gt t 0 with ht | ht
    · rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (by simpa using ht), norm_zero,
        Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (by simpa using ht)]
      norm_num
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
        Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
      have hnorm : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
        rw [Complex.norm_exp]
        simp
      rw [hnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hsplit : Real.exp (-2 * t) = Real.exp (-t) ^ (2 : ℕ) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
  exact (memLp_two_iff_integrable_sq_norm
    measurable_causalPoleVector.aestronglyMeasurable).mpr hsq

theorem laplaceBoundary_causalPoleVector (y : ℝ) :
    laplaceBoundary causalPoleVector y = 1 / (1 + (y : ℂ) * Complex.I) := by
  have hb : (0 : ℝ) < ((1 : ℂ) + (y : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
    norm_num
  rw [laplaceBoundary]
  have hpt : ∀ u : ℝ,
      Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) * causalPoleVector u
        = Set.indicator (Set.Ioi (0 : ℝ))
            (fun v : ℝ => Complex.exp (-(((1 : ℂ) + (y : ℂ) * Complex.I) * (v : ℂ)))) u := by
    intro u
    simp only [causalPoleVector]
    rcases le_or_gt u 0 with hu | hu
    · rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (by simpa using hu), mul_zero,
        Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (by simpa using hu)]
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu),
        Set.indicator_of_mem (Set.mem_Ioi.mpr hu), ← Complex.exp_add]
      congr 1
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_indicator measurableSet_Ioi,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hb, one_div]

/-! ### Card `(16)`: the strong causal critical limit -/

/-- **Card `(16)`.**  Every causal `L¹ ∩ L²` realization of the coupled source whose boundary
Laplace transform is the coupled causal multiplier converges in `L²(0,∞)` to `e^{-t}`. -/
theorem tendsto_integral_norm_sq_causalSource_sub
    (F : ℝ → ℝ → ℂ)
    (hint : ∀ ω : ℝ, 0 < ω → Integrable (F ω))
    (hmem : ∀ ω : ℝ, 0 < ω → MemLp (F ω) 2 volume)
    (htrans : ∀ ω : ℝ, 0 < ω → ∀ y : ℝ, y ≠ 0 →
      laplaceBoundary (F ω) y = mobiusCausalMultiplier ω ((y : ℂ) * Complex.I)) :
    Tendsto (fun ω : ℝ => ∫ t : ℝ, ‖F ω t - causalPoleVector t‖ ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hkey : ∀ ω : ℝ, 0 < ω →
      (∫ τ : ℝ, ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ ^ (2 : ℕ))
        = 2 * Real.pi * ∫ t : ℝ, ‖F ω t - causalPoleVector t‖ ^ (2 : ℕ) := by
    intro ω hω
    have hi : Integrable (fun u : ℝ => F ω u - causalPoleVector u) :=
      (hint ω hω).sub integrable_causalPoleVector
    have hm : MemLp (fun u : ℝ => F ω u - causalPoleVector u) 2 volume :=
      (hmem ω hω).sub memLp_causalPoleVector
    rw [← integral_norm_sq_laplaceBoundary hi hm]
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with y hy
    rw [laplaceBoundary_sub (hint ω hω) integrable_causalPoleVector,
      htrans ω hω y hy, laplaceBoundary_causalPoleVector]
  have hM := tendsto_boundary_multiplier_energy
  have hscaled : Tendsto (fun ω : ℝ => (2 * Real.pi)⁻¹ *
      ∫ τ : ℝ, ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hM.const_mul ((2 * Real.pi)⁻¹)
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  rw [hkey ω hω]
  field_simp

end RHTower
