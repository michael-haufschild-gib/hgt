import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailIsolation
import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesSampleEveryTopLayer
import GaloisForLFunctions.SquareRootThreshold.FiniteLagWindowRecordPotentialLaw
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# Positive deletion of the actual zeta spline tail

The reciprocal-square law for zeta ordinates supplies positive deletion
filters with arbitrarily small square cost. They preserve any specified
exponent and annihilate all but finitely many modes of the cubic-spline
trace, including after any real shift of the exponents.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23
open _root_.RHTower
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Zeta admits arbitrarily cheap positive deletion of a cofinite spectral tail. -/
theorem exists_zeta_tail_deletion (α : ℝ) (w₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a h : ℕ → ℝ) (S : Finset ℂ),
      Summable (fun n => h n ^ 2) ∧ (∑' n, h n ^ 2) < ε ∧
      (∏' n, quartetFactor (a n) (h n) w₀) ≠ 0 ∧
      ∀ z ∉ S, evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0 →
        ∃ n, (z - (α : ℂ)).re = a n ∧ h n * (z - (α : ℂ)).im = Real.pi := by
  classical
  let e := xiZeroCopyThermalEquiv
  let a : ℕ → ℝ := fun n => ((e n).1 : ℂ).re - 1 / 2 - α
  let h : ℕ → ℝ := fun n => Real.pi / xiCopyOrdinate (e n)
  have hsq : Summable fun n => h n ^ 2 := by
    have hs := (summable_inv_sq_xiCopyOrdinate.mul_left (Real.pi ^ 2)).comp_injective e.injective
    apply hs.congr
    intro n
    dsimp only [h, Function.comp_def]
    ring
  obtain ⟨N, hcost, hkeep⟩ := exists_small_nonzero_tail_multiplier a h hsq w₀ hε
  let S : Finset ℂ := (Finset.range N).image fun n => ((e n).1 : ℂ) - 1 / 2
  refine ⟨(fun n => a (n + N)), (fun n => h (n + N)), S,
    (summable_nat_add_iff N).mpr hsq, hcost, hkeep, ?_⟩
  intro z hz hcz
  have hρ : (1 / 2 : ℂ) + z ∈ zetaZeroConfig.carrier := by
    rcases mem_of_evenCoeff_ne_zero hcz with hz | hz
    · exact hz
    · simpa using conj_mem_zetaZeroConfig hz
  have hne1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro he
    have hr := hρ.2.2
    rw [he, Complex.one_re] at hr
    exact (lt_irrefl _ hr).elim
  have hxi := (xi_eq_zero_iff hρ.2.1 hne1).mpr hρ.1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  let n : ℕ := e.symm q
  have hen : ((e n).1 : ℂ) = (1 / 2 : ℂ) + z := by
    dsimp only [n]
    rw [e.apply_symm_apply, hq]
  have hN : N ≤ n := by
    by_contra hn
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_range.mpr (lt_of_not_ge hn), ?_⟩
    rw [hen]
    ring
  refine ⟨n - N, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hN]
    dsimp only [a]
    rw [hen]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    norm_num <;> ring
  · rw [Nat.sub_add_cancel hN]
    have him : xiCopyOrdinate (e n) = z.im := by
      dsimp only [xiCopyOrdinate]
      rw [hen]
      simp
    have hγ : z.im ≠ 0 := by rw [← him]; exact xiCopyOrdinate_ne_zero _
    dsimp only [h]
    rw [him]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact div_mul_cancel₀ _ hγ

theorem zeta_shifted_exponent_bound (α : ℝ) {z : ℂ}
    (hz : evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0) :
    |(z - (α : ℂ)).re| ≤ 1 / 2 + |α| := by
  have htri : |z.re - α| ≤ |z.re| + |α| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le z.re α
  exact htri.trans (add_le_add_right (abs_re_le_of_evenCoeff_ne_zero hz) _)

/-- The shifted spline trace is an absolutely convergent real exponential series. -/
theorem zeta_shifted_trace_series (α t : ℝ) :
    Real.exp (-α * t) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) t).re) =
      ∑' z : ℂ, (evenCoeff zetaZeroConfig (boxSpline 1 3) z *
        Complex.exp ((z - (α : ℂ)) * t)).re := by
  have he := ofReal_normTrace (b := α) temperedConfig_zetaZeroConfig t
  have hs : Summable fun z : ℂ => evenCoeff zetaZeroConfig (boxSpline 1 3) z *
      Complex.exp ((z - (α : ℂ)) * t) := by
    apply Summable.of_norm_bounded
      ((summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig).mul_right
        (Real.exp ((1 / 2 + |α|) * |t|)))
    intro z
    by_cases hz : evenCoeff zetaZeroConfig (boxSpline 1 3) z = 0
    · simp [hz]
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, mul_zero]
    have hw : |z.re - α| ≤ 1 / 2 + |α| := zeta_shifted_exponent_bound α hz
    exact (le_abs_self ((z.re - α) * t)).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hw (abs_nonneg _))
  have hre := congrArg Complex.re he
  rw [show (∑' z : ℂ, evenCoeff zetaZeroConfig (boxSpline 1 3) z *
      Complex.exp ((z - (α : ℂ)) * t)).re =
      ∑' z : ℂ, (evenCoeff zetaZeroConfig (boxSpline 1 3) z *
        Complex.exp ((z - (α : ℂ)) * t)).re from Complex.reCLM.map_tsum hs] at hre
  simpa only [normTrace, Complex.ofReal_re, neg_mul, mul_comm] using hre

#print axioms exists_zeta_tail_deletion
#print axioms zeta_shifted_trace_series

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
