import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin
import GaloisForLFunctions.RHTower.Sieve.SquarefreeGlobalCount
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The finite part of the squarefree harmonic diagonal

Abel summation, used in the proof of El Kaouni’s Proposition F.2 (arXiv:2610.42022),
identifies the constant term of the critical Möbius diagonal with the
regular part of its Dirichlet series. The square-root counting error
gives a uniform numerical constant in the analytic remainder estimate.
-/

noncomputable section

open Complex MeasureTheory Filter Finset
open scoped Topology
open RHTower RHTower.Sieve RHTower.SquarefreeDiscrepancy
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- The critical-line diagonal mass through a real cutoff. -/
def harmonicMoebiusDiagonal (X : ℝ) :=
  ∑ n ∈ Icc 1 ⌊X⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 / (n : ℝ)

/-- Finite part of ζ(s)/ζ(2s) at one. -/
def squarefreeHarmonicConstant : ℝ :=
  ((Real.eulerMascheroniConstant : ℂ) / riemannZeta 2 -
    2 * deriv riemannZeta 2 / (riemannZeta 2)^2).re

private theorem finite_part_at_one :
    (squarefreeDensity : ℂ) + moment 1 =
      (Real.eulerMascheroniConstant : ℂ) / riemannZeta 2 -
      2 * deriv riemannZeta 2 / (riemannZeta 2)^2 := by
  let d : ℂ := squarefreeDensity
  have hz : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hconst : d * riemannZeta 2 = 1 := by
    have h := moment_identity (s := 1) (by norm_num)
    simp only [sub_self, zero_mul, mul_one, zetaResidueUnit_one] at h
    linear_combination h
  have hnear : (fun s : ℂ => (s-1)*s*moment s*riemannZeta (2*s)) =ᶠ[𝓝 (1:ℂ)]
      (fun s : ℂ => zetaResidueUnit s - d*s*riemannZeta (2*s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1:ℂ) ∈ {s : ℂ | 1/2 < s.re})] with s hs
    exact moment_identity hs
  have hZ : HasDerivAt (fun s : ℂ => riemannZeta (2*s)) (deriv riemannZeta 2*2) 1 := by
    have hd : HasDerivAt riemannZeta (deriv riemannZeta 2) (2*(1:ℂ)) := by
      simpa only [mul_one] using (differentiableAt_riemannZeta (by norm_num : (2:ℂ) ≠ 1)).hasDerivAt
    have hg : HasDerivAt (fun z : ℂ => 2*z) 2 (1:ℂ) := by
      simpa only [mul_one] using (hasDerivAt_id' (1:ℂ)).const_mul 2
    simpa only [Function.comp_apply] using! hd.comp (1:ℂ) hg
  have hleft := ((((hasDerivAt_id' (1:ℂ)).sub_const 1).mul (hasDerivAt_id' 1)).mul
    (differentiableAt_moment (s := 1) (by norm_num)).hasDerivAt).mul hZ
  have hright := zetaResidueUnit_analyticAt.differentiableAt.hasDerivAt.sub
    (((hasDerivAt_id' (1:ℂ)).const_mul d).mul hZ)
  have h := (hleft.congr_of_eventuallyEq hnear.symm).unique hright
  simp only [Pi.mul_apply, sub_self, mul_one, one_mul, zero_mul, add_zero,
    deriv_zetaResidueUnit_one] at h
  change d + moment 1 = _
  field_simp [hz]
  linear_combination riemannZeta 2*h - (2*deriv riemannZeta 2)*hconst

private def weightedError (x : ℝ) := error x / x^2

private theorem literal_moment : moment 1 = ((∫ x in Set.Ioi (1:ℝ), weightedError x : ℝ) : ℂ) := by
  rw [moment_eq_integral, ← integral_complex_ofReal (f := weightedError) (μ := volume.restrict (Set.Ioi 1))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only [weightedError]
  norm_num [Complex.cpow_neg, div_eq_mul_inv]

private theorem weighted_bound {x : ℝ} (hx : 1 ≤ x) :
    |weightedError x| ≤ 4*x^(-(3/2:ℝ)) := by
  have hp := zero_lt_one.trans_le hx
  rw [weightedError, abs_div, abs_of_pos (sq_pos_of_pos hp)]
  refine (div_le_div_of_nonneg_right (abs_error_le hx) (sq_nonneg x)).trans_eq ?_
  rw [Real.sqrt_eq_rpow, div_eq_inv_mul, ← Real.rpow_natCast x 2,
    ← Real.rpow_neg hp.le]
  change x^(-(2:ℝ))*(4*x^((1:ℝ)/2)) = _
  rw [show x^(-(2:ℝ))*(4*x^((1:ℝ)/2)) = 4*(x^(-(2:ℝ))*x^((1:ℝ)/2)) by ring,
    ← Real.rpow_add hp]
  norm_num

private theorem weighted_integrable {X : ℝ} (hX : 1 ≤ X) :
    IntegrableOn weightedError (Set.Ioi X) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1)
    (zero_lt_one.trans_le hX)).const_mul 4
  apply hi.mono' (measurable_error.div (measurable_id.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (Real.norm_eq_abs _).le.trans (weighted_bound (hX.trans hx.le))

private theorem split_triangle {X : ℝ} (hX : 1 ≤ X) :
    |∫ x in Set.Ioi X, weightedError x| ≤ 8*X^(-(1/2:ℝ)) := by
  have hp := zero_lt_one.trans_le hX
  have hz := integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1) hp
  have hi := integral_mono_ae (weighted_integrable hX).norm (hz.const_mul 4) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (Real.norm_eq_abs _).le.trans (weighted_bound (hX.trans hx.le)))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hp] at hi
  rw [← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans (hi.trans_eq (by norm_num; ring))

private theorem sum_zero_start (n : ℕ) :
    (∑ k ∈ Icc 0 n, ((ArithmeticFunction.moebius k : ℤ) : ℝ)^2) = RHTower.SquarefreeDiscrepancy.count n := by
  change _ = ∑ k ∈ Icc 1 ⌊(n:ℝ)⌋₊, _
  rw [Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero, sum_range_succ',
    RHTower.sum_Icc_eq_sum_range_shift]
  simp

private theorem diagonal_abel {X : ℝ} (hX : 1 ≤ X) :
    harmonicMoebiusDiagonal X - squarefreeDensity*Real.log X =
      squarefreeDensity + error X/X + ∫ x in Set.Ioc 1 X, weightedError x := by
  let c := fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2
  let d := squarefreeDensity
  have hp := zero_lt_one.trans_le hX
  have hDer (x : ℝ) (hx : x ∈ Set.Icc 1 X) : HasDerivAt (fun t : ℝ => t⁻¹) (-(x^2)⁻¹) x :=
    hasDerivAt_inv (zero_lt_one.trans_le hx.1).ne'
  have hind : IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc 1 X) := by
    have hcont : ContinuousOn (fun t : ℝ => -(t^2)⁻¹) (Set.Icc 1 X) :=
      ((continuous_id.pow 2).continuousOn.inv₀ (fun t ht => pow_ne_zero _ (zero_lt_one.trans_le ht.1).ne')).neg
    exact (hcont.integrableOn_compact isCompact_Icc).congr_fun (fun t ht => (hDer _ ht).deriv.symm) measurableSet_Icc
  have hs := sum_mul_eq_sub_sub_integral_mul c (a := 1) zero_le_one hX (fun t ht => (hDer t ht).differentiableAt) hind
  have hc (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, c k) = RHTower.SquarefreeDiscrepancy.count t := by
    simpa only [RHTower.SquarefreeDiscrepancy.count,Nat.floor_natCast,c] using sum_zero_start ⌊t⌋₊
  simp only [hc,Nat.floor_one, inv_one, one_mul] at hs
  have hsum : harmonicMoebiusDiagonal X = 1 + ∑ k ∈ Ioc 1 ⌊X⌋₊, (k:ℝ)⁻¹*c k := by
    unfold harmonicMoebiusDiagonal
    rw [Finset.Icc_eq_cons_Ioc ((Nat.one_le_floor_iff X).mpr hX), Finset.sum_cons]
    simp only [Nat.cast_one,ArithmeticFunction.moebius_apply_one,Int.cast_one,one_pow,div_one]
    congr 1
    exact sum_congr rfl fun n _ => by simp only [c,div_eq_inv_mul]
  have hmod : (fun t : ℝ => deriv (fun x : ℝ => x⁻¹) t * RHTower.SquarefreeDiscrepancy.count t) =ᵐ[volume.restrict (Set.Ioc 1 X)]
      (fun t => -(weightedError t + d*t⁻¹)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(hDer t ⟨ht.1.le,ht.2⟩).deriv]
    dsimp only [weightedError,error,d]
    field_simp [(zero_lt_one.trans ht.1).ne']
    ring
  have hI : IntegrableOn weightedError (Set.Ioc 1 X) :=
    (weighted_integrable (X := 1) le_rfl).mono_set Set.Ioc_subset_Ioi_self
  have hJ : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 X) := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 X) :=
      continuousOn_id.inv₀ fun x hx => (zero_lt_one.trans_le hx.1).ne'
    exact (hcont.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hlog : (∫ t in Set.Ioc 1 X, t⁻¹) = Real.log X := by
    rw [← intervalIntegral.integral_of_le hX, integral_inv_of_pos zero_lt_one hp, div_one]
  rw [integral_congr_ae hmod,integral_neg,integral_add hI (hJ.const_mul d),
    integral_const_mul,hlog] at hs
  have h1 : RHTower.SquarefreeDiscrepancy.count 1 = 1 := by norm_num [RHTower.SquarefreeDiscrepancy.count]
  have hs1 := hc (1:ℝ)
  rw [Nat.floor_one,h1] at hs1
  rw [hs1] at hs
  rw [hsum,hs]
  dsimp only [error,d]
  field_simp [hp.ne']
  ring

/-- At every real cutoff X ≥ 1 the deviation from the logarithm and the
explicit zeta-derivative constant is at most 12/√X. -/
theorem squarefree_harmonic_finite_part {X : ℝ} (hX : 1 ≤ X) :
    |harmonicMoebiusDiagonal X - squarefreeDensity*Real.log X - squarefreeHarmonicConstant| ≤
      12*X^(-(1/2:ℝ)) := by
  have hp := zero_lt_one.trans_le hX
  have hconst := congrArg Complex.re finite_part_at_one
  rw [literal_moment,Complex.add_re,Complex.ofReal_re,Complex.ofReal_re] at hconst
  change squarefreeDensity + (∫ x in Set.Ioi 1, weightedError x) = squarefreeHarmonicConstant at hconst
  have he := setIntegral_union (μ := volume) (s := Set.Ioc 1 X) (t := Set.Ioi X)
    (Set.disjoint_left.mpr (fun _ h h' => h'.not_ge h.2)) measurableSet_Ioi
    ((weighted_integrable (X := 1) le_rfl).mono_set fun _ h => h.1) (weighted_integrable hX)
  rw [Set.Ioc_union_Ioi_eq_Ioi hX] at he
  have hb : |error X / X| ≤ 4*X^(-(1/2:ℝ)) := by
    rw [abs_div,abs_of_pos hp]
    refine (div_le_div_of_nonneg_right (abs_error_le hX) hp.le).trans_eq ?_
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ←Real.rpow_neg_one, mul_assoc, ←Real.rpow_add hp]
    norm_num
  rw [diagonal_abel hX,←hconst,he,show ∀ a b c d : ℝ, a+b+c-(a+(c+d))=b-d by intros; ring]
  exact (abs_sub _ _).trans (by linarith only [hb,split_triangle hX])

#print axioms squarefree_harmonic_finite_part

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
