import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellSplitGaussianMixture
import GaloisForLFunctions.HTGeometry.GaussianRealMoments

/-!
# Fourth-moment cost of a fitted Gaussian cell mixture

A Gaussian replacing a uniform interval preserves integration through
degree three. For a translated fourth power it adds width⁴/120. Splitting
the interval therefore preserves the first three moments and strictly
reduces this fourth-moment defect. At fixed total width the unique best
split is the midpoint and gives a factor of sixteen.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

private def meanPower (k : ℕ) (t a z : ℝ) :=
  ((t+a-z)^(k+1)-(t-z)^(k+1))/(((k:ℝ)+1)*a)

/-- All translated moments of physical position on one interval. -/
theorem position_moment (k : ℕ) (t w z : ℝ) :
    (∫ x, (x-z)^k ∂positionLaw t w) = meanPower k t (Real.exp w) z := by
  rw [positionLaw,ProbabilityTheory.cond,integral_smul_measure,Real.volume_Ioc,add_sub_cancel_left,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (Real.exp_pos w).le,smul_eq_mul,
    ← intervalIntegral.integral_of_le (le_add_of_nonneg_right (Real.exp_pos w).le),
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^k) z,integral_pow]
  unfold meanPower
  push_cast
  field_simp [Real.exp_ne_zero w,show (k:ℝ)+1≠0 by positivity]

private theorem gauss_power_integrable (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (gaussianReal m v) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
  simp [integrableExpSet_fun_id_gaussianReal]

theorem gauss_offset_integrable (m z : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (x-z)^k) (gaussianReal m v) := by
  have h := gauss_power_integrable (m-z) v k
  rw [sub_eq_add_neg,← gaussianReal_map_add_const] at h
  simpa only [Function.comp_def,sub_eq_add_neg] using
    (integrable_map_measure (by fun_prop) (by fun_prop)).mp h

/-- Binomial translation of Gaussian moments around an arbitrary center. -/
theorem gauss_shifted_moment (m z : ℝ) (v : ℝ≥0) (k : ℕ) :
    (∫ x, (x-z)^k ∂gaussianReal m v) =
      ∑ i ∈ range (k+1), (∫ x : ℝ, x^i ∂gaussianReal 0 v)*(m-z)^(k-i)*(k.choose i : ℝ) := by
  have hmap := gaussianReal_map_add_const (μ := 0) (v := v) m
  rw [zero_add] at hmap
  rw [← hmap,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [show ∀ x : ℝ, x+m-z = x+(m-z) by intro x; ring,add_pow]
  rw [integral_finsetSum]
  · exact sum_congr rfl fun i _ => by rw [integral_mul_const,integral_mul_const]
  · exact fun i _ => ((gauss_power_integrable 0 v i).mul_const _).mul_const _

/-- The KL-optimal component for one interval, parametrized by its log width. -/
def fittedPosition (t w : ℝ) := positionGaussian (t+Real.exp w/2) (Real.log ((Real.exp w)^2/12))

/-- Through degree four the only moment error of one projection is the
positive central fourth-moment surplus, independent of the center of the test. -/
theorem fitted_position_moments (t w z : ℝ) (k : ℕ) : k ≤ 4 →
    (∫ x, (x-z)^k ∂fittedPosition t w) =
      meanPower k t (Real.exp w) z + if k = 4 then (Real.exp w)^4/120 else 0 := by
  intro hk
  let a := Real.exp w
  let v := Real.toNNReal (a^2/12)
  have ha : 0 < a := Real.exp_pos w
  have hv : (v:ℝ) = a^2/12 := Real.coe_toNNReal _ (by positivity)
  change (∫ x, (x-z)^k ∂gaussianReal (t+a/2) (Real.toNNReal (Real.exp (Real.log (a^2/12))))) = _
  rw [Real.exp_log (by positivity : 0 < a^2/12)]
  change (∫ x, (x-z)^k ∂gaussianReal (t+a/2) v) = meanPower k t a z+_
  rw [gauss_shifted_moment]
  have h0 := HTGeometry.integral_pow_zero_gaussianReal v
  have h1 := HTGeometry.integral_pow_one_gaussianReal v
  have h2 : (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v:ℝ) := by
    simpa only [Nat.cast_zero,zero_add,one_mul,h0,mul_one] using HTGeometry.integral_pow_gaussianReal_succ_succ v 0
  have h3 : (∫ x : ℝ, x^3 ∂gaussianReal 0 v) = 0 := by
    simpa only [h1,mul_zero] using HTGeometry.integral_pow_gaussianReal_succ_succ v 1
  have h4 : (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3*(v:ℝ)^2 := by
    rw [HTGeometry.integral_pow_gaussianReal_succ_succ v 2,h2]
    push_cast
    ring
  interval_cases k <;>
    norm_num [Finset.sum_range_succ,Nat.choose,h0,h1,h2,h3,h4,hv,meanPower,← show a = Real.exp w from rfl] <;>
    field_simp [ha.ne'] <;> ring

private theorem meanPower_split (k : ℕ) (t z u v : ℝ) :
    lengthRatio u v*meanPower k t (Real.exp u) z +
      lengthRatio v u*meanPower k (t+Real.exp u) (Real.exp v) z =
        meanPower k t (Real.exp u+Real.exp v) z := by
  unfold lengthRatio meanPower
  rw [add_comm (Real.exp v) (Real.exp u),add_assoc t (Real.exp u) (Real.exp v)]
  field_simp [Real.exp_ne_zero _,(add_pos (Real.exp_pos u) (Real.exp_pos v)).ne',
    (by positivity : (k:ℝ)+1 ≠ 0)]
  ring

/-- Mixture of the two moment-matched components on adjacent intervals. -/
def fittedSplit (t u v : ℝ) := splitGaussian u v
  (t+Real.exp u/2,Real.log ((Real.exp u)^2/12))
  (t+Real.exp u+Real.exp v/2,Real.log ((Real.exp v)^2/12))

/-- The length-weighted fourth defect. Setting either log width to zero
gives physical length one. -/
def splitDefect (u v : ℝ) :=
  ((Real.exp u)^5+(Real.exp v)^5)/(120*(Real.exp u+Real.exp v))

private theorem fittedSplit_integral (t u v z : ℝ) (k : ℕ) :
    (∫ x, (x-z)^k ∂fittedSplit t u v) =
      lengthRatio u v*(∫ x, (x-z)^k ∂fittedPosition t u) +
      lengthRatio v u*(∫ x, (x-z)^k ∂fittedPosition (t+Real.exp u) v) := by
  have hi (s w : ℝ) : Integrable (fun x : ℝ => (x-z)^k) (fittedPosition s w) :=
    gauss_offset_integrable _ z _ k
  rw [fittedSplit,splitGaussian_components]
  change (∫ x, (x-z)^k ∂(ENNReal.ofReal (lengthRatio u v) • fittedPosition t u +
    ENNReal.ofReal (lengthRatio v u) • fittedPosition (t+Real.exp u) v))=_
  rw [integral_add_measure ((hi t u).smul_measure ENNReal.ofReal_ne_top)
    ((hi (t+Real.exp u) v).smul_measure ENNReal.ofReal_ne_top),integral_smul_measure,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (lengthRatio_pos _ _).le,smul_eq_mul]

/-- The first three moments of the genuine split and uniform measures agree
at every center. Their fourth moments differ by exactly the weighted defect. -/
theorem split_moment_error (t u v z : ℝ) (k : ℕ) : k ≤ 4 →
    let P := positionLaw t (Real.log (Real.exp u+Real.exp v))
    (∫ x, (x-z)^k ∂fittedSplit t u v) - (∫ x, (x-z)^k ∂P) = if k = 4 then splitDefect u v else 0 := by
  intro hk P
  have hab := add_pos (Real.exp_pos u) (Real.exp_pos v)
  dsimp only [P]
  rw [fittedSplit_integral,position_moment,Real.exp_log hab,fitted_position_moments _ _ _ _ hk,
    fitted_position_moments _ _ _ _ hk,← meanPower_split]
  by_cases he : k = 4
  · simp only [he,if_true]
    unfold splitDefect lengthRatio
    rw [add_comm (Real.exp v) (Real.exp u)]
    field_simp [hab.ne']
    ring
  · simp [he]

/-- Equal splitting uniquely minimizes the fourth defect at fixed total
width; the exact excess is a strictly positive factor times (a−b)². -/
theorem split_defect_midpoint (u v : ℝ) :
    let a := Real.exp u
    let b := Real.exp v
    1920*splitDefect u v-(a+b)^4 = 5*(a-b)^2*(3*a^2+2*a*b+3*b^2) ∧
    ((a+b)^4/1920 ≤ splitDefect u v) ∧ ((a+b)^4/1920 = splitDefect u v ↔ u = v) := by
  intro a b
  have ha : 0 < a := Real.exp_pos u
  have hb : 0 < b := Real.exp_pos v
  have hs := add_pos ha hb
  have h : 1920*splitDefect u v-(a+b)^4 = 5*(a-b)^2*(3*a^2+2*a*b+3*b^2) := by
    change 1920*((a^5+b^5)/(120*(a+b)))-_ = _
    field_simp [hs.ne']
    ring
  have hp : 0 < 3*a^2+2*a*b+3*b^2 := by positivity
  refine ⟨h,by linarith only [h,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) (sq_nonneg (a-b))) hp.le],?_⟩
  constructor
  · intro he
    have h0 : 5*(a-b)^2*(3*a^2+2*a*b+3*b^2) = 0 := by linarith only [h,he]
    have eq := (mul_eq_zero.mp h0).resolve_right hp.ne'
    exact Real.exp_injective (sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp eq).resolve_left (by norm_num))))
  · rintro rfl
    change (Real.exp u+Real.exp u)^4/1920 = splitDefect u u
    unfold splitDefect
    field_simp [(add_pos ha ha).ne']
    ring

#print axioms position_moment
#print axioms fitted_position_moments
#print axioms split_moment_error
#print axioms split_defect_midpoint
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
