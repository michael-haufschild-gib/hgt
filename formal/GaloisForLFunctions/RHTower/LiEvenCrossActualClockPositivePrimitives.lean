import GaloisForLFunctions.RHTower.LiEvenCrossActualClockScoreCorrelation
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Repeated Borel primitives and the positive primitive-transfer boundary

`M_0 = B` is the actual normalized theta Borel kernel and `M_{m+1}(t) = ∫₀ᵗ M_m`.  Every
primitive has the complete series `M_m(t) = ∑ ν_j t^{2j+m}/((2j)!(2j+m)!)`.

* The factor-one source law `P + P⋆K = tK` integrates to
  `P⋆M_m = tM_m - (m+1)M_{m+1}` for every `m` and `t ≥ 0`; the `j = 0` row cancels and the
  remaining rows are nonnegative, so `P⋆M_m ≥ ν₁ t^{m+3}/(m+3)! > 0` although `P` is signed.
* Integration by parts against the log history `D` (with `P = sD'`) gives the same-history
  balance `∫₀ᵗ D(s)(sM_m'(t-s) - M_m(t-s)) ds = tM_m - (m+1)M_{m+1} - tD(t)M_m(0)`.
* The gap `G(r) = M_1(r)/2 - rT(r) = ∑ b_j j r^{2j+1}/((2j+1)(2j+2))` is strictly positive, so
  `rT(r)` is not a nonnegative constant (finite or countable) mixture of the primitives on any
  interval `(0, R]`.
* The signed correction `P⋆(rT) = (tM_1 - 2M_2)/2 - P⋆G` and the outer score-history
  decomposition retain every signed term.
-/

open MeasureTheory Set Filter Topology
open scoped Interval ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "P" => liEvenCrossActualClockPrimitive
local notation "nu" => thetaCuspNormalizedEvenMoment

/-- The repeated Borel primitives: `M_0 = B`, `M_{m+1}(t) = ∫₀ᵗ M_m`. -/
def liEvenCrossActualClockBorelPrimitive : ℕ → ℝ → ℝ
  | 0,t => liEvenCrossActualClockBorelKernel t
  | m+1,t => ∫ s in (0:ℝ)..t, liEvenCrossActualClockBorelPrimitive m s
local notation "M" => liEvenCrossActualClockBorelPrimitive

/-- Every repeated primitive is smooth. -/
theorem contDiff_liEvenCrossActualClockBorelPrimitive (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (M m) := by
  induction m with
  | zero => exact contDiff_liEvenCrossActualClockBorelKernel
  | succ m ih =>
    change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ∫ s in (0:ℝ)..t, M m s)
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (ih.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt, ?_⟩
    have hd : deriv (fun t : ℝ => ∫ s in (0:ℝ)..t, M m s) = M m :=
      funext fun t => (ih.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt.deriv
    rw [hd]
    exact ih

/-- `M_{m+1}' = M_m` at every real clock. -/
theorem hasDerivAt_liEvenCrossActualClockBorelPrimitive (m : ℕ) (t : ℝ) :
    HasDerivAt (M (m+1)) (M m t) t := by
  exact ((contDiff_liEvenCrossActualClockBorelPrimitive m).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- `M_0(0) = 1` and `M_m(0) = 0` for `m ≥ 1`. -/
theorem liEvenCrossActualClockBorelPrimitive_origin (m : ℕ) :
    M m 0 = if m=0 then 1 else 0 := by
  cases m <;> simp [liEvenCrossActualClockBorelPrimitive]

private def ppTerm (m : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  nu j * t^(2*j+m) / (((2*j).factorial:ℝ)*((2*j+m).factorial:ℝ))

private theorem ppTerm_continuous (m j : ℕ) : Continuous (fun t : ℝ => ppTerm m t j) := by
  unfold ppTerm
  fun_prop

private theorem ppFactorial_le (m j : ℕ) :
    ((2*j).factorial:ℝ)*(m.factorial:ℝ) ≤ ((2*j+m).factorial:ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (2*j+m))
    (Nat.factorial_mul_factorial_dvd_factorial_add (2*j) m)

private theorem ppTerm_norm (m j : ℕ) (t : ℝ) :
    ‖ppTerm m t j‖ = ‖liEvenCrossActualClockBorelTerm t j‖ * |t|^m *
      ((2*j).factorial:ℝ) / ((2*j+m).factorial:ℝ) := by
  have hf : ((2*j).factorial:ℝ) ≠ 0 := by positivity
  have hfm : ((2*j+m).factorial:ℝ) ≠ 0 := by positivity
  simp only [ppTerm, liEvenCrossActualClockBorelTerm, norm_div, norm_mul, norm_pow,
    Real.norm_eq_abs, abs_of_pos (thetaCuspNormalizedEvenMoment_pos j),
    abs_of_pos (by positivity : (0:ℝ)<((2*j).factorial:ℝ)),
    abs_of_pos (by positivity : (0:ℝ)<((2*j+m).factorial:ℝ)), pow_add]
  field_simp

private theorem ppTerm_norm_le {R t : ℝ} (hR : 0≤R) (ht : |t|≤R) (m j : ℕ) :
    ‖ppTerm m t j‖ ≤ (R^m/(m.factorial:ℝ))*
      (((32/303:ℝ)*R^2)^j/(j.factorial:ℝ)) := by
  have hf : (0:ℝ)<((2*j).factorial:ℝ) := by positivity
  have hfm : (0:ℝ)<(m.factorial:ℝ) := by positivity
  have hsum : (0:ℝ)<((2*j+m).factorial:ℝ) := by positivity
  have hp : |t|^m≤R^m := pow_le_pow_left₀ (abs_nonneg t) ht m
  have hc := ppFactorial_le m j
  rw [ppTerm_norm]
  calc
    _ ≤ ‖liEvenCrossActualClockBorelTerm t j‖*R^m/(m.factorial:ℝ) := by
      apply (div_le_div_iff₀ hsum hfm).mpr
      calc
        _ = (‖liEvenCrossActualClockBorelTerm t j‖*|t|^m)*
              (((2*j).factorial:ℝ)*(m.factorial:ℝ)) := by ring
        _ ≤ (‖liEvenCrossActualClockBorelTerm t j‖*|t|^m)*((2*j+m).factorial:ℝ) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        _ ≤ (‖liEvenCrossActualClockBorelTerm t j‖*R^m)*((2*j+m).factorial:ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hsum.le
    _ ≤ (((32/303:ℝ)*R^2)^j/(j.factorial:ℝ))*R^m/(m.factorial:ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_liEvenCrossActualClockBorelTerm_le ht j)
          (pow_nonneg hR m)) hfm.le
    _ = _ := by ring

private theorem ppMajorant_summable (m : ℕ) (R : ℝ) :
    Summable (fun j : ℕ => (R^m/(m.factorial:ℝ))*
      (((32/303:ℝ)*R^2)^j/(j.factorial:ℝ))) :=
  (Real.summable_pow_div_factorial ((32/303:ℝ)*R^2)).mul_left _

private theorem ppTerm_summable (m : ℕ) (t : ℝ) : Summable (ppTerm m t) :=
  (ppMajorant_summable m |t|).of_norm_bounded
    (fun j => ppTerm_norm_le (abs_nonneg t) le_rfl m j)

private theorem ppInterval_abs {t s : ℝ} (hs : s ∈ uIcc (0:ℝ) t) : |s|≤|t| := by
  rw [mem_uIcc] at hs
  rcases hs with hs | hs
  · rw [abs_of_nonneg hs.1, abs_of_nonneg (le_trans hs.1 hs.2)]
    exact hs.2
  · rw [abs_of_nonpos hs.2, abs_of_nonpos (le_trans hs.1 hs.2)]
    exact neg_le_neg hs.1

private theorem ppTerm_integral (m j : ℕ) (t : ℝ) :
    (∫ s in (0:ℝ)..t, ppTerm m s j) = ppTerm (m+1) t j := by
  have hf : ((2*j).factorial:ℝ) ≠ 0 := by positivity
  have hg : ((2*j+m).factorial:ℝ) ≠ 0 := by positivity
  have hn : (2*j+m+1:ℝ) ≠ 0 := by positivity
  unfold ppTerm
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 2*j+m+1≠0), sub_zero]
  rw [show 2*j+(m+1)=2*j+m+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp

/-- Compact row majorant: for `|t| ≤ R`, the `j`th primitive row is at most
`(R^m/m!)·((32/303)R²)^j/j!`, a summable majorant independent of `t`. -/
theorem norm_liEvenCrossActualClockBorelPrimitiveRow_le {R t : ℝ} (hR : 0 ≤ R) (ht : |t| ≤ R)
    (m j : ℕ) :
    ‖nu j*t^(2*j+m)/(((2*j).factorial:ℝ)*((2*j+m).factorial:ℝ))‖ ≤
      (R^m/(m.factorial:ℝ))*(((32/303:ℝ)*R^2)^j/(j.factorial:ℝ)) :=
  ppTerm_norm_le hR ht m j

/-- Complete series of every primitive at every real clock. -/
theorem hasSum_liEvenCrossActualClockBorelPrimitive (m : ℕ) (t : ℝ) :
    HasSum (fun j : ℕ => nu j*t^(2*j+m)/
      (((2*j).factorial:ℝ)*((2*j+m).factorial:ℝ))) (M m t) := by
  change HasSum (ppTerm m t) (M m t)
  induction m generalizing t with
  | zero =>
    change HasSum (ppTerm 0 t) (B t)
    exact (summable_liEvenCrossActualClockBorelTerm t).hasSum.congr_fun
      (fun j => by simp [ppTerm, liEvenCrossActualClockBorelTerm, pow_two])
  | succ m ih =>
    have hall (s : ℝ) : HasSum (ppTerm m s) (M m s) := by
      exact ih s
    have hh := intervalIntegral.hasSum_integral_of_dominated_convergence
      (a:=0) (b:=t) (μ:=volume) (F:=fun j s=>ppTerm m s j) (f:=M m)
      (fun j _ => (|t|^m/(m.factorial:ℝ))*
        (((32/303:ℝ)*|t|^2)^j/(j.factorial:ℝ)))
      (fun j => (ppTerm_continuous m j).aestronglyMeasurable)
      (fun j => Eventually.of_forall fun s hs =>
        ppTerm_norm_le (abs_nonneg t) (ppInterval_abs (uIoc_subset_uIcc hs)) m j)
      (Eventually.of_forall fun _ _ => ppMajorant_summable m |t|)
      intervalIntegrable_const
      (Eventually.of_forall fun s _ => hall s)
    simpa only [ppTerm_integral, liEvenCrossActualClockBorelPrimitive] using hh


private theorem ppBorel_hasDerivAt (t : ℝ) : HasDerivAt B (deriv B t) t :=
  (hasDerivAt_liEvenCrossActualClockBorelKernel t).differentiableAt.hasDerivAt

private theorem ppKernel_continuous : Continuous (deriv B) :=
  contDiff_liEvenCrossActualClockBorelKernel.continuous_deriv (by simp)

private theorem ppPrimitive_continuous : Continuous P :=
  contDiff_liEvenCrossActualClockPrimitive.continuous

private theorem ppWeightedBorel_integral (t : ℝ) :
    (∫ s in (0:ℝ)..t, s*deriv B s) = t*B t-M 1 t := by
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    continuous_id.continuousOn contDiff_liEvenCrossActualClockBorelKernel.continuous.continuousOn
    (fun s _ => hasDerivAt_id s) (fun s _ => ppBorel_hasDerivAt s)
    (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 t from intervalIntegrable_const)
    (ppKernel_continuous.intervalIntegrable 0 t)
  simpa only [id_eq, zero_mul, sub_zero, one_mul, liEvenCrossActualClockBorelPrimitive] using hh

private theorem ppWeightedPrimitive_integral (m : ℕ) (t : ℝ) :
    (∫ s in (0:ℝ)..t, s*M m s) = t*M (m+1) t-M (m+2) t := by
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    continuous_id.continuousOn
    (contDiff_liEvenCrossActualClockBorelPrimitive (m+1)).continuous.continuousOn
    (fun s _ => hasDerivAt_id s) (fun s _ => hasDerivAt_liEvenCrossActualClockBorelPrimitive m s)
    (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 t from intervalIntegrable_const)
    ((contDiff_liEvenCrossActualClockBorelPrimitive m).continuous.intervalIntegrable 0 t)
  simpa only [id_eq, zero_mul, sub_zero, one_mul,
    show m+2=(m+1)+1 by omega, liEvenCrossActualClockBorelPrimitive] using hh

private theorem ppConvolution_zero {t : ℝ} (ht : 0≤t) :
    volterraConv (M 0) P t = t*M 0 t-M 1 t := by
  have hFTC := volterraConv_eq_integral_of_hasDerivAt
    ppBorel_hasDerivAt ppKernel_continuous ppPrimitive_continuous t
  simp only [liEvenCrossActualClockBorelKernel_zero, one_mul] at hFTC
  have hconv (u : ℝ) : volterraConv (deriv B) P u =
      ∫ s in (0:ℝ)..u, P s*deriv B (u-s) := by
    unfold volterraConv
    apply intervalIntegral.integral_congr
    intro s _
    ring
  calc
    _ = (∫ s in (0:ℝ)..t, P s)+∫ s in (0:ℝ)..t, volterraConv (deriv B) P s := hFTC
    _ = ∫ s in (0:ℝ)..t, P s+volterraConv (deriv B) P s :=
      (intervalIntegral.integral_add (ppPrimitive_continuous.intervalIntegrable 0 t)
        ((continuous_volterraConv ppKernel_continuous ppPrimitive_continuous).intervalIntegrable 0 t)).symm
    _ = ∫ s in (0:ℝ)..t, s*deriv B s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      change P s+volterraConv (deriv B) P s=s*deriv B s
      rw [hconv]
      exact liEvenCrossActualClockPrimitive_volterra hs.1
    _ = _ := ppWeightedBorel_integral t

private theorem ppConvolution_identity (m : ℕ) {t : ℝ} (ht : 0≤t) :
    volterraConv (M m) P t = t*M m t-(m+1:ℝ)*M (m+1) t := by
  induction m generalizing t with
  | zero => simpa using ppConvolution_zero ht
  | succ m ih =>
    have hM : M (m+1) = volterraConv (fun _ => (1:ℝ)) (M m) := by
      funext u
      rw [volterraConv_one_left]
      rfl
    have hI : (∫ s in (0:ℝ)..t, M (m+1) s) = M (m+2) t := rfl
    calc
      _ = volterraConv (volterraConv (fun _ => (1:ℝ)) (M m)) P t := by rw [hM]
      _ = volterraConv (fun _ => (1:ℝ)) (volterraConv (M m) P) t :=
        volterraConv_assoc continuous_const
          (contDiff_liEvenCrossActualClockBorelPrimitive m).continuous ppPrimitive_continuous t
      _ = ∫ s in (0:ℝ)..t, volterraConv (M m) P s := volterraConv_one_left _ t
      _ = ∫ s in (0:ℝ)..t, s*M m s-(m+1:ℝ)*M (m+1) s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact ih hs.1
      _ = t*M (m+1) t-M (m+2) t-(m+1:ℝ)*M (m+2) t := by
        have hi1 : IntervalIntegrable (fun s : ℝ => s*M m s) volume 0 t :=
          (continuous_id.mul (contDiff_liEvenCrossActualClockBorelPrimitive m).continuous).intervalIntegrable 0 t
        have hi2 : IntervalIntegrable (fun s : ℝ => (m+1:ℝ)*M (m+1) s) volume 0 t :=
          ((contDiff_liEvenCrossActualClockBorelPrimitive (m+1)).continuous.const_mul _).intervalIntegrable 0 t
        rw [intervalIntegral.integral_sub hi1 hi2,
          intervalIntegral.integral_const_mul, ppWeightedPrimitive_integral, hI]
      _ = _ := by push_cast; ring

/-- **Integrated source law.**  `∫₀ᵗ P(s)M_m(t-s) ds = tM_m(t) - (m+1)M_{m+1}(t)` for
`t ≥ 0`. -/
theorem liEvenCrossActualClockPrimitive_convolution_primitive (m : ℕ)
    {t : ℝ} (ht : 0≤t) :
    (∫ s in (0:ℝ)..t, P s*M m (t-s)) = t*M m t-(m+1:ℝ)*M (m+1) t := by
  have hh := ppConvolution_identity m ht
  unfold volterraConv at hh
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro s _
  ring

private def ppSkewTerm (m : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  (2*j:ℝ)*nu j*t^(2*j+m+1)/
    (((2*j).factorial:ℝ)*((2*j+m+1).factorial:ℝ))

private theorem ppSkewTerm_eq (m j : ℕ) (t : ℝ) :
    ppSkewTerm m t j = t*ppTerm m t j-(m+1:ℝ)*ppTerm (m+1) t j := by
  have hf : ((2*j).factorial:ℝ) ≠ 0 := by positivity
  have hg : ((2*j+m).factorial:ℝ) ≠ 0 := by positivity
  have hn : (2*j+m+1:ℝ) ≠ 0 := by positivity
  unfold ppSkewTerm ppTerm
  rw [show 2*j+(m+1)=2*j+m+1 by omega, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

private theorem ppSkewTerm_nonneg (m j : ℕ) {t : ℝ} (ht : 0≤t) :
    0≤ppSkewTerm m t j := by
  unfold ppSkewTerm
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (thetaCuspNormalizedEvenMoment_pos j).le) (pow_nonneg ht _)) (by positivity)

private theorem ppSkew_hasSum (m : ℕ) {t : ℝ} (ht : 0≤t) :
    HasSum (ppSkewTerm m t) (∫ s in (0:ℝ)..t, P s*M m (t-s)) := by
  have h1 := (hasSum_liEvenCrossActualClockBorelPrimitive m t).mul_left t
  have h2 := (hasSum_liEvenCrossActualClockBorelPrimitive (m+1) t).mul_left (m+1:ℝ)
  rw [liEvenCrossActualClockPrimitive_convolution_primitive m ht]
  exact (h1.sub h2).congr_fun (fun j => ppSkewTerm_eq m j t)

/-- The convolution series: the `j = 0` row cancels and every remaining row is retained. -/
theorem hasSum_liEvenCrossActualClockPrimitive_convolution_primitive (m : ℕ)
    {t : ℝ} (ht : 0≤t) :
    HasSum (fun j : ℕ => (2*(j+1):ℝ)*nu (j+1)*t^(2*(j+1)+m+1)/
      (((2*(j+1)).factorial:ℝ)*((2*(j+1)+m+1).factorial:ℝ)))
      (∫ s in (0:ℝ)..t, P s*M m (t-s)) := by
  have hh := (hasSum_nat_add_iff' (f:=ppSkewTerm m t) 1).mpr (ppSkew_hasSum m ht)
  simpa [ppSkewTerm] using hh

/-- The first surviving row: `ν₁ t^{m+3}/(m+3)! ≤ P⋆M_m(t)` for `t ≥ 0`. -/
theorem liEvenCrossActualClockPrimitive_convolution_primitive_lower (m : ℕ)
    {t : ℝ} (ht : 0≤t) :
    nu 1*t^(m+3)/((m+3).factorial:ℝ) ≤ ∫ s in (0:ℝ)..t, P s*M m (t-s) := by
  have hh := ppSkew_hasSum m ht
  have hle := hh.summable.le_tsum 1 (fun j _ => ppSkewTerm_nonneg m j ht)
  rw [hh.tsum_eq] at hle
  have heq : ppSkewTerm m t 1 = nu 1*t^(m+3)/((m+3).factorial:ℝ) := by
    unfold ppSkewTerm
    rw [show 2*1+m+1=m+3 by omega]
    norm_num
    field_simp
  rw [heq] at hle
  exact hle

/-- `P⋆M_m(t) > 0` for every `m` and `t > 0`. -/
theorem liEvenCrossActualClockPrimitive_convolution_primitive_pos (m : ℕ)
    {t : ℝ} (ht : 0<t) :
    0<∫ s in (0:ℝ)..t, P s*M m (t-s) := by
  exact lt_of_lt_of_le (div_pos (mul_pos (thetaCuspNormalizedEvenMoment_pos 1)
    (pow_pos ht _)) (by positivity))
    (liEvenCrossActualClockPrimitive_convolution_primitive_lower m ht.le)

local notation "D" => liEvenCrossActualClockLogHistory
local notation "Dens" => liEvenCrossActualClockLogHistoryDensity
local notation "T" => liClockThetaSmoothedBorelProfile
local notation "ell" => liEvenCrossActualClockHistoryScale
local notation "IU" => liEvenCrossActualClockScoreCostIntegral

private theorem ppTerm_nonneg (m j : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ppTerm m t j := by
  unfold ppTerm
  exact div_nonneg (mul_nonneg (thetaCuspNormalizedEvenMoment_pos j).le (pow_nonneg ht _))
    (by positivity)

/-- Elementary primitive bounds on the positive axis: `r^m/m! ≤ M_m(r) ≤ B(r) r^m/m!`. -/
theorem liEvenCrossActualClockBorelPrimitive_bounds (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r^m/(m.factorial:ℝ) ≤ M m r ∧ M m r ≤ B r*r^m/(m.factorial:ℝ) := by
  have hs : HasSum (ppTerm m r) (M m r) := hasSum_liEvenCrossActualClockBorelPrimitive m r
  refine ⟨?_, ?_⟩
  · have hle := hs.summable.le_tsum 0 (fun j _ => ppTerm_nonneg m j hr)
    rw [hs.tsum_eq] at hle
    simpa [ppTerm] using hle
  · have hB := (summable_liEvenCrossActualClockBorelTerm r).hasSum.mul_left
      (r^m/(m.factorial:ℝ))
    have hterm : ∀ j, ppTerm m r j ≤ r^m/(m.factorial:ℝ)*liEvenCrossActualClockBorelTerm r j := by
      intro j
      have hf : (0:ℝ) < ((2*j).factorial:ℝ) := by positivity
      have hnum : 0 ≤ nu j*r^(2*j)*r^m :=
        mul_nonneg (mul_nonneg (thetaCuspNormalizedEvenMoment_pos j).le (pow_nonneg hr _))
          (pow_nonneg hr _)
      calc ppTerm m r j = nu j*r^(2*j)*r^m/(((2*j).factorial:ℝ)*((2*j+m).factorial:ℝ)) := by
            unfold ppTerm; ring
        _ ≤ nu j*r^(2*j)*r^m/(((2*j).factorial:ℝ)*(((2*j).factorial:ℝ)*(m.factorial:ℝ))) :=
            div_le_div_of_nonneg_left hnum (by positivity)
              (mul_le_mul_of_nonneg_left (ppFactorial_le m j) hf.le)
        _ = r^m/(m.factorial:ℝ)*liEvenCrossActualClockBorelTerm r j := by
            unfold liEvenCrossActualClockBorelTerm; field_simp
    calc M m r ≤ r^m/(m.factorial:ℝ)*B r := hasSum_le hterm hs hB
      _ = B r*r^m/(m.factorial:ℝ) := by ring

/-- Every primitive is strictly positive at positive clocks. -/
theorem liEvenCrossActualClockBorelPrimitive_pos (m : ℕ) {r : ℝ} (hr : 0 < r) : 0 < M m r :=
  lt_of_lt_of_le (by positivity) (liEvenCrossActualClockBorelPrimitive_bounds m hr.le).1

private def ppT (r : ℝ) : ℝ := (T (r:ℂ)).re

private theorem ppT_differentiable : Differentiable ℂ T := fun z =>
  (liClockThetaScoreProfiles_analyticAt z).2.2.1.differentiableAt

private theorem ppT_contDiff : ContDiff ℝ (⊤:ℕ∞) ppT :=
  ppT_differentiable.contDiff.real_of_complex

private theorem ppT_hasSum (r : ℝ) :
    HasSum (fun j : ℕ => nu j*r^(2*j)/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ))) (ppT r) := by
  have hc := (liClockThetaScoreProfiles_summable_norm (r:ℂ)).2.2.1.of_norm
  have he : (fun j : ℕ => (nu j:ℂ)*(r:ℂ)^(2*j)/(((2*j+2).factorial:ℂ)*((2*j).factorial:ℂ))) =
      (fun j : ℕ => ((nu j*r^(2*j)/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ)):ℝ):ℂ)) := by
    funext j; push_cast; ring
  rw [he] at hc
  have hr := Complex.summable_ofReal.mp hc
  convert hr.hasSum using 1
  unfold ppT liClockThetaSmoothedBorelProfile
  rw [he, ← Complex.ofReal_tsum, Complex.ofReal_re]

private theorem ppT_zero : ppT 0 = 1/2 := by
  rw [← (ppT_hasSum 0).tsum_eq, tsum_eq_single 0]
  · norm_num
  · intro j hj
    simp [hj]

/-- The real smoothed profile series `T(r) = ∑ ν_j r^{2j}/((2j+2)!(2j)!)`. -/
theorem hasSum_liClockThetaSmoothedBorelProfile_re (r : ℝ) :
    HasSum (fun j : ℕ => nu j*r^(2*j)/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ)))
      ((T (r:ℂ)).re) :=
  ppT_hasSum r

/-- `T(0) = 1/2`. -/
theorem liClockThetaSmoothedBorelProfile_re_zero : (T ((0:ℝ):ℂ)).re = 1/2 := ppT_zero

/-- The positive transfer gap `G(r) = M_1(r)/2 - r T(r)`. -/
def liEvenCrossActualClockPrimitiveScoreGap (r : ℝ) : ℝ :=
  M 1 r/2 - r*(T (r:ℂ)).re

local notation "G" => liEvenCrossActualClockPrimitiveScoreGap

/-- Complete gap series `G(r) = ∑ b_j j r^{2j+1}/((2j+1)(2j+2))`, `b_j = ν_j/((2j)!)²`; the
`j = 0` row vanishes and every other row is retained. -/
theorem hasSum_liEvenCrossActualClockPrimitiveScoreGap (r : ℝ) :
    HasSum (fun j : ℕ => liEvenCrossActualClockBorelCoefficient j*(j:ℝ)*r^(2*j+1)/
      ((2*(j:ℝ)+1)*(2*(j:ℝ)+2))) (G r) := by
  have h1 := (hasSum_liEvenCrossActualClockBorelPrimitive 1 r).div_const 2
  have h2 := (ppT_hasSum r).mul_left r
  refine (h1.sub h2).congr_fun fun j => ?_
  have e1 : (2*j+1).factorial = (2*j+1)*(2*j).factorial := Nat.factorial_succ _
  have e2 : (2*j+2).factorial = (2*j+2)*((2*j+1)*(2*j).factorial) := by
    rw [show 2*j+2 = (2*j+1)+1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  unfold liEvenCrossActualClockBorelCoefficient
  rw [e1, e2, pow_succ]
  push_cast
  field_simp
  ring

/-- The first positive gap row: `ν₁ r³/48 ≤ G(r)` for `r ≥ 0`. -/
theorem liEvenCrossActualClockPrimitiveScoreGap_lower {r : ℝ} (hr : 0 ≤ r) :
    nu 1*r^3/48 ≤ G r := by
  have hs := hasSum_liEvenCrossActualClockPrimitiveScoreGap r
  have hle := hs.summable.le_tsum 1 (fun j _ => div_nonneg (mul_nonneg (mul_nonneg
    (liEvenCrossActualClockBorelCoefficient_pos j).le (Nat.cast_nonneg j)) (pow_nonneg hr _))
    (by positivity))
  rw [hs.tsum_eq] at hle
  refine le_of_eq_of_le ?_ hle
  unfold liEvenCrossActualClockBorelCoefficient
  norm_num [Nat.factorial]
  ring

/-- The gap profile is strictly positive at every positive lag. -/
theorem liEvenCrossActualClockPrimitiveScoreGap_pos {r : ℝ} (hr : 0 < r) : 0 < G r :=
  lt_of_lt_of_le (by have := thetaCuspNormalizedEvenMoment_pos 1; positivity)
    (liEvenCrossActualClockPrimitiveScoreGap_lower hr.le)

/-- The gap vanishes at the origin. -/
theorem liEvenCrossActualClockPrimitiveScoreGap_zero : G 0 = 0 := by
  simp [liEvenCrossActualClockPrimitiveScoreGap, liEvenCrossActualClockBorelPrimitive_origin]

/-- The gap profile is smooth. -/
theorem contDiff_liEvenCrossActualClockPrimitiveScoreGap : ContDiff ℝ (⊤:ℕ∞) G :=
  ((contDiff_liEvenCrossActualClockBorelPrimitive 1).div_const 2).sub (contDiff_id.mul ppT_contDiff)

private theorem pp_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_liEvenCrossActualClockLogHistory s).continuousAt

private theorem pp_mul_density (s : ℝ) : s*Dens s = P s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [liEvenCrossActualClockPrimitive_origin_even.1]
  · rw [liEvenCrossActualClockLogHistoryDensity]; field_simp

private theorem pp_history_IBP {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ) :
    (∫ s in (0:ℝ)..t, D s*(s*deriv g (t-s)-g (t-s))) =
      (∫ s in (0:ℝ)..t, P s*g (t-s)) - t*D t*g 0 := by
  have hgd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg.differentiable one_ne_zero x).hasDerivAt
  have hg'c : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hc1 : Continuous (fun s => deriv g (t-s)) := hg'c.comp (continuous_const.sub continuous_id)
  have hc2 : Continuous (fun s => g (t-s)) := hg.continuous.comp (continuous_const.sub continuous_id)
  have hu : ∀ s, HasDerivAt (fun s => s*D s) (D s + P s) s := by
    intro s
    have h := (hasDerivAt_id s).mul (hasDerivAt_liEvenCrossActualClockLogHistory s)
    simp only [id, one_mul, pp_mul_density] at h
    exact h
  have hv : ∀ s, HasDerivAt (fun s => g (t-s)) (-deriv g (t-s)) s := by
    intro s
    exact (hgd (t-s)).comp_const_sub t s
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := t) (u := fun s => s*D s) (v := fun s => g (t-s))
    (u' := fun s => D s + P s) (v' := fun s => -deriv g (t-s))
    ((continuous_id.mul pp_D_cont).continuousOn) hc2.continuousOn
    (fun s _ => hu s) (fun s _ => hv s)
    ((pp_D_cont.add ppPrimitive_continuous).intervalIntegrable _ _)
    (hc1.neg.intervalIntegrable _ _)
  beta_reduce at hIBP
  have e1 : (∫ s in (0:ℝ)..t, D s*(s*deriv g (t-s)-g (t-s))) =
      (∫ s in (0:ℝ)..t, s*D s*deriv g (t-s)) - ∫ s in (0:ℝ)..t, D s*g (t-s) := by
    rw [← intervalIntegral.integral_sub
      (by exact ((continuous_id.mul pp_D_cont).mul hc1).intervalIntegrable _ _ :
        IntervalIntegrable (fun s => s*D s*deriv g (t-s)) volume 0 t)
      (by exact (pp_D_cont.mul hc2).intervalIntegrable _ _ :
        IntervalIntegrable (fun s => D s*g (t-s)) volume 0 t)]
    congr 1; funext s; ring
  have e2 : (∫ s in (0:ℝ)..t, s*D s*-deriv g (t-s)) = -∫ s in (0:ℝ)..t, s*D s*deriv g (t-s) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext s; ring
  have e3 : (∫ s in (0:ℝ)..t, (D s+P s)*g (t-s)) =
      (∫ s in (0:ℝ)..t, D s*g (t-s)) + ∫ s in (0:ℝ)..t, P s*g (t-s) := by
    rw [← intervalIntegral.integral_add
      (by exact (pp_D_cont.mul hc2).intervalIntegrable _ _ :
        IntervalIntegrable (fun s => D s*g (t-s)) volume 0 t)
      (by exact (ppPrimitive_continuous.mul hc2).intervalIntegrable _ _ :
        IntervalIntegrable (fun s => P s*g (t-s)) volume 0 t)]
    congr 1; funext s; ring
  rw [e2, e3] at hIBP
  simp only [sub_self, sub_zero, zero_mul] at hIBP
  rw [e1]
  linarith

/-- **Same-history balance (B5).**  For `t ≥ 0`,
`∫₀ᵗ D(s)(sM_m'(t-s) - M_m(t-s)) ds = tM_m(t) - (m+1)M_{m+1}(t) - tD(t)M_m(0)`. -/
theorem liEvenCrossActualClockLogHistory_primitive_balance (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, D s*(s*deriv (M m) (t-s)-M m (t-s))) =
      t*M m t-(m+1:ℝ)*M (m+1) t-t*D t*M m 0 := by
  rw [pp_history_IBP ((contDiff_liEvenCrossActualClockBorelPrimitive m).of_le
    (by exact_mod_cast (le_top : (1:ℕ∞) ≤ ⊤))) t,
    liEvenCrossActualClockPrimitive_convolution_primitive m ht]

/-- At any clock where the history vanishes, every same-history balance is bounded below by
the strictly positive first source row. -/
theorem liEvenCrossActualClockLogHistory_primitive_balance_pos (m : ℕ) {t : ℝ} (ht : 0 < t)
    (hz : D t = 0) :
    nu 1*t^(m+3)/((m+3).factorial:ℝ) ≤
        ∫ s in (0:ℝ)..t, D s*(s*deriv (M m) (t-s)-M m (t-s)) ∧
      0 < ∫ s in (0:ℝ)..t, D s*(s*deriv (M m) (t-s)-M m (t-s)) := by
  rw [liEvenCrossActualClockLogHistory_primitive_balance m ht.le, hz, mul_zero, zero_mul, sub_zero,
    ← liEvenCrossActualClockPrimitive_convolution_primitive m ht.le]
  exact ⟨liEvenCrossActualClockPrimitive_convolution_primitive_lower m ht.le,
    liEvenCrossActualClockPrimitive_convolution_primitive_pos m ht⟩

/-- The same-history kernel `sM_m'(t-s) - M_m(t-s)` is negative at `s = 0` for `t > 0`. -/
theorem liEvenCrossActualClockBorelPrimitive_balanceKernel_origin_neg (m : ℕ) {t : ℝ}
    (ht : 0 < t) : 0*deriv (M m) (t-0) - M m (t-0) < 0 := by
  rw [sub_zero, zero_mul, zero_sub, neg_lt_zero]
  exact liEvenCrossActualClockBorelPrimitive_pos m ht

private theorem ppT_complex_cont : Continuous T := ppT_differentiable.continuous

private theorem pp_lag_cont (t : ℝ) : Continuous (fun s : ℝ => (T ((t-s):ℂ)).re) :=
  Complex.continuous_re.comp (ppT_complex_cont.comp (continuous_const.sub Complex.continuous_ofReal))

/-- **Signed correction (B7).**  For `t ≥ 0`,
`∫₀ᵗ P(s)(t-s)T(t-s) ds = (tM_1(t) - 2M_2(t))/2 - ∫₀ᵗ P(s)G(t-s) ds`. -/
theorem liEvenCrossActualClockPrimitive_score_convolution {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, P s*((t-s)*(T ((t-s):ℂ)).re)) =
      (t*M 1 t-2*M 2 t)/2 - ∫ s in (0:ℝ)..t, P s*G (t-s) := by
  have hGc : Continuous G := contDiff_liEvenCrossActualClockPrimitiveScoreGap.continuous
  have hM1 : Continuous (fun s => M 1 (t-s)) :=
    (contDiff_liEvenCrossActualClockBorelPrimitive 1).continuous.comp
      (continuous_const.sub continuous_id)
  have hG1 : Continuous (fun s => G (t-s)) := hGc.comp (continuous_const.sub continuous_id)
  have h1 := liEvenCrossActualClockPrimitive_convolution_primitive 1 ht
  calc (∫ s in (0:ℝ)..t, P s*((t-s)*(T ((t-s):ℂ)).re))
      = ∫ s in (0:ℝ)..t, (1/2)*(P s*M 1 (t-s)) - P s*G (t-s) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        rw [← Complex.ofReal_sub]
        unfold liEvenCrossActualClockPrimitiveScoreGap
        ring
    _ = (1/2)*(∫ s in (0:ℝ)..t, P s*M 1 (t-s)) - ∫ s in (0:ℝ)..t, P s*G (t-s) := by
        rw [intervalIntegral.integral_sub
          (by exact ((ppPrimitive_continuous.mul hM1).const_mul _).intervalIntegrable _ _ :
            IntervalIntegrable (fun s => (1/2)*(P s*M 1 (t-s))) volume 0 t)
          (by exact (ppPrimitive_continuous.mul hG1).intervalIntegrable _ _ :
            IntervalIntegrable (fun s => P s*G (t-s)) volume 0 t),
          intervalIntegral.integral_const_mul]
    _ = _ := by rw [h1]; push_cast; ring

/-- The gap convolution as a signed same-history test: for every `t`,
`∫₀ᵗ P(s)G(t-s) ds = ∫₀ᵗ D(s)(sG'(t-s) - G(t-s)) ds`. -/
theorem liEvenCrossActualClockLogHistory_score_gap_balance (t : ℝ) :
    (∫ s in (0:ℝ)..t, P s*G (t-s)) = ∫ s in (0:ℝ)..t, D s*(s*deriv G (t-s)-G (t-s)) := by
  rw [pp_history_IBP (contDiff_liEvenCrossActualClockPrimitiveScoreGap.of_le
    (by exact_mod_cast (le_top : (1:ℕ∞) ≤ ⊤))) t,
    liEvenCrossActualClockPrimitiveScoreGap_zero, mul_zero, sub_zero]

/-- **Outer score-history reduction (B8).**  At a guarded zero `t > 20`, `D(t) = 0`,
`D ≥ 0` on `[0,t]`, the cost integral splits into its two nonnegative history terms, the positive
primitive bracket, the signed gap convolution and the full early truncation. -/
theorem liEvenCrossActualClockScoreHistory_primitive_gap_decomposition {t : ℝ}
    (ht : 20 < t) (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    IU t = 16*ell t*D (ell t)*(t-ell t)*(T ((t-ell t):ℂ)).re +
      (∫ s in ell t..t, D s*(16*t-15*s)*(T ((t-s):ℂ)).re) +
      8*(t*M 1 t-2*M 2 t) - 16*(∫ s in (0:ℝ)..t, P s*G (t-s)) -
      16*(∫ s in (0:ℝ)..ell t, P s*((t-s)*(T ((t-s):ℂ)).re)) := by
  have hd := (liEvenCrossActualClockScoreHistory_signed_decomposition ht hz hHist).1
  have hc : Continuous (fun s => P s*((t-s)*(T ((t-s):ℂ)).re)) :=
    ppPrimitive_continuous.mul ((continuous_const.sub continuous_id).mul (pp_lag_cont t))
  have hsplit : (∫ s in ell t..t, P s*(t-s)*(T ((t-s):ℂ)).re) =
      (∫ s in (0:ℝ)..t, P s*((t-s)*(T ((t-s):ℂ)).re)) -
        ∫ s in (0:ℝ)..ell t, P s*((t-s)*(T ((t-s):ℂ)).re) := by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    congr 1; funext s; ring
  rw [hd, hsplit, liEvenCrossActualClockPrimitive_score_convolution (by linarith)]
  ring

private theorem pp_row_nonneg {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    0 ≤ a m*M m r :=
  mul_nonneg (ha m) (le_trans (by positivity) (liEvenCrossActualClockBorelPrimitive_bounds m hr).1)

/-- **No nonnegative constant primitive transfer (B6), countable form.**  For no `R > 0` and no
nonnegative coefficients is `rT(r) = ∑ a_m M_m(r)` (as a genuine `HasSum`) on all of `(0, R]`. -/
theorem not_liEvenCrossActualClock_nonneg_primitive_score_mixture
    {R : ℝ} (hR : 0 < R) (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) :
    ¬ ∀ r : ℝ, 0 < r → r ≤ R → HasSum (fun m : ℕ => a m*M m r) (r*(T (r:ℂ)).re) := by
  intro hrep
  have hnear : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r ∧ r ≤ R := by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr using ⟨hr.1, hr.2.le⟩
  have ha0 : a 0 = 0 := by
    refine le_antisymm ?_ (ha 0)
    have hlim : Tendsto (fun r => r*ppT r) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun r => r*ppT r) (𝓝 0) (𝓝 (0*ppT 0)) :=
        (continuous_id.mul ppT_contDiff.continuous).tendsto 0
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim (hnear.mono fun r ⟨hr, hrR⟩ => ?_)
    have hs := hrep r hr hrR
    have h0 := hs.summable.le_tsum 0 (fun m _ => pp_row_nonneg ha hr.le m)
    rw [hs.tsum_eq] at h0
    have hB : 1 ≤ M 0 r := by simpa using (liEvenCrossActualClockBorelPrimitive_bounds 0 hr.le).1
    calc a 0 = a 0*1 := by ring
      _ ≤ a 0*M 0 r := mul_le_mul_of_nonneg_left hB (ha 0)
      _ ≤ r*ppT r := h0
  have hsR := hrep R hR le_rfl
  have hsumR : Summable (fun m => a m*(R^m/(m.factorial:ℝ))) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (ha m) (by positivity))
      (fun m => mul_le_mul_of_nonneg_left (liEvenCrossActualClockBorelPrimitive_bounds m hR.le).1
        (ha m)) hsR.summable
  have hsum2 : Summable (fun m => a (m+2)*(R^(m+2)/((m+2).factorial:ℝ))) :=
    (summable_nat_add_iff (f := fun m => a m*(R^m/(m.factorial:ℝ))) 2).mpr hsumR
  set C := ∑' m, a (m+2)*(R^(m+2)/((m+2).factorial:ℝ)) with hC
  have hupper : ∀ r, 0 < r → r ≤ R → ppT r ≤ a 1*B r + B R*C*r/R^2 := by
    intro r hr hrR
    have hs := hrep r hr hrR
    have hs2 := (hasSum_nat_add_iff' 2).mpr hs
    have hBr : B r ≤ B R := liEvenCrossActualClockBorelKernel_mono hr.le hrR
    have hle : ∀ m, a (m+2)*M (m+2) r ≤
        (B R*r^2/R^2)*(a (m+2)*(R^(m+2)/((m+2).factorial:ℝ))) := by
      intro m
      have hb := (liEvenCrossActualClockBorelPrimitive_bounds (m+2) hr.le).2
      have hpow : r^(m+2) ≤ r^2/R^2*R^(m+2) := by
        have h := pow_le_pow_left₀ hr.le hrR m
        calc r^(m+2) = r^m*r^2 := pow_add r m 2
          _ ≤ R^m*r^2 := mul_le_mul_of_nonneg_right h (by positivity)
          _ = r^2/R^2*R^(m+2) := by rw [pow_add]; field_simp
      calc a (m+2)*M (m+2) r ≤ a (m+2)*(B r*r^(m+2)/((m+2).factorial:ℝ)) :=
            mul_le_mul_of_nonneg_left hb (ha _)
        _ ≤ a (m+2)*(B R*(r^2/R^2*R^(m+2))/((m+2).factorial:ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (ha _)
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul hBr hpow (by positivity)
              (le_trans zero_le_one (one_le_liEvenCrossActualClockBorelKernel R))
        _ = _ := by ring
    have htail : ∑' m, a (m+2)*M (m+2) r ≤ B R*C*r^2/R^2 := by
      calc ∑' m, a (m+2)*M (m+2) r ≤
            ∑' m, (B R*r^2/R^2)*(a (m+2)*(R^(m+2)/((m+2).factorial:ℝ))) :=
            Summable.tsum_le_tsum hle hs2.summable (hsum2.mul_left _)
        _ = B R*C*r^2/R^2 := by rw [tsum_mul_left, ← hC]; ring
    rw [hs2.tsum_eq] at htail
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ha0, zero_mul] at htail
    have hM1 : M 1 r ≤ B r*r := by
      simpa using (liEvenCrossActualClockBorelPrimitive_bounds 1 hr.le).2
    have h1 : a 1*M 1 r ≤ a 1*(B r*r) := mul_le_mul_of_nonneg_left hM1 (ha 1)
    have hmain : r*ppT r ≤ r*(a 1*B r + B R*C*r/R^2) := by
      have e : r*(a 1*B r + B R*C*r/R^2) = a 1*(B r*r) + B R*C*r^2/R^2 := by ring
      rw [e]
      change r*(T (r:ℂ)).re - a 1*M 1 r ≤ B R*C*r^2/R^2 at htail
      unfold ppT
      linarith
    exact le_of_mul_le_mul_left hmain hr
  have ha1 : 1/2 ≤ a 1 := by
    have hl : Tendsto ppT (𝓝[>] 0) (𝓝 (1/2)) := by
      rw [← ppT_zero]
      exact (ppT_contDiff.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
    have hr : Tendsto (fun r => a 1*B r + B R*C*r/R^2) (𝓝[>] 0) (𝓝 (a 1)) := by
      have h : Tendsto (fun r => a 1*B r + B R*C*r/R^2) (𝓝 0)
          (𝓝 (a 1*B 0 + B R*C*0/R^2)) :=
        ((continuous_const.mul continuous_liEvenCrossActualClockBorelKernel).add
          ((continuous_const.mul continuous_id).div_const _)).tendsto 0
      simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    exact le_of_tendsto_of_tendsto hl hr (hnear.mono fun r ⟨hr, hrR⟩ => hupper r hr hrR)
  have h1 := hsR.summable.le_tsum 1 (fun m _ => pp_row_nonneg ha hR.le m)
  rw [hsR.tsum_eq] at h1
  have hG := liEvenCrossActualClockPrimitiveScoreGap_pos hR
  unfold liEvenCrossActualClockPrimitiveScoreGap at hG
  have hM1 := liEvenCrossActualClockBorelPrimitive_pos 1 hR
  nlinarith [mul_le_mul_of_nonneg_right ha1 hM1.le]

/-- **No nonnegative constant primitive transfer (B6), finite form.** -/
theorem not_liEvenCrossActualClock_nonneg_finite_primitive_score_mixture
    {R : ℝ} (hR : 0 < R) (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ m ∈ S, 0 ≤ a m) :
    ¬ ∀ r : ℝ, 0 < r → r ≤ R → r*(T (r:ℂ)).re = ∑ m ∈ S, a m*M m r := by
  classical
  intro hrep
  refine not_liEvenCrossActualClock_nonneg_primitive_score_mixture hR
    (fun m => if m ∈ S then a m else 0)
    (fun m => by split_ifs with h; exacts [ha m h, le_rfl]) fun r hr hrR => ?_
  rw [hrep r hr hrR]
  have h : HasSum (fun m => (if m ∈ S then a m else 0)*M m r)
      (∑ m ∈ S, (if m ∈ S then a m else 0)*M m r) :=
    hasSum_sum_of_ne_finset_zero (fun m hm => by simp [hm])
  convert h using 1
  exact Finset.sum_congr rfl fun m hm => by simp [hm]

end
end RHTower
