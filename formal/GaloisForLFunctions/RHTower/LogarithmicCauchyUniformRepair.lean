import GaloisForLFunctions.HTGeometry.FrullaniIntegral
import GaloisForLFunctions.RHTower.CCMDiagonalFockLift
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A uniform squared-Cauchy repair of the logarithmic Cauchy kernel

For positive nodes, `[L+(log u+log v)/2]/(u+v)+c/(u+v)^2` is positive
semidefinite at every finite rank whenever `c>0` and `L+log c≥2`.
The proof retains Frullani cancellation and bounds the shift correlation by
ordinary exponential-feature energy and its first moment.

The coefficient obtained from the literal theta first correction meets this
condition beyond an explicit translation threshold. This is an exact theorem
about the corrected model; the complete-source remainder is not estimated here.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.LogCauchyRepair
open GaloisForLFunctions.HTGeometry

private def frullani (a b t : ℝ) : ℝ :=
  (Real.exp (-(a*t))-Real.exp (-(b*t)))/t

private theorem frullani_re (a b t : ℝ) : frullani a b t =
    ((Complex.exp (-((a:ℂ)*t))-Complex.exp (-((b:ℂ)*t)))/(t:ℂ)).re := by
  simp [frullani, Complex.exp_re]

private theorem frullani_integrable {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    IntegrableOn (frullani a b) (Ioi 0) := by
  have h := (integrableOn_frullani (a := (a:ℂ)) (b := (b:ℂ))
    (by simpa using ha) (by simpa using hb)).re
  change Integrable (frullani a b) (volume.restrict (Ioi 0))
  convert h using 1
  funext t
  exact frullani_re a b t

private theorem frullani_integral {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (∫ t in Ioi 0, frullani a b t) = Real.log b-Real.log a := by
  have hc := integrableOn_frullani (a := (a:ℂ)) (b := (b:ℂ))
    (by simpa using ha) (by simpa using hb)
  have he := integral_frullani (a := (a:ℂ)) (b := (b:ℂ))
    (by simpa using ha) (by simpa using hb)
  simp_rw [frullani_re]
  calc
    _ = ((∫ t in Ioi (0:ℝ), (Complex.exp (-((a:ℂ)*t))-
        Complex.exp (-((b:ℂ)*t)))/(t:ℂ)) : ℂ).re := by
      convert integral_re hc using 1 <;> rfl
    _ = _ := by rw [he]; simp [Complex.log_re, abs_of_pos ha, abs_of_pos hb]

def feature {n : ℕ} (u a : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i, a i*Real.exp (-(u i*s))

private theorem feature_mul {n : ℕ} (u a b : Fin n → ℝ) (s : ℝ) :
    feature u a s*feature u b s =
      ∑ i, ∑ j, a i*b j*Real.exp (-(u i+u j)*s) := by
  unfold feature
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show -(u i+u j)*s = -(u i*s)+-(u j*s) by ring, Real.exp_add]
  ring

private theorem cross_integrable {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a b : Fin n → ℝ) (r : ℝ) :
    IntegrableOn (fun s => feature u a s*feature u b s) (Ioi r) := by
  simp_rw [feature_mul]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (exp_neg_integrableOn_Ioi r (add_pos (hu i) (hu j))).const_mul _

private theorem cross_integral {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a b : Fin n → ℝ) (r : ℝ) :
    (∫ s in Ioi r, feature u a s*feature u b s) =
      ∑ i, ∑ j, a i*b j*Real.exp (-(u i+u j)*r)/(u i+u j) := by
  simp_rw [feature_mul]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (exp_neg_integrableOn_Ioi r (add_pos (hu i) (hu j))).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    (exp_neg_integrableOn_Ioi r (add_pos (hu i) (hu j))).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos (add_pos (hu i) (hu j)))]
  simp only [div_neg]
  ring

private theorem feature_shift {n : ℕ} (u a : Fin n → ℝ) (s t : ℝ) :
    feature u a (s+t) = feature u (fun i => a i*Real.exp (-(u i*t))) s := by
  unfold feature
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -(u i*(s+t)) = -(u i*t)+-(u i*s) by ring, Real.exp_add]
  ring

private theorem shifted_square_integral {n : ℕ} {u : Fin n → ℝ}
    (hu : ∀ i, 0<u i) (a : Fin n → ℝ) (t : ℝ) :
    (∫ s in Ioi 0, (feature u a (s+t))^2) =
      ∫ s in Ioi t, (feature u a s)^2 := by
  simp_rw [feature_shift, sq]
  rw [cross_integral hu, cross_integral hu]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_zero, Real.exp_zero, mul_one]
  rw [show -(u i+u j)*t = -(u i*t)+-(u j*t) by ring, Real.exp_add]
  ring

private theorem moment_pair_integrable {v : ℝ} (hv : 0<v) :
    IntegrableOn (fun s : ℝ => s*Real.exp (-v*s)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1:ℝ)) (p := (1:ℝ)) (by norm_num) le_rfl hv

private theorem moment_pair_integral {v : ℝ} (hv : 0<v) :
    (∫ s in Ioi 0, s*Real.exp (-v*s)) = 1/v^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2:ℝ)) (by norm_num) hv
  norm_num [Real.Gamma_nat_eq_factorial, ← neg_mul] at h
  simpa [one_div, inv_pow] using h

private theorem moment_expand {n : ℕ} (u a : Fin n → ℝ) (s : ℝ) :
    s*(feature u a s)^2 =
      ∑ i, ∑ j, a i*a j*(s*Real.exp (-(u i+u j)*s)) := by
  rw [sq, feature_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem moment_integrable {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) : IntegrableOn (fun s => s*(feature u a s)^2) (Ioi 0) := by
  simp_rw [moment_expand]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (moment_pair_integrable (add_pos (hu i) (hu j))).const_mul _

private theorem moment_integral {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) : (∫ s in Ioi 0, s*(feature u a s)^2) =
      ∑ i, ∑ j, a i*a j/(u i+u j)^2 := by
  simp_rw [moment_expand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (moment_pair_integrable (add_pos (hu i) (hu j))).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    (moment_pair_integrable (add_pos (hu i) (hu j))).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, moment_pair_integral (add_pos (hu i) (hu j))]
  ring

def energy {n : ℕ} (u a : Fin n → ℝ) : ℝ := ∫ s in Ioi 0, (feature u a s)^2
def moment {n : ℕ} (u a : Fin n → ℝ) : ℝ := ∫ s in Ioi 0, s*(feature u a s)^2
def correlation {n : ℕ} (u a : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioi 0, feature u a (s+t)*feature u a s

private theorem square_integrable {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (r : ℝ) : IntegrableOn (fun s => (feature u a s)^2) (Ioi r) := by
  simpa only [sq] using cross_integrable hu a a r

private theorem shifted_square_integrable {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (t : ℝ) :
    IntegrableOn (fun s => (feature u a (s+t))^2) (Ioi 0) := by
  simp_rw [feature_shift]
  exact square_integrable hu _ _

private theorem correlation_integrable {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (t : ℝ) :
    IntegrableOn (fun s => feature u a (s+t)*feature u a s) (Ioi 0) := by
  simp_rw [feature_shift]
  exact cross_integrable hu _ _ _

private theorem energy_nonneg {n : ℕ} (u a : Fin n → ℝ) : 0 ≤ energy u a :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _

private theorem moment_nonneg {n : ℕ} (u a : Fin n → ℝ) : 0 ≤ moment u a :=
  setIntegral_nonneg measurableSet_Ioi fun s hs => mul_nonneg hs.le (sq_nonneg _)

private theorem tail_energy_le {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {t : ℝ} (ht : 0≤t) :
    (∫ s in Ioi t, (feature u a s)^2) ≤ energy u a := by
  apply setIntegral_mono_set (square_integrable hu a 0)
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact (Ioi_subset_Ioi ht).eventuallyLE

private theorem tail_moment_le {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {t : ℝ} (ht : 0≤t) :
    t*(∫ s in Ioi t, (feature u a s)^2) ≤ moment u a := by
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ s in Ioi t, s*(feature u a s)^2 := by
      apply setIntegral_mono_on ((square_integrable hu a t).const_mul t)
        ((moment_integrable hu a).mono_set (Ioi_subset_Ioi ht)) measurableSet_Ioi
      intro s hs
      exact mul_le_mul_of_nonneg_right hs.le (sq_nonneg _)
    _ ≤ moment u a := by
      apply setIntegral_mono_set (moment_integrable hu a)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact mul_nonneg hs.le (sq_nonneg _)
      · exact (Ioi_subset_Ioi ht).eventuallyLE

private theorem correlation_young {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (t b : ℝ) :
    2*b*correlation u a t ≤ energy u a+b^2*(∫ s in Ioi t, (feature u a s)^2) := by
  have h := setIntegral_mono_on ((correlation_integrable hu a t).const_mul (2*b))
    ((square_integrable hu a 0).add ((shifted_square_integrable hu a t).const_mul (b^2)))
    measurableSet_Ioi (fun s _ => show
      2*b*(feature u a (s+t)*feature u a s) ≤
        (feature u a s)^2+b^2*(feature u a (s+t))^2 by
          nlinarith [sq_nonneg (feature u a s-b*feature u a (s+t))])
  dsimp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add (square_integrable hu a 0)
    ((shifted_square_integrable hu a t).const_mul (b^2)), integral_const_mul,
    shifted_square_integral hu a t] at h
  exact h

private theorem correlation_le_energy {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {t : ℝ} (ht : 0≤t) : correlation u a t ≤ energy u a := by
  have h := correlation_young hu a t 1
  have htail := tail_energy_le hu a ht
  norm_num at h
  linarith

private theorem correlation_tail_bound {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {t : ℝ} (ht : 0<t) :
    correlation u a t/t ≤ (energy u a+moment u a)/2*t^(-(3/2:ℝ)) := by
  have h := correlation_young hu a t (Real.sqrt t)
  rw [Real.sq_sqrt ht.le] at h
  have htail := tail_moment_le hu a ht.le
  have hs := Real.sqrt_pos.2 ht
  have hp : t^(-(3/2:ℝ)) = 1/(t*Real.sqrt t) := by
    rw [Real.rpow_neg ht.le, show (3/2:ℝ)=1+1/2 by norm_num,
      Real.rpow_add ht, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  rw [hp, mul_one_div]
  apply (le_div_iff₀ (show 0<t*Real.sqrt t by positivity)).2
  have hid : (correlation u a t/t)*(t*Real.sqrt t) =
      correlation u a t*Real.sqrt t := by field_simp
  rw [hid]
  linarith


private theorem energy_sum {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) : energy u a = ∑ i, ∑ j, a i*a j/(u i+u j) := by
  simp only [energy, sq, cross_integral hu, mul_zero, Real.exp_zero, mul_one]

private theorem correlation_sum {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (t : ℝ) : correlation u a t =
      ∑ i, ∑ j, a i*a j*Real.exp (-(u i*t))/(u i+u j) := by
  unfold correlation
  simp_rw [feature_shift]
  rw [cross_integral hu]
  simp only [mul_zero, Real.exp_zero, mul_one]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private def logIntegrand {n : ℕ} (u a : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, (a i*a j/(u i+u j))*frullani 1 (u i) t

private theorem logIntegrand_integrable {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) : IntegrableOn (logIntegrand u a) (Ioi 0) := by
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (frullani_integrable zero_lt_one (hu i)).const_mul _

private theorem logIntegrand_eq {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (t : ℝ) : logIntegrand u a t =
      (Real.exp (-t)*energy u a-correlation u a t)/t := by
  rw [energy_sum hu, correlation_sum hu]
  simp only [logIntegrand, frullani, one_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem logIntegrand_integral {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) : (∫ t in Ioi 0, logIntegrand u a t) =
      ∑ i, ∑ j, a i*a j*Real.log (u i)/(u i+u j) := by
  unfold logIntegrand
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (frullani_integrable zero_lt_one (hu i)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (frullani_integrable zero_lt_one (hu i)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, frullani_integral zero_lt_one (hu i), Real.log_one, sub_zero]
  ring

private theorem logIntegrand_short_bound {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {t : ℝ} (ht : 0<t) : -energy u a ≤ logIntegrand u a t := by
  rw [logIntegrand_eq hu]
  apply (le_div_iff₀ ht).2
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (energy_nonneg u a)
  have hc := correlation_le_energy hu a ht.le
  nlinarith

private theorem logIntegrand_long_bound {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {t : ℝ} (ht : 0<t) :
    -((energy u a+moment u a)/2)*t^(-(3/2:ℝ)) ≤ logIntegrand u a t := by
  rw [logIntegrand_eq hu, sub_div]
  have h := correlation_tail_bound hu a ht
  have hp : 0 ≤ Real.exp (-t)*energy u a/t := by
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (energy_nonneg u a)) ht.le
  linarith

/-- The cancelled logarithmic form is controlled by energy and its first moment,
independently of the number or spacing of the positive exponential rates. -/
theorem log_form_lower_bound {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) :
    -2*energy u a-moment u a ≤ ∑ i, ∑ j, a i*a j*Real.log (u i)/(u i+u j) := by
  have hi := logIntegrand_integrable hu a
  have hs := hi.mono_set (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hl := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  have hc : IntegrableOn (fun _ : ℝ => -energy u a) (Ioc (0:ℝ) 1) := by
    exact continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hshort := setIntegral_mono_on hc hs measurableSet_Ioc
    (fun t ht => logIntegrand_short_bound hu a ht.1)
  have hp := integrableOn_Ioi_rpow_of_lt (a := -(3/2:ℝ)) (by norm_num) (c := (1:ℝ)) zero_lt_one
  have hlong := setIntegral_mono_on
    (hp.const_mul (-((energy u a+moment u a)/2))) hl measurableSet_Ioi
    (fun t ht => logIntegrand_long_bound hu a (lt_trans zero_lt_one ht))
  have hv : (∫ t : ℝ in Ioi 1, t^(-(3/2:ℝ))) = 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) zero_lt_one]
    norm_num
  rw [integral_const_mul, hv] at hlong
  have hjoin := intervalIntegral.integral_interval_add_Ioi hi hl
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    logIntegrand_integral hu a] at hjoin
  have hcval : (∫ _ in Ioc (0:ℝ) 1, -energy u a) = -energy u a := by simp
  rw [hcval] at hshort
  linarith


/-- Logarithmic Cauchy kernel repaired by a squared-Cauchy term. -/
def kernel (L c u v : ℝ) : ℝ :=
  (L+(Real.log u+Real.log v)/2)/(u+v)+c/(u+v)^2

private theorem log_sum_swap {n : ℕ} (u a : Fin n → ℝ) :
    (∑ i, ∑ j, a i*a j*Real.log (u j)/(u i+u j)) =
      ∑ i, ∑ j, a i*a j*Real.log (u i)/(u i+u j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm (u j) (u i), mul_comm (a j) (a i)]

private theorem kernel_form {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (L c : ℝ) :
    (∑ i, ∑ j, a i*a j*kernel L c (u i) (u j)) =
      L*energy u a+(∑ i, ∑ j, a i*a j*Real.log (u i)/(u i+u j))+c*moment u a := by
  have hpoint (i j : Fin n) : a i*a j*kernel L c (u i) (u j) =
      L*(a i*a j/(u i+u j))+
      (a i*a j*Real.log (u i)/(u i+u j)+a i*a j*Real.log (u j)/(u i+u j))/2+
      c*(a i*a j/(u i+u j)^2) := by unfold kernel; ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  rw [log_sum_swap, ← energy_sum hu, ← moment_integral hu]
  unfold moment
  ring

/-- The unit squared-Cauchy term repairs every finite logarithmic Cauchy matrix
at level at least 2. The bound is independent of rank and node spacing. -/
theorem unit_repair_quadratic_nonneg {n : ℕ} {u : Fin n → ℝ}
    (hu : ∀ i, 0<u i) (a : Fin n → ℝ) {L : ℝ} (hL : 2≤L) :
    0 ≤ ∑ i, ∑ j, a i*a j*kernel L 1 (u i) (u j) := by
  rw [kernel_form hu, one_mul]
  have h := log_form_lower_bound hu a
  have he := energy_nonneg u a
  nlinarith

/-- Exact scaling law; no smallness restriction on the positive repair coefficient. -/
theorem kernel_scale {c u v : ℝ} (hc : 0<c) (hu : 0<u) (hv : 0<v) (L : ℝ) :
    kernel L c u v = (1/c)*kernel (L+Real.log c) 1 (u/c) (v/c) := by
  unfold kernel
  rw [Real.log_div hu.ne' hc.ne', Real.log_div hv.ne' hc.ne']
  have hs : u+v ≠ 0 := (add_pos hu hv).ne'
  have hsc : u/c+v/c ≠ 0 := (add_pos (div_pos hu hc) (div_pos hv hc)).ne'
  field_simp
  ring

/-- A positive squared-Cauchy term gives a uniform repair whenever
`L + log c ≥ 2`, with no restriction on matrix size or positive node locations. -/
theorem repair_quadratic_nonneg {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) {L c : ℝ} (hc : 0<c) (hL : 2≤L+Real.log c) :
    0 ≤ ∑ i, ∑ j, a i*a j*kernel L c (u i) (u j) := by
  have h := unit_repair_quadratic_nonneg (fun i => div_pos (hu i) hc) a hL
  have he : (∑ i, ∑ j, a i*a j*kernel L c (u i) (u j)) =
      (1/c)*(∑ i, ∑ j, a i*a j*kernel (L+Real.log c) 1 (u i/c) (u j/c)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [kernel_scale hc (hu i) (hu j) L]
    ring
  rw [he]
  exact mul_nonneg (by positivity) h

/-- All finite matrices of the repaired kernel are positive semidefinite. -/
theorem posSemidef_repaired_matrix {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    {L c : ℝ} (hc : 0<c) (hL : 2≤L+Real.log c) :
    (Matrix.of (fun i j => kernel L c (u i) (u j))).PosSemidef := by
  refine ⟨?_, fun a => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, kernel]
    rw [add_comm (u j) (u i), add_comm (Real.log (u j)) (Real.log (u i))]
  · have he : (a.sum fun i ai => a.sum fun j aj =>
        star ai*Matrix.of (fun i j => kernel L c (u i) (u j)) i j*aj) =
        ∑ i, ∑ j, a i*a j*kernel L c (u i) (u j) := by
      rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.of_apply, star_trivial]
      ring
    rw [he]
    exact repair_quadratic_nonneg hu a hc hL


/-- The coefficient supplied by the literal-source first correction meets the
uniform repair condition at an explicit symbolic translation threshold. -/
theorem source_scale_condition {r : ℝ} (hr : Real.pi*Real.exp 2/7 ≤ r) :
    0 < 7*r*Real.exp (-2*r)/Real.pi ∧
    2 ≤ 2*r+Real.log (7*r*Real.exp (-2*r)/Real.pi) := by
  have hrp : 0<r := lt_of_lt_of_le (by positivity) hr
  have hp : 0<7*r/Real.pi := by positivity
  constructor
  · positivity
  · rw [show 7*r*Real.exp (-2*r)/Real.pi =
        (7*r/Real.pi)*Real.exp (-2*r) by ring,
      Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp]
    have he : Real.exp 2 ≤ 7*r/Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).2
      have hh := (div_le_iff₀ (by norm_num : (0:ℝ)<7)).1 hr
      nlinarith
    have hl := (Real.le_log_iff_exp_le hp).2 he
    linarith

/-- The explicit logarithmic model with the complete-source first-correction
coefficient is positive semidefinite at every finite rank beyond this threshold.
This is a theorem about the model; no estimate of the full source remainder is assumed. -/
theorem posSemidef_source_scale_model {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    {r : ℝ} (hr : Real.pi*Real.exp 2/7 ≤ r) :
    (Matrix.of (fun i j => kernel (2*r) (7*r*Real.exp (-2*r)/Real.pi) (u i) (u j))).PosSemidef := by
  exact posSemidef_repaired_matrix hu (source_scale_condition hr).1 (source_scale_condition hr).2

/-- Uniform quantitative lower bound: the repair leaves this exact multiple of
Cauchy energy available to absorb a further signed remainder. -/
theorem repair_quadratic_lower_bound {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0<u i)
    (a : Fin n → ℝ) (L : ℝ) {c : ℝ} (hc : 0<c) :
    (L+Real.log c-2)*energy u a ≤
      ∑ i, ∑ j, a i*a j*kernel L c (u i) (u j) := by
  have h := repair_quadratic_nonneg hu a (L := 2-Real.log c) hc (by linarith)
  have hid : (∑ i, ∑ j, a i*a j*kernel L c (u i) (u j)) =
      (∑ i, ∑ j, a i*a j*kernel (2-Real.log c) c (u i) (u j))+
      (L+Real.log c-2)*energy u a := by
    have he : energy u a = ∑ i, ∑ j, a i*a j/(u i+u j) := by
      unfold energy feature
      rw [← GaloisForLFunctions.RHTower.cauchy_quadratic_form hu a]
      simp [GaloisForLFunctions.RHTower.cauchyKernel, div_eq_mul_inv]
    rw [he]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold kernel
    ring
  rw [hid]
  linarith

/-- The literal-source first-correction scale leaves a logarithmically growing
uniform model reserve. The full theta remainder is not bounded by this theorem. -/
theorem source_scale_quadratic_lower_bound {n : ℕ} {u : Fin n → ℝ}
    (hu : ∀ i, 0<u i) (a : Fin n → ℝ) {r : ℝ} (hr : 0<r) :
    (Real.log (7*r/Real.pi)-2)*energy u a ≤
      ∑ i, ∑ j, a i*a j*kernel (2*r) (7*r*Real.exp (-2*r)/Real.pi) (u i) (u j) := by
  have hc : 0<7*r*Real.exp (-2*r)/Real.pi := by positivity
  have h := repair_quadratic_lower_bound hu a (2*r) hc
  have hp : 0<7*r/Real.pi := by positivity
  rw [show 7*r*Real.exp (-2*r)/Real.pi =
      (7*r/Real.pi)*Real.exp (-2*r) by ring,
    Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp] at h
  convert h using 1 <;> ring
end RHTower.LogCauchyRepair
