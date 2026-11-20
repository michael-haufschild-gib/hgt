import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ThePrimitiveRatioVarianceOfATwistedMoebiusMoment
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided
import GaloisForLFunctions.RHTower.Sieve.PhaseIntegral
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Sharp interval measurements concentrate on the squarefree diagonal

For a time interval of length L the square of its Fourier transform is
at most 2L/|u| at frequency u. At a reduced ratio m/n the squared atom
costs at most H_N²/(mn). The reciprocal log spacing then leaves just
two harmonic sums. The variance grows linearly with the interval length,
uniformly in its starting height.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
open Finset Complex MeasureTheory
open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.ArithmeticLorentzianGeometry MoebiusGram
noncomputable section

private def logLoss (N : ℕ) := 1+Real.log ((N:ℝ)+1)

private theorem loss_one_le (N : ℕ) : 1 ≤ logLoss N :=
  le_add_of_nonneg_right (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _)))

private theorem harmonic_le_loss (N : ℕ) : ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹ ≤ logLoss N := by
  rcases Nat.eq_zero_or_pos N with rfl|hp
  · norm_num [logLoss]
  have hh := harmonic_le_one_add_log N
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hh
  exact hh.trans (add_le_add (le_refl 1) (Real.log_le_log (Nat.cast_pos.mpr hp)
    (le_add_of_nonneg_right zero_le_one)))

private theorem coeff_sq_le (n : ℕ) : (coeff n)^2 ≤ (n:ℝ)⁻¹ := by
  have hh : |mobiusRealCoefficient n| ≤ 1 := by
    unfold mobiusRealCoefficient
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg _),←one_div]
  exact div_le_div_of_nonneg_right ((sq_le_one_iff_abs_le_one _).mpr hh) (Nat.cast_nonneg _)

private theorem scale_le_loss (N m n : ℕ) : primitiveCubicScaleWeight 0 N m n ≤ logLoss N := by
  unfold primitiveCubicScaleWeight
  simp only [sub_zero,Real.rpow_neg_one]
  apply le_trans (sum_le_sum (g:=fun d : ℕ => (d:ℝ)⁻¹) (fun d _ => ?_))
    ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun d _ _ => inv_nonneg.mpr (Nat.cast_nonneg d))).trans
      (harmonic_le_loss N))
  split_ifs
  · have hh : |mobiusRealCoefficient d| ≤ 1 := by
      unfold mobiusRealCoefficient
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg _)) ((sq_le_one_iff_abs_le_one _).mpr hh)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem atom_sq_le (N m n : ℕ) :
    (atom N m n)^2 ≤ (logLoss N)^2*((m:ℝ)⁻¹*(n:ℝ)⁻¹) := by
  rw [atom,mul_pow,mul_pow,mul_comm _ ((primitiveCubicScaleWeight 0 N m n)^2)]
  exact mul_le_mul
    (pow_le_pow_left₀ (primitiveCubicScaleWeight_nonneg 0 N m n) (scale_le_loss N m n) 2)
    (mul_le_mul (coeff_sq_le m) (coeff_sq_le n) (sq_nonneg _) (by positivity))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

/-- A translated sharp interval retains both the length bound and the
inverse-frequency bound of the original Dirichlet kernel. -/
theorem sharp_time_transform_sq_le {A B u : ℝ} (h : A ≤ B) (hu : u ≠ 0) :
    ‖timeTransform (volume.restrict (Set.Ioc A B)) u‖^2 ≤ (B-A)*(2/|u|) := by
  have hlen := intervalIntegral.norm_integral_le_of_norm_le_const (a:=A) (b:=B)
    (fun t _ => (norm_timePhase u t).le)
  rw [abs_of_nonneg (sub_nonneg.mpr h),one_mul] at hlen
  have hprim : (∫ t in A..B, timePhase u t) = (timePhase u B-timePhase u A)/((u:ℂ)*Complex.I) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_phase u 0 A) (intervalIntegrable_exp_phase u A B)
    rw [integral_exp_phase u hu A,integral_exp_phase u hu B] at hh
    change (_-1)/((u:ℂ)*Complex.I)+(∫ t in A..B, timePhase u t)=(_-1)/((u:ℂ)*Complex.I) at hh
    calc _ = (timePhase u B-1)/((u:ℂ)*Complex.I)-(timePhase u A-1)/((u:ℂ)*Complex.I) := by linear_combination hh
         _ = _ := by ring
  have hfreq : ‖∫ t in A..B, timePhase u t‖ ≤ 2/|u| := by
    rw [hprim,norm_div,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    exact (norm_sub_le _ _).trans_eq (by rw [norm_timePhase,norm_timePhase]; norm_num)
  rw [timeTransform,←intervalIntegral.integral_of_le h,sq]
  exact mul_le_mul hlen hfreq (norm_nonneg _) (sub_nonneg.mpr h)

private def crossBound (m n : ℕ) :=
  (n:ℝ)⁻¹*(1/|(m:ℝ)-n|)+(m:ℝ)⁻¹*(n:ℝ)⁻¹

private theorem crossBound_nonneg (m n : ℕ) : 0 ≤ crossBound m n := by unfold crossBound; positivity

private theorem cross_term {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    (m:ℝ)⁻¹*(n:ℝ)⁻¹*(1/|ratioFrequency m n|) ≤ crossBound m n := by
  have h := mul_le_mul_of_nonneg_left (inv_abs_log_sub_le hm hn hmn)
    (by positivity : 0 ≤ (m:ℝ)⁻¹*(n:ℝ)⁻¹)
  apply h.trans_eq
  rw [abs_sub_comm (n:ℝ),crossBound]
  have hp : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  simp only [div_eq_mul_inv,one_mul]
  calc
    _ = (n:ℝ)⁻¹*(((m:ℝ)⁻¹*m)*|(m:ℝ)-n|⁻¹)+(m:ℝ)⁻¹*(n:ℝ)⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ hp,one_mul]

private theorem cross_sum (N : ℕ) : ∑ q ∈ primitiveRatioPairs N, crossBound q.1 q.2 ≤ 3*(logLoss N)^2 := by
  let S := Icc 1 N
  have hdist (n : ℕ) (hn : n∈S) : ∑ m ∈ S, 1/|(m:ℝ)-n| ≤ 2*logLoss N := by
    have h := sum_inv_abs_int_dist_le (N:=N+1) (m:=n) (Nat.lt_succ_of_le (mem_Icc.mp hn).2)
    rw [←sum_erase_add _ _ hn,sub_self,abs_zero,div_zero,add_zero]
    refine (sum_le_sum_of_subset_of_nonneg (fun m hm => mem_erase.mpr
      ⟨(mem_erase.mp hm).1,mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp (mem_erase.mp hm).2).2)⟩)
      (fun _ _ _ => by positivity)).trans ?_
    simpa only [Nat.cast_succ,logLoss] using h
  have hH := harmonic_le_loss N
  have hL : 0 ≤ logLoss N := zero_le_one.trans (loss_one_le N)
  have hrow (n : ℕ) (hn : n ∈ S) : ∑ m ∈ S, crossBound m n ≤ (n:ℝ)⁻¹*(3*logLoss N) := by
    simp only [crossBound,sum_add_distrib,←mul_sum,←sum_mul]
    have ha := mul_le_mul_of_nonneg_left (hdist n hn) (inv_nonneg.mpr (Nat.cast_nonneg n))
    have hb := mul_le_mul_of_nonneg_right hH (inv_nonneg.mpr (Nat.cast_nonneg n))
    nlinarith only [ha,hb]
  apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => crossBound_nonneg q.1 q.2)).trans
  rw [sum_product,sum_comm]
  refine (sum_le_sum hrow).trans ?_
  rw [←sum_mul]
  exact (mul_le_mul_of_nonneg_right hH (by positivity : 0 ≤ 3*logLoss N)).trans_eq (by ring)

/-- For every sharp height window the prime-twist variance is at most
six times its length times the fourth power of the logarithmic loss. -/
theorem sharp_interval_moebius_variance (N : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    ∫ x, (centeredMoment (volume.restrict (Set.Ioc A B)) N x)^2 ∂
      GaloisForLFunctions.ArithmeticCorrelationGeometry.gaugeHaar ≤
        6*(B-A)*(1+Real.log ((N:ℝ)+1))^4 := by
  let ν := volume.restrict (Set.Ioc A B)
  let C := 2*(B-A)*(logLoss N)^2
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hAB)) (sq_nonneg _)
  rw [integral_centered_moment_sq]
  have he (q : ℕ × ℕ) (hq : q ∈ primitiveRatioPairs N) :
      (atom N q.1 q.2)^2*‖timeTransform ν (ratioFrequency q.1 q.2)‖^2 ≤ C*crossBound q.1 q.2 := by
    obtain ⟨hin,hcop,hne⟩ := mem_filter.mp hq
    obtain ⟨hm,hn⟩ := mem_product.mp hin
    have hm' := (mem_Icc.mp hm).1
    have hn' := (mem_Icc.mp hn).1
    have hu : ratioFrequency q.1 q.2 ≠ 0 := sub_ne_zero.mpr (fun eq => hne
      (Nat.cast_injective (α:=ℝ) ((Real.log_injOn_pos (Nat.cast_pos.mpr hn') (Nat.cast_pos.mpr hm') eq).symm)))
    have h := mul_le_mul (atom_sq_le N q.1 q.2) (sharp_time_transform_sq_le hAB hu) (sq_nonneg _)
      (by positivity : 0 ≤ (logLoss N)^2*((q.1:ℝ)⁻¹*(q.2:ℝ)⁻¹))
    refine h.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (cross_term hm' hn' hne) hC))
    dsimp only [C]
    ring
  refine (sum_le_sum he).trans ?_
  rw [←mul_sum]
  exact (mul_le_mul_of_nonneg_left (cross_sum N) hC).trans_eq (by dsimp only [C,logLoss]; ring)

#print axioms sharp_time_transform_sq_le
#print axioms sharp_interval_moebius_variance
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
