import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePositiveMeasureOfAMixedConductorBlock
import GaloisForLFunctions.SignedArithmeticCorrespondences.TheRealPlaceAfterGluingSignedEndpoints
import GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound
import GaloisForLFunctions.RHTower.ModularArcDyadicOriginInfinityEquipartition

/-!
# The real-place energy of the pole-subtracted ordinary prefix

Intersect all lower graphs through M with the upper endpoint M. Both the
integer order and the opposite-degree product persist in the second
difference. Their signed defect is a positive moment whose density is
comparable with the actual degree-one real Weil metric.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory _root_.RHTower

/-- Logarithmic mean of one and x, with its continuous value at one. -/
def logMean (x : ℝ) : ℝ := if x=1 then 1 else (1-x)/(-Real.log x)

theorem logMean_bounds {x : ℝ} (hx : x∈Set.Icc (0:ℝ) 1) :
    x ≤ logMean x ∧ logMean x ≤ 1 := by
  obtain ⟨hx0,hx1⟩ := hx
  rcases hx0.eq_or_lt with h | hp
  · subst x; simp [logMean]
  rcases hx1.eq_or_lt with h | hl
  · subst x; simp [logMean]
  have hn : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hp hl)
  rw [logMean,if_neg hl.ne]
  constructor
  · apply (le_div_iff₀ hn).mpr
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
    rw [mul_sub,mul_one,mul_inv_cancel₀ hp.ne'] at h
    linarith only [h]
  · exact (div_le_one hn).mpr (by linarith only [Real.log_le_sub_one_of_pos hp])

theorem integrable_logMean_product {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun x => f x * logMean x) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h : IntegrableOn (fun x => ‖f x‖) (Set.Ioc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hf.norm.intervalIntegrable 0 1)
  refine h.mono' ?_ ?_
  · have hmean : Measurable logMean :=
      Measurable.ite (measurableSet_singleton (1:ℝ)) measurable_const
        ((measurable_const.sub measurable_id).div Real.measurable_log.neg)
    exact (hf.measurable.mul hmean).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hm := logMean_bounds (Set.Ioc_subset_Icc_self hx)
    rw [norm_mul,Real.norm_eq_abs (logMean x),abs_of_nonneg (hx.1.le.trans hm.1)]
    exact mul_le_of_le_one_right (norm_nonneg _) hm.2

/-- The logarithmic mean stays below the arithmetic mean on the full interval. -/
theorem logMean_le_midpoint {x : ℝ} (hx : x∈Set.Icc (0:ℝ) 1) : logMean x ≤ (1+x)/2 := by
  rcases hx.1.eq_or_lt with h | hp
  · subst x; norm_num [logMean]
  rcases hx.2.eq_or_lt with h | hl
  · subst x; norm_num [logMean]
  have hi : 1≤1/x := (le_div_iff₀ hp).mpr (by simpa using hx.2)
  have h := HTGeometry.two_mul_sub_one_div_add_one_le_log hi
  have he : 2*(1/x-1)/(1/x+1) = 2*(1-x)/(1+x) := by field_simp
  rw [he,Real.log_div one_ne_zero hp.ne',Real.log_one,zero_sub] at h
  have hlog : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hp hl)
  rw [logMean,if_neg hl.ne]
  apply (div_le_iff₀ hlog).mpr
  linarith only [(div_le_iff₀ (show 0<1+x by positivity)).mp h]

/-- Opposite-degree product minus the actual logarithmic graph order, both
evaluated on the full lower divisor and the effective flat endpoint M. -/
def prefixPoleDefect (M : ℕ) : ℝ :=
  poleProduct M M (fun _ => 1) (fun j => if j=M then 1 else 0) - prefixHeight M

private def prefixHarm (m : ℕ) : ℝ := ∑ i ∈ Icc 1 m, 1/(i:ℝ)

/-- Grouping ordinary prime-power contacts by the upper degree gives the
logarithmic column of every effective prefix. -/
theorem prefixHeight_eq_sum_log (m : ℕ) :
    prefixHeight m = ∑ j ∈ Icc 1 m, Real.log j := by
  rw [prefixHeight,height_eq_quotient,← floorSummatory_chebyshevPsi]
  unfold floorSummatory
  cases m with
  | zero => simp
  | succ m =>
    refine sum_congr rfl fun i _ => ?_
    simp [apply_ite,ite_mul]

private theorem prefixPoleDefect_explicit (m : ℕ) :
    prefixPoleDefect m = prefixHarm m*(m:ℝ) - ∑ j ∈ Icc 1 m, Real.log j := by
  rw [prefixPoleDefect,poleProduct,prefixHeight_eq_sum_log]
  cases m <;> simp [prefixHarm,apply_ite,ite_mul]

/-- The curvature retains the reciprocal term from the pole product. -/
def prefixDefectCurvature (m : ℕ) : ℝ :=
  prefixPoleDefect (m+2)-2*prefixPoleDefect (m+1)+prefixPoleDefect m

/-- The pole contributes the reciprocal conductor and the integer height
contributes the logarithmic increment. -/
theorem prefix_curvature_entry (m : ℕ) :
    prefixDefectCurvature m = 1/((m:ℝ)+1) - (Real.log ((m:ℝ)+2)-Real.log ((m:ℝ)+1)) := by
  have hh (k : ℕ) : prefixHarm (k+1)=prefixHarm k+1/((k:ℝ)+1) := by
    rw [prefixHarm,sum_Icc_succ_top (Nat.succ_pos k),Nat.cast_succ,prefixHarm]
  have hd (k : ℕ) : prefixPoleDefect (k+1)-prefixPoleDefect k =
      prefixHarm k+1-Real.log ((k:ℝ)+1) := by
    rw [prefixPoleDefect_explicit,prefixPoleDefect_explicit,hh,sum_Icc_succ_top (Nat.succ_pos k),Nat.cast_succ]
    field_simp
    ring
  rw [prefixDefectCurvature,show prefixPoleDefect (m+2)-2*prefixPoleDefect (m+1)+prefixPoleDefect m =
    (prefixPoleDefect (m+2)-prefixPoleDefect (m+1))-(prefixPoleDefect (m+1)-prefixPoleDefect m) by ring,
    hd (m+1),hd m,hh,Nat.cast_succ,show (m:ℝ)+1+1=m+2 by ring]
  ring

private theorem logMean_moment (m : ℕ) :
    (∫ x in (0:ℝ)..1, x^m*logMean x) = Real.log ((m:ℝ)+2)-Real.log ((m:ℝ)+1) := by
  rw [intervalIntegral.integral_of_le zero_le_one,setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  have h := integral_log_increment ((m:ℝ)+1) (by positivity)
  rw [show (m:ℝ)+2=m+1+1 by ring,← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hx := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  simp only [logMean,if_neg hx.ne,Real.log_exp,neg_neg]
  have he : Real.exp (-(((m:ℝ)+1)*t)) = Real.exp (-t)*Real.exp (-t)^m := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  rw [show -(((m:ℝ)+1+1)*t) = -(((m:ℝ)+1)*t)+(-t) by ring,Real.exp_add,he]
  ring

/-- One positive measure gives the curvature of the full ordinary-prime
defect at every conductor. -/
theorem prefixDefectCurvature_moment (m : ℕ) :
    prefixDefectCurvature m = ∫ x in (0:ℝ)..1, x^m*(1-logMean x) := by
  have h (x : ℝ) : x^m*(1-logMean x)=x^m-x^m*logMean x := by ring
  simp only [h]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x^m) (g := fun x : ℝ => x^m*logMean x)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (integrable_logMean_product (by fun_prop)),
    hilbertMoment_eq_integral_pow,logMean_moment,prefix_curvature_entry]

private def poly (S : Finset ℕ) (u : ℕ → ℝ) (x : ℝ) : ℝ := ∑ i ∈ S, u i*x^i

private theorem integrated_defect (n : ℕ) (S T : Finset ℕ) (u v : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, u i*v j*prefixDefectCurvature (n+i+j)) =
      ∫ x in (0:ℝ)..1, (x^n*poly S u x*poly T v x)*(1-logMean x) := by
  have hi {f : ℝ → ℝ} (hf : Continuous f) :
      IntervalIntegrable (fun x => f x*(1-logMean x)) volume 0 1 := by
    simp only [mul_sub,mul_one]
    exact (hf.intervalIntegrable _ _).sub (integrable_logMean_product hf)
  have he (x : ℝ) : (x^n*poly S u x*poly T v x)*(1-logMean x) =
      ∑ i ∈ S, ∑ j ∈ T, (u i*v j)*(x^(n+i+j)*(1-logMean x)) := by
    rw [mul_assoc (x^n),poly,poly,sum_mul_sum]
    simp only [mul_sum,sum_mul,pow_add]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => he x)]
  have hij (i j : ℕ) : IntervalIntegrable (fun x : ℝ => (u i*v j)*(x^(n+i+j)*(1-logMean x))) volume 0 1 :=
    (hi (f := fun x : ℝ => x^(n+i+j)) (by fun_prop)).const_mul _
  have hrow (i : ℕ) : IntervalIntegrable
      (fun x : ℝ => ∑ j ∈ T, (u i*v j)*(x^(n+i+j)*(1-logMean x))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrable_finsetSum T fun j _ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hij i j)
  rw [intervalIntegral.integral_finsetSum (fun i _ => hrow i)]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => hij i j)]
  refine sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul,← prefixDefectCurvature_moment]

private theorem degreeOne_metric (n : ℕ) (S : Finset ℕ) (u : ℕ → ℝ) :
    2*∑ i ∈ S, ∑ j ∈ S, u i*u j*realEndpoint 1 (n+i+j) =
      ∫ x in (0:ℝ)..1, x^n*(1-x)*(poly S u x)^2 := by
  rw [realEndpoint_mixed 1 n Nat.zero_lt_one]
  simp only [sum_range_one,pow_zero,mul_one,poly,sq,mul_assoc]

/-- The curvature of the genuine pole-subtracted prefix lies between the
degree-one real Weil metric and twice that metric as quadratic forms on
all signed endpoint sections. -/
theorem prefix_defect_between_weil_metrics (n : ℕ) (S : Finset ℕ) (u : ℕ → ℝ) :
    let D := ∑ i ∈ S, ∑ j ∈ S, u i*u j*realEndpoint 1 (n+i+j)
    let G := ∑ i ∈ S, ∑ j ∈ S, u i*u j*prefixDefectCurvature (n+i+j)
    D ≤ G ∧ G ≤ 2*D := by
  intro D G
  let f (x : ℝ) := x^n*(poly S u x)^2
  have hc : Continuous f := by unfold f poly; fun_prop
  have hn (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : 0≤ f x := mul_nonneg (pow_nonneg hx.1 _) (sq_nonneg _)
  have hg : G=(∫ x in (0:ℝ)..1, f x*(1-logMean x)) := by
    rw [show G = _ from integrated_defect n S S u u]
    exact intervalIntegral.integral_congr fun x _ => by dsimp only [f]; ring
  have hd : 2*D=(∫ x in (0:ℝ)..1, f x*(1-x)) := by
    rw [show 2*D = _ from degreeOne_metric n S u]
    exact intervalIntegral.integral_congr fun x _ => by dsimp only [f]; ring
  have hi : IntervalIntegrable (fun x => f x*(1-logMean x)) volume 0 1 := by
    simp only [mul_sub,mul_one]
    exact (hc.intervalIntegrable _ _).sub (integrable_logMean_product hc)
  have hD : Continuous (fun x : ℝ => f x*(1-x)) := by fun_prop
  constructor
  · have h : (∫ x in (0:ℝ)..1, (f x*(1-x))*(1/2)) ≤ ∫ x in (0:ℝ)..1, f x*(1-logMean x) := by
      apply intervalIntegral.integral_mono_on zero_le_one ((hD.mul continuous_const).intervalIntegrable _ _) hi
      intro x hx
      change (f x*(1-x))*(1/2) ≤ f x*(1-logMean x)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith only [logMean_le_midpoint hx]) (hn x hx)
    rw [intervalIntegral.integral_mul_const,← hd,← hg] at h
    linarith only [h]
  · rw [hg,hd]
    apply intervalIntegral.integral_mono_on zero_le_one hi (hD.intervalIntegrable _ _)
    exact fun x hx => mul_le_mul_of_nonneg_left (sub_le_sub_left (logMean_bounds hx).1 _) (hn x hx)

/-- A genuine mixed arithmetic defect is priced by the separate real Weil
energies of its two signed endpoint sections. The estimate is uniform in
both supports and their relative signs. -/
theorem prefix_mixed_defect_le_weil_energies (n : ℕ) (S T : Finset ℕ) (u v : ℕ → ℝ) :
    |∑ i ∈ S, ∑ j ∈ T, u i*v j*prefixDefectCurvature (n+i+j)| ≤
      (∑ i ∈ S, ∑ j ∈ S, u i*u j*realEndpoint 1 (n+i+j))+
      (∑ i ∈ T, ∑ j ∈ T, v i*v j*realEndpoint 1 (n+i+j)) := by
  let U := poly S u
  let V := poly T v
  let f (x : ℝ) := x^n*U x*V x
  let D (w : ℝ → ℝ) (x : ℝ) := x^n*(1-x)*(w x)^2
  have hU : Continuous U := by
    change Continuous (fun x : ℝ => ∑ i ∈ S, u i*x^i)
    fun_prop
  have hV : Continuous V := by
    change Continuous (fun x : ℝ => ∑ j ∈ T, v j*x^j)
    fun_prop
  have hf : Continuous f := by unfold f; fun_prop
  have hu : Continuous (D U) := by unfold D; fun_prop
  have hv : Continuous (D V) := by unfold D; fun_prop
  have hi : IntervalIntegrable (fun x => f x*(1-logMean x)) volume 0 1 := by
    simp only [mul_sub,mul_one]
    exact (hf.intervalIntegrable _ _).sub (integrable_logMean_product hf)
  have h₁ := degreeOne_metric n S u
  have h₂ := degreeOne_metric n T v
  change 2*_=(∫ x in (0:ℝ)..1,D U x) at h₁
  change 2*_=(∫ x in (0:ℝ)..1,D V x) at h₂
  rw [integrated_defect]
  change |∫ x in (0:ℝ)..1, f x*(1-logMean x)| ≤ _
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  calc _ ≤ ∫ x in (0:ℝ)..1, (D U x+D V x)*(1/2) := by
         apply intervalIntegral.integral_mono_on zero_le_one (by simpa only [Real.norm_eq_abs] using hi.norm)
           (((hu.add hv).mul continuous_const).intervalIntegrable _ _)
         intro x hx
         have hm := logMean_bounds hx
         have hpow := pow_nonneg hx.1 n
         have hprod : |U x| * |V x| ≤ ((U x)^2+(V x)^2)/2 := by
           nlinarith only [sq_nonneg (|U x| - |V x|),sq_abs (U x),sq_abs (V x)]
         change |x^n*U x*V x*(1-logMean x)| ≤ (D U x+D V x)*(1/2)
         simp only [abs_mul,abs_of_nonneg hpow,abs_of_nonneg (sub_nonneg.mpr hm.2)]
         calc _ ≤ x^n*(|U x| * |V x|)*(1-x) := by
                rw [← mul_assoc (x^n) |U x| |V x|]
                exact mul_le_mul_of_nonneg_left (sub_le_sub_left hm.1 _) (by positivity)
              _ ≤ x^n*(((U x)^2+(V x)^2)/2)*(1-x) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hpow) (sub_nonneg.mpr hx.2)
              _ = _ := by dsimp only [D]; ring
       _ = _ := by
         rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_add
           (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _),← h₁,← h₂]
         ring

#print axioms prefixDefectCurvature_moment
#print axioms prefix_defect_between_weil_metrics
#print axioms prefix_mixed_defect_le_weil_energies
end GaloisForLFunctions.SignedArithmeticCorrespondences
