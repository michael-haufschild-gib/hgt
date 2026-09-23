import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanRenewal

/-!
# Uniform ratio profile after a growing prime insertion

The source's integrable contour boundary bounds every dilation above one.
The exact renewal identity then has a remainder bounded independently of
the inserted prime and the next dilation. Continuity and the positive
diagonal pairing force a negative band at comparable scales, uniformly
as the inserted prime grows. The original core remains fixed.
-/

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology MeasureTheory Complex
namespace RHTower

private lemma boundary_norm (P : Finset ℕ) (a : ℝ) :
    ‖∫t : ℝ,Complex.exp ((a:ℂ)*(t:ℂ)*I)*divisorCoreMellinPairEntire P ((t:ℂ)*I)‖ ≤
      ∫t : ℝ,‖divisorCoreMellinPairEntire P ((t:ℂ)*I)‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with t
  rw [norm_mul,Complex.norm_exp]
  simp

/-- A single actual-source bound controls every dilation above one for a
fixed nonempty core; no rate of the distant-dilation limit is assumed. -/
theorem exists_bound_mobiusDivisorDilationMean (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀p∈P,p.Prime) :
    ∃B : ℝ, 0≤B ∧ ∀Y : ℝ, 1≤Y → |mobiusDivisorDilationMean P Y|≤B := by
  let B : ℝ := ‖divisorCoreMellinPairResidue P‖+
    ‖(1/(2*(Real.pi:ℂ)))‖*(∫t : ℝ,‖divisorCoreMellinPairEntire P ((t:ℂ)*I)‖)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro Y hY
  have hY0 : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have he := mobiusDivisorDilationMean_eq_contour P hP hprime (Real.log Y)
  rw [Real.exp_log hY0,divisorCoreMellinContourMean_eq_residue_add_boundary P hP
    (Real.log_nonneg hY)] at he
  calc
    _ = ‖(mobiusDivisorDilationMean P Y:ℂ)‖ := (Complex.norm_real _).symm
    _ ≤ B := by
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (boundary_norm P (Real.log Y)) (norm_nonneg (1/(2*(Real.pi:ℂ)))))

/-- Uniform control across an inserted prime and every next dilation.
The whole leading profile is the original physical mean at their ratio. -/
theorem exists_bound_mobiusDivisorDilationMean_insert_ratio (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀p∈P,p.Prime) :
    ∃C : ℝ, 0≤C ∧ ∀p : ℕ,p.Prime → p∉P → ∀Y : ℝ,1≤Y →
      |mobiusDivisorDilationMean (insert p P) Y+
        Real.sqrt p*mobiusDivisorDilationMean P (Y/p)|≤C := by
  obtain ⟨B,hB,hbound⟩ := exists_bound_mobiusDivisorDilationMean P hP hprime
  refine ⟨3*B,by positivity,?_⟩
  intro p hp hpP Y hY
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpY : 1≤(p:ℝ)*Y := by nlinarith
  have hdiv : (1:ℝ)/(p:ℝ)≤1 := (div_le_one hp0).mpr hp1
  have hs : Real.sqrt (p:ℝ)≤(p:ℝ)^(2 : ℕ) := by
    have hh := Real.sq_sqrt hp0.le
    have hp2 : (p:ℝ)≤(p:ℝ)^(2 : ℕ) := by nlinarith
    have hs1 : Real.sqrt (p:ℝ)≤(p:ℝ) := by nlinarith [Real.sqrt_nonneg (p:ℝ)]
    exact hs1.trans hp2
  have hcoef : Real.sqrt (p:ℝ)/(p:ℝ)^(2 : ℕ)≤1 := (div_le_one (pow_pos hp0 2)).mpr hs
  rw [mobiusDivisorDilationMean_insert P hprime hp hpP (lt_of_lt_of_le zero_lt_one hY)]
  rw [sub_add_cancel]
  calc
    _ ≤ |(1+1/(p:ℝ))*mobiusDivisorDilationMean P Y|+
        |Real.sqrt p/(p:ℝ)^(2 : ℕ)*mobiusDivisorDilationMean P ((p:ℝ)*Y)| := abs_sub _ _
    _ = (1+1/(p:ℝ))*|mobiusDivisorDilationMean P Y|+
        (Real.sqrt p/(p:ℝ)^(2 : ℕ))*|mobiusDivisorDilationMean P ((p:ℝ)*Y)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤1+1/(p:ℝ)),
        abs_of_nonneg (by positivity : 0≤Real.sqrt p/(p:ℝ)^(2 : ℕ))]
    _ ≤ (1+1/(p:ℝ))*B+(Real.sqrt p/(p:ℝ)^(2 : ℕ))*B :=
      add_le_add (mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity))
        (mul_le_mul_of_nonneg_left (hbound _ hpY) (by positivity))
    _ ≤ 3*B := by nlinarith [mul_le_mul_of_nonneg_right hdiv hB,
        mul_le_mul_of_nonneg_right hcoef hB]

private lemma oscillatory_continuous (f : ℝ→ℂ) (hf : Integrable f) :
    Continuous (fun a : ℝ => ∫t : ℝ,Complex.exp ((a:ℂ)*(t:ℂ)*I)*f t) := by
  apply continuous_of_dominated (bound := fun t => ‖f t‖)
  · intro a
    exact (show Continuous (fun t : ℝ => Complex.exp ((a:ℂ)*(t:ℂ)*I)) by fun_prop).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · intro a
    filter_upwards with t
    rw [norm_mul,Complex.norm_exp]
    simp
  · exact hf.norm
  · filter_upwards with t
    fun_prop

private lemma contour_continuous (P : Finset ℕ) (hP : P.Nonempty) :
    Continuous (divisorCoreMellinContourMean P) := by
  have hi := integrable_exp_mul_divisorCoreMellinPair_one P hP 0
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] at hi
  have hc := oscillatory_continuous _ hi
  have he : divisorCoreMellinContourMean P = fun a : ℝ =>
      (1/(2*(Real.pi:ℂ)))*Complex.exp (a:ℂ)*
        ∫t : ℝ,Complex.exp ((a:ℂ)*(t:ℂ)*I)*divisorCoreMellinPair P (1+(t:ℂ)*I) := by
    funext a
    rw [divisorCoreMellinContourMean,mul_assoc]
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [he]
  exact ((continuous_const.mul (Complex.continuous_exp.comp Complex.continuous_ofReal)).mul hc)

/-- The actual mean varies continuously at every positive ratio. -/
theorem continuousOn_mobiusDivisorDilationMean (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀p∈P,p.Prime) :
    ContinuousOn (mobiusDivisorDilationMean P) (Ioi 0) := by
  have hc := Complex.continuous_re.comp (contour_continuous P hP)
  have ht : ContinuousOn (fun Y : ℝ => (divisorCoreMellinContourMean P (Real.log Y)).re) (Ioi 0) :=
    hc.comp_continuousOn (Real.continuousOn_log.mono (fun Y hY => by
      simpa using ne_of_gt hY))
  apply ht.congr
  intro Y hY
  have he := congrArg Complex.re (mobiusDivisorDilationMean_eq_contour P hP hprime (Real.log Y))
  simpa only [Real.exp_log hY,Complex.ofReal_re] using he

/-- The diagonal physical pairing is strictly positive after every finite
prime core: a vanishing square norm would annihilate its positive moment. -/
theorem mobiusDivisorDilationMean_one_pos (P : Finset ℕ)
    (hprime : ∀p∈P,p.Prime) : 0 < mobiusDivisorDilationMean P 1 := by
  have hi := integrable_mobiusDivisorDilationMean_kernel P zero_lt_one
  simp only [one_mul] at hi
  have hn : ∀ᵐx ∂volume.restrict (Ioi (1:ℝ)),
      0 ≤ mobiusDivisorContinuousHead P x*mobiusDivisorContinuousHead P x/x^(3 : ℕ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := lt_trans zero_lt_one hx
    exact div_nonneg (mul_self_nonneg _) (by positivity)
  have hnon : 0 ≤ mobiusDivisorDilationMean P 1 := by
    simpa [mobiusDivisorDilationMean] using integral_nonneg_of_ae hn
  apply lt_of_le_of_ne hnon
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
    (by simpa [mobiusDivisorDilationMean] using hz.symm)
  have hm : (∫x in Ioi (1:ℝ),mobiusDivisorContinuousHead P x/x^(3 : ℕ))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he,ae_restrict_mem measurableSet_Ioi] with x hx hxx
    have hx0 : x≠0 := ne_of_gt (lt_trans zero_lt_one hxx)
    have hg : mobiusDivisorContinuousHead P x=0 := by
      have hmul := (div_eq_zero_iff).mp hx
      rcases hmul with h | h
      · rcases mul_eq_zero.mp h with h | h <;> exact h
      · exact False.elim ((pow_ne_zero _ hx0) h)
    simp [hg]
  rw [integral_mobiusDivisorContinuousHead_moment_Ioi_one] at hm
  exact (ne_of_gt (integral_mobiusDivisorContinuousHead_moment_pos P hprime)) hm

/-- Comparable next dilations have a uniformly negative physical mean
after a large prime is inserted. The interval and margin come from the
strict diagonal of the original source, rather than a distant-core limit. -/
theorem exists_mobiusDivisorDilationMean_insert_negative_band (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀p∈P,p.Prime) :
    ∃η c T : ℝ, 0<η ∧ 0<c ∧ ∀p : ℕ,p.Prime → p∉P → T≤(p:ℝ) →
      ∀Y : ℝ,(p:ℝ)≤Y → Y≤(1+η)*(p:ℝ) →
        mobiusDivisorDilationMean (insert p P) Y ≤ -c*Real.sqrt p := by
  have hw := mobiusDivisorDilationMean_one_pos P hprime
  have hc := (continuousOn_mobiusDivisorDilationMean P hP hprime).continuousAt
    (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  have he : ∀ᶠz : ℝ in 𝓝 1,
      mobiusDivisorDilationMean P 1/2 < mobiusDivisorDilationMean P z :=
    hc.eventually (eventually_gt_nhds (show mobiusDivisorDilationMean P 1/2 <
      mobiusDivisorDilationMean P 1 by linarith))
  obtain ⟨ε,hε,hεprop⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨C,hC,hbound⟩ := exists_bound_mobiusDivisorDilationMean_insert_ratio P hP hprime
  let c := mobiusDivisorDilationMean P 1/4
  have hc0 : 0<c := by dsimp [c]; linarith
  refine ⟨ε/2,c,(C/c+1)^(2 : ℕ),by positivity,hc0,?_⟩
  intro p hp hpP hpT Y hYlo hYhi
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hY1 : 1≤Y := hp1.trans hYlo
  have hzlo : 1≤Y/(p:ℝ) := (le_div_iff₀ hp0).mpr (by simpa using hYlo)
  have hzhi : Y/(p:ℝ)≤1+ε/2 := (div_le_iff₀ hp0).mpr hYhi
  have hdist : dist (Y/(p:ℝ)) 1<ε := by
    rw [Real.dist_eq,abs_of_nonneg (by linarith : 0≤Y/(p:ℝ)-1)]
    linarith
  have hwp := hεprop hdist
  have hmargin : C<c*Real.sqrt p := by
    have hb : 0≤C/c+1 := by positivity
    have hs := Real.sqrt_le_sqrt hpT
    rw [Real.sqrt_sq hb] at hs
    have heq : c*(C/c+1)=C+c := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hs hc0.le
    rw [heq] at hmul
    linarith
  have hcost := (abs_le.mp (hbound p hp hpP Y hY1)).2
  have hmul := mul_le_mul_of_nonneg_left hwp.le (Real.sqrt_nonneg (p:ℝ))
  dsimp [c] at hmargin ⊢
  nlinarith

end RHTower
