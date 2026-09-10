import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingTransform
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalBoundary

/-!
# Mean residue and spectral boundary of the actual theta response

Multiply the continued horizontal source symbol by the entire transform of the
actual common-forcing response. A single two-sided admitted tilt bounds that
response throughout the contour strip. The horizontal source decay therefore
supplies both integrable vertical sides and vanishing horizontal edges.

The only pole crossed from `Re z = 1/4` to `Re z = -1` is the mean pole. Its residue
is `mainTerm * xi(3/2) / (1 + alpha_q^2)`. The complete boundary value retains
`XiC(t) * (1 + boundaryPhase(t)) * profileTransform(q,t)`.

The main theorem is a closed source-specific contour identity at every actual Xi
copy. Identifying its right contour with the literal native height pairing still
requires the Plancherel and logarithmic-substitution join.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate FourierTransform
namespace RHTower.SelbergThetaNativeContour
noncomputable section
open SelbergThetaCommonForcing SelbergThetaCommonForcingTransform SelbergThetaHorizontalBoundary

private theorem norm_twist (q : XiZeroCopy) (w : ℂ) (x : ℝ) :
    ‖profile q x*Complex.exp (-I*w*(x:ℂ))‖ = ‖profile q x‖*Real.exp (w.im*x) := by
  rw [norm_mul,Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.mul_im]

private theorem norm_tiltedProfile (q : XiZeroCopy) (a x : ℝ) :
    ‖tiltedProfile q a x‖ = ‖profile q x‖*Real.exp (a*x) := by
  rw [tiltedProfile,norm_mul,Complex.norm_exp]
  congr 2
  simp

/-- A single admitted two-sided tilt controls the entire response on the whole contour strip. -/
theorem profileTransform_strip_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ 2 → ‖profileTransform q w‖ ≤ C := by
  let g : ℝ → ℝ := fun x => ‖tiltedProfile q 2 x‖+‖tiltedProfile q (-2) x‖
  have hg : Integrable g := (tiltedProfile_integrable q 2).norm.add
    (tiltedProfile_integrable q (-2)).norm
  refine ⟨∫ x, g x,integral_nonneg (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro w hw
  have hi := abs_le.mp hw
  calc ‖profileTransform q w‖ ≤ ∫ x, ‖profile q x*Complex.exp (-I*w*(x:ℂ))‖ := norm_integral_le_integral_norm _
       _ ≤ ∫ x, g x := by
         apply integral_mono (profile_integrable q w).norm hg
         intro x
         dsimp only
         rw [norm_twist]
         dsimp only [g]
         rw [norm_tiltedProfile,norm_tiltedProfile]
         rcases le_or_gt 0 x with hx | hx
         · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hi.2 hx)
           have hh := mul_le_mul_of_nonneg_left he (norm_nonneg (profile q x))
           exact hh.trans (le_add_of_nonneg_right (by positivity))
         · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hi.1 hx.le)
           have hh := mul_le_mul_of_nonneg_left he (norm_nonneg (profile q x))
           exact hh.trans (le_add_of_nonneg_left (by positivity))

/-- The pole-cleared horizontal symbol multiplied by the actual entire response transform. -/
def responseNumerator (q : XiZeroCopy) (z : ℂ) : ℂ :=
  poleNumerator z*profileTransform q (-I*(z+1))

/-- The complete source-response contour integrand. -/
def responseSymbol (q : XiZeroCopy) (z : ℂ) : ℂ := responseNumerator q z/z

/-- No additional spectral pole occurs after multiplication by the actual entire response. -/
theorem responseNumerator_analytic (q : XiZeroCopy) {z : ℂ} (hz : -1 ≤ z.re) :
    AnalyticAt ℂ (responseNumerator q) z := by
  apply (poleNumerator_analytic hz).mul
  exact (profileTransform_analytic q _ (mem_univ _)).comp (by fun_prop)

/-- The combined contour integrand is analytic off the mean pole. -/
theorem responseSymbol_analytic (q : XiZeroCopy) {z : ℂ} (hz : -1 ≤ z.re) (hn : z ≠ 0) :
    AnalyticAt ℂ (responseSymbol q) z :=
  (responseNumerator_analytic q hz).div analyticAt_id hn

/-- Exact product of the source symbol and the literal response transform. -/
theorem responseSymbol_eq_product (q : XiZeroCopy) (z : ℂ) :
    responseSymbol q z = symbol z*profileTransform q (-I*(z+1)) := by
  unfold responseSymbol responseNumerator symbol
  ring

/-- Uniform decay for the combined source-response integrand on the full contour strip. -/
theorem responseSymbol_decay (q : XiZeroCopy) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ z : ℂ,
      -1 ≤ z.re → z.re ≤ 1/4 → 2 ≤ |z.im| →
      ‖responseSymbol q z‖ ≤ C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4)) := by
  obtain ⟨K,hK,hp⟩ := profileTransform_strip_bound q
  obtain ⟨C,N,hC,hx⟩ := xi_strip_decay
  refine ⟨4*C*K,N,by positivity,?_⟩
  intro z hlo hhi ht
  have hw : |(-I*(z+1)).im| ≤ 2 := by
    have he : (-I*(z+1)).im = -(z.re+1) := by simp [Complex.mul_im]
    rw [he,abs_neg,abs_le]
    constructor <;> linarith
  have hi : ‖xi (z+3/2)‖ ≤ C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4)) := by
    simpa using hx (z+3/2) (by simp; linarith) (by simp; linarith) (by simpa using ht)
  rw [responseSymbol_eq_product,norm_mul]
  calc _ ≤ (4*‖xi (z+3/2)‖)*K :=
           mul_le_mul (norm_symbol_le hlo (by linarith)) (hp _ hw) (norm_nonneg _) (by positivity)
       _ ≤ (4*(C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4))))*K := by gcongr
       _ = _ := by ring

/-- Subtracting the exact mean principal part leaves a bounded local remainder. -/
theorem responseSymbol_pole (q : XiZeroCopy) :
    ((responseSymbol q)-fun z => responseNumerator q 0/(z-0))
      =O[nhdsWithin 0 {0}ᶜ] (1:ℂ → ℂ) := by
  have h : slope (responseNumerator q) 0 =O[nhdsWithin 0 {0}ᶜ] (1:ℂ → ℂ) :=
    (responseNumerator_analytic q (z := 0) (by norm_num)).differentiableAt.hasDerivAt.tendsto_slope.isBigO_one ℂ
  have he : ((responseSymbol q)-fun z => responseNumerator q 0/(z-0)) =
      slope (responseNumerator q) 0 := by
    ext z
    simp only [Pi.sub_apply,responseSymbol,slope,sub_zero,smul_eq_mul,vsub_eq_sub]
    ring
  rw [he]
  exact h

private theorem bound_integrable (C : ℝ) (N : ℕ) :
    Integrable (fun t : ℝ => C*|t|^N*Real.exp (-(Real.pi*|t|/4))) := by
  have h := (integrable_abs_pow_mul_exp_neg_mul_abs N
    (c := Real.pi/4) (by positivity)).const_mul C
  have he (t : ℝ) : -(Real.pi*|t|/4) = -(Real.pi/4)*|t| := by ring
  simpa only [he,mul_assoc] using h

/-- Absolute convergence on each vertical line in the strip away from the mean pole. -/
theorem responseSymbol_line_integrable (q : XiZeroCopy) {c : ℝ}
    (hc : -1 ≤ c) (hc' : c ≤ 1/4) (hn : c ≠ 0) :
    Integrable (fun t : ℝ => responseSymbol q ((c:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨C,N,hC,hb⟩ := responseSymbol_decay q
  have ht : Continuous (fun t : ℝ => responseSymbol q ((c:ℂ)+(t:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz : ((c:ℂ)+(t:ℂ)*I:ℂ) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact hn hr
    have hline : Continuous (fun t : ℝ => (c:ℂ)+(t:ℂ)*I) := by fun_prop
    have hout : ContinuousAt (responseSymbol q) ((c:ℂ)+(t:ℂ)*I) :=
      (responseSymbol_analytic q (z := (c:ℂ)+(t:ℂ)*I) (by simpa using hc) hz).continuousAt
    exact hout.comp (f := fun t : ℝ => (c:ℂ)+(t:ℂ)*I) (x := t) hline.continuousAt
  have hm : IntegrableOn (fun t : ℝ => responseSymbol q ((c:ℂ)+(t:ℂ)*I)) (Icc (-2:ℝ) 2) :=
    ht.continuousOn.integrableOn_compact isCompact_Icc
  have ho : IntegrableOn (fun t : ℝ => responseSymbol q ((c:ℂ)+(t:ℂ)*I)) (Icc (-2:ℝ) 2)ᶜ := by
    apply (bound_integrable C N).integrableOn.mono' ht.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    have ha : 2 ≤ |t| := by
      by_contra hn
      apply ht
      have hh := abs_lt.mp (lt_of_not_ge hn)
      exact ⟨hh.1.le,hh.2.le⟩
    simpa using hb ((c:ℂ)+(t:ℂ)*I) (by simpa using hc) (by simpa using hc') (by simpa using ha)
  rw [← integrableOn_univ,← union_compl_self (Icc (-2:ℝ) 2)]
  exact hm.union ho

private theorem bound_tendsto_zero (C : ℝ) (N : ℕ) :
    Tendsto (fun t : ℝ => C*t^N*Real.exp (-(Real.pi*t/4))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (N:ℝ) (Real.pi/4) (by positivity)).const_mul C
  have he (t : ℝ) : -(Real.pi*t/4) = -(Real.pi/4)*t := by ring
  simpa only [he,Real.rpow_natCast,mul_assoc,mul_zero] using h

private theorem responseSymbol_horizontal_limit (q : XiZeroCopy) {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => ∫ x in (-1:ℝ)..(1/4:ℝ),
      responseSymbol q ((x:ℂ)+(t:ℂ)*I)) l (𝓝 0) := by
  obtain ⟨C,N,hC,hb⟩ := responseSymbol_decay q
  have hB : Tendsto (fun t : ℝ =>
      (C*|t|^N*Real.exp (-(Real.pi*|t|/4)))*|(1/4:ℝ)-(-1)|) l (𝓝 0) := by
    simpa only [mul_zero,zero_mul,Function.comp_apply] using
      ((bound_tendsto_zero C N).comp hl).mul_const |(1/4:ℝ)-(-1)|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hB
  filter_upwards [hl.eventually (eventually_ge_atTop (2:ℝ))] with t ht
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
    rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1/4)] at hx
    simpa using hb ((x:ℂ)+(t:ℂ)*I) (by simpa using hx.1.le)
      (by simpa using hx.2) (by simpa using ht))

/-- The admitted rectangle shift crosses precisely the source mean pole. -/
theorem responseSymbol_contour_shift (q : XiZeroCopy) :
    VerticalIntegral' (responseSymbol q) (1/4) - VerticalIntegral' (responseSymbol q) (-1) =
      responseNumerator q 0 := by
  apply GaloisForLFunctions.HTGeometry.verticalIntegral'_sub_of_simple_pole
    (p := (0:ℂ)) (by norm_num) (by norm_num)
  · intro z hz
    have hm := hz.1
    rw [Complex.mem_reProdIm] at hm
    exact (responseSymbol_analytic q hm.1.1 (by simpa using hz.2)).differentiableAt.differentiableWithinAt
  · exact responseSymbol_pole q
  · exact responseSymbol_horizontal_limit q tendsto_abs_atBot_atTop
  · exact responseSymbol_horizontal_limit q tendsto_abs_atTop_atTop
  · exact responseSymbol_line_integrable q (by norm_num) (by norm_num) (by norm_num)
  · exact responseSymbol_line_integrable q (by norm_num) (by norm_num) (by norm_num)


/-- The crossed residue has an explicit entire-Xi value and the original mean denominator. -/
theorem responseNumerator_zero (q : XiZeroCopy) :
    responseNumerator q 0 = mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2) := by
  have h := profile_transform_equation q (-I)
  have he : XiC (-I) = xi (3/2) := by
    unfold XiC
    congr 1
    linear_combination -I_sq
  have hs : (xiSpectralPoint q)^2-(-I)^2 = 1+(xiSpectralPoint q)^2 := by
    rw [neg_sq,I_sq]
    ring
  rw [he,hs] at h
  have hp : profileTransform q (-I) = xi (3/2)/(1+(xiSpectralPoint q)^2) := by
    apply (eq_div_iff (mean_denominator_ne_zero q)).2
    rw [mul_comm]
    exact h
  simp only [responseNumerator,zero_add,mul_one,hp,mainTerm]
  ring

/-- The full arithmetic spectral boundary of the combined source-response symbol. -/
theorem responseSymbol_boundary (q : XiZeroCopy) (t : ℝ) :
    responseSymbol q (-1+(t:ℂ)*I) =
      XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ) := by
  rw [responseSymbol_eq_product,symbol_boundary]
  have he : -I*((-1+(t:ℂ)*I)+1) = (t:ℂ) := by
    linear_combination -(t:ℂ)*I_sq
  rw [he]

/-- The displayed complete spectral-boundary integral converges absolutely. -/
theorem responseSymbol_boundary_integrable (q : XiZeroCopy) :
    Integrable (fun t : ℝ => XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ)) := by
  simpa only [Complex.ofReal_neg,Complex.ofReal_one,responseSymbol_boundary] using
    responseSymbol_line_integrable q (c := (-1:ℝ)) (by norm_num) (by norm_num) (by norm_num)

/-- The right source-response contour equals its mean residue and its full arithmetic spectral boundary. -/
theorem responseSymbol_spectral_boundary (q : XiZeroCopy) :
    VerticalIntegral' (responseSymbol q) (1/4) =
      mainTerm*xi (3/2)/(1+(xiSpectralPoint q)^2)+
      (1/(2*(Real.pi:ℂ)))*∫ t : ℝ,
        XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ) := by
  have h := responseSymbol_contour_shift q
  rw [responseNumerator_zero] at h
  have hb : VerticalIntegral' (responseSymbol q) (-1) =
      (1/(2*(Real.pi:ℂ)))*∫ t : ℝ,
        XiC (t:ℂ)*(1+boundaryPhase t)*profileTransform q (t:ℂ) := by
    simp only [VerticalIntegral',VerticalIntegral,smul_eq_mul,Complex.ofReal_neg,Complex.ofReal_one]
    have he : (1/(2*(Real.pi:ℂ)*I))*I = 1/(2*(Real.pi:ℂ)) := by field_simp
    rw [← mul_assoc,he]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => responseSymbol_boundary q t)
  rw [hb] at h
  linear_combination h

end
end RHTower.SelbergThetaNativeContour
