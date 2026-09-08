import GaloisForLFunctions.RHTower.DivisorSourceEntire
import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadMoment

/-!
# Integrable paired Mellin boundary of the finite processed divisor source

The literal coefficient continuation and finite prime multiplier define
the paired kernel for the distant-head contour. Divided differences fill
the square-root pole. The whole imaginary boundary, after its possible
constant-term pole is removed, is absolutely integrable. The coefficient
of that pole is identified with the signed source at negative one half,
the explicit real prime factors, and the actual positive source moment.
No physical contour shift or distant-head mean limit is asserted here.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
namespace RHTower

/-- Literal finite prime-dilation multiplier in logarithmic coordinates. -/
def divisorCoreMellinEuler (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∏p∈P, (1-Complex.exp ((1/2-s)*(Real.log p : ℂ)))

/-- The finite source multiplier is entire. -/
theorem differentiable_divisorCoreMellinEuler (P : Finset ℕ) :
    Differentiable ℂ (divisorCoreMellinEuler P) := by
  intro s
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  fun_prop

/-- Any processed prime removes the common square-root Mellin pole. -/
theorem divisorCoreMellinEuler_half (P : Finset ℕ) (hP : P.Nonempty) :
    divisorCoreMellinEuler P (1/2)=0 := by
  obtain ⟨p,hp⟩ := hP
  apply Finset.prod_eq_zero hp
  simp

/-- Entire numerator after filling the square-root pole. -/
def divisorCoreMellinNumerator (P : Finset ℕ) (s : ℂ) : ℂ :=
  divisorSourceEntire (s-1/2)*dslope (divisorCoreMellinEuler P) (1/2) s/2

/-- The filled numerator introduces no source singularities. -/
theorem differentiable_divisorCoreMellinNumerator (P : Finset ℕ) :
    Differentiable ℂ (divisorCoreMellinNumerator P) := by
  have he : Differentiable ℂ (dslope (divisorCoreMellinEuler P) (1/2)) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ)∈𝓝 (1/2:ℂ))).mpr
      (differentiable_divisorCoreMellinEuler P).differentiableOn
  exact ((differentiable_divisorSourceEntire.comp (differentiable_id.sub_const (1/2))).mul he).div_const 2

/-- Processed source Mellin continuation, with the constant-term pole retained. -/
def divisorCoreMellin (P : Finset ℕ) (s : ℂ) : ℂ := divisorCoreMellinNumerator P s/s

/-- Off the two explicit denominator points the continuation has exactly the
finite source's Euler multiplier and summatory Mellin normalization. -/
theorem divisorCoreMellin_eq (P : Finset ℕ) (hP : P.Nonempty) {s : ℂ} (hs : s ≠ 1/2) :
    divisorCoreMellin P s = divisorSourceEntire (s-1/2)*divisorCoreMellinEuler P s /
      (2*s*(s-1/2)) := by
  rw [divisorCoreMellin,divisorCoreMellinNumerator,dslope_of_ne _ hs,slope_def_field,
    divisorCoreMellinEuler_half P hP]
  simp only [sub_zero, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact numerator of the constant-term pole; its sign is not postulated. -/
theorem divisorCoreMellinNumerator_zero (P : Finset ℕ) (hP : P.Nonempty) :
    divisorCoreMellinNumerator P 0 = -divisorSourceEntire (-1/2)*divisorCoreMellinEuler P 0 := by
  rw [divisorCoreMellinNumerator,dslope_of_ne _ (by norm_num : (0:ℂ) ≠ 1/2),
    slope_def_field,divisorCoreMellinEuler_half P hP]
  ring

private lemma core_euler_bound (P : Finset ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖divisorCoreMellinEuler P s‖  ≤  ∏p∈P, (1+Real.exp (Real.log p/2)) := by
  rw [divisorCoreMellinEuler,norm_prod]
  apply prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  have hlog := Real.log_natCast_nonneg p
  calc
    _  ≤  ‖(1:ℂ)‖+‖Complex.exp ((1/2-s)*(Real.log p : ℂ))‖ := norm_sub_le _ _
    _ = 1+Real.exp ((1/2-s.re)*Real.log p) := by
      simp only [norm_one, norm_exp, mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      norm_num
    _  ≤  _ := by
      gcongr
      nlinarith

/-- The paired literal source in the proposed contour for the signed dilation average. -/
def divisorCoreMellinPair (P : Finset ℕ) (s : ℂ) : ℂ :=
  divisorCoreMellin P s*divisorCoreMellin P (2-s)

private lemma imaginary_ne (t : ℝ) : (t:ℂ)*I ≠ (1/2:ℂ) := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- Quadratic tail decay of the literal paired Mellin source on Re(s)=0.
The reflected zeta derivative is included, with no source-growth premise. -/
theorem exists_bound_divisorCoreMellinPair_boundary
    (P : Finset ℕ) (hP : P.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀t : ℝ, 3 ≤ |t| →
      ‖divisorCoreMellinPair P ((t:ℂ)*I)‖  ≤  C/(1+t^2) := by
  obtain ⟨L,hL,hleft⟩ := exists_bound_divisorSourceEntire_negative_half
  obtain ⟨R,hR,hright⟩ := exists_bound_divisorSourceEntire_right
  let D : ℝ := ∏p∈P, (1+Real.exp (Real.log p/2))
  have hD : 0 ≤ D := prod_nonneg (fun p hp => by positivity)
  refine ⟨2*L*R*D^2,by positivity,?_⟩
  intro t ht
  let s : ℂ := (t:ℂ)*I
  have ht0 : 0 < |t| := by linarith
  have hsq : 0 < t^2 := by nlinarith [sq_abs t]
  have hsH : s ≠ 1/2 := imaginary_ne t
  have hs2H : 2-s ≠ 1/2 := by intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hden0 : 0 < ‖2*s*(s-1/2)‖ := by
    apply norm_pos_iff.mpr
    have hs0 : s ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [s] at him
      norm_num [him] at ht
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hsH)
  have hden2 : 0 < ‖2*(2-s)*(2-s-1/2)‖ := by
    apply norm_pos_iff.mpr
    have hs20 : 2-s ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num [s] at this
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs20) (sub_ne_zero.mpr hs2H)
  have hn (a : ℝ) : |t| ≤ ‖(a:ℂ)-s‖ := by
    simpa [s] using Complex.abs_im_le_norm ((a:ℂ)-s)
  have hn0 : |t| ≤ ‖s‖ := by simp [s]
  have hnH : |t| ≤ ‖s-1/2‖ := by simpa [s] using Complex.abs_im_le_norm (s-1/2)
  have hn2 : |t| ≤ ‖2-s‖ := by simpa using hn 2
  have hn2H : |t| ≤ ‖2-s-1/2‖ := by
    simpa [s] using Complex.abs_im_le_norm (2-s-1/2)
  have hd0 : 2*t^2 ≤ ‖2*s*(s-1/2)‖ := by
    rw [norm_mul,norm_mul,Complex.norm_ofNat]
    nlinarith [mul_le_mul hn0 hnH (abs_nonneg t) (norm_nonneg _),sq_abs t]
  have hd2 : 2*t^2 ≤ ‖2*(2-s)*(2-s-1/2)‖ := by
    rw [norm_mul,norm_mul,Complex.norm_ofNat]
    nlinarith [mul_le_mul hn2 hn2H (abs_nonneg t) (norm_nonneg _),sq_abs t]
  have he0 : ‖divisorCoreMellinEuler P s‖ ≤ D := core_euler_bound P (by simp [s])
  have he2 : ‖divisorCoreMellinEuler P (2-s)‖ ≤ D := core_euler_bound P (by norm_num [s])
  have hl : ‖divisorSourceEntire (s-1/2)‖ ≤ L*(1+|t|)^2 := by
    have he : s-1/2=(-1/2:ℂ)+(t:ℂ)*I := by dsimp [s]; ring
    rw [he]
    exact hleft t ht
  have hr : ‖divisorSourceEntire (2-s-1/2)‖ ≤ R := hright _ (by norm_num [s])
  have hf0 : ‖divisorCoreMellin P s‖ ≤ (L*(1+|t|)^2*D)/(2*t^2) := by
    rw [divisorCoreMellin_eq P hP hsH,norm_div,norm_mul]
    exact div_le_div₀ (mul_nonneg (by positivity) hD)
      (mul_le_mul hl he0 (norm_nonneg _) (by positivity)) (by positivity) hd0
  have hf2 : ‖divisorCoreMellin P (2-s)‖ ≤ (R*D)/(2*t^2) := by
    rw [divisorCoreMellin_eq P hP hs2H,norm_div,norm_mul]
    exact div_le_div₀ (mul_nonneg hR hD)
      (mul_le_mul hr he2 (norm_nonneg _) hR) (by positivity) hd2
  have hquad : (1+|t|)^2 ≤ 4*t^2 := by nlinarith [sq_abs t]
  have hf0' : ‖divisorCoreMellin P s‖ ≤ 2*L*D := by
    apply hf0.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*t^2)).mpr
    nlinarith [mul_nonneg (mul_nonneg hL hD) (sub_nonneg.mpr hquad)]
  rw [divisorCoreMellinPair,norm_mul]
  calc
    _ ≤ (2*L*D)*((R*D)/(2*t^2)) :=
      mul_le_mul hf0' hf2 (norm_nonneg _) (by positivity)
    _ = (L*R*D^2)/t^2 := by field_simp
    _ ≤ _ := by
      rw [div_le_div_iff₀ hsq (by positivity : (0:ℝ)<1+t^2)]
      have hh : 0 ≤ L*R*D^2 := by positivity
      nlinarith [mul_nonneg hh (show 0 ≤ t^2-1 by nlinarith [sq_abs t])]

private def corePairNumerator (P : Finset ℕ) (s : ℂ) : ℂ :=
  divisorCoreMellinNumerator P s*divisorCoreMellinNumerator P (2-s)/(2-s)

/-- Exact pole coefficient of the paired source at zero. -/
def divisorCoreMellinPairResidue (P : Finset ℕ) : ℂ := corePairNumerator P 0

/-- Boundary remainder with the pole removed by a quadratically decaying rational term. -/
def divisorCoreMellinPairRegular (P : Finset ℕ) (s : ℂ) : ℂ :=
  dslope (corePairNumerator P) 0 s + divisorCoreMellinPairResidue P/(1+s)

private lemma corePairNumerator_diff (P : Finset ℕ) {s : ℂ} (hs : s ≠ 2) :
    DifferentiableAt ℂ (corePairNumerator P) s := by
  have hn := differentiable_divisorCoreMellinNumerator P
  have hc : Differentiable ℂ (fun z => divisorCoreMellinNumerator P (2-z)) :=
    hn.comp ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact ((hn s).mul (hc s)).div ((differentiableAt_const (2:ℂ)).sub differentiableAt_id)
    (sub_ne_zero.mpr hs.symm)

/-- The actual pole coefficient retains the signed source value at -1/2
and the positive-moment companion; no residue sign is assumed. -/
theorem divisorCoreMellinPairResidue_eq (P : Finset ℕ) (hP : P.Nonempty) :
    divisorCoreMellinPairResidue P = -divisorSourceEntire (-1/2)*
      divisorCoreMellinEuler P 0*divisorCoreMellin P 2 := by
  rw [divisorCoreMellinPairResidue,corePairNumerator,
    divisorCoreMellinNumerator_zero P hP,divisorCoreMellin]
  ring

/-- Exact pole removal, including the correction that preserves quadratic tail decay. -/
theorem divisorCoreMellinPairRegular_eq (P : Finset ℕ) {s : ℂ}
    (hs : s ≠ 0) (hs1 : 1+s ≠ 0) :
    divisorCoreMellinPairRegular P s = divisorCoreMellinPair P s -
      divisorCoreMellinPairResidue P/(s*(1+s)) := by
  rw [divisorCoreMellinPairRegular,dslope_of_ne _ hs,slope_def_field]
  have he : corePairNumerator P s/s=divisorCoreMellinPair P s := by
    simp only [corePairNumerator,divisorCoreMellinPair,divisorCoreMellin,
      div_eq_mul_inv]
    ring
  rw [← he]
  change (corePairNumerator P s-divisorCoreMellinPairResidue P)/(s-0)+
    divisorCoreMellinPairResidue P/(1+s) = _
  field_simp
  ring

/-- The pole-subtracted paired source is continuous on its whole imaginary boundary. -/
theorem continuous_divisorCoreMellinPairRegular_boundary (P : Finset ℕ) :
    Continuous (fun t : ℝ => divisorCoreMellinPairRegular P ((t:ℂ)*I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h2 : (t:ℂ)*I ≠ 2 := by intro h; have := congrArg Complex.re h; norm_num at this
  have h1 : 1+(t:ℂ)*I ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num at this
  have hd : ContinuousAt (dslope (corePairNumerator P) 0) ((t:ℂ)*I) := by
    by_cases h0 : (t:ℂ)*I=0
    · rw [h0]
      exact continuousAt_dslope_same.mpr (corePairNumerator_diff P (by norm_num))
    · exact (continuousAt_dslope_of_ne h0).mpr (corePairNumerator_diff P h2).continuousAt
  have ha : ContinuousAt (fun s : ℂ => divisorCoreMellinPairResidue P/(1+s)) ((t:ℂ)*I) :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) h1
  have hp : ContinuousAt (fun u : ℝ => (u:ℂ)*I) t := by fun_prop
  exact ContinuousAt.comp (f := fun u : ℝ => (u:ℂ)*I) (hd.add ha) hp

private lemma regular_boundary_tail (P : Finset ℕ) (hP : P.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀t : ℝ, 3 ≤ |t| →
      ‖divisorCoreMellinPairRegular P ((t:ℂ)*I)‖ ≤ C/(1+t^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_divisorCoreMellinPair_boundary P hP
  refine ⟨C+2*‖divisorCoreMellinPairResidue P‖,by positivity,?_⟩
  intro t ht
  let s : ℂ := (t:ℂ)*I
  have hs : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [s] at him
    norm_num [him] at ht
  have hs1 : 1+s ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hsq : 0 < t^2 := by nlinarith [sq_abs t]
  have ht1 : 1 ≤ t^2 := by nlinarith [sq_abs t]
  have hd : t^2 ≤ ‖s*(1+s)‖ := by
    have h1 : |t| ≤ ‖1+s‖ := by simpa [s] using Complex.abs_im_le_norm (1+s)
    rw [norm_mul]
    have h0 : ‖s‖=|t| := by simp [s]
    rw [h0]
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg t),sq_abs t]
  have hr : ‖divisorCoreMellinPairResidue P/(s*(1+s))‖ ≤
      (2*‖divisorCoreMellinPairResidue P‖)/(1+t^2) := by
    rw [norm_div]
    apply (div_le_div_of_nonneg_left (norm_nonneg _) hsq hd).trans
    rw [div_le_div_iff₀ hsq (by positivity : (0:ℝ)<1+t^2)]
    nlinarith [mul_nonneg (norm_nonneg (divisorCoreMellinPairResidue P)) (sub_nonneg.mpr ht1)]
  rw [divisorCoreMellinPairRegular_eq P hs hs1]
  exact (norm_sub_le _ _).trans (by have := hbound t ht; dsimp [s] at *; rw [add_div]; linarith)

/-- Absolute integrability of the entire pole-subtracted paired boundary.
The local pole is removed analytically and the full remote tail is controlled. -/
theorem integrable_divisorCoreMellinPairRegular_boundary (P : Finset ℕ) (hP : P.Nonempty) :
    Integrable (fun t : ℝ => divisorCoreMellinPairRegular P ((t:ℂ)*I)) := by
  let f : ℝ→ℂ := fun t => divisorCoreMellinPairRegular P ((t:ℂ)*I)
  have hf : Continuous f := continuous_divisorCoreMellinPairRegular_boundary P
  obtain ⟨C,hC,hfar⟩ := regular_boundary_tail P hP
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := (-3:ℝ)) (b := 3)).exists_bound_of_continuousOn hf.continuousOn
  let K : ℝ := C+10*max B 0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (t : ℝ) : ‖f t‖ ≤ K*(1+t^2)⁻¹ := by
    rw [← div_eq_mul_inv]
    by_cases ht : |t| ≤ 3
    · have hB' := hB t (abs_le.mp ht)
      have hs : 1+t^2 ≤ 10 := by nlinarith [mul_self_le_mul_self (abs_nonneg t) ht, sq_abs t]
      apply hB'.trans
      apply (le_div_iff₀ (by positivity : (0:ℝ)<1+t^2)).mpr
      have hm : B*(1+t^2) ≤ (max B 0)*(1+t^2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      dsimp [K]
      nlinarith [mul_nonneg (le_max_right B 0) (sub_nonneg.mpr hs)]
    · apply (hfar t (le_of_not_ge ht)).trans
      exact div_le_div_of_nonneg_right (by dsimp [K]; exact le_add_of_nonneg_right (by positivity)) (by positivity)
  exact (integrable_inv_one_add_sq.const_mul K).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

private lemma source_three_halves_real : ∃ r : ℝ, divisorSourceEntire (3/2)=(r:ℂ) := by
  let r : ℝ := ∑' n : ℕ, if n=0 then 0 else primeFreeDivisorIncrement n/(n:ℝ)^(3/2:ℝ)
  refine ⟨r,?_⟩
  rw [divisorSourceEntire_eq_LSeries (by norm_num), LSeries]
  dsimp [r]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn,if_neg hn,Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_num

private lemma source_three_halves_moment :
    divisorSourceEntire (3/2) =
      (6*(∫ x in Set.Ioi (0:ℝ), divisorContinuousUnitHead x/x^3) : ℝ) := by
  obtain ⟨r,hr⟩ := source_three_halves_real
  have h := integral_divisorContinuousUnitHead_moment
  rw [← divisorSourceEntire_eq_LSeries (by norm_num),hr,Complex.ofReal_re] at h
  rw [hr]
  congr 1
  linarith

private lemma core_euler_real (P : Finset ℕ) (σ : ℝ) :
    divisorCoreMellinEuler P (σ:ℂ) =
      ((∏ p∈P, (1-Real.exp ((1/2-σ)*Real.log p)) : ℝ):ℂ) := by
  rw [divisorCoreMellinEuler,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_exp]
  congr 2
  push_cast
  ring

private lemma core_euler_two (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    divisorCoreMellinEuler P 2 = ((∏p∈P, (1-Real.sqrt p/(p:ℝ)^2) : ℝ):ℂ) := by
  have he := core_euler_real P 2
  change divisorCoreMellinEuler P 2 = ((∏ p∈P, (1-Real.exp ((1/2-(2:ℝ))*Real.log p)) : ℝ):ℂ) at he
  rw [he]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  congr 1
  have hpR : (0:ℝ)<p := by exact_mod_cast (hP p hp).pos
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (p:ℝ) 2, ← Real.rpow_sub hpR,
    Real.rpow_def_of_pos hpR]
  congr 1
  ring

/-- The companion of the boundary pole is exactly the already proved strictly
positive signed moment of the literal processed head. -/
theorem divisorCoreMellin_two_eq_moment (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) :
    divisorCoreMellin P 2 =
      ((∫ x in Set.Ioi (0:ℝ), mobiusDivisorContinuousHead P x/x^3 : ℝ):ℂ) := by
  rw [divisorCoreMellin_eq P hP (by norm_num),
    integral_mobiusDivisorContinuousHead_moment P hprime,core_euler_two P hprime]
  norm_num
  rw [source_three_halves_moment]
  push_cast
  ring

/-- Exact signed residue of the paired source, with its positive physical
moment identified and its remaining arithmetic sign isolated. -/
theorem divisorCoreMellinPairResidue_eq_signed_moment (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) :
    divisorCoreMellinPairResidue P = -divisorSourceEntire (-1/2)*
      divisorCoreMellinEuler P 0*
        ((∫ x in Set.Ioi (0:ℝ), mobiusDivisorContinuousHead P x/x^3 : ℝ):ℂ) := by
  rw [divisorCoreMellinPairResidue_eq P hP,divisorCoreMellin_two_eq_moment P hP hprime]

/-- The paired kernel has the asserted possible simple-pole coefficient in
the full punctured complex neighborhood, not only on its imaginary trace. -/
theorem tendsto_mul_divisorCoreMellinPair_zero (P : Finset ℕ) :
    Tendsto (fun s : ℂ => s*divisorCoreMellinPair P s) (𝓝[≠] 0)
      (𝓝 (divisorCoreMellinPairResidue P)) := by
  have hg : Tendsto (corePairNumerator P) (𝓝 (0:ℂ)) (𝓝 (corePairNumerator P 0)) :=
    (corePairNumerator_diff P (by norm_num : (0:ℂ) ≠ 2)).continuousAt
  have h : Tendsto (corePairNumerator P) (𝓝[≠] (0:ℂ)) (𝓝 (corePairNumerator P 0)) :=
    hg.mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  rw [divisorCoreMellinPair,divisorCoreMellin,divisorCoreMellin,corePairNumerator]
  field_simp [hs0]

/-- Explicit real prime factors in the possible constant-term residue. -/
theorem divisorCoreMellinEuler_zero (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    divisorCoreMellinEuler P 0 = ((∏p∈P, (1-Real.sqrt p) : ℝ):ℂ) := by
  have he := core_euler_real P 0
  change divisorCoreMellinEuler P 0 = ((∏p∈P, (1-Real.exp ((1/2-(0:ℝ))*Real.log p)) : ℝ):ℂ) at he
  rw [he]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  congr 1
  have hpR : (0:ℝ)<p := by exact_mod_cast (hP p hp).pos
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hpR]
  congr 1
  ring

end RHTower
