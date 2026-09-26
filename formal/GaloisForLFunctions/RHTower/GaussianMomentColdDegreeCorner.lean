import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureColdWatson

/-!
# The joint cold-aperture and degree boundary of a positive moment source

A positive even Gaussian-polynomial density has positive curvature at each fixed
degree for sufficiently cold aperture, and positive curvature uniformly at high
degree on every compact aperture interval. Its literal moment ratios obey the
same cooperative affine-Gamma flow as the completed theta source. Nevertheless,
its curvature is negative at an explicit aperture and along a cold/degree diagonal.

The positive survivor is an exact two-parameter sign classification and joint
limit. This excludes an inference from the two separate endpoint regimes. It
asserts no negative curvature for the actual theta source and no conclusion about RH.
-/

open Real MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.ColdDegreeCorner

def density (a x : ℝ) : ℝ := Real.exp (-x^2)*(1+a*x^6)
def moment (a c : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x^(2*j)*Real.exp (-c*x^2)*(1+a*x^6)
def denominator (a c A : ℝ) : ℝ := c^3+a*A*(A+1)*(A+2)
def ratio (a c A : ℝ) : ℝ := denominator a c (A+1)/(c*denominator a c A)
def curvature (a c A : ℝ) : ℝ := ratio a c A-2*ratio a c (A+1)+ratio a c (A+2)
def numerator (a c A : ℝ) : ℝ :=
  c^6-a*c^3*(A+2)*(A+3)*(7*A+13)+a^2*(A+1)*(A+2)^2*(A+3)^2*(A+4)

theorem density_pos {a : ℝ} (ha : 0≤a) (x : ℝ) : 0<density a x := by
  unfold density
  positivity

theorem density_even (a x : ℝ) : density a (-x)=density a x := by
  unfold density
  rw [neg_sq,show (-x)^6=x^6 by ring]

theorem moment_eq (a : ℝ) {c : ℝ} (hc : 0<c) (j : ℕ) :
    moment a c j = coldGaussianHalfMoment c j+a*coldGaussianHalfMoment c (j+3) := by
  have heq : (fun x : ℝ => x^(2*j)*Real.exp (-c*x^2)*(1+a*x^6)) =
      (fun x : ℝ => x^(2*j)*Real.exp (-c*x^2)+a*(x^(2*(j+3))*Real.exp (-c*x^2))) := by
    funext x
    rw [show 2*(j+3)=2*j+6 by omega,pow_add]
    ring
  unfold moment
  rw [heq,integral_add (integrableOn_coldGaussianHalfMoment hc j)
    ((integrableOn_coldGaussianHalfMoment hc (j+3)).const_mul a),integral_const_mul,
    integral_coldGaussianHalfMoment hc,integral_coldGaussianHalfMoment hc]

theorem moment_closed (a : ℝ) {c : ℝ} (hc : 0<c) (j : ℕ) :
    moment a c j = coldGaussianHalfMoment c j *
      denominator a c (thetaCuspGaussianApertureGammaShape j)/c^3 := by
  rw [moment_eq a hc,coldGaussianHalfMoment_add hc]
  simp only [coldGammaRising,Finset.prod_range_succ,Finset.prod_range_zero,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,add_zero,one_mul]
  unfold denominator
  field_simp

theorem denominator_pos {a c A : ℝ} (ha : 0≤a) (hc : 0<c) (hA : 0<A) :
    0<denominator a c A := by unfold denominator; positivity

theorem moment_pos {a c : ℝ} (ha : 0≤a) (hc : 0<c) (j : ℕ) : 0 < moment a c j := by
  rw [moment_closed a hc]
  exact div_pos (mul_pos (coldGaussianHalfMoment_pos hc j)
    (denominator_pos ha hc (thetaCuspGaussianApertureGammaShape_pos j))) (pow_pos hc 3)

theorem normalized_moment_ratio {a c : ℝ} (ha : 0≤a) (hc : 0<c) (j : ℕ) :
    (moment a c (j+1)/moment a c j)/thetaCuspGaussianApertureGammaShape j =
      ratio a c (thetaCuspGaussianApertureGammaShape j) := by
  rw [moment_closed a hc,moment_closed a hc,coldGaussianHalfMoment_succ hc,
    thetaCuspGaussianApertureGammaShape_add]
  have hG := (coldGaussianHalfMoment_pos hc j).ne'
  have hA := (thetaCuspGaussianApertureGammaShape_pos j).ne'
  have hD := (denominator_pos ha hc (thetaCuspGaussianApertureGammaShape_pos j)).ne'
  unfold ratio
  norm_num only [Nat.cast_one]
  field_simp

/-- Exact two-parameter curvature numerator. -/
theorem curvature_eq {a c A : ℝ} (ha : 0≤a) (hc : 0<c) (hA : 0<A) :
    curvature a c A = 6*a*numerator a c A /
      (c*denominator a c A*denominator a c (A+1)*denominator a c (A+2)) := by
  have h0 := (denominator_pos ha hc hA).ne'
  have h1 := (denominator_pos ha hc (show 0<A+1 by linarith)).ne'
  have h2 := (denominator_pos ha hc (show 0<A+2 by linarith)).ne'
  unfold curvature ratio
  rw [show A+1+1=A+2 by ring]
  field_simp
  unfold denominator numerator
  ring

/-- Sharp classification of the negative-curvature window. -/
theorem curvature_nonneg_iff {a c A : ℝ} (ha : 0<a) (hc : 0<c) (hA : 0<A) :
    0≤curvature a c A ↔
      (2*c^3/(a*(A+2)*(A+3))-(7*A+13))^2 ≥ 9*(5*A^2+18*A+17) := by
  rw [curvature_eq ha.le hc hA]
  have hD : 0<c*denominator a c A*denominator a c (A+1)*denominator a c (A+2) := by
    exact mul_pos (mul_pos (mul_pos hc (denominator_pos ha.le hc hA))
      (denominator_pos ha.le hc (by linarith))) (denominator_pos ha.le hc (by linarith))
  rw [le_div_iff₀ hD,zero_mul,mul_nonneg_iff_of_pos_left (show 0<6*a by positivity)]
  have hd : 0<a*(A+2)*(A+3) := by positivity
  have he : (2*c^3/(a*(A+2)*(A+3))-(7*A+13))^2-9*(5*A^2+18*A+17) =
      4*numerator a c A/(a*(A+2)*(A+3))^2 := by
    unfold numerator
    field_simp
    ring
  constructor
  · intro h
    have hp : 0≤4*numerator a c A/(a*(A+2)*(A+3))^2 :=
      div_nonneg (mul_nonneg (by norm_num) h) (sq_nonneg _)
    rw [← he] at hp
    linarith
  · intro h
    have hp : 0≤4*numerator a c A/(a*(A+2)*(A+3))^2 := by rw [← he]; linarith
    rw [le_div_iff₀ (sq_pos_of_pos hd),zero_mul] at hp
    linarith

def cornerProfile (a u e : ℝ) : ℝ :=
  6*a*(1-a*(u+2*e)*(u+3*e)*(7*u+13*e)+a^2*(u+e)*(u+2*e)^2*(u+3*e)^2*(u+4*e)) /
    ((1+a*u*(u+e)*(u+2*e))*(1+a*(u+e)*(u+2*e)*(u+3*e))*
      (1+a*(u+2*e)*(u+3*e)*(u+4*e)))

theorem scaled_corner_eq {a c u : ℝ} (ha : 0≤a) (hc : 0<c) (hu : 0<u) :
    c^4*curvature a c (c*u)=cornerProfile a u (1/c) := by
  rw [curvature_eq ha hc (mul_pos hc hu)]
  unfold cornerProfile numerator denominator
  field_simp
  ring

/-- The corner sign is a cubic logarithmic source jet, not either separate endpoint limit. -/
theorem tendsto_scaled_corner {a u : ℝ} (ha : 0≤a) (hu : 0<u) :
    Tendsto (fun c : ℝ => c^4*curvature a c (c*u)) atTop
      (𝓝 (6*a*(1-7*a*u^3+a^2*u^6)/(1+a*u^3)^3)) := by
  have hd : 0<1+a*u^3 := by positivity
  have hprof : ContinuousAt (cornerProfile a u) 0 := by
    unfold cornerProfile
    fun_prop (disch := positivity)
  have hh := hprof.tendsto.comp (show Tendsto (fun c : ℝ => 1/c) atTop (𝓝 0) from by simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0)))
  have hv : cornerProfile a u 0 = 6*a*(1-7*a*u^3+a^2*u^6)/(1+a*u^3)^3 := by
    unfold cornerProfile
    simp only [mul_zero,add_zero]
    congr 1 <;> ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
  exact (scaled_corner_eq ha hc hu).symm

/-- An exact negative interior aperture, with a strictly positive even density. -/
theorem curvature_exact_negative : curvature (64/105) 2 (1/2) = -7/40 := by
  norm_num [curvature,ratio,denominator]

/-- Gaussian damping of the stated positive source gives these literal moments. -/
theorem moment_eq_density_aperture (a lambda : ℝ) (j : ℕ) :
    moment a (1-lambda) j =
      ∫x : ℝ in Ioi 0, x^(2*j)*Real.exp (lambda*x^2)*density a x := by
  unfold moment density
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  have he : Real.exp (-(1-lambda)*x^2) = Real.exp (lambda*x^2)*Real.exp (-x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem ratio_pos {a c A : ℝ} (ha : 0≤a) (hc : 0<c) (hA : 0<A) :
    0<ratio a c A :=
  div_pos (denominator_pos ha hc (by linarith)) (mul_pos hc (denominator_pos ha hc hA))

/-- This genuine moment source obeys the same normalized Riccati chain as theta. -/
theorem hasDerivAt_ratio_aperture {a lambda A : ℝ}
    (ha : 0≤a) (hl : lambda<1) (hA : 0<A) :
    HasDerivAt (fun l => ratio a (1-l) A)
      (ratio a (1-lambda) A*((A+1)*ratio a (1-lambda) (A+1)-A*ratio a (1-lambda) A)) lambda := by
  have hc : 0<1-lambda := by linarith
  have hd (B : ℝ) : HasDerivAt (fun l : ℝ => denominator a (1-l) B)
      (-3*(1-lambda)^2) lambda := by
    have hh := ((((hasDerivAt_id lambda).const_sub 1).pow 3).add_const (a*B*(B+1)*(B+2)))
    simpa [denominator] using hh
  have hh := (hd (A+1)).div (((hasDerivAt_id lambda).const_sub 1).mul (hd A))
    (mul_pos hc (denominator_pos ha hc hA)).ne'
  apply hh.congr_deriv
  dsimp only [id_eq,Pi.mul_apply]
  unfold ratio
  have h0 := (denominator_pos ha hc hA).ne'
  have h1 := (denominator_pos ha hc (show 0<A+1 by linarith)).ne'
  field_simp
  unfold denominator
  ring

/-- Exact positive-square production plus forward transport and reaction. -/
theorem hasDerivAt_curvature_aperture {a lambda A : ℝ}
    (ha : 0≤a) (hl : lambda<1) (hA : 0<A) :
    HasDerivAt (fun l => curvature a (1-l) A)
      (4*(ratio a (1-lambda) A-ratio a (1-lambda) (A+1))^2+
        (A+3)*ratio a (1-lambda) (A+2)*curvature a (1-lambda) (A+1)+
        curvature a (1-lambda) A*
          (-(A+4)*ratio a (1-lambda) A+(1-A)*ratio a (1-lambda) (A+1)+
            (A+4)*ratio a (1-lambda) (A+2))) lambda := by
  have h0 := hasDerivAt_ratio_aperture ha hl hA
  have h1 := hasDerivAt_ratio_aperture ha hl (show 0<A+1 by linarith)
  have h2 := hasDerivAt_ratio_aperture ha hl (show 0<A+2 by linarith)
  apply ((h0.sub (h1.const_mul 2)).add h2).congr_deriv
  simpa only [curvature,HTGeometry.localRatioSecondCurvatureVelocity,
    show A+1+1=A+2 by ring,show A+2+1=A+3 by ring,show A+1+2=A+3 by ring,
    mul_one,mul_assoc] using HTGeometry.affineGamma_ratioSecondCurvatureVelocity_eq A 1
      (ratio a (1-lambda) A) (ratio a (1-lambda) (A+1))
      (ratio a (1-lambda) (A+2)) (ratio a (1-lambda) (A+3))

/-- Every fixed degree has a strictly positive cold leading coefficient. -/
theorem tendsto_scaled_fixed_degree {a A : ℝ} (ha : 0≤a) (hA : 0<A) :
    Tendsto (fun c : ℝ => c^4*curvature a c A) atTop (𝓝 (6*a)) := by
  have hprof : ContinuousAt (fun e : ℝ => cornerProfile a (A*e) e) 0 := by
    unfold cornerProfile
    fun_prop (disch := norm_num)
  have ht : Tendsto (fun c : ℝ => 1/c) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0))
  have hh := hprof.tendsto.comp ht
  have hv : cornerProfile a (A*0) 0 = 6*a := by simp [cornerProfile]
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
  have he := scaled_corner_eq ha hc (div_pos hA hc)
  rw [mul_div_cancel₀ A hc.ne'] at he
  simpa only [Function.comp_def,mul_one_div] using he.symm

theorem eventually_fixed_degree_pos {a A : ℝ} (ha : 0<a) (hA : 0<A) :
    ∀ᶠc : ℝ in atTop, 0<curvature a c A := by
  have hh := (tendsto_scaled_fixed_degree ha.le hA).eventually
    (Ioi_mem_nhds (show 0<6*a by positivity))
  filter_upwards [hh] with c hc
  exact pos_of_mul_pos_right hc (by positivity : 0≤c^4)

/-- An explicit sufficient tail bound, uniform on every bounded aperture set. -/
theorem curvature_pos_of_degree_bound {a c A : ℝ}
    (ha : 0<a) (hc : 0<c) (hA : 1≤A) (hbound : 240*c^3≤a*A^3) :
    0<curvature a c A := by
  have hA0 : 0<A := by linarith
  have hK : (A+2)*(A+3)*(7*A+13)≤240*A^3 := by
    calc
      (A+2)*(A+3)*(7*A+13) ≤ (3*A)*(4*A)*(20*A) := by gcongr <;> linarith
      _ = 240*A^3 := by ring
  have hV : A^6≤(A+1)*(A+2)^2*(A+3)^2*(A+4) := by
    calc
      A^6 = A*A^2*A^2*A := by ring
      _ ≤ (A+1)*(A+2)^2*(A+3)^2*(A+4) := by gcongr <;> linarith
  have hK' := mul_le_mul_of_nonneg_left hK (show 0≤a*c^3 by positivity)
  have hV' := mul_le_mul_of_nonneg_left hV (sq_nonneg a)
  have hb := mul_le_mul_of_nonneg_left hbound (show 0≤a*A^3 by positivity)
  have hN : 0<numerator a c A := by
    unfold numerator
    nlinarith [pow_pos hc 6]
  rw [curvature_eq ha.le hc hA0]
  exact div_pos (mul_pos (by positivity) hN)
    (mul_pos (mul_pos (mul_pos hc (denominator_pos ha.le hc hA0))
      (denominator_pos ha.le hc (by linarith))) (denominator_pos ha.le hc (by linarith)))

/-- The negative channel travels to unbounded degree in the cold corner. -/
theorem eventually_diagonal_negative :
    ∀ᶠc : ℝ in atTop, curvature (64/105) c c<0 := by
  have ht := tendsto_scaled_corner (a:=64/105) (u:=1) (by norm_num) (by norm_num)
  have hneg : 6*(64/105:ℝ)*(1-7*(64/105:ℝ)*1^3+(64/105:ℝ)^2*1^6)/(1+(64/105:ℝ)*1^3)^3<0 := by norm_num
  have hh := ht.eventually (Iio_mem_nhds hneg)
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with c h hc
  simp only [mul_one] at h
  have hc4 := pow_pos hc 4
  nlinarith

/-- Uniform high-degree positivity on every compact positive aperture interval. -/
theorem uniform_compact_degree_pos {a M : ℝ} (ha : 0<a) (hM : 0<M) :
    ∃ J : ℕ, ∀j : ℕ, J≤j → ∀c : ℝ, 0<c → c≤M →
      0<curvature a c (thetaCuspGaussianApertureGammaShape j) := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (1+240*M^3/a)
  refine ⟨J,?_⟩
  intro j hj c hc hcM
  have hjR : (J:ℝ)≤j := by exact_mod_cast hj
  let A := thetaCuspGaussianApertureGammaShape j
  have hA : (j:ℝ)≤A := by dsimp [A,thetaCuspGaussianApertureGammaShape]; linarith
  have hMterm : 0≤240*M^3/a := by positivity
  have hA1 : 1≤A := by linarith
  have hfrac : 240*M^3/a≤A := by linarith
  have hax : 240*M^3≤A*a := (div_le_iff₀ ha).mp hfrac
  have hpow : A≤A^3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hA1) (show 0≤A*(A+1) by positivity)
    nlinarith
  have hpow' := mul_le_mul_of_nonneg_left hpow ha.le
  have hc3 : c^3≤M^3 := by gcongr
  apply curvature_pos_of_degree_bound ha hc hA1
  nlinarith

/-- Natural degree and aperture escape together through a strictly negative channel. -/
theorem eventually_natural_diagonal_negative :
    ∀ᶠj : ℕ in atTop,
      curvature (64/105) (thetaCuspGaussianApertureGammaShape j)
        (thetaCuspGaussianApertureGammaShape j)<0 := by
  have ht : Tendsto thetaCuspGaussianApertureGammaShape atTop atTop := by
    unfold thetaCuspGaussianApertureGammaShape
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact ht.eventually eventually_diagonal_negative

/-- Neither separate endpoint regime controls the incoming cold/degree corner. -/
theorem exists_positive_source_corner_counterexample :
    ∃a : ℝ, 0<a ∧
      (∀x,0<density a x) ∧ (∀x,density a (-x)=density a x) ∧
      (∀j : ℕ, ∀ᶠc : ℝ in atTop,
        0<curvature a c (thetaCuspGaussianApertureGammaShape j)) ∧
      (∀M : ℝ, 0<M → ∃J : ℕ, ∀j : ℕ, J≤j → ∀c : ℝ, 0<c → c≤M →
        0<curvature a c (thetaCuspGaussianApertureGammaShape j)) ∧
      curvature a 2 (thetaCuspGaussianApertureGammaShape 0) = -7/40 ∧
      (∀ᶠj : ℕ in atTop,
        curvature a (thetaCuspGaussianApertureGammaShape j)
          (thetaCuspGaussianApertureGammaShape j)<0) := by
  refine ⟨64/105,by norm_num,density_pos (by norm_num),density_even _,?_,?_,?_,
    eventually_natural_diagonal_negative⟩
  · intro j
    exact eventually_fixed_degree_pos (by norm_num) (thetaCuspGaussianApertureGammaShape_pos j)
  · intro M hM
    exact uniform_compact_degree_pos (by norm_num) hM
  · simpa [thetaCuspGaussianApertureGammaShape] using curvature_exact_negative

end RHTower.ColdDegreeCorner
