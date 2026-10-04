import GaloisForLFunctions.RHTower.ThetaTwoNodeSignedSturmEnergy

/-! Polarized signed Sturm identity on the two-node theta source span, and its
three-node port form.

For nodes `0 ≤ x < z` the source translates obey the affine port law
`k(u+t)' = (j(t) - s(t)(u+t)) k(u+t)` exactly at `u = x, z`, where `s, j` are the slope
secant and intercept.  At a third node `y` the same law holds up to the extrapolation
defect `E(t) = p(y+t) - (s(t)(y+t) - j(t))`, which is positive for `y > z`.  Integrating
`(λ f g)'` with `λ = 1/s` against an old-span packet `f` and a three-node packet `g`
gives the polarized identity
`Q(f,g) = λ(0) f(0) g(0) + ∫ w f g - d ∫ λ f k(y+·) E`,
where `Q` is the literal common-tail bilinear form and `d` the coefficient of `k(y+·)`.
For the actual projection residual `R` of `k(y+·)` onto the two-node span, `Q(f,R) = 0`
for every old-span `f`; at the first port boundary `R(0) = 0` this yields
`∫ w G R = ∫ λ G k(y+·) E` for the inverse-Gram source representer `G`. -/

noncomputable section
open MeasureTheory Filter Topology Set

namespace RHTower.ThetaSturm

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel

/-- Extrapolation defect of the log-decay slope at `y+t` from the secant line through
the two nodes `x+t, z+t`. -/
def extrapolationDefect (x z y t : ℝ) : ℝ :=
  thetaCuspLogDecaySlope (y+t) - (secant x z t*(y+t) - intercept x z t)

/-- A three-node source packet: an old-span packet plus `d` times the new translate. -/
def portPacket (x z y d a b t : ℝ) : ℝ := d*k (y+t) + packet x z a b t

/-- The coordinate-weighted companion of `portPacket`. -/
def portCoordinate (x z y d a b t : ℝ) : ℝ :=
  d*((y+t)*k (y+t)) + coordinatePacket x z a b t

/-- The literal common-tail pairing of an old-span packet with a three-node packet. -/
def crossPairing (x z y d a b a' b' : ℝ) : ℝ :=
  a'*(d*H x y + a*H x x + b*H x z) + b'*(d*H z y + a*H z x + b*H z z)

/-- First coefficient of the projection of the translate at `y` onto the two-node span. -/
def portLeft (x z y : ℝ) : ℝ := (H z z*H x y - H x z*H z y)/determinant x z

/-- Second coefficient of the projection of the translate at `y` onto the two-node span. -/
def portRight (x z y : ℝ) : ℝ := (H x x*H z y - H x z*H x y)/determinant x z

/-- The actual projection residual `R(t) = k(y+t) - c₁ k(x+t) - c₂ k(z+t)`. -/
def portResidual (x z y : ℝ) : ℝ → ℝ :=
  portPacket x z y 1 (-portLeft x z y) (-portRight x z y)

private theorem source_deriv_eq (t : ℝ) :
    deriv k t = -thetaCuspLogDecaySlope t*k t := by
  have h : iteratedDeriv 1 thetaCuspLogSource t = deriv k t/k t := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all t).ne']

/-- The extrapolation defect is strictly positive beyond the second node. -/
theorem extrapolationDefect_pos {x z y : ℝ} (hx : 0 ≤ x) (hxz : x < z) (hzy : z < y)
    {t : ℝ} (ht : 0 ≤ t) : 0 < extrapolationDefect x z y t := by
  have h := (ThetaPort.two_node_extrapolation_defects_neg (show 0 ≤ x+t by linarith)
    (show x+t < z+t by linarith) (show z+t < y+t by linarith)).1
  have hd : (z+t)-(x+t) ≠ 0 := by linarith
  have he : extrapolationDefect x z y t = -(((z+t-(y+t))/(z+t-(x+t)))*thetaCuspLogDecaySlope (x+t) +
      ((y+t-(x+t))/(z+t-(x+t)))*thetaCuspLogDecaySlope (z+t) - thetaCuspLogDecaySlope (y+t)) := by
    have hzx : z-x ≠ 0 := sub_ne_zero.mpr hxz.ne'
    simp only [extrapolationDefect, secant, intercept, add_sub_add_right_eq_sub]
    field_simp
    ring
  rw [he]
  exact neg_pos.mpr h

/-- Exact port law: the three-node packet obeys the two-node affine law up to the
extrapolation defect carried by the new translate. -/
theorem portPacket_hasDerivAt {x z : ℝ} (hxz : x < z) (y d a b t : ℝ) :
    HasDerivAt (portPacket x z y d a b)
      (intercept x z t*portPacket x z y d a b t - secant x z t*portCoordinate x z y d a b t -
        d*(k (y+t)*extrapolationDefect x z y t)) t := by
  have hk : HasDerivAt k (deriv k (y+t)) (y+t) := thetaCuspSchwartzReal.hasDerivAt (y+t)
  have hy := hk.comp t ((hasDerivAt_id t).const_add y)
  convert! (hy.const_mul d).add (packet_hasDerivAt hxz a b t) using 1
  simp only [source_deriv_eq, portPacket, portCoordinate, extrapolationDefect, mul_one]
  ring

private theorem translate_continuous (φ : SchwartzMap ℝ ℝ) (u : ℝ) :
    Continuous (fun t : ℝ => φ (u+t)) :=
  φ.continuous.comp (continuous_const.add continuous_id)

/-- Products of two Schwartz translates are integrable on the half-line against every
continuous weight of at most linear growth there. -/
theorem weighted_translate_product_integrable {B : ℝ → ℝ} (hB : Continuous B) {C D : ℝ}
    (hb : ∀ t, 0 < t → |B t| ≤ C + D*t) (φ ψ : SchwartzMap ℝ ℝ) (u v : ℝ) :
    IntegrableOn (fun t => B t*(φ (u+t)*ψ (v+t))) (Ioi 0) := by
  have hφ := (φ.integrable (μ := (volume : Measure ℝ))).comp_add_left u
  have hwφ : Integrable (fun t => (C+D*t)*φ (u+t)) := by
    have hw := ((SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) φ).integrable
      (μ := (volume : Measure ℝ))).comp_add_left u
    have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul] at hw
    convert! (hφ.const_mul (C-D*u)).add (hw.const_mul D) using 1
    ext t
    dsimp
    ring
  have hp := hwφ.mul_bdd (translate_continuous ψ v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ψ.norm_le_seminorm ℝ (v+t))
  refine (hp.integrableOn (s := Ioi 0)).norm.mono'
    (hB.mul ((translate_continuous φ u).mul (translate_continuous ψ v))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h0 : 0 ≤ C + D*t := (abs_nonneg _).trans (hb t ht)
  have key := mul_le_mul_of_nonneg_right (hb t ht)
    (mul_nonneg (abs_nonneg (φ (u+t))) (abs_nonneg (ψ (v+t))))
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0, mul_assoc] using key

private theorem slope_continuous : Continuous thetaCuspLogDecaySlope :=
  continuous_iff_continuousAt.mpr fun t =>
    ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 t).neg).continuousAt

private theorem secant_continuous' (x z : ℝ) : Continuous (secant x z) :=
  continuous_iff_continuousAt.mpr fun t => (secant_hasDerivAt x z t).continuousAt

private theorem intercept_continuous' (x z : ℝ) : Continuous (intercept x z) :=
  (((continuous_const.add continuous_id).mul (slope_continuous.comp
    (continuous_const.add continuous_id))).sub ((continuous_const.add continuous_id).mul
      (slope_continuous.comp (continuous_const.add continuous_id)))).div_const _

private theorem ratio_continuous {x z : ℝ} (hxz : x < z) :
    Continuous (fun t => intercept x z t/secant x z t) :=
  (intercept_continuous' x z).div (secant_continuous' x z) fun t => (secant_pos hxz t).ne'

private theorem ratio_bound {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (t : ℝ) (ht : 0 < t) :
    |intercept x z t/secant x z t| ≤ x + 1*t := by
  rw [abs_of_nonneg (div_nonneg (intercept_nonneg hx hxz ht.le) (secant_pos hxz t).le), one_mul]
  exact intercept_div_le hx hxz ht.le

private theorem reciprocal_continuous {x z : ℝ} (hxz : x < z) : Continuous (reciprocal x z) :=
  continuous_iff_continuousAt.mpr fun t => (reciprocal_hasDerivAt hxz t).continuousAt

private theorem reciprocal_bound {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (t : ℝ) (ht : 0 < t) :
    |reciprocal x z t| ≤ reciprocal x z 0 + 0*t := by
  rw [zero_mul, add_zero,
    abs_of_pos (show 0 < reciprocal x z t from one_div_pos.mpr (secant_pos hxz t))]
  exact reciprocal_antitoneOn hx hxz self_mem_Ici
    (show t ∈ Ici 0 from ht.le) ht.le

private theorem source_bound (u : ℝ) : ‖k u‖ ≤ SchwartzMap.seminorm ℝ 0 0 thetaCuspSchwartzReal :=
  thetaCuspSchwartzReal.norm_le_seminorm ℝ u

/-- The signed Sturm density is integrable against every product of two source translates. -/
theorem density_mul_translates_integrable {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (u v : ℝ) :
    IntegrableOn (fun t => density x z t*(k (u+t)*k (v+t))) (Ioi 0) := by
  have hmain := weighted_translate_product_integrable
    ((ratio_continuous hxz).const_mul 2) (C := 2*x) (D := 2)
    (fun t ht => by
      rw [abs_mul, abs_two]
      linarith [ratio_bound hx hxz t ht]) thetaCuspSchwartzReal thetaCuspSchwartzReal u v
  set K := SchwartzMap.seminorm ℝ 0 0 thetaCuspSchwartzReal
  have htail : IntegrableOn (fun t => reciprocalJet x z t*(k (u+t)*k (v+t))) (Ioi 0) := by
    apply (reciprocalJet_integrable hx hxz).mul_bdd (c := K*K)
      ((translate_continuous thetaCuspSchwartzReal u).mul
        (translate_continuous thetaCuspSchwartzReal v)).aestronglyMeasurable
    filter_upwards [] with t
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (source_bound _) (source_bound _) (norm_nonneg _)
      ((norm_nonneg _).trans (source_bound 0))
  convert! hmain.add htail using 1
  ext t
  simp only [thetaCuspSchwartzReal_apply, density, Pi.add_apply]
  ring

private theorem translates_integrable_of {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ∀ u v, IntegrableOn (F u v) (Ioi 0)) (x z y d a b a' b' : ℝ) :
    IntegrableOn (fun t => a'*(d*F x y t + a*F x x t + b*F x z t) +
      b'*(d*F z y t + a*F z x t + b*F z z t)) (Ioi 0) := by
  have hrow (u : ℝ) : IntegrableOn (fun t => d*F u y t + a*F u x t + b*F u z t) (Ioi 0) :=
    (((hF u y).const_mul d).add ((hF u x).const_mul a)).add ((hF u z).const_mul b)
  exact ((hrow x).const_mul a').add ((hrow z).const_mul b')

private theorem integral_translates_comb {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ∀ u v, IntegrableOn (F u v) (Ioi 0)) (x z y d a b a' b' : ℝ) :
    (∫ t in Ioi 0, (a'*(d*F x y t + a*F x x t + b*F x z t) +
      b'*(d*F z y t + a*F z x t + b*F z z t))) =
    a'*(d*(∫ t in Ioi 0, F x y t) + a*(∫ t in Ioi 0, F x x t) + b*∫ t in Ioi 0, F x z t) +
      b'*(d*(∫ t in Ioi 0, F z y t) + a*(∫ t in Ioi 0, F z x t) + b*∫ t in Ioi 0, F z z t) := by
  have hrow (u : ℝ) : IntegrableOn (fun t => d*F u y t + a*F u x t + b*F u z t) (Ioi 0) :=
    (((hF u y).const_mul d).add ((hF u x).const_mul a)).add ((hF u z).const_mul b)
  have h3 (u : ℝ) : (∫ t in Ioi 0, (d*F u y t + a*F u x t + b*F u z t)) =
      d*(∫ t in Ioi 0, F u y t) + a*(∫ t in Ioi 0, F u x t) + b*∫ t in Ioi 0, F u z t := by
    have h1 : IntegrableOn (fun t => d*F u y t) (Ioi 0) := (hF u y).const_mul d
    have h2 : IntegrableOn (fun t => a*F u x t) (Ioi 0) := (hF u x).const_mul a
    have h4 : IntegrableOn (fun t => b*F u z t) (Ioi 0) := (hF u z).const_mul b
    have h12 : IntegrableOn (fun t => d*F u y t + a*F u x t) (Ioi 0) := h1.add h2
    rw [integral_add h12 h4, integral_add h1 h2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hx' : IntegrableOn (fun t => a'*(d*F x y t + a*F x x t + b*F x z t)) (Ioi 0) :=
    (hrow x).const_mul a'
  have hz' : IntegrableOn (fun t => b'*(d*F z y t + a*F z x t + b*F z z t)) (Ioi 0) :=
    (hrow z).const_mul b'
  rw [integral_add hx' hz', integral_const_mul, integral_const_mul, h3 x, h3 z]

theorem density_cross_integrable {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (y d a b a' b' : ℝ) :
    IntegrableOn (fun t => density x z t*(packet x z a' b' t*portPacket x z y d a b t)) (Ioi 0) := by
  convert! translates_integrable_of (density_mul_translates_integrable hx hxz) x z y d a b a' b'
    using 1
  ext t
  simp only [packet, portPacket]
  ring

private theorem pairing_integrand_eq (x z y d a b a' b' t : ℝ) :
    coordinatePacket x z a' b' t*portPacket x z y d a b t +
      packet x z a' b' t*portCoordinate x z y d a b t =
    a'*(d*thetaTailCommonTranslationIntegrand x y t + a*thetaTailCommonTranslationIntegrand x x t +
        b*thetaTailCommonTranslationIntegrand x z t) +
      b'*(d*thetaTailCommonTranslationIntegrand z y t + a*thetaTailCommonTranslationIntegrand z x t +
        b*thetaTailCommonTranslationIntegrand z z t) := by
  simp only [coordinatePacket, portPacket, packet, portCoordinate, thetaTailCommonTranslationIntegrand]
  ring

theorem pairing_integrable (x z y d a b a' b' : ℝ) :
    IntegrableOn (fun t => coordinatePacket x z a' b' t*portPacket x z y d a b t +
      packet x z a' b' t*portCoordinate x z y d a b t) (Ioi 0) := by
  simp only [pairing_integrand_eq]
  exact translates_integrable_of (fun u v => (integrable_thetaTailCommonTranslationIntegrand u v).integrableOn)
    x z y d a b a' b'

/-- The half-line pairing integral is the literal common-tail kernel pairing. -/
theorem integral_pairing_eq_crossPairing (x z y d a b a' b' : ℝ) :
    (∫ t in Ioi 0, (coordinatePacket x z a' b' t*portPacket x z y d a b t +
      packet x z a' b' t*portCoordinate x z y d a b t)) = crossPairing x z y d a b a' b' := by
  have hH (u v : ℝ) : (∫ t in Ioi 0, thetaTailCommonTranslationIntegrand u v t) = H u v := by
    simpa only [add_zero] using (thetaTailFirstMomentKernel_commonShift_eq_tail 0 u v).symm
  simp only [pairing_integrand_eq]
  rw [integral_translates_comb (fun u v => (integrable_thetaTailCommonTranslationIntegrand u v).integrableOn)]
  simp only [hH, crossPairing]

/-- The source-forcing term `λ f k(y+·) E` is integrable for every old-span packet `f`.
It is the difference of integrable derivative and source terms: `λ k(y+·) E` equals
`-λ k'(y+·) - (y+·) k(y+·) + (j/s) k(y+·)`. -/
theorem forcing_integrable {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (y a' b' : ℝ) :
    IntegrableOn (fun t => reciprocal x z t*(packet x z a' b' t*
      (k (y+t)*extrapolationDefect x z y t))) (Ioi 0) := by
  have hk' (u : ℝ) : SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal u =
      -thetaCuspLogDecaySlope u*k u := by
    rw [SchwartzMap.derivCLM_apply]
    exact source_deriv_eq u
  have h1 (u : ℝ) := weighted_translate_product_integrable (reciprocal_continuous hxz)
    (reciprocal_bound hx hxz) (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal)
    thetaCuspSchwartzReal y u
  have h2 (u : ℝ) := weighted_translate_product_integrable (B := fun t => y+t)
    (continuous_const.add continuous_id) (C := |y|) (D := 1)
    (fun t ht => by
      simpa only [one_mul, abs_of_pos ht] using abs_add_le y t) thetaCuspSchwartzReal
    thetaCuspSchwartzReal y u
  have h3 (u : ℝ) := weighted_translate_product_integrable (ratio_continuous hxz)
    (ratio_bound hx hxz) thetaCuspSchwartzReal thetaCuspSchwartzReal y u
  have hsum := ((((h1 x).neg.sub (h2 x)).add (h3 x)).const_mul a').add
    ((((h1 z).neg.sub (h2 z)).add (h3 z)).const_mul b')
  refine IntegrableOn.congr_fun hsum (fun t _ => ?_) measurableSet_Ioi
  have hs := (secant_pos hxz t).ne'
  simp only [hk', thetaCuspSchwartzReal_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    reciprocal, packet, extrapolationDefect]
  field_simp
  ring

private theorem translate_tendsto (u : ℝ) : Tendsto (fun t => k (u+t)) atTop (𝓝 0) :=
  (thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact).comp
    (tendsto_atTop_add_const_left atTop u tendsto_id)

private theorem packet_tendsto (x z a b : ℝ) : Tendsto (packet x z a b) atTop (𝓝 0) := by
  change Tendsto (fun t => a*k (x+t) + b*k (z+t)) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using ((translate_tendsto x).const_mul a).add
    ((translate_tendsto z).const_mul b)

private theorem portPacket_tendsto (x z y d a b : ℝ) :
    Tendsto (portPacket x z y d a b) atTop (𝓝 0) := by
  change Tendsto (fun t => d*k (y+t) + packet x z a b t) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using ((translate_tendsto y).const_mul d).add
    (packet_tendsto x z a b)

/-- Polarized signed Sturm identity for an old-span packet against a three-node packet:
`Q(f,g) = f(0)g(0)/s(0) + ∫ w f g - d ∫ λ f k(y+·) E`. -/
theorem crossPairing_eq_boundary_add_signed_integral {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z)
    (y d a b a' b' : ℝ) :
    crossPairing x z y d a b a' b' =
      packet x z a' b' 0*portPacket x z y d a b 0/secant x z 0 +
        (∫ t in Ioi 0, density x z t*(packet x z a' b' t*portPacket x z y d a b t)) -
        d*∫ t in Ioi 0, reciprocal x z t*(packet x z a' b' t*
          (k (y+t)*extrapolationDefect x z y t)) := by
  obtain ⟨l,hl⟩ := reciprocal_limit_exists hx hxz
  have hpk := packet_tendsto x z a' b'
  have hb : Tendsto (fun t => reciprocal x z t*packet x z a' b' t*portPacket x z y d a b t)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (hl.mul hpk).mul (portPacket_tendsto x z y d a b)
  have hd (t : ℝ) : HasDerivAt (fun t => reciprocal x z t*packet x z a' b' t*portPacket x z y d a b t)
      (density x z t*(packet x z a' b' t*portPacket x z y d a b t) -
        (coordinatePacket x z a' b' t*portPacket x z y d a b t +
          packet x z a' b' t*portCoordinate x z y d a b t) -
        d*(reciprocal x z t*(packet x z a' b' t*(k (y+t)*extrapolationDefect x z y t)))) t := by
    convert! ((reciprocal_hasDerivAt hxz t).mul (packet_hasDerivAt hxz a' b' t)).mul
      (portPacket_hasDerivAt hxz y d a b t) using 1
    simp only [density, reciprocal, Pi.mul_apply]
    field_simp [(secant_pos hxz t).ne']
    ring
  have hi1 := density_cross_integrable hx hxz y d a b a' b'
  have hi2 := pairing_integrable x z y d a b a' b'
  have hi3 := (forcing_integrable hx hxz y a' b').const_mul d
  have hi12 : IntegrableOn (fun t => density x z t*(packet x z a' b' t*portPacket x z y d a b t) -
      (coordinatePacket x z a' b' t*portPacket x z y d a b t +
        packet x z a' b' t*portCoordinate x z y d a b t)) (Ioi 0) := hi1.sub hi2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun t _ => hd t) (hi12.sub hi3) hb
  rw [integral_sub hi12 hi3, integral_sub hi1 hi2, integral_const_mul,
    integral_pairing_eq_crossPairing] at h
  have h0 : packet x z a' b' 0*portPacket x z y d a b 0/secant x z 0 =
      reciprocal x z 0*packet x z a' b' 0*portPacket x z y d a b 0 := by
    simp only [reciprocal]
    ring
  rw [h0]
  linarith only [h]

/-- Polarization of the two-node identity: on the old span the literal bilinear form is
`Q(f,g) = f(0)g(0)/s(0) + ∫ w f g`. -/
theorem crossPairing_old_span {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (y a b a' b' : ℝ) :
    crossPairing x z y 0 a b a' b' =
      packet x z a' b' 0*packet x z a b 0/secant x z 0 +
        ∫ t in Ioi 0, density x z t*(packet x z a' b' t*packet x z a b t) := by
  have h := crossPairing_eq_boundary_add_signed_integral hx hxz y 0 a b a' b'
  simpa only [portPacket, zero_mul, zero_add, sub_zero] using h

/-- The projection coefficients solve the literal two-node normal equations. -/
theorem port_equations {x z : ℝ} (hxz : x < z) (y : ℝ) :
    (H x x*portLeft x z y + H x z*portRight x z y = H x y) ∧
    (H x z*portLeft x z y + H z z*portRight x z y = H z y) := by
  have hD : determinant x z ≠ 0 := (ThetaTailTwoPoint.kernel_two_point_det_pos hxz.ne).ne'
  constructor <;> dsimp only [portLeft, portRight] <;>
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hD] <;>
    dsimp only [determinant] <;> ring

/-- The actual projection residual is orthogonal to the whole two-node span in the
literal common-tail form. -/
theorem crossPairing_portResidual_eq_zero {x z : ℝ} (hxz : x < z) (y a' b' : ℝ) :
    crossPairing x z y 1 (-portLeft x z y) (-portRight x z y) a' b' = 0 := by
  obtain ⟨h₁,h₂⟩ := port_equations hxz y
  have hc := thetaTailFirstMomentKernel_comm z x
  simp only [crossPairing]
  linear_combination (-a')*h₁ + (-b')*h₂ - b'*portLeft x z y*hc

/-- The projection residual obeys the exact port law
`R' = j R - s X - k(y+·) E` with `X` the coordinate-source residual. -/
theorem portResidual_hasDerivAt {x z : ℝ} (hxz : x < z) (y t : ℝ) :
    HasDerivAt (portResidual x z y)
      (intercept x z t*portResidual x z y t -
        secant x z t*portCoordinate x z y 1 (-portLeft x z y) (-portRight x z y) t -
        k (y+t)*extrapolationDefect x z y t) t := by
  simpa only [portResidual, one_mul] using
    portPacket_hasDerivAt hxz y 1 (-portLeft x z y) (-portRight x z y) t

/-- Signed Sturm identity for the actual projection residual against any old-span packet:
`λ(0) f(0) R(0) + ∫ w f R = ∫ λ f k(y+·) E`. -/
theorem portResidual_signed_identity {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (y a' b' : ℝ) :
    packet x z a' b' 0*portResidual x z y 0/secant x z 0 +
        (∫ t in Ioi 0, density x z t*(packet x z a' b' t*portResidual x z y t)) =
      ∫ t in Ioi 0, reciprocal x z t*(packet x z a' b' t*
        (k (y+t)*extrapolationDefect x z y t)) := by
  have h := crossPairing_eq_boundary_add_signed_integral hx hxz y 1
    (-portLeft x z y) (-portRight x z y) a' b'
  rw [crossPairing_portResidual_eq_zero hxz, one_mul] at h
  simp only [portResidual]
  linarith only [h]

/-- On the first port boundary `R(0) = 0`, the signed density pairs the actual
inverse-Gram source representer `G` with the projection residual exactly through the
positive extrapolation forcing: `∫ w G R = ∫ λ G k(y+·) E`. -/
theorem representer_portResidual_signed_identity {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (y : ℝ)
    (hR : portResidual x z y 0 = 0) :
    (∫ t in Ioi 0, density x z t*(representer x z t*portResidual x z y t)) =
      ∫ t in Ioi 0, reciprocal x z t*(representer x z t*
        (k (y+t)*extrapolationDefect x z y t)) := by
  have h := portResidual_signed_identity hx hxz y (representerLeft x z) (representerRight x z)
  rw [hR, mul_zero, zero_div, zero_add] at h
  exact h

end RHTower.ThetaSturm
