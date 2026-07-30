import GaloisForLFunctions.RHTower.MobiusLaplaceHalfPolylogCriterion
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import Mathlib.MeasureTheory.Integral.Gamma

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology


namespace RHTower

noncomputable section

private theorem exact_log_mellin_moment
    (q : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioc 0 1, x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) =
      (q.factorial : ℝ) / r ^ (q + 1) := by
  let f : ℝ → ℝ := fun u => Real.exp (-u)
  let g : ℝ → ℝ := fun x => x ^ (r - 1) * |Real.log x| ^ (q : ℝ)
  have hfderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (-Real.exp (-u)) (Ioi 0) u := by
    intro u hu
    apply HasDerivAt.hasDerivWithinAt
    dsimp only [f]
    convert! (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u) using 1
    all_goals ring
  have hfinj : Set.InjOn f (Ioi (0 : ℝ)) := by
    intro u hu v hv huv
    dsimp only [f] at huv
    exact neg_injective (Real.exp_injective huv)
  have hfimage : f '' Ioi (0 : ℝ) = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      dsimp only [f]
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)⟩
    · intro hx
      refine ⟨-Real.log x, ?_, ?_⟩
      · exact neg_pos.mpr (Real.log_neg hx.1 hx.2)
      · dsimp only [f]
        rw [neg_neg, Real.exp_log hx.1]
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hfderiv hfinj g
  rw [hfimage] at hchange
  rw [← setIntegral_congr_set Ioo_ae_eq_Ioc, hchange]
  have hpoint : ∀ u ∈ Ioi (0 : ℝ),
      |-Real.exp (-u)| • g (f u) =
        u ^ (q : ℝ) * Real.exp (-r * u) := by
    intro u hu
    have huexp : 0 < Real.exp (-u) := Real.exp_pos _
    dsimp only [f, g]
    rw [abs_of_neg (neg_neg_of_pos huexp), neg_neg,
      Real.rpow_def_of_pos huexp, Real.log_exp,
      abs_of_nonpos (neg_nonpos.mpr hu.le), neg_neg]
    simp only [smul_eq_mul]
    calc
      Real.exp (-u) * (Real.exp (-u * (r - 1)) * u ^ (q : ℝ)) =
          u ^ (q : ℝ) * (Real.exp (-u) * Real.exp (-u * (r - 1))) := by ring
      _ = u ^ (q : ℝ) * Real.exp ((-u) + (-u * (r - 1))) := by
        rw [Real.exp_add]
      _ = u ^ (q : ℝ) * Real.exp (-r * u) := by
        congr 2
        ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have hgamma := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (q : ℝ)) (b := r) (by norm_num)
      (by have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith) hr
  norm_num [Real.rpow_one] at hgamma
  rw [Real.Gamma_nat_eq_factorial] at hgamma
  have hexp : -(1 : ℝ) + -(q : ℝ) = -((q + 1 : ℕ) : ℝ) := by
    norm_num
  rw [hexp, Real.rpow_neg (le_of_lt hr), Real.rpow_natCast] at hgamma
  simpa [div_eq_mul_inv, mul_comm] using hgamma

private theorem abs_log_rpow_nat_le_factorial_div
    (q : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) (hxOne : x ≤ 1) :
    |Real.log x| ^ (q : ℝ) ≤
      ((q.factorial : ℝ) / (r / 2) ^ q) * x ^ (-(r / 2)) := by
  have hlog : 0 ≤ -Real.log x :=
    neg_nonneg.mpr (Real.log_nonpos hx.le hxOne)
  have ha : 0 < r / 2 := by linarith
  have hexp := Real.pow_div_factorial_le_exp
    ((r / 2) * (-Real.log x)) (mul_nonneg ha.le hlog) q
  have hfac : (0 : ℝ) < q.factorial := by positivity
  have hpow : 0 < (r / 2) ^ q := pow_pos ha q
  have hcore : (-Real.log x) ^ q ≤
      ((q.factorial : ℝ) / (r / 2) ^ q) *
        Real.exp ((r / 2) * (-Real.log x)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hpow).2
    calc
      (-Real.log x) ^ q * (r / 2) ^ q =
          ((r / 2) * (-Real.log x)) ^ q := by
        rw [← mul_pow]
        congr 1
        ring
      _ ≤ (q.factorial : ℝ) * Real.exp ((r / 2) * (-Real.log x)) := by
        have := (div_le_iff₀ hfac).1 hexp
        simpa [mul_comm] using this
  rw [Real.rpow_natCast]
  have habs : |Real.log x| = -Real.log x := by
    rw [abs_of_nonpos (Real.log_nonpos hx.le hxOne)]
  rw [habs]
  calc
    (-Real.log x) ^ q ≤
        ((q.factorial : ℝ) / (r / 2) ^ q) *
          Real.exp ((r / 2) * (-Real.log x)) := hcore
    _ = ((q.factorial : ℝ) / (r / 2) ^ q) * x ^ (-(r / 2)) := by
      rw [Real.rpow_def_of_pos hx]
      congr 2
      ring

private theorem integrableOn_halfPolylogMellinMajor
    (q : ℕ) {C r a : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (ha : 0 < a) (haOne : a ≤ 1) :
    IntegrableOn
      (fun x : ℝ => C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)))
      (Ioc 0 a) := by
  let K : ℝ := C * ((q.factorial : ℝ) / (r / 2) ^ q)
  have hK : 0 ≤ K := by positivity
  have hlooseInt : IntegrableOn
      (fun x : ℝ => K * x ^ (r / 2 - 1)) (Ioc 0 a) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
    exact (intervalIntegral.intervalIntegrable_rpow'
      (by linarith : -1 < r / 2 - 1)).const_mul K
  refine Integrable.mono
    (f := fun x : ℝ => C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)))
    (g := fun x : ℝ => K * x ^ (r / 2 - 1)) hlooseInt ?_ ?_
  · have hpow : ContinuousOn (fun x : ℝ => x ^ (r - 1)) (Ioc 0 a) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')
    have habslog : ContinuousOn (fun x : ℝ => |Real.log x|) (Ioc 0 a) :=
      Continuous.comp_continuousOn _root_.continuous_abs
        (Real.continuousOn_log.mono (fun x hx => hx.1.ne'))
    have hlogpow : ContinuousOn
        (fun x : ℝ => |Real.log x| ^ (q : ℝ)) (Ioc 0 a) :=
      habslog.rpow_const (fun _ _ => Or.inr (Nat.cast_nonneg q))
    exact (continuousOn_const.mul (hpow.mul hlogpow)).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := hx.1
    have hxOne : x ≤ 1 := hx.2.trans haOne
    have hlog := abs_log_rpow_nat_le_factorial_div q hr hxPos hxOne
    have htargetNonneg : 0 ≤
        C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) := by positivity
    have hlooseNonneg : 0 ≤ K * x ^ (r / 2 - 1) := by positivity
    change |C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ))| ≤
      |K * x ^ (r / 2 - 1)|
    rw [abs_of_nonneg htargetNonneg, abs_of_nonneg hlooseNonneg]
    calc
      C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) ≤
          C * (x ^ (r - 1) *
            (((q.factorial : ℝ) / (r / 2) ^ q) * x ^ (-(r / 2)))) := by
        gcongr
      _ = K * x ^ (r / 2 - 1) := by
        dsimp only [K]
        calc
          C * (x ^ (r - 1) *
                ((q.factorial : ℝ) / (r / 2) ^ q * x ^ (-(r / 2)))) =
              C * ((q.factorial : ℝ) / (r / 2) ^ q) *
                (x ^ (r - 1) * x ^ (-(r / 2))) := by ring
          _ = C * ((q.factorial : ℝ) / (r / 2) ^ q) *
                x ^ ((r - 1) + (-(r / 2))) := by
            rw [← Real.rpow_add hxPos]
          _ = C * ((q.factorial : ℝ) / (r / 2) ^ q) *
                x ^ (r / 2 - 1) := by
            congr 2
            all_goals ring

/-- Sharp eventual source estimate retaining the declared half-polylog constant. -/
theorem eventually_norm_scaled_mellin_le_halfPolylogConstant
    {q : ℕ} {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hsource : ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤
        C * mobiusLaplaceHalfPolylogKernel q x)
    (hmoment : ∀ {r : ℝ}, 0 < r →
      (∫ x : ℝ in Ioc 0 1, x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) =
        (q.factorial : ℝ) / r ^ (q + 1))
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖(r : ℂ) ^ (q + 1) *
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))‖ ≤
        C * (q.factorial : ℝ) +
          r ^ (q + 1) *
            (4 * (min (delta / 2) 1) ^ (-(1 / 2 : ℝ))) := by
  let d : ℝ := min (delta / 2) 1
  have hd : 0 < d := lt_min (half_pos hdelta) zero_lt_one
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact min_le_right (delta / 2) 1
  have hdDelta : d < delta :=
    (min_le_left (delta / 2) 1).trans_lt (half_lt_self hdelta)
  have hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q :=
    ⟨C, delta, hC, hdelta, hsource⟩
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrSmall
  have hrPos : 0 < r := hr
  have hrHalf : r < 1 / 2 := by linarith
  let s : ℂ := rho + (r : ℂ)
  have hsRe : s.re = 1 / 2 + r := by
    dsimp only [s]
    rw [Complex.add_re, Complex.ofReal_re, hrho]
  let b : ℝ := 1 / 2 + r / 2
  have hbHalf : 1 / 2 < b := by dsimp [b]; linarith
  have hbs : b < s.re := by rw [hsRe]; dsimp [b]; linarith
  have hconv : MellinConvergent mobiusDiscreteLaplaceTransform s :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := b) (by norm_num)
      mobiusDiscreteLaplaceTransform_locallyIntegrableOn
      mobiusDiscreteLaplaceTransform_isBigO_exp_neg
      (hdecay.isBigO_rpow hbHalf) hbs
  let F : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x
  have hFint : IntegrableOn F (Ioi 0) := by
    simpa only [MellinConvergent, F] using hconv
  have hFhead : IntegrableOn (fun x => ‖F x‖) (Ioc 0 d) :=
    (hFint.mono_set (by intro x hx; exact hx.1)).norm
  have hFtail : IntegrableOn (fun x => ‖F x‖) (Ioi d) :=
    (hFint.mono_set (Ioi_subset_Ioi hd.le)).norm
  have hsplit : (∫ x : ℝ in Ioi 0, ‖F x‖) =
      (∫ x : ℝ in Ioc 0 d, ‖F x‖) + ∫ x : ℝ in Ioi d, ‖F x‖ := by
    have hcover : Ioc (0 : ℝ) d ∪ Ioi d = Ioi 0 := by
      ext x
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (h | h) <;> linarith
      · intro hx
        by_cases hxd : x ≤ d
        · exact Or.inl ⟨hx, hxd⟩
        · exact Or.inr (lt_of_not_ge hxd)
    rw [← hcover]
    exact setIntegral_union (by
      rw [disjoint_left]
      intro x hx hxt
      exact (not_lt_of_ge hx.2) hxt) measurableSet_Ioi hFhead hFtail
  have hsharpInt : IntegrableOn
      (fun x : ℝ => C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)))
        (Ioc 0 d) :=
    integrableOn_halfPolylogMellinMajor q hC hrPos hd hdOne
  have hsharpIntOne : IntegrableOn
      (fun x : ℝ => C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)))
        (Ioc 0 1) :=
    integrableOn_halfPolylogMellinMajor q hC hrPos zero_lt_one le_rfl
  have hheadIntegral : (∫ x : ℝ in Ioc 0 d, ‖F x‖) ≤
      C * ((q.factorial : ℝ) / r ^ (q + 1)) := by
    calc
      (∫ x : ℝ in Ioc 0 d, ‖F x‖) ≤
          ∫ x : ℝ in Ioc 0 d,
            C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) := by
        apply MeasureTheory.integral_mono_ae hFhead hsharpInt
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxPos : 0 < x := hx.1
        have hxDelta : x < delta := hx.2.trans_lt hdDelta
        change ‖(x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x‖ ≤ _
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
          Complex.sub_re, Complex.one_re, hsRe]
        calc
          x ^ (1 / 2 + r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ≤
              x ^ (1 / 2 + r - 1) *
                (C * mobiusLaplaceHalfPolylogKernel q x) :=
            mul_le_mul_of_nonneg_left (hsource x hxPos hxDelta)
              (Real.rpow_nonneg hxPos.le _)
          _ = C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) := by
            rw [mobiusLaplaceHalfPolylogKernel]
            calc
              x ^ (1 / 2 + r - 1) *
                    (C * (x ^ (-(1 / 2 : ℝ)) * |Real.log x| ^ (q : ℝ))) =
                  C * ((x ^ (1 / 2 + r - 1) * x ^ (-(1 / 2 : ℝ))) *
                    |Real.log x| ^ (q : ℝ)) := by ring
              _ = C * (x ^ ((1 / 2 + r - 1) + (-(1 / 2 : ℝ))) *
                    |Real.log x| ^ (q : ℝ)) := by
                rw [← Real.rpow_add hxPos]
              _ = C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) := by
                congr 3
                all_goals ring
      _ ≤ ∫ x : ℝ in Ioc 0 1,
          C * (x ^ (r - 1) * |Real.log x| ^ (q : ℝ)) := by
        apply setIntegral_mono_set hsharpIntOne
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact mul_nonneg hC (mul_nonneg
            (Real.rpow_nonneg hx.1.le _)
            (Real.rpow_nonneg (abs_nonneg _) _))
        · exact Filter.Eventually.of_forall (fun x hx => Ioc_subset_Ioc_right hdOne hx)
      _ = C * ((q.factorial : ℝ) / r ^ (q + 1)) := by
        rw [MeasureTheory.integral_const_mul, hmoment hrPos]
  have htailMajorInt : IntegrableOn (fun x : ℝ => x ^ (r - 3 / 2)) (Ioi d) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hd
  have htailIntegral : (∫ x : ℝ in Ioi d, ‖F x‖) ≤
      4 * d ^ (-(1 / 2 : ℝ)) := by
    calc
      (∫ x : ℝ in Ioi d, ‖F x‖) ≤
          ∫ x : ℝ in Ioi d, x ^ (r - 3 / 2) := by
        apply MeasureTheory.integral_mono_ae hFtail htailMajorInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxPos : 0 < x := hd.trans hx
        change ‖(x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x‖ ≤ _
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
          Complex.sub_re, Complex.one_re, hsRe]
        calc
          x ^ (1 / 2 + r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ≤
              x ^ (1 / 2 + r - 1) * (1 / x) :=
            mul_le_mul_of_nonneg_left
              (norm_mobiusDiscreteLaplaceTransform_le_inv hxPos)
              (Real.rpow_nonneg hxPos.le _)
          _ = x ^ (r - 3 / 2) := by
            calc
              x ^ (1 / 2 + r - 1) * (1 / x) =
                  x ^ (1 / 2 + r - 1) * x ^ (-1 : ℝ) := by
                simp only [one_div, Real.rpow_neg_one]
              _ = x ^ ((1 / 2 + r - 1) + (-1 : ℝ)) := by
                rw [Real.rpow_add hxPos]
              _ = x ^ (r - 3 / 2) := by
                congr 1
                all_goals ring
      _ = d ^ (r - 1 / 2) / (1 / 2 - r) := by
        rw [integral_Ioi_rpow_of_lt (by linarith : r - 3 / 2 < -1) hd]
        rw [show r - 3 / 2 + 1 = r - 1 / 2 by ring]
        have hdenInv : (r - (2 : ℝ)⁻¹)⁻¹ = -((2 : ℝ)⁻¹ - r)⁻¹ := by
          rw [show r - (2 : ℝ)⁻¹ = -((2 : ℝ)⁻¹ - r) by ring, inv_neg]
        simp only [div_eq_mul_inv, one_mul]
        rw [hdenInv]
        ring
      _ ≤ 4 * d ^ (-(1 / 2 : ℝ)) := by
        have hdpow : d ^ (r - 1 / 2) ≤ d ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hd hdOne (by linarith)
        have hden : (1 / 2 - r)⁻¹ ≤ 4 := by
          rw [← one_div]
          apply (div_le_iff₀ (by linarith : 0 < 1 / 2 - r)).2
          linarith
        rw [div_eq_mul_inv]
        calc
          d ^ (r - 1 / 2) * (1 / 2 - r)⁻¹ ≤
              d ^ (-(1 / 2 : ℝ)) * (1 / 2 - r)⁻¹ :=
            mul_le_mul_of_nonneg_right hdpow (by positivity)
          _ ≤ d ^ (-(1 / 2 : ℝ)) * 4 :=
            mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hd.le _)
          _ = 4 * d ^ (-(1 / 2 : ℝ)) := by ring
  have hmellinNorm : ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
      C * ((q.factorial : ℝ) / r ^ (q + 1)) +
        4 * d ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
          ∫ x : ℝ in Ioi 0, ‖F x‖ := by
        rw [mellin]
        exact norm_integral_le_integral_norm _
      _ = (∫ x : ℝ in Ioc 0 d, ‖F x‖) +
          ∫ x : ℝ in Ioi d, ‖F x‖ := hsplit
      _ ≤ C * ((q.factorial : ℝ) / r ^ (q + 1)) +
          4 * d ^ (-(1 / 2 : ℝ)) :=
        add_le_add hheadIntegral htailIntegral
  change ‖(r : ℂ) ^ (q + 1) *
      mellin mobiusDiscreteLaplaceTransform s‖ ≤ _
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
  calc
    r ^ (q + 1) * ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
        r ^ (q + 1) *
          (C * ((q.factorial : ℝ) / r ^ (q + 1)) +
            4 * d ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hmellinNorm (pow_nonneg hrPos.le _)
    _ = C * (q.factorial : ℝ) +
        r ^ (q + 1) * (4 * d ^ (-(1 / 2 : ℝ))) := by
      field_simp [hrPos.ne']
    _ = C * (q.factorial : ℝ) +
        r ^ (q + 1) *
          (4 * (min (delta / 2) 1) ^ (-(1 / 2 : ℝ))) := rfl

private theorem tendsto_critical_ray (rho : ℂ) :
    Tendsto (fun r : ℝ => rho + (r : ℂ)) (𝓝[>] 0) (𝓝 rho) := by
  simpa using!
    ((continuous_const.add Complex.continuous_ofReal).tendsto 0).mono_left
      nhdsWithin_le_nhds

/-- A sharp scaled-Mellin upper bound controls the top local zeta coefficient. -/
private theorem norm_Gamma_div_localFactor_le_of_sharpPolylogAbel
    {q : ℕ} {C B : ℝ} {rho : ℂ} {p : ℂ → ℂ}
    (hrho : rho.re = 1 / 2)
    (hp : AnalyticAt ℂ p rho) (hpzero : p rho ≠ 0)
    (hfactor : riemannZeta =ᶠ[𝓝 rho]
      fun z : ℂ => (z - rho) ^ (q + 1) * p z)
    (hGanalytic : AnalyticOnNhd ℂ
      (mellin mobiusDiscreteLaplaceTransform) rightHalf)
    (hsharp : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖(r : ℂ) ^ (q + 1) *
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))‖ ≤
        C * (q.factorial : ℝ) + r ^ (q + 1) * B) :
    ‖Complex.Gamma rho / p rho‖ ≤ C * (q.factorial : ℝ) := by
  have hray := tendsto_critical_ray rho
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
  have hfactorRay : ∀ᶠ r : ℝ in 𝓝[>] 0,
      riemannZeta (rho + (r : ℂ)) =
        ((r : ℂ) ^ (q + 1)) * p (rho + (r : ℂ)) := by
    have h := hray.eventually hfactor
    filter_upwards [h] with r hr
    simpa using hr
  have hpRay : Tendsto (fun r : ℝ => p (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 (p rho)) := hp.continuousAt.tendsto.comp hray
  have hpRayNe : ∀ᶠ r : ℝ in 𝓝[>] 0, p (rho + (r : ℂ)) ≠ 0 :=
    hpRay.eventually (isOpen_ne.mem_nhds hpzero)
  have hnotOne : ∀ᶠ r : ℝ in 𝓝[>] 0, rho + (r : ℂ) ≠ 1 :=
    hray.eventually (isOpen_compl_singleton.mem_nhds hrhoOne)
  have hscaledEq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (r : ℂ) ^ (q + 1) *
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) =
        Complex.Gamma (rho + (r : ℂ)) / p (rho + (r : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin, hfactorRay, hpRayNe, hnotOne]
      with r hr hfac hpne hsone
    have hright : rho + (r : ℂ) ∈ rightHalf := by
      rw [mem_rightHalf, Complex.add_re, Complex.ofReal_re, hrho]
      norm_num
      exact hr
    have hcanonical :=
      mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_analyticOnNhd
        hGanalytic (rho + (r : ℂ)) hright
    simp only [zetaResidueUnit, Function.update_of_ne hsone] at hcanonical
    have hcancel :
        mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
            riemannZeta (rho + (r : ℂ)) =
          Complex.Gamma (rho + (r : ℂ)) := by
      apply mul_right_cancel₀ (sub_ne_zero.mpr hsone)
      calc
        (mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
              riemannZeta (rho + (r : ℂ))) *
            (rho + (r : ℂ) - 1) =
            mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
              ((rho + (r : ℂ) - 1) *
                riemannZeta (rho + (r : ℂ))) := by ring
        _ = Complex.Gamma (rho + (r : ℂ)) *
            (rho + (r : ℂ) - 1) := hcanonical
    apply (eq_div_iff hpne).2
    rw [hfac] at hcancel
    calc
      ((r : ℂ) ^ (q + 1) *
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))) *
          p (rho + (r : ℂ)) =
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
            ((r : ℂ) ^ (q + 1) * p (rho + (r : ℂ))) := by ring
      _ = Complex.Gamma (rho + (r : ℂ)) := hcancel
  have hnotGammaPole : ∀ m : ℕ, rho ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hgammaRay : Tendsto (fun r : ℝ => Complex.Gamma (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 (Complex.Gamma rho)) :=
    (Complex.continuousAt_Gamma rho hnotGammaPole).tendsto.comp hray
  have hscaled : Tendsto
      (fun r : ℝ => (r : ℂ) ^ (q + 1) *
        mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 (Complex.Gamma rho / p rho)) := by
    refine (hgammaRay.div hpRay hpzero).congr' ?_
    filter_upwards [hscaledEq] with r hr
    exact hr.symm
  have hrZero : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hrPowZero : Tendsto (fun r : ℝ => r ^ (q + 1))
      (𝓝[>] 0) (𝓝 0) := by
    have h := hrZero.pow (q + 1)
    simpa [zero_pow (by omega : q + 1 ≠ 0)] using h
  have hupper : Tendsto
      (fun r : ℝ => C * (q.factorial : ℝ) + r ^ (q + 1) * B)
      (𝓝[>] 0) (𝓝 (C * (q.factorial : ℝ))) := by
    simpa using tendsto_const_nhds.add (hrPowZero.mul tendsto_const_nhds)
  exact le_of_tendsto_of_tendsto hscaled.norm hupper hsharp

/-- **Sharp maximal-order coefficient law.** If a declared degree-`q` half-polylog
Möbius--Laplace bound is saturated by a critical zeta zero of order `q + 1`, its canonical
local factor has coefficient bounded by the same source constant times `q!`. -/
theorem exists_localFactor_with_Gamma_cap_of_halfPolylog_maximalOrder
    {q : ℕ} {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hsource : ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤
        C * mobiusLaplaceHalfPolylogKernel q x)
    {rho : ℂ} (hrho : rho.re = 1 / 2)
    (horder : analyticOrderAt riemannZeta rho = ((q + 1 : ℕ) : ℕ∞)) :
    ∃ p : ℂ → ℂ,
      AnalyticAt ℂ p rho ∧ p rho ≠ 0 ∧
      riemannZeta =ᶠ[𝓝 rho]
        (fun z : ℂ => (z - rho) ^ (q + 1) * p z) ∧
      ‖Complex.Gamma rho / p rho‖ ≤ C * (q.factorial : ℝ) := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho hrhoOne
  obtain ⟨p, hp, hpzero, hfactor⟩ :=
    (hzetaAnalytic.analyticOrderAt_eq_natCast).mp horder
  have hfactorMul : riemannZeta =ᶠ[𝓝 rho]
      (fun z : ℂ => (z - rho) ^ (q + 1) * p z) := by
    filter_upwards [hfactor] with z hz
    simpa [smul_eq_mul] using hz
  have hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q :=
    ⟨C, delta, hC, hdelta, hsource⟩
  have hsharp := eventually_norm_scaled_mellin_le_halfPolylogConstant
    hC hdelta hsource
      (fun {r} hr => by
        exact exact_log_mellin_moment q hr)
      hrho
  refine ⟨p, hp, hpzero, hfactorMul, ?_⟩
  exact norm_Gamma_div_localFactor_le_of_sharpPolylogAbel
    hrho hp hpzero hfactorMul
      (analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_halfPolylog hdecay)
      hsharp

end

end RHTower
