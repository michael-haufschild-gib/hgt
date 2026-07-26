import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Fixed polylogarithmic losses still imply the Möbius--Laplace Mellin wall

Liflandsky's source criterion asks for `O(x⁻¹ᐟ²)` decay of the discrete Möbius--Laplace
transform.  A fixed power of `|log x|` is smaller than every negative power at `0+`.  Consequently
the same Mellin transform is analytic at each point of `Re s > 1/2` under the strictly weaker
bound

`O(x⁻¹ᐟ² |log x|^q)`

for any fixed natural `q`.  The existing denominator-free identity-theorem connector then gives
the Mellin continuation wall and RH.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- Critical half-power kernel with a fixed polylogarithmic loss. -/
def mobiusLaplaceHalfPolylogKernel (q : ℕ) (x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * |Real.log x| ^ (q : ℝ)

/-- A fixed-polylog weakening of the Möbius--Laplace half-decay source statement. -/
def MobiusDiscreteLaplaceHalfPolylogDecay (q : ℕ) : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * mobiusLaplaceHalfPolylogKernel q x

/-- The explicit local bound gives the corresponding filter-form asymptotic estimate. -/
theorem MobiusDiscreteLaplaceHalfPolylogDecay.isBigO_kernel {q : ℕ}
    (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) :
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0]
      (mobiusLaplaceHalfPolylogKernel q) := by
  rcases hdecay with ⟨C, delta, hC, hdelta, hbound⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < delta :=
    (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxd
  have hxpos : 0 < x := hx
  have hkernel : 0 ≤ mobiusLaplaceHalfPolylogKernel q x := by
    exact mul_nonneg (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  calc
    ‖mobiusDiscreteLaplaceTransform x‖
        ≤ C * mobiusLaplaceHalfPolylogKernel q x := hbound x hxpos hxd
    _ = C * ‖mobiusLaplaceHalfPolylogKernel q x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hkernel]

/-- Every fixed half-polylog kernel is `O(x⁻ᵇ)` for each strict exponent `b > 1/2`. -/
theorem mobiusLaplaceHalfPolylogKernel_isBigO_rpow {q : ℕ} {b : ℝ}
    (hb : 1 / 2 < b) :
    mobiusLaplaceHalfPolylogKernel q =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  have hlog :
      (fun x : ℝ => |Real.log x| ^ (q : ℝ)) =O[𝓝[>] 0]
        (fun x : ℝ => x ^ (1 / 2 - b)) :=
    (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (q : ℝ) (by linarith)).isBigO
  have hpow :
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) =O[𝓝[>] 0]
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := isBigO_refl _ _
  have hmul := hpow.mul hlog
  refine hmul.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  rw [← Real.rpow_add hxpos]
  congr 1
  ring

/-- Half-polylog decay yields every strict power estimate above the critical exponent. -/
theorem MobiusDiscreteLaplaceHalfPolylogDecay.isBigO_rpow {q : ℕ}
    (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) {b : ℝ}
    (hb : 1 / 2 < b) :
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) :=
  hdecay.isBigO_kernel.trans (mobiusLaplaceHalfPolylogKernel_isBigO_rpow hb)

/-- A fixed polylogarithmic loss still makes the concrete Mellin transform analytic on the full
strict right half-plane.  The power margin may depend on the Mellin point. -/
theorem analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_halfPolylog
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) :
    AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_rightHalf
  let b : ℝ := (1 / 2 + s.re) / 2
  have hhalf : 1 / 2 < b := by
    dsimp [b]
    linarith [mem_rightHalf.mp hs]
  have hbs : b < s.re := by
    dsimp [b]
    linarith [mem_rightHalf.mp hs]
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := b) (by norm_num)
    mobiusDiscreteLaplaceTransform_locallyIntegrableOn
    mobiusDiscreteLaplaceTransform_isBigO_exp_neg
    (hdecay.isBigO_rpow hhalf) hbs).differentiableWithinAt

/-- **Half-polylog continuation theorem.** Any fixed logarithmic loss discharges the same
denominator-free Mellin wall as exact half-decay. -/
theorem mobiusLaplaceMellinContinuationWall_of_halfPolylog
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) :
    MobiusLaplaceMellinContinuationWall := by
  let G : ℂ → ℂ := mellin mobiusDiscreteLaplaceTransform
  have hG : AnalyticOnNhd ℂ G rightHalf :=
    analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_halfPolylog hdecay
  have hleft : AnalyticOnNhd ℂ
      (fun s => G s * zetaResidueUnit s) rightHalf := by
    intro s hs
    exact (hG s hs).mul (RHTower.analyticAt_zetaResidueUnit s)
  have hright : AnalyticOnNhd ℂ
      (fun s => Complex.Gamma s * (s - 1)) rightHalf := by
    intro s hs
    have hspos : 0 < s.re := lt_trans (by norm_num) (mem_rightHalf.mp hs)
    exact (HTGeometry.analyticAt_Gamma_of_re_pos hspos).mul
      (analyticAt_id.sub analyticAt_const)
  have hevent :
      (fun s => G s * zetaResidueUnit s) =ᶠ[𝓝 (2 : ℂ)]
        (fun s => Complex.Gamma s * (s - 1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro hsone
      subst s
      norm_num at hs
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    rw [show G s = Complex.Gamma s * (riemannZeta s)⁻¹ by
      simpa [G] using mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta hs]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp
  refine ⟨G, hG, ?_⟩
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    convex_rightHalf.isPreconnected two_mem_rightHalf hevent

/-- **Fixed-polylog Möbius--Laplace criterion for RH.**  For any natural `q`, the bound
`O(x⁻¹ᐟ² |log x|^q)` at `0+` implies the Riemann hypothesis. -/
theorem mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) :
    RiemannHypothesis :=
  mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis
    (mobiusLaplaceMellinContinuationWall_of_halfPolylog hdecay)

/-- The degree-`q` critical radial Mellin family is locally bounded after multiplication by
the sharp radial power `q + 1`. -/
def MobiusLaplaceCriticalPolylogAbelBound (q : ℕ) (rho : ℂ) : Prop :=
  IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
    (norm ∘ fun r : ℝ =>
      (r : ℂ) ^ (q + 1) *
        mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)))

/-- Exponential domination of a logarithmic power, with its dependence on the radial exponent
kept explicit. -/
private theorem abs_log_rpow_nat_le_factorial_div
    (q : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) (hxOne : x ≤ 1) :
    |Real.log x| ^ (q : ℝ) ≤
      ((q.factorial : ℝ) / (r / 2) ^ q) * x ^ (-(r / 2)) := by
  have hlog : 0 ≤ -Real.log x := by
    exact neg_nonneg.mpr (Real.log_nonpos hx.le hxOne)
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

/-- **Sharp source-to-polylog-Abel estimate.** A degree-`q` logarithmic loss gives at most a
`q + 1` radial pole at every critical-line point. -/
theorem mobiusLaplaceCriticalPolylogAbelBound_of_halfPolylog
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) {rho : ℂ}
    (hrho : rho.re = 1 / 2) :
    MobiusLaplaceCriticalPolylogAbelBound q rho := by
  have hdecay0 := hdecay
  rcases hdecay with ⟨C, delta, hC, hdelta, hsource⟩
  let d : ℝ := min (delta / 2) 1
  have hd : 0 < d := lt_min (half_pos hdelta) zero_lt_one
  have hdOne : d ≤ 1 := min_le_right _ _
  have hdDelta : d < delta :=
    (min_le_left (delta / 2) 1).trans_lt (half_lt_self hdelta)
  rw [MobiusLaplaceCriticalPolylogAbelBound]
  let A : ℝ := C * (q.factorial : ℝ) * (2 : ℝ) ^ (q + 1) +
    4 * d ^ (-(1 / 2 : ℝ))
  apply isBoundedUnder_of_eventually_le (a := A)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrSmall
  have hrPos : 0 < r := hr
  have hrHalf : r < 1 / 2 := by linarith
  have hrOne : r ≤ 1 := by linarith
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
      (hdecay0.isBigO_rpow hbHalf) hbs
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
  let K : ℝ := C * ((q.factorial : ℝ) / (r / 2) ^ q)
  have hK : 0 ≤ K := by positivity
  have hheadMajorInt : IntegrableOn
      (fun x : ℝ => K * x ^ (r / 2 - 1)) (Ioc 0 d) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mp
    exact (intervalIntegral.intervalIntegrable_rpow'
      (by linarith : -1 < r / 2 - 1)).const_mul K
  have hheadIntegral : (∫ x : ℝ in Ioc 0 d, ‖F x‖) ≤ K * (2 / r) := by
    have hdPow : d ^ (r / 2) ≤ 1 :=
      Real.rpow_le_one hd.le hdOne (by positivity)
    calc
      (∫ x : ℝ in Ioc 0 d, ‖F x‖) ≤
          ∫ x : ℝ in Ioc 0 d, K * x ^ (r / 2 - 1) := by
        apply MeasureTheory.integral_mono_ae hFhead hheadMajorInt
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxPos : 0 < x := hx.1
        have hxOne : x ≤ 1 := hx.2.trans hdOne
        have hxDelta : x < delta := hx.2.trans_lt hdDelta
        have hlog := abs_log_rpow_nat_le_factorial_div q hrPos hxPos hxOne
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
          _ ≤ C * (x ^ (r - 1) *
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
      _ = K * (d ^ (r / 2) / (r / 2)) := by
        rw [← intervalIntegral.integral_of_le hd.le,
          intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith : -1 < r / 2 - 1))]
        rw [show r / 2 - 1 + 1 = r / 2 by ring,
          Real.zero_rpow (by positivity : r / 2 ≠ 0), sub_zero]
      _ ≤ K * (1 / (r / 2)) := by gcongr
      _ = K * (2 / r) := by field_simp
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
        rw [show r - 1 / 2 = -(1 / 2 - r) by ring, neg_div_neg_eq]
      _ ≤ 4 * d ^ (-(1 / 2 : ℝ)) := by
        have hdpow : d ^ (r - 1 / 2) ≤ d ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hd hdOne (by linarith)
        have hden : 1 / (1 / 2 - r) ≤ 4 := by
          apply (div_le_iff₀ (by linarith : 0 < 1 / 2 - r)).2
          linarith
        have hden' : (1 / 2 - r)⁻¹ ≤ 4 := by
          simpa only [one_div] using hden
        rw [div_eq_mul_inv]
        calc
          d ^ (r - 1 / 2) * (1 / 2 - r)⁻¹ ≤
              d ^ (-(1 / 2 : ℝ)) * (1 / 2 - r)⁻¹ :=
            mul_le_mul_of_nonneg_right hdpow (by positivity)
          _ ≤ d ^ (-(1 / 2 : ℝ)) * 4 :=
            mul_le_mul_of_nonneg_left hden' (Real.rpow_nonneg hd.le _)
          _ = 4 * d ^ (-(1 / 2 : ℝ)) := by ring
  have hmellinNorm : ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
      K * (2 / r) + 4 * d ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
          ∫ x : ℝ in Ioi 0, ‖F x‖ := by
        rw [mellin]
        exact norm_integral_le_integral_norm _
      _ = (∫ x : ℝ in Ioc 0 d, ‖F x‖) +
          ∫ x : ℝ in Ioi d, ‖F x‖ := hsplit
      _ ≤ K * (2 / r) + 4 * d ^ (-(1 / 2 : ℝ)) :=
        add_le_add hheadIntegral htailIntegral
  have hscaledHead : r ^ (q + 1) * (K * (2 / r)) =
      C * (q.factorial : ℝ) * (2 : ℝ) ^ (q + 1) := by
    dsimp only [K]
    rw [pow_succ, pow_succ]
    field_simp [hrPos.ne']
    ring_nf
    conv_rhs => rw [mul_assoc, ← mul_pow]
    norm_num
  have hrPow : r ^ (q + 1) ≤ 1 :=
    pow_le_one₀ hrPos.le hrOne
  change ‖(r : ℂ) ^ (q + 1) *
      mellin mobiusDiscreteLaplaceTransform s‖ ≤ A
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
  calc
    r ^ (q + 1) * ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
        r ^ (q + 1) * (K * (2 / r) + 4 * d ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hmellinNorm (pow_nonneg hrPos.le _)
    _ = r ^ (q + 1) * (K * (2 / r)) +
        r ^ (q + 1) * (4 * d ^ (-(1 / 2 : ℝ))) := by ring
    _ ≤ C * (q.factorial : ℝ) * (2 : ℝ) ^ (q + 1) +
        4 * d ^ (-(1 / 2 : ℝ)) := by
      rw [hscaledHead]
      apply add_le_add_right
      calc
        r ^ (q + 1) * (4 * d ^ (-(1 / 2 : ℝ))) ≤
            1 * (4 * d ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hrPow (by positivity)
        _ = 4 * d ^ (-(1 / 2 : ℝ)) := one_mul _
    _ = A := rfl

end

end RHTower
