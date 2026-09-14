import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareEnergyWidthCollision
import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH

open Complex Filter Asymptotics Topology ArithmeticFunction MeasureTheory

namespace RHTower

noncomputable section

/-- A Xi right-half-plane bound gives the matching zero-free half-plane for zeta. -/
theorem riemannZeta_ne_zero_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha) {s : ℂ}
    (hs : 1 / 2 + alpha < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  rcases riemannZeta_eq_zero_iff_xi_or_trivial.mp hz with hxi | ⟨n, hn⟩
  · linarith [hXi s hxi]
  · rw [hn] at hs
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp at hs
    linarith

/-- A zeta zero with nonzero ordinate obeys every supplied Xi half-plane bound. -/
theorem riemannZeta_zero_re_le_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (hXi : XiZeroHalfPlaneBound alpha) {rho : ℂ}
    (hz : riemannZeta rho = 0) (him : rho.im ≠ 0) :
    rho.re ≤ 1 / 2 + alpha := by
  rcases riemannZeta_eq_zero_iff_xi_or_trivial.mp hz with hxi | ⟨n, hn⟩
  · exact hXi rho hxi
  · exfalso
    apply him
    rw [hn]
    simp

namespace Sieve

/-- Logarithmic-derivative bound to the right of an arbitrary Xi zero frontier. -/
theorem exists_logDeriv_zeta_bound_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma gamma : ℝ, 7 ≤ |gamma| →
      1 / 2 + alpha < sigma → sigma ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((sigma : ℂ) + (gamma : ℂ) * Complex.I)‖
        ≤ C * Real.log |gamma| / (sigma - (1 / 2 + alpha)) := by
  obtain ⟨D, hD0, hdata⟩ := exists_crit_landau_data
  obtain ⟨E, hE0, hcount⟩ := exists_crit_zero_count
  refine ⟨D + 50 * D + 50 * (8 + E), by positivity, ?_⟩
  intro sigma gamma hgamma hsigma0 hsigma1
  have hgamma0 : (0 : ℝ) < |gamma| := by linarith
  have hloggamma : (1 : ℝ) ≤ Real.log |gamma| := by
    have he : Real.exp 1 < 7 := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ |gamma|)
    rwa [Real.log_exp] at h
  have hgammanz : gamma ≠ 0 := by
    intro h
    rw [h] at hgamma
    norm_num at hgamma
  set z : ℂ := (sigma : ℂ) + (gamma : ℂ) * Complex.I with hzdef
  have hzre : z.re = sigma := by rw [hzdef]; simp
  have hzim : z.im = gamma := by rw [hzdef]; simp
  have hzc : ‖z - critCentre gamma‖ ≤ 5 / 8 := by
    have hdiff : z - critCentre gamma = (((sigma - 9 / 8 : ℝ)) : ℂ) := by
      rw [hzdef, critCentre]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzne : riemannZeta z ≠ 0 := by
    apply riemannZeta_ne_zero_of_xiZeroHalfPlaneBound halpha hXi
    rw [hzre]
    exact hsigma0
  obtain ⟨Z, m, h1, h2, _h3, _h4, h5⟩ := hdata gamma hgamma
  have hkeyc : ‖logDeriv riemannZeta (critCentre gamma)
      - ∑ rho ∈ Z, (m rho : ℂ) / (critCentre gamma - rho)‖ ≤ D * Real.log |gamma| := by
    refine h5 (critCentre gamma) (by rw [sub_self, norm_zero]; norm_num) ?_
    exact zeta_critCentre_ne_zero gamma
  have hcnt := hcount gamma hgamma Z m D h1 h2 hkeyc
  have hdist : ∀ rho ∈ Z, sigma - (1 / 2 + alpha) ≤ ‖z - rho‖ := by
    intro rho hrho
    have hrhoim : rho.im ≠ 0 := by
      have hd : |rho.im - gamma| ≤ ‖rho - critCentre gamma‖ := by
        have h := Complex.abs_im_le_norm (rho - critCentre gamma)
        rwa [Complex.sub_im, critCentre_im] at h
      have hb := h1 rho hrho
      intro hcon
      rw [hcon] at hd
      simp only [zero_sub, abs_neg] at hd
      linarith
    have hre := riemannZeta_zero_re_le_of_xiZeroHalfPlaneBound hXi (h2 rho hrho) hrhoim
    have h := Complex.abs_re_le_norm (z - rho)
    rw [Complex.sub_re, hzre] at h
    have hnonneg : 0 ≤ sigma - rho.re := by linarith
    rw [abs_of_nonneg hnonneg] at h
    linarith
  have hsum : ‖∑ rho ∈ Z, (m rho : ℂ) / (z - rho)‖
      ≤ (∑ rho ∈ Z, (m rho : ℝ)) / (sigma - (1 / 2 + alpha)) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun rho hrho => ?_
    rw [norm_div, Complex.norm_natCast]
    have hd := hdist rho hrho
    have hpos : (0 : ℝ) < sigma - (1 / 2 + alpha) := by linarith
    have hzr : (0 : ℝ) < ‖z - rho‖ := by linarith
    rw [div_le_div_iff₀ hzr hpos]
    have hm0 : (0 : ℝ) ≤ (m rho : ℝ) := Nat.cast_nonneg _
    nlinarith [hd, hm0]
  have hkeyz := h5 z hzc hzne
  have hsplit : ‖logDeriv riemannZeta z‖
      ≤ ‖logDeriv riemannZeta z - ∑ rho ∈ Z, (m rho : ℂ) / (z - rho)‖
        + ‖∑ rho ∈ Z, (m rho : ℂ) / (z - rho)‖ := by
    simpa using norm_add_le
      (logDeriv riemannZeta z - ∑ rho ∈ Z, (m rho : ℂ) / (z - rho))
      (∑ rho ∈ Z, (m rho : ℂ) / (z - rho))
  have hpos : (0 : ℝ) < sigma - (1 / 2 + alpha) := by linarith
  have hdelta1 : sigma - (1 / 2 + alpha) ≤ 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hsumb : (∑ rho ∈ Z, (m rho : ℝ)) / (sigma - (1 / 2 + alpha))
      ≤ (50 * (D * Real.log |gamma|) + 50 * (8 + E)) /
        (sigma - (1 / 2 + alpha)) := by gcongr
  have hchain : ‖logDeriv riemannZeta z‖
      ≤ D * Real.log |gamma| +
        (50 * (D * Real.log |gamma|) + 50 * (8 + E)) /
          (sigma - (1 / 2 + alpha)) := by
    linarith [hsplit, hkeyz, hsum, hsumb]
  have hmul : ‖logDeriv riemannZeta z‖ * (sigma - (1 / 2 + alpha))
      ≤ (D * Real.log |gamma| +
          (50 * (D * Real.log |gamma|) + 50 * (8 + E)) /
            (sigma - (1 / 2 + alpha))) * (sigma - (1 / 2 + alpha)) :=
    mul_le_mul_of_nonneg_right hchain hpos.le
  have hid : (D * Real.log |gamma| +
        (50 * (D * Real.log |gamma|) + 50 * (8 + E)) /
          (sigma - (1 / 2 + alpha))) * (sigma - (1 / 2 + alpha))
      = D * Real.log |gamma| * (sigma - (1 / 2 + alpha)) +
        (50 * (D * Real.log |gamma|) + 50 * (8 + E)) := by
    rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  rw [hid] at hmul
  refine hmul.trans ?_
  nlinarith [hloggamma, hD0, hE0, hdelta1, hpos,
    mul_nonneg hD0.le (by linarith : (0 : ℝ) ≤ Real.log |gamma|)]

/-- The logarithmic derivative is continuous on compact segments right of a Xi frontier. -/
theorem continuousOn_logDeriv_zeta_segment_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
    {sigma : ℝ} (hsigma0 : 1 / 2 + alpha < sigma) (hsigma1 : sigma < 1) (T : ℝ) :
    ContinuousOn
      (fun t : ℝ => logDeriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (-T) T) := by
  intro t _
  have hre : ((sigma : ℂ) + (t : ℂ) * Complex.I).re = sigma := by simp
  have hne1 : ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    rw [hcon] at hre
    simp only [Complex.one_re] at hre
    linarith
  have hzne : riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_xiZeroHalfPlaneBound halpha hXi
    rw [hre]
    exact hsigma0
  have hcont : ContinuousAt
      (fun t : ℝ => logDeriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)) t := by
    have hinner : ContinuousAt
        (fun t : ℝ => ((sigma : ℂ) + (t : ℂ) * Complex.I)) t := by fun_prop
    have hout : ContinuousAt (logDeriv riemannZeta)
        ((sigma : ℂ) + (t : ℂ) * Complex.I) := by
      have hd : DifferentiableAt ℂ (fun s : ℂ => deriv riemannZeta s / riemannZeta s)
          ((sigma : ℂ) + (t : ℂ) * Complex.I) :=
        (differentiableAt_deriv_riemannZeta hne1).div
          (differentiableAt_riemannZeta hne1) hzne
      have hfun : (fun s : ℂ => deriv riemannZeta s / riemannZeta s) =
          logDeriv riemannZeta := by
        funext s
        rw [logDeriv_apply]
      rw [hfun] at hd
      exact hd.continuousAt
    exact ContinuousAt.comp (g := logDeriv riemannZeta)
      (f := fun t : ℝ => (sigma : ℂ) + (t : ℂ) * Complex.I) hout hinner
  exact hcont.continuousWithinAt

/-- Uniform logarithmic-derivative bound on a fixed line right of a Xi frontier. -/
theorem exists_logDeriv_zeta_line_bound_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
    {sigma : ℝ} (hsigma0 : 1 / 2 + alpha < sigma) (hsigma1 : sigma < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ K * (1 + Real.log (2 + |t|)) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_logDeriv_zeta_bound_of_xiZeroHalfPlaneBound halpha hXi
  obtain ⟨K0, hK0⟩ :=
    (isCompact_Icc (a := (-7 : ℝ)) (b := 7)).exists_bound_of_continuousOn
      ((continuousOn_logDeriv_zeta_segment_of_xiZeroHalfPlaneBound
        halpha hXi hsigma0 hsigma1 7).norm)
  refine ⟨max K0 (C / (sigma - (1 / 2 + alpha))) + 1, by positivity, ?_⟩
  intro t
  have hlogpos : (0 : ℝ) ≤ Real.log (2 + |t|) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  rcases le_or_gt |t| 7 with hle | hgt
  · have hmem : t ∈ Set.Icc (-7 : ℝ) 7 := by
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have h : ‖logDeriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K0 := by
      simpa using hK0 t hmem
    have hK0le : K0 ≤ max K0 (C / (sigma - (1 / 2 + alpha))) := le_max_left _ _
    have hCpos : (0 : ℝ) < C / (sigma - (1 / 2 + alpha)) := by positivity
    have hmax0 : (0 : ℝ) < max K0 (C / (sigma - (1 / 2 + alpha))) :=
      lt_of_lt_of_le hCpos (le_max_right _ _)
    nlinarith [h, hlogpos, hK0le, hmax0]
  · have hb := hC sigma t (by linarith) hsigma0 (by linarith)
    have hlog7 : (1 : ℝ) ≤ Real.log |t| := by
      have he : Real.exp 1 < 7 := by
        have := Real.exp_one_lt_d9
        linarith
      have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ |t|)
      rwa [Real.log_exp] at h
    have hmono : Real.log |t| ≤ Real.log (2 + |t|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hpos : (0 : ℝ) < sigma - (1 / 2 + alpha) := by linarith
    have hle : C * Real.log |t| / (sigma - (1 / 2 + alpha))
        ≤ (C / (sigma - (1 / 2 + alpha))) * Real.log (2 + |t|) := by
      have hid : C * Real.log |t| / (sigma - (1 / 2 + alpha)) =
          (C / (sigma - (1 / 2 + alpha))) * Real.log |t| := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have hKle : C / (sigma - (1 / 2 + alpha))
        ≤ max K0 (C / (sigma - (1 / 2 + alpha))) := le_max_right _ _
    have hCpos : (0 : ℝ) < C / (sigma - (1 / 2 + alpha)) := by positivity
    nlinarith [hb, hle, hKle, hlogpos, hCpos]

/-- Perron rectangle residue formula right of an arbitrary Xi frontier. -/
theorem rectangleIntegral_perron_eq_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
    {x : ℝ} (hx : 0 < x) {sigma1 sigma0 T : ℝ}
    (hsigma1 : 1 / 2 + alpha < sigma1) (hsigma11 : sigma1 < 1)
    (hsigma0 : 1 < sigma0) (hT : 0 < T) :
    RectangleIntegral'
        (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
        ((sigma1 : ℂ) - Complex.I * (T : ℂ))
        ((sigma0 : ℂ) + Complex.I * (T : ℂ)) = (x : ℂ) := by
  have hzre : ((sigma1 : ℂ) - Complex.I * (T : ℂ)).re = sigma1 := by simp
  have hzim : ((sigma1 : ℂ) - Complex.I * (T : ℂ)).im = -T := by simp
  have hwre : ((sigma0 : ℂ) + Complex.I * (T : ℂ)).re = sigma0 := by simp
  have hwim : ((sigma0 : ℂ) + Complex.I * (T : ℂ)).im = T := by simp
  refine ResidueTheoremOnRectangleWithSimplePole' (p := 1) (A := (x : ℂ))
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) ?_ ?_
    (perron_integrand_residue hx)
  · rw [rectangle_mem_nhds_iff, hzre, hzim, hwre, hwim]
    constructor
    · rw [Set.uIoo_of_le (by linarith : sigma1 ≤ sigma0)]
      exact ⟨by simpa using hsigma11, by simpa using hsigma0⟩
    · rw [Set.uIoo_of_le (by linarith : -T ≤ T)]
      exact ⟨by simpa using (by linarith : -T < (0 : ℝ)), by simpa using hT⟩
  · intro s hs
    have hs1 : s ≠ 1 := hs.2
    have hsre : 1 / 2 + alpha < s.re := by
      have h := hs.1.1
      rw [hzre, hwre, Set.uIcc_of_le (by linarith)] at h
      linarith [h.1]
    have hzne : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_xiZeroHalfPlaneBound halpha hXi hsre
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hsre
      simp at hsre
      linarith
    have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
    refine DifferentiableWithinAt.mul ?_ ?_
    · exact ((differentiableAt_deriv_riemannZeta hs1).neg.div
        (differentiableAt_riemannZeta hs1) hzne).differentiableWithinAt
    · exact ((differentiableAt_id.const_cpow (Or.inl hxne)).div
        differentiableAt_id hs0).differentiableWithinAt

/-- Shifted Perron contour assembled right of an arbitrary Xi frontier. -/
theorem norm_vIntegral'_perron_sub_le_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
    {x : ℝ} (hx : 0 < x) {sigma1 sigma0 T : ℝ}
    (hsigma1 : 1 / 2 + alpha < sigma1) (hsigma11 : sigma1 < 1)
    (hsigma0 : 1 < sigma0) (hT : 0 < T) :
    ‖VIntegral'
        (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
          sigma0 (-T) T - (x : ℂ)‖
      ≤ (1 / (2 * Real.pi)) *
        (‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
              ((x : ℂ) ^ s / s)) sigma1 (-T) T‖
          + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
              ((x : ℂ) ^ s / s)) sigma1 sigma0 T‖
          + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
              ((x : ℂ) ^ s / s)) sigma1 sigma0 (-T)‖) := by
  set f : ℂ → ℂ := fun s : ℂ =>
    (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) with hf
  have hshift := vIntegral_shift f sigma1 sigma0 T
  have hres := rectangleIntegral_perron_eq_of_xiZeroHalfPlaneBound
    halpha hXi hx hsigma1 hsigma11 hsigma0 hT
  have hexp : VIntegral' f sigma0 (-T) T - (x : ℂ) =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (VIntegral f sigma1 (-T) T + HIntegral f sigma1 sigma0 T -
          HIntegral f sigma1 sigma0 (-T)) := by
    rw [VIntegral', hshift, ← hres, RectangleIntegral', ← hf, ← smul_sub]
    congr 1
    ring
  rw [hexp, norm_smul, norm_two_pi_I_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (norm_sub_le _ _) (add_le_add (le_trans (norm_add_le _ _) (by linarith)) le_rfl)

/-- Perron integrand continuity on a line right of an arbitrary Xi frontier. -/
theorem continuous_perron_integrand_line_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
    {x sigma : ℝ} (hx : 0 < x) (hsigma0 : 1 / 2 + alpha < sigma)
    (hsigma1 : sigma < 1) :
    Continuous fun t : ℝ =>
      (-deriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)) *
        ((x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I) /
          ((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hre : ((sigma : ℂ) + (t : ℂ) * Complex.I).re = sigma := by simp
  have hne1 : ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    rw [hcon] at hre
    simp only [Complex.one_re] at hre
    linarith
  have hne0 : ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro hcon
    rw [hcon] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have hzne : riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_xiZeroHalfPlaneBound halpha hXi
    rw [hre]
    exact hsigma0
  have hinner : ContinuousAt
      (fun t : ℝ => ((sigma : ℂ) + (t : ℂ) * Complex.I)) t := by fun_prop
  have hout : ContinuousAt
      (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
      ((sigma : ℂ) + (t : ℂ) * Complex.I) := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
        ((sigma : ℂ) + (t : ℂ) * Complex.I) :=
      (differentiableAt_deriv_riemannZeta hne1).neg.div
        (differentiableAt_riemannZeta hne1) hzne
    have h2 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s)
        ((sigma : ℂ) + (t : ℂ) * Complex.I) :=
      (differentiableAt_id.const_cpow (Or.inl hxne)).div differentiableAt_id hne0
    exact (h1.mul h2).continuousAt
  exact ContinuousAt.comp
    (g := fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
    (f := fun t : ℝ => ((sigma : ℂ) + (t : ℂ) * Complex.I)) hout hinner

/-- Horizontal Perron-side estimate relative to an arbitrary Xi frontier. -/
theorem norm_hIntegral_perron_le_of_frontier
    {frontier x sigma1 sigma0 y C : ℝ} (hx : 1 ≤ x)
    (hsigma1 : frontier < sigma1) (hsigma1sigma0 : sigma1 ≤ sigma0)
    (hsigma0 : sigma0 ≤ 9 / 8) (hy : 7 ≤ |y|) (hC0 : 0 < C)
    (hC : ∀ sigma gamma : ℝ, 7 ≤ |gamma| → frontier < sigma → sigma ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((sigma : ℂ) + (gamma : ℂ) * Complex.I)‖
        ≤ C * Real.log |gamma| / (sigma - frontier)) :
    ‖HIntegral
        (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
        sigma1 sigma0 y‖
      ≤ (C * Real.log |y| / (sigma1 - frontier)) *
        (x ^ sigma0 / |y|) * |sigma0 - sigma1| := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < |y| := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log |y| := Real.log_nonneg (by linarith)
  have hsigma10 : (0 : ℝ) < sigma1 - frontier := by linarith
  have hbound : ∀ sigma ∈ Set.uIoc sigma1 sigma0,
      ‖(-deriv riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I) /
            riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I)) *
          ((x : ℂ) ^ ((sigma : ℂ) + (y : ℂ) * Complex.I) /
            ((sigma : ℂ) + (y : ℂ) * Complex.I))‖
        ≤ (C * Real.log |y| / (sigma1 - frontier)) * (x ^ sigma0 / |y|) := by
    intro sigma hsigma
    rw [Set.uIoc_of_le hsigma1sigma0, Set.mem_Ioc] at hsigma
    have hsigmalow : frontier < sigma := by linarith [hsigma.1]
    have hsigmahigh : sigma ≤ 9 / 8 := by linarith [hsigma.2]
    have hlogd := hC sigma y hy hsigmalow hsigmahigh
    have hlog : (-deriv riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I)) =
        -logDeriv riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I) := by
      rw [logDeriv_apply, neg_div]
    rw [hlog, norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (((sigma : ℂ) + (y : ℂ) * Complex.I)).re = sigma := by simp
    rw [hre]
    have hden : |y| ≤ ‖(sigma : ℂ) + (y : ℂ) * Complex.I‖ :=
      abs_le_norm_sigma_add_mul_I (σ := sigma) (t := y)
    have hden0 : (0 : ℝ) < ‖(sigma : ℂ) + (y : ℂ) * Complex.I‖ := by linarith
    have hxsigma : x ^ sigma ≤ x ^ sigma0 :=
      Real.rpow_le_rpow_of_exponent_le hx hsigma.2
    have hxsigma0 : (0 : ℝ) ≤ x ^ sigma := Real.rpow_nonneg hx0.le sigma
    have hquot : x ^ sigma / ‖(sigma : ℂ) + (y : ℂ) * Complex.I‖
        ≤ x ^ sigma0 / |y| := by
      rw [div_le_div_iff₀ hden0 hy0]
      nlinarith [hxsigma, hden, hxsigma0, Real.rpow_nonneg hx0.le sigma0]
    have hlogd' : ‖logDeriv riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ C * Real.log |y| / (sigma1 - frontier) := by
      refine hlogd.trans ?_
      gcongr
      linarith [hsigma.1]
    have hLnn : (0 : ℝ) ≤
        ‖logDeriv riemannZeta ((sigma : ℂ) + (y : ℂ) * Complex.I)‖ := norm_nonneg _
    have hQnn : (0 : ℝ) ≤
        x ^ sigma / ‖(sigma : ℂ) + (y : ℂ) * Complex.I‖ := by positivity
    have hRnn : (0 : ℝ) ≤ C * Real.log |y| / (sigma1 - frontier) := by positivity
    exact mul_le_mul hlogd' hquot hQnn hRnn
  rw [HIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Chebyshev master inequality after shifting to a line right of a Xi frontier. -/
theorem norm_chebyshev_sub_halfInt_le_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
    {N : ℕ} {sigma1 sigma0 T : ℝ}
    (hsigma1 : 1 / 2 + alpha < sigma1) (hsigma11 : sigma1 < 1)
    (hsigma0 : 1 < sigma0) (hT : 0 < T) :
    |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - ((N : ℝ) + 1 / 2)|
      ≤ (∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ *
            ((((N : ℝ) + 1 / 2) / n) ^ sigma0 /
              (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)))
        + (1 / (2 * Real.pi)) *
          (‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
                ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) sigma1 (-T) T‖
            + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
                ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) sigma1 sigma0 T‖
            + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
                ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) sigma1 sigma0 (-T)‖) := by
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hsigma00 : (0 : ℝ) < sigma0 := by linarith
  have hne : ∀ n : ℕ, (n : ℝ) ≠ (N : ℝ) + 1 / 2 := by
    intro n hcon
    have h2 : (2 * n : ℤ) = 2 * (N : ℤ) + 1 := by
      have : (2 * (n : ℝ)) = 2 * (N : ℝ) + 1 := by linarith
      exact_mod_cast this
    omega
  have hconv := summable_vonMangoldt_perron hx hsigma0
  have hdef := summable_perron_error (c := fun n : ℕ => ((Λ n : ℝ) : ℂ))
    hx hsigma00 hT hconv
  have hperron := norm_tsum_lt_sub_perron_integral_le
    (c := fun n : ℕ => ((Λ n : ℝ) : ℂ)) (by simp) hx hne hsigma00 hT hconv hdef
  rw [tsum_indicator_vonMangoldt_eq N,
    perron_integral_eq_vIntegral' (x := (N : ℝ) + 1 / 2) (σ := sigma0)
      (T := T) hsigma0] at hperron
  have hshift := norm_vIntegral'_perron_sub_le_of_xiZeroHalfPlaneBound
    halpha hXi (x := (N : ℝ) + 1 / 2) hx hsigma1 hsigma11 hsigma0 hT
  have htri :
      ‖((∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) : ℝ) : ℂ) -
          (((N : ℝ) + 1 / 2 : ℝ) : ℂ)‖ ≤ _ + _ :=
    norm_sub_le_norm_sub_add_norm_sub _
      (VIntegral' (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
        ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) sigma0 (-T) T) _
  have hreal :
      ‖((∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) : ℝ) : ℂ) -
          (((N : ℝ) + 1 / 2 : ℝ) : ℂ)‖ =
        |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - ((N : ℝ) + 1 / 2)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hreal] at htri
  linarith [htri, hperron, hshift]

private theorem vonKoch_envelope_bounds
    {x p e : ℝ} (hx : 1 ≤ x) (hp : 0 ≤ p) (hep : e ≤ p) :
    0 ≤ x ^ p * (1 + Real.log x) ^ 2 ∧
      1 ≤ x ^ p * (1 + Real.log x) ^ 2 ∧
      x ^ e ≤ x ^ p * (1 + Real.log x) ^ 2 ∧
      (1 + Real.log x) ^ 2 ≤ x ^ p * (1 + Real.log x) ^ 2 ∧
      Real.log x * x ^ e ≤ x ^ p * (1 + Real.log x) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL1 : 1 ≤ 1 + Real.log x := by linarith
  have hL2 : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx hp
  have hxe : x ^ e ≤ x ^ p := Real.rpow_le_rpow_of_exponent_le hx hep
  have hxe0 : 0 ≤ x ^ e := Real.rpow_nonneg hx0 _
  have hP0 : 0 ≤ x ^ p := Real.rpow_nonneg hx0 _
  have hL0 : 0 ≤ (1 + Real.log x) ^ 2 := sq_nonneg _
  refine ⟨mul_nonneg hP0 hL0, ?_, ?_, ?_, ?_⟩
  · simpa using mul_le_mul hP1 hL2 (by norm_num : (0 : ℝ) ≤ 1) hP0
  · simpa using mul_le_mul hxe hL2 (by norm_num : (0 : ℝ) ≤ 1) hP0
  · simpa using mul_le_mul_of_nonneg_right hP1 hL0
  · have hlogle : Real.log x ≤ (1 + Real.log x) ^ 2 := by nlinarith
    have hmul := mul_le_mul hlogle hxe hxe0 hL0
    simpa only [mul_comm] using hmul

private theorem vonKoch_perron_leading_identity
    {x epsilon : ℝ} (hepsilon : 0 < epsilon) (hx : 0 < x) :
    (1 / (Real.pi * x * Real.log 2)) *
          (x ^ ((1 : ℝ) + epsilon / 2) * (8 / ((1 + epsilon / 2) - 1) ^ 2)) =
      (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) * x ^ (epsilon / 2) := by
  have hxrp : x ^ ((1 : ℝ) + epsilon / 2) = x * x ^ (epsilon / 2) := by
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [show ((1 : ℝ) + epsilon / 2) - 1 = epsilon / 2 by ring, hxrp]
  field_simp
  ring

private theorem vonKoch_log_product_le
    {A B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L)
    (hAL : A ≤ L) (hBL : B ≤ 3 * L) :
    64 * A * B ≤ 192 * L ^ 2 := by
  have hmul := mul_le_mul hAL hBL hB0 hL0
  nlinarith [hmul]

private theorem vonKoch_vertical_bracket_le
    {alpha epsilon x : ℝ} (halpha : 0 ≤ alpha) (hepsilon : 0 < epsilon)
    (hx4 : 4 ≤ x) :
    2 * (1 + Real.log 3) / (1 / 2 + alpha + epsilon / 2) +
        2 * (1 + Real.log (2 + x)) * Real.log x
      ≤ 14 * (1 + Real.log x) ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hL1 : (1 : ℝ) ≤ 1 + Real.log x := by linarith
  have hL2 : (1 : ℝ) ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hsigma10 : (0 : ℝ) < 1 / 2 + alpha + epsilon / 2 := by linarith
  have hlog3 : Real.log 3 ≤ 1.4 := by
    have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    nlinarith [Real.log_two_lt_d9]
  have h1 : 2 * (1 + Real.log 3) / (1 / 2 + alpha + epsilon / 2) ≤ 10 := by
    rw [div_le_iff₀ hsigma10]
    nlinarith [hlog3]
  have h2 : 1 + Real.log (2 + x) ≤ 2 * (1 + Real.log x) := by
    have hmono : Real.log (2 + x) ≤ Real.log (4 * x) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at hmono
    have hl4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx4
    linarith
  have h4 : (1 + Real.log (2 + x)) * Real.log x ≤
      (2 * (1 + Real.log x)) * (1 + Real.log x) :=
    mul_le_mul h2 (by linarith) hlogx0 (by linarith)
  nlinarith [h1, h4, hL2]

private theorem vonKoch_horizontal_identity
    {alpha epsilon C x : ℝ} (halphaHalf : alpha < 1 / 2)
    (hepsilon : 0 < epsilon) (hx : 0 < x) :
    (C * Real.log x / ((1 / 2 + alpha + epsilon / 2) - (1 / 2 + alpha))) *
          (x ^ ((1 : ℝ) + epsilon / 2) / x) *
          |(1 + epsilon / 2) - (1 / 2 + alpha + epsilon / 2)| =
      (2 * C * (1 / 2 - alpha) / epsilon) *
        (Real.log x * x ^ (epsilon / 2)) := by
  have hxrp : x ^ ((1 : ℝ) + epsilon / 2) = x * x ^ (epsilon / 2) := by
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [show (1 / 2 + alpha + epsilon / 2) - (1 / 2 + alpha) = epsilon / 2 by ring,
    show |(1 + epsilon / 2) - (1 / 2 + alpha + epsilon / 2)| =
        1 / 2 - alpha by
      rw [show (1 + epsilon / 2) - (1 / 2 + alpha + epsilon / 2) =
        1 / 2 - alpha by ring, abs_of_nonneg (by linarith)],
    hxrp]
  field_simp

private theorem vonKoch_perron_error_le
    {alpha epsilon : ℝ} (halpha : 0 ≤ alpha) (hepsilon : 0 < epsilon)
    (hepsilon4 : epsilon ≤ 1 / 4) {N : ℕ} (hN : 7 ≤ N) :
    (∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ *
          ((((N : ℝ) + 1 / 2) / n) ^ (1 + epsilon / 2) /
            (Real.pi * ((N : ℝ) + 1 / 2) *
              |Real.log (((N : ℝ) + 1 / 2) / n)|)))
      ≤ (32 / (Real.pi * Real.log 2 * epsilon ^ 2) + 192 / Real.pi) *
        (((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + epsilon / 2) *
          (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) := by
  have hN7 : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hx4 : (4 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) := Real.log_nonneg hx1
  have hsigma0 : (1 : ℝ) < 1 + epsilon / 2 := by linarith
  have hsigma02 : (1 : ℝ) + epsilon / 2 ≤ 2 := by linarith
  set Q : ℝ := ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) *
      (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 with hQdef
  have hQbounds := vonKoch_envelope_bounds hx1
    (show (0 : ℝ) ≤ 1 / 2 + alpha + epsilon / 2 by linarith)
    (show epsilon / 2 ≤ 1 / 2 + alpha + epsilon / 2 by linarith)
  rw [← hQdef] at hQbounds
  rcases hQbounds with ⟨_, _, hQxe, hQL, _⟩
  have hE := perron_error_vonMangoldt_total_le (N := N) (σ := 1 + epsilon / 2)
    (T := (N : ℝ) + 1 / 2) (by omega) hsigma0 hsigma02 hx0
  have hE1 : (1 / (Real.pi * ((N : ℝ) + 1 / 2) * Real.log 2)) *
        (((N : ℝ) + 1 / 2) ^ ((1 : ℝ) + epsilon / 2) *
          (8 / ((1 + epsilon / 2) - 1) ^ 2)) =
      (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) *
        ((N : ℝ) + 1 / 2) ^ (epsilon / 2) :=
    vonKoch_perron_leading_identity hepsilon hx0
  have hcast : ((2 * N + 2 : ℕ) : ℝ) = 2 * (N : ℝ) + 2 := by push_cast; ring
  have hlog2x : Real.log (2 * ((N : ℝ) + 1 / 2)) ≤
      1 + Real.log ((N : ℝ) + 1 / 2) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hlogN2 : 1 + Real.log ((2 * N + 2 : ℕ) : ℝ) ≤
      3 * (1 + Real.log ((N : ℝ) + 1 / 2)) := by
    rw [hcast]
    have hmono : Real.log (2 * (N : ℝ) + 2) ≤
        Real.log (4 * ((N : ℝ) + 1 / 2)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at hmono
    have hl4 : Real.log 4 ≤ Real.log ((N : ℝ) + 1 / 2) :=
      Real.log_le_log (by norm_num) hx4
    linarith
  have hlogN20 : (0 : ℝ) ≤ 1 + Real.log ((2 * N + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ Real.log ((2 * N + 2 : ℕ) : ℝ) := by
      rw [hcast]
      exact Real.log_nonneg (by linarith)
    linarith
  have hE2 : (16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2) /
        (Real.pi * ((N : ℝ) + 1 / 2))) *
        (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)))
      ≤ (192 / Real.pi) * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
    have hid : 16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2) /
          (Real.pi * ((N : ℝ) + 1 / 2)) *
          (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) =
        (64 * Real.log (2 * ((N : ℝ) + 1 / 2)) *
          (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) / Real.pi := by
      field_simp
      ring
    have hid2 : (192 / Real.pi) * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 =
        (192 * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) / Real.pi := by ring
    rw [hid, hid2]
    have hnum : 64 * Real.log (2 * ((N : ℝ) + 1 / 2)) *
          (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)) ≤
        192 * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 :=
      vonKoch_log_product_le hlogN20 (by linarith) hlog2x hlogN2
    exact div_le_div_of_nonneg_right hnum Real.pi_pos.le
  have hEq1 : (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) *
        ((N : ℝ) + 1 / 2) ^ (epsilon / 2) ≤
      (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) * Q :=
    mul_le_mul_of_nonneg_left hQxe (by positivity)
  have hEq2 : (192 / Real.pi) * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 ≤
      (192 / Real.pi) * Q := mul_le_mul_of_nonneg_left hQL (by positivity)
  rw [hE1] at hE
  calc
    (∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ *
          ((((N : ℝ) + 1 / 2) / n) ^ (1 + epsilon / 2) /
            (Real.pi * ((N : ℝ) + 1 / 2) *
              |Real.log (((N : ℝ) + 1 / 2) / n)|)))
        ≤ (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) *
            ((N : ℝ) + 1 / 2) ^ (epsilon / 2) +
          (16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2) /
            (Real.pi * ((N : ℝ) + 1 / 2))) *
            (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) := hE
    _ ≤ (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) * Q +
          (192 / Real.pi) * Q := add_le_add hEq1 (hE2.trans hEq2)
    _ = (32 / (Real.pi * Real.log 2 * epsilon ^ 2) + 192 / Real.pi) * Q := by ring
    _ = _ := by rw [hQdef]

private theorem exists_vonKoch_contour_sides_bound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon4 : epsilon ≤ 1 / 4)
    (hline : 1 / 2 + alpha + epsilon / 2 < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 7 ≤ N →
      ‖VIntegral
          (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
            ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s))
          (1 / 2 + alpha + epsilon / 2) (-((N : ℝ) + 1 / 2))
            ((N : ℝ) + 1 / 2)‖ +
        ‖HIntegral
          (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
            ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s))
          (1 / 2 + alpha + epsilon / 2) (1 + epsilon / 2)
            ((N : ℝ) + 1 / 2)‖ +
        ‖HIntegral
          (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
            ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s))
          (1 / 2 + alpha + epsilon / 2) (1 + epsilon / 2)
            (-((N : ℝ) + 1 / 2))‖
      ≤ 14 * K * (((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + epsilon / 2) *
            (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) +
        ((C / epsilon) * (((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + epsilon / 2) *
            (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) +
          (C / epsilon) * (((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + epsilon / 2) *
            (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2)) := by
  have hsigma1 : (1 : ℝ) / 2 + alpha < 1 / 2 + alpha + epsilon / 2 := by linarith
  have hsigma11 : (1 : ℝ) / 2 + alpha + epsilon / 2 < 1 := hline
  have hsigma098 : (1 : ℝ) + epsilon / 2 ≤ 9 / 8 := by linarith
  have hsigma1sigma0 : (1 : ℝ) / 2 + alpha + epsilon / 2 ≤ 1 + epsilon / 2 := by
    linarith
  have hsigma10 : (0 : ℝ) < 1 / 2 + alpha + epsilon / 2 := by linarith
  obtain ⟨K, hK0, hK⟩ :=
    exists_logDeriv_zeta_line_bound_of_xiZeroHalfPlaneBound
      halpha hXi hsigma1 hsigma11
  obtain ⟨C, hC0, hC⟩ :=
    exists_logDeriv_zeta_bound_of_xiZeroHalfPlaneBound halpha hXi
  refine ⟨K, hK0, C, hC0, ?_⟩
  intro N hN
  have hN7 : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hx4 : (4 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) := Real.log_nonneg hx1
  set Q : ℝ := ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) *
      (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 with hQdef
  have hQbounds := vonKoch_envelope_bounds hx1
    (show (0 : ℝ) ≤ 1 / 2 + alpha + epsilon / 2 by linarith)
    (show epsilon / 2 ≤ 1 / 2 + alpha + epsilon / 2 by linarith)
  rw [← hQdef] at hQbounds
  rcases hQbounds with ⟨_, _, _, _, hQlogxe⟩
  have hcont := continuous_perron_integrand_line_of_xiZeroHalfPlaneBound
    halpha hXi (x := (N : ℝ) + 1 / 2)
    (sigma := 1 / 2 + alpha + epsilon / 2) hx0 hsigma1 hsigma11
  have hV := norm_vIntegral_perron_le (x := (N : ℝ) + 1 / 2)
    (σ := 1 / 2 + alpha + epsilon / 2) (T := (N : ℝ) + 1 / 2)
    (K := K) hx0 hsigma10 hx1 hK0.le hK hcont
  have hVb := vonKoch_vertical_bracket_le halpha hepsilon hx4
  have hVfin : ‖VIntegral
        (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) *
          ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s))
        (1 / 2 + alpha + epsilon / 2) (-((N : ℝ) + 1 / 2))
          ((N : ℝ) + 1 / 2)‖ ≤ 14 * K * Q := by
    refine hV.trans ?_
    have hcoef : (0 : ℝ) ≤ K *
        ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) := by
      have : (0 : ℝ) ≤
          ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) :=
        Real.rpow_nonneg hx0.le _
      positivity
    have hmul := mul_le_mul_of_nonneg_left hVb hcoef
    rw [hQdef]
    calc
      K * ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) *
          (2 * (1 + Real.log 3) / (1 / 2 + alpha + epsilon / 2) +
            2 * (1 + Real.log (2 + ((N : ℝ) + 1 / 2))) *
              Real.log ((N : ℝ) + 1 / 2)) ≤
        K * ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) *
          (14 * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) := hmul
      _ = 14 * K * (((N : ℝ) + 1 / 2) ^
          ((1 : ℝ) / 2 + alpha + epsilon / 2) *
            (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) := by ring
  have habs : |(N : ℝ) + 1 / 2| = (N : ℝ) + 1 / 2 := abs_of_pos hx0
  have habsneg : |-((N : ℝ) + 1 / 2)| = (N : ℝ) + 1 / 2 := by
    rw [abs_neg]
    exact habs
  have hHp := norm_hIntegral_perron_le_of_frontier
    (frontier := 1 / 2 + alpha) (x := (N : ℝ) + 1 / 2)
    (sigma1 := 1 / 2 + alpha + epsilon / 2) (sigma0 := 1 + epsilon / 2)
    (y := (N : ℝ) + 1 / 2) (C := C) hx1 hsigma1 hsigma1sigma0 hsigma098
    (by rw [habs]; linarith) hC0 hC
  have hHm := norm_hIntegral_perron_le_of_frontier
    (frontier := 1 / 2 + alpha) (x := (N : ℝ) + 1 / 2)
    (sigma1 := 1 / 2 + alpha + epsilon / 2) (sigma0 := 1 + epsilon / 2)
    (y := -((N : ℝ) + 1 / 2)) (C := C) hx1 hsigma1 hsigma1sigma0 hsigma098
    (by rw [habsneg]; linarith) hC0 hC
  rw [habs] at hHp
  rw [habsneg] at hHm
  have hHid := vonKoch_horizontal_identity (C := C) (x := (N : ℝ) + 1 / 2)
    halphaHalf hepsilon hx0
  rw [hHid] at hHp hHm
  have hcoefle : 2 * C * (1 / 2 - alpha) / epsilon ≤ C / epsilon := by
    have hCe : (0 : ℝ) ≤ C / epsilon := by positivity
    have hw : 2 * (1 / 2 - alpha) ≤ 1 := by linarith
    calc
      2 * C * (1 / 2 - alpha) / epsilon =
          (C / epsilon) * (2 * (1 / 2 - alpha)) := by ring
      _ ≤ (C / epsilon) * 1 := mul_le_mul_of_nonneg_left hw hCe
      _ = C / epsilon := by ring
  have hxe0 : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ (epsilon / 2) :=
    Real.rpow_nonneg hx0.le _
  have hprod0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) *
      ((N : ℝ) + 1 / 2) ^ (epsilon / 2) := mul_nonneg hlogx0 hxe0
  have hHp' := hHp.trans (mul_le_mul_of_nonneg_right hcoefle hprod0)
  have hHm' := hHm.trans (mul_le_mul_of_nonneg_right hcoefle hprod0)
  have hHq : (C / epsilon) *
        (Real.log ((N : ℝ) + 1 / 2) * ((N : ℝ) + 1 / 2) ^ (epsilon / 2)) ≤
      (C / epsilon) * Q := mul_le_mul_of_nonneg_left hQlogxe (by positivity)
  have hHpq := hHp'.trans hHq
  have hHmq := hHm'.trans hHq
  calc
    _ ≤ (14 * K * Q + (C / epsilon) * Q) + (C / epsilon) * Q :=
      add_le_add (add_le_add hVfin hHpq) hHmq
    _ = 14 * K * Q + ((C / epsilon) * Q + (C / epsilon) * Q) := by ring

/-- Chebyshev error at half-integer cutoffs from an arbitrary Xi zero frontier below one. -/
theorem exists_chebyshev_error_halfInt_bound_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon4 : epsilon ≤ 1 / 4)
    (hline : 1 / 2 + alpha + epsilon / 2 < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 7 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ)|
        ≤ C * (((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + epsilon / 2) *
            (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) := by
  have hsigma1 : (1 : ℝ) / 2 + alpha < 1 / 2 + alpha + epsilon / 2 := by linarith
  have hsigma11 : (1 : ℝ) / 2 + alpha + epsilon / 2 < 1 := hline
  have hsigma0 : (1 : ℝ) < 1 + epsilon / 2 := by linarith
  obtain ⟨K, hK0, C, hC0, hcontour⟩ :=
    exists_vonKoch_contour_sides_bound halpha halphaHalf hXi hepsilon hepsilon4 hline
  refine ⟨32 / (Real.pi * Real.log 2 * epsilon ^ 2) + 192 / Real.pi +
      7 * K / Real.pi + C / (Real.pi * epsilon) + 1 / 2, by positivity, ?_⟩
  intro N hN
  have hN7 : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  set Q : ℝ := ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + alpha + epsilon / 2) *
      (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 with hQdef
  have hQbounds := vonKoch_envelope_bounds hx1
    (show (0 : ℝ) ≤ 1 / 2 + alpha + epsilon / 2 by linarith)
    (show epsilon / 2 ≤ 1 / 2 + alpha + epsilon / 2 by linarith)
  rw [← hQdef] at hQbounds
  rcases hQbounds with ⟨_, hQ1, _, _, _⟩
  have hmaster := norm_chebyshev_sub_halfInt_le_of_xiZeroHalfPlaneBound
    (N := N) (sigma1 := 1 / 2 + alpha + epsilon / 2)
    (sigma0 := 1 + epsilon / 2) (T := (N : ℝ) + 1 / 2)
    halpha hXi hsigma1 hsigma11 hsigma0 hx0
  have hE := vonKoch_perron_error_le halpha hepsilon hepsilon4 hN
  rw [← hQdef] at hE
  have hsides := hcontour N hN
  rw [← hQdef] at hsides
  have htri : |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ)| ≤
      |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - ((N : ℝ) + 1 / 2)| + 1 / 2 := by
    have h1 := abs_sub_le (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ))
      ((N : ℝ) + 1 / 2) (N : ℝ)
    have h2 : |((N : ℝ) + 1 / 2) - (N : ℝ)| = 1 / 2 := by
      rw [show ((N : ℝ) + 1 / 2) - (N : ℝ) = 1 / 2 by ring]
      norm_num
    rw [h2] at h1
    exact h1
  have hhalf : (1 : ℝ) / 2 ≤ 1 / 2 * Q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hexpand : (32 / (Real.pi * Real.log 2 * epsilon ^ 2) + 192 / Real.pi +
        7 * K / Real.pi + C / (Real.pi * epsilon) + 1 / 2) * Q =
      (32 / (Real.pi * Real.log 2 * epsilon ^ 2)) * Q +
        (192 / Real.pi) * Q + (1 / (2 * Real.pi)) * (14 * K * Q) +
        (1 / (2 * Real.pi)) * ((C / epsilon) * Q + (C / epsilon) * Q) +
        1 / 2 * Q := by
    field_simp
    ring
  rw [hexpand]
  have hpiinv : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsides hpiinv
  linarith [hmaster, hE, htri, hhalf, hscaled]

/-- Generalized von Koch natural-cutoff estimate below the trivial frontier. -/
theorem chebyshev_error_isBigO_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ))
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 + alpha + epsilon) := by
  let delta : ℝ := min epsilon (min (1 / 4) (1 / 2 - alpha))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min hepsilon (lt_min (by norm_num) (sub_pos.mpr halphaHalf))
  have hdelta4 : delta ≤ 1 / 4 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hdeltaEpsilon : delta ≤ epsilon := min_le_left _ _
  have hdeltamargin : delta ≤ 1 / 2 - alpha :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hline : 1 / 2 + alpha + delta / 2 < 1 := by linarith
  obtain ⟨Cst, hCst0, hCst⟩ :=
    exists_chebyshev_error_halfInt_bound_of_xiZeroHalfPlaneBound
      halpha halphaHalf hXi hdelta hdelta4 hline
  have hstep :
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ))
        =O[atTop] fun N : ℕ =>
          ((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + delta / 2) *
            (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
    refine Asymptotics.IsBigO.of_bound Cst ?_
    filter_upwards [eventually_ge_atTop 7] with N hN
    have hb := hCst N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤
        ((N : ℝ) + 1 / 2) ^ (1 / 2 + alpha + delta / 2) *
          (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2)]
    exact hb
  refine hstep.trans (isBigO_shift_rpow_one_add_log ?_ (by linarith) 2)
  linarith

/-- Generalized von Koch bound at every positive exponent above the supplied frontier. -/
theorem exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ)|
        ≤ C * (N : ℝ) ^ (1 / 2 + alpha + epsilon) :=
  exists_bound_of_isBigO_natRpow (by linarith)
    (chebyshev_error_isBigO_of_xiZeroHalfPlaneBound
      halpha halphaHalf hXi hepsilon)

/-- Real-variable generalized von Koch bound below the trivial frontier. -/
theorem exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |chebyshevPsiReal t - t| ≤ C * t ^ (1 / 2 + alpha + epsilon) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
      halpha halphaHalf hXi hepsilon
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hfl : 1 ≤ ⌊t⌋₊ := Nat.one_le_floor_iff t |>.2 ht
  have hflle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have hfllt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hfl1 : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfl
  have hpsi : chebyshevPsiReal t =
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Λ n : ℝ) := by
    rw [chebyshevPsiReal_eq_sum_range, sum_range_succ_vonMangoldt_eq_sum_Icc]
  have hb := hC ⌊t⌋₊ hfl
  have hmono : ((⌊t⌋₊ : ℕ) : ℝ) ^ (1 / 2 + alpha + epsilon) ≤
      t ^ (1 / 2 + alpha + epsilon) :=
    Real.rpow_le_rpow (by linarith) hflle (by linarith)
  have hone : (1 : ℝ) ≤ t ^ (1 / 2 + alpha + epsilon) := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht
      (show (0 : ℝ) ≤ 1 / 2 + alpha + epsilon by linarith)
  have htri : |chebyshevPsiReal t - t| ≤
      |(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Λ n : ℝ)) - ((⌊t⌋₊ : ℕ) : ℝ)| +
        |((⌊t⌋₊ : ℕ) : ℝ) - t| := by
    rw [hpsi]
    exact abs_sub_le _ _ _
  have hgap : |((⌊t⌋₊ : ℕ) : ℝ) - t| ≤ 1 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  nlinarith [htri, hb, hgap, hmono, hone, hC0]

end Sieve

/-- The project Chebyshev error is the real-variable Chebyshev remainder. -/
theorem criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub (x : ℝ) :
    criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) x =
      chebyshevPsiReal x - x := by
  rw [criticalMellinError, criticalCumulative, chebyshevPsiReal_eq_sum_range,
    sum_range_succ_vonMangoldt_eq_sum_Icc]
  congr 1
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn0 hn1
    simp only [Finset.mem_Icc] at hn0
    have hn : n = 0 := by
      by_contra hne
      have hone : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hne
      exact hn1 (by simp only [Finset.mem_Icc]; omega)
    subst n
    simp

/-- Generalized von Koch below the trivial frontier, in the exact source-spectrum form. -/
theorem chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound_lt_half
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) : ChebyshevErrorPowerSpectrum alpha := by
  intro epsilon hepsilon
  obtain ⟨C, hC0, hC⟩ :=
    Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound
      halpha halphaHalf hXi hepsilon
  refine ⟨C, hC0.le, ?_⟩
  intro x hx
  rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub]
  exact hC x hx

/-- At and beyond the trivial width, Chebyshev's linear estimate gives the source spectrum. -/
theorem chebyshevErrorPowerSpectrum_of_half_le {alpha : ℝ} (halpha : 1 / 2 ≤ alpha) :
    ChebyshevErrorPowerSpectrum alpha := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshevPsiReal_le_linear
  intro epsilon hepsilon
  refine ⟨C + 1, by positivity, ?_⟩
  intro x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hpsi0 : 0 ≤ chebyshevPsiReal x := chebyshevPsiReal_nonneg x
  have hlinear := hC x hx
  have herr : |chebyshevPsiReal x - x| ≤ (C + 1) * x := by
    rw [abs_le]
    constructor <;>
      linarith only [hlinear, hpsi0, hx0.le, mul_nonneg hC0.le hx0.le]
  have hexponent : (1 : ℝ) ≤ 1 / 2 + alpha + epsilon := by linarith
  have hpow : x ≤ x ^ (1 / 2 + alpha + epsilon) := by
    calc
      x = x ^ (1 : ℝ) := by simp
      _ ≤ x ^ (1 / 2 + alpha + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hx hexponent
  rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub]
  exact herr.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- **Generalized von Koch theorem.** Every Xi half-plane bound yields the matching all-epsilon
Chebyshev error spectrum, including the unconditional trivial-width endpoint. -/
theorem chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha) :
    ChebyshevErrorPowerSpectrum alpha := by
  rcases lt_or_ge alpha (1 / 2) with halphaHalf | hhalf
  · exact chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound_lt_half
      halpha halphaHalf hXi
  · exact chebyshevErrorPowerSpectrum_of_half_le hhalf

/-- The intrinsic rightmost transverse displacement is itself a global Xi half-plane bound. -/
theorem xiZeroHalfPlaneBound_xiRightTransverseSup :
    XiZeroHalfPlaneBound xiRightTransverseSup := by
  intro rho hzero
  by_cases hrho : 1 / 2 < rho.re
  · let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hpos := xi_divisor_pos_on_support support
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
      omega
    let q : XiZeroCopy := ⟨support, ⟨0, hn⟩⟩
    have hqright : 0 < (I * xiSpectralPoint q).re := by
      have hcoord : I * xiSpectralPoint q = rho - 1 / 2 := by
        simpa only [q, support] using I_mul_xiSpectralPoint q
      rw [hcoord, Complex.sub_re]
      norm_num
      linarith
    let qr : XiRightZeroCopy := ⟨q, hqright⟩
    have hsup := xiRightCenteredZero_re_le_sup qr
    have hcoord : (xiRightCenteredZero qr).re = rho.re - 1 / 2 := by
      change (I * xiSpectralPoint q).re = _
      have heq : I * xiSpectralPoint q = rho - 1 / 2 := by
        simpa only [q, support] using I_mul_xiSpectralPoint q
      rw [heq, Complex.sub_re]
      norm_num
    rw [hcoord] at hsup
    linarith
  · linarith
    [xiRightTransverseSup_nonneg]

/-- Closed intrinsic-width square-energy identity, with generalized von Koch discharged. -/
theorem squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth_unconditional
    (hne : Nonempty XiRightZeroCopy) :
    LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient =
      (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) := by
  apply squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth hne
  exact chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound
    xiRightTransverseSup_nonneg xiZeroHalfPlaneBound_xiRightTransverseSup

/-- Exact all-width collision between Xi zero geometry and literal sharp dyadic prime windows. -/
theorem xiZeroHalfPlaneBound_iff_exists_dyadicWeightedPrimeWindowPowerUpper
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiZeroHalfPlaneBound alpha ↔
      ∃ N : ℕ, DyadicWeightedPrimeWindowPowerUpper alpha N := by
  constructor
  · intro hXi
    exact ⟨2, dyadicWeightedPrimeWindowPowerUpper_of_chebyshevErrorPowerSpectrum
      halpha (chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound halpha hXi)⟩
  · rintro ⟨N, hwindow⟩
    exact xiZeroHalfPlaneBound_of_dyadicWeightedPrimeWindowPowerUpper halpha hwindow

/-- Exact zero-width collision between RH and sharp-window subpower upper bounds. -/
theorem riemannHypothesis_iff_exists_dyadicWeightedPrimeWindowSubpowerUpper :
    RiemannHypothesis ↔ ∃ N : ℕ, DyadicWeightedPrimeWindowSubpowerUpper N := by
  rw [← xiZeroHalfPlaneBound_zero_iff_rh]
  constructor
  · intro hXi
    obtain ⟨N, hN⟩ :=
      (xiZeroHalfPlaneBound_iff_exists_dyadicWeightedPrimeWindowPowerUpper
        (alpha := 0) le_rfl).mp hXi
    exact ⟨N, (dyadicWeightedPrimeWindowPowerUpper_zero_iff_subpowerUpper N).mp hN⟩
  · rintro ⟨N, hN⟩
    exact (xiZeroHalfPlaneBound_iff_exists_dyadicWeightedPrimeWindowPowerUpper
      (alpha := 0) le_rfl).mpr
        ⟨N, (dyadicWeightedPrimeWindowPowerUpper_zero_iff_subpowerUpper N).mpr hN⟩

end

end RHTower
