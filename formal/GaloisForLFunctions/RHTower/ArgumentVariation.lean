/-
Borel–Carathéodory argument variation, the analytic logarithm on zero-free discs, and the
carrier-side cap on the winding-phase advance.

For analytic `g` on `ball c R` with `Re g ≤ A` and `Re (g c) < A`, transporting the
half-plane `Re ≤ A − Re (g c)` into the closed unit disc by `w ↦ w/(2A' − w)` and applying
the Schwarz–Pick bound gives the Borel–Carathéodory estimate
`‖g z − g c‖ ≤ 2‖z−c‖/(R−‖z−c‖)·(A − Re (g c))`.  A nowhere-zero analytic function on a
disc has an analytic logarithm; a complex number whose exponential is a positive real has
imaginary part in `2πℤ`; and a continuous `2πℤ`-valued function on an interval is constant.
Combined with the winding phase lock — on a sign-constant line segment the rotated carrier
`arch·e^{iΘ}·g_N` is a positive real — these cap the winding-phase advance over any
sign-constant segment of a zero-free disc by twice the carrier's Borel–Carathéodory budget:
the phase the archimedean winding must spend is phase the carrier's `M/m`-ratio must pay
for, so sign-constant stretches cannot outlive the budget.
-/
import GaloisForLFunctions.RHTower.WindingRigidity
import GaloisForLFunctions.U0.U0KummerBranch

open Complex Metric MeasureTheory

namespace RHTower

/-! ### §1 Borel–Carathéodory -/

/-- **Borel–Carathéodory bound.**  An analytic function on a disc whose real part is bounded
above satisfies a full-norm bound off the center, proportional to the real-part defect at
the center. -/
theorem borel_caratheodory {g : ℂ → ℂ} {c z : ℂ} {R A : ℝ}
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ w ∈ ball c R, (g w).re ≤ A)
    (hA : (g c).re < A)
    (hz : z ∈ ball c R) :
    ‖g z - g c‖ ≤ 2 * ‖z - c‖ / (R - ‖z - c‖) * (A - (g c).re) := by
  have hρR : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hρR
  set A' : ℝ := A - (g c).re with hA'_def
  have hA'0 : 0 < A' := by
    dsimp [A']
    linarith
  set f : ℂ → ℂ := fun w => g w - g c with hf_def
  have hfRe : ∀ w ∈ ball c R, (f w).re ≤ A' := by
    intro w hw
    simp only [f, Complex.sub_re, A']
    linarith [hRe w hw]
  have hden : ∀ w ∈ ball c R, (2 * (A' : ℂ) - f w) ≠ 0 := by
    intro w hw h0
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re] at hre
    have := hfRe w hw
    norm_num at hre
    linarith
  set φ : ℂ → ℂ := fun w => f w / (2 * (A' : ℂ) - f w) with hφ_def
  have hφc : φ c = 0 := by
    simp [φ, f]
  have hφdiff : DifferentiableOn ℂ φ (ball c R) :=
    (hg.sub (differentiableOn_const _)).div
      ((differentiableOn_const _).sub (hg.sub (differentiableOn_const _))) hden
  have hmaps : Set.MapsTo φ (ball c R) (closedBall (φ c) 1) := by
    intro w hw
    rw [hφc, Metric.mem_closedBall, dist_zero_right]
    have hd0 : 0 < ‖2 * (A' : ℂ) - f w‖ := norm_pos_iff.mpr (hden w hw)
    rw [hφ_def]
    simp only
    rw [norm_div, div_le_one hd0]
    have h1 : ‖f w‖ ^ 2 = (f w).re ^ 2 + (f w).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h2 : ‖2 * (A' : ℂ) - f w‖ ^ 2 = (2 * A' - (f w).re) ^ 2 + (f w).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num
      ring
    nlinarith [hfRe w hw, norm_nonneg (f w), norm_nonneg (2 * (A' : ℂ) - f w), hA'0]
  rcases eq_or_ne z c with rfl | hzc
  · simp
  · have hd := Complex.norm_dslope_le_div_of_mapsTo_ball hφdiff hmaps hz
    rw [dslope_of_ne _ hzc, slope_def_field, hφc, sub_zero, norm_div] at hd
    have hzc0 : 0 < ‖z - c‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hzc
    have hφz : ‖φ z‖ ≤ ‖z - c‖ / R := by
      rw [div_le_div_iff₀ hzc0 hR0] at hd
      rw [le_div_iff₀ hR0]
      linarith
    have hφlt1 : ‖φ z‖ < 1 := lt_of_le_of_lt hφz (by rwa [div_lt_one hR0])
    have hkey : f z * (1 + φ z) = 2 * (A' : ℂ) * φ z := by
      have h0 := hden z hz
      rw [hφ_def]
      field_simp
      ring
    have hlow : 1 - ‖φ z‖ ≤ ‖1 + φ z‖ := by
      have h2 : ‖(1 : ℂ)‖ ≤ ‖1 + φ z‖ + ‖φ z‖ := by
        calc ‖(1 : ℂ)‖ = ‖(1 + φ z) + -(φ z)‖ := by ring_nf
          _ ≤ ‖1 + φ z‖ + ‖-(φ z)‖ := norm_add_le _ _
          _ = ‖1 + φ z‖ + ‖φ z‖ := by rw [norm_neg]
      rw [norm_one] at h2
      linarith
    have hnorm_eq : ‖f z‖ * ‖1 + φ z‖ = 2 * A' * ‖φ z‖ := by
      have h := congrArg norm hkey
      rwa [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hA'0, show ‖(2 : ℂ)‖ = 2 from by norm_num] at h
    have h3 : ‖f z‖ * (1 - ‖φ z‖) ≤ 2 * A' * (‖z - c‖ / R) := by
      calc ‖f z‖ * (1 - ‖φ z‖) ≤ ‖f z‖ * ‖1 + φ z‖ :=
            mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
        _ = 2 * A' * ‖φ z‖ := hnorm_eq
        _ ≤ 2 * A' * (‖z - c‖ / R) :=
            mul_le_mul_of_nonneg_left hφz (by positivity)
    have h5 : 0 < 1 - ‖z - c‖ / R := by
      rw [sub_pos, div_lt_one hR0]
      exact hρR
    have h6 : ‖f z‖ * (1 - ‖z - c‖ / R) ≤ 2 * A' * (‖z - c‖ / R) := by
      have h4 : ‖f z‖ * (1 - ‖z - c‖ / R) ≤ ‖f z‖ * (1 - ‖φ z‖) := by
        have := hφz
        nlinarith [norm_nonneg (f z)]
      linarith
    have h7 : ‖f z‖ ≤ 2 * A' * (‖z - c‖ / R) / (1 - ‖z - c‖ / R) := by
      rw [le_div_iff₀ h5]
      exact h6
    have h8 : 2 * A' * (‖z - c‖ / R) / (1 - ‖z - c‖ / R) =
        2 * ‖z - c‖ / (R - ‖z - c‖) * A' := by
      have hRρ : R - ‖z - c‖ ≠ 0 := by linarith
      field_simp
    calc ‖g z - g c‖ = ‖f z‖ := rfl
      _ ≤ 2 * A' * (‖z - c‖ / R) / (1 - ‖z - c‖ / R) := h7
      _ = 2 * ‖z - c‖ / (R - ‖z - c‖) * (A - (g c).re) := by rw [h8]

/-! ### §2 The analytic logarithm on zero-free discs -/

/-- A nowhere-zero analytic function on a disc has an analytic logarithm. -/
theorem exists_analyticOnNhd_exp_eq_ball {c : ℂ} {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (ball c R) ∧
      ∀ z ∈ ball c R, Complex.exp (f z) = g z := by
  have hUsc : IsSimplyConnected (ball c R) := by
    haveI : ContractibleSpace (ball c R) := Metric.contractibleSpace_ball hR
    exact SimplyConnectedSpace.ofContractible _
  have hU0 : (0 : ℂ) ∉ g '' ball c R := by
    rintro ⟨z, hz, hgz⟩
    exact hg0 z hz hgz
  obtain ⟨f, hfc, hfeq⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUsc isOpen_ball hg.continuousOn hU0
  exact ⟨f, U0KummerBranch.analyticOnNhd_of_continuousOn_exp_eq isOpen_ball hfc hg
    (fun z hz => hfeq hz), fun z hz => hfeq hz⟩

/-! ### §3 Integrality of positive-real exponentials -/

/-- A complex number whose exponential is a positive real has imaginary part in `2πℤ`. -/
theorem im_eq_int_mul_two_pi_of_exp_pos {w : ℂ} {r : ℝ} (hr : 0 < r)
    (h : Complex.exp w = (r : ℂ)) : ∃ n : ℤ, w.im = n * (2 * Real.pi) := by
  have hre : Real.exp w.re = r := by
    have hn := congrArg norm h
    rwa [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hn
  have h1 : Complex.exp (w - (w.re : ℂ)) = 1 := by
    rw [Complex.exp_sub, h, ← hre, Complex.ofReal_exp]
    exact div_self (Complex.exp_ne_zero _)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] at him
  rw [him]
  ring

/-- A continuous function with values in `2πℤ` on an interval is constant. -/
theorem continuousOn_int_mul_two_pi_const {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b))
    (hint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * (2 * Real.pi)) :
    ∀ τ ∈ Set.Icc a b, F τ = F a := by
  intro τ hτ
  by_contra hne
  have haI : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  obtain ⟨na, hna⟩ := hint a haI
  obtain ⟨nτ, hnτ⟩ := hint τ hτ
  have hFsub : ContinuousOn F (Set.Icc a τ) :=
    hF.mono (Set.Icc_subset_Icc le_rfl hτ.2)
  have hsub : Set.Icc a τ ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hτ.2
  have hπ : 0 < Real.pi := Real.pi_pos
  have hgap : 2 * Real.pi ≤ |F τ - F a| := by
    rw [hna, hnτ]
    have hne' : nτ ≠ na := by
      intro h
      exact hne (by rw [hna, hnτ, h])
    have : (1 : ℝ) ≤ |(nτ : ℝ) - na| := by
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne')
    calc 2 * Real.pi = 1 * (2 * Real.pi) := by ring
      _ ≤ |(nτ : ℝ) - na| * (2 * Real.pi) := by nlinarith
      _ = |(nτ : ℝ) * (2 * Real.pi) - na * (2 * Real.pi)| := by
          rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rcases abs_cases (F τ - F a) with ⟨heq, _⟩ | ⟨heq, _⟩
  · -- F a < F τ, target y := F a + π
    have hlt : F a + Real.pi ≤ F τ := by
      rw [heq] at hgap
      linarith
    obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc hτ.1 hFsub
      (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩ :
        F a + Real.pi ∈ Set.Icc (F a) (F τ))
    obtain ⟨m, hm⟩ := hint σ (hsub hσ)
    rw [hna] at hFσ
    rw [hFσ] at hm
    have hcast : (1 : ℝ) = 2 * ((m : ℝ) - na) := by
      have hπne : Real.pi ≠ 0 := hπ.ne'
      field_simp at hm ⊢
      nlinarith [hm]
    have : (1 : ℤ) = 2 * (m - na) := by exact_mod_cast hcast
    omega
  · -- F τ < F a, target y := F τ + π, IVT on decreasing direction
    have hlt : F τ + Real.pi ≤ F a := by
      rw [heq] at hgap
      linarith
    obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc' hτ.1 hFsub
      (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩ :
        F τ + Real.pi ∈ Set.Icc (F τ) (F a))
    obtain ⟨m, hm⟩ := hint σ (hsub hσ)
    rw [hnτ] at hFσ
    rw [hFσ] at hm
    have hcast : (1 : ℝ) = 2 * ((m : ℝ) - nτ) := by
      have hπne : Real.pi ≠ 0 := hπ.ne'
      field_simp at hm ⊢
      nlinarith [hm]
    have : (1 : ℤ) = 2 * (m - nτ) := by exact_mod_cast hcast
    omega

end RHTower

namespace RHTower

theorem norm_linePt_sub (s t : ℝ) : ‖linePt s - linePt t‖ = |s - t| := by
  have h : linePt s - linePt t = ((s - t : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **The winding-phase advance is capped by the carrier's Borel–Carathéodory budget.**
On a line segment where the completed carrier keeps positive sign, inside a disc where the
finite carrier is zero-free with modulus at most `M` and center modulus strictly below `M`,
the winding-phase advance satisfies
`|Θ(b) − Θ(a)| ≤ (BC(a) + BC(b))·log(M/‖g_N(center)‖)` with the explicit
Borel–Carathéodory prefactors: the phase the archimedean winding spends on the segment is
paid for by the carrier's modulus ratio.  Since the winding rate has an explicit positive
floor at large heights, sign-constant stretches cannot outlive this budget. -/
theorem abs_windingPhase_le_of_sign_constant_zero_free (N : ℕ)
    {τc a b R M : ℝ} (hR0 : 0 < R)
    (hball : ∀ z ∈ ball (linePt τc) R, z.re < 1)
    (hzf : ∀ z ∈ ball (linePt τc) R, gN N z ≠ 0)
    (hM : ∀ z ∈ ball (linePt τc) R, ‖gN N z‖ ≤ M)
    (hlt : ‖gN N (linePt τc)‖ < M)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hpos : ∀ τ ∈ Set.Icc a b, 0 < (completedGN N (linePt τ)).re) :
    |windingPhase a b| ≤
      (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
        (Real.log M - Real.log ‖gN N (linePt τc)‖) := by
  set c : ℂ := linePt τc with hc_def
  have hGan : AnalyticOnNhd ℂ (gN N) (ball c R) := by
    intro z hz
    exact gN_analyticAt (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [hball z hz]))
  obtain ⟨f, hfan, hfeq⟩ := exists_analyticOnNhd_exp_eq_ball hR0 hGan hzf
  have hfre : ∀ z ∈ ball c R, (f z).re = Real.log ‖gN N z‖ := by
    intro z hz
    rw [← hfeq z hz, Complex.norm_exp, Real.log_exp]
  have hcmem : c ∈ ball c R := mem_ball_self hR0
  have hfdiff : DifferentiableOn ℂ f (ball c R) :=
    fun z hz => (hfan z hz).differentiableAt.differentiableWithinAt
  have hRe : ∀ z ∈ ball c R, (f z).re ≤ Real.log M := by
    intro z hz
    rw [hfre z hz]
    exact Real.log_le_log (norm_pos_iff.mpr (hzf z hz)) (hM z hz)
  have hAc : (f c).re < Real.log M := by
    rw [hfre c hcmem]
    exact Real.log_lt_log (norm_pos_iff.mpr (hzf c hcmem)) hlt
  -- the integrality gluing
  set w₀ : ℂ := Complex.log (archFactor (linePt a)) with hw₀_def
  have hw₀ : Complex.exp w₀ = archFactor (linePt a) :=
    Complex.exp_log (archFactor_linePt_ne_zero a)
  set F : ℝ → ℝ := fun τ => w₀.im + windingPhase a τ + (f (linePt τ)).im with hF_def
  have hray := carrier_ray_of_sign_constant N (γ := a) hpos
  have hFint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * (2 * Real.pi) := by
    intro τ hτ
    obtain ⟨r, hr0, hr⟩ := hray τ hτ
    have hGexp : gN N (linePt τ) = Complex.exp (f (linePt τ)) :=
      (hfeq (linePt τ) (hseg τ hτ)).symm
    have hexp : Complex.exp (w₀ + Complex.I * ((windingPhase a τ : ℝ) : ℂ) +
        f (linePt τ)) = (r : ℂ) := by
      rw [Complex.exp_add, Complex.exp_add, hw₀, ← hGexp]
      linear_combination hr
    obtain ⟨n, hn⟩ := im_eq_int_mul_two_pi_of_exp_pos hr0 hexp
    refine ⟨n, ?_⟩
    have him : (w₀ + Complex.I * ((windingPhase a τ : ℝ) : ℂ) + f (linePt τ)).im =
        F τ := by
      simp [F, Complex.add_im, Complex.mul_im]
    rw [← him, hn]
  have hlinecont : Continuous fun τ : ℝ => linePt τ := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_linePt u).continuousAt
  have hΘcont : Continuous (windingPhase a) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_windingPhase a u).continuousAt
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    apply ContinuousOn.add
    · exact (continuousOn_const.add hΘcont.continuousOn)
    · exact Complex.continuous_im.comp_continuousOn
        (hfan.continuousOn.comp hlinecont.continuousOn (fun τ hτ => hseg τ hτ))
  have hFconst := continuousOn_int_mul_two_pi_const hab hFcont hFint
  have hFb := hFconst b (Set.right_mem_Icc.mpr hab)
  have hΘa : windingPhase a a = 0 := intervalIntegral.integral_same
  have hkey : windingPhase a b = (f (linePt a)).im - (f (linePt b)).im := by
    simp only [F] at hFb
    rw [hΘa] at hFb
    linarith
  -- Borel–Carathéodory at the two endpoints
  have hamem : linePt a ∈ ball c R := hseg a (Set.left_mem_Icc.mpr hab)
  have hbmem : linePt b ∈ ball c R := hseg b (Set.right_mem_Icc.mpr hab)
  have hbca := borel_caratheodory hfdiff hRe hAc hamem
  have hbcb := borel_caratheodory hfdiff hRe hAc hbmem
  rw [norm_linePt_sub] at hbca hbcb
  have hfcre : (f c).re = Real.log ‖gN N (linePt τc)‖ := by
    rw [hfre c hcmem, hc_def]
  rw [hfcre] at hbca hbcb
  have htri : |windingPhase a b| ≤ ‖f (linePt a) - f c‖ + ‖f (linePt b) - f c‖ := by
    rw [hkey]
    have h1 : (f (linePt a)).im - (f (linePt b)).im =
        ((f (linePt a) - f c) - (f (linePt b) - f c)).im := by
      simp [Complex.sub_im]
    rw [h1]
    calc |((f (linePt a) - f c) - (f (linePt b) - f c)).im|
        ≤ ‖(f (linePt a) - f c) - (f (linePt b) - f c)‖ :=
          Complex.abs_im_le_norm _
      _ ≤ ‖f (linePt a) - f c‖ + ‖f (linePt b) - f c‖ := norm_sub_le _ _
  calc |windingPhase a b|
      ≤ ‖f (linePt a) - f c‖ + ‖f (linePt b) - f c‖ := htri
    _ ≤ 2 * |a - τc| / (R - |a - τc|) * (Real.log M - Real.log ‖gN N (linePt τc)‖) +
        2 * |b - τc| / (R - |b - τc|) * (Real.log M - Real.log ‖gN N (linePt τc)‖) :=
        add_le_add hbca hbcb
    _ = (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
        (Real.log M - Real.log ‖gN N (linePt τc)‖) := by ring

end RHTower

namespace RHTower

/-- The winding phase advances at least at the winding floor of the left endpoint. -/
theorem windingPhase_ge_of_floor {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2) ≤
      windingPhase a b := by
  have hlow : ∀ u ∈ Set.Icc a b,
      (Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2 ≤ windingRate u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    exact le_trans (winding_floor_expr_mono ha hu.1) (windingRate_ge hu0)
  calc (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2)
      = ∫ _ in a..b, (Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ u in a..b, windingRate u :=
        intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (continuous_windingRate.intervalIntegrable a b) hlow
    _ = windingPhase a b := rfl

/-- **The explicit segment-length law.**  A sign-constant line segment of a zero-free
carrier disc has length at most the Borel–Carathéodory budget divided by the winding floor
of its left endpoint: at height `T` the floor is `≈ ½·log(T/2π)`, so sign-constant
stretches — and with them the admissible anchor radii of the window certificates — shrink
like `1/log T`. -/
theorem sign_constant_segment_length_le (N : ℕ)
    {τc a b R M : ℝ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2)
    (hball : ∀ z ∈ ball (linePt τc) R, z.re < 1)
    (hzf : ∀ z ∈ ball (linePt τc) R, gN N z ≠ 0)
    (hM : ∀ z ∈ ball (linePt τc) R, ‖gN N z‖ ≤ M)
    (hlt : ‖gN N (linePt τc)‖ < M)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hpos : ∀ τ ∈ Set.Icc a b, 0 < (completedGN N (linePt τ)).re) :
    b - a ≤
      (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log M - Real.log ‖gN N (linePt τc)‖) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2) := by
  have h1 := windingPhase_ge_of_floor ha hab
  have h2 := abs_windingPhase_le_of_sign_constant_zero_free N hR0 hball hzf hM hlt
    hab hseg hpos
  have h3 : windingPhase a b ≤ |windingPhase a b| := le_abs_self _
  rw [le_div_iff₀ hflr]
  calc (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2)
      ≤ windingPhase a b := h1
    _ ≤ |windingPhase a b| := h3
    _ ≤ _ := h2

end RHTower
