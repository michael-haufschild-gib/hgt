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
    have h1 : ‖f w‖ ^ (2 : ℕ) = (f w).re ^ (2 : ℕ) + (f w).im ^ (2 : ℕ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h2 : ‖2 * (A' : ℂ) - f w‖ ^ (2 : ℕ) = (2 * A' - (f w).re) ^ (2 : ℕ) + (f w).im ^ (2 : ℕ) := by
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

private theorem continuousOn_int_mul_const_of_pos {F : ℝ → ℝ} {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hF : ContinuousOn F (Set.Icc a b))
    (hint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * δ) :
    ∀ τ ∈ Set.Icc a b, F τ = F a := by
  intro τ hτ
  by_contra hne
  have haI : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  obtain ⟨na, hna⟩ := hint a haI
  obtain ⟨nτ, hnτ⟩ := hint τ hτ
  have hFsub : ContinuousOn F (Set.Icc a τ) :=
    hF.mono (Set.Icc_subset_Icc le_rfl hτ.2)
  have hsub : Set.Icc a τ ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hτ.2
  have hgap : δ ≤ |F τ - F a| := by
    rw [hna, hnτ]
    have hne' : nτ ≠ na := by
      intro h
      exact hne (by rw [hna, hnτ, h])
    have : (1 : ℝ) ≤ |(nτ : ℝ) - na| := by
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne')
    calc δ = 1 * δ := by ring
      _ ≤ |(nτ : ℝ) - na| * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = |(nτ : ℝ) * δ - na * δ| := by
          rw [← sub_mul, abs_mul, abs_of_pos hδ]
  rcases abs_cases (F τ - F a) with ⟨heq, _⟩ | ⟨heq, _⟩
  · have hlt : F a + δ / 2 ≤ F τ := by
      rw [heq] at hgap
      linarith
    obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc hτ.1 hFsub
      (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩ :
        F a + δ / 2 ∈ Set.Icc (F a) (F τ))
    obtain ⟨m, hm⟩ := hint σ (hsub hσ)
    rw [hna] at hFσ
    rw [hFσ] at hm
    have h2 : ((m : ℝ) - (na : ℝ)) * δ = (1 / 2) * δ := by linarith
    have h3 := mul_right_cancel₀ hδ.ne' h2
    have h4 : ((2 * m - 2 * na : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h5 : (2 * m - 2 * na : ℤ) = 1 := by exact_mod_cast h4
    omega
  · have hlt : F τ + δ / 2 ≤ F a := by
      rw [heq] at hgap
      linarith
    obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc' hτ.1 hFsub
      (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩ :
        F τ + δ / 2 ∈ Set.Icc (F τ) (F a))
    obtain ⟨m, hm⟩ := hint σ (hsub hσ)
    rw [hnτ] at hFσ
    rw [hFσ] at hm
    have h2 : ((m : ℝ) - (nτ : ℝ)) * δ = (1 / 2) * δ := by linarith
    have h3 := mul_right_cancel₀ hδ.ne' h2
    have h4 : ((2 * m - 2 * nτ : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h5 : (2 * m - 2 * nτ : ℤ) = 1 := by exact_mod_cast h4
    omega

/-- **Continuous lattice rigidity on an interval.** A continuous real-valued function whose
values all lie in one nontrivial integral lattice `δℤ` is constant. The lattice generator need
not be positively oriented. -/
theorem continuousOn_int_mul_const {F : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : δ ≠ 0)
    (hF : ContinuousOn F (Set.Icc a b))
    (hint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * δ) :
    ∀ τ ∈ Set.Icc a b, F τ = F a := by
  rcases lt_or_gt_of_ne hδ with hδneg | hδpos
  · apply continuousOn_int_mul_const_of_pos hab (neg_pos.mpr hδneg) hF
    intro τ hτ
    obtain ⟨n, hn⟩ := hint τ hτ
    refine ⟨-n, ?_⟩
    rw [hn]
    push_cast
    ring
  · exact continuousOn_int_mul_const_of_pos hab hδpos hF hint

/-- A continuous function with values in `2πℤ` on an interval is constant. -/
theorem continuousOn_int_mul_two_pi_const {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b))
    (hint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * (2 * Real.pi)) :
    ∀ τ ∈ Set.Icc a b, F τ = F a :=
  continuousOn_int_mul_const hab (mul_ne_zero (by norm_num) Real.pi_ne_zero) hF hint

/-- A complex number whose exponential is a nonzero real has imaginary part in `πℤ`. -/
theorem im_eq_int_mul_pi_of_exp_real {w : ℂ} {r : ℝ} (hr : r ≠ 0)
    (h : Complex.exp w = (r : ℂ)) : ∃ n : ℤ, w.im = n * Real.pi := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hexp : Complex.exp (w - (Real.pi : ℂ) * Complex.I) = ((-r : ℝ) : ℂ) := by
      rw [Complex.exp_sub, h, Complex.exp_pi_mul_I]
      push_cast
      ring
    obtain ⟨n, hn⟩ := im_eq_int_mul_two_pi_of_exp_pos
      (by linarith : (0 : ℝ) < -r) hexp
    refine ⟨2 * n + 1, ?_⟩
    have him : (w - (Real.pi : ℂ) * Complex.I).im = w.im - Real.pi := by
      simp [Complex.sub_im, Complex.mul_im]
    rw [him] at hn
    push_cast
    linarith [hn]
  · obtain ⟨n, hn⟩ := im_eq_int_mul_two_pi_of_exp_pos hpos h
    refine ⟨2 * n, ?_⟩
    rw [hn]
    push_cast
    ring

/-- A continuous function with values in `πℤ` on an interval is constant. -/
theorem continuousOn_int_mul_pi_const {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b))
    (hint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * Real.pi) :
    ∀ τ ∈ Set.Icc a b, F τ = F a :=
  continuousOn_int_mul_const hab Real.pi_ne_zero hF hint

end RHTower

namespace RHTower

theorem norm_linePt_sub (s t : ℝ) : ‖linePt s - linePt t‖ = |s - t| := by
  have h : linePt s - linePt t = ((s - t : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **The winding-phase advance is capped by the carrier's Borel–Carathéodory budget.**
On a line segment where the (real) completed carrier does not vanish, inside a disc where
the finite carrier is zero-free with modulus at most `M` and center modulus strictly below
`M`, the winding-phase advance satisfies
`|Θ(b) − Θ(a)| ≤ (BC(a) + BC(b))·log(M/‖g_N(center)‖)` with the explicit
Borel–Carathéodory prefactors: the phase the archimedean winding spends on the segment is
paid for by the carrier's modulus ratio.  Since the winding rate has an explicit positive
floor at large heights, nonvanishing stretches cannot outlive this budget. -/
theorem abs_windingPhase_le_of_sign_constant_zero_free (N : ℕ)
    {τc a b R M : ℝ} (hR0 : 0 < R)
    (hball : ∀ z ∈ ball (linePt τc) R, z.re < 1)
    (hzf : ∀ z ∈ ball (linePt τc) R, gN N z ≠ 0)
    (hM : ∀ z ∈ ball (linePt τc) R, ‖gN N z‖ ≤ M)
    (hlt : ‖gN N (linePt τc)‖ < M)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hsgn : ∀ τ ∈ Set.Icc a b, (completedGN N (linePt τ)).re ≠ 0) :
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
  have hray := carrier_ray_of_sign_ne_zero N (γ := a) hsgn
  have hFint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * Real.pi := by
    intro τ hτ
    obtain ⟨r, hr0, hr⟩ := hray τ hτ
    have hGexp : gN N (linePt τ) = Complex.exp (f (linePt τ)) :=
      (hfeq (linePt τ) (hseg τ hτ)).symm
    have hexp : Complex.exp (w₀ + Complex.I * ((windingPhase a τ : ℝ) : ℂ) +
        f (linePt τ)) = (r : ℂ) := by
      rw [Complex.exp_add, Complex.exp_add, hw₀, ← hGexp]
      linear_combination hr
    obtain ⟨n, hn⟩ := im_eq_int_mul_pi_of_exp_real hr0 hexp
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
  have hFconst := continuousOn_int_mul_pi_const hab hFcont hFint
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
    (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) ≤
      windingPhase a b := by
  have hlow : ∀ u ∈ Set.Icc a b,
      (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2 ≤ windingRate u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    exact le_trans (winding_floor_expr_mono ha hu.1) (windingRate_ge hu0)
  calc (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
      = ∫ _ in a..b, (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2 := by
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
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hball : ∀ z ∈ ball (linePt τc) R, z.re < 1)
    (hzf : ∀ z ∈ ball (linePt τc) R, gN N z ≠ 0)
    (hM : ∀ z ∈ ball (linePt τc) R, ‖gN N z‖ ≤ M)
    (hlt : ‖gN N (linePt τc)‖ < M)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hsgn : ∀ τ ∈ Set.Icc a b, (completedGN N (linePt τ)).re ≠ 0) :
    b - a ≤
      (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log M - Real.log ‖gN N (linePt τc)‖) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) := by
  have h1 := windingPhase_ge_of_floor ha hab
  have h2 := abs_windingPhase_le_of_sign_constant_zero_free N hR0 hball hzf hM hlt
    hab hseg hsgn
  have h3 : windingPhase a b ≤ |windingPhase a b| := le_abs_self _
  rw [le_div_iff₀ hflr]
  calc (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
      ≤ windingPhase a b := h1
    _ ≤ |windingPhase a b| := h3
    _ ≤ _ := h2

end RHTower

namespace RHTower

/-- A line segment avoiding a point admits a unit rotation placing the linear factor in
the open right half-plane. -/
theorem exists_unit_re_pos_linear_factor {ρ' : ℂ} {a b : ℝ}
    (hne : ∀ τ ∈ Set.Icc a b, linePt τ ≠ ρ') :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ τ ∈ Set.Icc a b, 0 < (u * (linePt τ - ρ')).re := by
  have hre : ∀ τ : ℝ, (linePt τ - ρ').re = 1 / 2 - ρ'.re := by
    intro τ
    unfold linePt
    simp
  have him : ∀ τ : ℝ, (linePt τ - ρ').im = τ - ρ'.im := by
    intro τ
    unfold linePt
    simp
  rcases lt_trichotomy ρ'.re (1 / 2) with hx | hx | hx
  · refine ⟨1, one_ne_zero, fun τ hτ => ?_⟩
    rw [one_mul, hre]
    linarith
  · have hy : ρ'.im < a ∨ b < ρ'.im := by
      by_contra hcon
      push Not at hcon
      refine hne ρ'.im ⟨hcon.1, hcon.2⟩ (Complex.ext ?_ ?_)
      · rw [linePt_re, hx]
      · unfold linePt
        simp
    rcases hy with hy | hy
    · refine ⟨-Complex.I, by simp, fun τ hτ => ?_⟩
      rw [Complex.mul_re]
      simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
      rw [him]
      have := hτ.1
      norm_num
      linarith
    · refine ⟨Complex.I, Complex.I_ne_zero, fun τ hτ => ?_⟩
      rw [Complex.mul_re]
      simp only [Complex.I_re, Complex.I_im]
      rw [him]
      have := hτ.2
      norm_num
      linarith
  · refine ⟨-1, by norm_num, fun τ hτ => ?_⟩
    rw [Complex.mul_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    rw [hre]
    norm_num
    linarith

/-- **One-zero segment law, phase side.**  On a sign-constant line segment inside a disc
where the finite carrier factors through a single point `ρ'` with nowhere-zero difference
quotient, the winding-phase advance is capped by `π` — the linear factor's half-turn —
plus the difference quotient's Borel–Carathéodory budget. -/
theorem abs_windingPhase_le_of_sign_constant_one_zero (N : ℕ)
    {τc a b R Md : ℝ} {ρ' : ℂ} (hR0 : 0 < R)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hsgn : ∀ τ ∈ Set.Icc a b, (completedGN N (linePt τ)).re ≠ 0) :
    |windingPhase a b| ≤ Real.pi +
      (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
        (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖) := by
  set c : ℂ := linePt τc with hc_def
  set ds : ℂ → ℂ := dslope (gN N) ρ' with hds_def
  have hgNne : ∀ τ ∈ Set.Icc a b, gN N (linePt τ) ≠ 0 := by
    intro τ hτ h0
    have hΦ : completedGN N (linePt τ) = 0 := by
      show archFactor (linePt τ) * gN N (linePt τ) = 0
      rw [h0, mul_zero]
    have := hsgn τ hτ
    rw [hΦ] at this
    simp at this
  have hne : ∀ τ ∈ Set.Icc a b, linePt τ ≠ ρ' := by
    intro τ hτ heq
    apply hgNne τ hτ
    rw [hfact (linePt τ) (hseg τ hτ), heq, sub_self, zero_mul]
  obtain ⟨u, hu0, hupos⟩ := exists_unit_re_pos_linear_factor hne
  obtain ⟨f, hfan, hfeq⟩ := exists_analyticOnNhd_exp_eq_ball hR0 hd_an hd_ne
  have hfre : ∀ z ∈ ball c R, (f z).re = Real.log ‖ds z‖ := by
    intro z hz
    rw [← hfeq z hz, Complex.norm_exp, Real.log_exp]
  have hcmem : c ∈ ball c R := mem_ball_self hR0
  have hfdiff : DifferentiableOn ℂ f (ball c R) :=
    fun z hz => (hfan z hz).differentiableAt.differentiableWithinAt
  have hRe : ∀ z ∈ ball c R, (f z).re ≤ Real.log Md := by
    intro z hz
    rw [hfre z hz]
    exact Real.log_le_log (norm_pos_iff.mpr (hd_ne z hz)) (hMd z hz)
  have hAc : (f c).re < Real.log Md := by
    rw [hfre c hcmem]
    exact Real.log_lt_log (norm_pos_iff.mpr (hd_ne c hcmem)) hltd
  set w₀ : ℂ := Complex.log (archFactor (linePt a)) with hw₀_def
  have hw₀ : Complex.exp w₀ = archFactor (linePt a) :=
    Complex.exp_log (archFactor_linePt_ne_zero a)
  have huκne : ∀ τ ∈ Set.Icc a b, u * (linePt τ - ρ') ≠ 0 := by
    intro τ hτ h0
    have := hupos τ hτ
    rw [h0] at this
    simp at this
  set F : ℝ → ℝ := fun τ => w₀.im + windingPhase a τ +
    ((Complex.log (u * (linePt τ - ρ'))).im - (Complex.log u).im) +
      (f (linePt τ)).im with hF_def
  have hray := carrier_ray_of_sign_ne_zero N (γ := a) hsgn
  have hFint : ∀ τ ∈ Set.Icc a b, ∃ n : ℤ, F τ = n * Real.pi := by
    intro τ hτ
    obtain ⟨r, hr0, hr⟩ := hray τ hτ
    have hdsexp : ds (linePt τ) = Complex.exp (f (linePt τ)) :=
      (hfeq (linePt τ) (hseg τ hτ)).symm
    have hκ : linePt τ - ρ' =
        Complex.exp (Complex.log (u * (linePt τ - ρ')) - Complex.log u) := by
      rw [Complex.exp_sub, Complex.exp_log (huκne τ hτ), Complex.exp_log hu0,
        mul_div_cancel_left₀ _ hu0]
    have hexp : Complex.exp (w₀ + Complex.I * ((windingPhase a τ : ℝ) : ℂ) +
        (Complex.log (u * (linePt τ - ρ')) - Complex.log u) + f (linePt τ)) =
        (r : ℂ) := by
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, hw₀, ← hκ, ← hdsexp]
      have hgN : gN N (linePt τ) = (linePt τ - ρ') * ds (linePt τ) :=
        hfact (linePt τ) (hseg τ hτ)
      rw [← hr, hgN]
      ring
    obtain ⟨n, hn⟩ := im_eq_int_mul_pi_of_exp_real hr0 hexp
    refine ⟨n, ?_⟩
    have him : (w₀ + Complex.I * ((windingPhase a τ : ℝ) : ℂ) +
        (Complex.log (u * (linePt τ - ρ')) - Complex.log u) + f (linePt τ)).im =
        F τ := by
      simp [F, Complex.add_im, Complex.sub_im, Complex.mul_im]
    rw [← him, hn]
  have hlinecont : Continuous fun τ : ℝ => linePt τ := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (hasDerivAt_linePt v).continuousAt
  have hΘcont : Continuous (windingPhase a) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (hasDerivAt_windingPhase a v).continuousAt
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    apply ContinuousOn.add
    apply ContinuousOn.add
    · exact continuousOn_const.add hΘcont.continuousOn
    · apply ContinuousOn.sub _ continuousOn_const
      apply Complex.continuous_im.comp_continuousOn
      intro τ hτ
      have hcont1 : ContinuousAt (fun τ : ℝ => u * (linePt τ - ρ')) τ := by
        fun_prop
      have hcomp : ContinuousAt
          (Complex.log ∘ fun τ : ℝ => u * (linePt τ - ρ')) τ :=
        ContinuousAt.comp (continuousAt_clog (Or.inl (hupos τ hτ))) hcont1
      exact hcomp.continuousWithinAt
    · exact Complex.continuous_im.comp_continuousOn
        (hfan.continuousOn.comp hlinecont.continuousOn (fun τ hτ => hseg τ hτ))
  have hFconst := continuousOn_int_mul_pi_const hab hFcont hFint
  have hFb := hFconst b (Set.right_mem_Icc.mpr hab)
  have hΘa : windingPhase a a = 0 := intervalIntegral.integral_same
  have hkey : windingPhase a b =
      ((Complex.log (u * (linePt a - ρ'))).im - (Complex.log (u * (linePt b - ρ'))).im) +
        ((f (linePt a)).im - (f (linePt b)).im) := by
    simp only [F] at hFb
    rw [hΘa] at hFb
    linarith
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hbmem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have harg : ∀ τ ∈ Set.Icc a b,
      |(Complex.log (u * (linePt τ - ρ'))).im| ≤ Real.pi / 2 := by
    intro τ hτ
    rw [Complex.log_im]
    exact le_of_lt (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hupos τ hτ)))
  have hbca := borel_caratheodory hfdiff hRe hAc (hseg a hamem)
  have hbcb := borel_caratheodory hfdiff hRe hAc (hseg b hbmem)
  rw [norm_linePt_sub] at hbca hbcb
  have hfcre : (f c).re = Real.log ‖ds c‖ := hfre c hcmem
  rw [hfcre] at hbca hbcb
  have htri2 : |(f (linePt a)).im - (f (linePt b)).im| ≤
      ‖f (linePt a) - f c‖ + ‖f (linePt b) - f c‖ := by
    have h1 : (f (linePt a)).im - (f (linePt b)).im =
        ((f (linePt a) - f c) - (f (linePt b) - f c)).im := by
      simp [Complex.sub_im]
    rw [h1]
    calc |((f (linePt a) - f c) - (f (linePt b) - f c)).im|
        ≤ ‖(f (linePt a) - f c) - (f (linePt b) - f c)‖ := Complex.abs_im_le_norm _
      _ ≤ ‖f (linePt a) - f c‖ + ‖f (linePt b) - f c‖ := norm_sub_le _ _
  have habs := abs_add_le
    ((Complex.log (u * (linePt a - ρ'))).im - (Complex.log (u * (linePt b - ρ'))).im)
    ((f (linePt a)).im - (f (linePt b)).im)
  have hargab : |(Complex.log (u * (linePt a - ρ'))).im -
      (Complex.log (u * (linePt b - ρ'))).im| ≤ Real.pi := by
    have h1 := harg a hamem
    have h2 := harg b hbmem
    have := abs_sub ((Complex.log (u * (linePt a - ρ'))).im)
      ((Complex.log (u * (linePt b - ρ'))).im)
    calc |(Complex.log (u * (linePt a - ρ'))).im -
        (Complex.log (u * (linePt b - ρ'))).im|
        ≤ |(Complex.log (u * (linePt a - ρ'))).im| +
          |(Complex.log (u * (linePt b - ρ'))).im| := abs_sub _ _
      _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add h1 h2
      _ = Real.pi := by ring
  calc |windingPhase a b|
      ≤ |(Complex.log (u * (linePt a - ρ'))).im -
          (Complex.log (u * (linePt b - ρ'))).im| +
        |(f (linePt a)).im - (f (linePt b)).im| := by
        rw [hkey]
        exact habs
    _ ≤ Real.pi + (‖f (linePt a) - f c‖ + ‖f (linePt b) - f c‖) :=
        add_le_add hargab htri2
    _ ≤ Real.pi +
        (2 * |a - τc| / (R - |a - τc|) * (Real.log Md - Real.log ‖ds c‖) +
         2 * |b - τc| / (R - |b - τc|) * (Real.log Md - Real.log ‖ds c‖)) := by
        exact add_le_add le_rfl (add_le_add hbca hbcb)
    _ = Real.pi +
        (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log Md - Real.log ‖ds c‖) := by ring

/-- **One-zero segment-length law.**  A sign-constant line segment of a one-zero carrier
disc has length at most `(π + Borel–Carathéodory budget)/windingFloor`: the admissible
sign-constant stretch — and with it the anchored-window radius — shrinks like `1/log T`
even in the presence of the single carrier zero the Jensen face permits. -/
theorem sign_constant_segment_length_le_one_zero (N : ℕ)
    {τc a b R Md : ℝ} {ρ' : ℂ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hsgn : ∀ τ ∈ Set.Icc a b, (completedGN N (linePt τ)).re ≠ 0) :
    b - a ≤
      (Real.pi + (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) := by
  have h1 := windingPhase_ge_of_floor ha hab
  have h2 := abs_windingPhase_le_of_sign_constant_one_zero N hR0 hd_an hd_ne hfact
    hMd hltd hab hseg hsgn
  rw [le_div_iff₀ hflr]
  calc (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
      ≤ windingPhase a b := h1
    _ ≤ |windingPhase a b| := le_abs_self _
    _ ≤ _ := h2

end RHTower
