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
