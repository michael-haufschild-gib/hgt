import GaloisForLFunctions.RHTower.XiMassShellRatio
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderCells

/-!
# The shell asymptotic

Assembling the Fourier–Bessel identity, the Schläfli remainder bound and the shell ratio bound
gives the uniform relative asymptotic on a spacelike shell:

`‖K_u(κu+s) − Λ(u,s)‖ ≤ (C/u)·|Λ(u,s)|`,  `0 ≤ s ≤ L`,

where `Λ` is the damped leading amplitude, a positive real multiple of one fixed unit phase.  Every
constant is explicit and independent of `s` on the window.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The modulus of the propagation radius -/

theorem norm_shellArgument_le {sigma kappa u s L : ℝ} (hkappa : 1 < kappa) (hu : 1 ≤ u)
    (hs : 0 ≤ s) (hsL : s ≤ L) (hsigma : 0 < sigma) :
    ‖xiMassShellArgument sigma kappa u s‖
      ≤ (shellQ kappa ^ (2 : ℕ) + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) * u ^ (2 : ℕ) := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqsq : shellQ kappa ^ (2 : ℕ) = kappa ^ (2 : ℕ) - 1 := shellQ_sq hkappa
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hL : 0 ≤ L := le_trans hs hsL
  have hre : (xiMassShellArgument sigma kappa u s).re
      = (kappa ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) + 2 * kappa * u * s + (sigma ^ (2 : ℕ) + s ^ (2 : ℕ)) :=
    xiMassShellArgument_re sigma kappa u s
  have him : (xiMassShellArgument sigma kappa u s).im = 2 * sigma * u := by
    rw [xiMassShellArgument]
    simp [Complex.add_im, Complex.mul_im, pow_two]
    ring
  have hbound := Complex.norm_le_abs_re_add_abs_im (xiMassShellArgument sigma kappa u s)
  rw [hre, him] at hbound
  refine le_trans hbound ?_
  have habs1 : |(kappa ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) + 2 * kappa * u * s + (sigma ^ (2 : ℕ) + s ^ (2 : ℕ))|
      = (kappa ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) + 2 * kappa * u * s + (sigma ^ (2 : ℕ) + s ^ (2 : ℕ)) := by
    refine abs_of_nonneg ?_
    have hk1a : (0 : ℝ) ≤ kappa - 1 := by linarith
    have hk1b : (0 : ℝ) ≤ kappa + 1 := by linarith
    have hk1 : (0 : ℝ) ≤ kappa ^ (2 : ℕ) - 1 := by nlinarith [mul_nonneg hk1a hk1b]
    have h1 : (0 : ℝ) ≤ (kappa ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) := mul_nonneg hk1 (sq_nonneg u)
    have h2 : (0 : ℝ) ≤ 2 * kappa * u * s := by positivity
    nlinarith [sq_nonneg sigma, sq_nonneg s, h1, h2]
  have habs2 : |2 * sigma * u| = 2 * sigma * u := abs_of_nonneg (by positivity)
  rw [habs1, habs2, hqsq]
  have hu2 : u ≤ u ^ (2 : ℕ) := by nlinarith
  have hone : (1 : ℝ) ≤ u ^ (2 : ℕ) := by nlinarith
  have h1 : u * s ≤ u ^ (2 : ℕ) * L := by nlinarith [hs, hsL, hu2, hL, hu0]
  have h2 : s ^ (2 : ℕ) ≤ L ^ (2 : ℕ) * u ^ (2 : ℕ) := by nlinarith [hs, hsL, hone, hL]
  have p1 : (0 : ℝ) ≤ 2 * kappa * (u ^ (2 : ℕ) * L - u * s) := by nlinarith [h1, hkappa0]
  have p2 : (0 : ℝ) ≤ sigma ^ (2 : ℕ) * (u ^ (2 : ℕ) - 1) := by nlinarith [hone, sq_nonneg sigma]
  have p3 : (0 : ℝ) ≤ L ^ (2 : ℕ) * u ^ (2 : ℕ) - s ^ (2 : ℕ) := by linarith [h2]
  have p4 : (0 : ℝ) ≤ 2 * sigma * (u ^ (2 : ℕ) - u) := by nlinarith [hu2, hsigma.le]
  linarith [p1, p2, p3, p4]

theorem norm_shellRoot_le {sigma kappa u s L : ℝ} (hkappa : 1 < kappa) (hu : 1 ≤ u)
    (hs : 0 ≤ s) (hsL : s ≤ L) (hsigma : 0 < sigma) :
    ‖shellRoot sigma kappa u s‖
      ≤ Real.sqrt (shellQ kappa ^ (2 : ℕ) + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) * u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hpos := xiMassShellArgument_re_pos hkappa hu0 hs hsigma
  have hbound := norm_shellArgument_le hkappa hu hs hsL hsigma
  have hL : (0 : ℝ) ≤ L := le_trans hs hsL
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hK0 : (0 : ℝ) ≤ shellQ kappa ^ (2 : ℕ) + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma) := by
    have h1 : (0 : ℝ) ≤ 2 * kappa * L := by positivity
    nlinarith [sq_nonneg (shellQ kappa), sq_nonneg sigma, sq_nonneg L, hsigma.le]
  rw [shellRoot, HTGeometry.norm_csqrt hpos]
  calc Real.sqrt ‖xiMassShellArgument sigma kappa u s‖
      ≤ Real.sqrt ((shellQ kappa ^ (2 : ℕ) + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) * u ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (shellQ kappa ^ (2 : ℕ) + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) * u := by
        rw [Real.sqrt_mul hK0, Real.sqrt_sq hu0.le]


/-! ## The relative asymptotic -/

/-- The relative size of the Schläfli remainder on a shell. -/
theorem shellRemainder_relative_le {a sigma kappa u s L : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hkappa : 1 < kappa) (hu : 1 ≤ u) (hs : 0 ≤ s) (hsL : s ≤ L) :
    2 / (Real.exp 1 * (a * (shellRoot sigma kappa u s).re))
        * Real.sqrt (2 * ‖shellRoot sigma kappa u s‖ / (shellRoot sigma kappa u s).re)
      ≤ (2 * Real.sqrt (2 * Real.sqrt (shellQ kappa ^ (2 : ℕ)
            + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) / shellQ kappa)
          / (Real.exp 1 * a * shellQ kappa)) / u := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hqu : (0 : ℝ) < shellQ kappa * u := mul_pos hq hu0
  have hZre : shellQ kappa * u ≤ (shellRoot sigma kappa u s).re :=
    shellRoot_re_ge hkappa hu0 hs hsigma
  have hZre0 : (0 : ℝ) < (shellRoot sigma kappa u s).re := lt_of_lt_of_le hqu hZre
  have hZn := norm_shellRoot_le hkappa hu hs hsL hsigma
  have hSq : (0 : ℝ) ≤ Real.sqrt (shellQ kappa ^ (2 : ℕ)
      + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) := Real.sqrt_nonneg _
  have hratio : 2 * ‖shellRoot sigma kappa u s‖ / (shellRoot sigma kappa u s).re
      ≤ 2 * Real.sqrt (shellQ kappa ^ (2 : ℕ)
        + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) / shellQ kappa := by
    rw [div_le_div_iff₀ hZre0 hq]
    have h1 : 2 * ‖shellRoot sigma kappa u s‖ ≤ 2 * (Real.sqrt (shellQ kappa ^ (2 : ℕ)
        + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) * u) := by linarith [hZn]
    nlinarith [h1, hZre, hq, hu0, hSq, hZre0]
  have hfirst : 2 / (Real.exp 1 * (a * (shellRoot sigma kappa u s).re))
      ≤ 2 / (Real.exp 1 * (a * (shellQ kappa * u))) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    have hpos : (0 : ℝ) < Real.exp 1 * a := by positivity
    nlinarith [hZre, hpos]
  have hsecond : Real.sqrt (2 * ‖shellRoot sigma kappa u s‖ / (shellRoot sigma kappa u s).re)
      ≤ Real.sqrt (2 * Real.sqrt (shellQ kappa ^ (2 : ℕ)
        + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) / shellQ kappa) :=
    Real.sqrt_le_sqrt hratio
  have hstep := mul_le_mul hfirst hsecond (Real.sqrt_nonneg _) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp


/-- **(17.20) The uniform shell asymptotic.**  On every window `0 ≤ s ≤ L` the damped mass profile
agrees with its rapidity model to relative order `1/u`. -/
theorem exists_shellProfile_relative_error {a sigma kappa L : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hkappa : 1 < kappa) (hL : 0 ≤ L) :
    ∃ C u₀ : ℝ, 0 < C ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ s : ℝ, 0 ≤ s → s ≤ L →
      ‖xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s‖
        ≤ C / u * shellModulus a kappa u s := by
  classical
  obtain ⟨C₁, u₁, hC₁, hu₁, hR⟩ := exists_shellRatio_bound ha hsigma hkappa hL
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, 2 * Real.sqrt (2 * Real.sqrt (shellQ kappa ^ (2 : ℕ)
      + (2 * kappa * L + sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + 2 * sigma)) / shellQ kappa)
      / (Real.exp 1 * a * shellQ kappa) = C₂ := ⟨_, rfl⟩
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hC₂0 : 0 ≤ C₂ := by
    rw [← hC₂]
    positivity
  refine ⟨C₁ + 2 * C₂ + 1, max u₁ (max 1 C₁), by positivity,
    le_trans (le_max_left 1 C₁) (le_max_right _ _), fun u hu s hs hsL => ?_⟩
  have hu1' : u₁ ≤ u := le_trans (le_max_left _ _) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (le_trans (le_max_left 1 C₁) (le_max_right u₁ _)) hu
  have hC₁u : C₁ ≤ u := le_trans (le_trans (le_max_right 1 C₁) (le_max_right u₁ _)) hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hRbound := hR u hu1' s hs hsL
  have hh0 : (0 : ℝ) < kappa * u + s := by nlinarith [lt_trans zero_lt_one hkappa]
  have hstrip : ((sigma : ℂ) + (u : ℂ) * I) ∈ xiMassBesselStrip (kappa * u + s) := by
    refine ⟨by simpa using hsigma, ?_⟩
    have him : ((sigma : ℂ) + (u : ℂ) * I).im = u := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him, abs_of_pos hu0]
    nlinarith [hkappa, hu0, hs]
  have hZre : 0 < (shellRoot sigma kappa u s).re := shellRoot_re_pos hkappa hu0 hs hsigma
  have haZre : 0 < ((a : ℂ) * shellRoot sigma kappa u s).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos ha hZre
  have hfb := stripFourier_xiMass_eq_bessel (a := a) (h := kappa * u + s)
    (τ := (sigma : ℂ) + (u : ℂ) * I) ha hh0 hstrip
  -- the profile in Bessel form
  have hprofile : xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
      = ((Real.exp (-((kappa * u + s) / 2)) : ℝ) : ℂ)
        * (2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s
          * HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)) := by
    rw [xiMassCriticalDampedFourierProfile, hfb]
    congr 2
    · rw [neg_div]
  -- the leading/remainder split
  have hsplitK : HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)
      = Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
          * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s))
        + (HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)
          - Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
            * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
            * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s))) := by
    ring
  have hcollapse := besselLeading_collapse (a := a) (τ := (sigma : ℂ) + (u : ℂ) * I)
    (z := shellRoot sigma kappa u s) ha hZre
  obtain ⟨Model, hMdef⟩ : ∃ M : ℂ,
      ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((u : ℂ) * I)
        * Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
        / (((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ)) = M :=
    ⟨_, rfl⟩
  have hmodel : ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((sigma : ℂ) + (u : ℂ) * I)
      * Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
      / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s))
      = Model * shellRatio a sigma kappa u s := by
    rw [← hMdef]
    exact shellLeading_eq_model_mul_ratio hkappa hu0 hs hsigma
  have hEmodel : shellLeadingDamped a sigma kappa u s
      = ((Real.exp (-((kappa * u + s) / 2)) : ℝ) : ℂ) * Model := by
    rw [← hMdef]
    rfl
  have hdiff : xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
      - shellLeadingDamped a sigma kappa u s
      = ((Real.exp (-((kappa * u + s) / 2)) : ℝ) : ℂ)
        * (Model * (shellRatio a sigma kappa u s - 1)
          + 2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s
            * (HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)
              - Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
                * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
                * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s)))) := by
    rw [hprofile, hEmodel, hsplitK, mul_add, hcollapse, hmodel]
    ring
  have hE : ‖((Real.exp (-((kappa * u + s) / 2)) : ℝ) : ℂ)‖
      = Real.exp (-((kappa * u + s) / 2)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmod : shellModulus a kappa u s = Real.exp (-((kappa * u + s) / 2)) * ‖Model‖ := by
    rw [← norm_shellLeadingDamped (sigma := sigma) ha hkappa hu0, hEmodel, norm_mul, hE]
  have hRnorm : ‖shellRatio a sigma kappa u s‖ ≤ 2 := by
    have hsplit : shellRatio a sigma kappa u s = (shellRatio a sigma kappa u s - 1) + 1 := by ring
    have hC₁1 : C₁ / u ≤ 1 := by
      rw [div_le_one hu0]
      exact hC₁u
    calc ‖shellRatio a sigma kappa u s‖
        = ‖(shellRatio a sigma kappa u s - 1) + 1‖ := by rw [← hsplit]
      _ ≤ ‖shellRatio a sigma kappa u s - 1‖ + 1 := by
          simpa using norm_add_le (shellRatio a sigma kappa u s - 1) (1 : ℂ)
      _ ≤ 2 := by linarith [hRbound, hC₁1]
  have hleadnorm : ‖2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s‖
      * ‖Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s))‖
      = ‖Model‖ * ‖shellRatio a sigma kappa u s‖ := by
    rw [← norm_mul, hcollapse, hmodel, norm_mul]
  have hrem := norm_besselRemainder_le_relative (a := a) (Z := shellRoot sigma kappa u s) ha hZre
  rw [← norm_besselLeadingFactor ha hZre] at hrem
  have hρ := shellRemainder_relative_le (a := a) (sigma := sigma) (kappa := kappa) (u := u)
    (s := s) (L := L) ha hsigma hkappa hu1 hs hsL
  rw [hC₂] at hρ
  have hcoef0 : (0 : ℝ)
      ≤ ‖2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s‖ := norm_nonneg _
  have hTbound : ‖2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s
      * (HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)
        - Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
          * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s)))‖
      ≤ C₂ / u * (‖Model‖ * 2) := by
    rw [norm_mul]
    have hstep := mul_le_mul_of_nonneg_left hrem hcoef0
    refine le_trans hstep ?_
    have hrew : ‖2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s‖
        * (2 / (Real.exp 1 * (a * (shellRoot sigma kappa u s).re))
            * Real.sqrt (2 * ‖shellRoot sigma kappa u s‖ / (shellRoot sigma kappa u s).re)
          * ‖Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
            * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
            * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s))‖)
        = (2 / (Real.exp 1 * (a * (shellRoot sigma kappa u s).re))
            * Real.sqrt (2 * ‖shellRoot sigma kappa u s‖ / (shellRoot sigma kappa u s).re))
          * (‖Model‖ * ‖shellRatio a sigma kappa u s‖) := by
      rw [← hleadnorm]
      ring
    rw [hrew]
    have hM0 : (0 : ℝ) ≤ ‖Model‖ := norm_nonneg _
    have hρ0 : (0 : ℝ) ≤ 2 / (Real.exp 1 * (a * (shellRoot sigma kappa u s).re))
        * Real.sqrt (2 * ‖shellRoot sigma kappa u s‖ / (shellRoot sigma kappa u s).re) := by
      have h1 : (0 : ℝ) < Real.exp 1 * (a * (shellRoot sigma kappa u s).re) := by positivity
      positivity
    have hprod : ‖Model‖ * ‖shellRatio a sigma kappa u s‖ ≤ ‖Model‖ * 2 :=
      mul_le_mul_of_nonneg_left hRnorm hM0
    have hC₂u0 : (0 : ℝ) ≤ C₂ / u := by positivity
    nlinarith [hρ, hprod, hρ0, hM0, mul_nonneg hM0 (by norm_num : (0:ℝ) ≤ 2)]
  rw [hdiff, norm_mul, hE, hmod]
  have hM0 : (0 : ℝ) ≤ ‖Model‖ := norm_nonneg _
  have hE0 : (0 : ℝ) < Real.exp (-((kappa * u + s) / 2)) := Real.exp_pos _
  have hinner : ‖Model * (shellRatio a sigma kappa u s - 1)
      + 2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s
        * (HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)
          - Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
            * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
            * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s)))‖
      ≤ (C₁ + 2 * C₂ + 1) / u * ‖Model‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
    have h1 : ‖Model‖ * ‖shellRatio a sigma kappa u s - 1‖ ≤ ‖Model‖ * (C₁ / u) :=
      mul_le_mul_of_nonneg_left hRbound hM0
    have hCu : (C₁ + 2 * C₂ + 1) / u * ‖Model‖
        = ‖Model‖ * (C₁ / u) + C₂ / u * (‖Model‖ * 2) + (1 / u) * ‖Model‖ := by
      field_simp
    rw [hCu]
    have hlast : (0 : ℝ) ≤ (1 / u) * ‖Model‖ := by positivity
    linarith [h1, hTbound, hlast]
  have hfinal := mul_le_mul_of_nonneg_left hinner hE0.le
  calc Real.exp (-((kappa * u + s) / 2))
        * ‖Model * (shellRatio a sigma kappa u s - 1)
          + 2 * (a : ℂ) * ((sigma : ℂ) + (u : ℂ) * I) / shellRoot sigma kappa u s
            * (HTGeometry.besselK1C ((a : ℂ) * shellRoot sigma kappa u s)
              - Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
                * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
                * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * shellRoot sigma kappa u s)))‖
      ≤ Real.exp (-((kappa * u + s) / 2)) * ((C₁ + 2 * C₂ + 1) / u * ‖Model‖) := hfinal
    _ = (C₁ + 2 * C₂ + 1) / u * (Real.exp (-((kappa * u + s) / 2)) * ‖Model‖) := by ring

end

end RHTower
