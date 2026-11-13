import GaloisForLFunctions.EulerFETransportTheory.UnequalCoefficientsFloorTheAbelMass
import GaloisForLFunctions.StripBochnerWeilForcing.TheSimplePoleClassIsZeta
import GaloisForLFunctions.RHTower.CrystallineProducerRigidity

/-!
# Polynomially bounded strip continuations lie in the Hamburger class

Let `G` be continuous on the closed strip `1/2 ≤ Re s ≤ 3/2`, holomorphic inside, polynomially
bounded, and equal to `(s - 1) Z(s)` on `Re s = 3/2`.  Put `ζ^ext(s) = G(s)/(s - 1)` and
`β = G(1)/2`.

* **Lemma 1.2(1)** (`hamburgerStripDefect_of_stripContinuation`).  `Z` continues to the critical
  line in the Hamburger strip class with parameter `β` and defect
  `g(t) = ζ^ext(1/2 + 2it) - χ(1/2 + 2it) ζ^ext(1/2 - 2it)`, `χ(s) = Γ_ℝ(1 - s)/Γ_ℝ(s)`
  (`stripDefect`).  The remainder is
  `E(s) = (Γ_ℝ(s) G(s) - G(1))/(s - 1) - β h(s - 1)`, `h(w) = Γ_ℝ(w) - 2/w` regular at `0`
  (`stripRemainder`): it equals `Γ_ℝ(s) ζ^ext(s) - β Γ_ℝ(s - 1)` off `s = 1`, and `Γ_ℝ` decays
  exponentially, so `E = O(1/(1 + t²))`.
* **Lemma 1.2(2)** (`stripDefect_eq_of_factor`).  If `ζ^ext = ζ M` on the critical line with
  `M(1 - s) = conj M(s)` there, then `g(t) = 2i ζ(1/2 + 2it) Im M(1/2 + 2it)`: the functional
  equation of `ζ` removes `χ`.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.StripBochnerWeilForcing

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory

/-- The Hamburger remainder `E(s) = (Γ_ℝ(s) G(s) - G(1))/(s - 1) - (G(1)/2) h(s - 1)` of a strip
continuation `G` of `(s - 1) Z(s)`. -/
def stripRemainder (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  dslope (fun z => Complex.Gammaℝ z * G z) 1 s - G 1 / 2 * gammaℝReg (s - 1)

/-- The critical-line FE defect `g(t) = ζ^ext(s) - χ(s) ζ^ext(1 - s)`, `s = 1/2 + 2it`. -/
def stripDefect (G : ℂ → ℂ) (t : ℝ) : ℂ :=
  G ((1 / 2 : ℂ) + (2 * t : ℝ) * I) / ((1 / 2 : ℂ) + (2 * t : ℝ) * I - 1) -
    Complex.Gammaℝ (1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I)) /
        Complex.Gammaℝ ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
      (G (1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I)) / (1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I) - 1))

/-- `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` is holomorphic on `Re s > 0`. -/
theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    have h := congrArg Complex.re hm
    simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at h
    norm_num at h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h := hpow.mul (hΓ.comp s (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z / 2) s))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp [Complex.Gammaℝ_def]

/-- Off `s = 1` the remainder is `Γ_ℝ(s) G(s)/(s - 1) - (G(1)/2) Γ_ℝ(s - 1)`. -/
theorem stripRemainder_eq (G : ℂ → ℂ) {s : ℂ} (hs : s ≠ 1) :
    stripRemainder G s = Complex.Gammaℝ s * G s / (s - 1) - G 1 / 2 * Complex.Gammaℝ (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [stripRemainder, dslope_of_ne _ hs, slope_def_field, gammaℝReg_eq hs1, Complex.Gammaℝ_one,
    one_mul]
  field_simp
  ring

/-- On the critical line `|Γ_ℝ(1 - s)| = |Γ_ℝ(s)|`, since `1 - s = s̄` there. -/
theorem norm_Gammaℝ_one_sub_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    ‖Complex.Gammaℝ (1 - s)‖ = ‖Complex.Gammaℝ s‖ := by
  have hc : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext <;> norm_num [hs]
  have hpi := Real.pi_pos
  rw [hc, Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos hpi,
    show (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) by rw [map_div₀, map_ofNat], Complex.Gamma_conj,
    Complex.norm_conj]
  congr 2
  simp

/-- **Lemma 1.2(1).**  A polynomially bounded strip continuation `G` of `(s - 1) Z(s)` puts `Z`
in the Hamburger strip class with parameter `G(1)/2` and defect `stripDefect G`. -/
theorem hamburgerStripDefect_of_stripContinuation {Z G : ℂ → ℂ}
    (hGc : ContinuousOn G (HTGeometry.verticalStrip (1 / 2) (3 / 2)))
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hGZ : ∀ s : ℂ, s.re = 3 / 2 → G s = (s - 1) * Z s)
    {C₀ : ℝ} {N₀ : ℕ}
    (hGb : ∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2), ‖G s‖ ≤ C₀ * (1 + |s.im|) ^ N₀) :
    HamburgerStripDefect Z (G 1 / 2) (stripDefect G) := by
  have hpi := Real.pi_pos
  set S := HTGeometry.verticalStrip (1 / 2) (3 / 2) with hS
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUS : U ⊆ S := fun s hs => by
    rw [hS, HTGeometry.mem_verticalStrip]; exact ⟨hs.1.le, hs.2.le⟩
  have hSre : ∀ s ∈ S, 0 < s.re := fun s hs => by
    rw [hS, HTGeometry.mem_verticalStrip] at hs; linarith [hs.1]
  have h1U : (1 : ℂ) ∈ U := by simp only [hU, Set.mem_setOf_eq, Complex.one_re]; norm_num
  have hC₀ : 0 ≤ C₀ := by
    have h := (norm_nonneg _).trans (hGb 1 (hUS h1U))
    have : (0 : ℝ) < (1 + |(1 : ℂ).im|) ^ N₀ := by positivity
    exact nonneg_of_mul_nonneg_left h this
  -- the product `Γ_ℝ G`
  set f : ℂ → ℂ := fun z => Complex.Gammaℝ z * G z with hf
  have hfd : DifferentiableOn ℂ f U := fun z hz =>
    ((differentiableAt_Gammaℝ_of_re_pos (hSre z (hUS hz))).differentiableWithinAt).mul
      (hGd z hz)
  have hfc : ContinuousOn f S := fun z hz =>
    (differentiableAt_Gammaℝ_of_re_pos (hSre z hz)).continuousAt.continuousWithinAt.mul (hGc z hz)
  have hreg : DifferentiableOn ℂ (fun s : ℂ => gammaℝReg (s - 1)) S := by
    intro s hs
    have hm : -2 < (s - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith [hSre s hs]
    exact ((differentiableOn_gammaℝReg.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hm)).comp s
      (differentiableAt_id.sub_const 1)).differentiableWithinAt
  -- continuity and holomorphy of `E`
  have hEd : DifferentiableOn ℂ (stripRemainder G) U :=
    ((Complex.differentiableOn_dslope (hUo.mem_nhds h1U)).mpr hfd).sub
      ((hreg.mono hUS).const_mul _)
  have hEc : ContinuousOn (stripRemainder G) S := by
    refine ContinuousOn.sub (fun s hs => ?_) (hreg.continuousOn.const_mul _)
    by_cases h1 : s = 1
    · subst h1
      exact (continuousAt_dslope_same.mpr (hfd.differentiableAt (hUo.mem_nhds h1U)))
        |>.continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne h1).mpr (hfc s hs)
  -- the decay `E = O(1/(1 + t²))`
  have hdecay : ∃ C : ℝ, ∀ s ∈ S, ‖stripRemainder G s‖ ≤ C / (1 + s.im ^ 2) := by
    obtain ⟨Cg, Ng, hCg, hg⟩ := exists_sharp_bound_norm_Gamma_strip (1 / 4) (3 / 4)
    obtain ⟨K, hK0, hK⟩ := RHTower.exists_bound_pow_mul_exp_neg (Ng + N₀ + 2)
    obtain ⟨Cd, hCd, hΓ1⟩ := RHTower.exists_decay_Gammaℝ_sub_one
    set Kset : Set ℂ := Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-4 : ℝ) 4 with hKset
    have hKc : IsCompact Kset := isCompact_Icc.reProdIm isCompact_Icc
    have hKS : Kset ⊆ S := by
      intro s hs
      rw [hS, HTGeometry.mem_verticalStrip]
      exact (Complex.mem_reProdIm.mp hs).1
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hEc.mono hKS)
    refine ⟨max (17 * max M 0) (Cg * C₀ * K + ‖G 1 / 2‖ * Cd), fun s hs => ?_⟩
    have hs' := hs
    rw [hS, HTGeometry.mem_verticalStrip] at hs'
    have hden : 0 < 1 + s.im ^ 2 := by positivity
    by_cases ht : 4 ≤ |s.im|
    · have h1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
      set τ : ℝ := |s.im| with hτ
      have hτ0 : 0 ≤ τ := abs_nonneg _
      -- `‖Γ_ℝ(s)‖ ≤ Cg τ^Ng e^{-πτ/4}`
      have hgam := hg (s / 2) (by simp; linarith [hs'.1]) (by simp; linarith [hs'.2])
        (by simp [abs_div]; linarith)
      have hsim : |(s / 2).im| = τ / 2 := by simp [hτ, abs_div]
      rw [hsim] at hgam
      have hcp : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
          (by simp; linarith [hs'.1])
      have hΓs : ‖Complex.Gammaℝ s‖ ≤ Cg * (τ + 4) ^ Ng * Real.exp (-(Real.pi * τ / 4)) := by
        rw [Complex.Gammaℝ_def, norm_mul]
        have hexp : Real.exp (-(Real.pi * (τ / 2) / 2)) = Real.exp (-(Real.pi * τ / 4)) := by
          congr 1; ring
        rw [hexp] at hgam
        calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
            ≤ 1 * (Cg * (τ / 2) ^ Ng * Real.exp (-(Real.pi * τ / 4))) :=
              mul_le_mul hcp hgam (norm_nonneg _) zero_le_one
          _ ≤ Cg * (τ + 4) ^ Ng * Real.exp (-(Real.pi * τ / 4)) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity) (by linarith) Ng) hCg) (Real.exp_pos _).le
      have hGs : ‖G s‖ ≤ C₀ * (τ + 4) ^ N₀ :=
        (hGb s hs).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by rw [hτ]; linarith) N₀) hC₀)
      have hs1 : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
        linarith
      have hK' := RHTower.pow_mul_exp_neg_le_div (N := Ng + N₀) hK hτ0
      rw [hτ, sq_abs] at hK'
      rw [stripRemainder_eq G h1]
      calc ‖Complex.Gammaℝ s * G s / (s - 1) - G 1 / 2 * Complex.Gammaℝ (s - 1)‖
          ≤ ‖Complex.Gammaℝ s‖ * ‖G s‖ / ‖s - 1‖ + ‖G 1 / 2‖ * ‖Complex.Gammaℝ (s - 1)‖ := by
            simpa only [norm_mul, norm_div] using norm_sub_le
              (Complex.Gammaℝ s * G s / (s - 1)) (G 1 / 2 * Complex.Gammaℝ (s - 1))
        _ ≤ ‖Complex.Gammaℝ s‖ * ‖G s‖ + ‖G 1 / 2‖ * (Cd / (1 + s.im ^ 2)) := by
            gcongr
            · exact div_le_self (by positivity) hs1
            · exact hΓ1 s hs'.1 hs'.2 ht
        _ ≤ Cg * C₀ * ((τ + 4) ^ (Ng + N₀) * Real.exp (-(Real.pi * τ / 4))) +
            ‖G 1 / 2‖ * (Cd / (1 + s.im ^ 2)) := by
            have hprod : ‖Complex.Gammaℝ s‖ * ‖G s‖ ≤
                Cg * C₀ * ((τ + 4) ^ (Ng + N₀) * Real.exp (-(Real.pi * τ / 4))) := by
              calc ‖Complex.Gammaℝ s‖ * ‖G s‖
                  ≤ (Cg * (τ + 4) ^ Ng * Real.exp (-(Real.pi * τ / 4))) * (C₀ * (τ + 4) ^ N₀) :=
                    mul_le_mul hΓs hGs (norm_nonneg _) (by positivity)
                _ = Cg * C₀ * ((τ + 4) ^ (Ng + N₀) * Real.exp (-(Real.pi * τ / 4))) := by ring
            exact add_le_add hprod le_rfl
        _ ≤ Cg * C₀ * (K / (1 + s.im ^ 2)) + ‖G 1 / 2‖ * (Cd / (1 + s.im ^ 2)) := by
            gcongr
        _ = (Cg * C₀ * K + ‖G 1 / 2‖ * Cd) / (1 + s.im ^ 2) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hden.le
    · have hsmall : |s.im| < 4 := lt_of_not_ge ht
      have hsK : s ∈ Kset := by
        rw [hKset, Complex.mem_reProdIm]
        exact ⟨hs', abs_le.mp hsmall.le⟩
      have hsq : s.im ^ 2 ≤ 16 := by
        nlinarith only [sq_abs s.im, abs_nonneg s.im, hsmall.le]
      calc ‖stripRemainder G s‖ ≤ max M 0 := (hM s hsK).trans (le_max_left _ _)
        _ ≤ 17 * max M 0 / (1 + s.im ^ 2) := by
            apply (le_div_iff₀ hden).mpr
            nlinarith only [mul_le_mul_of_nonneg_left hsq (le_max_right M 0)]
        _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hden.le
  obtain ⟨C, hC⟩ := hdecay
  -- the line `1/2 + 2it` lies in the strip
  have hline : ∀ t : ℝ, (1 / 2 : ℂ) + (2 * t : ℝ) * I ∈ S ∧
      1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I) ∈ S := by
    intro t
    rw [hS, HTGeometry.mem_verticalStrip, HTGeometry.mem_verticalStrip]
    simp
    norm_num
  refine ⟨stripRemainder G, C, hEc, hEd, hC, fun s hs => ?_, fun s hs => ?_, ?_, ?_⟩
  · -- the right boundary
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    rw [stripRemainder_eq G h1, hGZ s hs]
    field_simp [sub_ne_zero.mpr h1]
    ring
  · -- the central reflection
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have h1' : (1 : ℂ) - s ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      norm_num [hs] at h'
    have hpt : (1 / 2 : ℂ) + ((2 * (s.im / 2) : ℝ) : ℂ) * I = s := by
      apply Complex.ext
      · simp [hs]
      · simp; ring
    have hΓ0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
    rw [stripRemainder_eq G h1, stripRemainder_eq G h1', stripDefect, hpt,
      show (1 : ℂ) - s - 1 = -s by ring]
    field_simp
    ring
  · -- the defect is continuous
    have hcont : Continuous (stripDefect G) := by
      have hp1 : Continuous fun t : ℝ => (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I := by fun_prop
      have hp2 : Continuous fun t : ℝ => 1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by fun_prop
      have hG1 : Continuous fun t : ℝ => G ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) :=
        hGc.comp_continuous hp1 fun t => (hline t).1
      have hG2 : Continuous fun t : ℝ => G (1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)) :=
        hGc.comp_continuous hp2 fun t => (hline t).2
      have hre1 : ∀ t : ℝ, 0 < ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I).re := fun t => by
        norm_num
      have hre2 : ∀ t : ℝ, 0 < (1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := fun t => by
        norm_num
      have hΓ1 : Continuous fun t : ℝ => Complex.Gammaℝ ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) :=
        continuous_iff_continuousAt.mpr fun t =>
          ContinuousAt.comp (g := Complex.Gammaℝ)
            (f := fun t : ℝ => (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)
            (differentiableAt_Gammaℝ_of_re_pos (hre1 t)).continuousAt hp1.continuousAt
      have hΓ2 : Continuous fun t : ℝ =>
          Complex.Gammaℝ (1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)) :=
        continuous_iff_continuousAt.mpr fun t =>
          ContinuousAt.comp (g := Complex.Gammaℝ)
            (f := fun t : ℝ => 1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I))
            (differentiableAt_Gammaℝ_of_re_pos (hre2 t)).continuousAt hp2.continuousAt
      have hne1 : ∀ t : ℝ, (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1 ≠ 0 := fun t h => by
        have := congrArg Complex.re h; simp at this; norm_num at this
      have hne2 : ∀ t : ℝ, 1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) - 1 ≠ 0 := fun t h => by
        have := congrArg Complex.re h; simp at this
      unfold stripDefect
      exact (hG1.div (hp1.sub continuous_const) hne1).sub
        ((hΓ2.div hΓ1 fun t => Complex.Gammaℝ_ne_zero_of_re_pos (hre1 t)).mul
          (hG2.div (hp2.sub continuous_const) hne2))
    exact hcont.measurable
  · -- the defect is polynomially bounded
    refine ⟨4 * C₀ * 2 ^ N₀, N₀, fun t => ?_⟩
    set s : ℂ := (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I with hsdef
    have hsre : s.re = 1 / 2 := by simp [hsdef]
    have hsim : s.im = 2 * t := by simp [hsdef]
    have hns1 : 1 / 2 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      simp only [Complex.sub_re, Complex.one_re, hsre] at this
      norm_num at this; linarith
    have hns2 : 1 / 2 ≤ ‖1 - s - 1‖ := by
      rw [show (1 : ℂ) - s - 1 = -s by ring, norm_neg]
      have := Complex.abs_re_le_norm s
      rw [hsre] at this
      norm_num at this; linarith
    have hχ : ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ = 1 := by
      rw [norm_div, norm_Gammaℝ_one_sub_of_re_eq_half hsre,
        div_self (norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)))]
    have hb1 : ‖G s‖ ≤ C₀ * (2 * (1 + |t|)) ^ N₀ := by
      refine (hGb s (hline t).1).trans ?_
      rw [hsim, abs_mul, abs_two]
      gcongr; linarith [abs_nonneg t]
    have hb2 : ‖G (1 - s)‖ ≤ C₀ * (2 * (1 + |t|)) ^ N₀ := by
      refine (hGb (1 - s) (hline t).2).trans ?_
      have : (1 - s).im = -(2 * t) := by simp [hsim]
      rw [this, abs_neg, abs_mul, abs_two]
      gcongr; linarith [abs_nonneg t]
    have e : stripDefect G t = G s / (s - 1) -
        Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * (G (1 - s) / (1 - s - 1)) := rfl
    rw [e]
    calc ‖G s / (s - 1) - Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * (G (1 - s) / (1 - s - 1))‖
        ≤ ‖G s‖ / ‖s - 1‖ + 1 * (‖G (1 - s)‖ / ‖1 - s - 1‖) := by
          have := norm_sub_le (G s / (s - 1))
            (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * (G (1 - s) / (1 - s - 1)))
          rwa [norm_mul, hχ, norm_div, norm_div] at this
      _ ≤ C₀ * (2 * (1 + |t|)) ^ N₀ / (1 / 2) + 1 * (C₀ * (2 * (1 + |t|)) ^ N₀ / (1 / 2)) := by
          gcongr
      _ = 4 * C₀ * 2 ^ N₀ * (1 + |t|) ^ N₀ := by rw [mul_pow]; ring

/-- **Lemma 1.2(2).**  If `G(s)/(s - 1) = ζ(s) M(s)` on the critical line with
`M(1 - s) = conj M(s)` there, then `g(t) = 2i ζ(1/2 + 2it) Im M(1/2 + 2it)`. -/
theorem stripDefect_eq_of_factor {G M : ℂ → ℂ}
    (hfac : ∀ s : ℂ, s.re = 1 / 2 → G s / (s - 1) = riemannZeta s * M s)
    (hM : ∀ s : ℂ, s.re = 1 / 2 → M (1 - s) = (starRingEnd ℂ) (M s)) (t : ℝ) :
    stripDefect G t = 2 * I * riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
      ((M ((1 / 2 : ℂ) + (2 * t : ℝ) * I)).im : ℂ) := by
  set s : ℂ := (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I with hsdef
  have hsre : s.re = 1 / 2 := by simp [hsdef]
  have h1sre : (1 - s).re = 1 / 2 := by simp [hsre]; norm_num
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; norm_num at hsre
  have h1s0 : 1 - s ≠ 0 := fun h => by rw [h] at h1sre; norm_num at h1sre
  have hΓs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hΓ1s : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [h1sre]; norm_num)
  -- the functional equation `Γ_ℝ(1 - s) ζ(1 - s) = Γ_ℝ(s) ζ(s)`
  have hFE : Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero h1s0,
      completedRiemannZeta_one_sub]
    field_simp
  have e : stripDefect G t = G s / (s - 1) -
      Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * (G (1 - s) / (1 - s - 1)) := rfl
  rw [e, hfac s hsre, hfac (1 - s) h1sre, hM s hsre]
  have hzeta : Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * (riemannZeta (1 - s) *
      (starRingEnd ℂ) (M s)) = riemannZeta s * (starRingEnd ℂ) (M s) := by
    field_simp
    linear_combination (starRingEnd ℂ) (M s) * hFE
  rw [hzeta]
  have him : M s - (starRingEnd ℂ) (M s) = 2 * I * ((M s).im : ℂ) := by
    apply Complex.ext <;> simp; ring
  linear_combination riemannZeta s * him

end GaloisForLFunctions.EulerFETransportTheory
