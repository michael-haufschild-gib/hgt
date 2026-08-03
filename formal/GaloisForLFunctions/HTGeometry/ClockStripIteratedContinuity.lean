import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

/-!
# Continuity of a doubly-integrated family

The clock iterates are defined by integrating over both null coordinates, and the next stage
integrates the previous one again. So each stage must be continuous jointly in the two null
coordinates and the transverse point.

For a globally continuous integrand this is two applications of the parametric-integral continuity
theorem, once per direction. The iterates, however, are continuous only on a strip; composing with
the retraction of the plane onto a slightly smaller closed strip makes the integrand global without
changing any value inside, and the radius of the smaller strip may be chosen separately for each
point.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric MeasureTheory

/-- **The double integral of a globally continuous family is continuous.** -/
theorem continuous_iteratedIntegral {G : ℝ → ℝ → ℂ → ℂ}
    (hG : Continuous fun r : (ℝ × ℝ) × ℂ => G r.1.1 r.1.2 r.2) :
    Continuous fun r : (ℝ × ℝ) × ℂ =>
      ∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t r.2 := by
  have hinner : Continuous fun p : ℝ × ((ℝ × ℝ) × ℂ) =>
      ∫ t in (0 : ℝ)..p.2.1.2, G p.1 t p.2.2 := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ((ℝ × ℝ) × ℂ)) (t : ℝ) => G p.1 t p.2.2) ?_ ?_
    · exact hG.comp (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_fst)))
    · exact continuous_snd.comp (continuous_fst.comp continuous_snd)
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (r : (ℝ × ℝ) × ℂ) (s : ℝ) => ∫ t in (0 : ℝ)..r.1.2, G s t r.2) ?_ ?_
  · exact hinner.comp (continuous_snd.prodMk continuous_fst)
  · exact continuous_fst.comp continuous_fst

/-- **The double integral of a family continuous on a strip is continuous there.** -/
theorem continuousAt_iteratedIntegral_of_strip {ρ : ℝ} {G : ℝ → ℝ → ℂ → ℂ}
    (hG : ContinuousOn (fun r : (ℝ × ℝ) × ℂ => G r.1.1 r.1.2 r.2) (univ ×ˢ imStrip ρ))
    {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ) :
    ContinuousAt (fun r : (ℝ × ℝ) × ℂ =>
      ∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t r.2) q := by
  classical
  have him : |q.2.im| < ρ := mem_imStrip.mp hq
  set ρ₁ : ℝ := (|q.2.im| + ρ) / 2 with hρ₁
  have h1 : |q.2.im| < ρ₁ := by rw [hρ₁]; linarith
  have h2 : ρ₁ < ρ := by rw [hρ₁]; linarith
  have hρ₁0 : 0 ≤ ρ₁ := le_trans (abs_nonneg _) h1.le
  -- the retracted family is globally continuous
  have hmaps : ∀ z : ℂ, stripRetract ρ₁ z ∈ imStrip ρ :=
    fun z => lt_of_le_of_lt (abs_stripRetract_im_le hρ₁0 z) h2
  have hGret : Continuous fun r : (ℝ × ℝ) × ℂ => G r.1.1 r.1.2 (stripRetract ρ₁ r.2) := by
    have hmap : Continuous fun r : (ℝ × ℝ) × ℂ => ((r.1, stripRetract ρ₁ r.2) : (ℝ × ℝ) × ℂ) :=
      continuous_fst.prodMk ((continuous_stripRetract ρ₁).comp continuous_snd)
    exact hG.comp_continuous hmap fun r => ⟨mem_univ _, hmaps r.2⟩
  have hcont := continuous_iteratedIntegral
    (G := fun s t z => G s t (stripRetract ρ₁ z)) hGret
  -- inside the smaller strip the retraction changes nothing
  refine (hcont.continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_imStrip ρ₁).preimage continuous_snd).mem_nhds (mem_imStrip.mpr h1)) ?_
  intro r hr
  have hrz : stripRetract ρ₁ r.2 = r.2 :=
    stripRetract_eq_self (le_of_lt (mem_imStrip.mp hr))
  show (∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t (stripRetract ρ₁ r.2))
    = ∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t r.2
  rw [hrz]

/-! ## The second derivative on a strip, from continuity on the strip

Instrument for the iterates: their second `z`-derivative must be continuous jointly in the null
coordinates and the point, but they are continuous only on a strip. Here the retraction is legal,
because what is being proved is continuity, not holomorphy: the Cauchy contour is anchored at the
retracted point, which makes the representation globally continuous, and inside the strip the
retraction is the identity.
-/

theorem continuousAt_deriv_deriv_of_strip {P : Type*} [TopologicalSpace P] {ρ ρ' : ℝ}
    (hρ : ρ < ρ') (hρ0 : 0 ≤ ρ) {W : P → ℂ → ℂ}
    (hWc : ContinuousOn (fun q : P × ℂ => W q.1 q.2) (univ ×ˢ imStrip ρ'))
    (hWd : ∀ p : P, DifferentiableOn ℂ (W p) (imStrip ρ'))
    {q : P × ℂ} (hq : q.2 ∈ imStrip ρ) :
    ContinuousAt (fun q' : P × ℂ => deriv (deriv (W q'.1)) q'.2) q := by
  classical
  set R : ℝ := (ρ' - ρ) / 2 with hRdef
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; linarith
  -- every point of the retracted strip has its disc inside the big strip
  have hdisc : ∀ z : ℂ, closedBall (stripRetract ρ z) R ⊆ imStrip ρ' := by
    intro z w hw
    have h1 : |w.im - (stripRetract ρ z).im| ≤ R := by
      have h := Complex.abs_im_le_norm (w - stripRetract ρ z)
      rw [Complex.sub_im] at h
      have : ‖w - stripRetract ρ z‖ ≤ R := by
        rw [← dist_eq_norm]
        exact mem_closedBall.mp hw
      linarith
    have h2 : |(stripRetract ρ z).im| ≤ ρ := abs_stripRetract_im_le hρ0 z
    have h3 : |w.im| ≤ |(stripRetract ρ z).im| + |w.im - (stripRetract ρ z).im| := by
      have := abs_sub_abs_le_abs_sub w.im (stripRetract ρ z).im
      linarith
    show |w.im| < ρ'
    rw [hRdef] at h1
    linarith
  -- the retracted Cauchy representation is globally continuous
  have hcont : Continuous fun q' : P × ℂ =>
      (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
        • ∮ ζ in C(stripRetract ρ q'.2, R), (1 / (ζ - stripRetract ρ q'.2) ^ (2 + 1)) • W q'.1 ζ := by
    have hint : Continuous fun r : (P × ℂ) × ℝ =>
        (circleMap 0 R r.2 * Complex.I)
          • ((1 / (circleMap 0 R r.2) ^ (2 + 1))
            • W r.1.1 (stripRetract ρ r.1.2 + circleMap 0 R r.2)) := by
      have hc0 : Continuous fun r : (P × ℂ) × ℝ => circleMap 0 R r.2 :=
        (continuous_circleMap 0 R).comp continuous_snd
      have hden : Continuous fun r : (P × ℂ) × ℝ => 1 / (circleMap 0 R r.2) ^ (2 + 1) := by
        refine continuous_const.div (hc0.pow (2 + 1)) fun r => ?_
        exact pow_ne_zero _ (circleMap_ne_center hRpos.ne')
      have hmem : ∀ r : (P × ℂ) × ℝ,
          ((r.1.1, stripRetract ρ r.1.2 + circleMap 0 R r.2) : P × ℂ) ∈ univ ×ˢ imStrip ρ' := by
        intro r
        refine ⟨mem_univ _, hdisc r.1.2 ?_⟩
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_circleMap_zero,
          abs_of_pos hRpos]
      have hval : Continuous fun r : (P × ℂ) × ℝ =>
          W r.1.1 (stripRetract ρ r.1.2 + circleMap 0 R r.2) :=
        hWc.comp_continuous
          ((continuous_fst.comp continuous_fst).prodMk
            (((continuous_stripRetract ρ).comp (continuous_snd.comp continuous_fst)).add hc0))
          hmem
      exact (hc0.mul continuous_const).smul (hden.smul hval)
    have hcirc : Continuous fun q' : P × ℂ =>
        ∮ ζ in C(stripRetract ρ q'.2, R), (1 / (ζ - stripRetract ρ q'.2) ^ (2 + 1)) • W q'.1 ζ := by
      show Continuous fun q' : P × ℂ =>
        ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap (stripRetract ρ q'.2) R) θ
          • ((1 / (circleMap (stripRetract ρ q'.2) R θ - stripRetract ρ q'.2) ^ (2 + 1))
            • W q'.1 (circleMap (stripRetract ρ q'.2) R θ))
      have hrw : (Function.uncurry fun (q' : P × ℂ) (θ : ℝ) =>
          deriv (circleMap (stripRetract ρ q'.2) R) θ
            • ((1 / (circleMap (stripRetract ρ q'.2) R θ - stripRetract ρ q'.2) ^ (2 + 1))
              • W q'.1 (circleMap (stripRetract ρ q'.2) R θ)))
          = fun r : (P × ℂ) × ℝ => (circleMap 0 R r.2 * Complex.I)
            • ((1 / (circleMap 0 R r.2) ^ (2 + 1))
              • W r.1.1 (stripRetract ρ r.1.2 + circleMap 0 R r.2)) := by
        funext r
        show deriv (circleMap (stripRetract ρ r.1.2) R) r.2
            • ((1 / (circleMap (stripRetract ρ r.1.2) R r.2 - stripRetract ρ r.1.2) ^ (2 + 1))
              • W r.1.1 (circleMap (stripRetract ρ r.1.2) R r.2))
          = (circleMap 0 R r.2 * Complex.I)
            • ((1 / (circleMap 0 R r.2) ^ (2 + 1))
              • W r.1.1 (stripRetract ρ r.1.2 + circleMap 0 R r.2))
        rw [deriv_circleMap, circleMap_sub_center,
          circleMap_eq_add (stripRetract ρ r.1.2) R r.2]
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (by rw [hrw]; exact hint) 0 (2 * Real.pi)
    rw [show (fun q' : P × ℂ => (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
        • ∮ ζ in C(stripRetract ρ q'.2, R), (1 / (ζ - stripRetract ρ q'.2) ^ (2 + 1)) • W q'.1 ζ)
      = ((2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹ •
        fun q' : P × ℂ => ∮ ζ in C(stripRetract ρ q'.2, R),
          (1 / (ζ - stripRetract ρ q'.2) ^ (2 + 1)) • W q'.1 ζ) from rfl]
    exact hcirc.const_smul _
  refine (hcont.continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_imStrip ρ).preimage continuous_snd).mem_nhds hq) ?_
  intro q' hq'
  have hret : stripRetract ρ q'.2 = q'.2 :=
    stripRetract_eq_self (le_of_lt (mem_imStrip.mp hq'))
  have hsub : closedBall q'.2 R ⊆ imStrip ρ' := by
    rw [← hret]
    exact hdisc q'.2
  have hslice : ContinuousOn (W q'.1) (closedBall q'.2 R) :=
    hWc.comp ((continuous_const.prodMk continuous_id).continuousOn)
      fun ζ hζ => ⟨mem_univ _, hsub hζ⟩
  have hd : ∀ ζ ∈ ball q'.2 R, DifferentiableAt ℂ (W q'.1) ζ := fun ζ hζ =>
    (hWd q'.1).differentiableAt ((isOpen_imStrip ρ').mem_nhds (hsub (ball_subset_closedBall hζ)))
  have hform := iteratedDeriv_eq_circleIntegral hRpos 2 hslice hd
  rw [iteratedDeriv_two] at hform
  show (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
      • ∮ ζ in C(stripRetract ρ q'.2, R), (1 / (ζ - stripRetract ρ q'.2) ^ (2 + 1)) • W q'.1 ζ
    = deriv (deriv (W q'.1)) q'.2
  rw [hret, hform]

/-! ## The single integral

The holomorphy statement consumes the two integrations one at a time, so the inner integral is
needed as a function of the outer integration variable and the transverse point.
-/

/-- **The inner integral of a family continuous on a strip is continuous there**, jointly in the
remaining variable and the point. -/
theorem continuousAt_innerIntegral_of_strip {ρ η : ℝ} {H : ℝ → ℝ → ℂ → ℂ}
    (hH : ContinuousOn (fun r : (ℝ × ℝ) × ℂ => H r.1.1 r.1.2 r.2) (univ ×ˢ imStrip ρ))
    {q : ℝ × ℂ} (hq : q.2 ∈ imStrip ρ) :
    ContinuousAt (fun r : ℝ × ℂ => ∫ t in (0 : ℝ)..η, H r.1 t r.2) q := by
  classical
  have him : |q.2.im| < ρ := mem_imStrip.mp hq
  set ρ₁ : ℝ := (|q.2.im| + ρ) / 2 with hρ₁
  have h1 : |q.2.im| < ρ₁ := by rw [hρ₁]; linarith
  have h2 : ρ₁ < ρ := by rw [hρ₁]; linarith
  have hρ₁0 : 0 ≤ ρ₁ := le_trans (abs_nonneg _) h1.le
  have hmaps : ∀ z : ℂ, stripRetract ρ₁ z ∈ imStrip ρ :=
    fun z => lt_of_le_of_lt (abs_stripRetract_im_le hρ₁0 z) h2
  have hglob : Continuous fun p : (ℝ × ℂ) × ℝ => H p.1.1 p.2 (stripRetract ρ₁ p.1.2) := by
    have hmap : Continuous fun p : (ℝ × ℂ) × ℝ =>
        (((p.1.1, p.2), stripRetract ρ₁ p.1.2) : (ℝ × ℝ) × ℂ) :=
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
        ((continuous_stripRetract ρ₁).comp (continuous_snd.comp continuous_fst))
    exact hH.comp_continuous hmap fun p => ⟨mem_univ _, hmaps p.1.2⟩
  have hcont : Continuous fun r : ℝ × ℂ =>
      ∫ t in (0 : ℝ)..η, H r.1 t (stripRetract ρ₁ r.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (r : ℝ × ℂ) (t : ℝ) => H r.1 t (stripRetract ρ₁ r.2)) hglob 0 η
  refine (hcont.continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_imStrip ρ₁).preimage continuous_snd).mem_nhds (mem_imStrip.mpr h1)) ?_
  intro r hr
  have hrz : stripRetract ρ₁ r.2 = r.2 :=
    stripRetract_eq_self (le_of_lt (mem_imStrip.mp hr))
  show (∫ t in (0 : ℝ)..η, H r.1 t (stripRetract ρ₁ r.2))
    = ∫ t in (0 : ℝ)..η, H r.1 t r.2
  rw [hrz]

end GaloisForLFunctions.HTGeometry
