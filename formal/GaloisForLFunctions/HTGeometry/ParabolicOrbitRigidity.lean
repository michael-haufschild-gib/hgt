import GaloisForLFunctions.HTGeometry.ParabolicCayleyAutomorphism

/-!
# Rigidity of the parabolic orbit: injectivity, no universality, no strong recurrence

Three consequences of the modulus trap and the translation collapse.

The orbit map is injective: equality of two orbit points forces the Cauchy transform to be periodic
high in the half plane, and a periodic transform must vanish there because translation drives it to
zero — impossible for a nonzero positive measure, whose transform has positive imaginary part.

The orbit misses a whole disc of targets, since its modulus never drops to `exp (-N)`; and it
leaves every neighbourhood of its own initial point once the translation is large, because the
initial point is not the limiting constant.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set

open scoped Topology

noncomputable section

/-- The elementary height bound for a Cauchy transform. -/
theorem norm_cauchyTransform_le (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : 0 < z.im) :
    ‖cauchyTransform ν z‖ ≤ ν.real Set.univ / z.im := by
  have hzne : z.im ≠ 0 := ne_of_gt hz
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) ν :=
    HTGeometry.integrable_cauchy_kernel ν hzne
  have hbound : ∫ x : ℝ, ‖((x : ℂ) - z)⁻¹‖ ∂ν ≤ ∫ _x : ℝ, |z.im|⁻¹ ∂ν := by
    refine integral_mono hint.norm (integrable_const _) fun x => ?_
    exact HTGeometry.norm_cauchy_kernel_le x hzne
  calc ‖cauchyTransform ν z‖ ≤ ∫ x : ℝ, ‖((x : ℂ) - z)⁻¹‖ ∂ν :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _x : ℝ, |z.im|⁻¹ ∂ν := hbound
    _ = ν.real Set.univ * |z.im|⁻¹ := by rw [integral_const, smul_eq_mul]
    _ = ν.real Set.univ / z.im := by rw [abs_of_pos hz, div_eq_mul_inv]

/-- Pointwise form of the translation collapse. -/
theorem tendsto_cauchyTransform_translate (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ}
    (hz : 0 < z.im) :
    Tendsto (fun t : ℝ => cauchyTransform ν (z + (t : ℂ))) (cocompact ℝ) (𝓝 0) := by
  have hcompact : IsCompact ({z} : Set ℂ) := isCompact_singleton
  have hpos : ∀ u ∈ ({z} : Set ℂ), 0 < u.im := by
    intro u hu
    rw [mem_singleton_iff] at hu
    rw [hu]
    exact hz
  have huniform := tendstoUniformlyOn_cauchyTransform_translate_isCompact ν hcompact hpos
  exact huniform.tendsto_at (mem_singleton z)

/-- Multiples of a nonzero step escape every compact set. -/
theorem tendsto_nat_mul_cocompact {s : ℝ} (hs : s ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * s) atTop (cocompact ℝ) := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have h : Tendsto (fun n : ℕ => (n : ℝ) * s) atTop atBot :=
      Filter.Tendsto.atTop_mul_const_of_neg hneg tendsto_natCast_atTop_atTop
    refine h.mono_right ?_
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_left
  · have h : Tendsto (fun n : ℕ => (n : ℝ) * s) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hpos tendsto_natCast_atTop_atTop
    refine h.mono_right ?_
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right

/-- **A periodic Cauchy transform vanishes.**  Periodicity in the real direction is incompatible
with the translation collapse. -/
theorem cauchyTransform_eq_zero_of_periodic (ν : Measure ℝ) [IsFiniteMeasure ν] {s : ℝ}
    (hs : s ≠ 0) {Y : ℝ} (hper : ∀ u : ℂ, Y ≤ u.im → cauchyTransform ν (u + (s : ℂ))
      = cauchyTransform ν u) {z : ℂ} (hz : 0 < z.im) (hzY : Y ≤ z.im) :
    cauchyTransform ν z = 0 := by
  have hiter : ∀ n : ℕ, cauchyTransform ν (z + (((n : ℝ) * s : ℝ) : ℂ)) = cauchyTransform ν z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have him : (z + (((n : ℝ) * s : ℝ) : ℂ)).im = z.im := by simp
        have hstep := hper (z + (((n : ℝ) * s : ℝ) : ℂ)) (by rw [him]; exact hzY)
        have hcast : z + ((((n + 1 : ℕ) : ℝ) * s : ℝ) : ℂ)
            = (z + (((n : ℝ) * s : ℝ) : ℂ)) + (s : ℂ) := by
          push_cast
          ring
        rw [hcast, hstep, ih]
  have hlimit : Tendsto (fun n : ℕ => cauchyTransform ν (z + (((n : ℝ) * s : ℝ) : ℂ)))
      atTop (𝓝 0) :=
    (tendsto_cauchyTransform_translate ν hz).comp (tendsto_nat_mul_cocompact hs)
  have hconst : Tendsto (fun _ : ℕ => cauchyTransform ν z) atTop (𝓝 0) := by
    refine hlimit.congr ?_
    intro n
    exact hiter n
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- Two exponents with the same exponential and a difference below the full period agree. -/
theorem eq_of_exp_eq_of_norm_lt {a b : ℂ} (h : Complex.exp a = Complex.exp b)
    (hab : ‖a - b‖ < 2 * Real.pi) : a = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hdiff : a - b = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hn]
    ring
  rw [hdiff] at hab
  have hnorm : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [Complex.norm_intCast, Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hnorm] at hab
  have hpi : 0 < 2 * Real.pi := by positivity
  have hn0 : |(n : ℝ)| < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hnzero : n = 0 := by
    rw [← Int.cast_abs] at hn0
    have hlt : |n| < 1 := by exact_mod_cast hn0
    exact Int.abs_lt_one_iff.mp hlt
  rw [hnzero] at hn
  simpa using hn

/-- **Injectivity of the parabolic orbit map.**  Two translations with the same orbit point are
equal. -/
theorem parabolicOuterOrbit_injective (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {N : ℕ}
    (hN : 0 < N) {t₁ t₂ : ℝ}
    (h : ∀ w : ℂ, ‖w‖ < 1 → parabolicOuterOrbit ν N t₁ w = parabolicOuterOrbit ν N t₂ w) :
    t₁ = t₂ := by
  by_contra hne
  set s : ℝ := t₁ - t₂ with hsdef
  have hs : s ≠ 0 := sub_ne_zero.mpr hne
  set M : ℝ := ν.real Set.univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  set eta : ℝ := min (1 / 2) (Real.pi / (8 * (N : ℝ) + 8)) with heta
  have hetapos : 0 < eta := by
    refine lt_min (by norm_num) ?_
    have : (0 : ℝ) < 8 * (N : ℝ) + 8 := by positivity
    exact div_pos Real.pi_pos this
  set Y : ℝ := (M + 1) / eta with hY
  have hYpos : 0 < Y := by
    refine div_pos ?_ hetapos
    linarith
  -- above the height `Y` the transform is smaller than `eta` at both translates
  have hsmall : ∀ u : ℂ, Y ≤ u.im → ∀ t : ℝ, ‖cauchyTransform ν (u + (t : ℂ))‖ ≤ eta := by
    intro u hu t
    have huim : 0 < (u + (t : ℂ)).im := by
      have : (u + (t : ℂ)).im = u.im := by simp
      rw [this]
      exact lt_of_lt_of_le hYpos hu
    have hb := norm_cauchyTransform_le ν huim
    have hval : (u + (t : ℂ)).im = u.im := by simp
    rw [hval] at hb
    refine le_trans hb ?_
    rw [div_le_iff₀ (lt_of_lt_of_le hYpos hu)]
    have hYu : Y ≤ u.im := hu
    have hEY : eta * Y = M + 1 := by
      rw [hY]
      field_simp
    nlinarith [hetapos, hM0]
  -- the two translates of the transform agree above the height `Y`
  have hagree : ∀ u : ℂ, Y ≤ u.im →
      cauchyTransform ν (u + (t₁ : ℂ)) = cauchyTransform ν (u + (t₂ : ℂ)) := by
    intro u hu
    have huim : 0 < u.im := lt_of_lt_of_le hYpos hu
    set w : ℂ := cayleyToDisc u with hw
    have hwnorm : ‖w‖ < 1 := norm_cayleyToDisc_lt_one huim
    have hwup : cayleyToUpper w = u := cayleyToUpper_cayleyToDisc huim
    have horbit := h w hwnorm
    rw [parabolicOuterOrbit, parabolicOuterOrbit, discExponent_eq_cayleyToDisc,
      discExponent_eq_cayleyToDisc, hwup] at horbit
    -- the two Cayley exponents are within the period of each other
    have hq : ∀ t : ℝ, ‖cayleyToDisc (cauchyTransform ν (u + (t : ℂ))) + 1‖ ≤ 4 * eta := by
      intro t
      have hm := hsmall u hu t
      have hhalf : ‖cauchyTransform ν (u + (t : ℂ))‖ ≤ 1 / 2 :=
        le_trans hm (by rw [heta]; exact min_le_left _ _)
      refine le_trans (norm_cayleyQuotient_add_one_le hhalf) ?_
      exact mul_le_mul_of_nonneg_left hm (by norm_num)
    have hdiff : ‖(N : ℂ) * cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ)))
        - (N : ℂ) * cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ)))‖ < 2 * Real.pi := by
      have hsplit : (N : ℂ) * cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ)))
          - (N : ℂ) * cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ)))
          = (N : ℂ) * ((cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ))) + 1)
            - (cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ))) + 1)) := by ring
      rw [hsplit, norm_mul, Complex.norm_natCast]
      have htri : ‖(cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ))) + 1)
          - (cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ))) + 1)‖ ≤ 4 * eta + 4 * eta :=
        le_trans (norm_sub_le _ _) (add_le_add (hq t₁) (hq t₂))
      have hNle : (N : ℝ) * ‖(cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ))) + 1)
          - (cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ))) + 1)‖
          ≤ (N : ℝ) * (8 * eta) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
        linarith
      refine lt_of_le_of_lt hNle ?_
      have hetale : eta ≤ Real.pi / (8 * (N : ℝ) + 8) := by
        rw [heta]
        exact min_le_right _ _
      have hpos : (0 : ℝ) < 8 * (N : ℝ) + 8 := by positivity
      have hstep : (N : ℝ) * (8 * eta) ≤ (N : ℝ) * (8 * (Real.pi / (8 * (N : ℝ) + 8))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
        linarith
      refine lt_of_le_of_lt hstep ?_
      rw [mul_comm (8 : ℝ) (Real.pi / (8 * (N : ℝ) + 8)), ← mul_assoc, mul_comm (N : ℝ)]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) N]
    have hexp := eq_of_exp_eq_of_norm_lt horbit hdiff
    have hNne : (N : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hcayley : cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ)))
        = cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ))) := by
      exact mul_left_cancel₀ hNne hexp
    have him1 : 0 < (cauchyTransform ν (u + (t₁ : ℂ))).im := by
      refine im_cauchyTransform_pos_of_ne_zero ν hν ?_
      have : (u + (t₁ : ℂ)).im = u.im := by simp
      rw [this]
      exact huim
    have him2 : 0 < (cauchyTransform ν (u + (t₂ : ℂ))).im := by
      refine im_cauchyTransform_pos_of_ne_zero ν hν ?_
      have : (u + (t₂ : ℂ)).im = u.im := by simp
      rw [this]
      exact huim
    calc cauchyTransform ν (u + (t₁ : ℂ))
        = cayleyToUpper (cayleyToDisc (cauchyTransform ν (u + (t₁ : ℂ)))) :=
          (cayleyToUpper_cayleyToDisc him1).symm
      _ = cayleyToUpper (cayleyToDisc (cauchyTransform ν (u + (t₂ : ℂ)))) := by rw [hcayley]
      _ = cauchyTransform ν (u + (t₂ : ℂ)) := cayleyToUpper_cayleyToDisc him2
  -- periodicity with step `s`, hence vanishing, hence a contradiction with positivity
  have hper : ∀ u : ℂ, Y ≤ u.im → cauchyTransform ν (u + (s : ℂ)) = cauchyTransform ν u := by
    intro u hu
    have hshift : Y ≤ (u - (t₂ : ℂ)).im := by
      have : (u - (t₂ : ℂ)).im = u.im := by simp
      rw [this]
      exact hu
    have hval := hagree (u - (t₂ : ℂ)) hshift
    have hleft : (u - (t₂ : ℂ)) + (t₁ : ℂ) = u + (s : ℂ) := by
      rw [hsdef]
      push_cast
      ring
    have hright : (u - (t₂ : ℂ)) + (t₂ : ℂ) = u := by ring
    rw [hleft, hright] at hval
    exact hval
  have hzero : cauchyTransform ν (Complex.I * (Y + 1)) = 0 := by
    have him : (Complex.I * ((Y : ℂ) + 1)).im = Y + 1 := by
      simp [Complex.mul_im]
    refine cauchyTransform_eq_zero_of_periodic ν hs hper ?_ ?_
    · rw [him]; linarith
    · rw [him]; linarith
  have hpos : 0 < (cauchyTransform ν (Complex.I * ((Y : ℂ) + 1))).im := by
    refine im_cauchyTransform_pos_of_ne_zero ν hν ?_
    have him : (Complex.I * ((Y : ℂ) + 1)).im = Y + 1 := by
      simp [Complex.mul_im]
    rw [him]
    linarith
  rw [hzero] at hpos
  simp at hpos

/-- **No universality.**  A constant of small modulus is never approximated by the orbit, at any
point of the disc and at any translation. -/
theorem exists_target_not_approximable (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {N : ℕ}
    (hN : 0 < N) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (t : ℝ) (w : ℂ), ‖w‖ < 1 → ε ≤ ‖parabolicOuterOrbit ν N t w - c‖ := by
  refine ⟨(Real.exp (-(N : ℝ)) / 2 : ℝ), ?_, Real.exp (-(N : ℝ)) / 2, by positivity, ?_⟩
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  · intro t w hw
    have hbounds := norm_parabolicOuterOrbit_bounds ν hν N t hw hN
    have hc : ‖((Real.exp (-(N : ℝ)) / 2 : ℝ) : ℂ)‖ = Real.exp (-(N : ℝ)) / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have htri : ‖parabolicOuterOrbit ν N t w‖ - ‖((Real.exp (-(N : ℝ)) / 2 : ℝ) : ℂ)‖
        ≤ ‖parabolicOuterOrbit ν N t w - ((Real.exp (-(N : ℝ)) / 2 : ℝ) : ℂ)‖ :=
      norm_sub_norm_le _ _
    rw [hc] at htri
    linarith [hbounds.1]

/-- The carrier never takes the limiting value of its own orbit. -/
theorem outerCarrier_ne_exp_neg_one (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {w : ℂ}
    (hw : ‖w‖ < 1) : outerCarrier ν w ≠ Complex.exp (-1) := by
  intro hcon
  have hlt : ‖cayleyToDisc (cauchyTransform ν (cayleyToUpper w))‖ < 1 :=
    norm_cayleyToDisc_lt_one (im_cauchyTransform_pos_of_ne_zero ν hν (im_cayleyToUpper_pos hw))
  have hdiff : ‖cayleyToDisc (cauchyTransform ν (cayleyToUpper w)) - (-1)‖ < 2 * Real.pi := by
    have htri : ‖cayleyToDisc (cauchyTransform ν (cayleyToUpper w)) - (-1)‖
        ≤ ‖cayleyToDisc (cauchyTransform ν (cayleyToUpper w))‖ + ‖(-1 : ℂ)‖ := by
      have := norm_sub_le (cayleyToDisc (cauchyTransform ν (cayleyToUpper w))) (-1)
      simpa using this
    have hone : ‖(-1 : ℂ)‖ = 1 := by simp
    rw [hone] at htri
    have hpi : (2 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    linarith
  have heq := eq_of_exp_eq_of_norm_lt (a := cayleyToDisc (cauchyTransform ν (cayleyToUpper w)))
    (b := -1) hcon hdiff
  rw [heq] at hlt
  simp at hlt

/-- **No strong self-recurrence.**  Beyond a finite horizon the orbit stays a fixed distance from
its own initial point at a chosen point of the disc, so the return set is bounded. -/
theorem exists_bounded_returnSet (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {w : ℂ}
    (hw : ‖w‖ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| →
      ε ≤ ‖parabolicOuterOrbit ν 1 t w - outerCarrier ν w‖ := by
  have hne : outerCarrier ν w ≠ Complex.exp (-1) := outerCarrier_ne_exp_neg_one ν hν hw
  set d : ℝ := ‖outerCarrier ν w - Complex.exp (-1)‖ with hd
  have hdpos : 0 < d := by
    rw [hd, norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hlimit : TendstoUniformlyOn (parabolicOuterOrbit ν 1)
      (fun _ => Complex.exp (-((1 : ℕ) : ℂ))) (cocompact ℝ) {w} :=
    tendstoUniformlyOn_parabolicOuterOrbit ν 1 isCompact_singleton
      (by intro u hu; rw [mem_singleton_iff] at hu; rw [hu]; exact hw)
  have hpt : Tendsto (fun t : ℝ => parabolicOuterOrbit ν 1 t w) (cocompact ℝ)
      (𝓝 (Complex.exp (-((1 : ℕ) : ℂ)))) := hlimit.tendsto_at (mem_singleton w)
  have heventually : ∀ᶠ t : ℝ in cocompact ℝ,
      ‖parabolicOuterOrbit ν 1 t w - Complex.exp (-((1 : ℕ) : ℂ))‖ < d / 3 := by
    have hball := (Metric.tendsto_nhds.mp hpt) (d / 3) (by positivity)
    refine hball.mono fun t ht => ?_
    rw [dist_eq_norm] at ht
    exact ht
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup] at heventually
  obtain ⟨hbot, htop⟩ := heventually
  obtain ⟨a, ha⟩ := eventually_atBot.mp hbot
  obtain ⟨b, hb⟩ := eventually_atTop.mp htop
  refine ⟨d / 3, by positivity, max |a| |b|, fun t ht => ?_⟩
  have hcast : Complex.exp (-((1 : ℕ) : ℂ)) = Complex.exp (-1) := by norm_num
  have hclose : ‖parabolicOuterOrbit ν 1 t w - Complex.exp (-1)‖ < d / 3 := by
    rcases le_or_gt t 0 with hle | hgt
    · have hta : t ≤ a := by
        have h1 : |a| ≤ |t| := le_trans (le_max_left _ _) ht
        have h2 : -t = |t| := (abs_of_nonpos hle).symm
        have h3 : a ≤ |a| := le_abs_self a
        have h4 : -|a| ≤ a := neg_abs_le a
        nlinarith [h1, h3, h4]
      have := ha t hta
      rwa [hcast] at this
    · have htb : b ≤ t := by
        have h1 : |b| ≤ |t| := le_trans (le_max_right _ _) ht
        have h2 : |t| = t := abs_of_pos hgt
        have h3 : b ≤ |b| := le_abs_self b
        nlinarith [h1, h3]
      have := hb t htb
      rwa [hcast] at this
  have htri : d ≤ ‖outerCarrier ν w - parabolicOuterOrbit ν 1 t w‖
      + ‖parabolicOuterOrbit ν 1 t w - Complex.exp (-1)‖ := by
    rw [hd]
    have hsplit : outerCarrier ν w - Complex.exp (-1)
        = (outerCarrier ν w - parabolicOuterOrbit ν 1 t w)
          + (parabolicOuterOrbit ν 1 t w - Complex.exp (-1)) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hrev : ‖outerCarrier ν w - parabolicOuterOrbit ν 1 t w‖
      = ‖parabolicOuterOrbit ν 1 t w - outerCarrier ν w‖ := norm_sub_rev _ _
  rw [hrev] at htri
  linarith

end

end GaloisForLFunctions.HTGeometry
