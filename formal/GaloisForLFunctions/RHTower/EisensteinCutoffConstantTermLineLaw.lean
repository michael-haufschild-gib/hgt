import GaloisForLFunctions.RHTower.EisensteinHeckeMaassSelberg
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# The cutoff constant term of the level-one Eisenstein series vanishes only on the line

For `Y > 1` the constant term of the completed Eisenstein series `E*(z, s)` at height `Y`,

`c_Y(s) = Λ(2s) Y^s + Λ(2s − 1) Y^{1−s}`,   `Λ(w) = Γ_ℝ(w) ζ(w)`,

has no zero `s` with `0 < Re s < 1`, `Re s ≠ 1/2`, `Im s ≠ 0`
(`cutoffConstantTerm_ne_zero`). This is the Lax–Phillips / Lagarias–Suzuki line law: the zeros of
`c_Y` are the eigenvalue parameters of a self-adjoint pseudo-Laplacian, so `s(1 − s)` is real.

**Proof.** Write `s = 1/2 + u` with `u ∈ Ω = {−1/2 < Re u, 0 < Im u}`; then also `−ū ∈ Ω`.
- The Maass–Selberg relation on `Ω × Ω` (`maassSelberg_lineModel`) at `v = −ū` gives
  `(u + ū)(u − ū) ∫_𝒟 ‖Λ^Y E_u‖² = R(u, −ū, Y)`.
- If `c_Y(s) = 0` then `R(u, −ū, Y) = 0` identically (`msRight_neg_conj_eq_zero`): with
  `B(u) = −A(u)Y^{2u}` every term of `R` reduces to `±(u + ū)|A|² Y^{2 Re u}`.
- Since `Re u ≠ 0` and `Im u ≠ 0`, the truncated series has zero norm, hence vanishes almost
  everywhere on `𝒟`.
- On the band `1 < Im z ≤ Y` it is untruncated. Its pairing with `conj c(y)` is
  `∫_1^Y |c(y)|² y^{−2} dy` (`setIntegral_band_mul_line`), so `c(y) = 0` on `(1, Y]`.
- Two such heights force `Λ(2s) = Λ(2s − 1) = 0`, impossible: one of `2s`, `1 − (2s − 1)` has real
  part `≥ 1`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The constant term of `E*(·, ½ + u)` at height `y`: `c_u(y) = B(u) y^{½−u} + A(u) y^{½+u}`. -/
abbrev cutoffConstant (u : ℂ) (y : ℝ) : ℂ := d4BMCompletedEisensteinCuspConstantPart .scalar u y

theorem continuousOn_cutoffConstant (u : ℂ) : ContinuousOn (cutoffConstant u) (Ioi 0) := by
  intro y hy
  have hy0 : (0 : ℝ) < y := hy
  have hslit : ((y : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hy0
  have hc : ContinuousAt (fun y : ℝ => msB u * ((y : ℝ) : ℂ) ^ (1 / 2 - u) +
      msA u * ((y : ℝ) : ℂ) ^ (1 / 2 + u)) y := by
    have h1 : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (1 / 2 - u)) y :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))
    have h2 : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (1 / 2 + u)) y :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))
    exact (continuousAt_const.mul h1).add (continuousAt_const.mul h2)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards with w
  exact (cuspConstantPart_eq_msAB u w).symm

/-- **The Maass–Selberg right side vanishes at a zero of the cutoff constant term.** -/
theorem msRight_neg_conj_eq_zero {u : ℂ} (hu : u.im ≠ 0) {Y : ℝ} (hY : 0 < Y)
    (hc : cutoffConstant u Y = 0) : msRight u (-(starRingEnd ℂ) u) Y = 0 := by
  rw [cutoffConstant, cuspConstantPart_eq_msAB] at hc
  have hY0 : ((Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  set A := msA u with hA
  set B := msB u with hB
  set P := ((Y : ℝ) : ℂ) ^ u with hP
  set Q := ((Y : ℝ) : ℂ) ^ ((starRingEnd ℂ) u) with hQ
  set H := ((Y : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hH
  have hPne : P ≠ 0 := by rw [hP]; exact Complex.cpow_ne_zero_iff.mpr (Or.inl hY0)
  have hQne : Q ≠ 0 := by rw [hQ]; exact Complex.cpow_ne_zero_iff.mpr (Or.inl hY0)
  have hHne : H ≠ 0 := by rw [hH]; exact Complex.cpow_ne_zero_iff.mpr (Or.inl hY0)
  have hconjP : (starRingEnd ℂ) P = Q := by rw [hP, hQ, conj_cpow_of_pos hY]
  have e1 : ((Y : ℝ) : ℂ) ^ (1 / 2 - u) = H / P := by
    rw [hH, hP, Complex.cpow_sub _ _ hY0]
  have e2 : ((Y : ℝ) : ℂ) ^ (1 / 2 + u) = H * P := by
    rw [hH, hP, Complex.cpow_add _ _ hY0]
  rw [e1, e2] at hc
  -- `B = −A P²`
  have hBA : B = -(A * P ^ 2) := by
    have h' : (B * (H / P) + A * (H * P)) * (P / H) = 0 := by rw [hc, zero_mul]
    have e : (B * (H / P) + A * (H * P)) * (P / H) = B + A * P ^ 2 := by
      field_simp
    rw [e] at h'
    linear_combination h'
  have hBA' : (starRingEnd ℂ) B = -((starRingEnd ℂ) A * Q ^ 2) := by
    rw [hBA, map_neg, map_mul, map_pow, hconjP]
  have him : u.im ≠ 0 := hu
  unfold msRight
  rw [msA_neg_conj him, msB_neg_conj him, ← hA, ← hB, hBA']
  have f1 : ((Y : ℝ) : ℂ) ^ (u + -(starRingEnd ℂ) u) = P / Q := by
    rw [← sub_eq_add_neg, Complex.cpow_sub _ _ hY0]
  have f2 : ((Y : ℝ) : ℂ) ^ (u - -(starRingEnd ℂ) u) = P * Q := by
    rw [sub_neg_eq_add, Complex.cpow_add _ _ hY0]
  have f3 : ((Y : ℝ) : ℂ) ^ (-(starRingEnd ℂ) u - u) = 1 / (P * Q) := by
    rw [show -(starRingEnd ℂ) u - u = -(u + (starRingEnd ℂ) u) by ring, Complex.cpow_neg,
      Complex.cpow_add _ _ hY0, one_div]
  have f4 : ((Y : ℝ) : ℂ) ^ (-u - -(starRingEnd ℂ) u) = Q / P := by
    rw [show -u - -(starRingEnd ℂ) u = (starRingEnd ℂ) u - u by ring, Complex.cpow_sub _ _ hY0]
  rw [f1, f2, f3, f4, hBA]
  field_simp
  ring

/-- A zero-norm truncated Eisenstein series has vanishing constant term below the cutoff. -/
theorem cutoffConstant_eq_zero_of_norm_zero {u : ℂ} {Y : ℝ} (hY : 1 < Y)
    (hzero : ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 = 0) :
    ∀ y ∈ Ioo 1 Y, cutoffConstant u y = 0 := by
  have hY1 : (1 : ℝ) ≤ Y := hY.le
  -- the truncated series vanishes almost everywhere on `𝒟`
  have hint : IntegrableOn (fun z => ‖truncatedLineModel u Y z‖ ^ 2) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      ((measurable_truncatedLineModel u Y).norm.pow_const 2).aestronglyMeasurable
      (M := truncBound' u Y ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncatedLineModel_le_truncBound' u hY1 hz) 2
  have hae : ∀ᵐ z ∂(volume.restrict fd), truncatedLineModel u Y z = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint).mp hzero
    filter_upwards [h] with z hz
    simpa using hz
  -- pair with `conj c(y)` over the band `1 < Im z ≤ Y`
  set h : ℝ → ℂ := fun y => (starRingEnd ℂ) (cutoffConstant u y) with hhdef
  have hcont : ContinuousOn (cutoffConstant u) (Icc 1 Y) :=
    (continuousOn_cutoffConstant u).mono fun y hy => lt_of_lt_of_le one_pos hy.1
  have hhc : ContinuousOn h (Icc 1 Y) := Complex.continuous_conj.comp_continuousOn hcont
  have hband := setIntegral_band_mul_line u le_rfl h hhc
  have hlhs : (∫ z in fd, (if 1 < z.im ∧ z.im ≤ Y then h z.im * eisensteinLineModel u z else 0))
      = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with z hz
    by_cases hb : 1 < z.im ∧ z.im ≤ Y
    · rw [if_pos hb]
      have : truncatedLineModel u Y z = eisensteinLineModel u z := by
        unfold truncatedLineModel; rw [if_neg (not_lt.mpr hb.2), sub_zero]
      rw [← this, hz, mul_zero]; rfl
    · rw [if_neg hb]; rfl
  rw [hlhs] at hband
  -- the integrand is `‖c(y)‖² / y²`
  set g : ℝ → ℝ := fun y => ‖cutoffConstant u y‖ ^ 2 / y ^ 2 with hgdef
  have hgeq : ∀ y ∈ Ioc 1 Y, h y * cutoffConstant u y / ((y : ℝ) : ℂ) ^ 2 = ((g y : ℝ) : ℂ) := by
    intro y _
    rw [hhdef, hgdef, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioc hgeq, integral_complex_ofReal] at hband
  have hg0 : ∫ y in Ioc 1 Y, g y = 0 := by exact_mod_cast hband.symm
  -- a continuous nonnegative function with zero integral vanishes on the open interval
  have hgc : ContinuousOn g (Icc 1 Y) := by
    refine (hcont.norm.pow 2).div (continuousOn_id.pow 2) fun y hy => ?_
    have : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy.1
    positivity
  have hgnn : ∀ y, 0 ≤ g y := fun y => by rw [hgdef]; positivity
  intro y hy
  by_contra hne
  have hgy : 0 < g y := by
    have : 0 < ‖cutoffConstant u y‖ := norm_pos_iff.mpr hne
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy.1
    rw [hgdef]; positivity
  -- `g > 0` near `y`, so the integral is positive
  have hopen : ∃ δ > 0, ∀ w ∈ Icc (y - δ) (y + δ), 0 < g w ∧ w ∈ Ioo 1 Y := by
    have hcy : ContinuousAt g y :=
      hgc.continuousAt (Icc_mem_nhds hy.1 hy.2)
    have hev : ∀ᶠ w in 𝓝 y, 0 < g w ∧ w ∈ Ioo 1 Y :=
      (hcy.eventually (lt_mem_nhds hgy)).and (Ioo_mem_nhds hy.1 hy.2)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε / 2, by positivity, fun w hw => hball ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]
  obtain ⟨δ, hδ, hpos⟩ := hopen
  have hsub : Icc (y - δ) (y + δ) ⊆ Ioc 1 Y := fun w hw =>
    ⟨(hpos w hw).2.1, (hpos w hw).2.2.le⟩
  have hintg : IntegrableOn g (Ioc 1 Y) :=
    (hgc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hmono : ∫ w in Icc (y - δ) (y + δ), g w ≤ ∫ w in Ioc 1 Y, g w :=
    setIntegral_mono_set hintg (Filter.Eventually.of_forall fun w => hgnn w)
      (Filter.Eventually.of_forall hsub)
  have hposI : 0 < ∫ w in Icc (y - δ) (y + δ), g w := by
    have hcI : ContinuousOn g (Icc (y - δ) (y + δ)) := hgc.mono fun w hw => by
      have := (hpos w hw).2; exact ⟨this.1.le, this.2.le⟩
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcI.intervalIntegrable_of_Icc (by linarith))
      (fun w hw => (hpos w ⟨hw.1.le, hw.2.le⟩).1) (by linarith)
  linarith

/-- The two Weyl coefficients `A(u) = Λ(1+2u)`, `B(u) = Λ(2u)` do not both vanish when
`Im u ≠ 0`: one of `1 + 2u`, `1 − 2u` has real part at least `1`. -/
theorem msA_ne_zero_or_msB_ne_zero {u : ℂ} (hu : u.im ≠ 0) : msA u ≠ 0 ∨ msB u ≠ 0 := by
  have hΛ : ∀ w : ℂ, 1 ≤ w.re → w.im ≠ 0 → reflectedCompletedLambda w ≠ 0 := by
    intro w hw hwi
    rw [reflectedCompletedLambda]
    exact mul_ne_zero (Gammaℝ_ne_zero_of_im_ne_zero hwi) (riemannZeta_ne_zero_of_one_le_re hw)
  rcases le_or_gt 0 u.re with h | h
  · left
    unfold msA
    exact hΛ _ (by simp; linarith) (by simp [hu])
  · right
    unfold msB
    have hwi : (2 * u).im ≠ 0 := by simp [hu]
    rw [← reflectedCompletedLambda_one_sub_of_im hwi]
    exact hΛ _ (by simp; linarith) (by simp [hu])

/-- **The cutoff constant term vanishes only on the line (parameter form).** For `Y > 1`,
`u` with `−1/2 < Re u < 1/2`, `Re u ≠ 0`, `Im u ≠ 0`: `B(u) Y^{½−u} + A(u) Y^{½+u} ≠ 0`. -/
theorem cutoffConstant_ne_zero {u : ℂ} (h1 : -(1 / 2) < u.re) (h2 : u.re < 1 / 2)
    (hre : u.re ≠ 0) (him : u.im ≠ 0) {Y : ℝ} (hY : 1 < Y) : cutoffConstant u Y ≠ 0 := by
  -- reduce to `Im u > 0` by conjugation
  wlog hpos : 0 < u.im generalizing u
  · have hneg : u.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) him
    have h' := this (u := (starRingEnd ℂ) u) (by simpa using h1) (by simpa using h2)
      (by simpa using hre) (by simpa using him) (by simp; linarith)
    intro hc
    apply h'
    rw [cutoffConstant, ← cuspConstantPart_conj u (by linarith : (0 : ℝ) < Y)]
    rw [cutoffConstant] at hc
    rw [hc, map_zero]
  intro hc
  have hu : u ∈ eisensteinLineDomain := ⟨by linarith, hpos⟩
  have hv : -(starRingEnd ℂ) u ∈ eisensteinLineDomain := neg_conj_mem_eisensteinLineDomain hu h2
  have hY1 : (1 : ℝ) ≤ Y := hY.le
  have hms := maassSelberg_lineModel hu hv hY1
  rw [msRight_neg_conj_eq_zero him (by linarith) hc] at hms
  have hfac : (u - -(starRingEnd ℂ) u) * (u + -(starRingEnd ℂ) u) ≠ 0 := by
    have e1 : u - -(starRingEnd ℂ) u = ((2 * u.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; ring
      · simp
    have e2 : u + -(starRingEnd ℂ) u = ((2 * u.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [e1, e2]
    refine mul_ne_zero (by exact_mod_cast mul_ne_zero two_ne_zero hre)
      (mul_ne_zero (by exact_mod_cast mul_ne_zero two_ne_zero him) Complex.I_ne_zero)
  have hpair : truncatedPairing Y u (-(starRingEnd ℂ) u) = 0 :=
    (mul_eq_zero.mp hms).resolve_left hfac
  have hnorm : ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 = 0 := by
    have := integral_norm_sq_eq_truncatedPairing hu Y
    rw [hpair] at this
    exact_mod_cast this
  have hzero := cutoffConstant_eq_zero_of_norm_zero hY hnorm
  -- two heights force `A = B = 0`
  set y₁ : ℝ := (1 + Y) / 2 with hy₁
  set y₂ : ℝ := (1 + 3 * Y) / 4 with hy₂
  have hy₁m : y₁ ∈ Ioo 1 Y := ⟨by linarith, by linarith⟩
  have hy₂m : y₂ ∈ Ioo 1 Y := ⟨by linarith, by linarith⟩
  have hlt : y₁ < y₂ := by linarith
  have c₁ := hzero y₁ hy₁m
  have c₂ := hzero y₂ hy₂m
  rw [cutoffConstant, cuspConstantPart_eq_msAB] at c₁ c₂
  have hy₁0 : (0 : ℝ) < y₁ := by linarith
  have hy₂0 : (0 : ℝ) < y₂ := by linarith
  have hy₁C : ((y₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy₁0.ne'
  have hy₂C : ((y₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy₂0.ne'
  -- `B = −A y^{2u}` at both heights
  have key : ∀ {y : ℝ}, 0 < y → msB u * ((y : ℝ) : ℂ) ^ (1 / 2 - u) +
      msA u * ((y : ℝ) : ℂ) ^ (1 / 2 + u) = 0 → msB u = -(msA u * ((y : ℝ) : ℂ) ^ (2 * u)) := by
    intro y hy hcy
    have hyC : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have ha : ((y : ℝ) : ℂ) ^ (1 / 2 - u) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hyC)
    have hsplit : ((y : ℝ) : ℂ) ^ (1 / 2 + u) =
        ((y : ℝ) : ℂ) ^ (1 / 2 - u) * ((y : ℝ) : ℂ) ^ (2 * u) := by
      rw [← Complex.cpow_add _ _ hyC]; congr 1; ring
    rw [hsplit] at hcy
    have : ((y : ℝ) : ℂ) ^ (1 / 2 - u) * (msB u + msA u * ((y : ℝ) : ℂ) ^ (2 * u)) = 0 := by
      linear_combination hcy
    have := (mul_eq_zero.mp this).resolve_left ha
    linear_combination this
  have hB₁ := key hy₁0 c₁
  have hB₂ := key hy₂0 c₂
  -- the powers `y^{2u}` differ in modulus
  have hpow : ((y₁ : ℝ) : ℂ) ^ (2 * u) ≠ ((y₂ : ℝ) : ℂ) ^ (2 * u) := by
    intro heq
    have := congrArg norm heq
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy₁0, Complex.norm_cpow_eq_rpow_re_of_pos hy₂0] at this
    have hre2 : (2 * u).re ≠ 0 := by simp [hre]
    rcases lt_or_gt_of_ne hre2 with h | h
    · exact absurd this (Real.rpow_lt_rpow_of_neg hy₁0 hlt h).ne'
    · exact absurd this (Real.rpow_lt_rpow hy₁0.le hlt h).ne
  have hA0 : msA u = 0 := by
    have : msA u * (((y₁ : ℝ) : ℂ) ^ (2 * u) - ((y₂ : ℝ) : ℂ) ^ (2 * u)) = 0 := by
      linear_combination hB₁ - hB₂
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hpow)
  have hB0 : msB u = 0 := by rw [hB₁, hA0, zero_mul, neg_zero]
  rcases msA_ne_zero_or_msB_ne_zero him with h | h
  · exact h hA0
  · exact h hB0

/-- **Lax–Phillips / Lagarias–Suzuki line law.** For `Y > 1` and `0 < Re s < 1`, `Re s ≠ 1/2`,
`Im s ≠ 0`: `Λ(2s) Y^s + Λ(2s − 1) Y^{1−s} ≠ 0`, where `Λ = Γ_ℝ · ζ`. -/
theorem lagariasSuzuki_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hre : s.re ≠ 1 / 2)
    (him : s.im ≠ 0) {Y : ℝ} (hY : 1 < Y) :
    reflectedCompletedLambda (2 * s) * ((Y : ℝ) : ℂ) ^ s +
      reflectedCompletedLambda (2 * s - 1) * ((Y : ℝ) : ℂ) ^ (1 - s) ≠ 0 := by
  have h := cutoffConstant_ne_zero (u := s - 1 / 2) (by simp; linarith) (by simp; linarith)
    (by simp; intro h; apply hre; linarith) (by simpa using him) hY
  rw [cutoffConstant, cuspConstantPart_eq_msAB] at h
  unfold msA msB at h
  have e1 : 1 + 2 * (s - 1 / 2) = 2 * s := by ring
  have e2 : 2 * (s - 1 / 2) = 2 * s - 1 := by ring
  have e3 : (1 / 2 : ℂ) - (s - 1 / 2) = 1 - s := by ring
  have e4 : (1 / 2 : ℂ) + (s - 1 / 2) = s := by ring
  rw [e1, e2, e3, e4] at h
  intro hc
  apply h
  linear_combination hc

end

end RHTower
