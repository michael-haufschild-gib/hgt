import GaloisForLFunctions.BlackHoleRingdown.TheVolumeOfTheModularHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownOfAPulse
import GaloisForLFunctions.RHTower.DeckEisensteinSpectralIsometry

/-!
# The Eisenstein channel in `L²`

At a fixed time the image field of a pulse is an incomplete Eisenstein series, with profile `√y h(τ + log y)` and Mellin
transform `2π e^{(s-½)τ} a(-i(s-½))`. Its mean over the modular domain is `6 a(-i/2) e^{τ/2}`, by the volume `π/3`, so
the spectral field `𝓕_h = Π_h - 6a(-i/2)e^{τ/2}` is exactly the part orthogonal to the constants.

The Eisenstein transform of the corpus annihilates the constants: Parseval and Cauchy–Schwarz give
`(1 - κ‖𝟙‖²) c_τ ≲ ‖T_τ‖²`, where `c_τ = |⟨E_τ, 𝟙⟩|² ≍ e^τ` while `‖T_τ‖` stays bounded in `τ`.

On the mean-free part the transform is an isometry up to `π`, and
`T_τ(t) = 2π (e^{itτ} a(t) 𝟙 + e^{-itτ} a(-t) Φ(½-it) 𝟙)`. A single time translation is not a multiplier, but the even
part is: `½(T_τ + T_{-τ})(t) = cos(tτ) T_0(t)`. Hence

`∫_𝒟 |½(𝓕_h(τ) + 𝓕_h(-τ))|² ≤ ∫_𝒟 |𝓕_h(0)|²`,

the cosine family of the wave equation is contractive on the Eisenstein channel of the modular horizon.
-/

open Complex MeasureTheory Set Filter Topology ModularGroup EisensteinSeries
open scoped ContDiff InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower (linePt mem_window_self)
open GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet GaloisForLFunctions.RHTower.MaassCongruenceL2

namespace CompactPulse

variable (h : CompactPulse) (τ : ℝ)

theorem pulseF_eq_zero_of_lt {S₀ : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {y : ℝ}
    (hy : y < Real.exp (-(S₀ + |τ| + 1))) : pulseF h τ y = 0 := by
  by_cases hy0 : 0 < y
  · have hl : Real.log y < -(S₀ + |τ| + 1) := (Real.log_lt_iff_lt_exp hy0).mpr hy
    have hs : S₀ < |τ + Real.log y| := by
      have h1 := neg_abs_le (τ + Real.log y)
      have h2 := le_abs_self τ
      linarith
    rw [pulseF, hS₀ _ hs, mul_zero]
  · rw [pulseF, Real.sqrt_eq_zero_of_nonpos (not_lt.mp hy0)]
    simp

theorem pulseF_eq_zero_of_gt {S₀ : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {y : ℝ}
    (hy : Real.exp (S₀ + |τ| + 1) < y) : pulseF h τ y = 0 := by
  have hy0 : 0 < y := (Real.exp_pos _).trans hy
  have hl : S₀ + |τ| + 1 < Real.log y := (Real.lt_log_iff_exp_lt hy0).mpr hy
  have hs : S₀ < |τ + Real.log y| := by
    have h1 := le_abs_self (τ + Real.log y)
    have h2 := neg_abs_le τ
    linarith
  rw [pulseF, hS₀ _ hs, mul_zero]

/-- The field `√y h(τ + log y)` is smooth in `y`. -/
theorem contDiff_pulseF : ContDiff ℝ ∞ (pulseF h τ) := by
  obtain ⟨S₀, -, hS₀⟩ := h.exists_support_bound
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · have h1 : ContDiffAt ℝ ∞ (fun q : ℝ => ((Real.sqrt q : ℝ) : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    have h2 : ContDiffAt ℝ ∞ (fun q : ℝ => τ + Real.log q) y :=
      contDiffAt_const.add (Real.contDiffAt_log.mpr hy.ne')
    exact h1.mul (h.smooth.contDiffAt.comp y h2)
  · have hev : pulseF h τ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [gt_mem_nhds (lt_of_le_of_lt (not_lt.mp hy)
        (Real.exp_pos (-(S₀ + |τ| + 1))))] with q hq
      exact h.pulseF_eq_zero_of_lt τ hS₀ hq
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The height profile of the image field at time `τ`. -/
def pulseProfile : HeightProfile where
  toFun := pulseF h τ
  lower := Real.exp (-(Classical.choose h.exists_support_bound + |τ| + 1))
  upper := Real.exp (Classical.choose h.exists_support_bound + |τ| + 1)
  lower_pos := Real.exp_pos _
  lower_le_upper := by
    refine Real.exp_le_exp.mpr ?_
    have := (Classical.choose_spec h.exists_support_bound).1
    have := abs_nonneg τ
    linarith
  continuous := (h.contDiff_pulseF τ).continuous
  eq_zero_of_lt := fun _ hy =>
    h.pulseF_eq_zero_of_lt τ (Classical.choose_spec h.exists_support_bound).2 hy
  eq_zero_of_gt := fun _ hy =>
    h.pulseF_eq_zero_of_gt τ (Classical.choose_spec h.exists_support_bound).2 hy

theorem contDiff_pulseProfile : ContDiff ℝ 2 (h.pulseProfile τ).toFun := by
  exact_mod_cast contDiff_infty.mp (h.contDiff_pulseF τ) 2

/-- **The Mellin transform of the profile.** -/
theorem hMellin_pulseF (s : ℂ) :
    hMellin (pulseF h τ) s = 2 * Real.pi * Complex.exp ((s - 1 / 2) * (τ : ℂ)) *
      pulseAmplitude h (-I * (s - 1 / 2)) := by
  rw [hMellin_eq]
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, setIntegral_univ]
  set f : ℝ → ℂ := fun S => Complex.exp ((s - 1 / 2) * (τ : ℂ)) *
    (h S * Complex.exp (-(s - 1 / 2) * (S : ℂ))) with hf
  have hpt : ∀ S : ℝ, |Real.exp S| • (((Real.exp S : ℝ) : ℂ) ^ (-s - 1) * pulseF h τ (Real.exp S)) =
      f (τ + S) := fun S => by
    have hne : ((Real.exp S : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos S).ne'
    have hc : ((Real.exp S : ℝ) : ℂ) ^ (-s - 1) = Complex.exp ((S : ℂ) * (-s - 1)) := by
      rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos S).le, Real.log_exp]
    have hq : ((Real.sqrt (Real.exp S) : ℝ) : ℂ) = Complex.exp ((S : ℂ) / 2) := by
      rw [← Real.exp_half, Complex.ofReal_exp]
      congr 1
      push_cast
      rfl
    have hE : ((Real.exp S : ℝ) : ℂ) = Complex.exp (S : ℂ) := by rw [Complex.ofReal_exp]
    rw [abs_of_pos (Real.exp_pos S), Complex.real_smul, pulseF, Real.log_exp, hc, hq, hE]
    simp only [hf]
    have h1 : Complex.exp (S : ℂ) * (Complex.exp ((S : ℂ) * (-s - 1)) *
        (Complex.exp ((S : ℂ) / 2) * h (τ + S))) =
        (Complex.exp (S : ℂ) * Complex.exp ((S : ℂ) * (-s - 1)) * Complex.exp ((S : ℂ) / 2)) *
          h (τ + S) := by ring
    have hExp : Complex.exp ((S : ℂ) + (S : ℂ) * (-s - 1) + (S : ℂ) / 2) =
        Complex.exp ((s - 1 / 2) * (τ : ℂ)) * Complex.exp (-(s - 1 / 2) * ((τ + S : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h1, ← Complex.exp_add, ← Complex.exp_add, hExp]
    ring
  simp_rw [hpt]
  rw [integral_add_left_eq_self f τ]
  simp only [hf]
  rw [integral_const_mul, h.integral_mul_cexp_eq]
  ring

end CompactPulse

/-! ### The series -/

section Series

variable (h : CompactPulse) (τ : ℝ) (N : ℕ)

theorem eisTerm_pulse (p : gammaSet 1 1 0) (z : UpperHalfPlane) :
    eisTerm (pulseF h τ) (onesVec N) p z =
      imageTerm h (rowC p) (rowD p) τ z.re z.im • onesVec N := by
  rw [eisTerm, imageTerm, rowHgt_eq_im]
  congr 1
  have h1 := (deckRho N (GaloisForLFunctions.HTGeometry.gammaSetMatrix p)).symm_apply_apply (onesVec N)
  rwa [deckRho_onesVec] at h1

/-- **The image field is an incomplete Eisenstein series.** -/
theorem incEis_pulse (z : UpperHalfPlane) :
    incEis (pulseF h τ) (onesVec N) z = (2 * imageField h τ z.re z.im) • onesVec N := by
  obtain ⟨S, hS⟩ := exists_finset_box h τ z.re z.im_pos
  have hS' := hS τ z.re z.im (by simp) (by simp) (mem_window_self z.im_pos)
  rw [imageField, tsum_eq_sum (s := S) hS', incEis, tsum_eq_sum (s := S) fun p hp => by
    rw [eisTerm_pulse, hS' p hp, zero_smul]]
  simp_rw [eisTerm_pulse]
  rw [← Finset.sum_smul]
  congr 1
  ring

/-- The mean-free element of `L²`. -/
def pulseL2 : DeckL2 N :=
  incEisL2 (h.pulseProfile τ) (onesVec N) -
    (2 * meanCoefficient h * Complex.exp ((τ : ℂ) / 2)) • onesL2 N

theorem pulseL2_coeFn :
    (pulseL2 h τ N : UpperHalfPlane → DeckSpace N) =ᵐ[cellMeasure]
      fun z => (2 * pulseField h τ z.re z.im) • onesVec N := by
  filter_upwards [Lp.coeFn_sub (incEisL2 (h.pulseProfile τ) (onesVec N))
      ((2 * meanCoefficient h * Complex.exp ((τ : ℂ) / 2)) • onesL2 N),
    incEisL2_coeFn (h.pulseProfile τ) (onesVec N),
    Lp.coeFn_smul (2 * meanCoefficient h * Complex.exp ((τ : ℂ) / 2)) (onesL2 N),
    onesL2_coeFn (N := N)] with z h1 h2 h3 h4
  rw [pulseL2, h1, Pi.sub_apply, h2, h3, Pi.smul_apply, h4]
  change incEis (pulseF h τ) (onesVec N) z - _ • onesVec N = _
  rw [incEis_pulse, ← sub_smul, pulseField]
  congr 1
  ring

theorem inner_onesL2_self :
    ⟪onesL2 N, onesL2 N⟫_ℂ = ((Real.pi / 3 : ℝ) : ℂ) * ⟪onesVec N, onesVec N⟫_ℂ := by
  rw [L2.inner_def]
  have hae : (fun z => ⟪(onesL2 N : UpperHalfPlane → DeckSpace N) z,
      (onesL2 N : UpperHalfPlane → DeckSpace N) z⟫_ℂ) =ᵐ[cellMeasure]
      fun _ => ⟪onesVec N, onesVec N⟫_ℂ := by
    filter_upwards [onesL2_coeFn (N := N)] with z hz
    rw [hz]
    rfl
  rw [integral_congr_ae hae, integral_const]
  have hv : cellMeasure.real univ = Real.pi / 3 := by
    rw [Measure.real, Measure.restrict_apply_univ, volume_fd_eq,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hv, Complex.real_smul]

/-- **The field is orthogonal to the constants.** -/
theorem inner_pulseL2_ones : ⟪pulseL2 h τ N, onesL2 N⟫_ℂ = 0 := by
  have hT : deckRho N ModularGroup.T (onesVec N) = onesVec N := deckRho_onesVec _
  rw [pulseL2, inner_sub_left, inner_smul_left, inner_incEisL2_onesL2 _ hT, inner_onesL2_self]
  change 2 * (conj (hMellin (pulseF h τ) 1) * _) - _ = 0
  rw [h.hMellin_pulseF]
  have hs : (1 - 1 / 2 : ℂ) = 1 / 2 := by norm_num
  rw [hs, meanCoefficient]
  have he : Complex.exp ((1 / 2 : ℂ) * (τ : ℂ)) = Complex.exp ((τ : ℂ) / 2) := by
    congr 1
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [he]
  simp only [map_mul, Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring

end Series

/-! ### The transform -/

section Transform

variable {N : ℕ} (hN : 2 ≤ N) (h : CompactPulse) (τ : ℝ)

theorem isCuspVec_onesVec : IsCuspVec (onesVec N) := ⟨deckRho_onesVec _, deckRho_onesVec _⟩

/-- The generator of the Eisenstein space given by a pulse. -/
def pulseGen (h : CompactPulse) (τ : ℝ) (N : ℕ) : EisGenIndex N :=
  ⟨h.pulseProfile τ, h.contDiff_pulseProfile τ, onesVec N, isCuspVec_onesVec⟩

theorem line_sub (t : ℝ) : linePt t - 1 / 2 = (t : ℂ) * I := by
  simp [linePt]

theorem rotated_line (t : ℝ) : -I * ((t : ℂ) * I) = t := by
  linear_combination (-(t : ℂ)) * I_sq

/-- The two scattered coefficients of the transform. -/
theorem eisTransform_pulse (t : ℝ) :
    eisTransform (h.pulseProfile τ) (onesVec N) t =
      (2 * Real.pi * Complex.exp ((t : ℂ) * I * (τ : ℂ)) * pulseAmplitude h (t : ℂ)) • onesVec N +
      (2 * Real.pi * Complex.exp (-((t : ℂ) * I * (τ : ℂ))) * pulseAmplitude h ((-t : ℝ) : ℂ)) •
        scatExt (onesVec N) (linePt (-t)) := by
  rw [eisTransform]
  change hMellin (pulseF h τ) _ • _ + hMellin (pulseF h τ) _ • _ = _
  rw [h.hMellin_pulseF, h.hMellin_pulseF, line_sub, line_sub, rotated_line, rotated_line]
  congr 3
  push_cast
  ring_nf

/-- **The even part of the time translation is the cosine multiplier.** -/
theorem eisTransform_even (t : ℝ) :
    (1 / 2 : ℂ) • (eisTransform (h.pulseProfile τ) (onesVec N) t +
        eisTransform (h.pulseProfile (-τ)) (onesVec N) t) =
      (Real.cos (t * τ) : ℂ) • eisTransform (h.pulseProfile 0) (onesVec N) t := by
  rw [eisTransform_pulse, eisTransform_pulse, eisTransform_pulse]
  have hc : (Real.cos (t * τ) : ℂ) =
      (Complex.exp ((t : ℂ) * I * (τ : ℂ)) + Complex.exp (-((t : ℂ) * I * (τ : ℂ)))) / 2 := by
    push_cast
    rw [Complex.cos]
    have e3 : (t : ℂ) * (τ : ℂ) * I = (t : ℂ) * I * (τ : ℂ) := by ring
    have e4 : -((t : ℂ) * (τ : ℂ)) * I = -((t : ℂ) * I * (τ : ℂ)) := by ring
    rw [e3, e4]
  have e1 : ((-τ : ℝ) : ℂ) = -(τ : ℂ) := by push_cast; rfl
  have e2 : (t : ℂ) * I * -(τ : ℂ) = -((t : ℂ) * I * (τ : ℂ)) := by ring
  rw [e1, e2, neg_neg, hc]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  module

/-- The `L²` norm of the transform is bounded in time. -/
theorem exists_norm_genTrans_le :
    ∃ B : ℝ, ∀ τ : ℝ, ‖genTrans hN (pulseGen h τ N)‖ ≤ B := by
  obtain ⟨Ca, hCa, ha⟩ := h.rapidAmplitude.exists_mul_poly_le 0 0
  set G : ℝ → ℝ := fun t => 4 * Real.pi * Ca * ‖onesVec N‖ * ((1 + |t|) ^ 2)⁻¹ with hG
  have hGc : Continuous G := by
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun t => by positivity)
  have hGm : MemLp G 2 volume := by
    have hG2 : Integrable fun t => ‖G t‖ ^ 2 := by
      have hb : Integrable fun t : ℝ => (4 * Real.pi * Ca * ‖onesVec N‖) ^ 2 * ((1 + |t|) ^ 2)⁻¹ :=
        integrable_inv_one_add_abs_sq.const_mul _
      refine hb.mono' (hGc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
      have h0 : 0 ≤ ((1 + |t|) ^ 2)⁻¹ := by positivity
      have h1 : ((1 + |t|) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [abs_nonneg t]))
      simp only [hG, Real.norm_eq_abs, sq_abs]
      rw [abs_of_nonneg (by positivity), mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (((1 + |t|) ^ 2)⁻¹) ^ 2 = ((1 + |t|) ^ 2)⁻¹ * ((1 + |t|) ^ 2)⁻¹ := by ring
        _ ≤ ((1 + |t|) ^ 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h0
        _ = _ := mul_one _
    exact (memLp_two_iff_integrable_sq_norm hGc.aestronglyMeasurable).mpr hG2
  refine ⟨‖hGm.toLp G‖, fun τ => ?_⟩
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [genTrans_coeFn hN (pulseGen h τ N), hGm.coeFn_toLp] with t h1 h2
  rw [h1, h2]
  change ‖eisTransform (h.pulseProfile τ) (onesVec N) t‖ ≤ ‖G t‖
  rw [eisTransform_pulse]
  have hat : ∀ s : ℝ, ‖pulseAmplitude h (s : ℂ)‖ ≤ Ca * ((1 + |s|) ^ 2)⁻¹ := fun s => by
    have := ha (s : ℂ) (by simp)
    simpa using this
  have hscat : ‖scatExt (onesVec N) (linePt (-t))‖ = ‖onesVec N‖ :=
    norm_scatExt_line hN isCuspVec_onesVec (-t)
  have hphase : ∀ s : ℝ, ‖Complex.exp ((s : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  have e1 : ‖Complex.exp ((t : ℂ) * I * (τ : ℂ))‖ = 1 := by
    have : (t : ℂ) * I * (τ : ℂ) = ((t * τ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [this, hphase]
  have e2 : ‖Complex.exp (-((t : ℂ) * I * (τ : ℂ)))‖ = 1 := by
    have : -((t : ℂ) * I * (τ : ℂ)) = ((-(t * τ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [this, hphase]
  have hkey : ∀ (c x : ℂ) (v : DeckSpace N), ‖c‖ = 1 →
      ‖((2 : ℂ) * (Real.pi : ℂ) * c * x) • v‖ = 2 * Real.pi * (‖x‖ * ‖v‖) := fun c x v hc => by
    rw [norm_smul, norm_mul, norm_mul, norm_mul, hc, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    simp only [Complex.norm_ofNat, mul_one]
    ring
  refine (norm_add_le _ _).trans ?_
  rw [hkey _ _ _ e1, hkey _ _ _ e2, hscat, Real.norm_of_nonneg (by positivity)]
  have hneg : |(-t : ℝ)| = |t| := abs_neg t
  have h3 := hat t
  have h4 := hat (-t)
  rw [hneg] at h4
  have hon := norm_nonneg (onesVec N)
  have hπ := Real.pi_pos
  have h5 : ‖pulseAmplitude h (t : ℂ)‖ * ‖onesVec N‖ ≤ Ca * ((1 + |t|) ^ 2)⁻¹ * ‖onesVec N‖ :=
    mul_le_mul_of_nonneg_right h3 hon
  have h6 : ‖pulseAmplitude h ((-t : ℝ) : ℂ)‖ * ‖onesVec N‖ ≤ Ca * ((1 + |t|) ^ 2)⁻¹ * ‖onesVec N‖ :=
    mul_le_mul_of_nonneg_right h4 hon
  have h7 := mul_le_mul_of_nonneg_left (add_le_add h5 h6) (by positivity : 0 ≤ 2 * Real.pi)
  simp only [hG]
  linarith

end Transform

/-! ### Parseval for the constants -/

section Parseval

variable {N : ℕ} (hN : 2 ≤ N)

theorem onesVec_ne_zero (N : ℕ) : onesVec N ≠ 0 := by
  intro h0
  have h1 := congrArg (fun v : DeckSpace N => v (QuotientGroup.mk 1)) h0
  simp [onesVec_apply] at h1

/-- The constants in the Eisenstein space. -/
def onesE (N : ℕ) : eisSpace N := ⟨onesL2 N, onesL2_mem_eisSpace⟩

/-- The pulse in the Eisenstein space. -/
def pulseE (h : CompactPulse) (τ : ℝ) (N : ℕ) : eisSpace N :=
  ⟨genVec (pulseGen h τ N), genSpan_le_eisSpace (genVec_mem_genSpan _)⟩

theorem eisTransformE_pulseE (h : CompactPulse) (τ : ℝ) :
    eisTransformE hN (pulseE h τ N) = genTrans hN (pulseGen h τ N) :=
  eisTransformE_genVec hN _

theorem norm_inner_pulseE_ones (h : CompactPulse) (τ : ℝ) :
    ‖⟪((pulseE h τ N : eisSpace N) : DeckL2 N), onesL2 N⟫_ℂ‖ =
      4 * Real.pi * Real.exp (τ / 2) * ‖pulseAmplitude h (-I * (1 / 2))‖ * ‖⟪onesVec N, onesVec N⟫_ℂ‖ := by
  have hT : deckRho N ModularGroup.T (onesVec N) = onesVec N := deckRho_onesVec _
  change ‖⟪incEisL2 (h.pulseProfile τ) (onesVec N), onesL2 N⟫_ℂ‖ = _
  rw [inner_incEisL2_onesL2 _ hT]
  change ‖2 * (conj (hMellin (pulseF h τ) 1) * _)‖ = _
  rw [h.hMellin_pulseF]
  have hs : (1 - 1 / 2 : ℂ) = 1 / 2 := by norm_num
  rw [hs]
  have he : ‖Complex.exp ((1 / 2 : ℂ) * (τ : ℂ))‖ = Real.exp (τ / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp
    ring
  rw [norm_mul, norm_mul, RCLike.norm_conj, norm_mul, norm_mul, norm_mul, he, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.norm_ofNat]
  ring

/-- **The Eisenstein transform annihilates the constants.** -/
theorem eisTransformE_onesE : eisTransformE hN (onesE N) = 0 := by
  set h := excitingPulse (1 / 2) with hh
  have ha : pulseAmplitude h (-I * (1 / 2)) ≠ 0 := pulseAmplitude_excitingPulse_ne_zero (1 / 2)
  obtain ⟨B, hB⟩ := exists_norm_genTrans_le hN h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hpi := Real.pi_pos
  set X : ℝ := ‖onesL2 N‖ ^ 2 with hX
  have hXC : ⟪onesL2 N, onesL2 N⟫_ℂ = (X : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hX]
    push_cast
    rfl
  have hV : ‖⟪onesVec N, onesVec N⟫_ℂ‖ ≠ 0 := by
    rw [norm_ne_zero_iff, Ne, inner_self_eq_zero]
    exact onesVec_ne_zero N
  have hXpos : 0 < X := by
    have h1 := inner_onesL2_self N
    rw [hXC] at h1
    have hne : (X : ℂ) ≠ 0 := by
      rw [h1]
      refine mul_ne_zero ?_ (norm_ne_zero_iff.mp hV)
      exact_mod_cast (by positivity : Real.pi / 3 ≠ 0)
    have hXn : X ≠ 0 := by exact_mod_cast hne
    exact lt_of_le_of_ne (by rw [hX]; positivity) hXn.symm
  set R : ℝ := (Real.pi)⁻¹ * ‖eisTransformE hN (onesE N)‖ ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hP1 := inner_eisSpace hN (onesE N) (onesE N)
  have hP1' : (X : ℂ) = (R : ℂ) + resConst N * (X : ℂ) * (X : ℂ) := by
    have hin : ⟪eisTransformE hN (onesE N), eisTransformE hN (onesE N)⟫_ℂ =
        ((‖eisTransformE hN (onesE N)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have e : ((onesE N : eisSpace N) : DeckL2 N) = onesL2 N := rfl
    rw [e, hXC, hin] at hP1
    rw [hR]
    push_cast at hP1 ⊢
    exact hP1
  have hmain : ∀ τ : ℝ, R * ((4 * Real.pi * ‖pulseAmplitude h (-I * (1 / 2))‖ *
      ‖⟪onesVec N, onesVec N⟫_ℂ‖) ^ 2 * Real.exp τ) ≤ Real.pi⁻¹ * X ^ 2 * B ^ 2 := fun τ => by
    set e := pulseE h τ N with he
    set c : ℝ := ‖⟪(e : DeckL2 N), onesL2 N⟫_ℂ‖ ^ 2 with hc
    have hval : c = (4 * Real.pi * ‖pulseAmplitude h (-I * (1 / 2))‖ * ‖⟪onesVec N, onesVec N⟫_ℂ‖) ^ 2 *
        Real.exp τ := by
      rw [hc, he, norm_inner_pulseE_ones]
      have hE : Real.exp τ = Real.exp (τ / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hE]
      ring
    have hP2 := inner_eisSpace hN e e
    have hin1 : ⟪(e : DeckL2 N), (e : DeckL2 N)⟫_ℂ = ((‖(e : DeckL2 N)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have hin2 : ⟪eisTransformE hN e, eisTransformE hN e⟫_ℂ = ((‖eisTransformE hN e‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have hin3 : ⟪(e : DeckL2 N), onesL2 N⟫_ℂ * ⟪onesL2 N, (e : DeckL2 N)⟫_ℂ = (c : ℂ) := by
      rw [← inner_conj_symm (onesL2 N), hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hin1, hin2, mul_assoc, hin3] at hP2
    have hkey : ((X ^ 2 * ‖(e : DeckL2 N)‖ ^ 2 : ℝ) : ℂ) =
        ((X ^ 2 * (Real.pi⁻¹ * ‖eisTransformE hN e‖ ^ 2) + (X - R) * c : ℝ) : ℂ) := by
      have hκ : resConst N * (X : ℂ) * (X : ℂ) = (X : ℂ) - (R : ℂ) := by
        linear_combination -hP1'
      push_cast at hP2 ⊢
      linear_combination ((X : ℂ) ^ 2) * hP2 + (c : ℂ) * hκ
    have hreal : X ^ 2 * ‖(e : DeckL2 N)‖ ^ 2 =
        X ^ 2 * (Real.pi⁻¹ * ‖eisTransformE hN e‖ ^ 2) + (X - R) * c := by
      exact_mod_cast hkey
    have hCS : c ≤ ‖(e : DeckL2 N)‖ ^ 2 * X := by
      have h1 := norm_inner_le_norm (𝕜 := ℂ) (e : DeckL2 N) (onesL2 N)
      have h2 : c ≤ (‖(e : DeckL2 N)‖ * ‖onesL2 N‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [mul_pow] at h2
      exact h2
    have hbd : ‖eisTransformE hN e‖ ≤ B := by
      rw [he, eisTransformE_pulseE]
      exact hB τ
    have hbd2 : ‖eisTransformE hN e‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
    rw [← hval]
    have hc0 : 0 ≤ c := by positivity
    have h3 : X * c ≤ X ^ 2 * ‖(e : DeckL2 N)‖ ^ 2 := by nlinarith
    have h4 : X ^ 2 * (Real.pi⁻¹ * ‖eisTransformE hN e‖ ^ 2) ≤ Real.pi⁻¹ * X ^ 2 * B ^ 2 := by
      have hpinv : 0 ≤ Real.pi⁻¹ := by positivity
      have hX2 : 0 ≤ X ^ 2 := by positivity
      calc X ^ 2 * (Real.pi⁻¹ * ‖eisTransformE hN e‖ ^ 2) ≤ X ^ 2 * (Real.pi⁻¹ * B ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbd2 hpinv) hX2
        _ = _ := by ring
    nlinarith
  have hK : 0 < (4 * Real.pi * ‖pulseAmplitude h (-I * (1 / 2))‖ * ‖⟪onesVec N, onesVec N⟫_ℂ‖) ^ 2 := by
    have h1 : 0 < ‖pulseAmplitude h (-I * (1 / 2))‖ := norm_pos_iff.mpr ha
    have h2 : 0 < ‖⟪onesVec N, onesVec N⟫_ℂ‖ := lt_of_le_of_ne (norm_nonneg _) hV.symm
    positivity
  have hRz : R = 0 := by
    by_contra hne
    have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hne)
    set K := (4 * Real.pi * ‖pulseAmplitude h (-I * (1 / 2))‖ * ‖⟪onesVec N, onesVec N⟫_ℂ‖) ^ 2 with hKdef
    set D := Real.pi⁻¹ * X ^ 2 * B ^ 2 with hD
    have hRK : 0 < R * K := mul_pos hRpos hK
    have h1 := hmain (D / (R * K))
    have h2 := Real.add_one_le_exp (D / (R * K))
    have h3 : R * (K * Real.exp (D / (R * K))) ≥ R * K * (D / (R * K) + 1) := by
      have := mul_le_mul_of_nonneg_left h2 hRK.le
      nlinarith
    have h4 : R * K * (D / (R * K) + 1) = D + R * K := by
      field_simp
    linarith
  have hsq : ‖eisTransformE hN (onesE N)‖ ^ 2 = 0 := by
    have : Real.pi⁻¹ * ‖eisTransformE hN (onesE N)‖ ^ 2 = 0 := hRz
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hsq)

/-- **On the mean-free part the transform is an isometry up to `π`.** -/
theorem norm_sq_of_inner_ones_eq_zero (f : eisSpace N) (hf : ⟪(f : DeckL2 N), onesL2 N⟫_ℂ = 0) :
    ‖(f : DeckL2 N)‖ ^ 2 = Real.pi⁻¹ * ‖eisTransformE hN f‖ ^ 2 := by
  have hP := inner_eisSpace hN f f
  rw [hf, mul_zero, zero_mul, add_zero, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hP
  apply Complex.ofReal_injective
  push_cast
  exact hP

/-- The mean-free pulse in the Eisenstein space. -/
def pulseFE (h : CompactPulse) (τ : ℝ) (N : ℕ) : eisSpace N :=
  pulseE h τ N - (2 * meanCoefficient h * Complex.exp ((τ : ℂ) / 2)) • onesE N

theorem coe_pulseFE (h : CompactPulse) (τ : ℝ) : ((pulseFE h τ N : eisSpace N) : DeckL2 N) = pulseL2 h τ N :=
  rfl

theorem eisTransformE_pulseFE (h : CompactPulse) (τ : ℝ) :
    eisTransformE hN (pulseFE h τ N) = genTrans hN (pulseGen h τ N) := by
  rw [pulseFE, map_sub, map_smul, eisTransformE_onesE, smul_zero, sub_zero, eisTransformE_pulseE]

include hN in
/-- **The contraction, at level `N ≥ 2`.** -/
theorem norm_even_pulseL2_le_of_two_le (h : CompactPulse) (τ : ℝ) :
    ‖(1 / 2 : ℂ) • (pulseL2 h τ N + pulseL2 h (-τ) N)‖ ≤ ‖pulseL2 h 0 N‖ := by
  set g : eisSpace N := (1 / 2 : ℂ) • (pulseFE h τ N + pulseFE h (-τ) N) with hg
  have hcoe : (g : DeckL2 N) = (1 / 2 : ℂ) • (pulseL2 h τ N + pulseL2 h (-τ) N) := rfl
  have hin : ⟪(g : DeckL2 N), onesL2 N⟫_ℂ = 0 := by
    rw [hcoe, inner_smul_left, inner_add_left, inner_pulseL2_ones, inner_pulseL2_ones]
    simp
  have hin0 : ⟪((pulseFE h 0 N : eisSpace N) : DeckL2 N), onesL2 N⟫_ℂ = 0 := inner_pulseL2_ones h 0 N
  have h1 := norm_sq_of_inner_ones_eq_zero hN g hin
  have h2 := norm_sq_of_inner_ones_eq_zero hN (pulseFE h 0 N) hin0
  have hTg : eisTransformE hN g = (1 / 2 : ℂ) • (genTrans hN (pulseGen h τ N) + genTrans hN (pulseGen h (-τ) N)) := by
    rw [hg, map_smul, map_add, eisTransformE_pulseFE, eisTransformE_pulseFE]
  have hle : ‖eisTransformE hN g‖ ≤ ‖eisTransformE hN (pulseFE h 0 N)‖ := by
    rw [hTg, eisTransformE_pulseFE]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (genTrans hN (pulseGen h τ N) + genTrans hN (pulseGen h (-τ) N)),
      Lp.coeFn_add (genTrans hN (pulseGen h τ N)) (genTrans hN (pulseGen h (-τ) N)),
      genTrans_coeFn hN (pulseGen h τ N), genTrans_coeFn hN (pulseGen h (-τ) N),
      genTrans_coeFn hN (pulseGen h 0 N)] with t a1 a2 a3 a4 a5
    rw [a1, Pi.smul_apply, a2, Pi.add_apply, a3, a4, a5]
    change ‖(1 / 2 : ℂ) • (eisTransform (h.pulseProfile τ) (onesVec N) t +
      eisTransform (h.pulseProfile (-τ)) (onesVec N) t)‖ ≤ ‖eisTransform (h.pulseProfile 0) (onesVec N) t‖
    rw [eisTransform_even, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  have hsq : ‖(g : DeckL2 N)‖ ^ 2 ≤ ‖((pulseFE h 0 N : eisSpace N) : DeckL2 N)‖ ^ 2 := by
    rw [h1, h2]
    have hpinv : 0 ≤ Real.pi⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2) hpinv
  rw [← hcoe, ← coe_pulseFE]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end Parseval

/-! ### The horizon itself -/

section Horizon

variable {N : ℕ}

theorem norm_sq_deckL2 (f : DeckL2 N) :
    ‖f‖ ^ 2 = ∫ z, ‖(f : UpperHalfPlane → DeckSpace N) z‖ ^ 2 ∂cellMeasure := by
  have h1 := L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h1
  simp_rw [inner_self_eq_norm_sq_to_K] at h1
  have h2 : (∫ z, (((‖(f : UpperHalfPlane → DeckSpace N) z‖ ^ 2 : ℝ)) : ℂ) ∂cellMeasure) =
      ((∫ z, ‖(f : UpperHalfPlane → DeckSpace N) z‖ ^ 2 ∂cellMeasure : ℝ) : ℂ) := integral_ofReal
  have h3 : ((‖f‖ ^ 2 : ℝ) : ℂ) = ((∫ z, ‖(f : UpperHalfPlane → DeckSpace N) z‖ ^ 2 ∂cellMeasure : ℝ) : ℂ) := by
    rw [← h2]
    push_cast
    exact h1
  exact_mod_cast h3

/-- The norm of a scalar multiple of the constant vector, with a factor two. -/
theorem norm_sq_of_ae {x : DeckL2 N} {F : UpperHalfPlane → ℂ}
    (hx : (x : UpperHalfPlane → DeckSpace N) =ᵐ[cellMeasure] fun z => (2 * F z) • onesVec N) :
    ‖x‖ ^ 2 = 4 * ‖onesVec N‖ ^ 2 * ∫ z, ‖F z‖ ^ 2 ∂cellMeasure := by
  rw [norm_sq_deckL2, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hx] with z hz
  rw [hz, norm_smul, norm_mul]
  simp only [Complex.norm_ofNat]
  ring

theorem even_pulseL2_coeFn (h : CompactPulse) (τ : ℝ) :
    (((1 / 2 : ℂ) • (pulseL2 h τ N + pulseL2 h (-τ) N) : DeckL2 N) : UpperHalfPlane → DeckSpace N)
      =ᵐ[cellMeasure] fun z =>
        (2 * ((1 / 2 : ℂ) * (pulseField h τ z.re z.im + pulseField h (-τ) z.re z.im))) • onesVec N := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (pulseL2 h τ N + pulseL2 h (-τ) N),
    Lp.coeFn_add (pulseL2 h τ N) (pulseL2 h (-τ) N), pulseL2_coeFn h τ N, pulseL2_coeFn h (-τ) N]
    with z a1 a2 a3 a4
  rw [a1, Pi.smul_apply, a2, Pi.add_apply, a3, a4]
  module

/-- **The cosine family is contractive on the Eisenstein channel of the modular horizon.** -/
theorem integral_even_pulseField_le (h : CompactPulse) (τ : ℝ) :
    ∫ z, ‖(1 / 2 : ℂ) * (pulseField h τ z.re z.im + pulseField h (-τ) z.re z.im)‖ ^ 2 ∂cellMeasure ≤
      ∫ z, ‖pulseField h 0 z.re z.im‖ ^ 2 ∂cellMeasure := by
  have h1 := norm_even_pulseL2_le_of_two_le (N := 2) le_rfl h τ
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_sq_of_ae (even_pulseL2_coeFn h τ), norm_sq_of_ae (pulseL2_coeFn h 0 2)] at h2
  have hpos : 0 < 4 * ‖onesVec 2‖ ^ 2 := by
    have : 0 < ‖onesVec 2‖ := norm_pos_iff.mpr (onesVec_ne_zero 2)
    positivity
  exact le_of_mul_le_mul_left h2 hpos

/-- The contraction at every level, in particular on the modular horizon. -/
theorem norm_even_pulseL2_le (h : CompactPulse) (τ : ℝ) :
    ‖(1 / 2 : ℂ) • (pulseL2 h τ N + pulseL2 h (-τ) N)‖ ≤ ‖pulseL2 h 0 N‖ := by
  have h2 : ‖(1 / 2 : ℂ) • (pulseL2 h τ N + pulseL2 h (-τ) N)‖ ^ 2 ≤ ‖pulseL2 h 0 N‖ ^ 2 := by
    rw [norm_sq_of_ae (even_pulseL2_coeFn h τ), norm_sq_of_ae (pulseL2_coeFn h 0 N)]
    exact mul_le_mul_of_nonneg_left (integral_even_pulseField_le h τ) (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end Horizon

end GaloisForLFunctions.BlackHoleRingdown

end
