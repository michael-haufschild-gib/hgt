import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergBoundOfTheCuspModes
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleReadsTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheSpectrumOfTheImageField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct
import GaloisForLFunctions.CompletedArithmeticForms.BesselSpectralBand

/-!
# The Rankin–Selberg integral of the cusp modes

The energy density `|g|²` of a cusp mode, paired with the Eisenstein channel, is the Rankin–Selberg
L-function of the mode (`rankinSelberg_eisenstein`): for `Re s > 1`, `Im s ≠ 0`,

  `∫_𝒟 |g(z)|² E(s - ½; z) dμ(z) = π^{-s}/8 · Γ(s/2)² Γ(s/2 + ν) Γ(s/2 - ν)/Γ(s) · Σ_{n≠0} |ρ(n)|² |n|^{-s}`.

**Unfolding.** `E(s - ½) = ½ Σ_{(c,d)} Im(M_{c,d} z)^s`, and `|g|²` is invariant, so the pairing unfolds to the
strip, `∫_𝒟 |g|² Σ_v Im(M_v z)^s = 2 ∫_{0 ≤ x < 1} |g|² y^s dμ` (`two_mul_strip_eq`), which is the Mellin
transform `∫_0^∞ m(y) y^{s-2} dy` of the horocycle mass (`strip_eq_mellin`). Integrability: the chart integrand
has fibre integrals `y^{σ-2} m(y)`, bounded by `y^{σ-2}` near `0` and by `y^{σ-1} e^{-4πy}` in the cusp.

**Modes.** `m(y) = Σ_n |ρ(n)|² y K_ν(2π|n|y)²` (Parseval; `K_ν` is real for imaginary `ν`). Dominated
convergence exchanges the sum and the integral, and
`∫_0^∞ y^{s-1} K_ν(cy)² dy = c^{-s} 2^{s-3} Γ((s+2ν)/2) Γ(s/2)² Γ((s-2ν)/2)/Γ(s)` (corpus two-K Mellin product)
(`hasSum_mellin_slice`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair EisensteinSeries
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)
open GaloisForLFunctions.RHTower.SelbergMaassMean (point)

namespace CuspRSI

open HeckeCusp CuspL

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-- The Gamma factor `2^{s-3} Γ((s+2ν)/2) Γ(s/2)² Γ((s-2ν)/2)/Γ(s)` of the Mellin transform of `K_ν²`. -/
def gammaFactor (ν s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 3) / Gamma s *
    (Gamma ((s + ν + ν) / 2) * Gamma ((s + ν - ν) / 2) * Gamma ((s - ν + ν) / 2) * Gamma ((s - ν - ν) / 2))

/-! ### The horocycle mass -/

theorem continuousOn_slice_pos (hg : g ∈ cuspSpace lamE) : ContinuousOn (WeylUpper.slice g) (Ioi 0) :=
  fun _ hy => ((WeylUpper.continuousOn_slice hg (half_pos hy)).continuousAt
    (Ioi_mem_nhds (half_lt_self hy))).continuousWithinAt

/-- The horocycle mass over `[0, 1)`. -/
theorem integral_Ico_eq_slice (hg : g ∈ cuspSpace lamE) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, ‖g (ofComplex ⟨x, y⟩)‖ ^ 2 = WeylUpper.slice g y := by
  have hper : Function.Periodic (fun x => ‖g (ofComplex (point x y))‖ ^ 2) 1 := fun x => by
    have := periodic_comp hg (point x y) (point_im_pos hy)
    simp only [Function.comp] at this
    simp only [WeylUpper.point_add_one, this]
  have hshift := hper.intervalIntegral_add_eq (-(1 / 2)) 0
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at hshift
  rw [WeylUpper.slice, hshift, intervalIntegral.integral_of_le zero_le_one, ← integral_Ico_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  simp only [chart_point]

/-- `y^{σ-2} m(y)` is integrable on `(0, ∞)` for `σ > 1`. -/
theorem integrableOn_slice_weight (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun y => WeylUpper.slice g y * y ^ (σ - 2)) (Ioi 0) := by
  obtain ⟨Cg, hCg⟩ := exists_bound hg
  obtain ⟨D, hD0, hD⟩ := CuspRS.slice_le_decay hg hρ0 hρ
  have hcont : ContinuousOn (fun y => WeylUpper.slice g y * y ^ (σ - 2)) (Ioi 0) :=
    (continuousOn_slice_pos hg).mul
      (fun y hy => (Real.continuousAt_rpow_const y _ (Or.inl (ne_of_gt hy))).continuousWithinAt)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun y : ℝ => Cg ^ 2 * y ^ (σ - 2)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    refine hi.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (WeylUpper.slice_nonneg y)
      (Real.rpow_nonneg hy.1.le _))]
    exact mul_le_mul_of_nonneg_right (WeylUpper.slice_le hCg y) (Real.rpow_nonneg hy.1.le _)
  · have hi : IntegrableOn (fun y : ℝ => D * (y ^ (σ - 1) * Real.exp (-(4 * Real.pi) * y ^ (1 : ℝ))))
        (Ioi 1) :=
      ((integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl
        (by positivity)).mono_set (Ioi_subset_Ioi zero_le_one)).const_mul D
    refine hi.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : 1 ≤ y := le_of_lt hy
    have hy0 : 0 < y := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (WeylUpper.slice_nonneg y)
      (Real.rpow_nonneg hy0.le _)), Real.rpow_one]
    calc WeylUpper.slice g y * y ^ (σ - 2) ≤ D * (y * Real.exp (-(4 * Real.pi) * y)) * y ^ (σ - 2) :=
          mul_le_mul_of_nonneg_right (hD y hy1) (Real.rpow_nonneg hy0.le _)
      _ = D * (y ^ (σ - 1) * Real.exp (-(4 * Real.pi) * y)) := by
          rw [show σ - 1 = 1 + (σ - 2) by ring, Real.rpow_add hy0, Real.rpow_one]; ring

/-! ### The strip integral -/

/-- The strip integrand `|g(w)|² (Im w)^s`. -/
def rsStrip (g : UpperHalfPlane → ℂ) (s : ℂ) (w : ℍ) : ℂ := ((‖g w‖ ^ 2 : ℝ) : ℂ) * ((w.im : ℝ) : ℂ) ^ s

theorem stripChart_rsStrip {s : ℂ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    stripChartIntegrand (rsStrip g s) p =
      (p.1 : ℂ) ^ (s - 2) * ((‖g (ofComplex ⟨p.2, p.1⟩)‖ ^ 2 : ℝ) : ℂ) := by
  have h0 : (p.1 : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne'
  rw [stripChartIntegrand, rsStrip, im_ofComplex_mk hp, Complex.real_smul, cpow_sub _ _ h0, cpow_two]
  push_cast
  field_simp

theorem continuous_chart_g (hg : g ∈ cuspSpace lamE) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => g (ofComplex (⟨q.2, q.1⟩ : ℂ))) p := by
  have hmk : ContinuousAt (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) p := by
    have : (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) = fun q : ℝ × ℝ => (q.2 : ℂ) + (q.1 : ℂ) * Complex.I := by
      funext q; apply Complex.ext <;> simp
    rw [this]
    fun_prop
  have hoc : ContinuousAt (fun q : ℝ × ℝ => ofComplex (⟨q.2, q.1⟩ : ℂ)) p :=
    (UpperHalfPlane.ofComplex.continuousAt (by simp [UpperHalfPlane.ofComplex, hp])).comp hmk
  exact (continuous_of_maass hg.2.1).continuousAt.comp hoc

/-- **Integrability on the strip** for `Re s > 1`. -/
theorem integrableOn_rsStrip (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (rsStrip g s) modularStrip volume := by
  rw [integrableOn_modularStrip_iff, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 2) * ((‖g (ofComplex ⟨p.2, p.1⟩)‖ ^ 2 : ℝ) : ℂ))
      (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := by
    intro p hp
    have hp0 : (0 : ℝ) < p.1 := hp.1
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.comp (g := fun w : ℂ => w ^ (s - 2)) (f := fun q : ℝ × ℝ => (q.1 : ℂ))
        (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hp0))
        (Complex.continuous_ofReal.comp continuous_fst).continuousAt
    · exact Complex.continuous_ofReal.continuousAt.comp ((continuous_chart_g hg hp0).norm.pow 2)
  have hmeas : AEStronglyMeasurable (stripChartIntegrand (rsStrip g s))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine (hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ico)).congr ?_
    exact (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ico)).2
      (Eventually.of_forall fun p hp => (stripChart_rsStrip hp.1).symm)
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hc : ContinuousOn (fun x : ℝ => stripChartIntegrand (rsStrip g s) (y, x)) (Icc 0 1) := by
      intro x _
      refine ContinuousAt.continuousWithinAt ?_
      have h2 : ContinuousAt (fun x : ℝ => (y : ℂ) ^ (s - 2) * ((‖g (ofComplex ⟨x, y⟩)‖ ^ 2 : ℝ) : ℂ)) x :=
        continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
          (((continuous_chart_g hg (p := (y, x)) hy0).comp (continuousAt_const.prodMk continuousAt_id)).norm.pow 2))
      refine h2.congr (Eventually.of_forall fun x' => (stripChart_rsStrip (p := (y, x')) hy0).symm)
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  · refine (integrableOn_slice_weight hg hρ0 hρ hs).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have e : ∀ x : ℝ, ‖stripChartIntegrand (rsStrip g s) (y, x)‖ = y ^ (s.re - 2) * ‖g (ofComplex ⟨x, y⟩)‖ ^ 2 := by
      intro x
      rw [stripChart_rsStrip (p := (y, x)) hy0, norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp
    simp_rw [e]
    rw [integral_const_mul, integral_Ico_eq_slice hg hy0]
    ring

/-- **Unfolding**: `2 ∫_{strip} |g|² Im^s = ∫_𝒟 |g|² Σ_v Im(M_v z)^s`. -/
theorem two_mul_strip_eq (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    2 * ∫ z in modularStrip, rsStrip g s z = ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * rowSum s z := by
  have hint := integrableOn_rsStrip hg hρ0 hρ hs
  have hφ : ∀ (n : ℤ) (z : ℍ), rsStrip g s (ModularGroup.T ^ n • z) = rsStrip g s z := fun n z => by
    simp only [rsStrip]
    rw [hg.1, ModularGroup.im_T_zpow_smul]
  rw [← tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hφ hint]
  have hterm : ∀ (v : gammaSet 1 1 0) (z : ℍ), rsStrip g s (gammaSetMatrix v • z) =
      ((‖g z‖ ^ 2 : ℝ) : ℂ) * (rowHeight v z : ℂ) ^ s := fun v z => by
    rw [rsStrip, hg.1]
    rfl
  simp_rw [hterm]
  have hφn : ∀ (n : ℤ) (z : ℍ), ((‖rsStrip g s (ModularGroup.T ^ n • z)‖ : ℝ) : ℂ) =
      ((‖rsStrip g s z‖ : ℝ) : ℂ) := fun n z => by rw [hφ]
  have hsum := summable_fdUnfoldTerm hφn hint.norm.ofReal
  unfold fdUnfoldTerm at hsum
  simp_rw [integral_ofReal, hterm] at hsum
  rw [integral_tsum_of_summable_integral_norm (fun v => ?_) (Complex.summable_ofReal.1 hsum)]
  · refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
    rw [rowSum, tsum_mul_left]
  · have h1 := (integrableOn_smul_set_iff (gammaSetMatrix v) _ ModularGroup.fd).1
      (integrableOn_smul_fd_of_periodic hφ hint (gammaSetMatrix v))
    exact h1.congr_fun (fun z _ => hterm v z) ModularGroup.isClosed_fd.measurableSet

/-- **The strip integral is the Mellin transform of the horocycle mass.** -/
theorem strip_eq_mellin (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in modularStrip, rsStrip g s z =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 2) * (WeylUpper.slice g y : ℂ) := by
  rw [setIntegral_modularStrip_eq_iterated _ (integrableOn_rsStrip hg hρ0 hρ hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have h0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy0.ne'
  have e : ∀ x : ℝ, rsStrip g s (ofComplex ⟨x, y⟩) = ((‖g (ofComplex ⟨x, y⟩)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ s := by
    intro x; rw [rsStrip, im_ofComplex_mk hy0]
  simp_rw [e]
  rw [integral_mul_const, integral_complex_ofReal, integral_Ico_eq_slice hg hy0, Complex.real_smul,
    cpow_sub _ _ h0, cpow_two]
  push_cast
  field_simp

/-! ### The modes -/

theorem K_real (lamE : ℝ) (x : ℝ) :
    (((modifiedBesselKOrder x (nu lamE)).re : ℝ) : ℂ) = modifiedBesselKOrder x (nu lamE) := by
  apply Complex.ext
  · simp
  · simp only [ofReal_im]
    exact (GaloisForLFunctions.CompletedArithmeticForms.modifiedBesselKOrder_imaginaryOrder_im x
      (Real.sqrt (lamE - 1 / 4))).symm

/-- `∫_0^∞ y^{s-1} K_ν(cy)² dy = c^{-s} ∫_0^∞ x^{s-1} K_ν(x)² dx`. -/
theorem integral_scaled_KK {s : ℂ} {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) (nu lamE) * modifiedBesselKOrder (c * y) (nu lamE)) =
      (c : ℂ) ^ (-s) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        modifiedBesselKOrder x (nu lamE) * modifiedBesselKOrder x (nu lamE) := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => (x : ℂ) ^ (s - 1) *
    modifiedBesselKOrder x (nu lamE) * modifiedBesselKOrder x (nu lamE)) 0 hc
  rw [mul_zero, Complex.real_smul] at h
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hcs : (c : ℂ) ^ (s - 1) ≠ 0 := by rw [cpow_def_of_ne_zero hcC]; exact exp_ne_zero _
  have e : ∀ y ∈ Ioi (0 : ℝ), ((c * y : ℝ) : ℂ) ^ (s - 1) * modifiedBesselKOrder (c * y) (nu lamE) *
      modifiedBesselKOrder (c * y) (nu lamE) = (c : ℂ) ^ (s - 1) * ((y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) (nu lamE) * modifiedBesselKOrder (c * y) (nu lamE))) := by
    intro y hy
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hc.le (le_of_lt hy)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul] at h
  have hsplit : (c : ℂ) ^ s = (c : ℂ) ^ (s - 1) * c := by
    rw [show s = (s - 1) + 1 by ring, cpow_add _ _ hcC, cpow_one]; ring_nf
  rw [cpow_neg, hsplit]
  calc ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) (nu lamE) * modifiedBesselKOrder (c * y) (nu lamE))
      = ((c : ℂ) ^ (s - 1))⁻¹ * ((c : ℂ) ^ (s - 1) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) (nu lamE) * modifiedBesselKOrder (c * y) (nu lamE))) := by
        rw [inv_mul_cancel_left₀ hcs]
    _ = ((c : ℂ) ^ (s - 1))⁻¹ * ((c : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        modifiedBesselKOrder x (nu lamE) * modifiedBesselKOrder x (nu lamE)) := by rw [h, ofReal_inv]
    _ = _ := by rw [mul_inv]; ring

/-- **The Mellin transform of the horocycle mass is the Rankin–Selberg series.** For `Re s > 1`,
`∫_0^∞ m(y) y^{s-2} dy = Σ_n |ρ(n)|² (2π|n|)^{-s} G(s)`. -/
theorem hasSum_mellin_slice (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ => ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((2 * Real.pi * |(n : ℝ)| : ℝ) : ℂ) ^ (-s) *
      gammaFactor (nu lamE) s) (∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 2) * (WeylUpper.slice g y : ℂ)) := by
  set F : ℤ → ℝ → ℂ := fun n y => (y : ℂ) ^ (s - 2) * ((‖fourierCoeff g n y‖ ^ 2 : ℝ) : ℂ)
  have hmain : HasSum (fun n => ∫ y in Ioi (0 : ℝ), F n y)
      (∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 2) * (WeylUpper.slice g y : ℂ)) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n y => y ^ (s.re - 2) * ‖fourierCoeff g n y‖ ^ 2) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · have hc : ContinuousOn (F n) (Ioi 0) := by
        refine ContinuousOn.mul (fun y hy => ?_) ?_
        · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy)).comp
            Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
        · exact Complex.continuous_ofReal.comp_continuousOn
            (((modalSol_fourierCoeff hg n).continuousOn.1).norm.pow 2)
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact ((WeylUpper.hasSum_slice hg hy).mul_left _).summable
    · refine (integrableOn_slice_weight hg hρ0 hρ hs).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [((WeylUpper.hasSum_slice hg hy).mul_left _).tsum_eq]
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have h := Complex.hasSum_ofReal.2 (WeylUpper.hasSum_slice hg hy)
      exact h.mul_left _
  refine hmain.congr_fun fun n => ?_
  by_cases hn : n = 0
  · subst hn
    rw [hρ0, norm_zero]
    simp only [F]
    rw [setIntegral_congr_fun measurableSet_Ioi (show EqOn (fun y : ℝ => (y : ℂ) ^ (s - 2) *
      ((‖fourierCoeff g 0 y‖ ^ 2 : ℝ) : ℂ)) (fun _ => (0 : ℂ)) (Ioi 0) from fun y hy => by
        simp [fourierCoeff_zero hg hy])]
    simp
  have hc : 0 < 2 * Real.pi * |(n : ℝ)| := by
    have := abs_pos.2 (Int.cast_ne_zero.2 hn : (n : ℝ) ≠ 0); positivity
  have hpt : EqOn (F n) (fun y => ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((y : ℂ) ^ (s - 1) *
      (modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE) *
        modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)))) (Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have h0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy0.ne'
    simp only [F]
    rw [hρ n y hy0, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hy0.le]
    rw [← K_real lamE (2 * Real.pi * |(n : ℝ)| * y), Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsub : (y : ℂ) ^ (s - 1) = (y : ℂ) ^ (s - 2) * y := by
      rw [show s - 1 = (s - 2) + 1 by ring, cpow_add _ _ h0, cpow_one]
    rw [hsub]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_scaled_KK hc,
    GaloisForLFunctions.RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder
      (by rw [nu_re, abs_zero, add_zero]; linarith)]
  simp only [gammaFactor]
  ring

/-! ### The Rankin–Selberg identity -/

/-- **The Rankin–Selberg identity** for `Re s > 1`:
`∫_𝒟 |g|² Σ_v Im(M_v z)^s = 2 G(s) Σ_n |ρ(n)|² (2π|n|)^{-s}`. -/
theorem rankinSelberg_rowSum (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ => 2 * gammaFactor (nu lamE) s *
      (((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((2 * Real.pi * |(n : ℝ)| : ℝ) : ℂ) ^ (-s)))
      (∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * rowSum s z) := by
  rw [← two_mul_strip_eq hg hρ0 hρ hs, strip_eq_mellin hg hρ0 hρ hs]
  have h := (hasSum_mellin_slice hg hρ0 hρ hs).mul_left 2
  refine h.congr_fun fun n => ?_
  ring

/-- **The Rankin–Selberg L-function is the Eisenstein coefficient of the energy density.** For
`Re s > 1`, `Im s ≠ 0`:
`∫_𝒟 |g|² E(s - ½) = π^{-s}/8 · Γ(s/2)² Γ(s/2+ν) Γ(s/2-ν)/Γ(s) · Σ_{n≠0} |ρ(n)|² |n|^{-s}`. -/
theorem rankinSelberg_eisenstein (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) :
    HasSum (fun n : ℤ => (2 * Real.pi : ℂ) ^ (-s) * gammaFactor (nu lamE) s *
      (((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)))
      (∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * normalizedEisenstein (s - 1 / 2) z.re z.im) := by
  have hE : ∀ z : ℍ, normalizedEisenstein (s - 1 / 2) z.re z.im = (1 / 2 : ℂ) * rowSum s z := by
    intro z
    have := normalizedEisenstein_eq_rowSum (u := s - 1 / 2) (by simp; linarith) (by simpa using him) z
    rw [this, show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring]
  simp_rw [hE]
  have h := (rankinSelberg_rowSum hg hρ0 hρ hs).mul_left (1 / 2 : ℂ)
  have e : ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * rowSum s z) =
      (1 / 2 : ℂ) * ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * rowSum s z := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  rw [e]
  refine h.congr_fun fun n => ?_
  rw [ofReal_mul (2 * Real.pi) |(n : ℝ)|, mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _)]
  push_cast
  ring

end CuspRSI

end GaloisForLFunctions.BlackHoleRingdown
