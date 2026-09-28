import GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzLaplaceEscape
import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation
import GaloisForLFunctions.HTGeometry.SchwartzPositiveCompactDiagonal
import GaloisForLFunctions.RHTower.STCFlatGapMeasureReaderNoGo

/-!
# Density of positive even Schwartz sources with a prescribed off-axis Laplace zero

Fix `z` with `Re z ≠ 0` and `Im z ≠ 0`.  Every nonnegative even Schwartz function is a Schwartz
limit of strictly positive even Schwartz functions whose bilateral Laplace transform is entire and
vanishes at `z`.

* **Compact approximation.**  The expanding cutoffs `χ_n f` are nonnegative, even and compactly
  supported, hence have entire Laplace transform, and converge to `f` in every Schwartz seminorm.
* **Four remote phases.**  For `a = Re z > 0`, `τ = Im z > 0` and `R = (2π(N+1) + θ)/τ`,
  the packet `g_R` has Laplace value `G(z)(e^{aR} e^{iθ} + e^{-aR} e^{-iθ})`.  The phases
  `θ = 0, π/2, π, -π/2` give the four directions `2G cosh(aR)`, `2iG sinh(aR)`, `-2G cosh(aR)`,
  `-2iG sinh(aR)`, and nonnegative coefficients of size `O(1/cosh(aR))` cancel any prescribed
  Laplace value exactly while the packets tend to zero in the Schwartz topology.

Consequently the positive even entire-Laplace sources that do not vanish at `z` have empty interior,
and no Schwartz-open admission law forces nonvanishing at `z`.  The positive survivor is the
reporter bound `|𝓛_z f| ≤ ∫ e^{a|x|} |f(x)| dx` for `|Re z| ≤ a`.
-/

open Complex MeasureTheory Filter Topology
open scoped SchwartzMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape

/-! ## The Laplace transform of an entire-Laplace source is entire -/

theorem bilateralLaplace_eq_spectralLaplace (f : ℝ → ℝ) :
    bilateralLaplace f = RHTower.spectralLaplace volume (fun x => (f x : ℂ)) := by
  funext z
  unfold bilateralLaplace RHTower.spectralLaplace
  congr 1
  funext x
  rw [mul_comm (x : ℂ) z, mul_comm]

/-- A source with every exponential moment has an entire bilateral Laplace transform. -/
theorem HasEntireLaplace.differentiable {f : ℝ → ℝ} (hf : HasEntireLaplace f) :
    Differentiable ℂ (bilateralLaplace f) := by
  have hmeas : AEStronglyMeasurable (fun x => (f x : ℂ)) volume :=
    (hf 0).aestronglyMeasurable.congr (Eventually.of_forall fun x => by simp)
  have hmom : ∀ c : ℝ, Integrable (fun u => ‖(f u : ℂ)‖ * Real.exp (c * |u|)) volume := by
    intro c
    refine ((hf (c : ℂ)).norm.add (hf ((-c : ℝ) : ℂ)).norm).mono'
      (hmeas.norm.mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (c * |u|)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
    have hle : Real.exp (c * |u|) ≤ Real.exp (c * u) + Real.exp (-c * u) := by
      rcases abs_cases u with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        linarith [Real.exp_pos (-c * u)]
      · rw [h, show c * -u = -c * u by ring]
        linarith [Real.exp_pos (c * u)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    calc |f u| * Real.exp (c * |u|) ≤ |f u| * (Real.exp (c * u) + Real.exp (-c * u)) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = Real.exp (c * u) * |f u| + Real.exp (-c * u) * |f u| := by ring
  rw [bilateralLaplace_eq_spectralLaplace]
  exact RHTower.differentiable_spectralLaplace hmeas hmom

/-- A continuous compactly supported source has an entire bilateral Laplace transform. -/
theorem hasEntireLaplace_of_hasCompactSupport {f : ℝ → ℝ} (hc : Continuous f)
    (hs : HasCompactSupport f) : HasEntireLaplace f := fun z =>
  Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.mul_left (f := fun x : ℝ => cexp (z * x))
      (hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero))

/-! ## Compact positive approximation -/

/-- The real expanding cutoff `χ_n(t) = b(t/(n+1))`, a real Schwartz function. -/
def realScaledCutoff (n : ℕ) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.postcompCLM Complex.reCLM (SchwartzMap.scaledUnitCutoff n)

/-- The unit bump equal to one on `[-1, 1]` and supported in `[-2, 2]`. -/
def unitIntervalBump : ContDiffBump (0 : ℝ) := ⟨|0| + 1, |0| + 2, by positivity, by norm_num⟩

theorem scaledUnitCutoff_eq_bump (n : ℕ) (t : ℝ) :
    SchwartzMap.scaledUnitCutoff n t = ((unitIntervalBump (((n : ℝ) + 1)⁻¹ * t) : ℝ) : ℂ) :=
  rfl

theorem realScaledCutoff_apply (n : ℕ) (t : ℝ) :
    realScaledCutoff n t = unitIntervalBump (((n : ℝ) + 1)⁻¹ * t) := by
  change (SchwartzMap.scaledUnitCutoff n t).re = _
  rw [scaledUnitCutoff_eq_bump, Complex.ofReal_re]

theorem scaledUnitCutoff_eq_ofReal (n : ℕ) (t : ℝ) :
    SchwartzMap.scaledUnitCutoff n t = (realScaledCutoff n t : ℂ) := by
  rw [realScaledCutoff_apply, scaledUnitCutoff_eq_bump]

theorem realScaledCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ realScaledCutoff n t := by
  rw [realScaledCutoff_apply]
  exact unitIntervalBump.nonneg

theorem realScaledCutoff_neg (n : ℕ) (t : ℝ) : realScaledCutoff n (-t) = realScaledCutoff n t := by
  rw [realScaledCutoff_apply, realScaledCutoff_apply, mul_neg, unitIntervalBump.neg]

theorem hasCompactSupport_realScaledCutoff (n : ℕ) : HasCompactSupport (realScaledCutoff n) :=
  (SchwartzMap.scaledUnitCutoff_hasCompactSupport n).comp_left (g := Complex.re) Complex.zero_re

/-- `(EA.16)`  The compact positive approximation `h_n = χ_n f`. -/
def cutoffApprox (n : ℕ) (f : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (realScaledCutoff n) f

theorem cutoffApprox_apply (n : ℕ) (f : 𝓢(ℝ, ℝ)) (t : ℝ) :
    cutoffApprox n f t = realScaledCutoff n t * f t := by
  rw [cutoffApprox, SchwartzMap.smulLeftCLM_apply_apply (realScaledCutoff n).hasTemperateGrowth,
    smul_eq_mul]

theorem cutoffApprox_nonneg (n : ℕ) {f : 𝓢(ℝ, ℝ)} (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ cutoffApprox n f t := by
  rw [cutoffApprox_apply]
  exact mul_nonneg (realScaledCutoff_nonneg n t) (hf t)

theorem cutoffApprox_neg (n : ℕ) {f : 𝓢(ℝ, ℝ)} (hf : ∀ x, f (-x) = f x) (t : ℝ) :
    cutoffApprox n f (-t) = cutoffApprox n f t := by
  rw [cutoffApprox_apply, cutoffApprox_apply, realScaledCutoff_neg, hf]

theorem hasEntireLaplace_cutoffApprox (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    HasEntireLaplace (cutoffApprox n f) := by
  refine hasEntireLaplace_of_hasCompactSupport (cutoffApprox n f).continuous ?_
  have h : ⇑(cutoffApprox n f) = ⇑(realScaledCutoff n) * ⇑f := by
    funext t
    rw [cutoffApprox_apply, Pi.mul_apply]
  rw [h]
  exact (hasCompactSupport_realScaledCutoff n).mul_right

/-- Complexification does not decrease Schwartz seminorms. -/
theorem seminorm_le_seminorm_realToComplexSchwartz (g : 𝓢(ℝ, ℝ)) (k m : ℕ) :
    SchwartzMap.seminorm ℝ k m g ≤
      SchwartzMap.seminorm ℂ k m (SchwartzMap.realToComplexSchwartz g) := by
  refine SchwartzMap.seminorm_le_bound ℝ k m g (apply_nonneg _ _) fun x => ?_
  have h : ‖iteratedFDeriv ℝ m (⇑(SchwartzMap.realToComplexSchwartz g)) x‖ =
      ‖iteratedFDeriv ℝ m g x‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left ((g.smooth ⊤).contDiffAt)
      (by exact_mod_cast le_top)
  rw [← h]
  exact SchwartzMap.le_seminorm ℂ k m _ x

theorem realToComplexSchwartz_cutoffApprox_sub (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    SchwartzMap.realToComplexSchwartz (cutoffApprox n f - f) =
      SchwartzMap.compactSupportApproximation n (SchwartzMap.realToComplexSchwartz f) -
        SchwartzMap.realToComplexSchwartz f := by
  ext t
  simp only [SchwartzMap.realToComplexSchwartz_apply, sub_apply,
    SchwartzMap.compactSupportApproximation_apply, cutoffApprox_apply, scaledUnitCutoff_eq_ofReal]
  push_cast
  ring

/-- `(EA.16)`  `χ_n f → f` in the Schwartz topology. -/
theorem tendsto_cutoffApprox (f : 𝓢(ℝ, ℝ)) :
    Tendsto (fun n => cutoffApprox n f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ f]
  rintro ⟨k, m⟩ ε hε
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  filter_upwards [(SchwartzMap.tendsto_compactSupportApproximation_sub_seminorm k m
    (SchwartzMap.realToComplexSchwartz f)).eventually (Iio_mem_nhds hε)] with n hn
  calc SchwartzMap.seminorm ℝ k m (cutoffApprox n f - f)
      ≤ SchwartzMap.seminorm ℂ k m (SchwartzMap.realToComplexSchwartz (cutoffApprox n f - f)) :=
        seminorm_le_seminorm_realToComplexSchwartz _ k m
    _ < ε := by
      rw [realToComplexSchwartz_cutoffApprox_sub]
      exact hn

/-! ## Four remote phases -/

/-- The phase period `R = (2π(N+1) + θ)/τ`, on which `τR ≡ θ (mod 2π)`. -/
def phasePeriod (τ θ : ℝ) (N : ℕ) : ℝ := (2 * Real.pi * ((N : ℝ) + 1) + θ) / τ

theorem phasePeriod_pos {τ θ : ℝ} (hτ : 0 < τ) (hθ : -Real.pi ≤ θ) (N : ℕ) :
    0 < phasePeriod τ θ N := by
  unfold phasePeriod
  refine div_pos ?_ hτ
  have hN : (0 : ℝ) ≤ N := N.cast_nonneg
  nlinarith [Real.pi_pos]

theorem tendsto_phasePeriod {τ : ℝ} (hτ : 0 < τ) (θ : ℝ) :
    Tendsto (phasePeriod τ θ) atTop atTop := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) * (2 * Real.pi / τ) + (2 * Real.pi + θ) / τ)
      atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  refine h.congr fun N => ?_
  unfold phasePeriod
  field_simp
  ring

theorem cexp_mul_phasePeriod {z : ℂ} (hτ : 0 < z.im) (θ : ℝ) (N : ℕ) :
    cexp (z * phasePeriod z.im θ N) =
      (Real.exp (z.re * phasePeriod z.im θ N) : ℂ) * cexp ((θ : ℂ) * I) := by
  set R := phasePeriod z.im θ N with hR
  have himR : z.im * R = 2 * Real.pi * ((N : ℝ) + 1) + θ := by
    rw [hR, phasePeriod]
    field_simp
  have hz : z * R = ((z.re * R : ℝ) : ℂ) +
      (((N + 1 : ℕ) : ℂ) * (2 * Real.pi * I) + (θ : ℂ) * I) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) himR
    conv_lhs => rw [← Complex.re_add_im z]
    push_cast at h ⊢
    linear_combination I * h
  rw [hz, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul,
    Complex.ofReal_exp]

/-- On a phase period, `𝓛_z g_R = G(z)(e^{aR} e^{iθ} + e^{-aR} e^{-iθ})`. -/
theorem bilateralLaplace_evenPacket_phase {z : ℂ} (hτ : 0 < z.im) (θ : ℝ) (N : ℕ) :
    bilateralLaplace (evenPacket (phasePeriod z.im θ N)) z =
      cexp (z ^ 2 / 4) * ((Real.exp (z.re * phasePeriod z.im θ N) : ℂ) * cexp ((θ : ℂ) * I) +
        (Real.exp (-(z.re * phasePeriod z.im θ N)) : ℂ) * (cexp ((θ : ℂ) * I))⁻¹) := by
  rw [bilateralLaplace_evenPacket, Complex.exp_neg, cexp_mul_phasePeriod hτ, mul_inv,
    ← Complex.ofReal_inv, ← Real.exp_neg]

theorem cexp_quarter_mul_I : cexp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
  push_cast
  exact Complex.exp_pi_div_two_mul_I

theorem cexp_neg_quarter_mul_I : cexp (((-(Real.pi / 2) : ℝ) : ℂ) * I) = -I := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, cexp_quarter_mul_I, Complex.inv_I]

/-- Phase `0`: the direction `2G(z) cosh(aR)`. -/
theorem bilateralLaplace_phase_zero {z : ℂ} (hτ : 0 < z.im) (N : ℕ) :
    bilateralLaplace (evenPacket (phasePeriod z.im 0 N)) z =
      cexp (z ^ 2 / 4) * (2 * (Real.cosh (z.re * phasePeriod z.im 0 N) : ℂ)) := by
  rw [bilateralLaplace_evenPacket_phase hτ, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    inv_one, Real.cosh_eq]
  push_cast
  ring

/-- Phase `π/2`: the direction `2iG(z) sinh(aR)`. -/
theorem bilateralLaplace_phase_quarter {z : ℂ} (hτ : 0 < z.im) (N : ℕ) :
    bilateralLaplace (evenPacket (phasePeriod z.im (Real.pi / 2) N)) z =
      cexp (z ^ 2 / 4) * (2 * I * (Real.sinh (z.re * phasePeriod z.im (Real.pi / 2) N) : ℂ)) := by
  rw [bilateralLaplace_evenPacket_phase hτ, cexp_quarter_mul_I, Complex.inv_I, Real.sinh_eq]
  push_cast
  ring

/-- Phase `π`: the direction `-2G(z) cosh(aR)`. -/
theorem bilateralLaplace_phase_half {z : ℂ} (hτ : 0 < z.im) (N : ℕ) :
    bilateralLaplace (evenPacket (phasePeriod z.im Real.pi N)) z =
      cexp (z ^ 2 / 4) * (-(2 * (Real.cosh (z.re * phasePeriod z.im Real.pi N) : ℂ))) := by
  rw [bilateralLaplace_evenPacket_phase hτ, Complex.exp_pi_mul_I, Real.cosh_eq]
  push_cast
  ring

/-- Phase `-π/2`: the direction `-2iG(z) sinh(aR)`. -/
theorem bilateralLaplace_phase_neg_quarter {z : ℂ} (hτ : 0 < z.im) (N : ℕ) :
    bilateralLaplace (evenPacket (phasePeriod z.im (-(Real.pi / 2)) N)) z =
      cexp (z ^ 2 / 4) *
        (-(2 * I * (Real.sinh (z.re * phasePeriod z.im (-(Real.pi / 2)) N) : ℂ))) := by
  rw [bilateralLaplace_evenPacket_phase hτ, cexp_neg_quarter_mul_I, inv_neg, Complex.inv_I,
    Real.sinh_eq]
  push_cast
  ring

/-! ## Topology-small remote coefficients -/

theorem exp_div_two_le_cosh (u : ℝ) : Real.exp u / 2 ≤ Real.cosh u := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-u)]

theorem exp_div_four_le_sinh {u : ℝ} (hu : 1 ≤ u) : Real.exp u / 4 ≤ Real.sinh u := by
  have he : 2 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h1 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hinv : Real.exp (-u) ≤ 1 / 2 := by nlinarith [Real.exp_pos (-u)]
  rw [Real.sinh_eq]
  linarith

theorem tendsto_one_add_pow_div_cosh {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun R : ℝ => (1 + R) ^ k / Real.cosh (a * R)) atTop (𝓝 0) := by
  have h2 := (tendsto_one_add_pow_mul_exp_neg ha k).const_mul 2
  rw [mul_zero] at h2
  refine squeeze_zero' ((eventually_ge_atTop 0).mono fun R hR =>
      div_nonneg (pow_nonneg (by linarith) _) (Real.cosh_pos _).le)
    ((eventually_ge_atTop 0).mono fun R hR => ?_) h2
  have hpos : 0 < Real.exp (a * R) := Real.exp_pos _
  rw [div_le_iff₀ (Real.cosh_pos _)]
  calc (1 + R) ^ k = 2 * ((1 + R) ^ k * Real.exp (-a * R)) * (Real.exp (a * R) / 2) := by
        rw [show -a * R = -(a * R) by ring, Real.exp_neg]
        field_simp
    _ ≤ 2 * ((1 + R) ^ k * Real.exp (-a * R)) * Real.cosh (a * R) := by
        gcongr
        exact exp_div_two_le_cosh _

theorem tendsto_one_add_pow_div_sinh {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun R : ℝ => (1 + R) ^ k / Real.sinh (a * R)) atTop (𝓝 0) := by
  have h4 := (tendsto_one_add_pow_mul_exp_neg ha k).const_mul 4
  rw [mul_zero] at h4
  have hev : ∀ᶠ R : ℝ in atTop, 1 ≤ a * R ∧ 0 ≤ R :=
    ((eventually_ge_atTop (1 / a)).and (eventually_ge_atTop 0)).mono fun R hR =>
      ⟨by rw [div_le_iff₀ ha] at hR; linarith [hR.1], hR.2⟩
  refine squeeze_zero' (hev.mono fun R hR => div_nonneg (pow_nonneg (by linarith [hR.2]) _)
      (by linarith [exp_div_four_le_sinh hR.1, Real.exp_pos (a * R)]))
    (hev.mono fun R hR => ?_) h4
  have hs := exp_div_four_le_sinh hR.1
  have hpos : 0 < Real.exp (a * R) := Real.exp_pos _
  rw [div_le_iff₀ (by linarith)]
  calc (1 + R) ^ k = 4 * ((1 + R) ^ k * Real.exp (-a * R)) * (Real.exp (a * R) / 4) := by
        rw [show -a * R = -(a * R) by ring, Real.exp_neg]
        field_simp
    _ ≤ 4 * ((1 + R) ^ k * Real.exp (-a * R)) * Real.sinh (a * R) := by
        gcongr
        exact mul_nonneg zero_le_four (mul_nonneg (pow_nonneg (by linarith [hR.2]) _)
          (Real.exp_pos _).le)

/-- Packets with coefficients beating every polynomial tend to zero in the Schwartz topology. -/
theorem tendsto_smul_evenPacket_zero {c R : ℕ → ℝ} (hR : ∀ N, 0 ≤ R N)
    (h : ∀ k : ℕ, Tendsto (fun N => |c N| * (1 + R N) ^ k) atTop (𝓝 0)) :
    Tendsto (fun N => c N • evenPacket (R N)) atTop (𝓝 0) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ 0]
  rintro ⟨k, n⟩ ε hε
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  have hlim := (h k).const_mul (2 * translationConstant k n gaussianPacket)
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with N hN
  refine lt_of_le_of_lt ?_ hN
  rw [map_smul_eq_mul, Real.norm_eq_abs]
  calc |c N| * SchwartzMap.seminorm ℝ k n (evenPacket (R N))
      ≤ |c N| * (2 * ((1 + |R N|) ^ k * translationConstant k n gaussianPacket)) := by
        gcongr
        exact seminorm_evenPacket_le _ _ _
    _ = _ := by
      rw [abs_of_nonneg (hR N)]
      ring

theorem tendsto_cosh_coeff_smul_zero {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) {R : ℕ → ℝ}
    (hR : ∀ N, 0 ≤ R N) (hRlim : Tendsto R atTop atTop) :
    Tendsto (fun N => (K / (2 * Real.cosh (a * R N))) • evenPacket (R N)) atTop (𝓝 0) := by
  refine tendsto_smul_evenPacket_zero hR fun k => ?_
  have h := ((tendsto_one_add_pow_div_cosh ha k).comp hRlim).const_mul (K / 2)
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  have hc : 0 < Real.cosh (a * R N) := Real.cosh_pos _
  rw [Function.comp_apply, abs_of_nonneg (div_nonneg hK (by positivity))]
  field_simp

theorem tendsto_sinh_coeff_smul_zero {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) {R : ℕ → ℝ}
    (hR : ∀ N, 0 < R N) (hRlim : Tendsto R atTop atTop) :
    Tendsto (fun N => (K / (2 * Real.sinh (a * R N))) • evenPacket (R N)) atTop (𝓝 0) := by
  refine tendsto_smul_evenPacket_zero (fun N => (hR N).le) fun k => ?_
  have h := ((tendsto_one_add_pow_div_sinh ha k).comp hRlim).const_mul (K / 2)
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  have hs : 0 < Real.sinh (a * R N) := Real.sinh_pos_iff.mpr (mul_pos ha (hR N))
  rw [Function.comp_apply, abs_of_nonneg (div_nonneg hK (by positivity))]
  field_simp

/-! ## Exact positive cancellation -/

/-- `(EA.17)–(EA.24)`  **Exact zero insertion by remote positive packets.**  For `Re z > 0`,
`Im z > 0` and any prescribed value `L`, there are strictly positive even Schwartz packets with
entire Laplace transform, tending to zero in the Schwartz topology, whose Laplace transform at `z`
equals `L`. -/
theorem exists_zeroInsertion {z : ℂ} (ha : 0 < z.re) (hτ : 0 < z.im) (L : ℂ) :
    ∃ k : ℕ → 𝓢(ℝ, ℝ), (∀ N x, 0 < k N x) ∧ (∀ N x, k N (-x) = k N x) ∧
      (∀ N, HasEntireLaplace (k N)) ∧ Tendsto k atTop (𝓝 0) ∧
      ∀ N, bilateralLaplace (k N) z = L := by
  set G : ℂ := cexp (z ^ 2 / 4) with hG
  set V : ℂ := L / G with hV
  have hq : -Real.pi ≤ -(Real.pi / 2) := by linarith [Real.pi_pos]
  have hR0 : ∀ N, 0 < phasePeriod z.im 0 N := phasePeriod_pos hτ (by linarith [Real.pi_pos])
  have hR1 : ∀ N, 0 < phasePeriod z.im (Real.pi / 2) N :=
    phasePeriod_pos hτ (by linarith [Real.pi_pos])
  have hR2 : ∀ N, 0 < phasePeriod z.im Real.pi N := phasePeriod_pos hτ (by linarith [Real.pi_pos])
  have hR3 : ∀ N, 0 < phasePeriod z.im (-(Real.pi / 2)) N := phasePeriod_pos hτ hq
  have hs1 : ∀ N, 0 < Real.sinh (z.re * phasePeriod z.im (Real.pi / 2) N) := fun N =>
    Real.sinh_pos_iff.mpr (mul_pos ha (hR1 N))
  have hs3 : ∀ N, 0 < Real.sinh (z.re * phasePeriod z.im (-(Real.pi / 2)) N) := fun N =>
    Real.sinh_pos_iff.mpr (mul_pos ha (hR3 N))
  set c0 : ℕ → ℝ := fun N =>
    (max V.re 0 + 1) / (2 * Real.cosh (z.re * phasePeriod z.im 0 N)) with hc0
  set c1 : ℕ → ℝ := fun N =>
    max V.im 0 / (2 * Real.sinh (z.re * phasePeriod z.im (Real.pi / 2) N)) with hc1
  set c2 : ℕ → ℝ := fun N =>
    (max (-V.re) 0 + 1) / (2 * Real.cosh (z.re * phasePeriod z.im Real.pi N)) with hc2
  set c3 : ℕ → ℝ := fun N =>
    max (-V.im) 0 / (2 * Real.sinh (z.re * phasePeriod z.im (-(Real.pi / 2)) N)) with hc3
  have hc0pos : ∀ N, 0 < c0 N := fun N =>
    div_pos (by positivity) (by positivity)
  have hc1nn : ∀ N, 0 ≤ c1 N := fun N =>
    div_nonneg (le_max_right _ _) (by linarith [hs1 N])
  have hc2nn : ∀ N, 0 ≤ c2 N := fun N =>
    div_nonneg (by positivity) (by positivity)
  have hc3nn : ∀ N, 0 ≤ c3 N := fun N =>
    div_nonneg (le_max_right _ _) (by linarith [hs3 N])
  have hE : ∀ θ N (c : ℝ), HasEntireLaplace ⇑(c • evenPacket (phasePeriod z.im θ N)) :=
    fun θ N c => (hasEntireLaplace_evenPacket _).schwartz_smul c
  refine ⟨fun N => c0 N • evenPacket (phasePeriod z.im 0 N) +
      c1 N • evenPacket (phasePeriod z.im (Real.pi / 2) N) +
      c2 N • evenPacket (phasePeriod z.im Real.pi N) +
      c3 N • evenPacket (phasePeriod z.im (-(Real.pi / 2)) N), ?_, ?_, ?_, ?_, ?_⟩
  · intro N x
    simp only [add_apply, smul_apply, smul_eq_mul]
    have h0 := mul_pos (hc0pos N) (evenPacket_pos (phasePeriod z.im 0 N) x)
    have h1 := mul_nonneg (hc1nn N) (evenPacket_pos (phasePeriod z.im (Real.pi / 2) N) x).le
    have h2 := mul_nonneg (hc2nn N) (evenPacket_pos (phasePeriod z.im Real.pi N) x).le
    have h3 := mul_nonneg (hc3nn N) (evenPacket_pos (phasePeriod z.im (-(Real.pi / 2)) N) x).le
    linarith
  · intro N x
    simp only [add_apply, smul_apply, smul_eq_mul, evenPacket_neg]
  · intro N
    exact (((hE 0 N _).schwartz_add (hE _ N _)).schwartz_add (hE _ N _)).schwartz_add (hE _ N _)
  · have t0 := tendsto_cosh_coeff_smul_zero ha (K := max V.re 0 + 1) (by positivity)
      (fun N => (hR0 N).le) (tendsto_phasePeriod hτ 0)
    have t1 := tendsto_sinh_coeff_smul_zero ha (K := max V.im 0) (le_max_right _ _)
      hR1 (tendsto_phasePeriod hτ (Real.pi / 2))
    have t2 := tendsto_cosh_coeff_smul_zero ha (K := max (-V.re) 0 + 1) (by positivity)
      (fun N => (hR2 N).le) (tendsto_phasePeriod hτ Real.pi)
    have t3 := tendsto_sinh_coeff_smul_zero ha (K := max (-V.im) 0) (le_max_right _ _)
      hR3 (tendsto_phasePeriod hτ (-(Real.pi / 2)))
    have h := ((t0.add t1).add t2).add t3
    simp only [add_zero] at h
    exact h
  · intro N
    rw [bilateralLaplace_schwartz_add (((hE 0 N _).schwartz_add (hE _ N _)).schwartz_add
        (hE _ N _)) (hE _ N _),
      bilateralLaplace_schwartz_add ((hE 0 N _).schwartz_add (hE _ N _)) (hE _ N _),
      bilateralLaplace_schwartz_add (hE 0 N _) (hE _ N _),
      bilateralLaplace_schwartz_smul, bilateralLaplace_schwartz_smul,
      bilateralLaplace_schwartz_smul, bilateralLaplace_schwartz_smul,
      bilateralLaplace_phase_zero hτ, bilateralLaplace_phase_quarter hτ,
      bilateralLaplace_phase_half hτ, bilateralLaplace_phase_neg_quarter hτ]
    have e0 : ((c0 N : ℝ) : ℂ) * (2 * (Real.cosh (z.re * phasePeriod z.im 0 N) : ℂ)) =
        ((max V.re 0 + 1 : ℝ) : ℂ) := by
      have hc : 0 < Real.cosh (z.re * phasePeriod z.im 0 N) := Real.cosh_pos _
      have : c0 N * (2 * Real.cosh (z.re * phasePeriod z.im 0 N)) = max V.re 0 + 1 := by
        rw [hc0]
        field_simp
      exact_mod_cast this
    have e1 : ((c1 N : ℝ) : ℂ) * (2 * (Real.sinh (z.re * phasePeriod z.im (Real.pi / 2) N) : ℂ)) =
        ((max V.im 0 : ℝ) : ℂ) := by
      have hs := hs1 N
      have : c1 N * (2 * Real.sinh (z.re * phasePeriod z.im (Real.pi / 2) N)) = max V.im 0 := by
        rw [hc1]
        field_simp
      exact_mod_cast this
    have e2 : ((c2 N : ℝ) : ℂ) * (2 * (Real.cosh (z.re * phasePeriod z.im Real.pi N) : ℂ)) =
        ((max (-V.re) 0 + 1 : ℝ) : ℂ) := by
      have hc : 0 < Real.cosh (z.re * phasePeriod z.im Real.pi N) := Real.cosh_pos _
      have : c2 N * (2 * Real.cosh (z.re * phasePeriod z.im Real.pi N)) = max (-V.re) 0 + 1 := by
        rw [hc2]
        field_simp
      exact_mod_cast this
    have e3 : ((c3 N : ℝ) : ℂ) *
        (2 * (Real.sinh (z.re * phasePeriod z.im (-(Real.pi / 2)) N) : ℂ)) =
        ((max (-V.im) 0 : ℝ) : ℂ) := by
      have hs := hs3 N
      have : c3 N * (2 * Real.sinh (z.re * phasePeriod z.im (-(Real.pi / 2)) N)) =
          max (-V.im) 0 := by
        rw [hc3]
        field_simp
      exact_mod_cast this
    have hx : ((max V.re 0 : ℝ) : ℂ) - ((max (-V.re) 0 : ℝ) : ℂ) = (V.re : ℂ) := by
      exact_mod_cast max_zero_sub_eq_self V.re
    have hy : ((max V.im 0 : ℝ) : ℂ) - ((max (-V.im) 0 : ℝ) : ℂ) = (V.im : ℂ) := by
      exact_mod_cast max_zero_sub_eq_self V.im
    have hGne : G ≠ 0 := Complex.exp_ne_zero _
    have hVG : G * ((V.re : ℂ) + (V.im : ℂ) * I) = L := by
      rw [Complex.re_add_im, hV, mul_div_cancel₀ _ hGne]
    push_cast at e0 e1 e2 e3 ⊢
    linear_combination G * e0 + G * I * e1 - G * e2 - G * I * e3 + G * hx + G * I * hy + hVG

/-! ## Density -/

/-- The strictly positive even Schwartz sources with entire Laplace transform vanishing at `z`. -/
def offAxisZeroSources (z : ℂ) : Set 𝓢(ℝ, ℝ) :=
  {F | (∀ x, 0 < F x) ∧ (∀ x, F (-x) = F x) ∧ HasEntireLaplace F ∧ bilateralLaplace F z = 0}

theorem mem_closure_offAxisZeroSources_of_hasEntireLaplace {z : ℂ} (hre : z.re ≠ 0)
    (him : z.im ≠ 0) {h : 𝓢(ℝ, ℝ)} (h0 : ∀ x, 0 ≤ h x) (he : ∀ x, h (-x) = h x)
    (hent : HasEntireLaplace h) : h ∈ closure (offAxisZeroSources z) := by
  set w : ℂ := ((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I with hw
  have hwre : 0 < w.re := by simp [hw, abs_pos.mpr hre]
  have hwim : 0 < w.im := by simp [hw, abs_pos.mpr him]
  obtain ⟨k, hkpos, hkeven, hkent, hk0, hkL⟩ :=
    exists_zeroInsertion hwre hwim (-bilateralLaplace h w)
  refine mem_closure_of_tendsto (f := fun N => h + k N) (b := atTop) ?_
    (Eventually.of_forall fun N => ?_)
  · simpa using (tendsto_const_nhds (x := h)).add hk0
  · have hev : ∀ x, (h + k N) (-x) = (h + k N) x := fun x => by
      simp only [add_apply, he, hkeven]
    refine ⟨fun x => ?_, hev, hent.schwartz_add (hkent N), ?_⟩
    · simp only [add_apply]
      exact add_pos_of_nonneg_of_pos (h0 x) (hkpos N x)
    · rw [bilateralLaplace_eq_zero_iff_abs hev, ← hw,
        bilateralLaplace_schwartz_add hent (hkent N), hkL]
      ring

/-- `(EA.15)`  **Zero-insertion density.**  For `Re z ≠ 0` and `Im z ≠ 0`, every nonnegative even
Schwartz function lies in the Schwartz closure of the strictly positive even Schwartz sources with
entire Laplace transform vanishing at `z`. -/
theorem mem_closure_offAxisZeroSources {z : ℂ} (hre : z.re ≠ 0) (him : z.im ≠ 0)
    {f : 𝓢(ℝ, ℝ)} (hf0 : ∀ x, 0 ≤ f x) (hfe : ∀ x, f (-x) = f x) :
    f ∈ closure (offAxisZeroSources z) := by
  rw [← closure_closure]
  exact mem_closure_of_tendsto (tendsto_cutoffApprox f) (Eventually.of_forall fun n =>
    mem_closure_offAxisZeroSources_of_hasEntireLaplace hre him (cutoffApprox_nonneg n hf0)
      (cutoffApprox_neg n hfe) (hasEntireLaplace_cutoffApprox n f))

/-- `(EA.15)`, neighborhood form: every Schwartz neighborhood of a nonnegative even `f` contains a
strictly positive even source whose bilateral Laplace transform is entire and vanishes at `z`. -/
theorem exists_offAxisZeroSource_mem_nhds {z : ℂ} (hre : z.re ≠ 0) (him : z.im ≠ 0)
    {f : 𝓢(ℝ, ℝ)} (hf0 : ∀ x, 0 ≤ f x) (hfe : ∀ x, f (-x) = f x) {U : Set 𝓢(ℝ, ℝ)}
    (hU : U ∈ 𝓝 f) :
    ∃ F ∈ U, (∀ x, 0 < F x) ∧ (∀ x, F (-x) = F x) ∧ HasEntireLaplace F ∧
      Differentiable ℂ (bilateralLaplace F) ∧ bilateralLaplace F z = 0 := by
  obtain ⟨F, hFU, hF⟩ :=
    mem_closure_iff_nhds.mp (mem_closure_offAxisZeroSources hre him hf0 hfe) U hU
  exact ⟨F, hFU, hF.1, hF.2.1, hF.2.2.1, hF.2.2.1.differentiable, hF.2.2.2⟩

/-- The strictly positive even Schwartz sources with entire Laplace transform. -/
def positiveEvenEntireSources : Set 𝓢(ℝ, ℝ) :=
  {F | (∀ x, 0 < F x) ∧ (∀ x, F (-x) = F x) ∧ HasEntireLaplace F}

/-- **Corollary 6.2.**  For `Re z ≠ 0` and `Im z ≠ 0`, the positive even entire-Laplace sources
with `𝓛_z f ≠ 0` have empty interior for the inherited Schwartz topology. -/
theorem interior_nonvanishing_eq_empty {z : ℂ} (hre : z.re ≠ 0) (him : z.im ≠ 0) :
    interior {F : positiveEvenEntireSources | bilateralLaplace F z ≠ 0} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  intro F
  rw [closure_subtype]
  obtain ⟨hFpos, hFeven, -⟩ := F.2
  refine closure_mono ?_ (mem_closure_offAxisZeroSources hre him (fun x => (hFpos x).le) hFeven)
  rintro G ⟨hGpos, hGeven, hGent, hG0⟩
  exact ⟨⟨G, hGpos, hGeven, hGent⟩, by simp [hG0], rfl⟩

/-- **No Schwartz-open selection law.**  An open admission set of Schwartz sources on which every
positive even entire-Laplace source is nonvanishing at `z` contains no nonnegative even source. -/
theorem no_open_admission_selection {z : ℂ} (hre : z.re ≠ 0) (him : z.im ≠ 0)
    {U : Set 𝓢(ℝ, ℝ)} (hU : IsOpen U)
    (hsel : ∀ F ∈ U, (∀ x, 0 < F x) → (∀ x, F (-x) = F x) → HasEntireLaplace F →
      bilateralLaplace F z ≠ 0)
    {f : 𝓢(ℝ, ℝ)} (hfU : f ∈ U) (hf0 : ∀ x, 0 ≤ f x) : ¬ ∀ x, f (-x) = f x := by
  intro hfe
  obtain ⟨F, hFU, hFpos, hFeven, hFent, -, hF0⟩ :=
    exists_offAxisZeroSource_mem_nhds hre him hf0 hfe (hU.mem_nhds hfU)
  exact hsel F hFU hFpos hFeven hFent hF0

/-! ## The positive survivor: reporter-dominating admission -/

/-- `(EA.31)`  The reporter bound `|𝓛_z f| ≤ ∫ e^{a|x|} |f(x)| dx` for `|Re z| ≤ a`. -/
theorem norm_bilateralLaplace_le_reporter {f : ℝ → ℝ} {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a)
    (hf : Integrable (fun x => Real.exp (a * |x|) * |f x|)) :
    ‖bilateralLaplace f z‖ ≤ ∫ x, Real.exp (a * |x|) * |f x| := by
  refine norm_integral_le_of_norm_le hf (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc z.re * x ≤ |z.re * x| := le_abs_self _
    _ = |z.re| * |x| := abs_mul _ _
    _ ≤ a * |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg x)

theorem integrable_cexp_mul_of_reporter {f : ℝ → ℝ} {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a)
    (hf : Integrable (fun x => Real.exp (a * |x|) * f x)) :
    Integrable (fun x : ℝ => cexp (z * x) * (f x : ℂ)) := by
  have hfm : AEStronglyMeasurable f volume := by
    have h := (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun x : ℝ =>
      Real.exp (-(a * |x|)))).mul hf.aestronglyMeasurable
    refine h.congr (Eventually.of_forall fun x => ?_)
    change Real.exp (-(a * |x|)) * (Real.exp (a * |x|) * f x) = f x
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  refine hf.norm.mono'
    ((by fun_prop : Continuous fun x : ℝ => cexp (z * x)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hfm)) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  gcongr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc z.re * x ≤ |z.re * x| := le_abs_self _
    _ = |z.re| * |x| := abs_mul _ _
    _ ≤ a * |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg x)

/-- `(EA.30)–(EA.31)`  On sources controlling `∫ e^{a|x|} |f|`, evaluation at every `z` with
`|Re z| ≤ a` is Lipschitz, hence continuous, for the reporter norm. -/
theorem norm_bilateralLaplace_sub_le_reporter {f g : ℝ → ℝ} {a : ℝ} {z : ℂ} (hz : |z.re| ≤ a)
    (hf : Integrable (fun x => Real.exp (a * |x|) * f x))
    (hg : Integrable (fun x => Real.exp (a * |x|) * g x)) :
    ‖bilateralLaplace f z - bilateralLaplace g z‖ ≤
      ∫ x, Real.exp (a * |x|) * |f x - g x| := by
  have hsub : bilateralLaplace f z - bilateralLaplace g z =
      bilateralLaplace (fun x => f x - g x) z := by
    unfold bilateralLaplace
    rw [← integral_sub (integrable_cexp_mul_of_reporter hz hf)
      (integrable_cexp_mul_of_reporter hz hg)]
    congr 1
    funext x
    push_cast
    ring
  rw [hsub]
  refine norm_bilateralLaplace_le_reporter hz ((hf.sub hg).norm.congr
    (Eventually.of_forall fun x => ?_))
  change ‖Real.exp (a * |x|) * f x - Real.exp (a * |x|) * g x‖ = Real.exp (a * |x|) * |f x - g x|
  rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

end GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape
