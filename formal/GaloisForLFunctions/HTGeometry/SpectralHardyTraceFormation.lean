import GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit
import GaloisForLFunctions.HTGeometry.HardyLineIsometry
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCongr
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Spectral Hardy-trace formation

For a diagonal heat source the reachability map reads `⟨e_j, W h⟩ = v_j (ℒh)(λ_j)` (**(HTF.11)**),
where `ℒ` is the half-line Laplace transform.  Paley–Wiener identifies `ℒ` with an isometry of
`L²(0,∞)` onto the Hardy space `H²` of the right half-plane, normalized by
`‖H‖²_{H²} = (2π)^{-1} sup_x ∫ |H(x+iy)|² dy` (**(HTF.5)–(HTF.7)**).  Hence:

* `m(L)v ∈ Ran W` iff `m|_Λ` is the trace of an `H²` function on the spectrum `Λ = {λ_j}`
  (**(HTF.9)**), and the endogenous capital is the quotient norm
  `q_G(m(L)v) = min {‖H‖²_{H²} : H|_Λ = m|_Λ}` (**(HTF.10)**);
* on an `H²` uniqueness set the history is unique and `q_G(m(L)v) = ‖m‖²_{H²}` for `m ∈ H²`
  (**(HTF.12)–(HTF.13)**);
* a bounded holomorphic function on a half-plane vanishing on a real sequence with
  `Σ λ/(1+λ²) = ∞` vanishes identically (half-plane Blaschke condition), so a function of the
  Nevanlinna class (bounded type) outside `H²` has infinite capital on such a spectrum
  (**(HTF.14)**).
-/

open MeasureTheory Set Filter Topology Complex Metric
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

/-! ## The Hardy norm and Paley–Wiener -/

/-- **(HTF.6)** The Hardy norm `‖H‖²_{H²} = (2π)^{-1} sup_{x>0} ∫ |H(x+iy)|² dy`. -/
def hardyNormSq (F : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (σ : ℝ) (_ : 0 < σ), ENNReal.ofReal ((2 * Real.pi)⁻¹ * ∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ (2 : ℕ))

theorem integral_exp_mul_norm_sq_le {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ (2 : ℕ) ≤ ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ (2 : ℕ) := by
  refine setIntegral_mono_on (integrableOn_exp_mul_norm_sq hφ hσ) (integrableOn_norm_sq_of_memLp hφ)
    measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hle : Real.exp (-(2 * σ * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  nlinarith [sq_nonneg ‖φ x‖]

/-- The Hardy norm of a Laplace transform is the `L²` norm of its datum. -/
theorem hardyNormSq_laplaceRay {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    hardyNormSq (laplaceRay φ) = ENNReal.ofReal (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine le_antisymm (iSup₂_le fun σ hσ => ENNReal.ofReal_le_ofReal ?_) ?_
  · rw [integral_norm_sq_laplaceRay_vertical hφ hσ, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
    exact integral_exp_mul_norm_sq_le hφ hσ
  · have ht := (tendsto_integral_norm_sq_laplaceRay_vertical hφ).const_mul (2 * Real.pi)⁻¹
    rw [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at ht
    have ht' := (ENNReal.continuous_ofReal.tendsto _).comp ht
    exact le_of_tendsto ht' (eventually_mem_nhdsWithin.mono fun σ (hσ : 0 < σ) =>
      le_iSup₂_of_le (f := fun σ (_ : 0 < σ) => ENNReal.ofReal ((2 * Real.pi)⁻¹ *
        ∫ y : ℝ, ‖laplaceRay φ (hardyVerticalLine σ y)‖ ^ (2 : ℕ))) σ hσ le_rfl)

/-- The Hardy norm of a Hardy function is the `L²` norm of its Paley–Wiener datum. -/
theorem hardyNormSq_eq_datum {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    hardyNormSq F = ENNReal.ofReal (∫ x in Ioi (0 : ℝ), ‖hardyDatum F hF x‖ ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine le_antisymm (iSup₂_le fun σ hσ => ENNReal.ofReal_le_ofReal ?_) ?_
  · rw [isHalfPlaneHardy_integral_norm_sq_vertical_eq hF hσ, ← mul_assoc, inv_mul_cancel₀ hpi.ne',
      one_mul]
    exact integral_exp_mul_norm_sq_le (memLp_two_hardyDatum hF) hσ
  · have ht := (tendsto_isHalfPlaneHardy_integral_norm_sq_vertical hF).const_mul (2 * Real.pi)⁻¹
    rw [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at ht
    have ht' := (ENNReal.continuous_ofReal.tendsto _).comp ht
    exact le_of_tendsto ht' (eventually_mem_nhdsWithin.mono fun σ (hσ : 0 < σ) =>
      le_iSup₂_of_le (f := fun σ (_ : 0 < σ) => ENNReal.ofReal ((2 * Real.pi)⁻¹ *
        ∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ (2 : ℕ))) σ hσ le_rfl)

theorem norm_sq_halfLineL2 (h : HalfLineL2) : ‖h‖ ^ 2 = ∫ x in Ioi (0 : ℝ), ‖(h : ℝ → ℂ) x‖ ^ (2 : ℕ) :=
  Lp_two_norm_sq_eq_integral h

/-- **(HTF.7) Paley–Wiener.**  The Laplace transform maps `L²(0,∞)` isometrically onto `H²`:
`ℒh ∈ H²` with `‖ℒh‖²_{H²} = ‖h‖²`, and every `H ∈ H²` is `ℒh` on the half-plane for an
`h ∈ L²(0,∞)` with `‖h‖² = ‖H‖²_{H²}`. -/
theorem paleyWiener_halfPlane :
    (∀ h : HalfLineL2, IsHalfPlaneHardy (laplaceRay h) (‖h‖ ^ 2) ∧
      hardyNormSq (laplaceRay h) = ENNReal.ofReal (‖h‖ ^ 2)) ∧
    ∀ (F : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy F M → ∃ h : HalfLineL2,
      (∀ w : ℂ, 0 < w.re → F w = laplaceRay h w) ∧ hardyNormSq F = ENNReal.ofReal (‖h‖ ^ 2) := by
  refine ⟨fun h => ?_, fun F M hF => ?_⟩
  · rw [norm_sq_halfLineL2]
    exact ⟨isHalfPlaneHardy_laplaceRay (Lp.memLp h), hardyNormSq_laplaceRay (Lp.memLp h)⟩
  · set h : HalfLineL2 := (memLp_two_hardyDatum hF).toLp _
    have hae : (h : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] hardyDatum F hF := (memLp_two_hardyDatum hF).coeFn_toLp
    have hlap : ∀ w : ℂ, laplaceRay h w = laplaceRay (hardyDatum F hF) w := fun w => by
      unfold laplaceRay
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    refine ⟨h, fun w hw => by rw [hlap, ← isHalfPlaneHardy_eq_laplaceRay hF hw], ?_⟩
    rw [hardyNormSq_eq_datum hF, norm_sq_halfLineL2]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]

/-- **(HTF.25)** Point evaluation in `H²`: `|H(w)| ≤ ‖H‖_{H²}/√(2 Re w)`. -/
theorem norm_le_hardyNormSq {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {w : ℂ} (hw : 0 < w.re) :
    ‖F w‖ ≤ Real.sqrt (hardyNormSq F).toReal / Real.sqrt (2 * w.re) := by
  rw [hardyNormSq_eq_datum hF, ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity)]
  exact norm_le_of_isHalfPlaneHardy hF hw

/-- An `H²` function is bounded on every shifted half-plane `Re w > δ`, `δ > 0`. -/
theorem norm_le_of_isHalfPlaneHardy_of_lt {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {δ : ℝ}
    (hδ : 0 < δ) {w : ℂ} (hw : δ < w.re) :
    ‖F w‖ ≤ rayL2Norm (hardyDatum F hF) / Real.sqrt (2 * δ) :=
  (norm_le_of_isHalfPlaneHardy hF (hδ.trans hw)).trans
    (div_le_div_of_nonneg_left (rayL2Norm_nonneg _) (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (by linarith)))

/-- The exponential `e^{-az}` is not in `H²`: its modulus is constant on vertical lines. -/
theorem not_isHalfPlaneHardy_exp (a M : ℝ) : ¬ IsHalfPlaneHardy (fun z => Complex.exp (-(a * z))) M := by
  intro h
  have h1 := (h.memLp 1 one_pos).norm
  have hconst : (fun ξ : ℝ => ‖Complex.exp (-((a : ℂ) * rayLine 1 ξ))‖) = fun _ => Real.exp (-a) := by
    funext ξ
    rw [Complex.norm_exp]
    simp [rayLine]
  rw [hconst, memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top] at h1
  rcases h1 with h1 | h1
  · exact (Real.exp_pos _).ne' h1
  · simp at h1

/-- **(HTF.23)** The radial multiplier `d_a(z) = e^{2az} - 1`. -/
def radialMultiplier (a : ℝ) (z : ℂ) : ℂ := Complex.exp (2 * a * z) - 1

theorem radialMultiplier_ofReal (a x : ℝ) :
    radialMultiplier a x = ((Real.exp (2 * a * x) - 1 : ℝ) : ℂ) := by
  rw [radialMultiplier]
  push_cast
  rfl

/-- **(HTF.21)** The offset-window multiplier `m_{a,T}(z) = e^{-az}(1 - e^{-Tz})/(Tz)`. -/
def offsetWindowMultiplier (a T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a * z)) * (1 - Complex.exp (-(T * z))) / (T * z)

theorem integral_Ioc_expRay (a : ℝ) {T : ℝ} (hT : 0 < T) {z : ℂ} (hz : z ≠ 0) :
    ∫ t in Ioc a (a + T), expRay z t = T * offsetWindowMultiplier a T z := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hfun : (fun t : ℝ => expRay z t) = fun t : ℝ => Complex.exp (-z * t) := by
    funext t
    rw [expRay, neg_mul]
  rw [hfun, integral_exp_mul_complex (neg_ne_zero.2 hz), offsetWindowMultiplier]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hsplit : Complex.exp (-z * ((a + T : ℝ) : ℂ)) = Complex.exp (-(a * z)) * Complex.exp (-(T * z)) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  rw [hsplit, show -z * (a : ℂ) = -(a * z) by ring]
  field_simp
  ring

theorem halfLine_Ioc_offset_ne_top (a T : ℝ) : (volume.restrict (Ioi (0 : ℝ))) (Ioc a (a + T)) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (Measure.restrict_apply_le _ _)

/-- **(HTF.21)** The offset window control `T^{-1} 1_{(a,a+T]}`. -/
def offsetWindowControl (a T : ℝ) : HalfLineL2 :=
  indicatorConstLp 2 measurableSet_Ioc (halfLine_Ioc_offset_ne_top a T) ((T⁻¹ : ℝ) : ℂ)

theorem Ioc_offset_subset_Ioi {a T : ℝ} (ha : 0 ≤ a) : Ioc a (a + T) ⊆ Ioi 0 :=
  fun _ ht => lt_of_le_of_lt ha ht.1

/-- **(HTF.22)** `‖T^{-1} 1_{(a,a+T]}‖² = 1/T`, independently of the location `a ≥ 0`. -/
theorem norm_offsetWindowControl_sq {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) :
    ‖offsetWindowControl a T‖ ^ 2 = 1 / T := by
  have hreal : (volume.restrict (Ioi (0 : ℝ))).real (Ioc a (a + T)) = T := by
    rw [measureReal_def, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.2 (Ioc_offset_subset_Ioi ha), Real.volume_Ioc, add_sub_cancel_left,
      ENNReal.toReal_ofReal hT.le]
  rw [offsetWindowControl, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, hreal,
    Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hT.le), mul_pow, ENNReal.toReal_ofNat,
    show T ^ (1 / 2 : ℝ) = Real.sqrt T from (Real.sqrt_eq_rpow T).symm, Real.sq_sqrt hT.le]
  field_simp

/-- **(HTF.21)** `ℒ(T^{-1} 1_{(a,a+T]}) = m_{a,T}`. -/
theorem laplaceRay_offsetWindowControl {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) {z : ℂ} (hz : z ≠ 0) :
    laplaceRay (offsetWindowControl a T) z = offsetWindowMultiplier a T z := by
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      (offsetWindowControl a T : ℝ → ℂ) x * expRay z x =
        (Ioc a (a + T)).indicator (fun x => ((T⁻¹ : ℝ) : ℂ) * expRay z x) x := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
      (hμs := halfLine_Ioc_offset_ne_top a T) (c := ((T⁻¹ : ℝ) : ℂ))] with x hx
    rw [offsetWindowControl, hx]
    by_cases hmem : x ∈ Ioc a (a + T)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  rw [laplaceRay, integral_congr_ae hae, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (Ioc_offset_subset_Ioi ha),
    integral_const_mul, integral_Ioc_expRay a hT hz]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp

/-! ## The Hardy-trace formation law -/

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

/-- **(HTF.11)** `⟨e_j, W h⟩ = v_j (ℒh)(λ_j)`. -/
theorem heatReachability_apply_eq_laplace (h : HalfLineL2) (j : ι) :
    s.heatReachability h j = s.v j * laplaceRay h (s.lam j) := by
  rw [s.heatReachability_apply, MeasureTheory.L2.inner_def, laplaceRay, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [s.heatFrame_ae j] with t ht
  rw [ht, RCLike.inner_apply, map_mul, Complex.conj_conj, Complex.conj_ofReal, expRay]
  push_cast
  ring_nf

omit [DecidableEq ι] in
theorem memℓp_spectralPacket (m : ℂ → ℂ) (hm : Summable fun j => ‖s.v j * m (s.lam j)‖ ^ 2) :
    Memℓp (fun j => s.v j * m (s.lam j)) 2 :=
  memℓp_gen (by simpa using hm)

/-- **(HTF.4)** The spectral packet `m(L)v = Σ_j v_j m(λ_j) e_j`. -/
def spectralPacket (m : ℂ → ℂ) (hm : Summable fun j => ‖s.v j * m (s.lam j)‖ ^ 2) : ℓ²ι :=
  ⟨fun j => s.v j * m (s.lam j), s.memℓp_spectralPacket m hm⟩

omit [DecidableEq ι] in
theorem spectralPacket_apply (m : ℂ → ℂ) (hm : Summable fun j => ‖s.v j * m (s.lam j)‖ ^ 2) (j : ι) :
    s.spectralPacket m hm j = s.v j * m (s.lam j) := rfl

theorem heatReachability_eq_spectralPacket_iff (hF : s.FullSupport) (m : ℂ → ℂ)
    (hm : Summable fun j => ‖s.v j * m (s.lam j)‖ ^ 2) (h : HalfLineL2) :
    s.heatReachability h = s.spectralPacket m hm ↔ ∀ j, laplaceRay h (s.lam j) = m (s.lam j) := by
  constructor
  · intro hh j
    have := congrArg (fun x : ℓ²ι => x j) hh
    simp only [heatReachability_apply_eq_laplace, spectralPacket_apply] at this
    exact mul_left_cancel₀ (hF j) this
  · intro hj
    refine lp.ext (funext fun j => ?_)
    rw [heatReachability_apply_eq_laplace, spectralPacket_apply, hj]

/-- **(HTF.9) The Hardy-trace formation law.**  `m(L)v ∈ Ran W` iff `m|_Λ` is the trace of an `H²`
function. -/
theorem spectralPacket_mem_range_iff (hF : s.FullSupport) (m : ℂ → ℂ)
    (hm : Summable fun j => ‖s.v j * m (s.lam j)‖ ^ 2) :
    s.spectralPacket m hm ∈ Set.range s.heatReachability ↔
      ∃ (H : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy H M ∧ ∀ j, H (s.lam j) = m (s.lam j) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨laplaceRay h, _, (paleyWiener_halfPlane.1 h).1,
      (s.heatReachability_eq_spectralPacket_iff hF m hm h).1 hh⟩
  · rintro ⟨H, M, hH, hint⟩
    obtain ⟨h, hHh, -⟩ := paleyWiener_halfPlane.2 H M hH
    refine ⟨h, (s.heatReachability_eq_spectralPacket_iff hF m hm h).2 fun j => ?_⟩
    rw [← hHh _ (by simpa using s.lam_pos j), hint]

omit [DecidableEq ι] in
theorem summable_expPacket {a : ℝ} (ha : 0 ≤ a) :
    Summable fun j => ‖s.v j * Complex.exp (-(a * s.lam j))‖ ^ 2 := by
  refine s.summable_norm_sq.of_nonneg_of_le (fun _ => by positivity) fun j => ?_
  rw [norm_mul, Complex.norm_exp]
  have hle : Real.exp (-(a * s.lam j : ℂ)).re ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [s.lam_pos j]
  calc (‖s.v j‖ * Real.exp (-(a * s.lam j : ℂ)).re) ^ 2 ≤ (‖s.v j‖ * 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) 2
    _ = ‖s.v j‖ ^ 2 := by ring

omit [DecidableEq ι] in
/-- **(HTF.18)** The exact-time heat packet `e^{-aL}v` is the spectral packet of `m_a(z) = e^{-az}`. -/
theorem heatOrbit_eq_spectralPacket {a : ℝ} (ha : 0 ≤ a) :
    s.heatOrbit a = s.spectralPacket (fun z => Complex.exp (-(a * z))) (s.summable_expPacket ha) := by
  refine lp.ext (funext fun j => ?_)
  rw [s.heatOrbit_apply, heatFactor_of_nonneg _ ha, spectralPacket_apply, mul_comm, Complex.ofReal_exp]
  push_cast
  rfl

/-- **(HTF.20)** The normalized time-window packet `x_{a,T} = T^{-1} ∫_a^{a+T} S_t v dt`. -/
def offsetWindowPacket (a T : ℝ) : ℓ²ι := ((T⁻¹ : ℝ) : ℂ) • ∫ t in Ioc a (a + T), s.heatOrbit t

/-- **(HTF.21)** `x_{a,T} = m_{a,T}(L) v`. -/
theorem offsetWindowPacket_apply {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) (j : ι) :
    s.offsetWindowPacket a T j = s.v j * offsetWindowMultiplier a T (s.lam j) := by
  have hint : IntegrableOn s.heatOrbit (Ioc a (a + T)) :=
    (s.continuous_heatOrbit.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h := integral_inner (𝕜 := ℂ) hint (lp.single 2 j (1 : ℂ))
  rw [inner_single_one_left] at h
  rw [offsetWindowPacket, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← h]
  have hpt : ∀ t ∈ Ioc a (a + T), ⟪(lp.single 2 j (1 : ℂ) : ℓ²ι), s.heatOrbit t⟫_ℂ =
      s.v j * expRay (s.lam j) t := fun t ht => by
    rw [inner_single_one_left, s.heatOrbit_apply, heatFactor_of_nonneg _ (ha.trans ht.1.le), mul_comm,
      expRay, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hl : ((s.lam j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (s.lam_pos j).ne'
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul, integral_Ioc_expRay a hT hl]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp

/-- **(HTF.21)** `x_{a,T} = W(T^{-1} 1_{(a,a+T]})`. -/
theorem offsetWindowPacket_eq {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) :
    s.offsetWindowPacket a T = s.heatReachability (offsetWindowControl a T) := by
  refine lp.ext (funext fun j => ?_)
  have hl : ((s.lam j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (s.lam_pos j).ne'
  rw [s.offsetWindowPacket_apply ha hT, heatReachability_apply_eq_laplace,
    laplaceRay_offsetWindowControl ha hT hl]

omit [DecidableEq ι] in
theorem spectralPacket_radialMultiplier_eq_zero {a : ℝ} (ha : a = 0)
    (hm : Summable fun j => ‖s.v j * radialMultiplier a (s.lam j)‖ ^ 2) :
    s.spectralPacket (radialMultiplier a) hm = 0 := by
  subst ha
  refine lp.ext (funext fun j => ?_)
  rw [spectralPacket_apply, radialMultiplier]
  simp

end HeatSource

/-! ## Half-plane Blaschke uniqueness -/

/-- **Half-plane Blaschke condition.**  A bounded holomorphic function on `Re w > δ` (`δ ≥ 0`) that
vanishes on a real sequence `λ_j > δ`, injective and tending to infinity, with
`Σ_j λ_j/(1+λ_j²) = ∞`, vanishes identically.  For `R ≥ δ` the zeros pulled back to the disk by
`z ↦ R + (1+z)/(1-z)` sit at `(λ_j - R - 1)/(λ_j - R + 1)` with `1 - |z_j| = 2/(λ_j - R + 1)`; a
nonzero value at `R + 1` would make these defects summable. -/
theorem eqOn_zero_of_bounded_of_blaschke_divergent {G : ℂ → ℂ} {δ C : ℝ} (hδ : 0 ≤ δ)
    (hG : DifferentiableOn ℂ G {w : ℂ | δ < w.re}) (hb : ∀ w : ℂ, δ < w.re → ‖G w‖ ≤ C)
    {κ : Type*} {Λ : κ → ℝ} (hinj : Function.Injective Λ) (htend : Tendsto Λ cofinite atTop)
    (hpos : ∀ j, δ < Λ j) (hzero : ∀ j, G (Λ j) = 0)
    (hdiv : ¬ Summable fun j => Λ j / (1 + Λ j ^ 2)) :
    ∀ w : ℂ, δ < w.re → G w = 0 := by
  have hopen : IsOpen {w : ℂ | δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticOnNhd ℂ G {w : ℂ | δ < w.re} := hG.analyticOnNhd hopen
  have hray : ∀ R : ℝ, δ ≤ R → G ((R : ℂ) + 1) = 0 := by
    intro R hR
    by_contra hne
    have hR0 : 0 ≤ R := hδ.trans hR
    set f : ℂ → ℂ := fun z => G ((R : ℂ) + RHTower.diskToRight z) with hfdef
    have hmaps : ∀ z ∈ ball (0 : ℂ) 1, δ < ((R : ℂ) + RHTower.diskToRight z).re := fun z hz => by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [RHTower.diskToRight_re_pos hz]
    have hf : AnalyticOnNhd ℂ f (ball 0 1) := fun z hz => by
      have hg : AnalyticAt ℂ (fun z => (R : ℂ) + RHTower.diskToRight z) z :=
        analyticAt_const.add (RHTower.diskToRight_analyticAt hz)
      exact (hana _ (hmaps z hz)).comp_of_eq hg rfl
    have hf0 : f 0 ≠ 0 := by
      simp only [hfdef, RHTower.diskToRight, add_zero, sub_zero, div_one]
      exact hne
    have hfb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ max C 1 := fun z hz =>
      (hb _ (hmaps z hz)).trans (le_max_left _ _)
    set u : {j : κ // R + 1 < Λ j} → ℂ := fun j => (((Λ j - R - 1) / (Λ j - R + 1) : ℝ) : ℂ) with hudef
    have hden : ∀ j : {j : κ // R + 1 < Λ j}, 0 < Λ j - R + 1 := fun j => by linarith [j.2]
    have hu_norm_eq : ∀ j : {j : κ // R + 1 < Λ j}, ‖u j‖ = (Λ j - R - 1) / (Λ j - R + 1) := fun j => by
      rw [hudef, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith [j.2]) (hden j).le)]
    have hu_norm : ∀ j, ‖u j‖ < 1 := fun j => by
      rw [hu_norm_eq, div_lt_one (hden j)]
      linarith
    have hu_zero : ∀ j, f (u j) = 0 := fun j => by
      have hb' : (Λ j - R + 1 : ℂ) ≠ 0 := by exact_mod_cast (hden j).ne'
      have hd : RHTower.diskToRight (u j) = ((Λ j - R : ℝ) : ℂ) := by
        rw [RHTower.diskToRight, hudef]
        push_cast
        have h1 : (1 : ℂ) - ((Λ j : ℂ) - R - 1) / ((Λ j : ℂ) - R + 1) ≠ 0 := by
          rw [one_sub_div hb']
          refine div_ne_zero ?_ hb'
          ring_nf
          norm_num
        field_simp
        ring
      simp only [hfdef, hd]
      push_cast
      rw [show (R : ℂ) + ((Λ j : ℂ) - R) = Λ j by ring]
      exact hzero j
    have hu_inj : Function.Injective u := fun a b hab => by
      have h1 : (Λ a - R - 1) / (Λ a - R + 1) = (Λ b - R - 1) / (Λ b - R + 1) :=
        Complex.ofReal_injective hab
      have ha := hden a
      have hb2 := hden b
      rw [div_eq_div_iff ha.ne' hb2.ne'] at h1
      exact Subtype.ext (hinj (by linarith))
    have hsum := RHTower.summable_one_sub_norm_of_bounded_analytic_zeros_openDisk (le_max_right C 1)
      hf hf0 hfb u hu_inj hu_norm hu_zero
    apply hdiv
    have hcompl : {j : κ | ¬ R + 1 < Λ j}.Finite := by
      have := htend.eventually (eventually_gt_atTop (R + 1))
      rw [Filter.eventually_cofinite] at this
      exact this
    rw [← summable_subtype_and_compl (s := {j : κ | R + 1 < Λ j})]
    refine ⟨hsum.of_nonneg_of_le (fun j => div_nonneg (by linarith [hpos j]) (by positivity))
      fun j => ?_, ?_⟩
    · have hj2 : R + 1 < Λ j := j.2
      have hΛ : 0 < Λ j := by linarith
      rw [hu_norm_eq, show 1 - (Λ j - R - 1) / (Λ j - R + 1) = 2 / (Λ j - R + 1) by
        field_simp [(hden j).ne']; ring]
      rw [div_le_div_iff₀ (by positivity) (hden j)]
      nlinarith [sq_nonneg (Λ j - 1)]
    · haveI : Finite ↥({j : κ | R + 1 < Λ j}ᶜ) := hcompl.to_subtype
      exact Summable.of_finite
  have hzero_ray : ∀ n : ℕ, G ((δ : ℂ) + 2 + (((n : ℝ) + 1)⁻¹ : ℝ)) = 0 := by
    intro n
    have h := hray (δ + 1 + ((n : ℝ) + 1)⁻¹) (by
      have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      linarith)
    convert h using 2
    push_cast
    ring
  have hfreq : ∃ᶠ w in 𝓝[≠] ((δ : ℂ) + 2), G w = 0 := by
    have htend' : Tendsto (fun n : ℕ => (δ : ℂ) + 2 + (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝[≠] ((δ : ℂ) + 2)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using (tendsto_const_nhds (x := (δ : ℂ) + 2)).add
          (Complex.continuous_ofReal.tendsto 0 |>.comp h0)
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
        exact Complex.ofReal_ne_zero.mpr (by positivity)
    exact htend'.frequently (Frequently.of_forall fun n => hzero_ray n)
  have hconn : IsPreconnected {w : ℂ | δ < w.re} := (convex_halfSpace_re_gt δ).isPreconnected
  have heq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn
    (by simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.re_ofNat]; linarith)
    hfreq
  exact fun w hw => heq hw

/-- **The Nevanlinna class** of the right half-plane: functions of bounded type, quotients
`G₁/G₂` of bounded holomorphic functions with zero-free denominator. -/
def IsHalfPlaneNevanlinna (F : ℂ → ℂ) : Prop :=
  ∃ G₁ G₂ : ℂ → ℂ, DifferentiableOn ℂ G₁ {w : ℂ | 0 < w.re} ∧
    DifferentiableOn ℂ G₂ {w : ℂ | 0 < w.re} ∧
    (∃ C, ∀ w : ℂ, 0 < w.re → ‖G₁ w‖ ≤ C) ∧ (∃ C, ∀ w : ℂ, 0 < w.re → ‖G₂ w‖ ≤ C) ∧
    (∀ w : ℂ, 0 < w.re → G₂ w ≠ 0) ∧ ∀ w : ℂ, 0 < w.re → F w = G₁ w / G₂ w

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

/-- **(HTF.10) The quotient-norm capital.**  `q_G(m(L)v) = inf {‖H‖²_{H²} : H|_Λ = m|_Λ}`, which is
`+∞` when no Hardy interpolant exists. -/
theorem orbitCostForm_spectralPacket (m : ℂ → ℂ) (hm : Summable fun j => ‖c.v j * m (c.lam j)‖ ^ 2) :
    c.orbitCostForm (c.spectralPacket m hm) =
      ⨅ (H : ℂ → ℂ) (_ : (∃ M, IsHalfPlaneHardy H M) ∧ ∀ j, H (c.lam j) = m (c.lam j)), hardyNormSq H := by
  rw [orbitCostForm_eq_iInf]
  refine le_antisymm (le_iInf₂ fun H ⟨⟨M, hH⟩, hint⟩ => ?_) (le_iInf₂ fun u hu => ?_)
  · obtain ⟨h, hHh, hnorm⟩ := paleyWiener_halfPlane.2 H M hH
    refine (iInf₂_le h ?_).trans hnorm.ge
    refine (c.heatReachability_eq_spectralPacket_iff c.fullSupport m hm h).2 fun j => ?_
    rw [← hHh _ (by simpa using c.lam_pos j), hint]
  · obtain ⟨hH, hnorm⟩ := paleyWiener_halfPlane.1 u
    refine (iInf₂_le (laplaceRay u) ⟨⟨_, hH⟩, ?_⟩).trans hnorm.le
    exact (c.heatReachability_eq_spectralPacket_iff c.fullSupport m hm u).1 hu

/-- **(HTF.10)** The quotient norm is attained: a packet of finite capital has a Hardy interpolant
of norm exactly `q_G(m(L)v)`. -/
theorem exists_hardy_interpolant_eq_orbitCostForm (m : ℂ → ℂ)
    (hm : Summable fun j => ‖c.v j * m (c.lam j)‖ ^ 2) (hq : c.orbitCostForm (c.spectralPacket m hm) < ⊤) :
    ∃ (H : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy H M ∧ (∀ j, H (c.lam j) = m (c.lam j)) ∧
      hardyNormSq H = c.orbitCostForm (c.spectralPacket m hm) := by
  obtain ⟨u, hu, hE⟩ := c.exists_minimalControl hq
  obtain ⟨hH, hnorm⟩ := paleyWiener_halfPlane.1 u
  exact ⟨laplaceRay u, _, hH, (c.heatReachability_eq_spectralPacket_iff c.fullSupport m hm u).1 hu,
    hnorm.trans hE⟩

/-- **(HTF.12)** The spectrum is an `H²` uniqueness set. -/
def IsHardyUniquenessSet : Prop :=
  ∀ (H : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy H M → (∀ j, H (c.lam j) = 0) → ∀ w : ℂ, 0 < w.re → H w = 0

/-- On an `H²` uniqueness set the reachability map is injective: every admitted packet has a unique
history. -/
theorem heatReachability_injective_of_uniqueness (hU : c.IsHardyUniquenessSet) :
    Function.Injective c.heatReachability := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  have hzero : ∀ j, laplaceRay h (c.lam j) = 0 := fun j => by
    have := congrArg (fun x : ℓ²ι => x j) hh
    simp only [HeatSource.heatReachability_apply_eq_laplace, lp.coeFn_zero, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (c.fullSupport j)
  have hL := hU _ _ (paleyWiener_halfPlane.1 h).1 hzero
  have hae := ae_eq_zero_of_laplaceRay_eq_zero (Lp.memLp h) hL
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae] with t ht
  rw [ht, Pi.zero_apply]

/-- **(HTF.13)** On an `H²` uniqueness set, `q_G(m(L)v) = ‖m‖²_{H²}` for `m ∈ H²`. -/
theorem orbitCostForm_spectralPacket_of_hardy (hU : c.IsHardyUniquenessSet) {m : ℂ → ℂ} {M : ℝ}
    (hmH : IsHalfPlaneHardy m M) (hm : Summable fun j => ‖c.v j * m (c.lam j)‖ ^ 2) :
    c.orbitCostForm (c.spectralPacket m hm) = hardyNormSq m := by
  obtain ⟨h, hmh, hnorm⟩ := paleyWiener_halfPlane.2 m M hmH
  have hWh : c.heatReachability h = c.spectralPacket m hm :=
    (c.heatReachability_eq_spectralPacket_iff c.fullSupport m hm h).2 fun j =>
      (hmh _ (by simpa using c.lam_pos j)).symm
  rw [orbitCostForm_eq_iInf, hnorm]
  refine le_antisymm (iInf₂_le h hWh) (le_iInf₂ fun u hu => ?_)
  rw [c.heatReachability_injective_of_uniqueness hU (hu.trans hWh.symm)]

/-- **(HTF.14)** If the spectrum violates the Blaschke condition, a Nevanlinna-class multiplier
outside `H²` has infinite capital: an `H²` interpolant `H` would make the bounded function
`H G₂ - G₁` vanish on the spectrum away from the boundary, forcing `H = m`. -/
theorem orbitCostForm_spectralPacket_eq_top_of_nevanlinna
    (hdiv : ¬ Summable fun j => c.lam j / (1 + c.lam j ^ 2)) {m : ℂ → ℂ}
    (hN : IsHalfPlaneNevanlinna m) (hnot : ¬ ∃ M, IsHalfPlaneHardy m M)
    (hm : Summable fun j => ‖c.v j * m (c.lam j)‖ ^ 2) :
    c.orbitCostForm (c.spectralPacket m hm) = ⊤ := by
  by_contra htop
  have hlt : c.orbitCostForm (c.spectralPacket m hm) < ⊤ := lt_top_iff_ne_top.2 htop
  have hmem : c.spectralPacket m hm ∈ Set.range c.heatReachability := by
    rw [(c.range_heatReachability).2]
    exact hlt
  obtain ⟨H, M, hH, hint⟩ := (c.spectralPacket_mem_range_iff c.fullSupport m hm).1 hmem
  obtain ⟨G₁, G₂, hG₁, hG₂, ⟨C₁, hC₁⟩, ⟨C₂, hC₂⟩, hne, hmG⟩ := hN
  set δ := c.gap / 2 with hδdef
  have hδ : 0 < δ := by have := c.gap_pos; positivity
  have hsub : {w : ℂ | δ < w.re} ⊆ {w : ℂ | 0 < w.re} := fun w hw => lt_trans hδ hw
  set B := rayL2Norm (hardyDatum H hH) / Real.sqrt (2 * δ)
  have hHb : ∀ w : ℂ, δ < w.re → ‖H w‖ ≤ B := fun w hw => by
    refine (norm_le_of_isHalfPlaneHardy hH (hδ.trans hw)).trans ?_
    exact div_le_div_of_nonneg_left (rayL2Norm_nonneg _) (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (by linarith))
  have hK := eqOn_zero_of_bounded_of_blaschke_divergent (G := fun w => H w * G₂ w - G₁ w)
    (C := B * C₂ + C₁) hδ.le
    (((hH.holo.mono hsub).mul (hG₂.mono hsub)).sub (hG₁.mono hsub))
    (fun w hw => by
      have hw0 : 0 < w.re := hδ.trans hw
      calc ‖H w * G₂ w - G₁ w‖ ≤ ‖H w‖ * ‖G₂ w‖ + ‖G₁ w‖ := by
            rw [← norm_mul]; exact norm_sub_le _ _
        _ ≤ B * C₂ + C₁ := by
            gcongr
            · exact (norm_nonneg _).trans (hHb w hw)
            · exact hHb w hw
            · exact hC₂ w hw0
            · exact hC₁ w hw0)
    c.simple c.proper (fun j => by have := c.gap_le j; have := c.gap_pos; linarith)
    (fun j => by
      have hj : (0 : ℝ) < ((c.lam j : ℝ) : ℂ).re := by simpa using c.lam_pos j
      rw [hint j, hmG _ hj, div_mul_cancel₀ _ (hne _ hj), sub_self])
    hdiv
  have hHm : ∀ w : ℂ, δ < w.re → H w = G₁ w / G₂ w := fun w hw => by
    have h := hK w hw
    rw [eq_div_iff (hne w (hδ.trans hw))]
    linear_combination h
  have hopen0 : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hanaH : AnalyticOnNhd ℂ H {w : ℂ | 0 < w.re} := hH.holo.analyticOnNhd hopen0
  have hanaQ : AnalyticOnNhd ℂ (fun w => G₁ w / G₂ w) {w : ℂ | 0 < w.re} :=
    (hG₁.div hG₂ fun w hw => hne w hw).analyticOnNhd hopen0
  have hev : H =ᶠ[𝓝 ((δ : ℂ) + 1)] fun w => G₁ w / G₂ w := by
    have hmem : {w : ℂ | δ < w.re} ∈ 𝓝 ((δ : ℂ) + 1) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with w hw
    exact hHm w hw
  have heqOn := hanaH.eqOn_of_preconnected_of_eventuallyEq hanaQ
    (convex_halfSpace_re_gt 0).isPreconnected (by simp; linarith) hev
  exact hnot ⟨M, hH.congr_right fun w hw => (heqOn hw).trans (hmG w hw).symm⟩

omit [DecidableEq ι] in
/-- An `H²` function tends to zero along a proper spectrum. -/
theorem tendsto_hardy_lam {H : ℂ → ℂ} {M : ℝ} (hH : IsHalfPlaneHardy H M) :
    Tendsto (fun j => H (c.lam j)) cofinite (𝓝 0) := by
  refine squeeze_zero_norm' (Eventually.of_forall fun j =>
    norm_le_of_isHalfPlaneHardy hH (by simpa using c.lam_pos j)) ?_
  have h2 : Tendsto (fun j => Real.sqrt (2 * c.lam j)) cofinite atTop :=
    Real.tendsto_sqrt_atTop.comp (c.proper.const_mul_atTop two_pos)
  simpa using (tendsto_const_nhds (x := rayL2Norm (hardyDatum H hH))).div_atTop h2

omit [DecidableEq ι] in
/-- A spectrum violating the half-plane Blaschke condition is an `H²` uniqueness set. -/
theorem isHardyUniquenessSet_of_not_summable
    (hdiv : ¬ Summable fun j => c.lam j / (1 + c.lam j ^ 2)) : c.IsHardyUniquenessSet := by
  intro H M hH hzero
  set δ := c.gap / 2 with hδdef
  have hδ : 0 < δ := by have := c.gap_pos; positivity
  have hsub : {w : ℂ | δ < w.re} ⊆ {w : ℂ | 0 < w.re} := fun w hw => lt_trans hδ hw
  have hK := eqOn_zero_of_bounded_of_blaschke_divergent hδ.le (hH.holo.mono hsub)
    (fun w hw => norm_le_of_isHalfPlaneHardy_of_lt hH hδ hw) c.simple c.proper
    (fun j => by have := c.gap_le j; have := c.gap_pos; linarith) hzero hdiv
  have hopen0 : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hanaH : AnalyticOnNhd ℂ H {w : ℂ | 0 < w.re} := hH.holo.analyticOnNhd hopen0
  have hev : H =ᶠ[𝓝 ((δ : ℂ) + 1)] 0 := by
    have hmem : {w : ℂ | δ < w.re} ∈ 𝓝 ((δ : ℂ) + 1) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with w hw
    exact hK w hw
  exact fun w hw => hanaH.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (by simp; linarith) hev hw

theorem orbitCostForm_zero : c.orbitCostForm 0 = 0 := by
  simp [orbitCostForm]

/-- **(HTF.24) The radial-defect selection wall.**  On an infinite proper spectrum, an admissible
radial packet `d_a(L)v` has finite capital exactly when `a = 0`: an `H²` interpolant tends to zero
along the spectrum by **(HTF.25)**, while `d_a(λ_j)` tends to `∞` (`a > 0`) or `-1` (`a < 0`). -/
theorem orbitCostForm_radialPacket_lt_top_iff [Infinite ι] (a : ℝ)
    (hm : Summable fun j => ‖c.v j * radialMultiplier a (c.lam j)‖ ^ 2) :
    c.orbitCostForm (c.spectralPacket (radialMultiplier a) hm) < ⊤ ↔ a = 0 := by
  constructor
  · intro hlt
    have hmem : c.spectralPacket (radialMultiplier a) hm ∈ Set.range c.heatReachability := by
      rw [(c.range_heatReachability).2]
      exact hlt
    obtain ⟨H, M, hH, hint⟩ := (c.spectralPacket_mem_range_iff c.fullSupport _ hm).1 hmem
    have ht : Tendsto (fun j => ((Real.exp (2 * a * c.lam j) - 1 : ℝ) : ℂ)) cofinite (𝓝 0) :=
      (c.tendsto_hardy_lam hH).congr fun j => by rw [hint j, radialMultiplier_ofReal]
    have hre : Tendsto (fun j => Real.exp (2 * a * c.lam j) - 1) cofinite (𝓝 0) := by
      have h := (Complex.continuous_re.tendsto 0).comp ht
      simp only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] at h
      exact h
    by_contra ha
    rcases lt_or_gt_of_ne ha with ha | ha
    · have hbot : Tendsto (fun j => 2 * a * c.lam j) cofinite atBot := by
        simpa [mul_assoc] using c.proper.const_mul_atTop_of_neg (by linarith : 2 * a < 0)
      have h1 : Tendsto (fun j => Real.exp (2 * a * c.lam j) - 1) cofinite (𝓝 (0 - 1)) :=
        (Real.tendsto_exp_atBot.comp hbot).sub_const 1
      have := tendsto_nhds_unique h1 hre
      norm_num at this
    · have htop : Tendsto (fun j => 2 * a * c.lam j) cofinite atTop := by
        simpa [mul_assoc] using c.proper.const_mul_atTop (by linarith : 0 < 2 * a)
      have h1 : Tendsto (fun j => Real.exp (2 * a * c.lam j) - 1) cofinite atTop :=
        tendsto_atTop_add_const_right _ (-1) (Real.tendsto_exp_atTop.comp htop)
      exact not_tendsto_nhds_of_tendsto_atTop h1 0 hre
  · intro ha
    rw [c.spectralPacket_radialMultiplier_eq_zero ha, orbitCostForm_zero]
    exact ENNReal.zero_lt_top

/-- **(HTF.24)** `q_G(d_0(L)v) = 0`. -/
theorem orbitCostForm_radialPacket_eq_zero {a : ℝ} (ha : a = 0)
    (hm : Summable fun j => ‖c.v j * radialMultiplier a (c.lam j)‖ ^ 2) :
    c.orbitCostForm (c.spectralPacket (radialMultiplier a) hm) = 0 := by
  rw [c.spectralPacket_radialMultiplier_eq_zero ha, orbitCostForm_zero]

/-- The positive defect of a rank-one projection is the capital of its vector:
`E_G(|x⟩⟨x|) = q_G(x)`. -/
theorem orbitDefectCost_rankOne (x : ℓ²ι) :
    c.orbitDefectCost (InnerProductSpace.rankOne ℂ x x) = c.orbitCostForm x := by
  rw [orbitDefectCost, orbitCostForm]
  refine tsum_congr fun k => ?_
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re]

end CyclicHeatSource

end GaloisForLFunctions.HTGeometry
