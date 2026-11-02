import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringCore

/-!
# Reflection Positivity, Modular Inversion Blindness, and Co-Isometry Defect on Lewis Period Functions

This module establishes the Hilbert-space and reflection-positivity structure on global Lewis
period functions of the Mayer operator:

1. **Modular Inversion Blindness (`I_s` at fixed `s`):** The Lewis modular inversion
   `(I_s ψ)(a) = a^(-2s) ψ(a⁻¹)` fixes every resonant global Lewis period function
   `resonantLewisPeriod s` and every Mayer scattering core `fieldCore (2s)` both on and off
   `Re s = 1/4`. Consequently, in any positive-semidefinite Hermitian space `(V, h)`, both
   `h(ψ_s, ψ_s) ≥ 0` and the `I_s`-induced Krein self-pairing `h(ψ_s, I_s ψ_s) = h(ψ_s, ψ_s) ≥ 0`
   are blind to `Re s = 1/4`; likewise, on the `s`-dependent Cauchy–Mellin space
   `L²((0, ∞), a^(2 Re s - 1) da)`, `I_s` is an exact norm isometry for every `s ∈ ℂ`.
2. **Canonical `s`-Independent Möbius–Critical Hilbert Space `H_LP`:** Equipped with the weight
   `lewisCriticalWeight a = (a + a⁻¹)^(-6) * a^(-1/2)` on `(0, ∞)`, every unsubtracted global
   Lewis period function across the entire open strip `0 < Re s < 1/2` (together with its
   Riemann–Mayer reflected image) is square-integrable, and every resonant Lewis period function
   has strictly positive norm.
3. **Hilbert Adjoint `I_s† = I_{1/2 - conj s}` and Strict Co-Isometry Negativity Off `Re s = 1/4`:**
   On `H_LP`, `⟨I_s f, g⟩_LP = ⟨f, I_{1/2 - conj s} g⟩_LP`, `I_s` is an isometry iff `s.re = 1/4`,
   and the co-isometry defect `lewisCoIsometryDefect s ψ = ‖ψ‖_LP² - ‖I_{1/2 - conj s} ψ‖_LP²` of
   every resonant Lewis period function `ψ_s = resonantLewisPeriod s` satisfies
   `lewisCoIsometryDefect s ψ_s = 0 ↔ s.re = 1/4` and
   `lewisCoIsometryDefect s ψ_s < 0 ↔ s.re ≠ 1/4`.
-/

open Complex Set Filter MeasureTheory Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringState
open MayerGlobalPeriods MayerScatteringCore

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ## Reciprocal change of variables on `(0, ∞)` and `(0, 1]` -/

private theorem hasDerivWithinAt_inv_Ioi {v : ℝ} (hv : 0 < v) :
    HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(v ^ 2)⁻¹) (Ioi 0) v :=
  (hasDerivAt_inv hv.ne').hasDerivWithinAt

theorem integral_Ioi_zero_inv_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    (∫ a in Ioi (0 : ℝ), g a) = ∫ b in Ioi (0 : ℝ), b ^ (-2 : ℝ) • g b⁻¹ := by
  have himg : (fun b : ℝ => b⁻¹) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi]
    exact ⟨fun ⟨b, hb, hbu⟩ => hbu ▸ inv_pos.mpr hb,
      fun hu => ⟨u⁻¹, inv_pos.mpr hu, inv_inv u⟩⟩
  have hinj : Set.InjOn (fun b : ℝ => b⁻¹) (Ioi 0) := fun _ _ _ _ h => inv_injective h
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi (fun b hb => hasDerivWithinAt_inv_Ioi hb) hinj g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := hb
  have habs : |-(b ^ 2)⁻¹| = b ^ (-2 : ℝ) := by
    rw [abs_neg, abs_of_pos (by positivity), Real.rpow_neg hb0.le, Real.rpow_two]
  change |-(b ^ 2)⁻¹| • g b⁻¹ = b ^ (-2 : ℝ) • g b⁻¹
  rw [habs]

private theorem integral_Ioc_zero_one_inv_subst (g : ℝ → ℝ) :
    (∫ a in Ioc (0 : ℝ) 1, g a) = ∫ b in Ioi (1 : ℝ), b ^ (-2 : ℝ) * g b⁻¹ := by
  have himg : (fun b : ℝ => b⁻¹) '' Ioi (1 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨b, hb1, rfl⟩
      have hb0 : 0 < b := zero_lt_one.trans hb1
      exact ⟨inv_pos.mpr hb0, inv_lt_one_of_one_lt₀ hb1⟩
    · rintro ⟨hu0, hu1⟩
      exact ⟨u⁻¹, one_lt_inv₀ hu0 |>.mpr hu1, inv_inv u⟩
  have hinj : Set.InjOn (fun b : ℝ => b⁻¹) (Ioi 1) := fun _ _ _ _ h => inv_injective h
  have hderiv : ∀ b ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(b ^ 2)⁻¹) (Ioi 1) b :=
    fun b hb => (hasDerivAt_inv (zero_lt_one.trans hb).ne').hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj g
  rw [himg] at h
  rw [← setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := zero_lt_one.trans hb
  have habs : |-(b ^ 2)⁻¹| = b ^ (-2 : ℝ) := by
    rw [abs_neg, abs_of_pos (by positivity), Real.rpow_neg hb0.le, Real.rpow_two]
  dsimp only [smul_eq_mul]
  rw [habs]

/-! ## Part A: Lewis modular inversion and blindness at fixed `s` -/

/-- The Lewis modular inversion `(I_s f)(a) = a^(-2s) f(a⁻¹)` on `(0, ∞)`. -/
def lewisModularInversion (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (a : ℂ) ^ (-(2 * s)) * f a⁻¹

theorem ofReal_inv_cpow_pos {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a⁻¹ : ℝ) : ℂ) ^ z = (a : ℂ) ^ (-z) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]

private theorem conj_ofReal_cpow_pos {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (starRingEnd ℂ) ((b : ℂ) ^ z) = (b : ℂ) ^ ((starRingEnd ℂ) z) := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  rw [Complex.cpow_def_of_ne_zero hbC, Complex.cpow_def_of_ne_zero hbC,
    ← Complex.ofReal_log hb.le, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem lewisModularInversion_involutive {s : ℂ} {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (lewisModularInversion s f) a = f a := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold lewisModularInversion
  rw [ofReal_inv_cpow_pos ha, inv_inv, ← mul_assoc, ← Complex.cpow_add _ _ haC]
  simp

/-- Every resonant global Lewis period function (on OR off `Re s = 1/4`) is pointwise fixed by
`lewisModularInversion s` on `(0, ∞)`. -/
theorem lewisModularInversion_resonantLewisPeriod {s : ℂ} (hs : IsMayerScatteringResonance s)
    {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (fun x : ℝ => resonantLewisPeriod s x) a = resonantLewisPeriod s a := by
  dsimp only [lewisModularInversion]
  have hrec := resonantLewisPeriod_reciprocity hs (a := (a : ℂ)) (by simpa using ha)
  rw [Complex.ofReal_inv]
  exact hrec.symm

/-- Every Mayer scattering core `fieldCore (2s)` (`Re s > 0`, `Im s > 0`, on OR off `Re s = 1/4`)
is pointwise fixed by `lewisModularInversion s` on `(0, ∞)`. -/
theorem lewisModularInversion_fieldCore {s : ℂ} (h0 : 0 < s.re) (him : 0 < s.im)
    {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (fieldCore (2 * s)) a = fieldCore (2 * s) a := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hwim : 0 < (2 * s).im := by simp; linarith
  have hrec := fieldCore_reciprocity hw0 hwim ha
  unfold lewisModularInversion
  simpa only [one_div] using hrec.symm

/-- **Modular Inversion Blindness (Abstract Form).** In any type `V` equipped with a pairing
`h : V → V → ℂ` with nonnegative self-pairings `0 ≤ (h v v).re` and any operator `T : V → V`,
every `+1` fixed vector `T v = v` has nonnegative `T`-induced Krein self-pairing
`0 ≤ (h v (T v)).re` (strictly positive if `(h v v).re > 0`). Hence no positive-definite pairing
combined with `I_s` at fixed `s` can assign a negative self-pairing to a `+1` resonant period
function off `Re s = 1/4`. -/
theorem fixed_vector_krein_self_pairing_nonneg {V : Type*} (h : V → V → ℂ)
    (h_nonneg : ∀ v : V, 0 ≤ (h v v).re) (T : V → V) {v : V} (hv : T v = v) :
    (h v (T v)).re = (h v v).re ∧ 0 ≤ (h v (T v)).re := by
  rw [hv]
  exact ⟨rfl, h_nonneg v⟩

/-- **Modular Inversion Blindness on the `s`-Dependent Cauchy–Mellin Space.** For EVERY `s ∈ ℂ`
(whether `Re s = 1/4` or `Re s ≠ 1/4`), `lewisModularInversion s` is an exact norm isometry of
`L²((0, ∞), a^(2 Re s - 1) da)`. -/
theorem cauchyMellinWeight_isometry (s : ℂ) (f : ℝ → ℂ) :
    (∫ a in Ioi (0 : ℝ), a ^ (2 * s.re - 1) * ‖lewisModularInversion s f a‖ ^ 2) =
      ∫ b in Ioi (0 : ℝ), b ^ (2 * s.re - 1) * ‖f b‖ ^ 2 := by
  rw [integral_Ioi_zero_inv_subst]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := hb
  have hb_inv : 0 < b⁻¹ := inv_pos.mpr hb0
  dsimp only [smul_eq_mul, lewisModularInversion]
  rw [inv_inv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb_inv,
    Real.inv_rpow hb0.le, Real.inv_rpow hb0.le, mul_pow]
  have hre : (-(2 * s)).re = -2 * s.re := by simp
  rw [hre]
  have hrpow1 : (b ^ (2 * s.re - 1))⁻¹ = b ^ (1 - 2 * s.re) := by
    rw [← Real.rpow_neg hb0.le, show -(2 * s.re - 1) = 1 - 2 * s.re by ring]
  have hrpow2 : ((b ^ (-2 * s.re))⁻¹) ^ (2 : ℕ) = b ^ (4 * s.re) := by
    rw [← Real.rpow_neg hb0.le, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    congr 1
    push_cast
    ring
  rw [hrpow1, hrpow2]
  have hcomb : b ^ (-2 : ℝ) * (b ^ (1 - 2 * s.re) * (b ^ (4 * s.re) * ‖f b‖ ^ 2)) =
      (b ^ (-2 : ℝ) * b ^ (1 - 2 * s.re) * b ^ (4 * s.re)) * ‖f b‖ ^ 2 := by ring
  rw [hcomb, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
  congr 2
  ring

/-! ## Part B: Canonical `s`-independent Möbius–critical Hilbert space `H_LP` -/

/-- The canonical `s`-independent Möbius–critical weight `(a + a⁻¹)^(-6) * a^(-1/2)` on `(0, ∞)`. -/
def lewisCriticalWeight (a : ℝ) : ℝ :=
  (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))

theorem lewisCriticalWeight_pos {a : ℝ} (ha : 0 < a) : 0 < lewisCriticalWeight a := by
  unfold lewisCriticalWeight
  have hsum : 0 < a + a⁻¹ := add_pos ha (inv_pos.mpr ha)
  exact mul_pos (Real.rpow_pos_of_pos hsum _) (Real.rpow_pos_of_pos ha _)

theorem lewisCriticalWeight_continuousOn : ContinuousOn lewisCriticalWeight (Ioi 0) := by
  intro a ha
  have ha0 : 0 < a := ha
  have hsum : a + a⁻¹ ≠ 0 := (add_pos ha0 (inv_pos.mpr ha0)).ne'
  unfold lewisCriticalWeight
  exact (((continuousAt_id.add (continuousAt_inv₀ ha0.ne')).rpow continuousAt_const
    (Or.inl hsum)).mul (continuousAt_id.rpow continuousAt_const (Or.inl ha0.ne'))).continuousWithinAt

private theorem lewisCriticalWeight_inv_mul_jac {b : ℝ} (hb : 0 < b) :
    b ^ (-2 : ℝ) * lewisCriticalWeight b⁻¹ = b ^ (-1 : ℝ) * lewisCriticalWeight b := by
  unfold lewisCriticalWeight
  rw [inv_inv, add_comm b⁻¹ b, Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, neg_neg]
  have h1 : b ^ (-2 : ℝ) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (1 / 2 : ℝ)) =
      (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (-2 : ℝ) * b ^ (1 / 2 : ℝ)) := by ring
  have h2 : b ^ (-1 : ℝ) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))) =
      (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (-1 : ℝ) * b ^ (-(1 / 2 : ℝ))) := by ring
  rw [h1, h2, ← Real.rpow_add hb, ← Real.rpow_add hb]
  congr 2
  norm_num

/-- Positive-definite `s`-independent Hermitian inner product on functions on `(0, ∞)`. -/
def lewisCriticalInner (f g : ℝ → ℂ) : ℂ :=
  ∫ a in Ioi (0 : ℝ), f a * (starRingEnd ℂ) (g a) * (lewisCriticalWeight a : ℂ)

/-- Squared norm on `H_LP`. -/
def lewisCriticalNormSq (f : ℝ → ℂ) : ℝ :=
  ∫ a in Ioi (0 : ℝ), ‖f a‖ ^ 2 * lewisCriticalWeight a

theorem lewisCriticalInner_self_eq_ofReal_normSq (f : ℝ → ℂ) :
    lewisCriticalInner f f = (lewisCriticalNormSq f : ℂ) := by
  unfold lewisCriticalInner lewisCriticalNormSq
  calc
    (∫ a in Ioi (0 : ℝ), f a * (starRingEnd ℂ) (f a) * (lewisCriticalWeight a : ℂ)) =
        ∫ a in Ioi (0 : ℝ), ((‖f a‖ ^ 2 * lewisCriticalWeight a : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
      rw [Complex.mul_conj', Complex.ofReal_mul, Complex.ofReal_pow]
    _ = ((∫ a in Ioi (0 : ℝ), ‖f a‖ ^ 2 * lewisCriticalWeight a : ℝ) : ℂ) := integral_ofReal

theorem lewisCriticalNormSq_nonneg (f : ℝ → ℂ) : 0 ≤ lewisCriticalNormSq f := by
  unfold lewisCriticalNormSq
  refine setIntegral_nonneg measurableSet_Ioi fun a ha => ?_
  exact mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos ha).le

/-- Positive-definiteness on continuous functions: a continuous function on `(0, ∞)` with
vanishing `lewisCriticalNormSq` (when integrable) vanishes identically on `(0, ∞)`. -/
theorem eq_zero_on_Ioi_of_lewisCriticalNormSq_eq_zero {f : ℝ → ℂ}
    (hf_cont : ContinuousOn f (Ioi 0))
    (hf_int : IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0))
    (hzero : lewisCriticalNormSq f = 0) :
    ∀ a > 0, f a = 0 := by
  intro a₀ ha₀
  by_contra hne
  have hc0 : 0 < ‖f a₀‖ := norm_pos_iff.mpr hne
  have hnorm_cont : ContinuousAt (fun x : ℝ => ‖f x‖) a₀ :=
    (hf_cont.continuousAt (isOpen_Ioi.mem_nhds ha₀)).norm
  obtain ⟨r, hr_pos, hball⟩ := Metric.continuousAt_iff.mp hnorm_cont (‖f a₀‖ / 2) (half_pos hc0)
  let p : ℝ := max (a₀ / 2) (a₀ - r / 2)
  let q : ℝ := a₀ + r / 2
  have hp_pos : 0 < p := lt_max_of_lt_left (half_pos ha₀)
  have hp_lt_a₀ : p < a₀ := max_lt (half_lt_self ha₀) (by linarith)
  have hp_lt_q : p < q := by dsimp [q]; linarith
  have hw_min : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Ioc p q, m ≤ ‖f x‖ ^ 2 * lewisCriticalWeight x := by
    let g : ℝ → ℝ := fun x => (‖f a₀‖ / 2) ^ 2 * lewisCriticalWeight x
    have hg_cont : ContinuousOn g (Icc p q) :=
      (lewisCriticalWeight_continuousOn.mono (fun x hx => lt_of_lt_of_le hp_pos hx.1)).const_mul _
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hp_lt_q.le) hg_cont
    refine ⟨g x₀, mul_pos (sq_pos_of_pos (half_pos hc0))
      (lewisCriticalWeight_pos (lt_of_lt_of_le hp_pos hx₀.1)), fun x hx => ?_⟩
    have hx_dist : dist x a₀ < r := by
      rw [Real.dist_eq, abs_lt]
      have hp2 : a₀ - r / 2 ≤ p := le_max_right _ _
      have hx_le : x ≤ a₀ + r / 2 := hx.2
      exact ⟨by linarith [hx.1], by linarith⟩
    have hfx : ‖f a₀‖ / 2 ≤ ‖f x‖ := by
      have hb := abs_lt.mp (by simpa [Real.dist_eq] using hball hx_dist)
      linarith
    have hsq : (‖f a₀‖ / 2) ^ 2 ≤ ‖f x‖ ^ 2 :=
      pow_le_pow_left₀ (half_pos hc0).le hfx 2
    exact le_trans (hmin ⟨hx.1.le, hx.2⟩)
      (mul_le_mul_of_nonneg_right hsq (lewisCriticalWeight_pos (hp_pos.trans hx.1)).le)
  obtain ⟨m, hm_pos, hm_le⟩ := hw_min
  have hsub : Ioc p q ⊆ Ioi 0 := fun x hx => hp_pos.trans hx.1
  have hunion : Ioi (0 : ℝ) = Ioc p q ∪ (Ioi 0 \ Ioc p q) := (Set.union_sdiff_cancel hsub).symm
  have hdisj : Disjoint (Ioc p q) (Ioi 0 \ Ioc p q) := disjoint_sdiff_self_right
  have hsplit : lewisCriticalNormSq f =
      (∫ x in Ioc p q, ‖f x‖ ^ 2 * lewisCriticalWeight x) +
        ∫ x in Ioi 0 \ Ioc p q, ‖f x‖ ^ 2 * lewisCriticalWeight x := by
    unfold lewisCriticalNormSq
    conv_lhs => rw [hunion]
    exact setIntegral_union hdisj (measurableSet_Ioi.diff measurableSet_Ioc)
      (hf_int.mono_set hsub) (hf_int.mono_set Set.sdiff_subset)
  have hrest_nn : 0 ≤ ∫ x in Ioi 0 \ Ioc p q, ‖f x‖ ^ 2 * lewisCriticalWeight x :=
    setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioc) fun x hx =>
      mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hx.1).le
  have hm_le_int : (q - p) * m ≤ ∫ x in Ioc p q, ‖f x‖ ^ 2 * lewisCriticalWeight x := by
    have hconst : (∫ _ in Ioc p q, m) = (q - p) * m := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hp_lt_q.le, smul_eq_mul]
    rw [← hconst]
    exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      (hf_int.mono_set hsub) measurableSet_Ioc hm_le
  have hpos_prod : 0 < (q - p) * m := mul_pos (sub_pos.mpr hp_lt_q) hm_pos
  linarith

/-! ## Global Lewis period functions belong to `H_LP` across `0 < Re s < 1/2` -/

theorem period_real_continuousOn {w : ℂ} (hw : 0 < w.re) (ε c : ℂ) (f : DiscSpace) :
    ContinuousOn (fun a : ℝ => period w ε c f a) (Ioi 0) := by
  have hdom_open : IsOpen MayerGlobalPeriods.domain :=
    isOpen_lt continuous_const Complex.continuous_re
  intro a ha
  have ha0 : 0 < a := ha
  have hd : (a : ℂ) - 1 ∈ MayerGlobalPeriods.domain := by
    change -1 < ((a : ℂ) - 1).re
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hh := (extension_differentiableOn hw ε c f).differentiableAt (hdom_open.mem_nhds hd)
  have hcomp : ContinuousAt (fun x : ℝ => period w ε c f x) a := by
    change ContinuousAt (fun x : ℝ => extension w ε c f ((x : ℂ) - 1)) a
    exact ContinuousAt.comp hh.continuousAt
      (show ContinuousAt (fun x : ℝ => (x : ℂ) - 1) a by fun_prop)
  exact hcomp.continuousWithinAt

/-- Linear growth bound `‖period w ε c f b‖ ≤ M * b` on `[1, ∞)` deduced directly from
`period_shift` and compactness of `[1, 2]`. -/
theorem exists_period_linear_bound_Ici_one {w ε c : ℂ} (hw : 0 < w.re) (hε : ε ^ 2 = 1)
    (f : DiscSpace) (hf : regularized w hw f = ε • f + constant c) :
    ∃ M : ℝ, 0 < M ∧ ∀ b : ℝ, 1 ≤ b → ‖period w ε c f b‖ ≤ M * b := by
  let ψ : ℝ → ℂ := fun a => period w ε c f a
  have hcont : ContinuousOn (fun x : ℝ => ‖ψ x‖) (Icc 1 2) :=
    ((period_real_continuousOn hw ε c f).mono (fun x hx => zero_lt_one.trans_le hx.1)).norm
  obtain ⟨x₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (by norm_num : (Icc (1 : ℝ) 2).Nonempty) hcont
  let M : ℝ := max ‖ψ x₀‖ 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM_Icc : ∀ x ∈ Icc (1 : ℝ) 2, ‖ψ x‖ ≤ M := fun x hx =>
    le_trans (hmax hx) (le_max_left _ _)
  have hnorm_ε : ‖ε‖ = 1 := by
    have hsq : ‖ε‖ ^ 2 = 1 := by rw [← norm_pow, hε, norm_one]
    nlinarith [norm_nonneg ε]
  have hstep : ∀ u : ℝ, 1 ≤ u → ‖ψ (u + 1)‖ ≤ ‖ψ u‖ + M := by
    intro u hu
    have hu_pos : 0 < u := zero_lt_one.trans_le hu
    have hsh := period_shift hw hε f hf (a := (u : ℂ)) (by simpa using hu_pos)
    have hcast1 : ((u : ℂ) + 1) = ((u + 1 : ℝ) : ℂ) := by push_cast; ring
    have hcast2 : (1 + (u : ℂ)⁻¹) = ((1 + u⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast1, hcast2] at hsh
    have heq : ψ (u + 1) = ψ u - ε * (u : ℂ) ^ (-w) * ψ (1 + u⁻¹) := by
      dsimp [ψ]
      linear_combination -hsh
    have hu_pow : ‖(u : ℂ) ^ (-w)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
    have hinv_mem : 1 + u⁻¹ ∈ Icc (1 : ℝ) 2 :=
      ⟨by linarith [inv_pos.mpr hu_pos], by linarith [inv_le_one_of_one_le₀ hu]⟩
    calc
      ‖ψ (u + 1)‖ = ‖ψ u - ε * (u : ℂ) ^ (-w) * ψ (1 + u⁻¹)‖ := congrArg norm heq
      _ ≤ ‖ψ u‖ + ‖ε * (u : ℂ) ^ (-w) * ψ (1 + u⁻¹)‖ := norm_sub_le _ _
      _ = ‖ψ u‖ + ‖ε‖ * ‖(u : ℂ) ^ (-w)‖ * ‖ψ (1 + u⁻¹)‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖ψ u‖ + 1 * 1 * M := by
        rw [hnorm_ε]
        have hprod : 1 * ‖(u : ℂ) ^ (-w)‖ * ‖ψ (1 + u⁻¹)‖ ≤ 1 * 1 * M := by
          simpa only [one_mul] using
            mul_le_mul hu_pow (hM_Icc _ hinv_mem) (norm_nonneg _) zero_le_one
        linarith
      _ = ‖ψ u‖ + M := by ring
  have hind : ∀ (n : ℕ) {t : ℝ}, t ∈ Icc (1 : ℝ) 2 → ‖ψ (t + n)‖ ≤ ((n : ℝ) + 1) * M := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa using hM_Icc t ht
    | succ n ih =>
      intro t ht
      have htn1 : 1 ≤ t + (n : ℝ) := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith [ht.1]
      have hrew : t + ((n + 1 : ℕ) : ℝ) = (t + (n : ℝ)) + 1 := by push_cast; ring
      rw [hrew]
      calc
        ‖ψ ((t + n) + 1)‖ ≤ ‖ψ (t + n)‖ + M := hstep (t + n) htn1
        _ ≤ ((n : ℝ) + 1) * M + M := by linarith [ih ht]
        _ = (((n + 1 : ℕ) : ℝ) + 1) * M := by push_cast; ring
  refine ⟨M, hM_pos, fun b hb => ?_⟩
  let n : ℕ := ⌊b - 1⌋₊
  let t : ℝ := b - n
  have hb0 : 0 ≤ b - 1 := sub_nonneg.mpr hb
  have hn_le : (n : ℝ) ≤ b - 1 := Nat.floor_le hb0
  have hn_lt : b - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (b - 1)
  have ht_mem : t ∈ Icc (1 : ℝ) 2 := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  have htb : t + (n : ℝ) = b := sub_add_cancel b n
  calc
    ‖ψ b‖ = ‖ψ (t + n)‖ := by rw [htb]
    _ ≤ ((n : ℝ) + 1) * M := hind n ht_mem
    _ ≤ ((b - 1) + 1) * M := mul_le_mul_of_nonneg_right (by linarith) hM_pos.le
    _ = M * b := by ring

private theorem weight_le_Ioc {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    (a + a⁻¹) ^ (-6 : ℝ) ≤ a ^ (6 : ℝ) := by
  have ha_inv_pos : 0 < a⁻¹ := inv_pos.mpr ha.1
  have hle : a⁻¹ ≤ a + a⁻¹ := by linarith [ha.1]
  calc
    (a + a⁻¹) ^ (-6 : ℝ) ≤ (a⁻¹) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha_inv_pos hle (by norm_num)
    _ = a ^ (6 : ℝ) := by
      rw [Real.inv_rpow ha.1.le, ← Real.rpow_neg ha.1.le]
      norm_num

private theorem weight_le_Ioi {b : ℝ} (hb : b ∈ Ioi (1 : ℝ)) :
    (b + b⁻¹) ^ (-6 : ℝ) ≤ b ^ (-6 : ℝ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hle : b ≤ b + b⁻¹ := by linarith [inv_pos.mpr hb0]
  exact Real.rpow_le_rpow_of_nonpos hb0 hle (by norm_num)

/-- Every global Lewis period function satisfies `(b + b⁻¹)^(-6) b^β ‖ψ b‖² ∈ L¹(1, ∞)` for all
`β < 3`. -/
theorem globalLewisPeriod_rpow_integrableOn_Ioi_one {w ε c : ℂ} (hw : 0 < w.re)
    (hε : ε ^ 2 = 1) (f : DiscSpace) (hf : regularized w hw f = ε • f + constant c)
    {β : ℝ} (hβ : β < 3) :
    IntegrableOn
      (fun b : ℝ => ‖period w ε c f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β))
      (Ioi 1) := by
  obtain ⟨M, hM_pos, hM⟩ := exists_period_linear_bound_Ici_one hw hε f hf
  have hdom : IntegrableOn (fun b : ℝ => M ^ 2 * b ^ (β - 4)) (Ioi 1) :=
    ((integrableOn_Ioi_rpow_iff zero_lt_one).2 (by linarith)).const_mul (M ^ 2)
  have hcont : ContinuousOn
      (fun b : ℝ => ‖period w ε c f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β)) (Ioi 1) := by
    intro b hb
    have hb0 : 0 < b := zero_lt_one.trans hb
    have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
    have hψ : ContinuousAt (fun x : ℝ => ‖period w ε c f x‖ ^ 2) b :=
      ((period_real_continuousOn hw ε c f).continuousAt
        (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hb0))).norm.pow 2
    have hw1 : ContinuousAt (fun x : ℝ => (x + x⁻¹) ^ (-6 : ℝ)) b :=
      (continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (-6 : ℝ)) b) (Or.inl hsum)
    have hw2 : ContinuousAt (fun x : ℝ => x ^ β) b :=
      continuousAt_id.rpow
        (continuousAt_const : ContinuousAt (fun _ : ℝ => β) b) (Or.inl hb0.ne')
    exact (hψ.mul (hw1.mul hw2)).continuousWithinAt
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
  have hb1 : 1 ≤ b := le_of_lt hb
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hψ_sq : ‖period w ε c f b‖ ^ 2 ≤ M ^ 2 * b ^ (2 : ℝ) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hM b hb1) 2
    rw [mul_pow, ← Real.rpow_natCast b 2] at h1
    simpa using h1
  have hw_sq : (b + b⁻¹) ^ (-6 : ℝ) * b ^ β ≤ b ^ (-6 : ℝ) * b ^ β :=
    mul_le_mul_of_nonneg_right (weight_le_Ioi hb) (Real.rpow_pos_of_pos hb0 β).le
  have hnn : 0 ≤ ‖period w ε c f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β) :=
    mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
        (Real.rpow_pos_of_pos hb0 _).le)
  rw [Real.norm_of_nonneg hnn]
  calc
    ‖period w ε c f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β)
        ≤ (M ^ 2 * b ^ (2 : ℝ)) * (b ^ (-6 : ℝ) * b ^ β) :=
      mul_le_mul hψ_sq hw_sq
        (mul_nonneg (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
          (Real.rpow_pos_of_pos hb0 _).le)
        (mul_nonneg (sq_nonneg M) (Real.rpow_pos_of_pos hb0 _).le)
    _ = M ^ 2 * (b ^ (2 : ℝ) * b ^ (-6 : ℝ) * b ^ β) := by ring
    _ = M ^ 2 * b ^ (β - 4) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]
      congr 2
      ring

/-- **Global `H_LP` Membership Across the Strip.** For every `0 < Re s < 1/2` (`w = 2s`), every
sign `ε^2 = 1`, and every `f ∈ DiscSpace` satisfying `regularized (2s) hw f = ε • f + constant c`,
both `period (2s) ε c f` and its Riemann–Mayer reflected partner `I_{1/2 - conj s}(period (2s) ε c f)`
have finite `H_LP`-norm on `(0, ∞)`. -/
theorem globalLewisPeriod_integrable_lewisCriticalNormSq {s ε c : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (hε : ε ^ 2 = 1) (f : DiscSpace)
    (hf : regularized (2 * s) (by simp; linarith) f = ε • f + constant c) :
    IntegrableOn (fun a : ℝ => ‖period (2 * s) ε c f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
      IntegrableOn (fun a : ℝ =>
        ‖lewisModularInversion (riemannMayerReflect s) (fun x => period (2 * s) ε c f x) a‖ ^ 2 *
          lewisCriticalWeight a) (Ioi 0) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s).re < 1 := by simp; linarith
  obtain ⟨M, hM_pos, hM⟩ := exists_period_linear_bound_Ici_one hw0 hε f hf
  have hnorm_ε : ‖ε‖ = 1 := by
    have hsq : ‖ε‖ ^ 2 = 1 := by rw [← norm_pow, hε, norm_one]
    nlinarith [norm_nonneg ε]
  have hnear_bound : ∀ a ∈ Ioc (0 : ℝ) 1,
      ‖period (2 * s) ε c f a‖ ≤ M * a ^ (-(2 * s).re - 1) := by
    intro a ha
    have ha_inv_ge : 1 ≤ a⁻¹ := (one_le_inv₀ ha.1).mpr ha.2
    have hrec := MayerGlobalPeriods.reciprocity hw0 hε f hf (a := (a : ℂ)) (by simpa using ha.1)
    rw [← Complex.ofReal_inv] at hrec
    calc
      ‖period (2 * s) ε c f a‖
          = ‖ε‖ * ‖(a : ℂ) ^ (-(2 * s))‖ * ‖period (2 * s) ε c f (a⁻¹ : ℝ)‖ := by
        rw [hrec, norm_mul, norm_mul]
      _ ≤ 1 * a ^ (-(2 * s).re) * (M * a⁻¹) := by
        rw [hnorm_ε, Complex.norm_cpow_eq_rpow_re_of_pos ha.1, Complex.neg_re, one_mul]
        exact mul_le_mul_of_nonneg_left (hM a⁻¹ ha_inv_ge) (Real.rpow_pos_of_pos ha.1 _).le
      _ = M * (a ^ (-(2 * s).re) * a ^ (-1 : ℝ)) := by
        rw [← Real.rpow_neg_one a]
        ring
      _ = M * a ^ (-(2 * s).re - 1) := by
        rw [← Real.rpow_add ha.1, ← sub_eq_add_neg]
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  constructor
  · rw [hunion]
    apply IntegrableOn.union
    · have hcont : ContinuousOn
          (fun a : ℝ => ‖period (2 * s) ε c f a‖ ^ 2 * lewisCriticalWeight a) (Ioc 0 1) :=
        (((period_real_continuousOn hw0 ε c f).norm.pow 2).mul lewisCriticalWeight_continuousOn).mono
          Ioc_subset_Ioi_self
      refine (integrableOn_const (C := M ^ 2) (hs := measure_Ioc_lt_top.ne)).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have hnn : 0 ≤ ‖period (2 * s) ε c f a‖ ^ 2 * lewisCriticalWeight a :=
        mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos ha.1).le
      rw [Real.norm_of_nonneg hnn]
      have hψ_sq : ‖period (2 * s) ε c f a‖ ^ 2 ≤ M ^ 2 * a ^ (-2 * (2 * s).re - 2) := by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) (hnear_bound a ha) 2
        rw [mul_pow, ← Real.rpow_natCast (a ^ (-(2 * s).re - 1)) 2, ← Real.rpow_mul ha.1.le] at h1
        have hexp : (-(2 * s).re - 1) * ((2 : ℕ) : ℝ) = -2 * (2 * s).re - 2 := by
          push_cast
          ring
        rwa [hexp] at h1
      have hw_le : lewisCriticalWeight a ≤ a ^ (11 / 2 : ℝ) := by
        unfold lewisCriticalWeight
        calc
          (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))
              ≤ a ^ (6 : ℝ) * a ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (weight_le_Ioc ha) (Real.rpow_pos_of_pos ha.1 _).le
          _ = a ^ (11 / 2 : ℝ) := by rw [← Real.rpow_add ha.1]; norm_num
      calc
        ‖period (2 * s) ε c f a‖ ^ 2 * lewisCriticalWeight a
            ≤ (M ^ 2 * a ^ (-2 * (2 * s).re - 2)) * a ^ (11 / 2 : ℝ) :=
          mul_le_mul hψ_sq hw_le (lewisCriticalWeight_pos ha.1).le
            (mul_nonneg (sq_nonneg M) (Real.rpow_pos_of_pos ha.1 _).le)
        _ = M ^ 2 * a ^ (7 / 2 - 2 * (2 * s).re) := by
          rw [mul_assoc, ← Real.rpow_add ha.1]
          congr 2
          ring
        _ ≤ M ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one ha.1.le ha.2 (by linarith)) (sq_nonneg M)
        _ = M ^ 2 := mul_one _
    · simpa only [lewisCriticalWeight] using
        globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 hε f hf (β := -(1 / 2 : ℝ)) (by norm_num)
  · rw [hunion]
    have hcontR : ContinuousOn
        (fun a : ℝ =>
          ‖lewisModularInversion (riemannMayerReflect s) (fun x => period (2 * s) ε c f x) a‖ ^ 2 *
            lewisCriticalWeight a) (Ioi 0) := by
      intro a ha
      have ha0 : 0 < a := ha
      have hpow : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-(2 * riemannMayerReflect s))) a :=
        Complex.continuousAt_ofReal_cpow_const a _ (Or.inr ha0.ne')
      have hψinv : ContinuousAt (fun x : ℝ => period (2 * s) ε c f (x⁻¹ : ℝ)) a :=
        ContinuousAt.comp (g := fun u : ℝ => period (2 * s) ε c f u)
          ((period_real_continuousOn hw0 ε c f).continuousAt
            (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (inv_pos.mpr ha0))))
          (continuousAt_inv₀ ha0.ne')
      have htot : ContinuousAt
          (fun x : ℝ =>
            ‖lewisModularInversion (riemannMayerReflect s) (fun u => period (2 * s) ε c f u) x‖ ^ 2 *
              lewisCriticalWeight x) a := by
        unfold lewisModularInversion
        exact ((hpow.mul hψinv).norm.pow 2).mul
          (lewisCriticalWeight_continuousOn.continuousAt
            (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ha0)))
      exact htot.continuousWithinAt
    have hre_ref : (-(2 * riemannMayerReflect s)).re = (2 * s).re - 1 := by
      simp [riemannMayerReflect]
      ring
    apply IntegrableOn.union
    · refine (integrableOn_const (C := M ^ 2) (hs := measure_Ioc_lt_top.ne)).mono'
        ((hcontR.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have hnn : 0 ≤
          ‖lewisModularInversion (riemannMayerReflect s) (fun x => period (2 * s) ε c f x) a‖ ^ 2 *
            lewisCriticalWeight a :=
        mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos ha.1).le
      rw [Real.norm_of_nonneg hnn]
      have ha_inv_ge : 1 ≤ a⁻¹ := (one_le_inv₀ ha.1).mpr ha.2
      have hR_le : ‖lewisModularInversion (riemannMayerReflect s)
          (fun x => period (2 * s) ε c f x) a‖ ≤ M * a ^ ((2 * s).re - 2) := by
        dsimp only [lewisModularInversion]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha.1, hre_ref]
        calc
          a ^ ((2 * s).re - 1) * ‖period (2 * s) ε c f (a⁻¹ : ℝ)‖
              ≤ a ^ ((2 * s).re - 1) * (M * a⁻¹) :=
            mul_le_mul_of_nonneg_left (hM a⁻¹ ha_inv_ge) (Real.rpow_pos_of_pos ha.1 _).le
          _ = M * (a ^ ((2 * s).re - 1) * a ^ (-1 : ℝ)) := by rw [← Real.rpow_neg_one a]; ring
          _ = M * a ^ ((2 * s).re - 2) := by rw [← Real.rpow_add ha.1]; congr 2; ring
      have hR_sq : ‖lewisModularInversion (riemannMayerReflect s)
          (fun x => period (2 * s) ε c f x) a‖ ^ 2 ≤ M ^ 2 * a ^ (2 * (2 * s).re - 4) := by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) hR_le 2
        rw [mul_pow, ← Real.rpow_natCast (a ^ ((2 * s).re - 2)) 2, ← Real.rpow_mul ha.1.le] at h1
        have hexp : ((2 * s).re - 2) * ((2 : ℕ) : ℝ) = 2 * (2 * s).re - 4 := by
          push_cast
          ring
        rwa [hexp] at h1
      have hw_le : lewisCriticalWeight a ≤ a ^ (11 / 2 : ℝ) := by
        unfold lewisCriticalWeight
        calc
          (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))
              ≤ a ^ (6 : ℝ) * a ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (weight_le_Ioc ha) (Real.rpow_pos_of_pos ha.1 _).le
          _ = a ^ (11 / 2 : ℝ) := by rw [← Real.rpow_add ha.1]; norm_num
      calc
        ‖lewisModularInversion (riemannMayerReflect s)
            (fun x => period (2 * s) ε c f x) a‖ ^ 2 * lewisCriticalWeight a
            ≤ (M ^ 2 * a ^ (2 * (2 * s).re - 4)) * a ^ (11 / 2 : ℝ) :=
          mul_le_mul hR_sq hw_le (lewisCriticalWeight_pos ha.1).le
            (mul_nonneg (sq_nonneg M) (Real.rpow_pos_of_pos ha.1 _).le)
        _ = M ^ 2 * a ^ (2 * (2 * s).re + 3 / 2) := by
          rw [mul_assoc, ← Real.rpow_add ha.1]
          congr 2
          ring
        _ ≤ M ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one ha.1.le ha.2 (by linarith)) (sq_nonneg M)
        _ = M ^ 2 := mul_one _
    · have hdom : IntegrableOn (fun b : ℝ => M ^ 2 * b ^ (-5 / 2 : ℝ)) (Ioi 1) :=
        ((integrableOn_Ioi_rpow_iff zero_lt_one).2 (by norm_num)).const_mul (M ^ 2)
      refine hdom.mono'
        ((hcontR.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
      have hb0 : 0 < b := zero_lt_one.trans hb
      have hnn : 0 ≤
          ‖lewisModularInversion (riemannMayerReflect s) (fun x => period (2 * s) ε c f x) b‖ ^ 2 *
            lewisCriticalWeight b :=
        mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hb0).le
      rw [Real.norm_of_nonneg hnn]
      have hbinv_mem : b⁻¹ ∈ Ioc (0 : ℝ) 1 := ⟨inv_pos.mpr hb0, inv_le_one_of_one_le₀ hb.le⟩
      have hR_le : ‖lewisModularInversion (riemannMayerReflect s)
          (fun x => period (2 * s) ε c f x) b‖ ≤ M * b ^ (2 * (2 * s).re) := by
        dsimp only [lewisModularInversion]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb0, hre_ref]
        calc
          b ^ ((2 * s).re - 1) * ‖period (2 * s) ε c f (b⁻¹ : ℝ)‖
              ≤ b ^ ((2 * s).re - 1) * (M * (b⁻¹) ^ (-(2 * s).re - 1)) :=
            mul_le_mul_of_nonneg_left (hnear_bound b⁻¹ hbinv_mem) (Real.rpow_pos_of_pos hb0 _).le
          _ = M * (b ^ ((2 * s).re - 1) * b ^ ((2 * s).re + 1)) := by
            rw [Real.inv_rpow hb0.le, ← Real.rpow_neg hb0.le,
              show -(-(2 * s).re - 1) = (2 * s).re + 1 by ring]
            ring
          _ = M * b ^ (2 * (2 * s).re) := by rw [← Real.rpow_add hb0]; congr 2; ring
      have hR_sq : ‖lewisModularInversion (riemannMayerReflect s)
          (fun x => period (2 * s) ε c f x) b‖ ^ 2 ≤ M ^ 2 * b ^ (4 * (2 * s).re) := by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) hR_le 2
        rw [mul_pow, ← Real.rpow_natCast (b ^ (2 * (2 * s).re)) 2, ← Real.rpow_mul hb0.le] at h1
        have hexp : 2 * (2 * s).re * ((2 : ℕ) : ℝ) = 4 * (2 * s).re := by
          push_cast
          ring
        rwa [hexp] at h1
      have hw_le : lewisCriticalWeight b ≤ b ^ (-13 / 2 : ℝ) := by
        unfold lewisCriticalWeight
        calc
          (b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))
              ≤ b ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (weight_le_Ioi hb) (Real.rpow_pos_of_pos hb0 _).le
          _ = b ^ (-13 / 2 : ℝ) := by rw [← Real.rpow_add hb0]; norm_num
      calc
        ‖lewisModularInversion (riemannMayerReflect s)
            (fun x => period (2 * s) ε c f x) b‖ ^ 2 * lewisCriticalWeight b
            ≤ (M ^ 2 * b ^ (4 * (2 * s).re)) * b ^ (-13 / 2 : ℝ) :=
          mul_le_mul hR_sq hw_le (lewisCriticalWeight_pos hb0).le
            (mul_nonneg (sq_nonneg M) (Real.rpow_pos_of_pos hb0 _).le)
        _ = M ^ 2 * b ^ (4 * (2 * s).re - 13 / 2) := by
          rw [mul_assoc, ← Real.rpow_add hb0]
          congr 2
          ring
        _ ≤ M ^ 2 * b ^ (-5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hb.le (by linarith)) (sq_nonneg M)

theorem resonantLewisPeriod_integrable_lewisCriticalNormSq {s : ℂ}
    (hs : IsMayerScatteringResonance s) :
    IntegrableOn (fun a : ℝ => ‖resonantLewisPeriod s a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
      IntegrableOn (fun a : ℝ =>
        ‖lewisModularInversion (riemannMayerReflect s) (fun x => resonantLewisPeriod s x) a‖ ^ 2 *
          lewisCriticalWeight a) (Ioi 0) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith [hs.1]
  have hconst0 : (constant 0 : DiscSpace) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_constant, norm_zero]
  have hreg : regularized (2 * s) hw0 (state (2 * s)) =
      (1 : ℂ) • state (2 * s) + constant 0 := by
    rw [← source_eq hw0, hs.2.2, one_smul, hconst0, add_zero]
  exact globalLewisPeriod_integrable_lewisCriticalNormSq hs.1 hs.2.1 (by norm_num)
    (state (2 * s)) hreg

theorem resonantLewisPeriod_pos_lewisCriticalNormSq {s : ℂ} (hs : IsMayerScatteringResonance s) :
    0 < lewisCriticalNormSq (fun a : ℝ => resonantLewisPeriod s a) := by
  have hnn := lewisCriticalNormSq_nonneg (fun a : ℝ => resonantLewisPeriod s a)
  apply lt_of_le_of_ne hnn
  intro hzero
  have hcont : ContinuousOn (fun a : ℝ => resonantLewisPeriod s a) (Ioi 0) :=
    period_real_continuousOn (by simp; linarith [hs.1]) 1 0 (state (2 * s))
  have hvan := eq_zero_on_Ioi_of_lewisCriticalNormSq_eq_zero hcont
    (resonantLewisPeriod_integrable_lewisCriticalNormSq hs).1 hzero.symm 1 zero_lt_one
  exact resonantLewisPeriod_one_ne_zero hs (by simpa using hvan)

/-! ## Hilbert adjoint `I_s† = I_{1/2 - conj s}` and exact unitarity criterion -/

/-- On `H_LP`, the formal Hilbert adjoint of `lewisModularInversion s` is
`lewisModularInversion (riemannMayerReflect s)`. -/
theorem lewisCriticalInner_modularInversion_adj (s : ℂ) (f g : ℝ → ℂ) :
    lewisCriticalInner (lewisModularInversion s f) g =
      lewisCriticalInner f (lewisModularInversion (riemannMayerReflect s) g) := by
  unfold lewisCriticalInner
  rw [integral_Ioi_zero_inv_subst]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := hb
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0.ne'
  dsimp only [lewisModularInversion]
  rw [inv_inv, Complex.real_smul, ofReal_inv_cpow_pos hb0 (-(2 * s)), neg_neg,
    map_mul, conj_ofReal_cpow_pos hb0]
  have hjac_w : ((b ^ (-2 : ℝ) : ℝ) : ℂ) * (lewisCriticalWeight b⁻¹ : ℂ) =
      (b : ℂ) ^ (-1 : ℂ) * (lewisCriticalWeight b : ℂ) := by
    have hb_pow : ((b ^ (-1 : ℝ) : ℝ) : ℂ) = (b : ℂ) ^ (-1 : ℂ) := by
      simpa using (Complex.ofReal_cpow hb0.le (-1 : ℝ)).symm
    rw [← Complex.ofReal_mul, lewisCriticalWeight_inv_mul_jac hb0, Complex.ofReal_mul, hb_pow]
  have hexp_conj : (starRingEnd ℂ) (-(2 * riemannMayerReflect s)) = 2 * s - 1 := by
    unfold riemannMayerReflect
    rw [map_neg, map_mul, map_ofNat, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
    ring
  rw [hexp_conj]
  have hpow : (b : ℂ) ^ (2 * s) * (b : ℂ) ^ (-1 : ℂ) = (b : ℂ) ^ (2 * s - 1) := by
    rw [← Complex.cpow_add _ _ hbC, ← sub_eq_add_neg]
  calc
    ((b ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((b : ℂ) ^ (2 * s) * f b * (starRingEnd ℂ) (g b⁻¹) * (lewisCriticalWeight b⁻¹ : ℂ))
        = ((b : ℂ) ^ (2 * s) * f b * (starRingEnd ℂ) (g b⁻¹)) *
            (((b ^ (-2 : ℝ) : ℝ) : ℂ) * (lewisCriticalWeight b⁻¹ : ℂ)) := by ring
    _ = ((b : ℂ) ^ (2 * s) * f b * (starRingEnd ℂ) (g b⁻¹)) *
          ((b : ℂ) ^ (-1 : ℂ) * (lewisCriticalWeight b : ℂ)) := by rw [hjac_w]
    _ = f b * (((b : ℂ) ^ (2 * s) * (b : ℂ) ^ (-1 : ℂ)) * (starRingEnd ℂ) (g b⁻¹)) *
          (lewisCriticalWeight b : ℂ) := by ring
    _ = f b * ((b : ℂ) ^ (2 * s - 1) * (starRingEnd ℂ) (g b⁻¹)) *
          (lewisCriticalWeight b : ℂ) := by rw [hpow]

theorem lewisCriticalNormSq_modularInversion (s : ℂ) (f : ℝ → ℂ) :
    lewisCriticalNormSq (lewisModularInversion s f) =
      ∫ b in Ioi (0 : ℝ), ‖f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2)) := by
  unfold lewisCriticalNormSq
  rw [integral_Ioi_zero_inv_subst]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := hb
  have hb_inv : 0 < b⁻¹ := inv_pos.mpr hb0
  dsimp only [smul_eq_mul, lewisModularInversion]
  rw [inv_inv, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hb_inv]
  have hpow : ((b⁻¹) ^ (-(2 * s)).re) ^ (2 : ℕ) = b ^ (4 * s.re) := by
    have hre : (-(2 * s)).re = -2 * s.re := by simp
    rw [hre, Real.inv_rpow hb0.le, ← Real.rpow_neg hb0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hb0.le]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hmul_jac : b ^ (-2 : ℝ) * ((b ^ (4 * s.re) * ‖f b‖ ^ 2) *
      lewisCriticalWeight b⁻¹) =
      ‖f b‖ ^ 2 * (b ^ (4 * s.re) *
        (b ^ (-2 : ℝ) * lewisCriticalWeight b⁻¹)) := by ring
  rw [hmul_jac, lewisCriticalWeight_inv_mul_jac hb0]
  unfold lewisCriticalWeight
  have hcomb : b ^ (4 * s.re) *
      (b ^ (-1 : ℝ) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)))) =
      (b + b⁻¹) ^ (-6 : ℝ) *
        (b ^ (4 * s.re) * b ^ (-1 : ℝ) * b ^ (-(1 / 2 : ℝ))) := by ring
  rw [hcomb, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
  congr 3
  ring

/-- `lewisModularInversion s` preserves `lewisCriticalNormSq` for all functions iff `s` lies on
the critical scattering line `Re s = 1/4`. -/
theorem lewisModularInversion_isometry_iff (s : ℂ) :
    (∀ f : ℝ → ℂ, lewisCriticalNormSq (lewisModularInversion s f) = lewisCriticalNormSq f) ↔
      s.re = 1 / 4 := by
  constructor
  · intro hiso
    let f : ℝ → ℂ := (Ioc (1 : ℝ) 2).indicator (fun _ => 1)
    have htest := hiso f
    rw [lewisCriticalNormSq_modularInversion] at htest
    unfold lewisCriticalNormSq lewisCriticalWeight at htest
    have hind : ∀ α : ℝ,
        (∫ b in Ioi (0 : ℝ), ‖f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ α)) =
          ∫ b in Ioc (1 : ℝ) 2, (b + b⁻¹) ^ (-6 : ℝ) * b ^ α := by
      intro α
      have hfun : (fun b : ℝ => ‖f b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ α)) =
          (Ioc (1 : ℝ) 2).indicator (fun b => (b + b⁻¹) ^ (-6 : ℝ) * b ^ α) := by
        ext b
        by_cases hb : b ∈ Ioc (1 : ℝ) 2 <;> simp [f, hb]
      rw [hfun, setIntegral_indicator measurableSet_Ioc,
        inter_eq_self_of_subset_right (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one))]
    rw [hind (4 * s.re - 3 / 2), hind (-(1 / 2 : ℝ))] at htest
    have hint_α : ∀ α : ℝ,
        IntegrableOn (fun b : ℝ => (b + b⁻¹) ^ (-6 : ℝ) * b ^ α) (Ioc 1 2) := by
      intro α
      apply ContinuousOn.integrableOn_Icc _ |>.mono_set Ioc_subset_Icc_self
      intro b hb
      have hb0 : 0 < b := zero_lt_one.trans_le hb.1
      have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
      exact (((continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow continuousAt_const
        (Or.inl hsum)).mul (continuousAt_id.rpow continuousAt_const
        (Or.inl hb0.ne'))).continuousWithinAt
    by_contra hne
    have hpos_int : ∀ {α₁ α₂ : ℝ}, α₁ < α₂ →
        0 < ∫ b in Ioc (1 : ℝ) 2, (b + b⁻¹) ^ (-6 : ℝ) * (b ^ α₂ - b ^ α₁) := by
      intro α₁ α₂ hlt
      let d : ℝ → ℝ := fun b => (b + b⁻¹) ^ (-6 : ℝ) * (b ^ α₂ - b ^ α₁)
      have hd_int : IntegrableOn d (Ioc 1 2) := by
        have hsub_int := (hint_α α₂).sub (hint_α α₁)
        refine hsub_int.congr_fun (fun b _ => ?_) measurableSet_Ioc
        dsimp [d]
        ring
      have hsub_set : Ioc (3 / 2 : ℝ) 2 ⊆ Ioc 1 2 :=
        fun x hx => ⟨by linarith [hx.1], hx.2⟩
      have hunion : Ioc (1 : ℝ) 2 = Ioc (3 / 2) 2 ∪ (Ioc 1 2 \ Ioc (3 / 2) 2) :=
        (Set.union_sdiff_cancel hsub_set).symm
      have hsplit : (∫ b in Ioc (1 : ℝ) 2, d b) =
          (∫ b in Ioc (3 / 2) 2, d b) + ∫ b in Ioc 1 2 \ Ioc (3 / 2) 2, d b := by
        conv_lhs => rw [hunion]
        exact setIntegral_union disjoint_sdiff_self_right
          (measurableSet_Ioc.diff measurableSet_Ioc)
          (hd_int.mono_set hsub_set) (hd_int.mono_set Set.sdiff_subset)
      have hrest : 0 ≤ ∫ b in Ioc 1 2 \ Ioc (3 / 2) 2, d b := by
        refine setIntegral_nonneg (measurableSet_Ioc.diff measurableSet_Ioc) fun b hb => ?_
        have hb0 : 0 < b := zero_lt_one.trans hb.1.1
        exact mul_nonneg (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
          (sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le hb.1.1.le hlt.le))
      have hd_cont : ContinuousOn d (Icc (3 / 2) 2) := by
        intro b hb
        have hb0 : 0 < b := by linarith [hb.1]
        have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
        exact (((continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow continuousAt_const
          (Or.inl hsum)).mul ((continuousAt_id.rpow continuousAt_const (Or.inl hb0.ne')).sub
          (continuousAt_id.rpow continuousAt_const (Or.inl hb0.ne')))).continuousWithinAt
      obtain ⟨x₀, hx₀, hmin⟩ :=
        isCompact_Icc.exists_isMinOn (by norm_num : (Icc (3 / 2 : ℝ) 2).Nonempty) hd_cont
      have hx₀_gt1 : 1 < x₀ := by linarith [hx₀.1]
      have hx₀_pos : 0 < x₀ := zero_lt_one.trans hx₀_gt1
      have hdx₀ : 0 < d x₀ := mul_pos
        (Real.rpow_pos_of_pos (add_pos hx₀_pos (inv_pos.mpr hx₀_pos)) _)
        (sub_pos.mpr (Real.rpow_lt_rpow_of_exponent_lt hx₀_gt1 hlt))
      have hlow : (1 / 2 : ℝ) * d x₀ ≤ ∫ b in Ioc (3 / 2) 2, d b := by
        have hc : (∫ _ in Ioc (3 / 2 : ℝ) 2, d x₀) = (1 / 2 : ℝ) * d x₀ := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
          ring
        rw [← hc]
        exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
          (hd_int.mono_set hsub_set) measurableSet_Ioc fun b hb => hmin ⟨hb.1.le, hb.2⟩
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub_eq : (∫ b in Ioc (1 : ℝ) 2,
          (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (-(1 / 2 : ℝ)) - b ^ (4 * s.re - 3 / 2))) = 0 := by
        have hrew : (fun b : ℝ =>
            (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (-(1 / 2 : ℝ)) - b ^ (4 * s.re - 3 / 2))) =
            fun b => (b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)) -
              (b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2) := by
          ext b; ring
        rw [hrew, integral_sub (hint_α _) (hint_α _), htest, sub_self]
      have hp := hpos_int (α₁ := 4 * s.re - 3 / 2) (α₂ := -(1 / 2 : ℝ)) (by linarith)
      linarith
    · have hsub_eq : (∫ b in Ioc (1 : ℝ) 2,
          (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (4 * s.re - 3 / 2) - b ^ (-(1 / 2 : ℝ)))) = 0 := by
        have hrew : (fun b : ℝ =>
            (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (4 * s.re - 3 / 2) - b ^ (-(1 / 2 : ℝ)))) =
            fun b => (b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2) -
              (b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)) := by
          ext b; ring
        rw [hrew, integral_sub (hint_α _) (hint_α _), htest, sub_self]
      have hp := hpos_int (α₁ := -(1 / 2 : ℝ)) (α₂ := 4 * s.re - 3 / 2) (by linarith)
      linarith
  · intro hs f
    rw [lewisCriticalNormSq_modularInversion, hs,
      show (4 * (1 / 4 : ℝ) - 3 / 2) = -(1 / 2 : ℝ) by norm_num]
    rfl

/-! ## Co-isometry defect `Q_s(ψ)` and strict negativity off `Re s = 1/4` -/

/-- The co-isometry / reflected Krein defect `‖ψ‖_LP² - ‖I_{1/2 - conj s} ψ‖_LP²` on `H_LP`. -/
def lewisCoIsometryDefect (s : ℂ) (ψ : ℝ → ℂ) : ℝ :=
  lewisCriticalNormSq ψ - lewisCriticalNormSq (lewisModularInversion (riemannMayerReflect s) ψ)

private theorem norm_sq_inv_of_modular_fixed {s : ℂ} {ψ : ℝ → ℂ}
    (hfix : ∀ a > 0, lewisModularInversion s ψ a = ψ a) {b : ℝ} (hb : 0 < b) :
    ‖ψ b⁻¹‖ ^ 2 = b ^ (4 * s.re) * ‖ψ b‖ ^ 2 := by
  have hb_inv : 0 < b⁻¹ := inv_pos.mpr hb
  have heq := (hfix b⁻¹ hb_inv).symm
  unfold lewisModularInversion at heq
  rw [inv_inv, ofReal_inv_cpow_pos hb (-(2 * s)), neg_neg] at heq
  rw [heq, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hb,
    ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
  congr 2
  have hre : (2 * s).re = 2 * s.re := by simp
  rw [hre]
  push_cast
  ring

private theorem norm_sq_reflected_of_modular_fixed {s : ℂ} {ψ : ℝ → ℂ}
    (hfix : ∀ a > 0, lewisModularInversion s ψ a = ψ a) {a : ℝ} (ha : 0 < a) :
    ‖lewisModularInversion (riemannMayerReflect s) ψ a‖ ^ 2 =
      a ^ (8 * s.re - 2) * ‖ψ a‖ ^ 2 := by
  unfold lewisModularInversion
  rw [norm_mul, mul_pow, norm_sq_inv_of_modular_fixed hfix ha,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, ← Real.rpow_natCast, ← Real.rpow_mul ha.le,
    ← mul_assoc, ← Real.rpow_add ha]
  congr 2
  have hre : (-(2 * riemannMayerReflect s)).re = 2 * s.re - 1 := by
    simp [riemannMayerReflect]
    ring
  rw [hre]
  push_cast
  ring

private theorem fold_Ioi_zero_to_Ioi_one {s : ℂ} {ψ : ℝ → ℂ}
    (hfix : ∀ a > 0, lewisModularInversion s ψ a = ψ a) {α : ℝ}
    (h_int : IntegrableOn (fun a : ℝ => ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ α)) (Ioi 0))
    (h_fold_int : IntegrableOn
      (fun b : ℝ => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 2 - α))) (Ioi 1)) :
    (∫ a in Ioi (0 : ℝ), ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ α)) =
      ∫ b in Ioi (1 : ℝ),
        ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * (b ^ α + b ^ (4 * s.re - 2 - α))) := by
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt.mpr hx.2) hy
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union hdisj measurableSet_Ioi
      (h_int.mono_set Ioc_subset_Ioi_self)
      (h_int.mono_set (Ioi_subset_Ioi zero_le_one)),
    integral_Ioc_zero_one_inv_subst]
  have hfold_eq :
      (∫ b in Ioi (1 : ℝ),
          b ^ (-2 : ℝ) * (‖ψ b⁻¹‖ ^ 2 * ((b⁻¹ + (b⁻¹)⁻¹) ^ (-6 : ℝ) * (b⁻¹) ^ α))) =
        ∫ b in Ioi (1 : ℝ),
          ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 2 - α)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
    have hb0 : 0 < b := zero_lt_one.trans hb
    rw [norm_sq_inv_of_modular_fixed hfix hb0, inv_inv, add_comm b⁻¹ b,
      Real.inv_rpow hb0.le, ← Real.rpow_neg hb0.le]
    have h1 : b ^ (-2 : ℝ) * ((b ^ (4 * s.re) * ‖ψ b‖ ^ 2) *
        ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-α))) =
        ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) *
          (b ^ (-2 : ℝ) * b ^ (4 * s.re) * b ^ (-α))) := by ring
    rw [h1, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
    congr 3
    ring
  rw [hfold_eq, ← integral_add h_fold_int (h_int.mono_set (Ioi_subset_Ioi zero_le_one))]
  refine setIntegral_congr_fun measurableSet_Ioi fun b _ => ?_
  ring

/-- **Exact Integral Identity for the Co-Isometry Defect `Q_s(ψ)`.**
For any `+1` `I_s`-fixed function `ψ` on `(0, ∞)` satisfying the half-line integrability
conditions, `Q_s(ψ)` collapses to a single manifest nonpositive integral over `(1, ∞)` with kernel
`-(b + b⁻¹)^(-6) b^(2 Re s - 1) (b^δ + b^(-δ)) (b^δ - b^(-δ))²` (`δ = 2 Re s - 1/2`). -/
theorem lewisCoIsometryDefect_eq_neg_integral {s : ℂ} {ψ : ℝ → ℂ}
    (hfix : ∀ a > 0, lewisModularInversion s ψ a = ψ a)
    (hψ_int : IntegrableOn (fun a => ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0))
    (hψR_int : IntegrableOn
      (fun a => ‖lewisModularInversion (riemannMayerReflect s) ψ a‖ ^ 2 * lewisCriticalWeight a)
      (Ioi 0))
    (hfold1 : IntegrableOn
      (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2))) (Ioi 1))
    (hfold2 : IntegrableOn
      (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-4 * s.re + 1 / 2))) (Ioi 1)) :
    lewisCoIsometryDefect s ψ =
      -∫ b in Ioi (1 : ℝ),
        (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) *
          (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
          (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 * ‖ψ b‖ ^ 2 := by
  let δ : ℝ := 2 * s.re - 1 / 2
  have h1_int : IntegrableOn
      (fun a : ℝ => ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ)))) (Ioi 0) := hψ_int
  have h2_congr : ∀ a ∈ Ioi (0 : ℝ),
      ‖lewisModularInversion (riemannMayerReflect s) ψ a‖ ^ 2 * lewisCriticalWeight a =
        ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (8 * s.re - 5 / 2)) := by
    intro a ha
    have ha0 : 0 < a := ha
    rw [norm_sq_reflected_of_modular_fixed hfix ha0]
    unfold lewisCriticalWeight
    have hmul : (a ^ (8 * s.re - 2) * ‖ψ a‖ ^ 2) *
        ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))) =
        ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * (a ^ (8 * s.re - 2) * a ^ (-(1 / 2 : ℝ)))) := by ring
    rw [hmul, ← Real.rpow_add ha0]
    congr 3
    ring
  have h2_int : IntegrableOn
      (fun a : ℝ => ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (8 * s.re - 5 / 2))) (Ioi 0) :=
    hψR_int.congr_fun h2_congr measurableSet_Ioi
  have hnorm2_eq : lewisCriticalNormSq (lewisModularInversion (riemannMayerReflect s) ψ) =
      ∫ a in Ioi (0 : ℝ), ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (8 * s.re - 5 / 2)) :=
    setIntegral_congr_fun measurableSet_Ioi h2_congr
  have hf1 := fold_Ioi_zero_to_Ioi_one hfix h1_int
    (by convert hfold1 using 3; ring)
  have hf2 := fold_Ioi_zero_to_Ioi_one hfix h2_int
    (by convert hfold2 using 3; ring)
  unfold lewisCoIsometryDefect
  change (∫ a in Ioi (0 : ℝ), ‖ψ a‖ ^ 2 * ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ)))) -
      lewisCriticalNormSq (lewisModularInversion (riemannMayerReflect s) ψ) = _
  rw [hnorm2_eq, hf1, hf2]
  have hintA : IntegrableOn
      (fun b : ℝ =>
        ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) *
          (b ^ (-(1 / 2 : ℝ)) + b ^ (4 * s.re - 2 - -(1 / 2 : ℝ))))) (Ioi 1) := by
    have hs := (h1_int.mono_set (Ioi_subset_Ioi zero_le_one)).add hfold1
    refine hs.congr_fun (fun b _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    rw [show 4 * s.re - 2 - -(1 / 2 : ℝ) = 4 * s.re - 3 / 2 by ring]
    ring
  have hintB : IntegrableOn
      (fun b : ℝ =>
        ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) *
          (b ^ (8 * s.re - 5 / 2) + b ^ (4 * s.re - 2 - (8 * s.re - 5 / 2))))) (Ioi 1) := by
    have hs := (h2_int.mono_set (Ioi_subset_Ioi zero_le_one)).add hfold2
    refine hs.congr_fun (fun b _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    rw [show 4 * s.re - 2 - (8 * s.re - 5 / 2) = -4 * s.re + 1 / 2 by ring]
    ring
  rw [← integral_sub hintA hintB, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := zero_lt_one.trans hb
  let x : ℝ := b ^ δ
  let y : ℝ := b ^ (-δ)
  have hxy : x * y = 1 := by
    dsimp [x, y]
    rw [← Real.rpow_add hb0, add_neg_cancel, Real.rpow_zero]
  have hp1 : b ^ (-(1 / 2 : ℝ)) = b ^ (2 * s.re - 1) * y := by
    dsimp [y, δ]
    rw [← Real.rpow_add hb0]
    congr 1
    ring
  have hp2 : b ^ (4 * s.re - 2 - -(1 / 2 : ℝ)) = b ^ (2 * s.re - 1) * x := by
    dsimp [x, δ]
    rw [← Real.rpow_add hb0]
    congr 1
    ring
  have hp3 : b ^ (8 * s.re - 5 / 2) = b ^ (2 * s.re - 1) * x ^ 3 := by
    dsimp [x, δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    congr 1
    push_cast
    ring
  have hp4 : b ^ (4 * s.re - 2 - (8 * s.re - 5 / 2)) = b ^ (2 * s.re - 1) * y ^ 3 := by
    dsimp [y, δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    congr 1
    push_cast
    ring
  have halg : (y + x) - (x ^ 3 + y ^ 3) = -(x + y) * (x - y) ^ 2 := by
    linear_combination -(x + y) * hxy
  rw [hp1, hp2, hp3, hp4]
  change ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * (b ^ (2 * s.re - 1) * y + b ^ (2 * s.re - 1) * x)) -
      ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) *
        (b ^ (2 * s.re - 1) * x ^ 3 + b ^ (2 * s.re - 1) * y ^ 3)) =
    -((b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) * (x + y) * (x - y) ^ 2 * ‖ψ b‖ ^ 2)
  linear_combination (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) * ‖ψ b‖ ^ 2 * halg

/-- Exact integral formula specialized to every resonant Lewis period function. -/
theorem resonantLewisPeriod_coIsometryDefect_eq {s : ℂ} (hs : IsMayerScatteringResonance s) :
    lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) =
      -∫ b in Ioi (1 : ℝ),
        (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) *
          (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
          (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 *
          ‖resonantLewisPeriod s b‖ ^ 2 := by
  have hw0 : 0 < (2 * s).re := by simp; linarith [hs.1]
  have hconst0 : (constant 0 : DiscSpace) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_constant, norm_zero]
  have hreg : regularized (2 * s) hw0 (state (2 * s)) =
      (1 : ℂ) • state (2 * s) + constant 0 := by
    rw [← source_eq hw0, hs.2.2, one_smul, hconst0, add_zero]
  obtain ⟨hi1, hi2⟩ := resonantLewisPeriod_integrable_lewisCriticalNormSq hs
  have hf1 := globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 (by norm_num) (state (2 * s)) hreg
    (β := 4 * s.re - 3 / 2) (by linarith [hs.2.1])
  have hf2 := globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 (by norm_num) (state (2 * s)) hreg
    (β := -4 * s.re + 1 / 2) (by linarith [hs.1])
  exact lewisCoIsometryDefect_eq_neg_integral
    (fun a ha => lewisModularInversion_resonantLewisPeriod hs ha) hi1 hi2 hf1 hf2

/-- Unconditional nonpositivity of `lewisCoIsometryDefect` at every Mayer scattering resonance. -/
theorem resonantLewisPeriod_coIsometryDefect_nonpos {s : ℂ} (hs : IsMayerScatteringResonance s) :
    lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) ≤ 0 := by
  rw [resonantLewisPeriod_coIsometryDefect_eq hs, Left.neg_nonpos_iff]
  refine setIntegral_nonneg measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := zero_lt_one.trans hb
  have h1 : 0 ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
    (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
  have h2 : 0 ≤ b ^ (2 * s.re - 1) := (Real.rpow_pos_of_pos hb0 _).le
  have h3 : 0 ≤ b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2)) :=
    add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) (sq_nonneg _)) (sq_nonneg _)

/-- **Strict Co-Isometry Negativity Off `Re s = 1/4`.**
At any Mayer scattering resonance `s`, the co-isometry defect of `resonantLewisPeriod s` on `H_LP`
is strictly negative iff `s.re ≠ 1/4`. -/
theorem resonantLewisPeriod_coIsometryDefect_lt_zero_iff {s : ℂ}
    (hs : IsMayerScatteringResonance s) :
    lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) < 0 ↔ s.re ≠ 1 / 4 := by
  constructor
  · intro hlt heq
    rw [resonantLewisPeriod_coIsometryDefect_eq hs, heq] at hlt
    have hzero_int :
        (∫ b in Ioi (1 : ℝ),
          (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * (1 / 4 : ℝ) - 1) *
            (b ^ (2 * (1 / 4 : ℝ) - 1 / 2) + b ^ (-(2 * (1 / 4 : ℝ) - 1 / 2))) *
            (b ^ (2 * (1 / 4 : ℝ) - 1 / 2) - b ^ (-(2 * (1 / 4 : ℝ) - 1 / 2))) ^ 2 *
            ‖resonantLewisPeriod s b‖ ^ 2) = 0 := by
      rw [show (2 * (1 / 4 : ℝ) - 1 / 2) = 0 by norm_num, neg_zero]
      simp [sub_self]
    rw [hzero_int, neg_zero] at hlt
    exact lt_irrefl 0 hlt
  · intro hne
    rw [resonantLewisPeriod_coIsometryDefect_eq hs, Left.neg_neg_iff]
    let δ : ℝ := 2 * s.re - 1 / 2
    have hδ_ne : δ ≠ 0 := by dsimp [δ]; intro h; apply hne; linarith
    let K : ℝ → ℝ := fun b =>
      (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) *
        (b ^ δ + b ^ (-δ)) * (b ^ δ - b ^ (-δ)) ^ 2 * ‖resonantLewisPeriod s b‖ ^ 2
    have hψ_cont : ContinuousOn (fun b : ℝ => resonantLewisPeriod s b) (Ioi 0) :=
      period_real_continuousOn (by simp; linarith [hs.1]) 1 0 (state (2 * s))
    have hc1 : 0 < ‖resonantLewisPeriod s (1 : ℝ)‖ :=
      norm_pos_iff.mpr (by simpa using resonantLewisPeriod_one_ne_zero hs)
    have hcont1 : ContinuousAt (fun x : ℝ => ‖resonantLewisPeriod s x‖) 1 :=
      (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr zero_lt_one))).norm
    obtain ⟨r, hr_pos, hball⟩ :=
      Metric.continuousAt_iff.mp hcont1 (‖resonantLewisPeriod s (1 : ℝ)‖ / 2) (half_pos hc1)
    let p : ℝ := 1 + min r 1 / 4
    let q : ℝ := 1 + min r 1 / 2
    have hmin_pos : 0 < min r 1 := lt_min hr_pos zero_lt_one
    have hp_gt1 : 1 < p := by dsimp [p]; linarith
    have hp_lt_q : p < q := by dsimp [p, q]; linarith
    have hK_cont : ContinuousOn K (Ioi 0) := by
      intro b hb
      have hb0 : 0 < b := hb
      have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
      have c1 : ContinuousAt (fun x : ℝ => (x + x⁻¹) ^ (-6 : ℝ)) b :=
        (continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (-6 : ℝ)) b) (Or.inl hsum)
      have c2 : ContinuousAt (fun x : ℝ => x ^ (2 * s.re - 1)) b :=
        continuousAt_id.rpow
          (continuousAt_const : ContinuousAt (fun _ : ℝ => 2 * s.re - 1) b) (Or.inl hb0.ne')
      have c3 : ContinuousAt (fun x : ℝ => x ^ δ + x ^ (-δ)) b :=
        (continuousAt_id.rpow (continuousAt_const : ContinuousAt (fun _ : ℝ => δ) b) (Or.inl hb0.ne')).add
          (continuousAt_id.rpow (continuousAt_const : ContinuousAt (fun _ : ℝ => -δ) b) (Or.inl hb0.ne'))
      have c4 : ContinuousAt (fun x : ℝ => (x ^ δ - x ^ (-δ)) ^ 2) b :=
        ((continuousAt_id.rpow (continuousAt_const : ContinuousAt (fun _ : ℝ => δ) b) (Or.inl hb0.ne')).sub
          (continuousAt_id.rpow (continuousAt_const : ContinuousAt (fun _ : ℝ => -δ) b) (Or.inl hb0.ne'))).pow 2
      have c5 : ContinuousAt (fun x : ℝ => ‖resonantLewisPeriod s x‖ ^ 2) b :=
        (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hb0))).norm.pow 2
      exact ((((c1.mul c2).mul c3).mul c4).mul c5).continuousWithinAt
    obtain ⟨x₀, hx₀, hminK⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr hp_lt_q.le)
      (hK_cont.mono (fun x hx => zero_lt_one.trans (lt_of_lt_of_le hp_gt1 hx.1)))
    have hx₀_gt1 : 1 < x₀ := lt_of_lt_of_le hp_gt1 hx₀.1
    have hx₀_pos : 0 < x₀ := zero_lt_one.trans hx₀_gt1
    have hx₀_dist : dist x₀ 1 < r := by
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < x₀ - 1)]
      have hle_r : min r 1 ≤ r := min_le_left r 1
      have hx₀_le : x₀ ≤ 1 + min r 1 / 2 := hx₀.2
      linarith
    have hx₀_ψ_pos : 0 < ‖resonantLewisPeriod s x₀‖ := by
      have hb := abs_lt.mp (by simpa [Real.dist_eq] using hball hx₀_dist)
      linarith
    have hx₀_diff_ne : x₀ ^ δ - x₀ ^ (-δ) ≠ 0 := by
      intro heq_pow
      have hpow_eq : x₀ ^ δ = x₀ ^ (-δ) := sub_eq_zero.mp heq_pow
      rcases lt_or_gt_of_ne hδ_ne with hneg | hpos
      · have hlt := Real.rpow_lt_rpow_of_exponent_lt hx₀_gt1 (show δ < -δ by linarith)
        exact hlt.ne hpow_eq
      · have hlt := Real.rpow_lt_rpow_of_exponent_lt hx₀_gt1 (show -δ < δ by linarith)
        exact hlt.ne hpow_eq.symm
    have hKx₀_pos : 0 < K x₀ := by
      dsimp [K]
      refine mul_pos (mul_pos (mul_pos (mul_pos ?_ ?_) ?_) (sq_pos_iff.mpr hx₀_diff_ne))
        (sq_pos_of_pos hx₀_ψ_pos)
      · exact Real.rpow_pos_of_pos (add_pos hx₀_pos (inv_pos.mpr hx₀_pos)) _
      · exact Real.rpow_pos_of_pos hx₀_pos _
      · exact add_pos (Real.rpow_pos_of_pos hx₀_pos _) (Real.rpow_pos_of_pos hx₀_pos _)
    -- Integrability of `K` on `Ioi 1` via polynomial upper bound:
    have hK_int : IntegrableOn K (Ioi 1) := by
      have hw0 : 0 < (2 * s).re := by simp; linarith [hs.1]
      have hconst0 : (constant 0 : DiscSpace) = 0 := by
        apply norm_eq_zero.mp; rw [norm_constant, norm_zero]
      have hreg : regularized (2 * s) hw0 (state (2 * s)) =
          (1 : ℂ) • state (2 * s) + constant 0 := by
        rw [← source_eq hw0, hs.2.2, one_smul, hconst0, add_zero]
      have hdom := (globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 (by norm_num) (state (2 * s))
        hreg (β := 5 / 2) (by norm_num)).const_mul 8
      refine hdom.mono' ((hK_cont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
      have hb0 : 0 < b := zero_lt_one.trans hb
      have hb1 : 1 ≤ b := hb.le
      have hK_nn : 0 ≤ K b := by
        dsimp [K]
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
          (Real.rpow_pos_of_pos hb0 _).le)
          (add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le))
          (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_of_nonneg hK_nn]
      have hδ1 : δ ≤ 1 / 2 := by dsimp [δ]; linarith [hs.2.1]
      have hδ2 : -δ ≤ 1 / 2 := by dsimp [δ]; linarith [hs.1]
      have hbd1 : b ^ δ ≤ b ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hδ1
      have hbd2 : b ^ (-δ) ≤ b ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hδ2
      have hsum_le : b ^ δ + b ^ (-δ) ≤ 2 * b ^ (1 / 2 : ℝ) := by linarith
      have hdiff_abs : |b ^ δ - b ^ (-δ)| ≤ 2 * b ^ (1 / 2 : ℝ) := by
        have hp_d1 : 0 < b ^ δ := Real.rpow_pos_of_pos hb0 δ
        have hp_d2 : 0 < b ^ (-δ) := Real.rpow_pos_of_pos hb0 (-δ)
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      have hsq_le : (b ^ δ - b ^ (-δ)) ^ 2 ≤ 4 * b ^ (1 : ℝ) := by
        have h1 := pow_le_pow_left₀ (abs_nonneg _) hdiff_abs 2
        rw [sq_abs, mul_pow, ← Real.rpow_natCast (b ^ (1 / 2 : ℝ)) 2,
          ← Real.rpow_mul hb0.le] at h1
        have hexp : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 := by norm_num
        have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
        rwa [hexp, h4] at h1
      have hbase_le : b ^ (2 * s.re - 1) ≤ b ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith [hs.2.1])
      have hmid : b ^ (2 * s.re - 1) * (b ^ δ + b ^ (-δ)) * (b ^ δ - b ^ (-δ)) ^ 2 ≤
          8 * b ^ (5 / 2 : ℝ) := by
        calc
          b ^ (2 * s.re - 1) * (b ^ δ + b ^ (-δ)) * (b ^ δ - b ^ (-δ)) ^ 2
              ≤ (b ^ (1 : ℝ) * (2 * b ^ (1 / 2 : ℝ))) * (4 * b ^ (1 : ℝ)) := by
            apply mul_le_mul _ hsq_le (sq_nonneg _) (by positivity)
            exact mul_le_mul hbase_le hsum_le
              (add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le)
              (Real.rpow_pos_of_pos hb0 _).le
          _ = 8 * (b ^ (1 : ℝ) * b ^ (1 / 2 : ℝ) * b ^ (1 : ℝ)) := by ring
          _ = 8 * b ^ (5 / 2 : ℝ) := by rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; norm_num
      dsimp [K, resonantLewisPeriod]
      calc
        (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) * (b ^ δ + b ^ (-δ)) *
            (b ^ δ - b ^ (-δ)) ^ 2 * ‖period (2 * s) 1 0 (state (2 * s)) b‖ ^ 2
            = (b + b⁻¹) ^ (-6 : ℝ) * ‖period (2 * s) 1 0 (state (2 * s)) b‖ ^ 2 *
                (b ^ (2 * s.re - 1) * (b ^ δ + b ^ (-δ)) * (b ^ δ - b ^ (-δ)) ^ 2) := by ring
        _ ≤ (b + b⁻¹) ^ (-6 : ℝ) * ‖period (2 * s) 1 0 (state (2 * s)) b‖ ^ 2 *
              (8 * b ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmid
            (mul_nonneg (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le (sq_nonneg _))
        _ = 8 * (‖period (2 * s) 1 0 (state (2 * s)) b‖ ^ 2 *
              ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (5 / 2 : ℝ))) := by ring
    have hsub_Ioi : Ioc p q ⊆ Ioi 1 := fun x hx => hp_gt1.trans hx.1
    have hunion : Ioi (1 : ℝ) = Ioc p q ∪ (Ioi 1 \ Ioc p q) :=
      (Set.union_sdiff_cancel hsub_Ioi).symm
    have hsplit : (∫ b in Ioi (1 : ℝ), K b) =
        (∫ b in Ioc p q, K b) + ∫ b in Ioi 1 \ Ioc p q, K b := by
      conv_lhs => rw [hunion]
      exact setIntegral_union disjoint_sdiff_self_right
        (measurableSet_Ioi.diff measurableSet_Ioc)
        (hK_int.mono_set hsub_Ioi) (hK_int.mono_set Set.sdiff_subset)
    have hrest : 0 ≤ ∫ b in Ioi 1 \ Ioc p q, K b := by
      refine setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioc) fun b hb => ?_
      have hb0 : 0 < b := zero_lt_one.trans hb.1
      dsimp [K]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
        (Real.rpow_pos_of_pos hb0 _).le)
        (add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le))
        (sq_nonneg _)) (sq_nonneg _)
    have hlow : (q - p) * K x₀ ≤ ∫ b in Ioc p q, K b := by
      have hc : (∫ _ in Ioc p q, K x₀) = (q - p) * K x₀ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hp_lt_q.le, smul_eq_mul]
      rw [← hc]
      exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
        (hK_int.mono_set hsub_Ioi) measurableSet_Ioc fun b hb => hminK ⟨hb.1.le, hb.2⟩
    have hprod_pos : 0 < (q - p) * K x₀ := mul_pos (sub_pos.mpr hp_lt_q) hKx₀_pos
    linarith

/-- Vanishing of `lewisCoIsometryDefect` at a Mayer scattering resonance characterizes the critical
scattering line `Re s = 1/4`. -/
theorem resonantLewisPeriod_coIsometryDefect_eq_zero_iff {s : ℂ}
    (hs : IsMayerScatteringResonance s) :
    lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) = 0 ↔ s.re = 1 / 4 := by
  have hnonpos := resonantLewisPeriod_coIsometryDefect_nonpos hs
  have hlt_iff := resonantLewisPeriod_coIsometryDefect_lt_zero_iff hs
  constructor
  · intro hz
    by_contra hne
    have hlt := hlt_iff.mpr hne
    linarith
  · intro heq
    by_contra hne0
    have hlt : lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) < 0 :=
      lt_of_le_of_ne hnonpos hne0
    exact (hlt_iff.mp hlt) heq

#print axioms fixed_vector_krein_self_pairing_nonneg
#print axioms cauchyMellinWeight_isometry
#print axioms eq_zero_on_Ioi_of_lewisCriticalNormSq_eq_zero
#print axioms globalLewisPeriod_integrable_lewisCriticalNormSq
#print axioms lewisCriticalInner_modularInversion_adj
#print axioms lewisModularInversion_isometry_iff
#print axioms lewisCoIsometryDefect_eq_neg_integral
#print axioms resonantLewisPeriod_coIsometryDefect_lt_zero_iff
#print axioms resonantLewisPeriod_coIsometryDefect_eq_zero_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
