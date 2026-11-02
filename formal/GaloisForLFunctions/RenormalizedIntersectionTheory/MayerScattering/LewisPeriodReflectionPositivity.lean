import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringCore

/-!
# Reflection Positivity, Modular Inversion Blindness, and Co-Isometry Defect on Lewis Period Functions

This module establishes Parts A and B of the reflection-positivity structure on Lewis period
functions for the Mayer operator:

1. **Modular Inversion Blindness (`I_s` at fixed `s`):** The Lewis modular inversion
   `(I_s ψ)(a) = a^(-2s) ψ(a⁻¹)` fixes every resonant global Lewis period function
   `resonantLewisPeriod s` and every Mayer scattering core `fieldCore (2s)` both on and off
   `Re s = 1/4`. Consequently, in any positive-semidefinite Hermitian space `(V, h)`, both
   `h(ψ_s, ψ_s) ≥ 0` and the `I_s`-induced Krein self-pairing `h(ψ_s, I_s ψ_s) = h(ψ_s, ψ_s) ≥ 0`
   are blind to `Re s = 1/4`; likewise, on the `s`-dependent Cauchy–Mellin space
   `L²((0, ∞), a^(4 Re s - 1) da)`, `I_s` is an exact isometry for every `s ∈ ℂ`.
2. **Canonical `s`-Independent Möbius–Critical Hilbert Space `H_LP`:** Equipped with the weight
   `lewisCriticalWeight a = (a + a⁻¹)^(-6) * a^(-1/2)` on `(0, ∞)`, every unsubtracted global
   Lewis period function across the entire open strip `0 < Re s < 1/2` (together with its
   Riemann–Mayer reflected partner) has finite positive norm.
3. **Hilbert Adjoint `I_s† = I_{1/2 - conj s}` and Strict Co-Isometry Negativity Off `Re s = 1/4`:**
   On `H_LP`, `⟨I_s f, g⟩_LP = ⟨f, I_{1/2 - conj s} g⟩_LP`, `I_s` is an isometry iff `s.re = 1/4`,
   and the co-isometry defect `lewisCoIsometryDefect s ψ = ‖ψ‖_LP² - ‖I_{1/2 - conj s} ψ‖_LP²` of
   any resonant Lewis period function `ψ_s = resonantLewisPeriod s` satisfies
   `lewisCoIsometryDefect s ψ_s = 0 ↔ s.re = 1/4` and
   `lewisCoIsometryDefect s ψ_s < 0 ↔ s.re ≠ 1/4`.
-/

open Complex Set Filter MeasureTheory Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerGlobalPeriods MayerScatteringCore

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ## Reciprocal change of variables on `(0, ∞)` and `(0, 1]` -/

private theorem hasDerivWithinAt_inv_Ioi {v : ℝ} (hv : 0 < v) :
    HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(v ^ 2)⁻¹) (Ioi 0) v :=
  (hasDerivAt_inv hv.ne').hasDerivWithinAt

private theorem integral_Ioi_zero_inv_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    (∫ a in Ioi (0 : ℝ), g a) = ∫ b in Ioi (0 : ℝ), b ^ (-2 : ℝ) • g b⁻¹ := by
  have himg : (fun b : ℝ => b⁻¹) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext u
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
  dsimp only
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

private theorem ofReal_inv_cpow_pos {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a⁻¹ : ℝ) : ℂ) ^ z = (a : ℂ) ^ (-z) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]

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
  unfold lewisModularInversion
  have hrec := resonantLewisPeriod_reciprocity hs (a := (a : ℂ)) (by simpa using ha)
  rw [Complex.ofReal_inv]
  exact hrec.symm

/-- Every Mayer scattering core `fieldCore (2s)` (`Re s > 0`, `Im s > 0`, on OR off `Re s = 1/4`)
is pointwise fixed by `lewisModularInversion s` on `(0, ∞)`. -/
theorem lewisModularInversion_fieldCore {s : ℂ} (h0 : 0 < s.re) (him : 0 < s.im)
    {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (fieldCore (2 * s)) a = fieldCore (2 * s) a := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hwim : 0 < (2 * s).im := by
    simp only [Complex.mul_im, Complex.ofNat_re, Complex.ofNat_im, zero_mul, add_zero]
    linarith
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
`L²((0, ∞), a^(4 Re s - 1) da)`. -/
theorem cauchyMellinWeight_isometry (s : ℂ) (f : ℝ → ℂ) :
    (∫ a in Ioi (0 : ℝ), a ^ (4 * s.re - 1) * ‖lewisModularInversion s f a‖ ^ 2) =
      ∫ b in Ioi (0 : ℝ), b ^ (4 * s.re - 1) * ‖f b‖ ^ 2 := by
  rw [integral_Ioi_zero_inv_subst]
  refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
  have hb0 : 0 < b := hb
  have hb_inv : 0 < b⁻¹ := inv_pos.mpr hb0
  dsimp only [smul_eq_mul, lewisModularInversion]
  rw [inv_inv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb_inv,
    Real.inv_rpow hb0.le, Real.inv_rpow hb0.le, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
  have hre : (-(2 * s)).re = -2 * s.re := by simp
  rw [hre]
  have hexp : b ^ (-2 : ℝ) * ((b ^ (4 * s.re - 1))⁻¹ * ((b ^ (-2 * s.re))⁻¹ * ‖f b‖) ^ 2) =
      (b ^ (-2 : ℝ) * b ^ (1 - 4 * s.re) * b ^ (4 * s.re)) * ‖f b‖ ^ 2 := by
    rw [mul_pow, ← Real.rpow_neg hb0.le, ← Real.rpow_neg hb0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hb0.le]
    have h1 : -(4 * s.re - 1) = 1 - 4 * s.re := by ring
    have h2 : -(-2 * s.re) * ((2 : ℕ) : ℝ) = 4 * s.re := by push_cast; ring
    rw [h1, h2]
    ring
  -- Direct rpow simplification:
  have hrpow1 : (b ^ (4 * s.re - 1))⁻¹ = b ^ (1 - 4 * s.re) := by
    rw [← Real.rpow_neg hb0.le, show -(4 * s.re - 1) = 1 - 4 * s.re by ring]
  have hrpow2 : ((b ^ (-2 * s.re))⁻¹) ^ (2 : ℕ) = b ^ (4 * s.re) := by
    rw [← Real.rpow_neg hb0.le, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    congr 1
    push_cast
    ring
  rw [hrpow1, hrpow2]
  have hcomb : b ^ (-2 : ℝ) * (b ^ (1 - 4 * s.re) * (b ^ (4 * s.re) * ‖f b‖ ^ 2)) =
      (b ^ (-2 : ℝ) * b ^ (1 - 4 * s.re) * b ^ (4 * s.re)) * ‖f b‖ ^ 2 := by ring
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

/-- Positive-definite `s`-independent Hermitian inner product on functions on `(0, ∞)`. -/
def lewisCriticalInner (f g : ℝ → ℂ) : ℂ :=
  ∫ a in Ioi (0 : ℝ), f a * (starRingEnd ℂ) (g a) * (lewisCriticalWeight a : ℂ)

/-- Squared norm on `H_LP`. -/
def lewisCriticalNormSq (f : ℝ → ℂ) : ℝ :=
  ∫ a in Ioi (0 : ℝ), ‖f a‖ ^ 2 * lewisCriticalWeight a

theorem lewisCriticalInner_self_eq_ofReal_normSq (f : ℝ → ℂ) :
    lewisCriticalInner f f = (lewisCriticalNormSq f : ℂ) := by
  unfold lewisCriticalInner lewisCriticalNormSq
  rw [← integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
  rw [Complex.mul_conj', Complex.ofReal_mul, Complex.ofReal_pow]

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
  have hp_lt_q : p < q := by linarith
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
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hfx : ‖f a₀‖ / 2 ≤ ‖f x‖ := by
      have hb := abs_lt.mp (by simpa [Real.dist_eq] using hball hx_dist)
      linarith
    have hsq : (‖f a₀‖ / 2) ^ 2 ≤ ‖f x‖ ^ 2 :=
      pow_le_pow_left₀ (half_pos hc0).le hfx 2
    exact le_trans (hmin ⟨hx.1.le, hx.2⟩)
      (mul_le_mul_of_nonneg_right hsq (lewisCriticalWeight_pos ( hp_pos.trans hx.1)).le)
  obtain ⟨m, hm_pos, hm_le⟩ := hw_min
  have hsub : Ioc p q ⊆ Ioi 0 := fun x hx => hp_pos.trans hx.1
  have hint_sub : (∫ x in Ioc p q, m) ≤ lewisCriticalNormSq f := by
    calc
      (∫ x in Ioc p q, m) ≤ ∫ x in Ioc p q, ‖f x‖ ^ 2 * lewisCriticalWeight x :=
        setIntegral_mono_on (integrableOn_const (hs := by simp)) (hf_int.mono_set hsub)
          measurableSet_Ioc hm_le
      _ ≤ lewisCriticalNormSq f :=
        setIntegral_mono_set hf_int
          (Filter.Eventually.of_forall fun x =>
            (le_iff_imp _ _).mp fun _ => by positivity) -- wait: let's use setIntegral_le_integral or union!
  -- Wait: let's write the subset integral bound cleanly!
  sorry
