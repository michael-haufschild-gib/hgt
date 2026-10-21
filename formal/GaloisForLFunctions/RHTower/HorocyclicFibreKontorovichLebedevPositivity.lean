import GaloisForLFunctions.RHTower.HorocyclicWhittakerEigenfunctionFibreRelation
import GaloisForLFunctions.RHTower.KontorovichLebedevInversion

/-!
# Positivity of the horocyclic fibres by Kontorovich–Lebedev inversion

Fix `ξ ≠ 0`, `κ = 2π|ξ|` and the Whittaker functions `W_τ(y) = √y K_{iτ}(κy)`.  For a smooth `G` with
compact support in `(0, ∞)` put `c(τ) = ∫ G(y) W_τ(y) dy/y²` (`whittakerPairing`).

* **Expansion** (`whittaker_expansion`).  `π² G(y) = ∫ τ sinh(πτ) c(τ) W_τ(y) dτ`: the
  Kontorovich–Lebedev inversion (corpus) for `f(t) = G(t/κ) t^{−3/2}`, whose transform is
  `κ^{−1/2} c(τ)` (`klTransform_klTestOf`).
* **Fibre positivity** (`re_fibreForm_nonneg`).  If the Selberg transform is nonnegative on the
  critical line, the fibre form
  `B_ξ(G) = ∫∫ K_ξ(y, y') G(y) Ḡ(y') dy dy'/(y²y'²)` has `Re B_ξ(G) ≥ 0`: with the fibre
  eigen-relation `∫ K_ξ(y, ·) W_τ dy'/y'² = h(½ + iτ) W_τ(y)` and Fubini,
  `B_ξ(G) = π^{−2} ∫ τ sinh(πτ) h(½ + iτ) |c(τ)|² dτ`.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real ContDiff

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open MaassWhittaker KontorovichLebedev

/-! ### The Kontorovich–Lebedev test of a fibre -/

/-- `f(t) = G(t/κ) t^{−3/2}`. -/
def klTestOf (κ : ℝ) (G : ℝ → ℂ) (t : ℝ) : ℂ := G (t / κ) * (((Real.sqrt t ^ 3)⁻¹ : ℝ) : ℂ)

/-- The Whittaker pairing `c(τ) = ∫ G(y) W_τ(y) dy/y²`. -/
def whittakerPairing (κ : ℝ) (G : ℝ → ℂ) (τ : ℝ) : ℂ :=
  ∫ y, G y * whittakerW κ ((τ : ℂ) * I) y * (((y ^ 2)⁻¹ : ℝ) : ℂ)

/-- The Whittaker functions of imaginary order are real. -/
theorem conj_whittakerW (κ τ y : ℝ) :
    conj (whittakerW κ ((τ : ℂ) * I) y) = whittakerW κ ((τ : ℂ) * I) y := by
  rw [whittakerW, map_mul, Complex.conj_ofReal, conj_besK_I_mul]

section Test

variable {κ : ℝ} (hκ : 0 < κ) {G : ℝ → ℂ} (hG : IsKLTest G)
include hκ hG

omit hG in
theorem klTestOf_eq_zero_of_lt {a b : ℝ} (hsupp : tsupport G ⊆ Icc a b) {t : ℝ} (ht : t < κ * a) :
    klTestOf κ G t = 0 := by
  rw [klTestOf, eq_zero_of_tsupport_subset hsupp (fun h => by
    have := h.1; rw [le_div_iff₀ hκ] at this; linarith), zero_mul]

theorem isKLTest_klTestOf : IsKLTest (klTestOf κ G) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := hG.exists_Icc
  have hz : ∀ t, t ∉ Icc (κ * a) (κ * b) → klTestOf κ G t = 0 := by
    intro t ht
    rw [klTestOf, eq_zero_of_tsupport_subset hsupp (fun h => ht ⟨?_, ?_⟩), zero_mul]
    · have := h.1; rw [le_div_iff₀ hκ] at this; linarith
    · have := h.2; rw [div_le_iff₀ hκ] at this; linarith
  refine ⟨?_, HasCompactSupport.intro isCompact_Icc hz, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge 0 t with ht | ht
    · have h1 : ContDiffAt ℝ ∞ (fun t => G (t / κ)) t :=
        hG.smooth.comp_contDiffAt t (contDiffAt_id.div_const κ)
      have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => (((Real.sqrt t ^ 3)⁻¹ : ℝ) : ℂ)) t :=
        Complex.ofRealCLM.contDiff.comp_contDiffAt t
          (((Real.contDiffAt_sqrt ht.ne').pow 3).inv (pow_ne_zero 3 (Real.sqrt_pos.mpr ht).ne'))
      exact h1.mul h2
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show t < κ * a by nlinarith)] with s hs
      exact klTestOf_eq_zero_of_lt hκ hsupp hs
  · have hsub : tsupport (klTestOf κ G) ⊆ Icc (κ * a) (κ * b) :=
      closure_minimal (fun t ht => by by_contra h; exact ht (hz t h)) isClosed_Icc
    exact fun t ht => lt_of_lt_of_le (mul_pos hκ ha) (hsub ht).1

omit hκ in
/-- `G` vanishes off `(0, ∞)`. -/
theorem isKLTest_apply_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : G y = 0 := by
  obtain ⟨a, b, ha, -, hsupp⟩ := hG.exists_Icc
  exact eq_zero_of_tsupport_subset hsupp (fun h => by linarith [h.1])

/-- **The transform of the test is the Whittaker pairing.**  `KL[f](τ) = κ^{−1/2} c(τ)`. -/
theorem klTransform_klTestOf (τ : ℝ) :
    klTransform (klTestOf κ G) τ = (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * whittakerPairing κ G τ := by
  have h := Measure.integral_comp_mul_left
    (fun t : ℝ => klTestOf κ G t * modifiedBesselKOrder t ((τ : ℂ) * I)) κ
  rw [abs_inv, abs_of_pos hκ, Complex.real_smul] at h
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hpt : ∀ y : ℝ, klTestOf κ G (κ * y) * modifiedBesselKOrder (κ * y) ((τ : ℂ) * I) =
      (((Real.sqrt κ ^ 3)⁻¹ : ℝ) : ℂ) *
        (G y * whittakerW κ ((τ : ℂ) * I) y * (((y ^ 2)⁻¹ : ℝ) : ℂ)) := by
    intro y
    rcases le_or_gt y 0 with hy | hy
    · simp [klTestOf, whittakerW, isKLTest_apply_eq_zero_of_nonpos hG hy,
        mul_div_cancel_left₀ y hκ.ne']
    · have hr : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
      have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
      have hsC : (Real.sqrt κ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hrC : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [klTestOf, whittakerW, mul_div_cancel_left₀ y hκ.ne', Real.sqrt_mul hκ.le,
        show y ^ 2 = Real.sqrt y ^ 4 by
          rw [show Real.sqrt y ^ 4 = (Real.sqrt y ^ 2) ^ 2 by ring, hy2]]
      simp only [besK]
      push_cast
      field_simp
  simp only [hpt] at h
  rw [integral_const_mul] at h
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hsC : (Real.sqrt κ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h2 : klTransform (klTestOf κ G) τ =
      (κ : ℂ) * ((((Real.sqrt κ ^ 3)⁻¹ : ℝ) : ℂ) * whittakerPairing κ G τ) := by
    rw [whittakerPairing, h, klTransform]
    push_cast
    field_simp
  have hκs : (κ : ℂ) = (Real.sqrt κ : ℂ) ^ 2 := by rw [← Complex.ofReal_pow, hsq]
  rw [h2, hκs]
  push_cast
  field_simp

/-- **The Whittaker expansion.**  `π² G(y) = ∫ τ sinh(πτ) c(τ) W_τ(y) dτ` for `y > 0`. -/
theorem whittaker_expansion {y : ℝ} (hy : 0 < y) :
    ∫ τ : ℝ, (τ : ℂ) * Real.sinh (π * τ) * whittakerPairing κ G τ * whittakerW κ ((τ : ℂ) * I) y =
      (π : ℂ) ^ 2 * G y := by
  have h := kontorovichLebedev_inversion (isKLTest_klTestOf hκ hG) (mul_pos hκ hy)
  simp only [klTransform_klTestOf hκ hG] at h
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hr : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hκ2 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hsC : (Real.sqrt κ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hrC : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hfun : (fun τ : ℝ => (τ : ℂ) * Real.sinh (π * τ) * whittakerPairing κ G τ *
      whittakerW κ ((τ : ℂ) * I) y) = fun τ : ℝ => ((Real.sqrt κ * Real.sqrt y : ℝ) : ℂ) *
        ((τ : ℂ) * Real.sinh (Real.pi * τ) * kIm (κ * y) τ *
          ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * whittakerPairing κ G τ)) := by
    funext τ
    rw [whittakerW, kIm]
    simp only [besK]
    push_cast
    field_simp
  rw [hfun, integral_const_mul, h, klTestOf, mul_div_cancel_left₀ y hκ.ne',
    Real.sqrt_mul hκ.le]
  rw [← hκ2, ← hy2]
  simp only [Real.sqrt_sq hs.le, Real.sqrt_sq hr.le]
  push_cast
  field_simp

/-- `c(τ) = √κ · KL[f](τ)`. -/
theorem whittakerPairing_eq_sqrt_mul_klTransform (τ : ℝ) :
    whittakerPairing κ G τ = ((Real.sqrt κ : ℝ) : ℂ) * klTransform (klTestOf κ G) τ := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  rw [klTransform_klTestOf hκ hG, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne',
    Complex.ofReal_one, one_mul]

theorem continuous_whittakerPairing : Continuous (whittakerPairing κ G) := by
  rw [show whittakerPairing κ G = fun τ => ((Real.sqrt κ : ℝ) : ℂ) * klTransform (klTestOf κ G) τ
    from funext (whittakerPairing_eq_sqrt_mul_klTransform hκ hG)]
  exact continuous_const.mul (continuous_klTransform (isKLTest_klTestOf hκ hG))

/-- The conjugated expansion `Ḡ(y) = π^{−2} ∫ τ sinh(πτ) c̄(τ) W_τ(y) dτ` (`W_τ` is real). -/
theorem conj_eq_whittaker_expansion {y : ℝ} (hy : 0 < y) :
    conj (G y) = ((π : ℂ) ^ 2)⁻¹ * ∫ τ : ℝ, (τ : ℂ) * Real.sinh (π * τ) *
      conj (whittakerPairing κ G τ) * whittakerW κ ((τ : ℂ) * I) y := by
  have hπ : ((π : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (pow_pos Real.pi_pos 2).ne'
  have h := congrArg conj (whittaker_expansion hκ hG hy)
  rw [← integral_conj, map_mul, map_pow, Complex.conj_ofReal] at h
  simp only [map_mul, Complex.conj_ofReal, conj_whittakerW] at h
  rw [h, inv_mul_cancel_left₀ hπ]

end Test

/-! ### Uniform spectral bounds -/

/-- The spectral integrand of a Kontorovich–Lebedev test, uniformly in `x`:
`|τ| e^{π|τ|} |K_{iτ}(x)| |KL[f](τ)| ≤ C (|log x| + 4) (1 + τ²)⁻¹`. -/
theorem exists_bound_spectral_uniform {f : ℝ → ℂ} (hf : IsKLTest f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ y : ℝ,
      |y| * Real.exp (Real.pi * |y|) * ‖kIm x y‖ * ‖klTransform f y‖ ≤
        C * (|Real.log x| + 4) * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C₄, hC₄, hb⟩ := exists_bound_klTransform hf 4
  refine ⟨16 * (2 * Real.exp 2 * C₄), by positivity, fun x hx y => ?_⟩
  set K : ℝ := 2 * Real.exp 2 * (|Real.log x| + 4) * C₄
  set t := |y|
  have ht : 0 ≤ t := abs_nonneg y
  have hk := norm_kIm_le hx y
  have hg := hb y
  have hy8 : y ^ (2 * 4) = t ^ 8 := by
    simp only [t]; rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_mul, sq_abs]
  have hpos8 : 0 < 1 + y ^ (2 * 4) := by rw [hy8]; positivity
  have hy2 : y ^ 2 = t ^ 2 := by simp only [t]; rw [sq_abs]
  rw [hy8] at hg hpos8
  have he : Real.exp (Real.pi * t) * (Real.exp (-(Real.pi * t) / 2) *
      Real.exp (-(Real.pi * t) / 2)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hk' : ‖kIm x y‖ ≤ Real.exp 2 * (|Real.log x| + 4) * (1 + t) *
      Real.exp (-(Real.pi * t) / 2) := by
    refine hk.trans (le_of_le_of_eq (b := Real.exp 2 * ((|Real.log x| + 4) * (1 + t)) *
      Real.exp (-(Real.pi * t) / 2)) ?_ (by ring))
    gcongr
    have := log_two_add_abs_le y
    nlinarith [abs_nonneg (Real.log x)]
  have hg' : ‖klTransform f y‖ ≤ C₄ * (2 * (1 + t)) * Real.exp (-(Real.pi * t) / 2) /
      (1 + t ^ 8) := by
    refine hg.trans ?_
    gcongr
    linarith [log_two_add_abs_le y]
  have hprod : |y| * Real.exp (Real.pi * |y|) * ‖kIm x y‖ * ‖klTransform f y‖ ≤
      K * ((1 + t) ^ 3 / (1 + t ^ 8)) := by
    calc |y| * Real.exp (Real.pi * |y|) * ‖kIm x y‖ * ‖klTransform f y‖
        ≤ t * Real.exp (Real.pi * t) * (Real.exp 2 * (|Real.log x| + 4) * (1 + t) *
            Real.exp (-(Real.pi * t) / 2)) * (C₄ * (2 * (1 + t)) *
              Real.exp (-(Real.pi * t) / 2) / (1 + t ^ 8)) := by gcongr
      _ = K * (t * (1 + t) ^ 2 / (1 + t ^ 8)) *
            (Real.exp (Real.pi * t) * (Real.exp (-(Real.pi * t) / 2) *
              Real.exp (-(Real.pi * t) / 2))) := by simp only [K]; ring
      _ = K * (t * (1 + t) ^ 2 / (1 + t ^ 8)) := by rw [he, mul_one]
      _ ≤ K * ((1 + t) ^ 3 / (1 + t ^ 8)) := by
          gcongr
          nlinarith [sq_nonneg (1 + t)]
  refine hprod.trans ?_
  rw [hy2]
  have h16 := one_add_pow_three_mul_le ht
  have hK : 0 ≤ K := by positivity
  rw [div_eq_mul_inv]
  have hinv : (1 + t) ^ 3 * (1 + t ^ 8)⁻¹ ≤ 16 * (1 + t ^ 2)⁻¹ := by
    rw [mul_inv_le_iff₀ hpos8, mul_comm (16 : ℝ), mul_assoc, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    linarith
  calc K * ((1 + t) ^ 3 * (1 + t ^ 8)⁻¹) ≤ K * (16 * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv hK
    _ = 16 * (2 * Real.exp 2 * C₄) * (|Real.log x| + 4) * (1 + t ^ 2)⁻¹ := by
        simp only [K]; ring

section Bound

variable {κ : ℝ} (hκ : 0 < κ) {G : ℝ → ℂ} (hG : IsKLTest G)
include hκ hG

/-- `|τ sinh(πτ) c(τ) W_τ(y)| ≤ C √(κy) (|log κy| + 4) (1 + τ²)⁻¹`. -/
theorem exists_bound_expansion : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → ∀ τ : ℝ,
    ‖(τ : ℂ) * Real.sinh (π * τ) * whittakerPairing κ G τ * whittakerW κ ((τ : ℂ) * I) y‖ ≤
      C * Real.sqrt (κ * y) * (|Real.log (κ * y)| + 4) * (1 + τ ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_bound_spectral_uniform (isKLTest_klTestOf hκ hG)
  refine ⟨C, hC, fun y hy τ => ?_⟩
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hb' := hb (κ * y) (mul_pos hκ hy) τ
  rw [whittakerPairing_eq_sqrt_mul_klTransform hκ hG, whittakerW]
  simp only [besK]
  rw [show modifiedBesselKOrder (κ * y) ((τ : ℂ) * I) = kIm (κ * y) τ from rfl]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg κ), abs_of_nonneg (Real.sqrt_nonneg y)]
  have hsinh : |Real.sinh (π * τ)| ≤ Real.exp (π * |τ|) := by
    have := norm_sinh_le_exp_abs (π * τ)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  have hsq : Real.sqrt (κ * y) = Real.sqrt κ * Real.sqrt y := Real.sqrt_mul hκ.le y
  calc |τ| * |Real.sinh (π * τ)| * (Real.sqrt κ * ‖klTransform (klTestOf κ G) τ‖) *
        (Real.sqrt y * ‖kIm (κ * y) τ‖)
      ≤ |τ| * Real.exp (π * |τ|) * (Real.sqrt κ * ‖klTransform (klTestOf κ G) τ‖) *
        (Real.sqrt y * ‖kIm (κ * y) τ‖) := by gcongr
    _ = Real.sqrt (κ * y) * (|τ| * Real.exp (Real.pi * |τ|) * ‖kIm (κ * y) τ‖ *
          ‖klTransform (klTestOf κ G) τ‖) := by rw [hsq]; ring
    _ ≤ Real.sqrt (κ * y) * (C * (|Real.log (κ * y)| + 4) * (1 + τ ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hb' (Real.sqrt_nonneg _)
    _ = _ := by ring

end Bound

/-! ### Measurability, kernel bounds and a Fubini lemma -/

theorem norm_horocyclicPhase (ξ x : ℝ) : ‖horocyclicPhase ξ x‖ = 1 := by
  rw [horocyclicPhase, Complex.norm_exp]
  simp

/-- `(y, τ) ↦ W_τ(y)` is measurable. -/
theorem measurable_whittakerW (κ : ℝ) :
    Measurable fun p : ℝ × ℝ => whittakerW κ ((p.2 : ℂ) * I) p.1 := by
  have h : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ =>
      besselOrderKernel (κ * q.1.1) ((q.1.2 : ℂ) * I) q.2 :=
    (by unfold besselOrderKernel; fun_prop : Continuous _).stronglyMeasurable
  exact (by fun_prop : Measurable fun p : ℝ × ℝ => ((Real.sqrt p.1 : ℝ) : ℂ)).mul
    (h.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

theorem measurable_horocyclicFibreKernel {k : ℝ → ℝ} (hkc : Continuous k) (ξ y : ℝ) :
    Measurable fun y' => horocyclicFibreKernel k ξ y y' := by
  have hp : Measurable fun p : ℝ × ℝ => pairUCoord p.2 y 0 p.1 := by unfold pairUCoord; fun_prop
  have h : StronglyMeasurable fun p : ℝ × ℝ =>
      (k (pairUCoord p.2 y 0 p.1) : ℂ) * horocyclicPhase ξ p.2 :=
    ((Complex.measurable_ofReal.comp (hkc.measurable.comp hp)).mul
      ((by unfold horocyclicPhase; fun_prop : Continuous (horocyclicPhase ξ)).measurable.comp
        measurable_snd)).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- `y ↦ √(κy) (|log κy| + 4)` is continuous on `(0, ∞)`. -/
theorem continuousOn_expansionWeight {κ : ℝ} (hκ : 0 < κ) :
    ContinuousOn (fun y : ℝ => Real.sqrt (κ * y) * (|Real.log (κ * y)| + 4)) (Ioi 0) :=
  (by fun_prop : Continuous fun y : ℝ => Real.sqrt (κ * y)).continuousOn.mul
    ((Real.continuousOn_log.comp (by fun_prop : Continuous fun y : ℝ => κ * y).continuousOn
      fun y hy => (mul_pos hκ hy).ne').abs.add continuousOn_const)

theorem mul_sinh_pi_mul_nonneg (τ : ℝ) : 0 ≤ τ * Real.sinh (π * τ) := by
  rcases le_total 0 τ with h | h
  · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr (by positivity))
  · have hs := Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h)
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (neg_nonneg.mpr hs)]

/-- Functions vanishing on `(−∞, 0]` integrate over `(0, ∞)`. -/
theorem integral_eq_setIntegral_Ioi {f : ℝ → ℂ} (hf : ∀ y ≤ 0, f y = 0) :
    ∫ y, f y = ∫ y in Ioi 0, f y :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hf y (not_lt.mp hy)).symm

/-- Fubini on `(0, ∞) × ℝ` for a measurable integrand vanishing for `y ∉ [lo, hi]` and dominated
there by `φ(y) (1 + τ²)⁻¹`, `φ` continuous. -/
theorem integral_Ioi_integral_comm {F : ℝ → ℝ → ℂ} (hF : Measurable (Function.uncurry F)) {lo hi : ℝ}
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc lo hi))
    (hb : ∀ y ∈ Icc lo hi, ∀ τ, ‖F y τ‖ ≤ φ y * (1 + τ ^ 2)⁻¹)
    (hz : ∀ y, 0 < y → y ∉ Icc lo hi → ∀ τ, F y τ = 0) :
    ∫ y in Ioi 0, ∫ τ, F y τ = ∫ τ, ∫ y in Ioi 0, F y τ := by
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hg : Integrable (fun p : ℝ × ℝ => (Icc lo hi).indicator (fun _ => max P 0) p.1 *
      (1 + p.2 ^ 2)⁻¹) ((volume.restrict (Ioi 0)).prod volume) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp) (by simp))).restrict integrable_inv_one_add_sq
  refine integral_integral_swap (hg.mono' hF.aestronglyMeasurable ?_)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)]
    with ⟨y, τ⟩ hy
  simp only [Function.uncurry_apply_pair]
  by_cases hyI : y ∈ Icc lo hi
  · rw [indicator_of_mem hyI]
    have hPy := hP y hyI
    rw [Real.norm_eq_abs] at hPy
    exact (hb y hyI τ).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hPy.trans
      (le_max_left _ _))) (by positivity))
  · rw [indicator_of_notMem hyI, zero_mul, hz y hy hyI τ, norm_zero]

section Kernel

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : DeckPointPair.KernelSupport k R)
include hkc hkR

omit hkc in
/-- The fibre kernel vanishes once `|log y − log y'| > 2 arsinh √R⁺`. -/
theorem horocyclicFibreKernel_eq_zero {ξ y y' : ℝ} (hy : 0 < y) (hy' : 0 < y')
    (h : 2 * Real.arsinh (Real.sqrt (max R 0)) < |Real.log y - Real.log y'|) :
    horocyclicFibreKernel k ξ y y' = 0 := by
  have hs := lt_sinh_sq_of_lt_abs h
  rw [← sq_sub_div_eq_sinh_sq hy hy'] at hs
  rw [horocyclicFibreKernel]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  have hle : (y - y') ^ 2 / (4 * y * y') ≤ pairUCoord t y 0 y' := by
    rw [pairUCoord]
    gcongr
    nlinarith [sq_nonneg (t - 0)]
  simp [hkR _ (hs.trans_le hle)]

omit hkc in
/-- The slice kernel `t ↦ k(u(t + iy, iy'))` vanishes for `|t| > 2√(R⁺ y y')`. -/
theorem pairKernel_slice_eq_zero {y y' t : ℝ} (hy : 0 < y) (hy' : 0 < y')
    (ht : 2 * Real.sqrt (max R 0 * (y * y')) < |t|) : k (pairUCoord t y 0 y') = 0 := by
  have hL : 0 ≤ 2 * Real.sqrt (max R 0 * (y * y')) := by positivity
  have hL2 : (2 * Real.sqrt (max R 0 * (y * y'))) ^ 2 = 4 * (max R 0 * (y * y')) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have ht2 : (2 * Real.sqrt (max R 0 * (y * y'))) ^ 2 < t ^ 2 := by
    rw [← sq_abs t]; exact pow_lt_pow_left₀ ht hL two_ne_zero
  have hm : R * (y * y') ≤ max R 0 * (y * y') :=
    mul_le_mul_of_nonneg_right (le_max_left R 0) (mul_pos hy hy').le
  refine hkR _ ?_
  rw [pairUCoord, lt_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (y - y')]

omit hkc in
/-- `|K_ξ(y, y')| ≤ 4M √(R⁺ y y')`. -/
theorem norm_horocyclicFibreKernel_le {M : ℝ} (hM : ∀ u, 0 ≤ u → |k u| ≤ M) {ξ y y' : ℝ}
    (hy : 0 < y) (hy' : 0 < y') :
    ‖horocyclicFibreKernel k ξ y y'‖ ≤ 4 * Real.sqrt (max R 0 * (y * y')) * M := by
  set L := 2 * Real.sqrt (max R 0 * (y * y')) with hLdef
  have hL : 0 ≤ L := by positivity
  have hb : ∀ t, ‖(k (pairUCoord t y 0 y') : ℂ) * horocyclicPhase ξ t‖ ≤
      (Icc (-L) L).indicator (fun _ => M) t := by
    intro t
    rw [norm_mul, norm_horocyclicPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : t ∈ Icc (-L) L
    · rw [indicator_of_mem ht]
      exact hM _ (by rw [pairUCoord]; positivity)
    · rw [indicator_of_notMem ht]
      have hlt : L < |t| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [pairKernel_slice_eq_zero hkR hy hy' hlt, abs_zero]
  calc ‖horocyclicFibreKernel k ξ y y'‖ ≤ ∫ t, (Icc (-L) L).indicator (fun _ => M) t :=
        norm_integral_le_of_norm_le ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (by simp) (by simp))) (Eventually.of_forall hb)
    _ = 4 * Real.sqrt (max R 0 * (y * y')) * M := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul, hLdef]
        ring

theorem measurable_selbergTransform_critical :
    Measurable fun τ : ℝ => DeckPointPair.selbergTransform k (1 / 2 + τ * I) := by
  simp_rw [selbergTransform_critical_eq_ofReal hkc hkR]
  have h : StronglyMeasurable fun p : ℝ × ℝ => abelTransform k p.2 * Real.cos (p.1 * p.2) :=
    (((continuous_abelTransform hkc hkR).comp continuous_snd).mul
      (by fun_prop)).stronglyMeasurable
  exact Complex.measurable_ofReal.comp h.integral_prod_right'.measurable

/-- `|h_k(½ + iτ)| ≤ ∫ |𝒜k|`. -/
theorem norm_selbergTransform_critical_le (τ : ℝ) :
    ‖DeckPointPair.selbergTransform k (1 / 2 + τ * I)‖ ≤ ∫ v, |abelTransform k v| := by
  rw [selbergTransform_critical_eq_ofReal hkc hkR, Complex.norm_real]
  refine norm_integral_le_of_norm_le ((continuous_abelTransform hkc hkR).integrable_of_hasCompactSupport
    (hasCompactSupport_abelTransform hkR)).abs (Eventually.of_forall fun v => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

end Kernel

/-! ### The fibre form and its spectral expansion -/

/-- The fibre form `B_ξ(G) = ∫∫ K_ξ(y, y') G(y) Ḡ(y') dy dy'/(y²y'²)`. -/
def horocyclicFibreForm (k : ℝ → ℝ) (ξ : ℝ) (G : ℝ → ℂ) : ℂ :=
  ∫ y, ∫ y', (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ : ℝ) : ℂ) * horocyclicFibreKernel k ξ y y' * G y *
    conj (G y')

section Positivity

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : DeckPointPair.KernelSupport k R)
  {ξ : ℝ} (hξ : ξ ≠ 0) {G : ℝ → ℂ} (hG : IsKLTest G)
include hkc hkR hξ hG

/-- The inner integral of the fibre form: for `y > 0`,
`∫ K_ξ(y, y') G(y) Ḡ(y') dy'/(y²y'²) = y^{−2} G(y) π^{−2} ∫ W_τ(y) h(½ + iτ) τ sinh(πτ) c̄(τ) dτ`. -/
theorem integral_horocyclicFibreForm_inner {y : ℝ} (hy : 0 < y) :
    ∫ y', (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ : ℝ) : ℂ) * horocyclicFibreKernel k ξ y y' * G y * conj (G y') =
      (((y ^ 2)⁻¹ : ℝ) : ℂ) * G y * (((π : ℂ) ^ 2)⁻¹ * ∫ τ : ℝ,
        whittakerW (2 * π * |ξ|) ((τ : ℂ) * I) y * DeckPointPair.selbergTransform k (1 / 2 + τ * I) *
          ((τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing (2 * π * |ξ|) G τ))) := by
  have hκ : 0 < 2 * π * |ξ| := mul_pos (by positivity) (abs_pos.mpr hξ)
  have heig := fun τ : ℝ => integral_horocyclicFibreKernel_mul_whittakerW hkc hkR hξ τ hy
  generalize hκdef : 2 * π * |ξ| = κ at hκ heig ⊢
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  obtain ⟨C, hC, hE⟩ := exists_bound_expansion hκ hG
  set V := 2 * Real.arsinh (Real.sqrt (max R 0)) with hVdef
  have hV0 : 0 ≤ V := mul_nonneg zero_le_two (Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _))
  set F : ℝ → ℝ → ℂ := fun y' τ => (((y' ^ 2)⁻¹ : ℝ) : ℂ) * horocyclicFibreKernel k ξ y y' *
    whittakerW κ ((τ : ℂ) * I) y' * ((τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing κ G τ))
    with hFdef
  have hlo : 0 < y * Real.exp (-V) := by positivity
  have hsub : Icc (y * Real.exp (-V)) (y * Real.exp V) ⊆ Ioi 0 := fun y' h => hlo.trans_le h.1
  -- `Ḡ(y')` expanded in Whittaker functions
  have hstep : ∀ y' ∈ Ioi (0 : ℝ), (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ : ℝ) : ℂ) * horocyclicFibreKernel k ξ y y' *
      G y * conj (G y') = ((((y ^ 2)⁻¹ : ℝ) : ℂ) * G y * ((π : ℂ) ^ 2)⁻¹) * ∫ τ, F y' τ := by
    intro y' hy'
    have hF : ∫ τ, F y' τ = (((y' ^ 2)⁻¹ : ℝ) : ℂ) * horocyclicFibreKernel k ξ y y' *
        ∫ τ : ℝ, (τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing κ G τ) *
          whittakerW κ ((τ : ℂ) * I) y' := by
      rw [← integral_const_mul]
      congr 1 with τ
      simp only [hFdef]
      ring
    rw [conj_eq_whittaker_expansion hκ hG hy', hF]
    push_cast
    ring
  -- Fubini in `(y', τ)`
  have hFm : Measurable (Function.uncurry F) :=
    (((by fun_prop : Measurable fun p : ℝ × ℝ => (((p.1 ^ 2)⁻¹ : ℝ) : ℂ)).mul
      ((measurable_horocyclicFibreKernel hkc ξ y).comp measurable_fst)).mul
        (measurable_whittakerW κ)).mul
      (((by fun_prop : Continuous fun τ : ℝ => (τ : ℂ) * Real.sinh (π * τ)).mul
        (Complex.continuous_conj.comp (continuous_whittakerPairing hκ hG))).measurable.comp
          measurable_snd)
  have hφ : ContinuousOn (fun y' => (y' ^ 2)⁻¹ * (4 * Real.sqrt (max R 0 * (y * y')) * M) *
      (C * (Real.sqrt (κ * y') * (|Real.log (κ * y')| + 4))))
      (Icc (y * Real.exp (-V)) (y * Real.exp V)) :=
    (((continuous_pow 2).continuousOn.inv₀ fun y' h => pow_ne_zero 2 (hsub h).ne').mul
      (by fun_prop : Continuous fun y' : ℝ => 4 * Real.sqrt (max R 0 * (y * y')) * M).continuousOn).mul
      (continuousOn_const.mul ((continuousOn_expansionWeight hκ).mono hsub))
  have hb : ∀ y' ∈ Icc (y * Real.exp (-V)) (y * Real.exp V), ∀ τ, ‖F y' τ‖ ≤
      (y' ^ 2)⁻¹ * (4 * Real.sqrt (max R 0 * (y * y')) * M) *
        (C * (Real.sqrt (κ * y') * (|Real.log (κ * y')| + 4))) * (1 + τ ^ 2)⁻¹ := by
    intro y' hy' τ
    have hy'0 : 0 < y' := hsub hy'
    have hKb := norm_horocyclicFibreKernel_le hkR hM (ξ := ξ) hy hy'0
    have hEb := hE y' hy'0 τ
    have heq : ‖F y' τ‖ = (y' ^ 2)⁻¹ * ‖horocyclicFibreKernel k ξ y y'‖ *
        ‖(τ : ℂ) * Real.sinh (π * τ) * whittakerPairing κ G τ * whittakerW κ ((τ : ℂ) * I) y'‖ := by
      simp only [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg y'))]
      ring
    rw [heq]
    calc _ ≤ (y' ^ 2)⁻¹ * (4 * Real.sqrt (max R 0 * (y * y')) * M) *
          (C * Real.sqrt (κ * y') * (|Real.log (κ * y')| + 4) * (1 + τ ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  have hz : ∀ y', 0 < y' → y' ∉ Icc (y * Real.exp (-V)) (y * Real.exp V) → ∀ τ, F y' τ = 0 := by
    intro y' hy'0 hy' τ
    have hV : V < |Real.log y - Real.log y'| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hy'
      rcases hy' with h | h
      · have h' := Real.log_lt_log hy'0 h
        rw [Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp] at h'
        rw [abs_of_pos (by linarith)]; linarith
      · have h' := Real.log_lt_log (by positivity) h
        rw [Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp] at h'
        rw [abs_of_neg (by linarith)]; linarith
    simp only [hFdef, horocyclicFibreKernel_eq_zero hkR hy hy'0 hV, mul_zero, zero_mul]
  -- the eigen-relation on each Whittaker mode
  have hmode : ∀ τ : ℝ, ∫ y' in Ioi 0, F y' τ = whittakerW κ ((τ : ℂ) * I) y *
      DeckPointPair.selbergTransform k (1 / 2 + τ * I) *
        ((τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing κ G τ)) := by
    intro τ
    simp only [hFdef]
    rw [integral_mul_const, ← heig τ]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun y' _ => ?_
    rw [Complex.real_smul]
    ring
  rw [integral_eq_setIntegral_Ioi, setIntegral_congr_fun measurableSet_Ioi hstep, integral_const_mul,
    integral_Ioi_integral_comm hFm hφ hb hz]
  · simp only [hmode]
    ring
  · intro y' hy'
    rw [isKLTest_apply_eq_zero_of_nonpos hG hy', map_zero, mul_zero]

/-- **The Kontorovich–Lebedev form of the fibre.**
`B_ξ(G) = π^{−2} ∫ τ sinh(πτ) |c(τ)|² h(½ + iτ) dτ`. -/
theorem horocyclicFibreForm_eq :
    horocyclicFibreForm k ξ G = ((π : ℂ) ^ 2)⁻¹ * ∫ τ : ℝ,
      ((τ * Real.sinh (π * τ) * ‖whittakerPairing (2 * π * |ξ|) G τ‖ ^ 2 : ℝ) : ℂ) *
        DeckPointPair.selbergTransform k (1 / 2 + τ * I) := by
  have hκ : 0 < 2 * π * |ξ| := mul_pos (by positivity) (abs_pos.mpr hξ)
  have hin := fun y (hy : 0 < y) => integral_horocyclicFibreForm_inner hkc hkR hξ hG hy
  generalize hκdef : 2 * π * |ξ| = κ at hκ hin ⊢
  obtain ⟨a, b, ha, -, hsupp⟩ := hG.exists_Icc
  obtain ⟨C, hC, hE⟩ := exists_bound_expansion hκ hG
  obtain ⟨H, hH⟩ : ∃ H, ∀ τ : ℝ, ‖DeckPointPair.selbergTransform k (1 / 2 + τ * I)‖ ≤ H :=
    ⟨_, norm_selbergTransform_critical_le hkc hkR⟩
  have hGc : Continuous G := hG.smooth.continuous
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hsub : Icc a b ⊆ Ioi 0 := fun y h => ha.trans_le h.1
  set F : ℝ → ℝ → ℂ := fun y τ => (((y ^ 2)⁻¹ : ℝ) : ℂ) * G y * whittakerW κ ((τ : ℂ) * I) y *
    (DeckPointPair.selbergTransform k (1 / 2 + τ * I) *
      ((τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing κ G τ))) with hFdef
  have hstep : ∀ y ∈ Ioi (0 : ℝ), (∫ y', (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ : ℝ) : ℂ) *
      horocyclicFibreKernel k ξ y y' * G y * conj (G y')) = ((π : ℂ) ^ 2)⁻¹ * ∫ τ, F y τ := by
    intro y hy
    have hF : ∫ τ, F y τ = (((y ^ 2)⁻¹ : ℝ) : ℂ) * G y * ∫ τ : ℝ, whittakerW κ ((τ : ℂ) * I) y *
        DeckPointPair.selbergTransform k (1 / 2 + τ * I) *
          ((τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing κ G τ)) := by
      rw [← integral_const_mul]
      congr 1 with τ
      simp only [hFdef]
      ring
    rw [hin y hy, hF]
    ring
  have hFm : Measurable (Function.uncurry F) :=
    (((by fun_prop : Measurable fun p : ℝ × ℝ => (((p.1 ^ 2)⁻¹ : ℝ) : ℂ)).mul
      (hGc.measurable.comp measurable_fst)).mul (measurable_whittakerW κ)).mul
      (((measurable_selbergTransform_critical hkc hkR).mul
        ((by fun_prop : Continuous fun τ : ℝ => (τ : ℂ) * Real.sinh (π * τ)).mul
          (Complex.continuous_conj.comp (continuous_whittakerPairing hκ hG))).measurable).comp
        measurable_snd)
  have hφ : ContinuousOn (fun y => (y ^ 2)⁻¹ * ‖G y‖ * H *
      (C * (Real.sqrt (κ * y) * (|Real.log (κ * y)| + 4)))) (Icc a b) :=
    ((((continuous_pow 2).continuousOn.inv₀ fun y h => pow_ne_zero 2 (hsub h).ne').mul
      hGc.norm.continuousOn).mul continuousOn_const).mul
      (continuousOn_const.mul ((continuousOn_expansionWeight hκ).mono hsub))
  have hb : ∀ y ∈ Icc a b, ∀ τ, ‖F y τ‖ ≤ (y ^ 2)⁻¹ * ‖G y‖ * H *
      (C * (Real.sqrt (κ * y) * (|Real.log (κ * y)| + 4))) * (1 + τ ^ 2)⁻¹ := by
    intro y hy τ
    have hy0 : 0 < y := hsub hy
    have hEb := hE y hy0 τ
    have hHb := hH τ
    have heq : ‖F y τ‖ = (y ^ 2)⁻¹ * ‖G y‖ *
        ‖DeckPointPair.selbergTransform k (1 / 2 + τ * I)‖ *
        ‖(τ : ℂ) * Real.sinh (π * τ) * whittakerPairing κ G τ * whittakerW κ ((τ : ℂ) * I) y‖ := by
      simp only [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg y))]
      ring
    rw [heq]
    calc _ ≤ (y ^ 2)⁻¹ * ‖G y‖ * H *
          (C * Real.sqrt (κ * y) * (|Real.log (κ * y)| + 4) * (1 + τ ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  have hz : ∀ y, 0 < y → y ∉ Icc a b → ∀ τ, F y τ = 0 := by
    intro y _ hy τ
    simp only [hFdef, eq_zero_of_tsupport_subset hsupp hy, mul_zero, zero_mul]
  rw [horocyclicFibreForm, integral_eq_setIntegral_Ioi, setIntegral_congr_fun measurableSet_Ioi hstep,
    integral_const_mul, integral_Ioi_integral_comm hFm hφ hb hz]
  · congr 1
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    have hcI : whittakerPairing κ G τ =
        ∫ y in Ioi 0, G y * whittakerW κ ((τ : ℂ) * I) y * (((y ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [whittakerPairing, integral_eq_setIntegral_Ioi]
      intro y hy
      rw [isKLTest_apply_eq_zero_of_nonpos hG hy, zero_mul, zero_mul]
    have hc : ∫ y in Ioi 0, F y τ = whittakerPairing κ G τ *
        (DeckPointPair.selbergTransform k (1 / 2 + τ * I) *
          ((τ : ℂ) * Real.sinh (π * τ) * conj (whittakerPairing κ G τ))) := by
      nth_rewrite 1 [hcI]
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [hFdef]
      ring
    simp only
    rw [hc]
    have hcc := Complex.mul_conj' (whittakerPairing κ G τ)
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    linear_combination (DeckPointPair.selbergTransform k (1 / 2 + τ * I) * (τ : ℂ) *
      Real.sinh (π * τ)) * hcc
  · intro y hy
    simp [isKLTest_apply_eq_zero_of_nonpos hG hy]

/-- **Fibre positivity.**  If `Re h_k(½ + iτ) ≥ 0` for every `τ`, then `Re B_ξ(G) ≥ 0`. -/
theorem re_horocyclicFibreForm_nonneg
    (hh : ∀ τ : ℝ, 0 ≤ (DeckPointPair.selbergTransform k (1 / 2 + τ * I)).re) :
    0 ≤ (horocyclicFibreForm k ξ G).re := by
  rw [horocyclicFibreForm_eq hkc hkR hξ hG,
    show ((π : ℂ) ^ 2)⁻¹ = (((π ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  refine mul_nonneg (by positivity) ?_
  set f : ℝ → ℂ := fun τ => ((τ * Real.sinh (π * τ) * ‖whittakerPairing (2 * π * |ξ|) G τ‖ ^ 2 : ℝ) : ℂ) *
    DeckPointPair.selbergTransform k (1 / 2 + τ * I)
  have hre : ∀ τ, 0 ≤ (f τ).re := fun τ => by
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (mul_nonneg (mul_sinh_pi_mul_nonneg τ) (sq_nonneg _)) (hh τ)
  by_cases hint : Integrable f
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    exact integral_nonneg hre
  · rw [integral_undef hint, Complex.zero_re]

end Positivity

end GaloisForLFunctions.RHTower.MehlerFock
