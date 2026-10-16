import GaloisForLFunctions.RHTower.WeilCutEvenMeanZeroDeficit

/-!
# Holomorphic extension of the Weil function from a cut-free Nevanlinna measure

Let `(ν, c)` be the Nevanlinna data of the squared-variable Weil function `aΨ(½+a)`, `z = a²`,
of an odd Weil-positive weight, and suppose `ν` has no mass on the real cut
(`ν{ζ ≠ 1, γ < 0} = 0`).  Then
`g(z) = ∫ k(z, ζ) dν(ζ) − c`, `k(z, ζ) = (γz − 1)/(z + γ)` for `ζ ≠ 1` and `k(z, 1) = z`,
is holomorphic on `ℂ ∖ (−∞, 0]` (dominated differentiation under the integral), and
`Φ(s) = g((s − ½)²)/(s − ½)` is holomorphic on `Re s > ½`.  On the upper quadrant `Φ` agrees with the
slit continuation by the Nevanlinna representation, hence with the Weil function on `Re s > 1` by the
identity theorem.

**Consequences.**
* `exists_extension_of_cut_eq_zero`: a cut-free Nevanlinna measure gives a holomorphic extension of
  the Weil function to `Re s > ½`.
* `exists_extension_of_weilPositiveOdd_of_even_meanZero_nonneg`: odd Weil positivity together with
  nonnegativity on even mean-zero tests gives that extension (cut removal).
* `eq_vonMangoldt_and_riemannHypothesis_of_even_meanZero_nonneg`: with central nonnegativity of the
  extension on `(½, ∞)`, the weight is `Λ` and RH holds (square-root Herglotz transfer).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 Zeta23.WeilEF GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.OddResolvent
open WeilHerglotz RHTower.AtomDomination RHTower.WeilLineIntegral RHTower.WeilAtomic RHTower.EvenSector

/-! ## The explicit Nevanlinna kernel and its derivative -/

/-- `k(z, ζ) = (γz − 1)/(z + γ)` for `ζ ≠ 1`, and `z` at `ζ = 1`. -/
def nevKernel (z ζ : ℂ) : ℂ :=
  if ζ = 1 then z else ((circleOrd ζ : ℂ) * z - 1) / (z + circleOrd ζ)

/-- `∂_z k(z, ζ) = (1 + γ²)/(z + γ)²` for `ζ ≠ 1`, and `1` at `ζ = 1`. -/
def nevKernelDeriv (z ζ : ℂ) : ℂ :=
  if ζ = 1 then 1 else (1 + (circleOrd ζ : ℂ) ^ 2) / (z + circleOrd ζ) ^ 2

/-- The plane with the closed negative real axis removed. -/
def offNegAxis : Set ℂ := {z : ℂ | z.im ≠ 0 ∨ 0 < z.re}

theorem isOpen_offNegAxis : IsOpen offNegAxis :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const Complex.continuous_re)

theorem circleOrd_one : circleOrd 1 = 0 := by
  simp [circleOrd]

theorem hasDerivAt_nevKernel {z ζ : ℂ} (hz : z + circleOrd ζ ≠ 0) :
    HasDerivAt (fun w => nevKernel w ζ) (nevKernelDeriv z ζ) z := by
  by_cases h1 : ζ = 1
  · simp only [nevKernel, nevKernelDeriv, h1, if_true]
    exact hasDerivAt_id z
  · simp only [nevKernel, nevKernelDeriv, h1, if_false]
    have hn : HasDerivAt (fun w : ℂ => (circleOrd ζ : ℂ) * w - 1) (circleOrd ζ : ℂ) z := by
      simpa using ((hasDerivAt_id z).const_mul (circleOrd ζ : ℂ)).sub_const (1 : ℂ)
    have hd : HasDerivAt (fun w : ℂ => w + circleOrd ζ) 1 z := (hasDerivAt_id z).add_const _
    refine (hn.div hd hz).congr_deriv ?_
    congr 1
    ring

theorem measurable_nevKernel_circleMap (z : ℂ) :
    Measurable fun θ => nevKernel z (circleMap 0 1 θ) := by
  unfold nevKernel
  refine Measurable.ite (measurable_circleMap 0 1 (measurableSet_singleton 1)) measurable_const ?_
  have hγ : Measurable fun θ => ((circleOrd (circleMap 0 1 θ) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp measurable_angleOrd
  exact ((hγ.mul_const z).sub_const 1).div (measurable_const.add hγ)

theorem measurable_nevKernelDeriv_circleMap (z : ℂ) :
    Measurable fun θ => nevKernelDeriv z (circleMap 0 1 θ) := by
  unfold nevKernelDeriv
  refine Measurable.ite (measurable_circleMap 0 1 (measurableSet_singleton 1)) measurable_const ?_
  have hγ : Measurable fun θ => ((circleOrd (circleMap 0 1 θ) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp measurable_angleOrd
  exact ((measurable_const.add (hγ.pow_const 2))).div ((measurable_const.add hγ).pow_const 2)

/-! ## Uniform bounds on a ball -/

/-- Around a point off the negative axis, `|z + γ| ≥ ε` and `|z + γ| ≥ γ − (|z₀| + ε)` for all
`γ ≥ 0` and `z` in the ball of radius `ε`. -/
theorem exists_ball_bound_of_mem_offNegAxis {z₀ : ℂ} (hz₀ : z₀ ∈ offNegAxis) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball z₀ ε, ∀ γ : ℝ, 0 ≤ γ →
      ε ≤ ‖z + γ‖ ∧ γ - (‖z₀‖ + ε) ≤ ‖z + γ‖ := by
  have key : ∀ z : ℂ, ∀ γ : ℝ, |z.im| ≤ ‖z + γ‖ ∧ |z.re + γ| ≤ ‖z + γ‖ := fun z γ => by
    have h1 : (z + γ).im = z.im := by simp
    have h2 : (z + γ).re = z.re + γ := by simp
    exact ⟨h1 ▸ Complex.abs_im_le_norm (z + γ), h2 ▸ Complex.abs_re_le_norm (z + γ)⟩
  have hnorm : ∀ z : ℂ, ∀ ε : ℝ, z ∈ Metric.ball z₀ ε → -(‖z₀‖ + ε) ≤ z.re := by
    intro z ε hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : ‖z‖ ≤ ‖z₀‖ + ε := by
      calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + ε := by linarith
    have h2 := Complex.abs_re_le_norm z
    linarith [(abs_le.mp h2).1]
  rcases hz₀ with him | hre
  · have hε : 0 < |z₀.im| / 2 := by positivity
    refine ⟨|z₀.im| / 2, hε, fun z hz γ hγ => ?_⟩
    have hre' := hnorm z _ hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hzim : |z₀.im| / 2 ≤ |z.im| := by
      have h1 := Complex.abs_im_le_norm (z - z₀)
      rw [Complex.sub_im] at h1
      have h2 := abs_sub_abs_le_abs_sub z₀.im z.im
      rw [abs_sub_comm] at h2
      linarith
    obtain ⟨k1, k2⟩ := key z γ
    refine ⟨by linarith, ?_⟩
    calc γ - (‖z₀‖ + |z₀.im| / 2) ≤ z.re + γ := by linarith
      _ ≤ |z.re + γ| := le_abs_self _
      _ ≤ ‖z + γ‖ := k2
  · have hε : 0 < z₀.re / 2 := by positivity
    refine ⟨z₀.re / 2, hε, fun z hz γ hγ => ?_⟩
    have hre' := hnorm z _ hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hzre : z₀.re / 2 ≤ z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [Complex.sub_re] at h1
      linarith [(abs_le.mp (h1.trans hz.le)).1]
    obtain ⟨k1, k2⟩ := key z γ
    constructor
    · calc z₀.re / 2 ≤ z.re + γ := by linarith
        _ ≤ |z.re + γ| := le_abs_self _
        _ ≤ ‖z + γ‖ := k2
    · calc γ - (‖z₀‖ + z₀.re / 2) ≤ z.re + γ := by linarith [norm_nonneg z₀]
        _ ≤ |z.re + γ| := le_abs_self _
        _ ≤ ‖z + γ‖ := k2

/-- The derivative kernel is bounded by `(1 + (2R+1)²)/ε² + 8` under the ball bounds. -/
theorem norm_nevKernelDeriv_le {z ζ : ℂ} {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hγ : ζ = 1 ∨ 0 ≤ circleOrd ζ)
    (h1 : ζ ≠ 1 → ε ≤ ‖z + circleOrd ζ‖) (h2 : ζ ≠ 1 → circleOrd ζ - R ≤ ‖z + circleOrd ζ‖) :
    ‖nevKernelDeriv z ζ‖ ≤ (1 + (2 * R + 1) ^ 2) / ε ^ 2 + 8 := by
  by_cases hζ1 : ζ = 1
  · simp only [nevKernelDeriv, hζ1, if_true, norm_one]
    have : 0 ≤ (1 + (2 * R + 1) ^ 2) / ε ^ 2 := by positivity
    linarith
  · simp only [nevKernelDeriv, hζ1, if_false]
    have hγ0 : 0 ≤ circleOrd ζ := hγ.resolve_left hζ1
    have hA := h1 hζ1
    have hB := h2 hζ1
    have hN0 : 0 < ‖z + circleOrd ζ‖ := lt_of_lt_of_le hε hA
    rw [norm_div, norm_pow]
    have hnum : ‖(1 : ℂ) + (circleOrd ζ : ℂ) ^ 2‖ = 1 + circleOrd ζ ^ 2 := by
      rw [show (1 : ℂ) + (circleOrd ζ : ℂ) ^ 2 = ((1 + circleOrd ζ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnum, div_le_iff₀ (by positivity)]
    have hε2 : ε ^ 2 ≤ ‖z + circleOrd ζ‖ ^ 2 := pow_le_pow_left₀ hε.le hA 2
    have hQ : 0 ≤ (1 + (2 * R + 1) ^ 2) / ε ^ 2 := by positivity
    by_cases hcase : circleOrd ζ ≤ 2 * R + 1
    · have e1 : 1 + circleOrd ζ ^ 2 ≤ 1 + (2 * R + 1) ^ 2 := by nlinarith
      have e3 : (1 + (2 * R + 1) ^ 2) = (1 + (2 * R + 1) ^ 2) / ε ^ 2 * ε ^ 2 := by
        field_simp
      calc 1 + circleOrd ζ ^ 2 ≤ (1 + (2 * R + 1) ^ 2) / ε ^ 2 * ε ^ 2 := by rw [← e3]; exact e1
        _ ≤ (1 + (2 * R + 1) ^ 2) / ε ^ 2 * ‖z + circleOrd ζ‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hε2 hQ
        _ ≤ ((1 + (2 * R + 1) ^ 2) / ε ^ 2 + 8) * ‖z + circleOrd ζ‖ ^ 2 := by
            nlinarith [sq_nonneg ‖z + circleOrd ζ‖]
    · have hγR : 2 * R + 1 < circleOrd ζ := not_le.mp hcase
      have hgR : circleOrd ζ / 2 ≤ circleOrd ζ - R := by linarith
      have hsq : (circleOrd ζ / 2) ^ 2 ≤ ‖z + circleOrd ζ‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hgR.trans hB) 2
      have hpos : 0 ≤ (1 + (2 * R + 1) ^ 2) / ε ^ 2 * ‖z + circleOrd ζ‖ ^ 2 := by positivity
      nlinarith

/-- The kernel itself is bounded by `((2R+1)|z| + 1)/ε + 2|z| + 2` under the ball bounds. -/
theorem norm_nevKernel_le {z ζ : ℂ} {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hγ : ζ = 1 ∨ 0 ≤ circleOrd ζ)
    (h1 : ζ ≠ 1 → ε ≤ ‖z + circleOrd ζ‖) (h2 : ζ ≠ 1 → circleOrd ζ - R ≤ ‖z + circleOrd ζ‖) :
    ‖nevKernel z ζ‖ ≤ ((2 * R + 1) * ‖z‖ + 1) / ε + 2 * ‖z‖ + 2 := by
  by_cases hζ1 : ζ = 1
  · simp only [nevKernel, hζ1, if_true]
    have : 0 ≤ ((2 * R + 1) * ‖z‖ + 1) / ε := by positivity
    linarith [norm_nonneg z]
  · simp only [nevKernel, hζ1, if_false]
    have hγ0 : 0 ≤ circleOrd ζ := hγ.resolve_left hζ1
    have hA := h1 hζ1
    have hB := h2 hζ1
    have hN0 : 0 < ‖z + circleOrd ζ‖ := lt_of_lt_of_le hε hA
    rw [norm_div, div_le_iff₀ hN0]
    have hnum : ‖(circleOrd ζ : ℂ) * z - 1‖ ≤ circleOrd ζ * ‖z‖ + 1 := by
      calc ‖(circleOrd ζ : ℂ) * z - 1‖ ≤ ‖(circleOrd ζ : ℂ) * z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = circleOrd ζ * ‖z‖ + 1 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ0, norm_one]
    have hz0 := norm_nonneg z
    by_cases hcase : circleOrd ζ ≤ 2 * R + 1
    · have e1 : circleOrd ζ * ‖z‖ + 1 ≤ (2 * R + 1) * ‖z‖ + 1 := by nlinarith
      have e3 : ((2 * R + 1) * ‖z‖ + 1) = ((2 * R + 1) * ‖z‖ + 1) / ε * ε := by field_simp
      have hQ : 0 ≤ ((2 * R + 1) * ‖z‖ + 1) / ε := by positivity
      calc ‖(circleOrd ζ : ℂ) * z - 1‖ ≤ ((2 * R + 1) * ‖z‖ + 1) / ε * ε := by
            rw [← e3]; exact hnum.trans e1
        _ ≤ ((2 * R + 1) * ‖z‖ + 1) / ε * ‖z + circleOrd ζ‖ := mul_le_mul_of_nonneg_left hA hQ
        _ ≤ (((2 * R + 1) * ‖z‖ + 1) / ε + 2 * ‖z‖ + 2) * ‖z + circleOrd ζ‖ := by nlinarith
    · have hγR : 2 * R + 1 < circleOrd ζ := not_le.mp hcase
      have hgR : circleOrd ζ / 2 ≤ ‖z + circleOrd ζ‖ := by linarith
      have hQ : 0 ≤ ((2 * R + 1) * ‖z‖ + 1) / ε * ‖z + circleOrd ζ‖ := by positivity
      -- `γ|z| + 1 ≤ (2|z| + 2)(γ/2) ≤ (2|z| + 2)|z + γ|` since `γ ≥ 1`
      have : circleOrd ζ * ‖z‖ + 1 ≤ (2 * ‖z‖ + 2) * ‖z + circleOrd ζ‖ := by nlinarith
      nlinarith

/-! ## Differentiation under the integral -/

theorem ae_support_of_cut_eq_zero {ν : Measure ℝ}
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0) :
    ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ 0 ≤ circleOrd (circleMap 0 1 θ) := by
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) hcut
  simp only [Set.mem_setOf_eq, not_or, not_le] at hθ
  exact ⟨hθ.1, hθ.2⟩

/-- **Holomorphy of the Nevanlinna integral off the negative axis** when `ν` has no cut mass. -/
theorem hasDerivAt_integral_nevKernel {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ offNegAxis) :
    HasDerivAt (fun z => ∫ θ, nevKernel z (circleMap 0 1 θ) ∂ν)
      (∫ θ, nevKernelDeriv z₀ (circleMap 0 1 θ) ∂ν) z₀ := by
  obtain ⟨ε, hε, hball⟩ := exists_ball_bound_of_mem_offNegAxis hz₀
  set R : ℝ := ‖z₀‖ + ε with hR
  have hR0 : 0 ≤ R := by positivity
  have hae := ae_support_of_cut_eq_zero hcut
  have hz₀ball : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε
  have hγ0 : ∀ ζ : ℂ, (ζ = 1 ∨ 0 ≤ circleOrd ζ) → 0 ≤ circleOrd ζ := fun ζ h => by
    rcases h with h | h
    · rw [h, circleOrd_one]
    · exact h
  have hbounds : ∀ z ∈ Metric.ball z₀ ε, ∀ ζ : ℂ, (ζ = 1 ∨ 0 ≤ circleOrd ζ) →
      ε ≤ ‖z + circleOrd ζ‖ ∧ circleOrd ζ - R ≤ ‖z + circleOrd ζ‖ :=
    fun z hz ζ hζ => hball z hz _ (hγ0 ζ hζ)
  have hne : ∀ z ∈ Metric.ball z₀ ε, ∀ ζ : ℂ, (ζ = 1 ∨ 0 ≤ circleOrd ζ) →
      z + circleOrd ζ ≠ 0 := fun z hz ζ hζ => by
    intro h
    have := (hbounds z hz ζ hζ).1
    rw [h, norm_zero] at this
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z θ => nevKernel z (circleMap 0 1 θ))
    (F' := fun z θ => nevKernelDeriv z (circleMap 0 1 θ)) (Metric.ball_mem_nhds z₀ hε)
    (Eventually.of_forall fun z => (measurable_nevKernel_circleMap z).aestronglyMeasurable)
    ?_ (measurable_nevKernelDeriv_circleMap z₀).aestronglyMeasurable
    (bound := fun _ => (1 + (2 * R + 1) ^ 2) / ε ^ 2 + 8) ?_ (integrable_const _) ?_).2
  · refine Integrable.mono' (integrable_const (((2 * R + 1) * ‖z₀‖ + 1) / ε + 2 * ‖z₀‖ + 2))
      (measurable_nevKernel_circleMap z₀).aestronglyMeasurable ?_
    filter_upwards [hae] with θ hθ
    exact norm_nevKernel_le hε hR0 hθ (fun _ => (hbounds z₀ hz₀ball _ hθ).1)
      (fun _ => (hbounds z₀ hz₀ball _ hθ).2)
  · filter_upwards [hae] with θ hθ
    intro z hz
    exact norm_nevKernelDeriv_le hε hR0 hθ (fun _ => (hbounds z hz _ hθ).1)
      (fun _ => (hbounds z hz _ hθ).2)
  · filter_upwards [hae] with θ hθ
    intro z hz
    exact hasDerivAt_nevKernel (hne z hz _ hθ)

/-! ## The extension -/

/-- The candidate extension `Φ(s) = (∫ k((s − ½)², ζ) dν(ζ) − c)/(s − ½)`. -/
def cutFreeExtension (ν : Measure ℝ) (c : ℝ) (s : ℂ) : ℂ :=
  ((∫ θ, nevKernel ((s - 1 / 2) ^ 2) (circleMap 0 1 θ) ∂ν) - c) / (s - 1 / 2)

theorem sq_mem_offNegAxis {a : ℂ} (ha : 0 < a.re) : a ^ 2 ∈ offNegAxis := by
  by_cases him : a.im = 0
  · right
    rw [pow_two, Complex.mul_re, him]
    nlinarith
  · left
    rw [pow_two, Complex.mul_im]
    intro h
    have : a.re * a.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact him h1

theorem differentiableOn_cutFreeExtension {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0) (c : ℝ) :
    DifferentiableOn ℂ (cutFreeExtension ν c) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  have ha : 0 < (s - 1 / 2).re := by simp; linarith
  have hG := (hasDerivAt_integral_nevKernel hcut (sq_mem_offNegAxis ha)).differentiableAt
  have hsq : DifferentiableAt ℂ (fun s : ℂ => (s - 1 / 2) ^ 2) s := by fun_prop
  have h1 : DifferentiableAt ℂ
      (fun s : ℂ => (∫ θ, nevKernel ((s - 1 / 2) ^ 2) (circleMap 0 1 θ) ∂ν) - c) s :=
    (hG.comp s hsq).sub_const _
  have hne : s - 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact (h1.div (differentiableAt_id.sub_const _) hne).differentiableWithinAt

/-- On the upper quadrant the extension agrees with the slit continuation. -/
theorem cutFreeExtension_eq_of_im_pos {Ψ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs' : 0 < s.im) : cutFreeExtension ν c s = Ψ s := by
  set a : ℂ := s - 1 / 2 with ha
  have hare : 0 < a.re := by simp [ha]; linarith
  have haim : 0 < a.im := by simp [ha]; exact hs'
  have hrep' := hrep a hare haim
  have hzim : 0 < (a ^ 2).im := by
    rw [pow_two, Complex.mul_im]
    positivity
  have hs0 : 2 * (1 / 2 - I * a ^ 2) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hint : (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) =
      ∫ θ, nevKernel (a ^ 2) (circleMap 0 1 θ) ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    show I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) = nevKernel (a ^ 2) (circleMap 0 1 θ)
    by_cases h1 : circleMap 0 1 θ = 1
    · rw [h1, I_mul_hrKernel_one hs0]
      simp [nevKernel]
    · have hzγ : a ^ 2 + circleOrd (circleMap 0 1 θ) ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      rw [I_mul_hrKernel_eq hs0 (norm_circleMap_one θ) h1 hzγ]
      simp [nevKernel, h1]
  have hane : a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsa : (1 / 2 : ℂ) + a = s := by rw [ha]; ring
  unfold cutFreeExtension
  rw [← ha, ← hint, ← hrep', hsa]
  field_simp

/-- On `Re s > 1` the extension is the Weil function (identity theorem). -/
theorem cutFreeExtension_eq_weilFunction {lam : ℕ → ℝ} {Ψ : ℂ → ℂ}
    (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    {s : ℂ} (hs : 1 < s.re) : cutFreeExtension ν c s = weilFunction lam s := by
  set V : Set ℂ := {z : ℂ | 1 < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : IsPreconnected V := (convex_halfSpace_re_gt 1).isPreconnected
  have hΦV : DifferentiableOn ℂ (cutFreeExtension ν c) V :=
    (differentiableOn_cutFreeExtension hcut c).mono fun z hz => by
      have : 1 < z.re := hz
      show 1 / 2 < z.re
      linarith
  have hΨV : DifferentiableOn ℂ Ψ V := hΨd.mono fun z hz => by
    have : 1 < z.re := hz
    exact ⟨by linarith, Or.inr this⟩
  have heq : cutFreeExtension ν c =ᶠ[𝓝 (2 + I : ℂ)] Ψ := by
    have hm : {z : ℂ | 1 < z.re ∧ 0 < z.im} ∈ 𝓝 (2 + I : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds (by norm_num)
    filter_upwards [hm] with z hz
    exact cutFreeExtension_eq_of_im_pos hrep (by linarith [hz.1]) hz.2
  have hmem : (2 + I : ℂ) ∈ V := by
    show (1 : ℝ) < (2 + I : ℂ).re
    simp
  have hEq := (hΦV.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq
    (hΨV.analyticOnNhd hVo) hVc hmem heq
  rw [hEq hs, hΨe s hs]

/-- **A cut-free Nevanlinna measure gives a holomorphic extension of the Weil function to
`Re s > ½`.** -/
theorem exists_extension_of_cut_eq_zero {lam : ℕ → ℝ} {Ψ : ℂ → ℂ}
    (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hcut : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ < 0} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → Φ s = weilFunction lam s :=
  ⟨cutFreeExtension ν c, differentiableOn_cutFreeExtension hcut c,
    fun _ hs => cutFreeExtension_eq_weilFunction hΨd hΨe hcut hrep hs⟩

/-! ## Cut removal for odd Weil-positive weights -/

/-- **Even mean-zero positivity removes the cut.**  An odd Weil-positive weight whose functional is
nonnegative on every even mean-zero test has a Weil function extending holomorphically to
`Re s > ½`. -/
theorem exists_extension_of_weilPositiveOdd_of_even_meanZero_nonneg {lam : ℕ → ℝ}
    (hW : WeilPositiveOdd lam)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = f x) →
      paperFT f 0 = 0 → 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → Φ s = weilFunction lam s := by
  obtain ⟨Ψ, hΨd, hΨe, -, ν, hν, c, hsupp, hrep⟩ := exists_nevanlinna_measure_of_weilPositiveOdd hW
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := fun σ hσ =>
    OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight
      (weilPositiveOddAt_one_iff.mpr hW) hσ
  have hcut := cut_measure_eq_zero_of_even_meanZero_nonneg hsl hΨd hΨe hsupp hrep hpos
  exact exists_extension_of_cut_eq_zero hΨd hΨe hcut hrep

/-- **Odd positivity, even mean-zero positivity and central nonnegativity give `λ = Λ` and RH.** -/
theorem eq_vonMangoldt_and_riemannHypothesis_of_even_meanZero_nonneg {lam : ℕ → ℝ}
    (hW : WeilPositiveOdd lam)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = f x) →
      paperFT f 0 = 0 → 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re)
    (hcentral : ∀ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} →
      (∀ s : ℂ, 1 < s.re → Φ s = weilFunction lam s) → ∀ x : ℝ, 1 / 2 < x → 0 ≤ (Φ x).re) :
    (∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨Φ, hΦd, hΦe⟩ := exists_extension_of_weilPositiveOdd_of_even_meanZero_nonneg hW hpos
  exact eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension hW hΦd hΦe
    (hcentral Φ hΦd hΦe)

end RHTower.OddResolvent
