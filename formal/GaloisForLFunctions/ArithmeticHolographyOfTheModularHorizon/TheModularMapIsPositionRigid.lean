import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateOfTheCuspEnergyReadsTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheLFunctionsOfTheCuspModes

/-!
# The modular map is position rigid

A **seed** of the modular horizon is a continuous, bounded, `SL₂(ℤ)`-invariant function `F` on `ℍ` with
exponential decay in the cusp (`IsSeed`). The modular map reads it on the closed horocycles: its
**response** is the horocycle mean `a_F(y) = ∫_0^1 F(x + iy) dx`. Its **completed transform** is

  `Λ_F(s) = ∫_𝒟 F · E*(s − ½) dμ`,   `E*(u) = ξ(1 + 2u) E(½ + u)/((1 + 2u) 2u)`.

**Theorems.**
* `differentiableOn_seedTransform`, `seedTransform_one_sub`: for every seed, `Λ_F` is holomorphic on
  `ℂ ∖ {0, ½, 1}` and `Λ_F(1 − s) = Λ_F(s)`.
* `seedTransform_eq_mellin` (unfolding): for `Re s > 1`, `Im s ≠ 0`,
  `Λ_F(s) = ξ(2s)/(2s(2s − 1)) · ∫_0^∞ a_F(y) y^{s−2} dy`.
* `differentiableAt_responseContinuation`, `responseContinuation_eq_mellin` (**position rigidity**): the Mellin
  transform of the response of every seed continues to `Λ_F(s) · 2s(2s − 1)/ξ(2s)`, holomorphic at every
  `s ∉ {0, ½, 1}` with `ξ(2s) ≠ 0`. The resonances of every seed sit at the zeros of `ξ(2s)`: the group fixes
  the positions, the seed enters only through the values `Λ_F(ρ/2)`.
* `seedTransform_eq_zero_of_rate` (**receiver**): `|a_F(y) − c| ≤ C y^α` on `(0, 1]` forces `Λ_F(s₀) = 0` at
  every zero `s₀` of `ξ(2s)` with `Re s₀ > 1 − α`.
* `IsSeed.add`, `IsSeed.mul`, `IsSeed.star`, `IsSeed.const_mul`, `isSeed_of_mem_cuspSpace`: seeds form a
  `*`-algebra containing every Maass cusp form; for a cusp form `g`, `Λ_{|g|²}` is the completed
  Rankin–Selberg function (`seedTransform_normSq_eq_completedRS`).

**Proof.** A seed is bounded by `M e^{−c Im z}` on all of `ℍ`; on a compact set of `u` avoiding `{0, ±½}` the
completed Eisenstein function is at most `α Y^a + β` on `𝒟`, so `F E*` is dominated by a bounded function on a
set of finite measure, and holomorphy follows by Cauchy domination; the functional equation is pointwise.
Unfolding the row sum `E(s − ½) = ½ Σ_v Im(M_v z)^s` along the translations and Fubini on the strip give the
Mellin transform of the response. For the receiver, the response minus `c 1_{(0,1]}` has a Mellin transform
holomorphic on `Re s > 1 − α`, and the identity theorem on the two quarter planes `±Im s > 0` (`ξ` has no real
zeros) transports the unfolding identity to the zeros.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown EisensteinSeries
open UpperHalfPlane (ofComplex)

/-! ### Seeds -/

/-- A **seed** of the modular map: continuous, bounded, `SL₂(ℤ)`-invariant, exponentially small in the cusp. -/
structure IsSeed (F : ℍ → ℂ) : Prop where
  invariant : ∀ (γ : SL(2, ℤ)) (z : ℍ), F (γ • z) = F z
  continuous : Continuous F
  bounded : ∃ B : ℝ, ∀ z, ‖F z‖ ≤ B
  decay : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ z : ℍ, 1 ≤ z.im → ‖F z‖ ≤ C * Real.exp (-c * z.im)

variable {F G : ℍ → ℂ}

/-- A seed is at most `M e^{−c Im z}` on all of `ℍ`. -/
theorem IsSeed.exists_exp_bound (hF : IsSeed F) :
    ∃ M c : ℝ, 0 ≤ M ∧ 0 < c ∧ ∀ z : ℍ, ‖F z‖ ≤ M * Real.exp (-c * z.im) := by
  obtain ⟨B, hB⟩ := hF.bounded
  obtain ⟨C, c, hC, hc, hd⟩ := hF.decay
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB UpperHalfPlane.I)
  refine ⟨B * Real.exp c + C, c, by positivity, hc, fun z => ?_⟩
  by_cases hz : 1 ≤ z.im
  · calc ‖F z‖ ≤ C * Real.exp (-c * z.im) := hd z hz
      _ ≤ (B * Real.exp c + C) * Real.exp (-c * z.im) :=
          mul_le_mul_of_nonneg_right (by nlinarith [Real.exp_pos c]) (Real.exp_pos _).le
  · have h1 : 1 ≤ Real.exp c * Real.exp (-c * z.im) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [z.im_pos])
    calc ‖F z‖ ≤ B := hB z
      _ ≤ B * (Real.exp c * Real.exp (-c * z.im)) := le_mul_of_one_le_right hB0 h1
      _ ≤ (B * Real.exp c + C) * Real.exp (-c * z.im) := by
          nlinarith [Real.exp_pos (-c * z.im)]

theorem IsSeed.add (hF : IsSeed F) (hG : IsSeed G) : IsSeed (F + G) := by
  obtain ⟨B₁, hB₁⟩ := hF.bounded
  obtain ⟨B₂, hB₂⟩ := hG.bounded
  obtain ⟨M₁, c₁, hM₁, hc₁, h₁⟩ := hF.exists_exp_bound
  obtain ⟨M₂, c₂, hM₂, hc₂, h₂⟩ := hG.exists_exp_bound
  refine ⟨fun γ z => by show F (γ • z) + G (γ • z) = F z + G z; rw [hF.invariant, hG.invariant],
    hF.continuous.add hG.continuous,
    ⟨B₁ + B₂, fun z => (norm_add_le _ _).trans (add_le_add (hB₁ z) (hB₂ z))⟩,
    ⟨M₁ + M₂, min c₁ c₂, by positivity, lt_min hc₁ hc₂, fun z hz => ?_⟩⟩
  have hy : 0 < z.im := z.im_pos
  have e₁ : Real.exp (-c₁ * z.im) ≤ Real.exp (-min c₁ c₂ * z.im) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c₁ c₂])
  have e₂ : Real.exp (-c₂ * z.im) ≤ Real.exp (-min c₁ c₂ * z.im) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c₁ c₂])
  calc ‖(F + G) z‖ ≤ ‖F z‖ + ‖G z‖ := norm_add_le _ _
    _ ≤ M₁ * Real.exp (-c₁ * z.im) + M₂ * Real.exp (-c₂ * z.im) := add_le_add (h₁ z) (h₂ z)
    _ ≤ M₁ * Real.exp (-min c₁ c₂ * z.im) + M₂ * Real.exp (-min c₁ c₂ * z.im) :=
        add_le_add (mul_le_mul_of_nonneg_left e₁ hM₁) (mul_le_mul_of_nonneg_left e₂ hM₂)
    _ = (M₁ + M₂) * Real.exp (-min c₁ c₂ * z.im) := by ring

theorem IsSeed.const_mul (hF : IsSeed F) (a : ℂ) : IsSeed (fun z => a * F z) := by
  obtain ⟨B, hB⟩ := hF.bounded
  obtain ⟨C, c, hC, hc, hd⟩ := hF.decay
  refine ⟨fun γ z => by show a * F (γ • z) = a * F z; rw [hF.invariant], continuous_const.mul hF.continuous,
    ⟨‖a‖ * B, fun z => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB z) (norm_nonneg _)⟩,
    ⟨‖a‖ * C, c, by positivity, hc, fun z hz => ?_⟩⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hd z hz) (norm_nonneg _)

theorem IsSeed.mul (hF : IsSeed F) (hG : IsSeed G) : IsSeed (fun z => F z * G z) := by
  obtain ⟨B₁, hB₁⟩ := hF.bounded
  obtain ⟨B₂, hB₂⟩ := hG.bounded
  obtain ⟨C, c, hC, hc, hd⟩ := hF.decay
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ UpperHalfPlane.I)
  refine ⟨fun γ z => by show F (γ • z) * G (γ • z) = F z * G z; rw [hF.invariant, hG.invariant],
    hF.continuous.mul hG.continuous,
    ⟨B₁ * B₂, fun z => by
      rw [norm_mul]; exact mul_le_mul (hB₁ z) (hB₂ z) (norm_nonneg _) ((norm_nonneg _).trans (hB₁ z))⟩,
    ⟨C * B₂, c, mul_nonneg hC hB₂0, hc, fun z hz => ?_⟩⟩
  rw [norm_mul]
  calc ‖F z‖ * ‖G z‖ ≤ C * Real.exp (-c * z.im) * B₂ :=
        mul_le_mul (hd z hz) (hB₂ z) (norm_nonneg _) (by positivity)
    _ = C * B₂ * Real.exp (-c * z.im) := by ring

theorem IsSeed.star (hF : IsSeed F) : IsSeed (fun z => starRingEnd ℂ (F z)) := by
  obtain ⟨B, hB⟩ := hF.bounded
  obtain ⟨C, c, hC, hc, hd⟩ := hF.decay
  exact ⟨fun γ z => by show starRingEnd ℂ (F (γ • z)) = starRingEnd ℂ (F z); rw [hF.invariant],
    Complex.continuous_conj.comp hF.continuous,
    ⟨B, fun z => by rw [Complex.norm_conj]; exact hB z⟩,
    ⟨C, c, hC, hc, fun z hz => by rw [Complex.norm_conj]; exact hd z hz⟩⟩

/-! ### The response -/

/-- The **response** of a seed: its mean over the closed horocycle of height `y`. -/
def response (F : ℍ → ℂ) (y : ℝ) : ℂ := ∫ x in Ico (0 : ℝ) 1, F (ofComplex ⟨x, y⟩)

theorem ofComplex_mk_im {x y : ℝ} (hy : 0 < y) : (ofComplex (⟨x, y⟩ : ℂ)).im = y :=
  BlackHoleRingdown.im_ofComplex_mk hy

theorem norm_response_le (hF : IsSeed F) :
    ∃ M c : ℝ, 0 ≤ M ∧ 0 < c ∧ ∀ y : ℝ, 0 < y → ‖response F y‖ ≤ M * Real.exp (-c * y) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hF.exists_exp_bound
  refine ⟨M, c, hM, hc, fun y hy => ?_⟩
  have h := norm_setIntegral_le_of_norm_le_const (s := Ico (0 : ℝ) 1) (μ := volume)
    (by simp) (fun x _ => (hb (ofComplex ⟨x, y⟩)).trans_eq (by rw [ofComplex_mk_im hy]))
  rw [measureReal_def, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal zero_le_one, mul_one] at h
  exact h

/-- The response as an interval integral. -/
theorem response_eq_intervalIntegral (F : ℍ → ℂ) (y : ℝ) :
    response F y = ∫ x in (0 : ℝ)..1, F (ofComplex ⟨x, y⟩) := by
  rw [intervalIntegral.integral_of_le zero_le_one, response, integral_Ico_eq_integral_Ioc]

theorem continuousOn_response (hF : IsSeed F) : ContinuousOn (response F) (Ioi 0) := by
  intro y₀ hy₀
  have hY : (0 : ℝ) < y₀ / 2 := half_pos hy₀
  set H : ℝ → ℝ → ℂ := fun y x => F (ofComplex ⟨x, max y (y₀ / 2)⟩)
  have hH : Continuous (Function.uncurry H) := by
    have hp : Continuous fun p : ℝ × ℝ => (⟨p.2, max p.1 (y₀ / 2)⟩ : ℂ) := by
      have : (fun p : ℝ × ℝ => (⟨p.2, max p.1 (y₀ / 2)⟩ : ℂ)) =
          fun p : ℝ × ℝ => (p.2 : ℂ) + ((max p.1 (y₀ / 2) : ℝ) : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      rw [this]; fun_prop
    have hmaps : ∀ p : ℝ × ℝ, (⟨p.2, max p.1 (y₀ / 2)⟩ : ℂ) ∈ {w : ℂ | 0 < w.im} :=
      fun p => lt_max_of_lt_right hY
    have hoc : ContinuousOn (fun w : ℂ => F (ofComplex w)) {w : ℂ | 0 < w.im} :=
      hF.continuous.comp_continuousOn (UpperHalfPlane.ofComplex.continuousOn.mono fun w hw => by
        simpa [UpperHalfPlane.ofComplex] using hw)
    exact hoc.comp_continuous hp hmaps
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hH 0 1
  have heq : (fun y => ∫ x in (0 : ℝ)..1, H y x) =ᶠ[𝓝 y₀] response F := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hy₀)] with y hy
    rw [response_eq_intervalIntegral]
    simp only [H, max_eq_left (le_of_lt (mem_Ioi.1 hy))]
  exact ((hc.continuousAt).congr heq).continuousWithinAt

/-! ### The completed transform and its continuation -/

/-- The **completed transform** `Λ_F(s) = ∫_𝒟 F · E*(s − ½)` of a seed. -/
def seedTransform (F : ℍ → ℂ) (s : ℂ) : ℂ :=
  ∫ z in ModularGroup.fd, F z * EisAuto.completedEisenstein (s - 1 / 2) z.re z.im

/-- For a cusp form `g`, the transform of `|g|²` is the completed Rankin–Selberg function. -/
theorem seedTransform_normSq_eq_completedRS (g : ℍ → ℂ) :
    seedTransform (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) = CuspRSC.completedRS g := rfl

theorem exists_rpow_mul_exp_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → y ^ a * Real.exp (-c * y) ≤ K := by
  set n := ⌈a⌉₊
  refine ⟨1 + n.factorial / c ^ n, by positivity, fun y hy => ?_⟩
  rcases le_or_gt y 1 with hy1 | hy1
  · have h1 : y ^ a ≤ 1 := Real.rpow_le_one hy.le hy1 ha
    have h2 : Real.exp (-c * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have : y ^ a * Real.exp (-c * y) ≤ 1 :=
      calc y ^ a * Real.exp (-c * y) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    have : (0 : ℝ) ≤ n.factorial / c ^ n := by positivity
    linarith
  · have h1 : y ^ a ≤ y ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1.le (Nat.le_ceil a)
    rw [Real.rpow_natCast] at h1
    have h2 := Real.pow_div_factorial_le_exp (c * y) (by positivity) n
    rw [mul_pow, div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)] at h2
    have hcn : 0 < c ^ n := pow_pos hc n
    have h3 : y ^ n * Real.exp (-c * y) ≤ n.factorial / c ^ n := by
      rw [le_div_iff₀ hcn]
      have he : Real.exp (c * y) * Real.exp (-c * y) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-c * y), Real.exp_pos (c * y)]
    have : y ^ a * Real.exp (-c * y) ≤ y ^ n * Real.exp (-c * y) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    linarith

/-- On `𝒟` a seed times a polynomial in the height is bounded. -/
theorem IsSeed.exists_bound_on_fd (hF : IsSeed F) {α β a : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 ≤ a) :
    ∃ B, ∀ z ∈ ModularGroup.fd, ‖F z‖ * (α * z.im ^ a + β) ≤ B := by
  obtain ⟨M, c, hM, hc, hb⟩ := hF.exists_exp_bound
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_le ha hc
  refine ⟨M * (α * K + β), fun z _ => ?_⟩
  have hy := z.im_pos
  have h1 : Real.exp (-c * z.im) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc ‖F z‖ * (α * z.im ^ a + β) ≤ M * Real.exp (-c * z.im) * (α * z.im ^ a + β) :=
        mul_le_mul_of_nonneg_right (hb z) (by positivity)
    _ = M * (α * (z.im ^ a * Real.exp (-c * z.im)) + β * Real.exp (-c * z.im)) := by ring
    _ ≤ M * (α * K + β * 1) := by
        gcongr
        exact hK _ hy
    _ = M * (α * K + β) := by ring

/-- **The completed transform of every seed is holomorphic on `ℂ ∖ {0, ½, 1}`.** -/
theorem differentiableOn_seedTransform (hF : IsSeed F) :
    DifferentiableOn ℂ (seedTransform F) ({0, 1 / 2, 1} : Set ℂ)ᶜ := by
  set U : Set ℂ := ({0, 1 / 2, 1} : Set ℂ)ᶜ
  have hU : IsOpen U := (Set.toFinite _).isClosed.isOpen_compl
  have hmemU : ∀ {s : ℂ}, s ∈ U ↔ s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := fun {s} => by
    simp [U, not_or]
  set Φ : ℍ → ℂ → ℂ := fun z s => ModularGroup.fd.indicator
    (fun w => F w * EisAuto.completedEisenstein (s - 1 / 2) w.re w.im) z
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  have hint : ∀ s, seedTransform F s = ∫ z, Φ z s := fun s => by
    simp only [Φ]; rw [integral_indicator hfd]; rfl
  have hΦ : ∀ z, DifferentiableOn ℂ (Φ z) U := by
    intro z
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [Φ, indicator_of_mem hz]
      intro s hs
      obtain ⟨h0, h1, h2⟩ := hmemU.1 hs
      have hd := EisAuto.differentiableAt_completed z.re z.im_pos (u := s - 1 / 2)
        (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination h))
        (fun h => h0 (by linear_combination h))
      exact ((differentiableAt_const _).mul
        (hd.comp s (differentiableAt_id.sub_const _))).differentiableWithinAt
    · simp only [Φ, indicator_of_notMem hz]
      exact differentiableOn_const _
  have hmeas : ∀ s ∈ U, AEStronglyMeasurable (fun z => Φ z s) volume := by
    intro s _
    have hc : Continuous fun w : ℍ => F w *
        EisAuto.completedEisenstein (s - 1 / 2) w.re (max w.im (1 / 2)) :=
      hF.continuous.mul (CuspRSC.continuous_completed_max _)
    refine (hc.aestronglyMeasurable.indicator hfd).congr (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [Φ, indicator_of_mem hz, max_eq_left (CuspRSC.half_lt_im_of_mem_fd hz).le]
    · simp only [Φ, indicator_of_notMem hz]
  refine (RHTower.differentiableOn_integral_of_locally_bounded hU hΦ hmeas fun s₀ hs₀ => ?_).congr
    fun s _ => hint s
  obtain ⟨h0, h1, h2⟩ := hmemU.1 hs₀
  set r := min ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖) / 2
  have a1 := norm_pos_iff.2 h0
  have a2 := norm_pos_iff.2 (sub_ne_zero.2 h1)
  have a3 := norm_pos_iff.2 (sub_ne_zero.2 h2)
  have hr : 0 < r := by simp only [r]; positivity
  have m1 := min_le_left ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖)
  have m2 := (min_le_right ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖)).trans (min_le_left _ _)
  have m3 := (min_le_right ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖)).trans (min_le_right _ _)
  have mpos : 0 < min ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖) := lt_min a1 (lt_min a2 a3)
  have hball : ∀ s ∈ Metric.closedBall s₀ r, s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [h, norm_sub_rev, sub_zero] at hs; simp only [r] at hs; linarith
    · rw [h, norm_sub_rev] at hs; simp only [r] at hs; linarith
    · rw [h, norm_sub_rev] at hs; simp only [r] at hs; linarith
  refine ⟨r, hr, fun s hs => hmemU.2 (hball s hs), ?_⟩
  set K : Set ℂ := (fun s => s - 1 / 2) '' Metric.closedBall s₀ r
  have hK : IsCompact K := (isCompact_closedBall s₀ r).image (by fun_prop)
  have hKU : ∀ u ∈ K, u ≠ 1 / 2 ∧ u ≠ 0 ∧ u ≠ -(1 / 2) := by
    rintro u ⟨s, hs, rfl⟩
    obtain ⟨h0', h1', h2'⟩ := hball s hs
    exact ⟨fun h => h2' (by linear_combination h), fun h => h1' (by linear_combination h),
      fun h => h0' (by linear_combination h)⟩
  obtain ⟨α, β, a, hα, hβ, ha, hb⟩ := CuspRSC.exists_completed_bound hK hKU
  obtain ⟨B, hB⟩ := hF.exists_bound_on_fd hα hβ ha
  refine ⟨ModularGroup.fd.indicator (fun z => ‖F z‖ * (α * z.im ^ a + β)), ?_, fun z s hs => ?_⟩
  · have hvol : volume ModularGroup.fd ≠ ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_ne_top
    refine (integrable_indicator_iff hfd).2 (Measure.integrableOn_of_bounded (M := B) hvol ?_ ?_)
    · exact (hF.continuous.norm.mul ((continuous_const.mul (UpperHalfPlane.continuous_im.rpow_const
        fun z => Or.inl (ne_of_gt z.im_pos))).add continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hfd] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := z.im_pos; positivity)]
      exact hB z hz
  · by_cases hz : z ∈ ModularGroup.fd
    · simp only [Φ, indicator_of_mem hz]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb _ ⟨s, hs, rfl⟩ z.re z.im
        (CuspRSC.half_lt_im_of_mem_fd hz).le) (norm_nonneg _)
    · simp only [Φ, indicator_of_notMem hz, norm_zero, le_refl]

/-- **The functional equation** `Λ_F(1 − s) = Λ_F(s)`. -/
theorem seedTransform_one_sub (F : ℍ → ℂ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    seedTransform F (1 - s) = seedTransform F s := by
  unfold seedTransform
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
  rw [show 1 - s - 1 / 2 = -(s - 1 / 2) by ring,
    EisAuto.completedEisenstein_neg z.re z.im_pos (fun h => h2 (by linear_combination h))
      (fun h => h1 (by linear_combination h)) (fun h => h0 (by linear_combination h))]

/-! ### Unfolding -/

/-- The strip integrand `F(w) (Im w)^s`. -/
def stripIntegrand (F : ℍ → ℂ) (s : ℂ) (w : ℍ) : ℂ := F w * ((w.im : ℝ) : ℂ) ^ s

theorem stripChart_stripIntegrand {s : ℂ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    stripChartIntegrand (stripIntegrand F s) p = (p.1 : ℂ) ^ (s - 2) * F (ofComplex ⟨p.2, p.1⟩) := by
  have h0 : (p.1 : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne'
  rw [stripChartIntegrand, stripIntegrand, ofComplex_mk_im hp, Complex.real_smul, cpow_sub _ _ h0,
    cpow_two]
  push_cast
  field_simp

/-- **Integrability on the strip** for `Re s > 1`. -/
theorem integrableOn_stripIntegrand (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (stripIntegrand F s) modularStrip volume := by
  obtain ⟨M, c, hM, hc, hb⟩ := hF.exists_exp_bound
  rw [integrableOn_modularStrip_iff, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 2) * F (ofComplex ⟨p.2, p.1⟩))
      (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := by
    intro p hp
    have hp0 : (0 : ℝ) < p.1 := hp.1
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.comp (g := fun w : ℂ => w ^ (s - 2)) (f := fun q : ℝ × ℝ => (q.1 : ℂ))
        (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hp0))
        (Complex.continuous_ofReal.comp continuous_fst).continuousAt
    · have hmk : ContinuousAt (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) p := by
        have : (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) = fun q : ℝ × ℝ => (q.2 : ℂ) + (q.1 : ℂ) * Complex.I := by
          funext q; apply Complex.ext <;> simp
        rw [this]
        fun_prop
      have hoc : ContinuousAt (fun q : ℝ × ℝ => ofComplex (⟨q.2, q.1⟩ : ℂ)) p :=
        (UpperHalfPlane.ofComplex.continuousAt (by simp [UpperHalfPlane.ofComplex, hp0])).comp hmk
      exact hF.continuous.continuousAt.comp hoc
  have hmeas : AEStronglyMeasurable (stripChartIntegrand (stripIntegrand F s))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine (hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ico)).congr ?_
    exact (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ico)).2
      (Eventually.of_forall fun p hp => (stripChart_stripIntegrand hp.1).symm)
  have hdom : Integrable (fun p : ℝ × ℝ => (M * (p.1 ^ (s.re - 2) * Real.exp (-c * p.1 ^ (1 : ℝ)))) * 1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
    refine Integrable.mul_prod (f := fun y : ℝ => M * (y ^ (s.re - 2) * Real.exp (-c * y ^ (1 : ℝ))))
      (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_
    · exact (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl hc).const_mul M
    · exact integrableOn_const (by simp) (by simp)
  refine hdom.mono' hmeas ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ico)] with p hp
  have hp0 : (0 : ℝ) < p.1 := hp.1
  rw [stripChart_stripIntegrand hp0, norm_mul, norm_cpow_eq_rpow_re_of_pos hp0, Real.rpow_one, mul_one]
  have hb' := hb (ofComplex ⟨p.2, p.1⟩)
  rw [ofComplex_mk_im hp0] at hb'
  simp only [sub_re, Complex.re_ofNat]
  calc p.1 ^ (s.re - 2) * ‖F (ofComplex ⟨p.2, p.1⟩)‖ ≤ p.1 ^ (s.re - 2) * (M * Real.exp (-c * p.1)) :=
        mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hp0.le _)
    _ = M * (p.1 ^ (s.re - 2) * Real.exp (-c * p.1)) := by ring

/-- **Unfolding**: `2 ∫_{strip} F Im^s = ∫_𝒟 F · Σ_v Im(M_v z)^s`. -/
theorem two_mul_strip_eq (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) :
    2 * ∫ z in modularStrip, stripIntegrand F s z = ∫ z in ModularGroup.fd, F z * rowSum s z := by
  have hint := integrableOn_stripIntegrand hF hs
  have hφ : ∀ (n : ℤ) (z : ℍ), stripIntegrand F s (ModularGroup.T ^ n • z) = stripIntegrand F s z :=
    fun n z => by
      simp only [stripIntegrand]
      rw [hF.invariant, ModularGroup.im_T_zpow_smul]
  rw [← tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hφ hint]
  have hterm : ∀ (v : gammaSet 1 1 0) (z : ℍ), stripIntegrand F s (gammaSetMatrix v • z) =
      F z * (rowHeight v z : ℂ) ^ s := fun v z => by
    rw [stripIntegrand, hF.invariant]
    rfl
  simp_rw [hterm]
  have hφn : ∀ (n : ℤ) (z : ℍ), ((‖stripIntegrand F s (ModularGroup.T ^ n • z)‖ : ℝ) : ℂ) =
      ((‖stripIntegrand F s z‖ : ℝ) : ℂ) := fun n z => by rw [hφ]
  have hsum := summable_fdUnfoldTerm hφn hint.norm.ofReal
  unfold fdUnfoldTerm at hsum
  simp_rw [integral_ofReal, hterm] at hsum
  rw [integral_tsum_of_summable_integral_norm (fun v => ?_) (Complex.summable_ofReal.1 hsum)]
  · refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
    rw [rowSum, tsum_mul_left]
  · have h1 := (integrableOn_smul_set_iff (gammaSetMatrix v) _ ModularGroup.fd).1
      (integrableOn_smul_fd_of_periodic hφ hint (gammaSetMatrix v))
    exact h1.congr_fun (fun z _ => hterm v z) ModularGroup.isClosed_fd.measurableSet

/-- **The strip integral is the Mellin transform of the response.** -/
theorem strip_eq_mellin (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in modularStrip, stripIntegrand F s z = mellin (response F) (s - 1) := by
  rw [setIntegral_modularStrip_eq_iterated _ (integrableOn_stripIntegrand hF hs), mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have h0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy0.ne'
  have e : ∀ x : ℝ, stripIntegrand F s (ofComplex ⟨x, y⟩) = F (ofComplex ⟨x, y⟩) * (y : ℂ) ^ s := by
    intro x; rw [stripIntegrand, ofComplex_mk_im hy0]
  simp_rw [e]
  rw [integral_mul_const, ← response, Complex.real_smul, smul_eq_mul,
    show s - 1 - 1 = s - 2 by ring, cpow_sub _ _ h0, cpow_two]
  push_cast
  field_simp

/-- **Unfolding of the completed transform**: for `Re s > 1`, `Im s ≠ 0`,
`Λ_F(s) = ξ(2s)/(2s(2s − 1)) · 𝓜a_F(s − 1)`. -/
theorem seedTransform_eq_mellin (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) (him : s.im ≠ 0) :
    seedTransform F s = xi (2 * s) / (2 * s * (2 * s - 1)) * mellin (response F) (s - 1) := by
  have hxi : xi (1 + 2 * (s - 1 / 2)) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  have hpt : ∀ z : ℍ, EisAuto.completedEisenstein (s - 1 / 2) z.re z.im =
      normalizedEisenstein (s - 1 / 2) z.re z.im * (xi (2 * s) / (2 * s * (2 * s - 1))) := by
    intro z
    rw [normalizedEisenstein_eq_numerator_div hxi, EisAuto.completedEisenstein,
      show 1 + 2 * (s - 1 / 2) = 2 * s by ring, show 2 * (s - 1 / 2) = 2 * s - 1 by ring]
    have hx2 : xi (2 * s) ≠ 0 := by rwa [show 1 + 2 * (s - 1 / 2) = 2 * s by ring] at hxi
    rw [div_mul_div_comm, mul_comm (xi (2 * s)) (2 * s * (2 * s - 1)), mul_div_mul_right _ _ hx2]
  have hrow : ∀ z : ℍ, normalizedEisenstein (s - 1 / 2) z.re z.im = (1 / 2 : ℂ) * rowSum s z := by
    intro z
    have := normalizedEisenstein_eq_rowSum (u := s - 1 / 2) (by simp; linarith) (by simpa using him) z
    rw [this, show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring]
  unfold seedTransform
  have e : ∫ z in ModularGroup.fd, F z * EisAuto.completedEisenstein (s - 1 / 2) z.re z.im =
      (xi (2 * s) / (2 * s * (2 * s - 1)) * (1 / 2 : ℂ)) * ∫ z in ModularGroup.fd, F z * rowSum s z := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hpt, hrow]
    ring
  rw [e, ← two_mul_strip_eq hF hs, strip_eq_mellin hF hs]
  ring

/-! ### Position rigidity -/

/-- The continuation `Λ_F(s) · 2s(2s − 1)/ξ(2s)` of the Mellin transform of the response. -/
def responseContinuation (F : ℍ → ℂ) (s : ℂ) : ℂ :=
  seedTransform F s * (2 * s * (2 * s - 1)) / xi (2 * s)

/-- The continuation is the Mellin transform of the response on `Re s > 1`, `Im s ≠ 0`. -/
theorem responseContinuation_eq_mellin (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) (him : s.im ≠ 0) :
    responseContinuation F s = mellin (response F) (s - 1) := by
  have hxi : xi (2 * s) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  have h0 : s ≠ 0 := fun h => him (by rw [h]; simp)
  have h2 : 2 * s - 1 ≠ 0 := fun h => him (by have := congrArg Complex.im h; simp at this; linarith)
  have hden : 2 * s * (2 * s - 1) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero h0) h2
  rw [responseContinuation, seedTransform_eq_mellin hF hs him]
  field_simp

/-- **Position rigidity.** For every seed the continued response transform is holomorphic at every
`s ∉ {0, ½, 1}` with `ξ(2s) ≠ 0`: its only possible resonances are the zeros of `ξ(2s)`. -/
theorem differentiableAt_responseContinuation (hF : IsSeed F) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2)
    (h2 : s ≠ 1) (hxi : xi (2 * s) ≠ 0) : DifferentiableAt ℂ (responseContinuation F) s := by
  have hmem : s ∈ ({0, 1 / 2, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨h0, h1, h2⟩
  have hopen : IsOpen (({0, 1 / 2, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hΛ := (differentiableOn_seedTransform hF).differentiableAt (hopen.mem_nhds hmem)
  have hξ : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s
  exact (hΛ.mul (by fun_prop)).div hξ hxi

/-! ### The receiver -/

theorem mellinConvergent_response (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (response F) (s - 1) := by
  obtain ⟨M, c, hM, hc, hb⟩ := norm_response_le hF
  have hI : IntegrableOn (fun t : ℝ => M * (t ^ (s.re - 2) * Real.exp (-c * t ^ (1 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl hc).const_mul M
  refine Integrable.mono' hI ?_ ?_
  · have hcf : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1 - 1) * response F t) (Ioi 0) := by
      refine ContinuousOn.mul (fun t (ht : 0 < t) => ?_) (continuousOn_response hF)
      exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 ht)).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    simp only [smul_eq_mul]
    exact hcf.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [smul_eq_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Real.rpow_one]
    simp only [sub_re, one_re]
    rw [show s.re - 1 - 1 = s.re - 2 by ring]
    calc t ^ (s.re - 2) * ‖response F t‖ ≤ t ^ (s.re - 2) * (M * Real.exp (-c * t)) :=
          mul_le_mul_of_nonneg_left (hb t ht) (Real.rpow_nonneg ht.le _)
      _ = M * (t ^ (s.re - 2) * Real.exp (-c * t)) := by ring

/-- **The receiver.** A rate `|a_F(y) − c| ≤ C y^α` on `(0, 1]` forces `Λ_F(s₀) = 0` at every zero `s₀`
of `ξ(2s)` with `Re s₀ > 1 − α`. -/
theorem seedTransform_eq_zero_of_rate (hF : IsSeed F) {α : ℝ} {c : ℂ} {C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖response F y - c‖ ≤ C * y ^ α)
    {s₀ : ℂ} (hs₀ : 1 - α < s₀.re) (hz : xi (2 * s₀) = 0) : seedTransform F s₀ = 0 := by
  have him₀ : s₀.im ≠ 0 := by
    intro h
    have e : 2 * s₀ = ((2 * s₀.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
    exact xi_ne_zero_of_real _ (e ▸ hz)
  set ind : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun _ => c with hind
  set rem : ℝ → ℂ := fun y => response F y - ind y with hrem
  obtain ⟨M, κ, hM, hκ, hb⟩ := norm_response_le hF
  have hindM : ∀ w : ℂ, 0 < w.re → MellinConvergent ind w ∧ mellin ind w = c / w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hasMellin_one_Ioc hw
    have hind_smul : ind = fun y => c • (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) y := by
      funext y
      by_cases hy : y ∈ Ioc (0 : ℝ) 1 <;> simp [hind, hy]
    rw [hind_smul]
    refine ⟨h1.const_smul c, ?_⟩
    rw [mellin_const_smul, h2, smul_eq_mul]
    ring
  have hAint : IntegrableOn (response F) (Ioi 0) := by
    have h := mellinConvergent_response hF (s := 2) (by norm_num)
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
  have hindint : IntegrableOn ind (Ioi 0) := by
    have := (hindM 1 one_pos).1
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
  have hsplit : ∀ s : ℂ, 1 < s.re → mellin (response F) (s - 1) = mellin rem (s - 1) + c / (s - 1) := by
    intro s hs
    have hw : 0 < (s - 1).re := by simp; linarith
    have hAM := mellinConvergent_response hF hs
    obtain ⟨hiM, hiV⟩ := hindM (s - 1) hw
    have hgM : MellinConvergent rem (s - 1) := by
      refine (hAM.sub hiM).congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, hrem, smul_sub]
    rw [← hiV, mellin, mellin, mellin, ← integral_add hgM hiM]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hrem, smul_sub, sub_add_cancel]
  have hg_top : rem =O[atTop] fun t => Real.exp (-κ * t) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [eventually_gt_atTop 1] with y hy
    have hy1 : y ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.2 hy) h.2
    have hind0 : ind y = 0 := indicator_of_notMem hy1 _
    rw [show rem y = response F y - ind y from rfl, hind0, sub_zero,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hb y (by linarith)
  have hg_bot : rem =O[𝓝[>] 0] (· ^ (-(-α))) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    have hy1 : y ∈ Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)]
    rw [show rem y = response F y - ind y from rfl, hind, indicator_of_mem hy1]
    exact hrate y hy.1 hy.2.le
  have hgint : LocallyIntegrableOn rem (Ioi 0) := (hAint.sub hindint).locallyIntegrableOn
  set Ψ : ℂ → ℂ := fun s => xi (2 * s) / (2 * s * (2 * s - 1)) * (mellin rem (s - 1) + c / (s - 1))
    with hΨ
  have hdiffΨ : ∀ s : ℂ, 1 - α < s.re → s.im ≠ 0 → DifferentiableAt ℂ Ψ s := by
    intro s hs him
    have h0 : s ≠ 0 := fun h => him (by rw [h]; simp)
    have h1 : s ≠ 1 := fun h => him (by rw [h]; simp)
    have h2 : 2 * s - 1 ≠ 0 := fun h => him (by
      have := congrArg Complex.im h; simp at this; linarith)
    have hden : 2 * s * (2 * s - 1) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero h0) h2
    have hmr : DifferentiableAt ℂ (mellin rem) (s - 1) :=
      mellin_differentiableAt_of_isBigO_rpow_exp hκ hgint hg_top hg_bot (by simp; linarith)
    have hxi : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
      (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s
    have hA := DifferentiableAt.comp (g := mellin rem) (f := fun s : ℂ => s - 1) s hmr
      (differentiableAt_id.sub_const 1)
    have hB : DifferentiableAt ℂ (fun s : ℂ => c / (s - 1)) s :=
      (differentiableAt_const c).div (by fun_prop) (sub_ne_zero.2 h1)
    have hC : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s) / (2 * s * (2 * s - 1))) s :=
      hxi.div (by fun_prop) hden
    exact hC.mul (hA.add hB)
  have hdiffΛ : ∀ s : ℂ, s.im ≠ 0 → DifferentiableAt ℂ (seedTransform F) s := by
    intro s him
    have hmem : s ∈ ({0, 1 / 2, 1} : Set ℂ)ᶜ := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨fun h => him (by rw [h]; simp), fun h => him (by rw [h]; simp),
        fun h => him (by rw [h]; simp)⟩
    have hopen : IsOpen (({0, 1 / 2, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    exact (differentiableOn_seedTransform hF).differentiableAt (hopen.mem_nhds hmem)
  have hEqRight : ∀ s : ℂ, 1 < s.re → s.im ≠ 0 → seedTransform F s = Ψ s := by
    intro s hs him
    rw [seedTransform_eq_mellin hF hs him, hsplit s hs]
  have key : ∀ W : Set ℂ, IsOpen W → IsPreconnected W → (∀ s ∈ W, 1 - α < s.re ∧ s.im ≠ 0) →
      ∀ z₀ ∈ W, 1 < z₀.re → EqOn (seedTransform F) Ψ W := by
    intro W hW hWc hWs z₀ hz₀ hz₀re
    have hfΛ : AnalyticOnNhd ℂ (seedTransform F) W := DifferentiableOn.analyticOnNhd
      (fun s hs => (hdiffΛ s (hWs s hs).2).differentiableWithinAt) hW
    have hfΨ : AnalyticOnNhd ℂ Ψ W := DifferentiableOn.analyticOnNhd
      (fun s hs => (hdiffΨ s (hWs s hs).1 (hWs s hs).2).differentiableWithinAt) hW
    have hev : seedTransform F =ᶠ[𝓝 z₀] Ψ := by
      have hopen : IsOpen ({s : ℂ | 1 < s.re} ∩ W) :=
        (isOpen_lt continuous_const continuous_re).inter hW
      filter_upwards [hopen.mem_nhds ⟨hz₀re, hz₀⟩] with s hs
      exact hEqRight s hs.1 (hWs s hs.2).2
    exact hfΛ.eqOn_of_preconnected_of_eventuallyEq hfΨ hWc hz₀ hev
  have hval : seedTransform F s₀ = Ψ s₀ := by
    rcases lt_or_gt_of_ne him₀ with hneg | hpos
    · set W : Set ℂ := {s | 1 - α < s.re ∧ s.im < 0}
      have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_im continuous_const)
      have hWc : IsPreconnected W :=
        ((convex_halfSpace_re_gt (1 - α)).inter (convex_halfSpace_im_lt 0)).isPreconnected
      have hre : (((max (1 - α) 1 + 1 : ℝ) : ℂ) - I).re = max (1 - α) 1 + 1 := by simp
      refine key W hW hWc (fun s hs => ⟨hs.1, hs.2.ne⟩) (((max (1 - α) 1 + 1 : ℝ) : ℂ) - I)
        ⟨?_, by simp⟩ ?_ ⟨hs₀, hneg⟩
      · rw [hre]; linarith [le_max_left (1 - α) 1]
      · rw [hre]; linarith [le_max_right (1 - α) 1]
    · set W : Set ℂ := {s | 1 - α < s.re ∧ 0 < s.im}
      have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_const continuous_im)
      have hWc : IsPreconnected W :=
        ((convex_halfSpace_re_gt (1 - α)).inter (convex_halfSpace_im_gt 0)).isPreconnected
      have hre : (((max (1 - α) 1 + 1 : ℝ) : ℂ) + I).re = max (1 - α) 1 + 1 := by simp
      refine key W hW hWc (fun s hs => ⟨hs.1, hs.2.ne'⟩) (((max (1 - α) 1 + 1 : ℝ) : ℂ) + I)
        ⟨?_, by simp⟩ ?_ ⟨hs₀, hpos⟩
      · rw [hre]; linarith [le_max_left (1 - α) 1]
      · rw [hre]; linarith [le_max_right (1 - α) 1]
  rw [hval, hΨ]
  simp only [hz, zero_div, zero_mul]

/-- **The receiver at the zeros of `ζ`.** If `|a_F(y) − c| ≤ C y^α` on `(0, 1]`, every zero `ρ` of `ζ` with
`Re ρ > max(0, 2 − 2α)` has `Λ_F(ρ/2) = 0`. -/
theorem seedTransform_half_eq_zero_of_rate (hF : IsSeed F) {α : ℝ} {c : ℂ} {C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖response F y - c‖ ≤ C * y ^ α)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) (hre : 2 - 2 * α < ρ.re) :
    seedTransform F (ρ / 2) = 0 := by
  have hxi : xi ρ = 0 := by
    refine xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.2 ⟨hζ, fun n hn => ?_⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  refine seedTransform_eq_zero_of_rate hF hrate (by simp; linarith) ?_
  rwa [show 2 * (ρ / 2) = ρ by ring]

/-- **A seen resonance caps the rate**: if `ζ(ρ) = 0`, `Re ρ > 0` and `Λ_F(ρ/2) ≠ 0`, no bound
`|a_F(y) − c| ≤ C y^α` on `(0, 1]` holds with `α > 1 − Re ρ/2`. -/
theorem not_rate_of_seen (hF : IsSeed F) {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re)
    (hseen : seedTransform F (ρ / 2) ≠ 0) {α : ℝ} (hα : 1 - ρ.re / 2 < α) (c : ℂ) (C : ℝ) :
    ¬ ∀ y : ℝ, 0 < y → y ≤ 1 → ‖response F y - c‖ ≤ C * y ^ α := fun hrate =>
  hseen (seedTransform_half_eq_zero_of_rate hF hrate hζ hpos (by linarith))

/-! ### Cusp forms are seeds -/

/-- **Cusp forms decay like `e^{−π Im z}`** in the cusp. -/
theorem cuspForm_decay {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℍ, 1 ≤ z.im → ‖g z‖ ≤ D * Real.exp (-Real.pi * z.im) := by
  obtain ⟨ρ, hρ0, hρ⟩ := CuspL.exists_whittaker hg
  obtain ⟨D, hD0, hD⟩ := CuspRSC.norm_point_le hg hρ0 hρ
  refine ⟨D, hD0, fun z hz => ?_⟩
  have hz' : z = ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point z.re z.im) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (HeckeCusp.point_im_pos z.im_pos)]
    apply Complex.ext <;> simp [GaloisForLFunctions.RHTower.SelbergMaassMean.point]
  have h := hD z.re z.im hz
  rw [← hz'] at h
  have hy0 : 0 < z.im := z.im_pos
  have hs : Real.sqrt z.im ≤ Real.exp (Real.pi * z.im) := by
    have h1 : Real.sqrt z.im ≤ z.im := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h2 := Real.add_one_le_exp (Real.pi * z.im)
    nlinarith [Real.pi_gt_three]
  calc ‖g z‖ ≤ D * (Real.sqrt z.im * Real.exp (-(2 * Real.pi * z.im))) := h
    _ ≤ D * (Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) hD0
    _ = D * Real.exp (-Real.pi * z.im) := by rw [← Real.exp_add]; congr 2; ring

/-- **Every Maass cusp form is a seed.** -/
theorem isSeed_of_mem_cuspSpace {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) : IsSeed g := by
  obtain ⟨D, hD0, hD⟩ := cuspForm_decay hg
  exact ⟨hg.1, HeckeCusp.continuous_of_maass hg.2.1, HeckeCusp.exists_bound hg,
    ⟨D, Real.pi, hD0, Real.pi_pos, hD⟩⟩

/-- A bounded function with decay `C e^{−c Im z}` on `Im z ≥ 1` is at most `M e^{−c Im z}` everywhere. -/
theorem exists_global_exp_bound {g : ℍ → ℂ} {B C c : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) (hC : 0 ≤ C) (hc : 0 < c)
    (hd : ∀ z : ℍ, 1 ≤ z.im → ‖g z‖ ≤ C * Real.exp (-c * z.im)) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℍ, ‖g z‖ ≤ M * Real.exp (-c * z.im) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB UpperHalfPlane.I)
  refine ⟨B * Real.exp c + C + 1, by positivity, fun z => ?_⟩
  have hE := Real.exp_pos (-c * z.im)
  by_cases hz : 1 ≤ z.im
  · calc ‖g z‖ ≤ C * Real.exp (-c * z.im) := hd z hz
      _ ≤ (B * Real.exp c + C + 1) * Real.exp (-c * z.im) :=
          mul_le_mul_of_nonneg_right (by nlinarith [Real.exp_pos c]) hE.le
  · have h1 : 1 ≤ Real.exp c * Real.exp (-c * z.im) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [z.im_pos])
    calc ‖g z‖ ≤ B := hB z
      _ ≤ B * (Real.exp c * Real.exp (-c * z.im)) := le_mul_of_one_le_right hB0 h1
      _ ≤ (B * Real.exp c + C + 1) * Real.exp (-c * z.im) := by nlinarith

/-- The energy density `|F|²` of a seed is a seed. -/
theorem IsSeed.normSq (hF : IsSeed F) : IsSeed (fun z => ((‖F z‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨B, hB⟩ := hF.bounded
  obtain ⟨C, c, hC, hc, hd⟩ := hF.decay
  refine ⟨fun γ z => by show ((‖F (γ • z)‖ ^ 2 : ℝ) : ℂ) = ((‖F z‖ ^ 2 : ℝ) : ℂ); rw [hF.invariant],
    Complex.continuous_ofReal.comp (hF.continuous.norm.pow 2), ⟨B ^ 2, fun z => ?_⟩,
    ⟨C ^ 2, 2 * c, sq_nonneg _, by positivity, fun z hz => ?_⟩⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB z) 2
  · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖F z‖ ^ 2 ≤ (C * Real.exp (-c * z.im)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd z hz) 2
      _ = C ^ 2 * Real.exp (-(2 * c) * z.im) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

/-- The energy density `|g|²` of a cusp form is a seed. -/
theorem isSeed_normSq_of_mem_cuspSpace {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) :
    IsSeed (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) :=
  (isSeed_of_mem_cuspSpace hg).normSq

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
