import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers
import GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarIsCoerciveAndPrimeBlind
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilSymbolIsALogarithmicMultiplierPlusABoundedKernel
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers

/-!
# The state solves a logarithmic equation on every window of the half-line

Write `ω` for the Lévy density of the Gamma form, `ν(x) = e^{−x}/(2x)` for the Lévy density of the
logarithmic multiplier `½ log(1 + ξ²)`, and `r = ω − ν`, a bounded integrable kernel. Fix a window
`[c, d]` with `d ≤ 0` and a Lipschitz cutoff `χ` with values in `[0, 1]` that vanishes on the negative
half-line outside the window (`IsWindowCutoff`); `U = χF` is the state cut off to the window. Tests are
profiles of the energy domain carried by the window (`IsCarriedTest`).

**Theorem** (`criticalState_logarithmic_equation_on_window`). There is a function `g`, bounded on the
window, such that for every test `G`

  `∫ U G + ∫_{x>0} ν(x) ∫ (U(u) − U(u+x)) (G(u) − G(u+x)) du dx = ∫ G g`.

The left side is the logarithmic full form of `(U, G)`: `U` solves the logarithmic equation on the
window with a bounded forcing.

Mechanism. The jump form of `ν` is the Gamma jump form minus the jump form of `r`, which is a mass
term minus two convolutions with `r` (`isBoundedForcingOn_remainderJump`). Moving `χ` from `F` to the
test costs the commutator `∫_{x>0} ω(x) ∫ (χ(u) − χ(u+x)) (F(u+x) G(u) − F(u) G(u+x))`, a
convolution with a kernel bounded by `ω(x) min(Λx, 1) ≤ (3Λ + 2) e^{−x/2}`
(`levyMixed_cutoff_commutator`). Against `χG` the weak equation is the window equation
(`criticalState_window_equation`): the Gamma form is the prime wave
`Σ Λ(n) n^{−½} (F(u + log n) + F(u − log n))` minus the pole and confinement pairings. The state is
essentially bounded with `|F(u)| ≤ C e^{2u}`, so on the window the backward wave converges absolutely
and the forward wave has finitely many terms, `F` vanishing on `[0, ∞)`. Every term integrates `G`
against a function bounded on the window.

The wall ramp (`wallRamp`, window `[−½, 0]`) and the interior cutoff around a point `p`
(`interiorCutoff`, window `[p − ¾, p + ¼]`) are window cutoffs.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Moving a kernel onto the test -/

/-- **A kernel bounded by an integrable function of the lag moves onto the test.** If
`|φ(x, u)| ≤ m(x)` for `x > 0` with `m` integrable on `(0, ∞)`, and `F, G` are square integrable, then
`x ↦ ∫ φ(x,u) F(u + σx) G(u) du` is integrable on `(0, ∞)` and
`∫_{x>0} ∫ φ(x,u) F(u + σx) G(u) du dx = ∫ (∫_{x>0} φ(x,u) F(u + σx) dx) G(u) du`. -/
theorem kernel_translate_pairing {m : ℝ → ℝ} (hm : IntegrableOn m (Ioi 0))
    {φ : ℝ → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ))
    (hφm : ∀ x ∈ Ioi (0 : ℝ), ∀ u, |φ x u| ≤ m x) {F G : ℝ → ℝ} (hFm : Measurable F)
    (hGm : Measurable G) (hF2 : Integrable fun u => F u ^ 2) (hG2 : Integrable fun u => G u ^ 2)
    (σ : ℝ) :
    IntegrableOn (fun x => ∫ u, φ x u * F (u + σ * x) * G u) (Ioi 0) ∧
      (∫ x in Ioi 0, ∫ u, φ x u * F (u + σ * x) * G u) =
        ∫ u, (∫ x in Ioi 0, φ x u * F (u + σ * x)) * G u := by
  let f : ℝ × ℝ → ℝ := fun p => φ p.1 p.2 * F (p.2 + σ * p.1) * G p.2
  have hfm : Measurable f :=
    (hφ.mul (hFm.comp (measurable_snd.add (measurable_fst.const_mul σ)))).mul
      (hGm.comp measurable_snd)
  have hb : ∀ x ∈ Ioi (0 : ℝ), ∀ u, ‖f (x, u)‖ ≤ m x * ((F (u + σ * x) ^ 2 + G u ^ 2) / 2) := by
    intro x hx u
    have h1 := hφm x hx u
    have hm0 : 0 ≤ m x := (abs_nonneg _).trans h1
    have h2 : |F (u + σ * x)| * |G u| ≤ (F (u + σ * x) ^ 2 + G u ^ 2) / 2 := by
      nlinarith only [sq_nonneg (|F (u + σ * x)| - |G u|), sq_abs (F (u + σ * x)), sq_abs (G u)]
    show ‖φ x u * F (u + σ * x) * G u‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul h1 h2 (by positivity) hm0
  have hFs : ∀ x, Integrable fun u => F (u + σ * x) ^ 2 := fun x =>
    hF2.comp_add_right (σ * x)
  have hFsI : ∀ x, (∫ u, F (u + σ * x) ^ 2) = ∫ u, F u ^ 2 := fun x =>
    integral_add_right_eq_self (fun u => F u ^ 2) (σ * x)
  have hint : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Integrable.mono' ((((hFs x).add hG2).div_const 2).const_mul (m x))
        (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall fun u => hb x hx u)
    · refine Integrable.mono' (hm.mul_const (((∫ u, F u ^ 2) + ∫ u, G u ^ 2) / 2))
        (hfm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
      calc (∫ u, ‖f (x, u)‖) ≤ ∫ u, m x * ((F (u + σ * x) ^ 2 + G u ^ 2) / 2) :=
            integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
              ((((hFs x).add hG2).div_const 2).const_mul (m x))
              (Eventually.of_forall fun u => hb x hx u)
        _ = m x * (((∫ u, F u ^ 2) + ∫ u, G u ^ 2) / 2) := by
            rw [integral_const_mul, integral_div, integral_add (hFs x) hG2, hFsI]
  refine ⟨hint.integral_prod_left, ?_⟩
  have hswap := integral_integral_swap (f := fun x u => φ x u * F (u + σ * x) * G u) hint
  rw [hswap]
  exact integral_congr_ae (Eventually.of_forall fun u => integral_mul_const (G u) _)

/-- The kernel integral `u ↦ ∫_{x>0} φ(x,u) F(u + σx) dx` is strongly measurable. -/
theorem stronglyMeasurable_kernel_translate {φ : ℝ → ℝ → ℝ}
    (hφ : Measurable (Function.uncurry φ)) {F : ℝ → ℝ} (hFm : Measurable F) (σ : ℝ) :
    StronglyMeasurable fun u => ∫ x in Ioi 0, φ x u * F (u + σ * x) := by
  have h : Measurable fun p : ℝ × ℝ => φ p.2 p.1 * F (p.1 + σ * p.2) :=
    (hφ.comp measurable_swap).mul (hFm.comp (measurable_fst.add (measurable_snd.const_mul σ)))
  exact h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

/-- A kernel integral of an essentially bounded profile is bounded: `|∫ φ F(u ± x)| ≤ C ∫ m`. -/
theorem abs_kernel_translate_le {m : ℝ → ℝ} (hm : IntegrableOn m (Ioi 0)) {φ : ℝ → ℝ → ℝ}
    (hφm : ∀ x ∈ Ioi (0 : ℝ), ∀ u, |φ x u| ≤ m x) {F : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᵐ v, |F v| ≤ C) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (u : ℝ) :
    |∫ x in Ioi 0, φ x u * F (u + σ * x)| ≤ C * ∫ x in Ioi 0, m x := by
  have hae : ∀ᵐ x : ℝ, |F (u + σ * x)| ≤ C := by
    rcases hσ with rfl | rfl
    · have h := (measurePreserving_add_left (volume : Measure ℝ) u).quasiMeasurePreserving.ae hb
      filter_upwards [h] with x hx
      rwa [one_mul]
    · have h1 : ∀ᵐ x : ℝ, |F (x - -u)| ≤ C :=
        (measurePreserving_sub_right (volume : Measure ℝ) (-u)).quasiMeasurePreserving.ae hb
      have h2 : ∀ᵐ x : ℝ, |F (-x - -u)| ≤ C :=
        (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
      filter_upwards [h2] with x hx
      rwa [show u + -1 * x = -x - -u by ring]
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hm.const_mul C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hae] with x hx hFx
  have h1 := hφm x hx u
  have hm0 : 0 ≤ m x := (abs_nonneg _).trans h1
  rw [Real.norm_eq_abs, abs_mul]
  calc |φ x u| * |F (u + σ * x)| ≤ m x * C := mul_le_mul h1 hFx (abs_nonneg _) hm0
    _ = C * m x := mul_comm _ _

/-! ### Window cutoffs -/

/-- A **window cutoff** for `[c, d]`: continuous, with values in `[0, 1]`, Lipschitz with constant `Λ`,
and zero on the negative half-line outside `[c, d]`. -/
structure IsWindowCutoff (c d Λ : ℝ) (χ : ℝ → ℝ) : Prop where
  continuous : Continuous χ
  nonneg : ∀ u, 0 ≤ χ u
  le_one : ∀ u, χ u ≤ 1
  lipschitz : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|
  vanish : ∀ u, u ∉ Icc c d → u < 0 → χ u = 0

theorem IsWindowCutoff.abs_le_one {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ) (u : ℝ) :
    |χ u| ≤ 1 := by
  rw [abs_of_nonneg (hχ.nonneg u)]
  exact hχ.le_one u

theorem IsWindowCutoff.lipschitz_nonneg {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ) :
    0 ≤ Λ := by
  have h := (abs_nonneg _).trans (hχ.lipschitz 0 1)
  rwa [zero_sub, abs_neg, abs_one, mul_one] at h

/-- A jump of a window cutoff over a lag `x > 0` is at most `min(Λx, 1)`. -/
theorem IsWindowCutoff.abs_sub_shift_le {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ)
    {x : ℝ} (hx : 0 < x) (u : ℝ) : |χ u - χ (u + x)| ≤ min (Λ * x) 1 := by
  refine le_min ?_ ?_
  · have h := hχ.lipschitz u (u + x)
    rwa [show u - (u + x) = -x by ring, abs_neg, abs_of_pos hx] at h
  · rw [abs_le]
    constructor <;> linarith [hχ.nonneg u, hχ.le_one u, hχ.nonneg (u + x), hχ.le_one (u + x)]

/-- `ω(x) min(Λx, 1) ≤ (3Λ + 2) e^{−x/2}`: the commutator kernel of a cutoff is integrable. -/
theorem archLevyDensity_mul_min_le {Λ x : ℝ} (hΛ : 0 ≤ Λ) (hx : 0 < x) :
    archLevyDensity x * min (Λ * x) 1 ≤ (3 * Λ + 2) * Real.exp (-(x / 2)) := by
  have hm0 : 0 ≤ min (Λ * x) 1 := le_min (mul_nonneg hΛ hx.le) zero_le_one
  rcases le_total x 1 with h1 | h1
  · have h2 := archLevyDensity_le_near hx h1
    have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(x / 2)) := by
      have := Real.add_one_le_exp (-(x / 2))
      linarith
    calc archLevyDensity x * min (Λ * x) 1 ≤ 3 / (2 * x) * (Λ * x) :=
          mul_le_mul h2 (min_le_left _ _) hm0 (by positivity)
      _ = 3 / 2 * Λ := by
          rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
          ring
      _ ≤ (3 * Λ + 2) * Real.exp (-(x / 2)) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Λ + 2) (sub_nonneg.mpr hexp)]
  · have h2 := archLevyDensity_le_far h1
    calc archLevyDensity x * min (Λ * x) 1 ≤ 2 * Real.exp (-(x / 2)) * 1 :=
          mul_le_mul h2 (min_le_right _ _) hm0 (by positivity)
      _ ≤ (3 * Λ + 2) * Real.exp (-(x / 2)) := by nlinarith [Real.exp_pos (-(x / 2))]

/-- The wall ramp: `0` left of `−½`, `1` right of `−¼`, linear in between. -/
def wallRamp (u : ℝ) : ℝ := min (max (4 * u + 2) 0) 1

theorem continuous_wallRamp : Continuous wallRamp := by
  unfold wallRamp
  fun_prop

theorem measurable_wallRamp : Measurable wallRamp := continuous_wallRamp.measurable

theorem wallRamp_nonneg (u : ℝ) : 0 ≤ wallRamp u :=
  le_min (le_max_right _ _) zero_le_one

theorem wallRamp_le_one (u : ℝ) : wallRamp u ≤ 1 := min_le_right _ _

theorem abs_wallRamp_le_one (u : ℝ) : |wallRamp u| ≤ 1 := by
  rw [abs_of_nonneg (wallRamp_nonneg u)]
  exact wallRamp_le_one u

theorem wallRamp_of_le {u : ℝ} (hu : u ≤ -(1 / 2)) : wallRamp u = 0 := by
  unfold wallRamp
  rw [max_eq_right (by linarith), min_eq_left zero_le_one]

theorem wallRamp_of_ge {u : ℝ} (hu : -(1 / 4) ≤ u) : wallRamp u = 1 := by
  unfold wallRamp
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

theorem abs_wallRamp_sub_le (u v : ℝ) : |wallRamp u - wallRamp v| ≤ 4 * |u - v| := by
  unfold wallRamp
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le ((abs_max_sub_max_le_max _ _ _ _).trans ?_) (by positivity)
  rw [sub_self, abs_zero]
  refine max_le (le_of_eq ?_) (by positivity)
  rw [show 4 * u + 2 - (4 * v + 2) = 4 * (u - v) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]

theorem isWindowCutoff_wallRamp : IsWindowCutoff (-(1 / 2)) 0 4 wallRamp :=
  ⟨continuous_wallRamp, wallRamp_nonneg, wallRamp_le_one, abs_wallRamp_sub_le, fun u hu hu0 =>
    wallRamp_of_le (by
      by_contra h
      exact hu ⟨le_of_lt (not_le.mp h), hu0.le⟩)⟩

/-- The interior cutoff around `p`: `1` on `[p − ½, p + ⅛]`, `0` outside `[p − ¾, p + ¼]`, linear in
between. -/
def interiorCutoff (p u : ℝ) : ℝ := max (min (min (4 * (u - p) + 3) 1) (2 - 8 * (u - p))) 0

theorem continuous_interiorCutoff (p : ℝ) : Continuous (interiorCutoff p) := by
  unfold interiorCutoff
  fun_prop

theorem interiorCutoff_eq_one {p u : ℝ} (h1 : p - 1 / 2 ≤ u) (h2 : u ≤ p + 1 / 8) :
    interiorCutoff p u = 1 := by
  have hA : (1 : ℝ) ≤ 4 * (u - p) + 3 := by linarith
  have hB : (1 : ℝ) ≤ 2 - 8 * (u - p) := by linarith
  unfold interiorCutoff
  rw [min_eq_right hA, min_eq_left hB, max_eq_left zero_le_one]

theorem isWindowCutoff_interiorCutoff (p : ℝ) :
    IsWindowCutoff (p - 3 / 4) (p + 1 / 4) 8 (interiorCutoff p) := by
  refine ⟨continuous_interiorCutoff p, fun u => le_max_right _ _, fun u => ?_, fun u v => ?_,
    fun u hu _ => ?_⟩
  · exact max_le ((min_le_left _ _).trans (min_le_right _ _)) zero_le_one
  · unfold interiorCutoff
    refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    refine max_le ((abs_min_sub_min_le_max _ _ _ _).trans (max_le
      ((abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)) ?_)) (by positivity)
    · rw [show 4 * (u - p) + 3 - (4 * (v - p) + 3) = 4 * (u - v) by ring, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [abs_nonneg (u - v)]
    · rw [sub_self, abs_zero]
      positivity
    · rw [show 2 - 8 * (u - p) - (2 - 8 * (v - p)) = -8 * (u - v) by ring, abs_mul]
      norm_num
  · unfold interiorCutoff
    rcases not_and_or.mp (show ¬(p - 3 / 4 ≤ u ∧ u ≤ p + 1 / 4) from hu) with h | h
    · exact max_eq_right ((min_le_left _ _).trans ((min_le_left _ _).trans (by linarith)))
    · exact max_eq_right ((min_le_right _ _).trans (by linarith))

/-! ### Carried tests and bounded forcings -/

/-- A **test carried by `[c, d]`** is a profile of the energy domain vanishing outside `[c, d]`. -/
structure IsCarriedTest (c d : ℝ) (G : ℝ → ℝ) : Prop where
  domain : CriticalHalfLineEnergyDomain G
  vanish : ∀ x, x ∉ Icc c d → G x = 0

/-- A cutoff keeps the tests of its window. -/
theorem IsCarriedTest.cutoff {c d Λ : ℝ} {χ G : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ)
    (hG : IsCarriedTest c d G) : IsCarriedTest c d fun u => χ u * G u :=
  ⟨criticalHalfLineEnergyDomain_lipschitz_mul hG.domain hχ.continuous.measurable hχ.abs_le_one
    hχ.lipschitz, fun x hx => by rw [hG.vanish x hx, mul_zero]⟩

/-- A functional on the tests of `[c, d]` is a **bounded forcing** when it integrates the test against
a function bounded on the window. -/
def IsBoundedForcingOn (c d : ℝ) (T : (ℝ → ℝ) → ℝ) : Prop :=
  ∃ h : ℝ → ℝ, AEStronglyMeasurable h volume ∧
    (∃ C, ∀ᵐ y, y ∈ Icc c d → |h y| ≤ C) ∧ ∀ G, IsCarriedTest c d G → T G = ∫ y, G y * h y

theorem IsCarriedTest.integrable_mul {c d : ℝ} {G h : ℝ → ℝ} (hG : IsCarriedTest c d G)
    (hh : AEStronglyMeasurable h volume) {C : ℝ}
    (hC : ∀ᵐ y, y ∈ Icc c d → |h y| ≤ C) : Integrable fun y => G y * h y := by
  refine (hG.domain.integrable.norm.const_mul C).mono'
    (hG.domain.meas.aestronglyMeasurable.mul hh) ?_
  filter_upwards [hC] with y hy
  by_cases hm : y ∈ Icc c d
  · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hy hm) (abs_nonneg _)
  · simp only [hG.vanish y hm, zero_mul, norm_zero, mul_zero, le_refl]

theorem IsBoundedForcingOn.congr {c d : ℝ} {T₁ T₂ : (ℝ → ℝ) → ℝ} (h : IsBoundedForcingOn c d T₁)
    (he : ∀ G, IsCarriedTest c d G → T₁ G = T₂ G) : IsBoundedForcingOn c d T₂ := by
  obtain ⟨g, hm, hC, hg⟩ := h
  exact ⟨g, hm, hC, fun G hG => (he G hG).symm.trans (hg G hG)⟩

theorem IsBoundedForcingOn.add {c d : ℝ} {T₁ T₂ : (ℝ → ℝ) → ℝ} (h₁ : IsBoundedForcingOn c d T₁)
    (h₂ : IsBoundedForcingOn c d T₂) : IsBoundedForcingOn c d fun G => T₁ G + T₂ G := by
  obtain ⟨g₁, hm₁, ⟨C₁, hC₁⟩, he₁⟩ := h₁
  obtain ⟨g₂, hm₂, ⟨C₂, hC₂⟩, he₂⟩ := h₂
  refine ⟨fun y => g₁ y + g₂ y, hm₁.add hm₂, ⟨C₁ + C₂, ?_⟩, fun G hG => ?_⟩
  · filter_upwards [hC₁, hC₂] with y h1 h2 hy
    exact (abs_add_le _ _).trans (add_le_add (h1 hy) (h2 hy))
  · show T₁ G + T₂ G = ∫ y, G y * (g₁ y + g₂ y)
    rw [he₁ G hG, he₂ G hG,
      ← integral_add (hG.integrable_mul hm₁ hC₁) (hG.integrable_mul hm₂ hC₂)]
    exact integral_congr_ae (Eventually.of_forall fun y => (mul_add _ _ _).symm)

theorem IsBoundedForcingOn.const_mul {c d : ℝ} {T : (ℝ → ℝ) → ℝ} (h : IsBoundedForcingOn c d T)
    (a : ℝ) : IsBoundedForcingOn c d fun G => a * T G := by
  obtain ⟨g, hm, ⟨C, hC⟩, he⟩ := h
  refine ⟨fun y => a * g y, hm.const_mul a, ⟨|a| * C, ?_⟩, fun G hG => ?_⟩
  · filter_upwards [hC] with y h1 hy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h1 hy) (abs_nonneg a)
  · show a * T G = ∫ y, G y * (a * g y)
    rw [he G hG, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)

theorem IsBoundedForcingOn.sub {c d : ℝ} {T₁ T₂ : (ℝ → ℝ) → ℝ} (h₁ : IsBoundedForcingOn c d T₁)
    (h₂ : IsBoundedForcingOn c d T₂) : IsBoundedForcingOn c d fun G => T₁ G - T₂ G :=
  (h₁.add (h₂.const_mul (-1))).congr fun G _ => by ring

/-- Integration against an essentially bounded function is a bounded forcing. -/
theorem isBoundedForcingOn_mass {c d : ℝ} {V : ℝ → ℝ} (hV : AEStronglyMeasurable V volume)
    {C : ℝ} (hC : ∀ᵐ u, |V u| ≤ C) : IsBoundedForcingOn c d fun G => ∫ u, V u * G u :=
  ⟨V, hV, ⟨C, hC.mono fun _ h _ => h⟩, fun _ _ =>
    integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)⟩

/-- Integration against a continuous function is a bounded forcing (the window is compact). -/
theorem isBoundedForcingOn_continuous {c d : ℝ} {k : ℝ → ℝ} (hk : Continuous k) :
    IsBoundedForcingOn c d fun G => ∫ y, G y * k y := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := d)).exists_bound_of_continuousOn
    (f := k) hk.continuousOn
  exact ⟨k, hk.aestronglyMeasurable,
    ⟨C, Eventually.of_forall fun y hy => by simpa only [Real.norm_eq_abs] using hC y hy⟩,
    fun _ _ => rfl⟩

/-- The state is essentially bounded, with `|F(u)| ≤ C e^{2u}`. -/
theorem criticalState_ae_abs_le {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C, 0 ≤ C ∧ (∀ᵐ u, |F u| ≤ C * Real.exp (2 * u)) ∧ ∀ᵐ u, |F u| ≤ C := by
  obtain ⟨C, hC, hbexp⟩ :=
    (criticalHalfLineGroundState_exponential_bounds hW ht hF).1 2 (by norm_num) (by norm_num)
  refine ⟨C, hC, hbexp, ?_⟩
  filter_upwards [hbexp] with u hu
  rcases le_or_gt 0 u with h0 | h0
  · rw [hF.2.2.2.2.2.1 u h0, abs_zero]
    exact hC
  · exact hu.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith)))

/-! ### The remainder kernel `r = ω − ν` -/

open CanonicalSystemOfTheWindowTower in
/-- The jump integrand of the remainder kernel is integrable: `0 ≤ r ≤ ω`. -/
theorem integrableOn_remainderJump {U G : ℝ → ℝ} (hU : CriticalHalfLineEnergyDomain U)
    (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (fun x => archLogRemainder x * ∫ u, (U u - U (u + x)) * (G u - G (u + x)))
      (Ioi 0) := by
  have h := (integrableOn_levyMixedIntegrand hU hG).bdd_mul (c := 1)
    (f := fun x => archLogRemainder x / archLevyDensity x)
    ((measurable_archLogRemainder.div measurable_archLevyDensity).aestronglyMeasurable) ?_
  · refine IntegrableOn.congr_fun (show IntegrableOn _ (Ioi 0) volume from h) (fun x hx => ?_)
      measurableSet_Ioi
    have hω := (archLevyDensity_pos hx).ne'
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hω := archLevyDensity_pos hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (archLogRemainder_nonneg hx) hω.le),
      div_le_one hω]
    exact archLogRemainder_le_density hx

open CanonicalSystemOfTheWindowTower in
/-- The jump integrand of the logarithmic reference density is integrable on the energy domain. -/
theorem integrableOn_logJump {U G : ℝ → ℝ} (hU : CriticalHalfLineEnergyDomain U)
    (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (fun x => logReferenceLevyDensity x * ∫ u, (U u - U (u + x)) * (G u - G (u + x)))
      (Ioi 0) := by
  refine ((integrableOn_levyMixedIntegrand hU hG).sub (integrableOn_remainderJump hU hG)).congr_fun
    (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, archLogRemainder]
  ring

/-- Expansion of a jump pairing: `∫ ΔU ΔG = 2 ∫ UG − ∫ U(u − x) G(u) − ∫ U(u + x) G(u)`. -/
theorem integral_jump_mul_jump_eq {U G : ℝ → ℝ} (hU : MemLp U 2 volume) (hG : MemLp G 2 volume)
    (x : ℝ) :
    (∫ u, (U u - U (u + x)) * (G u - G (u + x))) =
      2 * (∫ u, U u * G u) - (∫ u, U (u + -1 * x) * G u) - ∫ u, U (u + 1 * x) * G u := by
  have hUx := memLp_two_shift hU x
  have hGx := memLp_two_shift hG x
  have i1 := integrable_mul_of_memLp hU hG
  have i2 := integrable_mul_of_memLp hU hGx
  have i3 := integrable_mul_of_memLp hUx hG
  have i4 := integrable_mul_of_memLp hUx hGx
  have e4 : (∫ u, U (u + x) * G (u + x)) = ∫ u, U u * G u :=
    integral_add_right_eq_self (fun u => U u * G u) x
  have e2 : (∫ u, U u * G (u + x)) = ∫ u, U (u + -1 * x) * G u := by
    have h := integral_add_right_eq_self (μ := volume) (fun u => U (u + -1 * x) * G u) x
    simp only [show ∀ u : ℝ, u + x + -1 * x = u from fun u => by ring] at h
    exact h
  have e3 : (∫ u, U (u + 1 * x) * G u) = ∫ u, U (u + x) * G u := by simp only [one_mul]
  have hexp : (fun u => (U u - U (u + x)) * (G u - G (u + x))) =
      fun u => ((U u * G u - U u * G (u + x)) - U (u + x) * G u) + U (u + x) * G (u + x) := by
    funext u
    ring
  have j12 : Integrable (fun u => U u * G u - U u * G (u + x)) := i1.sub i2
  have j123 : Integrable (fun u => U u * G u - U u * G (u + x) - U (u + x) * G u) := j12.sub i3
  rw [hexp, integral_add j123 i4, integral_sub j12 i3, integral_sub i1 i2, e4, e2, e3]
  ring

open CanonicalSystemOfTheWindowTower in
/-- **The remainder jump form is a mass term minus two convolutions with `r`.** -/
theorem remainderJump_eq {U G : ℝ → ℝ} (hUm : Measurable U) (hGm : Measurable G)
    (hU2 : Integrable fun u => U u ^ 2) (hG2 : Integrable fun u => G u ^ 2) :
    (∫ x in Ioi 0, archLogRemainder x * ∫ u, (U u - U (u + x)) * (G u - G (u + x))) =
      2 * (∫ x in Ioi 0, archLogRemainder x) * (∫ u, U u * G u) -
        (∫ u, (∫ x in Ioi 0, archLogRemainder x * U (u + -1 * x)) * G u) -
          ∫ u, (∫ x in Ioi 0, archLogRemainder x * U (u + 1 * x)) * G u := by
  have hUL : MemLp U 2 volume := (memLp_two_iff_integrable_sq hUm.aestronglyMeasurable).mpr hU2
  have hGL : MemLp G 2 volume := (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr hG2
  have hφ : Measurable (Function.uncurry fun x (_ : ℝ) => archLogRemainder x) :=
    measurable_archLogRemainder.comp measurable_fst
  have hb : ∀ x ∈ Ioi (0 : ℝ), ∀ u : ℝ,
      |(fun x (_ : ℝ) => archLogRemainder x) x u| ≤ archLogRemainder x := fun x hx _ =>
    (abs_of_nonneg (archLogRemainder_nonneg hx)).le
  obtain ⟨iM, eM⟩ := kernel_translate_pairing integrableOn_archLogRemainder hφ hb hUm hGm hU2 hG2 (-1)
  obtain ⟨iP, eP⟩ := kernel_translate_pairing integrableOn_archLogRemainder hφ hb hUm hGm hU2 hG2 1
  have hpull : ∀ σ x : ℝ, (∫ u, archLogRemainder x * U (u + σ * x) * G u) =
      archLogRemainder x * ∫ u, U (u + σ * x) * G u := fun σ x => by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      archLogRemainder x * (∫ u, (U u - U (u + x)) * (G u - G (u + x))) =
        2 * (∫ u, U u * G u) * archLogRemainder x -
          (∫ u, archLogRemainder x * U (u + -1 * x) * G u) -
            ∫ u, archLogRemainder x * U (u + 1 * x) * G u := fun x _ => by
    rw [integral_jump_mul_jump_eq hUL hGL x, hpull, hpull]
    ring
  have hc : IntegrableOn (fun x => 2 * (∫ u, U u * G u) * archLogRemainder x) (Ioi 0) :=
    integrableOn_archLogRemainder.const_mul _
  have j1 : IntegrableOn (fun x => 2 * (∫ u, U u * G u) * archLogRemainder x -
      ∫ u, archLogRemainder x * U (u + -1 * x) * G u) (Ioi 0) := hc.sub iM
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub j1 iP, integral_sub hc iM,
    integral_const_mul, eM, eP]
  ring

open CanonicalSystemOfTheWindowTower in
/-- The remainder jump form against an essentially bounded profile is a bounded forcing on every window. -/
theorem isBoundedForcingOn_remainderJump {c d : ℝ} {U : ℝ → ℝ} (hU : CriticalHalfLineEnergyDomain U)
    {C : ℝ} (hC : ∀ᵐ u, |U u| ≤ C) :
    IsBoundedForcingOn c d fun G =>
      ∫ x in Ioi 0, archLogRemainder x * ∫ u, (U u - U (u + x)) * (G u - G (u + x)) := by
  have hφ : Measurable (Function.uncurry fun x (_ : ℝ) => archLogRemainder x) :=
    measurable_archLogRemainder.comp measurable_fst
  have hb : ∀ x ∈ Ioi (0 : ℝ), ∀ u : ℝ,
      |(fun x (_ : ℝ) => archLogRemainder x) x u| ≤ archLogRemainder x := fun x hx _ =>
    (abs_of_nonneg (archLogRemainder_nonneg hx)).le
  have hk : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → IsBoundedForcingOn c d fun G =>
      ∫ u, (∫ x in Ioi 0, archLogRemainder x * U (u + σ * x)) * G u := fun σ hσ =>
    isBoundedForcingOn_mass
      (stronglyMeasurable_kernel_translate hφ hU.meas σ).aestronglyMeasurable
      (Eventually.of_forall fun u =>
        abs_kernel_translate_le integrableOn_archLogRemainder hb hC hσ u)
  refine ((((isBoundedForcingOn_mass hU.meas.aestronglyMeasurable hC).const_mul
    (2 * ∫ x in Ioi 0, archLogRemainder x)).sub (hk (-1) (Or.inr rfl))).sub
      (hk 1 (Or.inl rfl))).congr fun G hG => ?_
  rw [remainderJump_eq hU.meas hG.domain.meas hU.sq hG.domain.sq]

/-! ### The commutator of a cutoff -/

/-- The kernel of the commutator on forward translates. -/
def cutoffKernelRight (χ : ℝ → ℝ) (x u : ℝ) : ℝ := archLevyDensity x * (χ u - χ (u + x))

/-- The kernel of the commutator on backward translates. -/
def cutoffKernelLeft (χ : ℝ → ℝ) (x u : ℝ) : ℝ := archLevyDensity x * (χ (u + -1 * x) - χ u)

theorem measurable_cutoffKernelRight {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Measurable (Function.uncurry (cutoffKernelRight χ)) :=
  (measurable_archLevyDensity.comp measurable_fst).mul
    ((hχ.measurable.comp measurable_snd).sub (hχ.measurable.comp (measurable_snd.add measurable_fst)))

theorem measurable_cutoffKernelLeft {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Measurable (Function.uncurry (cutoffKernelLeft χ)) :=
  (measurable_archLevyDensity.comp measurable_fst).mul
    ((hχ.measurable.comp (measurable_snd.add (measurable_fst.const_mul (-1)))).sub
      (hχ.measurable.comp measurable_snd))

theorem abs_cutoffKernelRight_le {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ) :
    ∀ x ∈ Ioi (0 : ℝ), ∀ u, |cutoffKernelRight χ x u| ≤ (3 * Λ + 2) * Real.exp (-(x / 2)) := by
  intro x hx u
  have hx0 : (0 : ℝ) < x := hx
  unfold cutoffKernelRight
  rw [abs_mul, abs_of_pos (archLevyDensity_pos hx0)]
  exact (mul_le_mul_of_nonneg_left (hχ.abs_sub_shift_le hx0 u)
    (archLevyDensity_pos hx0).le).trans (archLevyDensity_mul_min_le hχ.lipschitz_nonneg hx0)

theorem abs_cutoffKernelLeft_le {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ) :
    ∀ x ∈ Ioi (0 : ℝ), ∀ u, |cutoffKernelLeft χ x u| ≤ (3 * Λ + 2) * Real.exp (-(x / 2)) := by
  intro x hx u
  have hx0 : (0 : ℝ) < x := hx
  unfold cutoffKernelLeft
  rw [abs_mul, abs_of_pos (archLevyDensity_pos hx0)]
  have h := hχ.abs_sub_shift_le hx0 (u + -1 * x)
  rw [show u + -1 * x + x = u by ring] at h
  exact (mul_le_mul_of_nonneg_left h (archLevyDensity_pos hx0).le).trans
    (archLevyDensity_mul_min_le hχ.lipschitz_nonneg hx0)

theorem integrableOn_cutoffKernelBound (Λ : ℝ) :
    IntegrableOn (fun x : ℝ => (3 * Λ + 2) * Real.exp (-(x / 2))) (Ioi 0) :=
  integrableOn_exp_neg_half.const_mul _

/-- **The commutator of a cutoff with the Lévy form** is two kernel convolutions:
`levyMixed (χF) G − levyMixed F (χG) = ∫ (∫ κ₊ F(u + x)) G − ∫ (∫ κ₋ F(u − x)) G`. -/
theorem levyMixed_cutoff_commutator {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ)
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    levyMixed (fun u => χ u * F u) G - levyMixed F (fun u => χ u * G u) =
      (∫ u, (∫ x in Ioi 0, cutoffKernelRight χ x u * F (u + 1 * x)) * G u) -
        ∫ u, (∫ x in Ioi 0, cutoffKernelLeft χ x u * F (u + -1 * x)) * G u := by
  have hU := criticalHalfLineEnergyDomain_lipschitz_mul hF hχ.continuous.measurable hχ.abs_le_one
    hχ.lipschitz
  have hχG := criticalHalfLineEnergyDomain_lipschitz_mul hG hχ.continuous.measurable
    hχ.abs_le_one hχ.lipschitz
  obtain ⟨i₁, e₁⟩ := kernel_translate_pairing (integrableOn_cutoffKernelBound Λ)
    (measurable_cutoffKernelRight hχ.continuous) (abs_cutoffKernelRight_le hχ) hF.meas hG.meas
    hF.sq hG.sq 1
  obtain ⟨i₂, e₂⟩ := kernel_translate_pairing (integrableOn_cutoffKernelBound Λ)
    (measurable_cutoffKernelLeft hχ.continuous) (abs_cutoffKernelLeft_le hχ) hF.meas hG.meas
    hF.sq hG.sq (-1)
  have hA := integrableOn_levyMixedIntegrand hU hG
  have hB := integrableOn_levyMixedIntegrand hF hχG
  have hFL := hF.memLp_real
  have hGL := hG.memLp_real
  have hUL := hU.memLp_real
  have hχGL := hχG.memLp_real
  unfold levyMixed
  rw [← integral_sub hA hB, ← e₁, ← e₂, ← integral_sub i₁ i₂]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hχb : ∀ᵐ u ∂volume, ‖χ u - χ (u + x)‖ ≤ 1 := Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs]
    exact (hχ.abs_sub_shift_le hx0 u).trans (min_le_right _ _)
  have hχm : AEStronglyMeasurable (fun u => χ u - χ (u + x)) volume :=
    (hχ.continuous.sub (hχ.continuous.comp (continuous_add_const x))).aestronglyMeasurable
  have iA : Integrable fun u =>
      (χ u * F u - χ (u + x) * F (u + x)) * (G u - G (u + x)) :=
    integrable_mul_of_memLp (hUL.sub (memLp_two_shift hUL x)) (hGL.sub (memLp_two_shift hGL x))
  have iB : Integrable fun u =>
      (F u - F (u + x)) * (χ u * G u - χ (u + x) * G (u + x)) :=
    integrable_mul_of_memLp (hFL.sub (memLp_two_shift hFL x)) (hχGL.sub (memLp_two_shift hχGL x))
  have iP := (integrable_mul_of_memLp (memLp_two_shift hFL x) hGL).bdd_mul hχm hχb
  have iQ := (integrable_mul_of_memLp hFL (memLp_two_shift hGL x)).bdd_mul hχm hχb
  have hAB : (∫ u, (χ u * F u - χ (u + x) * F (u + x)) * (G u - G (u + x))) -
      (∫ u, (F u - F (u + x)) * (χ u * G u - χ (u + x) * G (u + x))) =
      (∫ u, (χ u - χ (u + x)) * (F (u + x) * G u)) -
        ∫ u, (χ u - χ (u + x)) * (F u * G (u + x)) := by
    rw [← integral_sub iA iB, ← integral_sub iP iQ]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have hQ : (∫ u, (χ u - χ (u + x)) * (F u * G (u + x))) =
      ∫ u, (χ (u + -1 * x) - χ u) * (F (u + -1 * x) * G u) := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun u => (χ (u + -1 * x) - χ u) * (F (u + -1 * x) * G u)) x
    simp only [show ∀ u : ℝ, u + x + -1 * x = u from fun u => by ring] at h
    exact h
  have e1 : (∫ u, cutoffKernelRight χ x u * F (u + 1 * x) * G u) =
      archLevyDensity x * ∫ u, (χ u - χ (u + x)) * (F (u + x) * G u) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      simp only [cutoffKernelRight, one_mul]; ring)
  have e2 : (∫ u, cutoffKernelLeft χ x u * F (u + -1 * x) * G u) =
      archLevyDensity x * ∫ u, (χ (u + -1 * x) - χ u) * (F (u + -1 * x) * G u) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [cutoffKernelLeft]; ring)
  show archLevyDensity x *
      (∫ u, (χ u * F u - χ (u + x) * F (u + x)) * (G u - G (u + x))) -
    archLevyDensity x *
      (∫ u, (F u - F (u + x)) * (χ u * G u - χ (u + x) * G (u + x))) =
    (∫ u, cutoffKernelRight χ x u * F (u + 1 * x) * G u) -
      ∫ u, cutoffKernelLeft χ x u * F (u + -1 * x) * G u
  rw [e1, e2, ← hQ, ← mul_sub, ← mul_sub, hAB]

/-- The commutator of a cutoff against an essentially bounded profile is a bounded forcing. -/
theorem isBoundedForcingOn_commutator {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {C : ℝ} (hC : ∀ᵐ u, |F u| ≤ C) :
    IsBoundedForcingOn c d fun G =>
      levyMixed (fun u => χ u * F u) G - levyMixed F (fun u => χ u * G u) := by
  have hk₁ := isBoundedForcingOn_mass (c := c) (d := d)
    (stronglyMeasurable_kernel_translate (measurable_cutoffKernelRight hχ.continuous) hF.meas 1).aestronglyMeasurable
    (Eventually.of_forall fun u => abs_kernel_translate_le (integrableOn_cutoffKernelBound Λ)
      (abs_cutoffKernelRight_le hχ) hC (Or.inl rfl) u)
  have hk₂ := isBoundedForcingOn_mass (c := c) (d := d)
    (stronglyMeasurable_kernel_translate (measurable_cutoffKernelLeft hχ.continuous) hF.meas (-1)).aestronglyMeasurable
    (Eventually.of_forall fun u => abs_kernel_translate_le (integrableOn_cutoffKernelBound Λ)
      (abs_cutoffKernelLeft_le hχ) hC (Or.inr rfl) u)
  exact (hk₁.sub hk₂).congr fun G hG => (levyMixed_cutoff_commutator hχ hF hG.domain).symm

/-! ### The prime wave -/

/-- The prime wave `Σ_n Λ(n) n^{−½} (F(y + log n) + F(y − log n))` of a half-line profile. -/
def primeWave (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (F (y + Real.log n) + F (y - Real.log n))

theorem vonMangoldtAtom_nonneg' (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The backward weights `Λ(n) n^{−½} e^{−2 log n}` are summable. -/
theorem summable_vonMangoldtAtom_mul_exp :
    Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(2 * Real.log n)) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg' n) (Real.exp_pos _).le) (fun n => ?_)
    (summable_vonMangoldt_mul_rpow (by norm_num : (1 : ℝ) < 2))
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  unfold vonMangoldtAtom
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
    have he : Real.exp (-(2 * Real.log n)) = (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hn0]
      congr 1
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (div_le_self hΛ hsq) (Real.rpow_nonneg hn0.le _)
  · rw [zero_mul]
    exact mul_nonneg hΛ (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Almost everywhere, every backward prime term is bounded by `C e^{2y}` times a summable weight. -/
theorem ae_abs_primeTerm_le {F : ℝ → ℝ} {C : ℝ} (hb : ∀ᵐ u, |F u| ≤ C * Real.exp (2 * u)) :
    ∀ᵐ y : ℝ, ∀ n : ℕ, |vonMangoldtAtom n * F (y - Real.log n)| ≤
      C * Real.exp (2 * y) * (vonMangoldtAtom n * Real.exp (-(2 * Real.log n))) := by
  have hall : ∀ᵐ y : ℝ, ∀ n : ℕ, |F (y - Real.log n)| ≤ C * Real.exp (2 * (y - Real.log n)) :=
    ae_all_iff.mpr fun n =>
      (measurePreserving_sub_right (volume : Measure ℝ) (Real.log n)).quasiMeasurePreserving.ae hb
  filter_upwards [hall] with y hy n
  rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' n)]
  have he : C * Real.exp (2 * (y - Real.log n)) =
      C * Real.exp (2 * y) * Real.exp (-(2 * Real.log n)) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  calc vonMangoldtAtom n * |F (y - Real.log n)| ≤
        vonMangoldtAtom n * (C * Real.exp (2 * (y - Real.log n))) :=
        mul_le_mul_of_nonneg_left (hy n) (vonMangoldtAtom_nonneg' n)
    _ = _ := by rw [he]; ring

/-- The forward weights: `Λ(n) n^{−½}` for the `n < e^{−y}`, whose forward translate of `y` stays left
of the wall. -/
def forwardWeight (y : ℝ) (n : ℕ) : ℝ := if (n : ℝ) * Real.exp y < 1 then vonMangoldtAtom n else 0

theorem forwardWeight_nonneg (y : ℝ) (n : ℕ) : 0 ≤ forwardWeight y n := by
  unfold forwardWeight
  split_ifs
  · exact vonMangoldtAtom_nonneg' n
  · exact le_rfl

theorem summable_forwardWeight (y : ℝ) : Summable (forwardWeight y) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp (-y)⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  unfold forwardWeight
  rw [if_neg (not_lt.mpr ?_)]
  have h1 : Real.exp (-y) ≤ n := by
    have hc := Nat.le_ceil (Real.exp (-y))
    have hn' : (⌈Real.exp (-y)⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈Real.exp (-y)⌉₊ ≤ n)
    linarith
  calc (1 : ℝ) = Real.exp (-y) * Real.exp y := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    _ ≤ n * Real.exp y := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

theorem forwardWeight_anti {y z : ℝ} (hyz : y ≤ z) (n : ℕ) : forwardWeight z n ≤ forwardWeight y n := by
  unfold forwardWeight
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hyz)
      (Nat.cast_nonneg n)) h1) h2
  · exact vonMangoldtAtom_nonneg' n
  · exact le_rfl

/-- A forward prime translate reaching the wall vanishes. -/
theorem forward_eq_zero {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) {y : ℝ} {n : ℕ}
    (hn : ¬(n : ℝ) * Real.exp y < 1) : F (y + Real.log n) = 0 := by
  apply hsupp
  rw [not_lt] at hn
  have hn0 : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg (α := ℝ) n).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hn
      linarith
  have h := Real.log_nonneg hn
  rw [Real.log_mul hn0.ne' (Real.exp_pos y).ne', Real.log_exp] at h
  linarith

/-- Almost everywhere, each term of the prime wave is bounded by a summable weight. -/
theorem ae_abs_primeWaveTerm_le {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) {C : ℝ}
    (hbexp : ∀ᵐ u, |F u| ≤ C * Real.exp (2 * u)) (hb : ∀ᵐ u, |F u| ≤ C) :
    ∀ᵐ y : ℝ, ∀ n : ℕ, |vonMangoldtAtom n * (F (y + Real.log n) + F (y - Real.log n))| ≤
      C * forwardWeight y n +
        C * Real.exp (2 * y) * (vonMangoldtAtom n * Real.exp (-(2 * Real.log n))) := by
  have hfw : ∀ᵐ y : ℝ, ∀ n : ℕ, |F (y + Real.log n)| ≤ C :=
    ae_all_iff.mpr fun n =>
      (measurePreserving_add_right (volume : Measure ℝ) (Real.log n)).quasiMeasurePreserving.ae hb
  filter_upwards [hfw, ae_abs_primeTerm_le hbexp] with y h1 h2 n
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ (h2 n))
  rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' n)]
  unfold forwardWeight
  split_ifs with h
  · rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (h1 n) (vonMangoldtAtom_nonneg' n)
  · rw [forward_eq_zero hsupp h, abs_zero, mul_zero, mul_zero]

theorem summable_primeWaveBound (C y : ℝ) : Summable fun n : ℕ =>
    C * forwardWeight y n +
      C * Real.exp (2 * y) * (vonMangoldtAtom n * Real.exp (-(2 * Real.log n))) :=
  ((summable_forwardWeight y).mul_left C).add (summable_vonMangoldtAtom_mul_exp.mul_left _)

theorem aestronglyMeasurable_primeWave {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {C : ℝ} (hbexp : ∀ᵐ u, |F u| ≤ C * Real.exp (2 * u))
    (hb : ∀ᵐ u, |F u| ≤ C) : AEStronglyMeasurable (primeWave F) volume := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N y => ∑ n ∈ Finset.range N,
      vonMangoldtAtom n * (F (y + Real.log n) + F (y - Real.log n)))
    (fun N => (Finset.measurable_sum _ fun n _ => measurable_const.mul
      ((hFm.comp (measurable_id.add_const _)).add
        (hFm.comp (measurable_id.sub_const _)))).aestronglyMeasurable) ?_
  filter_upwards [ae_abs_primeWaveTerm_le hsupp hbexp hb] with y hy
  exact (Summable.of_norm_bounded (summable_primeWaveBound C y)
    fun n => by rw [Real.norm_eq_abs]; exact hy n).hasSum.tendsto_sum_nat

/-- On a window of the half-line the prime wave is bounded. -/
theorem ae_abs_primeWave_le {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hbexp : ∀ᵐ u, |F u| ≤ C * Real.exp (2 * u)) (hb : ∀ᵐ u, |F u| ≤ C) {c d : ℝ} (hd : d ≤ 0) :
    ∀ᵐ y, y ∈ Icc c d → |primeWave F y| ≤ C * (∑' n : ℕ, forwardWeight c n) +
      C * ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(2 * Real.log n)) := by
  filter_upwards [ae_abs_primeWaveTerm_le hsupp hbexp hb] with y hy hm
  have h1 := tsum_of_norm_bounded (summable_primeWaveBound C y).hasSum
    fun n => by rw [Real.norm_eq_abs]; exact hy n
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [((summable_forwardWeight y).mul_left C).tsum_add
    (summable_vonMangoldtAtom_mul_exp.mul_left _), tsum_mul_left, tsum_mul_left]
  have he : Real.exp (2 * y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hm.2])
  have hfw : ∑' n : ℕ, forwardWeight y n ≤ ∑' n : ℕ, forwardWeight c n :=
    Summable.tsum_le_tsum (fun n => forwardWeight_anti hm.1 n) (summable_forwardWeight y)
      (summable_forwardWeight c)
  have hS0 : 0 ≤ ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(2 * Real.log n)) :=
    tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg' n) (Real.exp_pos _).le
  have h2 := mul_le_mul_of_nonneg_left hfw hC0
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hS0) hC0
  linarith

/-- A prime pair term is the integral of the test against the two prime translates. -/
theorem primePairTerm_eq_wave {F G : ℝ → ℝ} (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (n : ℕ) : primePairTerm F G n =
      vonMangoldtAtom n * ∫ y, G y * (F (y + Real.log n) + F (y - Real.log n)) := by
  unfold primePairTerm
  have e1 : (∫ t, F t * G (t - Real.log n)) = ∫ y, F (y + Real.log n) * G y := by
    have h := integral_add_right_eq_self (μ := volume) (fun t => F t * G (t - Real.log n))
      (Real.log n)
    simp only [add_sub_cancel_right] at h
    exact h.symm
  have e2 : (∫ t, F t * G (t + Real.log n)) = ∫ y, F (y - Real.log n) * G y := by
    have h := integral_sub_right_eq_self (μ := volume) (fun t => F t * G (t + Real.log n))
      (Real.log n)
    simp only [sub_add_cancel] at h
    exact h.symm
  have i1 : Integrable fun y => F (y + Real.log n) * G y :=
    integrable_mul_of_memLp (memLp_two_shift hF (Real.log n)) hG
  have i2 : Integrable fun y => F (y - Real.log n) * G y :=
    integrable_mul_of_memLp
      (hF.comp_measurePreserving (measurePreserving_sub_right volume (Real.log n))) hG
  rw [e1, e2, ← integral_add i1 i2]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- The transposed prime pair term is the same integral. -/
theorem primePairTerm_swap_eq_wave {F G : ℝ → ℝ} (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (n : ℕ) : primePairTerm G F n =
      vonMangoldtAtom n * ∫ y, G y * (F (y + Real.log n) + F (y - Real.log n)) := by
  unfold primePairTerm
  have i1 : Integrable fun y => G y * F (y - Real.log n) :=
    integrable_mul_of_memLp hG
      (hF.comp_measurePreserving (measurePreserving_sub_right volume (Real.log n)))
  have i2 : Integrable fun y => G y * F (y + Real.log n) :=
    integrable_mul_of_memLp hG (memLp_two_shift hF (Real.log n))
  rw [← integral_add i1 i2]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- **The prime pairing of a test is integration against the prime wave.** -/
theorem tsum_primePairing_eq_primeWave {F : ℝ → ℝ} (hFm : Measurable F)
    (hF2 : Integrable fun u => F u ^ 2) (hsupp : ∀ u, 0 ≤ u → F u = 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hbexp : ∀ᵐ u, |F u| ≤ C * Real.exp (2 * u)) (hb : ∀ᵐ u, |F u| ≤ C) {c d : ℝ} (hd : d ≤ 0)
    {G : ℝ → ℝ} (hG : IsCarriedTest c d G) :
    (∑' n : ℕ, vonMangoldtAtom n * ∫ y, G y * (F (y + Real.log n) + F (y - Real.log n))) =
      ∫ y, G y * primeWave F y := by
  have hFL : MemLp F 2 volume := (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).mpr hF2
  have hGL := hG.domain.memLp_real
  have hint : ∀ n : ℕ, Integrable fun y =>
      G y * (vonMangoldtAtom n * (F (y + Real.log n) + F (y - Real.log n))) := fun n => by
    have h1 := integrable_mul_of_memLp hGL (memLp_two_shift hFL (Real.log n))
    have h2 := integrable_mul_of_memLp hGL
      (hFL.comp_measurePreserving (measurePreserving_sub_right volume (Real.log n)))
    refine ((h1.add h2).const_mul (vonMangoldtAtom n)).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, Function.comp_apply]
    ring
  have hbound : ∀ n : ℕ, (∫ y, ‖G y * (vonMangoldtAtom n *
      (F (y + Real.log n) + F (y - Real.log n)))‖) ≤
        (C * forwardWeight c n + C * (vonMangoldtAtom n * Real.exp (-(2 * Real.log n)))) *
          ∫ y, ‖G y‖ := fun n => by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
      (hG.domain.integrable.norm.const_mul _) ?_
    filter_upwards [ae_abs_primeWaveTerm_le hsupp hbexp hb] with y hy
    by_cases hm : y ∈ Icc c d
    · have he : Real.exp (2 * y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hm.2])
      have hs := mul_nonneg (vonMangoldtAtom_nonneg' n) (Real.exp_pos (-(2 * Real.log n))).le
      have h2 := mul_le_mul_of_nonneg_left (forwardWeight_anti hm.1 n) hC0
      have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hs) hC0
      have hw : |vonMangoldtAtom n * (F (y + Real.log n) + F (y - Real.log n))| ≤
          C * forwardWeight c n + C * (vonMangoldtAtom n * Real.exp (-(2 * Real.log n))) := by
        have := hy n
        nlinarith
      rw [norm_mul, Real.norm_eq_abs (vonMangoldtAtom n * _), mul_comm]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    · rw [hG.vanish y hm, norm_zero, zero_mul, norm_zero, mul_zero]
  have hw : Summable fun n : ℕ =>
      C * forwardWeight c n + C * (vonMangoldtAtom n * Real.exp (-(2 * Real.log n))) :=
    ((summable_forwardWeight c).mul_left C).add (summable_vonMangoldtAtom_mul_exp.mul_left C)
  have hsum : Summable fun n : ℕ => ∫ y, ‖G y * (vonMangoldtAtom n *
      (F (y + Real.log n) + F (y - Real.log n)))‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hbound
      (hw.mul_right _)
  calc (∑' n : ℕ, vonMangoldtAtom n * ∫ y, G y * (F (y + Real.log n) + F (y - Real.log n)))
      = ∑' n : ℕ, ∫ y, G y * (vonMangoldtAtom n *
          (F (y + Real.log n) + F (y - Real.log n))) := by
        congr 1
        funext n
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    _ = ∫ y, ∑' n : ℕ, G y * (vonMangoldtAtom n *
          (F (y + Real.log n) + F (y - Real.log n))) :=
        integral_tsum_of_summable_integral_norm hint hsum
    _ = ∫ y, G y * primeWave F y := by
        unfold primeWave
        exact integral_congr_ae (Eventually.of_forall fun y => tsum_mul_left)

/-- **The window equation.** Against a test of a window of the half-line, the Gamma form of the
state is its prime wave minus the pole and confinement pairings. -/
theorem criticalState_window_equation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c d : ℝ} (hd : d ≤ 0) {G : ℝ → ℝ}
    (hG : IsCarriedTest c d G) :
    gammaMixedForm F G = (∫ y, G y * primeWave F y) -
      (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) -
        criticalAliasCoefficient W₀ * ∫ u in Iio 0, F u * G u * Real.exp (-(8 * u)) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC0, hbexp, hb⟩ := criticalState_ae_abs_le hW ht hF
  have hweak := criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG.domain
  unfold criticalHalfLineMixedEnergy primeMixedForm at hweak
  simp_rw [primePairTerm_eq_wave hdF.memLp_real hG.domain.memLp_real,
    primePairTerm_swap_eq_wave hdF.memLp_real hG.domain.memLp_real] at hweak
  rw [tsum_primePairing_eq_primeWave hdF.meas hdF.sq hF.2.2.2.2.2.1 hC0 hbexp hb hd hG] at hweak
  linarith

/-- The prime pairing of `χG` is a bounded forcing. -/
theorem isBoundedForcingOn_primeWave {c d Λ : ℝ} (hd : d ≤ 0) {χ : ℝ → ℝ}
    (hχ : IsWindowCutoff c d Λ χ) {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hbexp : ∀ᵐ u, |F u| ≤ C * Real.exp (2 * u)) (hb : ∀ᵐ u, |F u| ≤ C) :
    IsBoundedForcingOn c d fun G => ∫ y, (χ y * G y) * primeWave F y := by
  refine ⟨fun y => χ y * primeWave F y, hχ.continuous.aestronglyMeasurable.mul
    (aestronglyMeasurable_primeWave hFm hsupp hbexp hb), ⟨C * (∑' n : ℕ, forwardWeight c n) +
      C * ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(2 * Real.log n)), ?_⟩, fun G _ =>
    integral_congr_ae (Eventually.of_forall fun y => by ring)⟩
  filter_upwards [ae_abs_primeWave_le hsupp hC0 hbexp hb hd] with y hy hm
  rw [abs_mul]
  calc |χ y| * |primeWave F y| ≤ 1 * |primeWave F y| :=
        mul_le_mul_of_nonneg_right (hχ.abs_le_one y) (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hy hm

/-! ### The pole and the confinement -/

/-- The pole pairing of `χG` is a bounded forcing. -/
theorem isBoundedForcingOn_pole {c d : ℝ} {χ : ℝ → ℝ} (hχ : Continuous χ) (F : ℝ → ℝ) :
    IsBoundedForcingOn c d fun G =>
      2 * coshHalfMoment F * coshHalfMoment (fun u => χ u * G u) -
        2 * sinhHalfMoment F * sinhHalfMoment (fun u => χ u * G u) := by
  have hc : Continuous fun y : ℝ => χ y * Real.cosh (y / 2) :=
    hχ.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hs : Continuous fun y : ℝ => χ y * Real.sinh (y / 2) :=
    hχ.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  refine (((isBoundedForcingOn_continuous hc).const_mul (2 * coshHalfMoment F)).sub
    ((isBoundedForcingOn_continuous hs).const_mul (2 * sinhHalfMoment F))).congr fun G _ => ?_
  have e1 : coshHalfMoment (fun u => χ u * G u) = ∫ y, G y * (χ y * Real.cosh (y / 2)) := by
    unfold coshHalfMoment
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have e2 : sinhHalfMoment (fun u => χ u * G u) = ∫ y, G y * (χ y * Real.sinh (y / 2)) := by
    unfold sinhHalfMoment
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [e1, e2]

/-- The confinement pairing of `χG` against an essentially bounded profile is a bounded forcing. -/
theorem isBoundedForcingOn_confinement {c d Λ : ℝ} {χ : ℝ → ℝ} (hχ : IsWindowCutoff c d Λ χ)
    {F : ℝ → ℝ} (hFm : Measurable F) {C : ℝ} (hC : ∀ᵐ u, |F u| ≤ C) :
    IsBoundedForcingOn c d fun G =>
      ∫ u in Iio 0, F u * (χ u * G u) * Real.exp (-(8 * u)) := by
  refine ⟨(Iio 0).indicator fun u => χ u * F u * Real.exp (-(8 * u)),
    (((hχ.continuous.measurable.mul hFm).mul (by fun_prop)).indicator
      measurableSet_Iio).aestronglyMeasurable, ⟨C * Real.exp (-(8 * c)), ?_⟩, fun G _ => ?_⟩
  · filter_upwards [hC] with u hu hmem
    have hC0 : 0 ≤ C := (abs_nonneg _).trans hu
    by_cases hneg : u ∈ Iio (0 : ℝ)
    · rw [indicator_of_mem hneg, abs_mul, abs_mul, abs_of_nonneg (hχ.nonneg u),
        abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(8 * u)) ≤ Real.exp (-(8 * c)) :=
        Real.exp_le_exp.mpr (by linarith [hmem.1])
      calc χ u * |F u| * Real.exp (-(8 * u)) ≤ 1 * C * Real.exp (-(8 * c)) := by
            gcongr
            exact hχ.le_one u
        _ = C * Real.exp (-(8 * c)) := by ring
    · rw [indicator_of_notMem hneg, abs_zero]
      positivity
  · show (∫ u in Iio 0, F u * (χ u * G u) * Real.exp (-(8 * u))) =
      ∫ y, G y * (Iio 0).indicator (fun u => χ u * F u * Real.exp (-(8 * u))) y
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases h : u ∈ Iio (0 : ℝ)
    · simp only [indicator_of_mem h]
      ring
    · simp only [indicator_of_notMem h, mul_zero]

/-! ### The logarithmic equation on a window -/

open CanonicalSystemOfTheWindowTower in
/-- **The state solves a logarithmic equation on every window of the half-line.** For a cutoff `χ`
of a window `[c, d]`, `d ≤ 0`, and `U = χF`, the logarithmic full form
`G ↦ ∫ U G + ∫_{x>0} ν(x) ∫ ΔₓU ΔₓG` is a bounded forcing on the window. -/
theorem criticalState_logarithmic_equation_on_window {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c d Λ : ℝ} (hd : d ≤ 0) {χ : ℝ → ℝ}
    (hχ : IsWindowCutoff c d Λ χ) :
    IsBoundedForcingOn c d fun G => (∫ u, χ u * F u * G u) +
      ∫ x in Ioi 0, logReferenceLevyDensity x *
        ∫ u, (χ u * F u - χ (u + x) * F (u + x)) * (G u - G (u + x)) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC0, hbexp, hb⟩ := criticalState_ae_abs_le hW ht hF
  have hU : CriticalHalfLineEnergyDomain fun u => χ u * F u :=
    criticalHalfLineEnergyDomain_lipschitz_mul hdF hχ.continuous.measurable hχ.abs_le_one
      hχ.lipschitz
  have hUb : ∀ᵐ u, |χ u * F u| ≤ C := hb.mono fun u hu => by
    rw [abs_mul]
    calc |χ u| * |F u| ≤ 1 * C := mul_le_mul (hχ.abs_le_one u) hu (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hM := isBoundedForcingOn_mass (c := c) (d := d) hU.meas.aestronglyMeasurable hUb
  have hR := isBoundedForcingOn_remainderJump (c := c) (d := d) hU hUb
  have hK := isBoundedForcingOn_commutator hχ hdF hb
  have hP := isBoundedForcingOn_primeWave hd hχ hdF.meas hF.2.2.2.2.2.1 hC0 hbexp hb
  have hPo := isBoundedForcingOn_pole (c := c) (d := d) hχ.continuous F
  have hCf := isBoundedForcingOn_confinement hχ hdF.meas hb
  refine ((((((hM.sub hR).add hK).add hP).sub hPo).sub
    (hCf.const_mul (criticalAliasCoefficient W₀))).sub
      (hM.const_mul (2 * gammaHardyPhaseRate 0))).congr fun G hG => ?_
  have hχG := hG.cutoff hχ
  have hlevy := gammaMixedForm_eq_levy hdF hχG.domain
  have hwall := criticalState_window_equation hW ht hF hd hχG
  have hsplit : (∫ x in Ioi 0, logReferenceLevyDensity x *
        ∫ u, (χ u * F u - χ (u + x) * F (u + x)) * (G u - G (u + x))) =
      levyMixed (fun u => χ u * F u) G - ∫ x in Ioi 0, archLogRemainder x *
        ∫ u, (χ u * F u - χ (u + x) * F (u + x)) * (G u - G (u + x)) := by
    unfold levyMixed
    rw [← integral_sub (integrableOn_levyMixedIntegrand hU hG.domain)
      (integrableOn_remainderJump hU hG.domain)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [archLogRemainder]
    ring
  have hmass : (∫ u, F u * (χ u * G u)) = ∫ u, χ u * F u * G u :=
    integral_congr_ae (Eventually.of_forall fun u => by ring)
  rw [hmass] at hlevy
  rw [hsplit]
  linarith

#print axioms criticalState_logarithmic_equation_on_window

end GaloisForLFunctions.ExclusionOfTheCriticalState
