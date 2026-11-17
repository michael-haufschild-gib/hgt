import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers
import GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarIsCoerciveAndPrimeBlind
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilSymbolIsALogarithmicMultiplierPlusABoundedKernel
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers

/-!
# The state solves a logarithmic equation at the wall

Write \`ω\` for the Lévy density of the Gamma form, \`ν(x) = e^{−x}/(2x)\` for the Lévy density of the
logarithmic multiplier \`½ log(1 + ξ²)\`, and \`r = ω − ν\`, a bounded integrable kernel. Let \`χ\` be the
ramp equal to \`0\` left of \`−½\` and to \`1\` right of \`−¼\` (\`wallRamp\`), and \`U = χF\` the state cut off
near the wall. Wall tests are profiles of the energy domain carried by the collar \`[−½, 0]\`.

**Theorem** (\`criticalState_logarithmic_equation_at_wall\`). There is a function \`g\`, bounded on the
collar, such that for every wall test \`G\`

  \`∫ U G + ∫_{x>0} ν(x) ∫ (U(u) − U(u+x)) (G(u) − G(u+x)) du dx = ∫ G g\`.

The left side is the logarithmic full form of \`(U, G)\`: \`U\` solves the logarithmic equation on the
collar with a bounded forcing.

Mechanism. The jump form of \`ν\` is the Gamma jump form minus the jump form of \`r\`, and the latter
is a mass term minus two convolutions with \`r\` (\`isBoundedWallForcing_remainderJump\`). Moving \`χ\`
from \`F\` to the test costs the commutator
\`∫_{x>0} ω(x) ∫ (χ(u) − χ(u+x)) (F(u+x) G(u) − F(u) G(u+x))\`, a convolution with a kernel bounded
by \`ω(x) min(4x, 1) ≤ 14 e^{−x/2}\` (\`isBoundedWallForcing_commutator\`). Against the test \`χG\`, which
lies on the collar, the weak equation is the collar equation: no forward prime translate enters,
and the Gamma form equals the backward prime wave minus the pole and confinement terms
(\`criticalState_wall_equation\`). Every term integrates \`G\` against a function bounded on the
collar: the state is essentially bounded, \`|F(u)| ≤ C e^{2u}\`, so the backward prime wave
\`Σ Λ(n) n^{−½} F(u − log n)\` converges absolutely and is bounded there.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Moving a kernel onto the test -/

/-- **A kernel bounded by an integrable function of the lag moves onto the test.** If
\`|φ(x, u)| ≤ m(x)\` for \`x > 0\` with \`m\` integrable on \`(0, ∞)\`, and \`F, G\` are square integrable, then
\`x ↦ ∫ φ(x,u) F(u + σx) G(u) du\` is integrable on \`(0, ∞)\` and
\`∫_{x>0} ∫ φ(x,u) F(u + σx) G(u) du dx = ∫ (∫_{x>0} φ(x,u) F(u + σx) dx) G(u) du\`. -/
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

/-- The kernel integral \`u ↦ ∫_{x>0} φ(x,u) F(u + σx) dx\` is strongly measurable. -/
theorem stronglyMeasurable_kernel_translate {φ : ℝ → ℝ → ℝ}
    (hφ : Measurable (Function.uncurry φ)) {F : ℝ → ℝ} (hFm : Measurable F) (σ : ℝ) :
    StronglyMeasurable fun u => ∫ x in Ioi 0, φ x u * F (u + σ * x) := by
  have h : Measurable fun p : ℝ × ℝ => φ p.2 p.1 * F (p.1 + σ * p.2) :=
    (hφ.comp measurable_swap).mul (hFm.comp (measurable_fst.add (measurable_snd.const_mul σ)))
  exact h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

/-- A kernel integral of an essentially bounded profile is bounded: \`|∫ φ F(u ± x)| ≤ C ∫ m\`. -/
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

/-! ### The wall ramp -/

/-- The wall ramp: \`0\` left of \`−½\`, \`1\` right of \`−¼\`, linear in between. -/
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
  rw [show 4 * u + 2 - (4 * v + 2) = 4 * (u - v) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]

/-- A jump of the ramp over a lag \`x > 0\` is at most \`min(4x, 1)\`. -/
theorem abs_wallRamp_sub_shift_le {x : ℝ} (hx : 0 < x) (u : ℝ) :
    |wallRamp u - wallRamp (u + x)| ≤ min (4 * x) 1 := by
  refine le_min ?_ ?_
  · have h := abs_wallRamp_sub_le u (u + x)
    rwa [show u - (u + x) = -x by ring, abs_neg, abs_of_pos hx] at h
  · rw [abs_le]
    constructor <;> linarith [wallRamp_nonneg u, wallRamp_le_one u, wallRamp_nonneg (u + x),
      wallRamp_le_one (u + x)]

/-- \`ω(x) min(4x, 1) ≤ 14 e^{−x/2}\`: the commutator kernel of the ramp is integrable. -/
theorem archLevyDensity_mul_min_le {x : ℝ} (hx : 0 < x) :
    archLevyDensity x * min (4 * x) 1 ≤ 14 * Real.exp (-(x / 2)) := by
  have hω := (archLevyDensity_pos hx).le
  rcases le_total x 1 with h1 | h1
  · have h2 := archLevyDensity_le_near hx h1
    have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(x / 2)) := by
      have := Real.add_one_le_exp (-(x / 2))
      linarith
    calc archLevyDensity x * min (4 * x) 1 ≤ 3 / (2 * x) * (4 * x) :=
          mul_le_mul h2 (min_le_left _ _) (le_min (by positivity) zero_le_one) (by positivity)
      _ = 6 := by field_simp; ring
      _ ≤ 14 * Real.exp (-(x / 2)) := by linarith
  · have h2 := archLevyDensity_le_far h1
    calc archLevyDensity x * min (4 * x) 1 ≤ 2 * Real.exp (-(x / 2)) * 1 :=
          mul_le_mul h2 (min_le_right _ _) (le_min (by positivity) zero_le_one) (by positivity)
      _ ≤ 14 * Real.exp (-(x / 2)) := by nlinarith [Real.exp_pos (-(x / 2))]

/-! ### Wall tests and the wall equation -/

/-- A **wall test** is a profile of the energy domain carried by the collar \`[−½, 0]\`. -/
structure IsWallTest (G : ℝ → ℝ) : Prop where
  domain : CriticalHalfLineEnergyDomain G
  vanish : ∀ x, x ∉ Icc (-(1 / 2 : ℝ)) 0 → G x = 0

theorem one_half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

/-- The ramp keeps wall tests: \`χG\` is a wall test. -/
theorem IsWallTest.ramp {G : ℝ → ℝ} (hG : IsWallTest G) :
    IsWallTest fun u => wallRamp u * G u :=
  ⟨criticalHalfLineEnergyDomain_lipschitz_mul hG.domain measurable_wallRamp abs_wallRamp_le_one
    abs_wallRamp_sub_le, fun x hx => by rw [hG.vanish x hx, mul_zero]⟩

/-- A wall test meets a half-line profile only through backward prime translates. -/
theorem primePairTerm_wall_left {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0)
    (hG : ∀ x, x ∉ Icc (-(1 / 2 : ℝ)) 0 → G x = 0) (n : ℕ) :
    primePairTerm F G n = vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primePairTerm
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hn, zero_mul, zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h12 := one_half_lt_log_two
    have h0 : (fun t => F t * G (t - Real.log n)) = fun _ => 0 := by
      funext t
      by_cases ht : 0 ≤ t
      · rw [hF t ht, zero_mul]
      · rw [hG (t - Real.log n) fun hm => by linarith [hm.1], mul_zero]
    rw [h0, integral_zero, zero_add]

/-- The transposed prime term of a wall test is the same backward translate. -/
theorem primePairTerm_wall_right {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0)
    (hG : ∀ x, x ∉ Icc (-(1 / 2 : ℝ)) 0 → G x = 0) (n : ℕ) :
    primePairTerm G F n = vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primePairTerm
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hn, zero_mul, zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h12 := one_half_lt_log_two
    have h0 : (fun t => G t * F (t + Real.log n)) = fun _ => 0 := by
      funext t
      by_cases ht : t ∈ Icc (-(1 / 2 : ℝ)) 0
      · rw [hF (t + Real.log n) (by linarith [ht.1]), mul_zero]
      · rw [hG t ht, zero_mul]
    have hs : (∫ t, G t * F (t - Real.log n)) = ∫ t, F t * G (t + Real.log n) := by
      have h := integral_add_right_eq_self (μ := volume)
        (fun t => G t * F (t - Real.log n)) (Real.log n)
      simp only [add_sub_cancel_right] at h
      rw [← h]
      exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
    rw [h0, integral_zero, add_zero, hs]

/-- **The wall equation.** Against a wall test the Gamma form of the state is its backward prime
wave minus the pole and confinement pairings. -/
theorem criticalState_wall_equation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ} (hG : IsWallTest G) :
    gammaMixedForm F G = (∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n)) -
      (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) -
        criticalAliasCoefficient W₀ * ∫ u in Iio 0, F u * G u * Real.exp (-(8 * u)) := by
  have hweak := criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG.domain
  unfold criticalHalfLineMixedEnergy primeMixedForm at hweak
  simp_rw [primePairTerm_wall_left hF.2.2.2.2.2.1 hG.vanish,
    primePairTerm_wall_right hF.2.2.2.2.2.1 hG.vanish] at hweak
  linarith

/-! ### Bounded wall forcings -/

/-- A functional on wall tests is a **bounded wall forcing** when it integrates the test against a
function bounded on the collar. -/
def IsBoundedWallForcing (Λ : (ℝ → ℝ) → ℝ) : Prop :=
  ∃ h : ℝ → ℝ, AEStronglyMeasurable h volume ∧
    (∃ C, ∀ᵐ y, y ∈ Icc (-(1 / 2 : ℝ)) 0 → |h y| ≤ C) ∧ ∀ G, IsWallTest G → Λ G = ∫ y, G y * h y

theorem IsWallTest.integrable_mul {G h : ℝ → ℝ} (hG : IsWallTest G)
    (hh : AEStronglyMeasurable h volume) {C : ℝ}
    (hC : ∀ᵐ y, y ∈ Icc (-(1 / 2 : ℝ)) 0 → |h y| ≤ C) : Integrable fun y => G y * h y := by
  refine (hG.domain.integrable.norm.const_mul C).mono'
    (hG.domain.meas.aestronglyMeasurable.mul hh) ?_
  filter_upwards [hC] with y hy
  by_cases hm : y ∈ Icc (-(1 / 2 : ℝ)) 0
  · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hy hm) (abs_nonneg _)
  · simp only [hG.vanish y hm, zero_mul, norm_zero, mul_zero, le_refl]

theorem IsBoundedWallForcing.congr {Λ₁ Λ₂ : (ℝ → ℝ) → ℝ} (h : IsBoundedWallForcing Λ₁)
    (he : ∀ G, IsWallTest G → Λ₁ G = Λ₂ G) : IsBoundedWallForcing Λ₂ := by
  obtain ⟨g, hm, hC, hg⟩ := h
  exact ⟨g, hm, hC, fun G hG => (he G hG).symm.trans (hg G hG)⟩

theorem IsBoundedWallForcing.add {Λ₁ Λ₂ : (ℝ → ℝ) → ℝ} (h₁ : IsBoundedWallForcing Λ₁)
    (h₂ : IsBoundedWallForcing Λ₂) : IsBoundedWallForcing fun G => Λ₁ G + Λ₂ G := by
  obtain ⟨g₁, hm₁, ⟨C₁, hC₁⟩, he₁⟩ := h₁
  obtain ⟨g₂, hm₂, ⟨C₂, hC₂⟩, he₂⟩ := h₂
  refine ⟨fun y => g₁ y + g₂ y, hm₁.add hm₂, ⟨C₁ + C₂, ?_⟩, fun G hG => ?_⟩
  · filter_upwards [hC₁, hC₂] with y h1 h2 hy
    exact (abs_add_le _ _).trans (add_le_add (h1 hy) (h2 hy))
  · show Λ₁ G + Λ₂ G = ∫ y, G y * (g₁ y + g₂ y)
    rw [he₁ G hG, he₂ G hG,
      ← integral_add (hG.integrable_mul hm₁ hC₁) (hG.integrable_mul hm₂ hC₂)]
    exact integral_congr_ae (Eventually.of_forall fun y => (mul_add _ _ _).symm)

theorem IsBoundedWallForcing.const_mul {Λ : (ℝ → ℝ) → ℝ} (h : IsBoundedWallForcing Λ) (c : ℝ) :
    IsBoundedWallForcing fun G => c * Λ G := by
  obtain ⟨g, hm, ⟨C, hC⟩, he⟩ := h
  refine ⟨fun y => c * g y, hm.const_mul c, ⟨|c| * C, ?_⟩, fun G hG => ?_⟩
  · filter_upwards [hC] with y h1 hy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h1 hy) (abs_nonneg c)
  · show c * Λ G = ∫ y, G y * (c * g y)
    rw [he G hG, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)

theorem IsBoundedWallForcing.sub {Λ₁ Λ₂ : (ℝ → ℝ) → ℝ} (h₁ : IsBoundedWallForcing Λ₁)
    (h₂ : IsBoundedWallForcing Λ₂) : IsBoundedWallForcing fun G => Λ₁ G - Λ₂ G :=
  (h₁.add (h₂.const_mul (-1))).congr fun G _ => by ring

/-- Integration against an essentially bounded function is a bounded wall forcing. -/
theorem isBoundedWallForcing_mass {V : ℝ → ℝ} (hV : AEStronglyMeasurable V volume) {C : ℝ}
    (hC : ∀ᵐ u, |V u| ≤ C) : IsBoundedWallForcing fun G => ∫ u, V u * G u :=
  ⟨V, hV, ⟨C, hC.mono fun _ h _ => h⟩, fun _ _ =>
    integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)⟩

/-- Integration against a continuous function is a bounded wall forcing (the collar is compact). -/
theorem isBoundedWallForcing_continuous {k : ℝ → ℝ} (hk : Continuous k) :
    IsBoundedWallForcing fun G => ∫ y, G y * k y := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 0)).exists_bound_of_continuousOn'
    hk.continuousOn
  exact ⟨k, hk.aestronglyMeasurable,
    ⟨C, Eventually.of_forall fun y hy => by simpa only [Real.norm_eq_abs] using hC y hy⟩,
    fun _ _ => rfl⟩

/-- The state is essentially bounded, with \`|F(u)| ≤ C e^{2u}\`. -/
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

/-! ### The remainder kernel \`r = ω − ν\` -/

open CanonicalSystemOfTheWindowTower in
/-- The jump integrand of the remainder kernel is integrable: \`0 ≤ r ≤ ω\`. -/
theorem integrableOn_remainderJump {U G : ℝ → ℝ} (hU : CriticalHalfLineEnergyDomain U)
    (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (fun x => archLogRemainder x * ∫ u, (U u - U (u + x)) * (G u - G (u + x)))
      (Ioi 0) := by
  have h := (integrableOn_levyMixedIntegrand hU hG).bdd_mul (c := 1)
    (f := fun x => archLogRemainder x / archLevyDensity x)
    ((measurable_archLogRemainder.div measurable_archLevyDensity).aestronglyMeasurable) ?_
  · refine IntegrableOn.congr_fun (show IntegrableOn _ (Ioi 0) from h) (fun x hx => ?_)
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

/-- Expansion of a jump pairing: \`∫ ΔU ΔG = 2 ∫ UG − ∫ U(u − x) G(u) − ∫ U(u + x) G(u)\`. -/
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
/-- **The remainder jump form is a mass term minus two convolutions with \`r\`.** -/
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
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hc.sub iM) iP,
    integral_sub hc iM, integral_const_mul]
  simp only at eM eP
  rw [eM, eP]
  ring

open CanonicalSystemOfTheWindowTower in
/-- The remainder jump form against an essentially bounded profile is a bounded wall forcing. -/
theorem isBoundedWallForcing_remainderJump {U : ℝ → ℝ} (hU : CriticalHalfLineEnergyDomain U)
    {C : ℝ} (hC : ∀ᵐ u, |U u| ≤ C) :
    IsBoundedWallForcing fun G =>
      ∫ x in Ioi 0, archLogRemainder x * ∫ u, (U u - U (u + x)) * (G u - G (u + x)) := by
  have hφ : Measurable (Function.uncurry fun x (_ : ℝ) => archLogRemainder x) :=
    measurable_archLogRemainder.comp measurable_fst
  have hb : ∀ x ∈ Ioi (0 : ℝ), ∀ u : ℝ,
      |(fun x (_ : ℝ) => archLogRemainder x) x u| ≤ archLogRemainder x := fun x hx _ =>
    (abs_of_nonneg (archLogRemainder_nonneg hx)).le
  have hk : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → IsBoundedWallForcing fun G =>
      ∫ u, (∫ x in Ioi 0, archLogRemainder x * U (u + σ * x)) * G u := fun σ hσ =>
    isBoundedWallForcing_mass
      (stronglyMeasurable_kernel_translate hφ hU.meas σ).aestronglyMeasurable
      (Eventually.of_forall fun u =>
        abs_kernel_translate_le integrableOn_archLogRemainder hb hC hσ u)
  refine ((((isBoundedWallForcing_mass hU.meas.aestronglyMeasurable hC).const_mul
    (2 * ∫ x in Ioi 0, archLogRemainder x)).sub (hk (-1) (Or.inr rfl))).sub
      (hk 1 (Or.inl rfl))).congr fun G hG => ?_
  rw [remainderJump_eq hU.meas hG.domain.meas hU.sq hG.domain.sq]
  ring

/-! ### The commutator of the ramp -/

/-- The kernel of the commutator on forward translates. -/
def rampKernelRight (x u : ℝ) : ℝ := archLevyDensity x * (wallRamp u - wallRamp (u + x))

/-- The kernel of the commutator on backward translates. -/
def rampKernelLeft (x u : ℝ) : ℝ := archLevyDensity x * (wallRamp (u + -1 * x) - wallRamp u)

theorem measurable_rampKernelRight : Measurable (Function.uncurry rampKernelRight) :=
  (measurable_archLevyDensity.comp measurable_fst).mul
    ((measurable_wallRamp.comp measurable_snd).sub
      (measurable_wallRamp.comp (measurable_snd.add measurable_fst)))

theorem measurable_rampKernelLeft : Measurable (Function.uncurry rampKernelLeft) :=
  (measurable_archLevyDensity.comp measurable_fst).mul
    ((measurable_wallRamp.comp (measurable_snd.add (measurable_fst.const_mul (-1)))).sub
      (measurable_wallRamp.comp measurable_snd))

theorem abs_rampKernelRight_le :
    ∀ x ∈ Ioi (0 : ℝ), ∀ u, |rampKernelRight x u| ≤ 14 * Real.exp (-(x / 2)) := by
  intro x hx u
  have hx0 : (0 : ℝ) < x := hx
  unfold rampKernelRight
  rw [abs_mul, abs_of_pos (archLevyDensity_pos hx0)]
  exact (mul_le_mul_of_nonneg_left (abs_wallRamp_sub_shift_le hx0 u)
    (archLevyDensity_pos hx0).le).trans (archLevyDensity_mul_min_le hx0)

theorem abs_rampKernelLeft_le :
    ∀ x ∈ Ioi (0 : ℝ), ∀ u, |rampKernelLeft x u| ≤ 14 * Real.exp (-(x / 2)) := by
  intro x hx u
  have hx0 : (0 : ℝ) < x := hx
  unfold rampKernelLeft
  rw [abs_mul, abs_of_pos (archLevyDensity_pos hx0)]
  have h := abs_wallRamp_sub_shift_le hx0 (u + -1 * x)
  rw [show u + -1 * x + x = u by ring] at h
  exact (mul_le_mul_of_nonneg_left h (archLevyDensity_pos hx0).le).trans
    (archLevyDensity_mul_min_le hx0)

theorem integrableOn_fourteen_exp : IntegrableOn (fun x : ℝ => 14 * Real.exp (-(x / 2))) (Ioi 0) :=
  integrableOn_exp_neg_half.const_mul 14

/-- **The commutator of the ramp with the Lévy form** is two kernel convolutions:
\`levyMixed (χF) G − levyMixed F (χG) = ∫ (∫ κ₊ F(u + x)) G − ∫ (∫ κ₋ F(u − x)) G\`. -/
theorem levyMixed_ramp_commutator {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    levyMixed (fun u => wallRamp u * F u) G - levyMixed F (fun u => wallRamp u * G u) =
      (∫ u, (∫ x in Ioi 0, rampKernelRight x u * F (u + 1 * x)) * G u) -
        ∫ u, (∫ x in Ioi 0, rampKernelLeft x u * F (u + -1 * x)) * G u := by
  have hU := criticalHalfLineEnergyDomain_lipschitz_mul hF measurable_wallRamp
    abs_wallRamp_le_one abs_wallRamp_sub_le
  have hχG := criticalHalfLineEnergyDomain_lipschitz_mul hG measurable_wallRamp
    abs_wallRamp_le_one abs_wallRamp_sub_le
  obtain ⟨i₁, e₁⟩ := kernel_translate_pairing integrableOn_fourteen_exp measurable_rampKernelRight
    abs_rampKernelRight_le hF.meas hG.meas hF.sq hG.sq 1
  obtain ⟨i₂, e₂⟩ := kernel_translate_pairing integrableOn_fourteen_exp measurable_rampKernelLeft
    abs_rampKernelLeft_le hF.meas hG.meas hF.sq hG.sq (-1)
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
  have hχb : ∀ᵐ u ∂volume, ‖wallRamp u - wallRamp (u + x)‖ ≤ 1 := Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs]
    exact (abs_wallRamp_sub_shift_le hx0 u).trans (min_le_right _ _)
  have hχm : AEStronglyMeasurable (fun u => wallRamp u - wallRamp (u + x)) volume :=
    (continuous_wallRamp.sub (continuous_wallRamp.comp (continuous_add_right x))).aestronglyMeasurable
  have iA := integrable_mul_of_memLp (hUL.sub (memLp_two_shift hUL x))
    (hGL.sub (memLp_two_shift hGL x))
  have iB := integrable_mul_of_memLp (hFL.sub (memLp_two_shift hFL x))
    (hχGL.sub (memLp_two_shift hχGL x))
  have iP := (integrable_mul_of_memLp (memLp_two_shift hFL x) hGL).bdd_mul hχm hχb
  have iQ := (integrable_mul_of_memLp hFL (memLp_two_shift hGL x)).bdd_mul hχm hχb
  have hAB : (∫ u, (wallRamp u * F u - wallRamp (u + x) * F (u + x)) * (G u - G (u + x))) -
      (∫ u, (F u - F (u + x)) * (wallRamp u * G u - wallRamp (u + x) * G (u + x))) =
      (∫ u, (wallRamp u - wallRamp (u + x)) * (F (u + x) * G u)) -
        ∫ u, (wallRamp u - wallRamp (u + x)) * (F u * G (u + x)) := by
    rw [← integral_sub iA iB, ← integral_sub iP iQ]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [Pi.sub_apply]; ring)
  have hQ : (∫ u, (wallRamp u - wallRamp (u + x)) * (F u * G (u + x))) =
      ∫ u, (wallRamp (u + -1 * x) - wallRamp u) * (F (u + -1 * x) * G u) := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun u => (wallRamp (u + -1 * x) - wallRamp u) * (F (u + -1 * x) * G u)) x
    simp only [show ∀ u : ℝ, u + x + -1 * x = u from fun u => by ring] at h
    exact h
  have e1 : (∫ u, rampKernelRight x u * F (u + 1 * x) * G u) =
      archLevyDensity x * ∫ u, (wallRamp u - wallRamp (u + x)) * (F (u + x) * G u) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      simp only [rampKernelRight, one_mul]; ring)
  have e2 : (∫ u, rampKernelLeft x u * F (u + -1 * x) * G u) =
      archLevyDensity x * ∫ u, (wallRamp (u + -1 * x) - wallRamp u) * (F (u + -1 * x) * G u) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [rampKernelLeft]; ring)
  simp only
  rw [e1, e2, ← hQ, ← mul_sub, ← mul_sub, hAB]

/-- The commutator of the ramp against an essentially bounded profile is a bounded wall forcing. -/
theorem isBoundedWallForcing_commutator {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {C : ℝ}
    (hC : ∀ᵐ u, |F u| ≤ C) :
    IsBoundedWallForcing fun G =>
      levyMixed (fun u => wallRamp u * F u) G - levyMixed F (fun u => wallRamp u * G u) := by
  have hk₁ := isBoundedWallForcing_mass
    (stronglyMeasurable_kernel_translate measurable_rampKernelRight hF.meas 1).aestronglyMeasurable
    (Eventually.of_forall fun u => abs_kernel_translate_le integrableOn_fourteen_exp
      abs_rampKernelRight_le hC (Or.inl rfl) u)
  have hk₂ := isBoundedWallForcing_mass
    (stronglyMeasurable_kernel_translate measurable_rampKernelLeft hF.meas (-1)).aestronglyMeasurable
    (Eventually.of_forall fun u => abs_kernel_translate_le integrableOn_fourteen_exp
      abs_rampKernelLeft_le hC (Or.inr rfl) u)
  exact (hk₁.sub hk₂).congr fun G hG => (levyMixed_ramp_commutator hF hG.domain).symm

end GaloisForLFunctions.ExclusionOfTheCriticalState
