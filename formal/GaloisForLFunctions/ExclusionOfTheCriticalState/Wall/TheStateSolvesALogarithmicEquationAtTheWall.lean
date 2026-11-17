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

end GaloisForLFunctions.ExclusionOfTheCriticalState
