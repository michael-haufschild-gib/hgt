import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasSquaredLogarithmicEnergyOnTheLinesOfItsDecay
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateSatisfiesTheWeakEquation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilSymbolIsALogarithmicMultiplierPlusABoundedKernel

/-!
# The cut state solves the logarithmic window equation

Let `F` solve the weak equation `Q_R(F, H) = 0` on the energy domain, with `|F(u)| ≤ C e^u`, and let
`χ` be a bounded Lipschitz multiplier, `|χ| ≤ 1`. Split the Lévy density of the Gamma form as
`ω = ν + r`, with `ν(t) = e^{−t}/(2t)` the Lévy density of the logarithmic form and `r ≥ 0`
integrable (`archLogRemainder`). For every test `G` of the energy domain carried by `[−2A, 0]`

  `∫ G χF + ∫_{t>0} ν(t) ∫ (G(u) − G(u+t)) (χF(u) − χF(u+t)) du dt = ∫ G φ`
  (`cut_logarithmic_equation`),

with the explicit forcing `φ = cutForcing R χ F`, essentially bounded on `[−2A, 0]`
(`cutForcing_bounded`). Its terms:

* the weak equation with the test `χG` trades the Gamma form of `(F, χG)` for the prime, pole and
  confinement forms; each is a pairing of `G` with a function bounded on the window, the prime wave
  `Σ_n Λ(n) n^{−1/2} (F(y − log n) + F(y + log n))` converging because `|F(u)| ≤ C e^u`;
* moving `χ` across the Lévy form costs the commutator
  `∫_{t>0} ω(t) [F(y−t)(χ(y) − χ(y−t)) + F(y+t)(χ(y) − χ(y+t))] dt` (`levyCommutator`), bounded
  because `ω(t) min(Λt, 2)` is integrable;
* the remainder `r` contributes the second difference `∫ r(t) (2W(y) − W(y+t) − W(y−t)) dt`
  (`remainderAverage`).

For the critical state and the cutoff `wallWindowCutoff A` (`0` left of `−2A`, `1` right of `−A`)
this is the window equation of the critical Hardy theory of the window cone in half-line
coordinates (`criticalState_cut_logarithmic_equation`).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open CanonicalSystemOfTheWindowTower (logReferenceLevyDensity archLogRemainder
  measurable_archLogRemainder archLogRemainder_nonneg integrableOn_archLogRemainder)

/-! ### The cutoff of the window -/

/-- The cutoff of the window `[−2A, 0]`: `0` left of `−2A`, `1` right of `−A`, linear between. -/
def wallWindowCutoff (A u : ℝ) : ℝ := min (max ((u + 2 * A) / A) 0) 1

theorem continuous_wallWindowCutoff (A : ℝ) : Continuous (wallWindowCutoff A) :=
  (((continuous_id.add continuous_const).div_const A).max continuous_const).min continuous_const

theorem measurable_wallWindowCutoff (A : ℝ) : Measurable (wallWindowCutoff A) :=
  (continuous_wallWindowCutoff A).measurable

theorem wallWindowCutoff_nonneg (A u : ℝ) : 0 ≤ wallWindowCutoff A u :=
  le_min (le_max_right _ _) zero_le_one

theorem abs_wallWindowCutoff_le (A u : ℝ) : |wallWindowCutoff A u| ≤ 1 := by
  rw [abs_of_nonneg (wallWindowCutoff_nonneg A u)]
  exact min_le_right _ _

theorem wallWindowCutoff_of_le {A u : ℝ} (hA : 0 < A) (hu : u ≤ -(2 * A)) :
    wallWindowCutoff A u = 0 := by
  have h : (u + 2 * A) / A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  rw [wallWindowCutoff, max_eq_right h, min_eq_left zero_le_one]

theorem wallWindowCutoff_of_ge {A u : ℝ} (hA : 0 < A) (hu : -A ≤ u) :
    wallWindowCutoff A u = 1 := by
  have h : 1 ≤ (u + 2 * A) / A := by rw [le_div_iff₀ hA]; linarith
  rw [wallWindowCutoff, max_eq_left (zero_le_one.trans h), min_eq_right h]

theorem abs_wallWindowCutoff_sub_le {A : ℝ} (hA : 0 < A) (u v : ℝ) :
    |wallWindowCutoff A u - wallWindowCutoff A v| ≤ A⁻¹ * |u - v| := by
  unfold wallWindowCutoff
  have e : (u + 2 * A) / A - (v + 2 * A) / A = A⁻¹ * (u - v) := by
    rw [div_sub_div_same, div_eq_inv_mul]; ring
  calc _ ≤ max |max ((u + 2 * A) / A) 0 - max ((v + 2 * A) / A) 0| |(1 : ℝ) - 1| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = |max ((u + 2 * A) / A) 0 - max ((v + 2 * A) / A) 0| := by
        rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    _ ≤ |(u + 2 * A) / A - (v + 2 * A) / A| := abs_max_sub_max_le_abs _ _ _
    _ = A⁻¹ * |u - v| := by rw [e, abs_mul, abs_of_pos (inv_pos.mpr hA)]

/-! ### Elementary bounds -/

private theorem abs_sub_le_two {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a - b| ≤ 2 := by
  rw [abs_le] at ha hb ⊢
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

private theorem ae_comp_add_right {p : ℝ → Prop} (h : ∀ᵐ v, p v) (t : ℝ) : ∀ᵐ u, p (u + t) :=
  (measurePreserving_add_right volume t).quasiMeasurePreserving.ae h

private theorem ae_comp_sub_right {p : ℝ → Prop} (h : ∀ᵐ v, p v) (t : ℝ) : ∀ᵐ u, p (u - t) :=
  (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae h

private theorem ae_comp_sub_left {p : ℝ → Prop} (h : ∀ᵐ v, p v) (y : ℝ) : ∀ᵐ t, p (y - t) :=
  (Measure.measurePreserving_sub_left volume y).quasiMeasurePreserving.ae h

private theorem ae_comp_add_left {p : ℝ → Prop} (h : ∀ᵐ v, p v) (y : ℝ) : ∀ᵐ t, p (y + t) :=
  (measurePreserving_add_left volume y).quasiMeasurePreserving.ae h

private theorem memLp_two_shift_sub {F : ℝ → ℝ} (hF : MemLp F 2 volume) (x : ℝ) :
    MemLp (fun u => F (u - x)) 2 volume :=
  hF.comp_measurePreserving (measurePreserving_sub_right volume x)

private theorem integrable_bdd_mul {f g : ℝ → ℝ} (hg : Integrable g)
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hb : ∀ᵐ x, |f x| ≤ C) :
    Integrable fun x => f x * g x :=
  (hg.mul_bdd hf (hb.mono fun _ hx => (Real.norm_eq_abs _).trans_le hx)).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

/-- A function bounded on `[−2A, 0]` pairs integrably with a profile carried by `[−2A, 0]`. -/
private theorem integrable_mul_of_window {G T : ℝ → ℝ} (hG1 : Integrable G)
    (hTm : AEStronglyMeasurable T volume) {A K : ℝ}
    (hGA : ∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0)
    (hT : ∀ᵐ y, y ∈ Icc (-(2 * A)) 0 → |T y| ≤ K) : Integrable fun y => G y * T y := by
  refine (hG1.abs.mul_const K).mono' (hG1.aestronglyMeasurable.mul hTm) ?_
  filter_upwards [hT] with y hy
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hG0 : G y = 0
  · rw [hG0, abs_zero, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hy (hGA y hG0)) (abs_nonneg _)

/-- With `F = 0` on `[0, ∞)`, the bound `|F(u)| ≤ C e^u` gives `|F| ≤ C`. -/
theorem ae_abs_le_of_abs_le_exp {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hsupp : ∀ v, 0 ≤ v → F v = 0) (hCe : ∀ᵐ v, |F v| ≤ C * Real.exp v) :
    ∀ᵐ v, |F v| ≤ C := by
  filter_upwards [hCe] with v hv
  rcases lt_or_ge v 0 with h | h
  · exact hv.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr h.le))
  · rw [hsupp v h, abs_zero]; exact hC

/-- The critical state is `O(e^u)`. -/
theorem criticalState_ae_abs_le_exp {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ u ∂volume, |F u| ≤ C * Real.exp u := by
  obtain ⟨C, hC, h⟩ :=
    (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).1 1 (by norm_num) (by norm_num)
  exact ⟨C, hC, h.mono fun u hu => by rwa [one_mul] at hu⟩

/-- `ω(t) min(Λt, M) ≤ (3Λ + 2M) e^{−t/2}`: a Lipschitz jump is paid near the origin. -/
private theorem archLevyDensity_mul_min_le {Λ M t : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (ht : 0 < t) :
    archLevyDensity t * min (Λ * t) M ≤ (3 * Λ + 2 * M) * Real.exp (-(t / 2)) := by
  have hmin0 : 0 ≤ min (Λ * t) M := le_min (mul_nonneg hΛ ht.le) hM
  have he0 := Real.exp_pos (-(t / 2))
  rcases le_total t 1 with h1 | h1
  · have hn := archLevyDensity_le_near ht h1
    have he : 1 / 2 ≤ Real.exp (-(t / 2)) := by linarith [Real.add_one_le_exp (-(t / 2))]
    calc archLevyDensity t * min (Λ * t) M ≤ 3 / (2 * t) * (Λ * t) :=
          mul_le_mul hn (min_le_left _ _) hmin0 (by positivity)
      _ = 3 * Λ / 2 := by
          rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]; ring
      _ ≤ (3 * Λ + 2 * M) * Real.exp (-(t / 2)) := by
          nlinarith [mul_nonneg hΛ (sub_nonneg.mpr he), mul_nonneg hM he0.le]
  · have hf := archLevyDensity_le_far h1
    calc archLevyDensity t * min (Λ * t) M ≤ 2 * Real.exp (-(t / 2)) * M :=
          mul_le_mul hf (min_le_right _ _) hmin0 (by positivity)
      _ ≤ (3 * Λ + 2 * M) * Real.exp (-(t / 2)) := by
          nlinarith [mul_nonneg hΛ he0.le]

private theorem integrableOn_archLevyDensity_mul_min {Λ M : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    IntegrableOn (fun t => archLevyDensity t * min (Λ * t) M) (Ioi 0) := by
  refine (integrableOn_exp_neg_half.const_mul (3 * Λ + 2 * M)).mono'
    (measurable_archLevyDensity.mul
      ((measurable_const.mul measurable_id).min measurable_const)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht).le
    (le_min (mul_nonneg hΛ (le_of_lt ht)) hM))]
  exact archLevyDensity_mul_min_le hΛ hM ht

/-! ### The remainder density -/

/-- The second difference of `W` averaged against the remainder density `r = ω − ν`. -/
def remainderAverage (W : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in Ioi 0, archLogRemainder t * (2 * W y - W (y + t) - W (y - t))

/-- The jump pairing at lag `t` is the pairing with the second difference. -/
private theorem integral_jump_mul_eq {G W : ℝ → ℝ} (hG : MemLp G 2 volume)
    (hW : MemLp W 2 volume) (t : ℝ) :
    (∫ u, (G u - G (u + t)) * (W u - W (u + t))) =
      ∫ y, G y * (2 * W y - W (y + t) - W (y - t)) := by
  have h1 := integrable_mul_of_memLp hG hW
  have h2 := integrable_mul_of_memLp hG (memLp_two_shift hW t)
  have h3 := integrable_mul_of_memLp (memLp_two_shift hG t) hW
  have h4 := integrable_mul_of_memLp (memLp_two_shift hG t) (memLp_two_shift hW t)
  have h5 := integrable_mul_of_memLp hG (memLp_two_shift_sub hW t)
  have h12 : Integrable fun u => G u * W u - G u * W (u + t) := h1.sub h2
  have h123 : Integrable fun u => G u * W u - G u * W (u + t) - G (u + t) * W u := h12.sub h3
  have h6 : Integrable fun y => 2 * (G y * W y) - G y * W (y + t) := (h1.const_mul 2).sub h2
  have e3 : (∫ u, G (u + t) * W u) = ∫ y, G y * W (y - t) := by
    rw [← integral_sub_right_eq_self (fun u => G (u + t) * W u) t]
    simp only [sub_add_cancel]
  have e4 : (∫ u, G (u + t) * W (u + t)) = ∫ y, G y * W y :=
    integral_add_right_eq_self (fun u => G u * W u) t
  calc (∫ u, (G u - G (u + t)) * (W u - W (u + t)))
      = ∫ u, (G u * W u - G u * W (u + t) - G (u + t) * W u + G (u + t) * W (u + t)) := by
        congr 1; ext u; ring
    _ = (∫ u, G u * W u) - (∫ u, G u * W (u + t)) - (∫ u, G (u + t) * W u) +
          ∫ u, G (u + t) * W (u + t) := by
        rw [integral_add h123 h4, integral_sub h12 h3, integral_sub h1 h2]
    _ = 2 * (∫ y, G y * W y) - (∫ y, G y * W (y + t)) - ∫ y, G y * W (y - t) := by
        rw [e3, e4]; ring
    _ = ∫ y, G y * (2 * W y - W (y + t) - W (y - t)) := by
        rw [← integral_const_mul, ← integral_sub (h1.const_mul 2) h2, ← integral_sub h6 h5]
        congr 1; ext y; ring

/-- **The remainder form is a pairing with a bounded average.** -/
theorem integral_archLogRemainder_jump {G W : ℝ → ℝ} (hGm : Measurable G) (hG1 : Integrable G)
    (hG : MemLp G 2 volume) (hWm : Measurable W) (hW : MemLp W 2 volume) {C : ℝ}
    (hC : ∀ᵐ u, |W u| ≤ C) :
    IntegrableOn (fun t => archLogRemainder t *
        ∫ u, (G u - G (u + t)) * (W u - W (u + t))) (Ioi 0) ∧
      (∫ t in Ioi 0, archLogRemainder t * ∫ u, (G u - G (u + t)) * (W u - W (u + t))) =
        ∫ y, G y * remainderAverage W y := by
  have hr : Integrable archLogRemainder (volume.restrict (Ioi 0)) := integrableOn_archLogRemainder
  have hmaj : Integrable (fun p : ℝ × ℝ => |archLogRemainder p.1| * (4 * C * |G p.2|))
      ((volume.restrict (Ioi 0)).prod volume) :=
    hr.abs.mul_prod (hG1.abs.const_mul (4 * C))
  have hset : MeasurableSet {p : ℝ × ℝ | |W p.2| ≤ C ∧ |W (p.2 + p.1)| ≤ C ∧
      |W (p.2 - p.1)| ≤ C} :=
    (measurableSet_le (continuous_abs.measurable.comp (hWm.comp measurable_snd))
      measurable_const).inter
      ((measurableSet_le (continuous_abs.measurable.comp
        (hWm.comp (measurable_snd.add measurable_fst))) measurable_const).inter
        (measurableSet_le (continuous_abs.measurable.comp
          (hWm.comp (measurable_snd.sub measurable_fst))) measurable_const))
  have hae : ∀ᵐ p ∂((volume.restrict (Ioi 0)).prod volume),
      |W p.2| ≤ C ∧ |W (p.2 + p.1)| ≤ C ∧ |W (p.2 - p.1)| ≤ C :=
    (Measure.ae_prod_iff_ae_ae hset).mpr
      (ae_of_all _ fun t => hC.and ((ae_comp_add_right hC t).and (ae_comp_sub_right hC t)))
  have hint : Integrable (Function.uncurry fun t y => archLogRemainder t *
      (G y * (2 * W y - W (y + t) - W (y - t)))) ((volume.restrict (Ioi 0)).prod volume) := by
    refine hmaj.mono' ?_ ?_
    · exact ((measurable_archLogRemainder.comp measurable_fst).mul ((hGm.comp measurable_snd).mul
        (((measurable_const.mul (hWm.comp measurable_snd)).sub
          (hWm.comp (measurable_snd.add measurable_fst))).sub
            (hWm.comp (measurable_snd.sub measurable_fst))))).aestronglyMeasurable
    · filter_upwards [hae] with p hp
      obtain ⟨h0, h1, h2⟩ := hp
      have hK : |2 * W p.2 - W (p.2 + p.1) - W (p.2 - p.1)| ≤ 4 * C := by
        rw [abs_le] at h0 h1 h2 ⊢
        constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
      show ‖archLogRemainder p.1 * (G p.2 * (2 * W p.2 - W (p.2 + p.1) - W (p.2 - p.1)))‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |archLogRemainder p.1| * (|G p.2| * |2 * W p.2 - W (p.2 + p.1) - W (p.2 - p.1)|)
          ≤ |archLogRemainder p.1| * (|G p.2| * (4 * C)) := by gcongr
        _ = |archLogRemainder p.1| * (4 * C * |G p.2|) := by ring
  have hfun : (fun t => archLogRemainder t * ∫ u, (G u - G (u + t)) * (W u - W (u + t))) =
      fun t => ∫ y, archLogRemainder t * (G y * (2 * W y - W (y + t) - W (y - t))) := by
    ext t; rw [integral_jump_mul_eq hG hW t, integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hfun]; exact hint.integral_prod_left
  · rw [hfun, integral_integral_swap hint]
    congr 1; ext y
    rw [remainderAverage, ← integral_const_mul]
    congr 1; ext t; ring

/-- The remainder average of an essentially bounded profile is bounded. -/
theorem abs_remainderAverage_le {W : ℝ → ℝ} {C : ℝ} (hC : ∀ᵐ u, |W u| ≤ C) {y : ℝ}
    (hy : |W y| ≤ C) :
    |remainderAverage W y| ≤ 4 * C * ∫ t in Ioi 0, archLogRemainder t := by
  have hr : Integrable archLogRemainder (volume.restrict (Ioi 0)) := integrableOn_archLogRemainder
  rw [remainderAverage, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hr.const_mul (4 * C)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (ae_comp_add_left hC y),
    ae_restrict_of_ae (ae_comp_sub_left hC y)] with t ht h1 h2
  have hK : |2 * W y - W (y + t) - W (y - t)| ≤ 4 * C := by
    have h0 := hy
    rw [abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (archLogRemainder_nonneg ht)]
  calc archLogRemainder t * |2 * W y - W (y + t) - W (y - t)| ≤ archLogRemainder t * (4 * C) :=
        mul_le_mul_of_nonneg_left hK (archLogRemainder_nonneg ht)
    _ = 4 * C * archLogRemainder t := by ring

theorem stronglyMeasurable_remainderAverage {W : ℝ → ℝ} (hWm : Measurable W) :
    StronglyMeasurable (remainderAverage W) :=
  StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))
    (f := fun p : ℝ × ℝ => archLogRemainder p.2 * (2 * W p.1 - W (p.1 + p.2) - W (p.1 - p.2)))
    ((measurable_archLogRemainder.comp measurable_snd).mul
      (((measurable_const.mul (hWm.comp measurable_fst)).sub
        (hWm.comp (measurable_fst.add measurable_snd))).sub
          (hWm.comp (measurable_fst.sub measurable_snd)))).stronglyMeasurable

/-! ### The commutator of a multiplier with the Lévy form -/

/-- The Lévy commutator of a multiplier `χ` with a profile `F`. -/
def levyCommutator (χ F : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in Ioi 0, archLevyDensity t *
    (F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t)))

private theorem integral_commutator_jump_eq {χ F G : ℝ → ℝ} (hχm : Measurable χ)
    (hχ : ∀ u, |χ u| ≤ 1) (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) (t : ℝ) :
    (∫ u, (χ u * F u - χ (u + t) * F (u + t)) * (G u - G (u + t))) -
        ∫ u, (F u - F (u + t)) * (χ u * G u - χ (u + t) * G (u + t)) =
      ∫ y, G y * (F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t))) := by
  have hb : ∀ u v, |χ u - χ v| ≤ 2 := fun u v => abs_sub_le_two (hχ u) (hχ v)
  have hmul : ∀ {f : ℝ → ℝ}, MemLp f 2 volume → MemLp (fun u => χ u * f u) 2 volume :=
    fun {f} hf => hf.of_le (hχm.aestronglyMeasurable.mul hf.1) (ae_of_all _ fun u =>
      (norm_mul _ _).trans_le (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hχ u)))
  have hχF := hmul hF
  have hχG := hmul hG
  have ha : Integrable fun u => (χ u * F u - χ (u + t) * F (u + t)) * (G u - G (u + t)) :=
    integrable_mul_of_memLp (hχF.sub (memLp_two_shift hχF t)) (hG.sub (memLp_two_shift hG t))
  have hb' : Integrable fun u => (F u - F (u + t)) * (χ u * G u - χ (u + t) * G (u + t)) :=
    integrable_mul_of_memLp (hF.sub (memLp_two_shift hF t)) (hχG.sub (memLp_two_shift hχG t))
  have hm1 : Measurable fun u => χ (u + t) - χ u := (hχm.comp (measurable_add_const t)).sub hχm
  have hm2 : Measurable fun u => χ u - χ (u + t) := hχm.sub (hχm.comp (measurable_add_const t))
  have hm3 : Measurable fun y => χ y - χ (y - t) := hχm.sub (hχm.comp (measurable_sub_const t))
  have hp : Integrable fun u => F u * G (u + t) * (χ (u + t) - χ u) :=
    (integrable_mul_of_memLp hF (memLp_two_shift hG t)).mul_bdd hm1.aestronglyMeasurable
      (ae_of_all _ fun u => (Real.norm_eq_abs _).trans_le (hb _ _))
  have hq : Integrable fun u => F (u + t) * G u * (χ u - χ (u + t)) :=
    (integrable_mul_of_memLp (memLp_two_shift hF t) hG).mul_bdd hm2.aestronglyMeasurable
      (ae_of_all _ fun u => (Real.norm_eq_abs _).trans_le (hb _ _))
  have hp' : Integrable fun y => F (y - t) * G y * (χ y - χ (y - t)) :=
    (integrable_mul_of_memLp (memLp_two_shift_sub hF t) hG).mul_bdd hm3.aestronglyMeasurable
      (ae_of_all _ fun u => (Real.norm_eq_abs _).trans_le (hb _ _))
  rw [← integral_sub ha hb']
  calc (∫ u, ((χ u * F u - χ (u + t) * F (u + t)) * (G u - G (u + t)) -
          (F u - F (u + t)) * (χ u * G u - χ (u + t) * G (u + t))))
      = ∫ u, (F u * G (u + t) * (χ (u + t) - χ u) + F (u + t) * G u * (χ u - χ (u + t))) := by
        congr 1; ext u; ring
    _ = (∫ u, F u * G (u + t) * (χ (u + t) - χ u)) +
          ∫ u, F (u + t) * G u * (χ u - χ (u + t)) := integral_add hp hq
    _ = (∫ y, F (y - t) * G y * (χ y - χ (y - t))) +
          ∫ y, F (y + t) * G y * (χ y - χ (y + t)) := by
        congr 1
        rw [← integral_sub_right_eq_self (fun u => F u * G (u + t) * (χ (u + t) - χ u)) t]
        simp only [sub_add_cancel]
    _ = ∫ y, G y * (F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t))) := by
        rw [← integral_add hp' hq]
        congr 1; ext y; ring

private theorem abs_commutator_integrand_le {χ F : ℝ → ℝ} (hχ : ∀ u, |χ u| ≤ 1) {Λ : ℝ}
    (hχL : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|) {C y t : ℝ} (ht : 0 < t)
    (h1 : |F (y - t)| ≤ C) (h2 : |F (y + t)| ≤ C) :
    |F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t))| ≤
      2 * C * min (Λ * t) 2 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans h1
  have m1 : |χ y - χ (y - t)| ≤ min (Λ * t) 2 := by
    refine le_min ?_ (abs_sub_le_two (hχ _) (hχ _))
    have := hχL y (y - t)
    rwa [show y - (y - t) = t by ring, abs_of_pos ht] at this
  have m2 : |χ y - χ (y + t)| ≤ min (Λ * t) 2 := by
    refine le_min ?_ (abs_sub_le_two (hχ _) (hχ _))
    have := hχL y (y + t)
    rwa [show y - (y + t) = -t by ring, abs_neg, abs_of_pos ht] at this
  calc _ ≤ |F (y - t) * (χ y - χ (y - t))| + |F (y + t) * (χ y - χ (y + t))| := abs_add_le _ _
    _ = |F (y - t)| * |χ y - χ (y - t)| + |F (y + t)| * |χ y - χ (y + t)| := by
        rw [abs_mul, abs_mul]
    _ ≤ C * min (Λ * t) 2 + C * min (Λ * t) 2 := by gcongr
    _ = 2 * C * min (Λ * t) 2 := by ring

/-- **Moving a Lipschitz multiplier across the Lévy form.**
`L(χF, G) − L(F, χG) = ∫ G · [χ, L]F`. -/
theorem levyMixed_mul_left_sub_mul_right {χ F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hχm : Measurable χ) (hχ : ∀ u, |χ u| ≤ 1) {Λ : ℝ}
    (hχL : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|) {C : ℝ} (hC : ∀ᵐ u, |F u| ≤ C) :
    levyMixed (fun u => χ u * F u) G - levyMixed F (fun u => χ u * G u) =
      ∫ y, G y * levyCommutator χ F y := by
  have hχF := criticalHalfLineEnergyDomain_lipschitz_mul hF hχm hχ hχL
  have hχG := criticalHalfLineEnergyDomain_lipschitz_mul hG hχm hχ hχL
  have hΛ0 : 0 ≤ Λ := by
    have h := (abs_nonneg _).trans (hχL 0 1)
    rwa [zero_sub, abs_neg, abs_one, mul_one] at h
  have hFm := hF.meas
  have hω : Integrable (fun t => archLevyDensity t * min (Λ * t) 2) (volume.restrict (Ioi 0)) :=
    integrableOn_archLevyDensity_mul_min hΛ0 zero_le_two
  have hmaj : Integrable (fun p : ℝ × ℝ => 2 * C * (archLevyDensity p.1 * min (Λ * p.1) 2) *
      |G p.2|) ((volume.restrict (Ioi 0)).prod volume) :=
    (hω.const_mul (2 * C)).mul_prod hG.integrable.abs
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ |F (p.2 - p.1)| ≤ C ∧ |F (p.2 + p.1)| ≤ C} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le (continuous_abs.measurable.comp
        (hFm.comp (measurable_snd.sub measurable_fst))) measurable_const).inter
        (measurableSet_le (continuous_abs.measurable.comp
          (hFm.comp (measurable_snd.add measurable_fst))) measurable_const))
  have hae : ∀ᵐ p ∂((volume.restrict (Ioi 0)).prod volume),
      0 < p.1 ∧ |F (p.2 - p.1)| ≤ C ∧ |F (p.2 + p.1)| ≤ C := by
    refine (Measure.ae_prod_iff_ae_ae hset).mpr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((ae_comp_sub_right hC t).and (ae_comp_add_right hC t)).mono fun y hy => ⟨ht, hy.1, hy.2⟩
  have hint : Integrable (Function.uncurry fun t y => archLevyDensity t *
      (G y * (F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t)))))
      ((volume.restrict (Ioi 0)).prod volume) := by
    refine hmaj.mono' ?_ ?_
    · exact ((measurable_archLevyDensity.comp measurable_fst).mul
        ((hG.meas.comp measurable_snd).mul
        (((hFm.comp (measurable_snd.sub measurable_fst)).mul ((hχm.comp measurable_snd).sub
          (hχm.comp (measurable_snd.sub measurable_fst)))).add
        ((hFm.comp (measurable_snd.add measurable_fst)).mul ((hχm.comp measurable_snd).sub
          (hχm.comp (measurable_snd.add measurable_fst))))))).aestronglyMeasurable
    · filter_upwards [hae] with p hp
      obtain ⟨ht, h1, h2⟩ := hp
      have hk := abs_commutator_integrand_le hχ hχL ht h1 h2
      show ‖archLevyDensity p.1 * (G p.2 * (F (p.2 - p.1) * (χ p.2 - χ (p.2 - p.1)) +
        F (p.2 + p.1) * (χ p.2 - χ (p.2 + p.1))))‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (archLevyDensity_pos ht)]
      calc archLevyDensity p.1 * (|G p.2| * |F (p.2 - p.1) * (χ p.2 - χ (p.2 - p.1)) +
            F (p.2 + p.1) * (χ p.2 - χ (p.2 + p.1))|)
          ≤ archLevyDensity p.1 * (|G p.2| * (2 * C * min (Λ * p.1) 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
              (archLevyDensity_pos ht).le
        _ = 2 * C * (archLevyDensity p.1 * min (Λ * p.1) 2) * |G p.2| := by ring
  have hfun : (fun t => archLevyDensity t *
      ((∫ u, (χ u * F u - χ (u + t) * F (u + t)) * (G u - G (u + t))) -
        ∫ u, (F u - F (u + t)) * (χ u * G u - χ (u + t) * G (u + t)))) =
      fun t => ∫ y, archLevyDensity t *
        (G y * (F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t)))) := by
    ext t
    rw [integral_commutator_jump_eq hχm hχ hF.memLp_real hG.memLp_real t, integral_const_mul]
  simp only [levyMixed]
  rw [← integral_sub (integrableOn_levyMixedIntegrand hχF hG)
    (integrableOn_levyMixedIntegrand hF hχG)]
  simp_rw [← mul_sub]
  rw [hfun, integral_integral_swap hint]
  congr 1; ext y
  rw [levyCommutator, ← integral_const_mul]
  congr 1; ext t; ring

/-- The commutator is bounded by `2C ∫ ω(t) min(Λt, 2) dt` at every point. -/
theorem abs_levyCommutator_le {χ F : ℝ → ℝ} (hχ : ∀ u, |χ u| ≤ 1) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hχL : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|) {C : ℝ} (hC : ∀ᵐ u, |F u| ≤ C) (y : ℝ) :
    |levyCommutator χ F y| ≤ 2 * C * ∫ t in Ioi 0, archLevyDensity t * min (Λ * t) 2 := by
  have hω : Integrable (fun t => archLevyDensity t * min (Λ * t) 2) (volume.restrict (Ioi 0)) :=
    integrableOn_archLevyDensity_mul_min hΛ0 zero_le_two
  rw [levyCommutator, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hω.const_mul (2 * C)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (ae_comp_sub_left hC y),
    ae_restrict_of_ae (ae_comp_add_left hC y)] with t ht h1 h2
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht)]
  calc archLevyDensity t * |F (y - t) * (χ y - χ (y - t)) + F (y + t) * (χ y - χ (y + t))|
      ≤ archLevyDensity t * (2 * C * min (Λ * t) 2) :=
        mul_le_mul_of_nonneg_left (abs_commutator_integrand_le hχ hχL ht h1 h2)
          (archLevyDensity_pos ht).le
    _ = 2 * C * (archLevyDensity t * min (Λ * t) 2) := by ring

theorem stronglyMeasurable_levyCommutator {χ F : ℝ → ℝ} (hχm : Measurable χ)
    (hFm : Measurable F) : StronglyMeasurable (levyCommutator χ F) :=
  StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))
    (f := fun p : ℝ × ℝ => archLevyDensity p.2 * (F (p.1 - p.2) * (χ p.1 - χ (p.1 - p.2)) +
      F (p.1 + p.2) * (χ p.1 - χ (p.1 + p.2))))
    ((measurable_archLevyDensity.comp measurable_snd).mul
      (((hFm.comp (measurable_fst.sub measurable_snd)).mul ((hχm.comp measurable_fst).sub
        (hχm.comp (measurable_fst.sub measurable_snd)))).add
      ((hFm.comp (measurable_fst.add measurable_snd)).mul ((hχm.comp measurable_fst).sub
        (hχm.comp (measurable_fst.add measurable_snd)))))).stronglyMeasurable

/-! ### The prime wave -/

/-- The prime wave of `F`: `Σ_n Λ(n) n^{−1/2} (F(y − log n) + F(y + log n))`. -/
def statePrimeWave (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (F (y - Real.log n) + F (y + Real.log n))

theorem measurable_statePrimeWave {F : ℝ → ℝ} (hFm : Measurable F) :
    Measurable (statePrimeWave F) :=
  Measurable.tsum fun _ => measurable_const.mul
    ((hFm.comp (measurable_sub_const _)).add (hFm.comp (measurable_add_const _)))

/-- The summable majorant of the prime atoms on `[−2A, 0]`. -/
private def primeAtomMajorant (C A : ℝ) (n : ℕ) : ℝ :=
  vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) * (C * (1 + Real.exp (2 * A)))

private theorem summable_primeAtomMajorant (C A : ℝ) : Summable (primeAtomMajorant C A) :=
  summable_vonMangoldtAtom_mul_exp_neg_one_log.mul_right _

/-- On `[−2A, 0]` the `n`-th prime atom is at most `Λ(n) n^{−3/2} C (1 + e^{2A})`: the backward
shift sees `C e^{y − log n}`, the forward shift is nonzero only for `log n < 2A`. -/
private theorem abs_primeAtom_le {F : ℝ → ℝ} {C A y : ℝ} (hsupp : ∀ v, 0 ≤ v → F v = 0)
    (hy : y ∈ Icc (-(2 * A)) 0) {n : ℕ}
    (h1 : |F (y - Real.log n)| ≤ C * Real.exp (y - Real.log n))
    (h2 : |F (y + Real.log n)| ≤ C * Real.exp (y + Real.log n)) (hC : 0 ≤ C) :
    |vonMangoldtAtom n * (F (y - Real.log n) + F (y + Real.log n))| ≤
      primeAtomMajorant C A n := by
  have hb1 : |F (y - Real.log n)| ≤ C * Real.exp (-(1 * Real.log n)) :=
    h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hy.2])) hC)
  have hb2 : |F (y + Real.log n)| ≤ C * Real.exp (2 * A) * Real.exp (-(1 * Real.log n)) := by
    rcases le_or_gt 0 (y + Real.log n) with h | h
    · rw [hsupp _ h, abs_zero]
      exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (Real.exp_pos _).le
    · calc |F (y + Real.log n)| ≤ C * Real.exp (y + Real.log n) := h2
        _ ≤ C * Real.exp (2 * A + -(1 * Real.log n)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hy.1])) hC
        _ = C * Real.exp (2 * A) * Real.exp (-(1 * Real.log n)) := by rw [Real.exp_add]; ring
  have hs : |F (y - Real.log n) + F (y + Real.log n)| ≤
      C * Real.exp (-(1 * Real.log n)) + C * Real.exp (2 * A) * Real.exp (-(1 * Real.log n)) :=
    (abs_add_le _ _).trans (add_le_add hb1 hb2)
  rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n), primeAtomMajorant]
  calc vonMangoldtAtom n * |F (y - Real.log n) + F (y + Real.log n)| ≤ vonMangoldtAtom n *
        (C * Real.exp (-(1 * Real.log n)) + C * Real.exp (2 * A) * Real.exp (-(1 * Real.log n))) :=
        mul_le_mul_of_nonneg_left hs (vonMangoldtAtom_nonneg n)
    _ = _ := by ring

/-- The `n`-th prime atom of the pairing of `G` with `F`. -/
private def primeAtomTerm (F G : ℝ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  G y * (vonMangoldtAtom n * (F (y - Real.log n) + F (y + Real.log n)))

/-- **The prime form is a pairing with the prime wave.** For `G` carried by `[−2A, 0]` both prime
forms of `(F, G)` equal `∫ G · Σ_n Λ(n) n^{−1/2} (F(y − log n) + F(y + log n))`. -/
theorem primeMixedForm_eq_integral_statePrimeWave {F G : ℝ → ℝ} (hFm : Measurable F) {C A : ℝ}
    (hC : 0 ≤ C) (hCe : ∀ᵐ v, |F v| ≤ C * Real.exp v) (hsupp : ∀ v, 0 ≤ v → F v = 0)
    (hGm : Measurable G) (hG1 : Integrable G) (hGA : ∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0) :
    Integrable (fun y => G y * statePrimeWave F y) ∧
      primeMixedForm F G = ∫ y, G y * statePrimeWave F y ∧
      primeMixedForm G F = ∫ y, G y * statePrimeWave F y := by
  have hCb := ae_abs_le_of_abs_le_exp hC hsupp hCe
  have hpt : ∀ᵐ y, ∀ n : ℕ, |F (y - Real.log n)| ≤ C * Real.exp (y - Real.log n) ∧
      |F (y + Real.log n)| ≤ C * Real.exp (y + Real.log n) :=
    ae_all_iff.mpr fun n => (ae_comp_sub_right hCe _).and (ae_comp_add_right hCe _)
  have hatom : ∀ᵐ y, y ∈ Icc (-(2 * A)) 0 → ∀ n : ℕ,
      |vonMangoldtAtom n * (F (y - Real.log n) + F (y + Real.log n))| ≤
        primeAtomMajorant C A n := by
    filter_upwards [hpt] with y hy hyA n
    exact abs_primeAtom_le hsupp hyA (hy n).1 (hy n).2 hC
  have hbd : ∀ᵐ y, ∀ n : ℕ, |primeAtomTerm F G n y| ≤ |G y| * primeAtomMajorant C A n := by
    filter_upwards [hatom] with y hy n
    rw [primeAtomTerm, abs_mul]
    by_cases hG0 : G y = 0
    · rw [hG0, abs_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hy (hGA y hG0) n) (abs_nonneg _)
  have hTm : ∀ n, Measurable (primeAtomTerm F G n) := fun n =>
    hGm.mul (measurable_const.mul
      ((hFm.comp (measurable_sub_const _)).add (hFm.comp (measurable_add_const _))))
  have hTi : ∀ n, Integrable (primeAtomTerm F G n) := fun n =>
    (hG1.abs.mul_const (primeAtomMajorant C A n)).mono' (hTm n).aestronglyMeasurable
      (hbd.mono fun y hy => (Real.norm_eq_abs _).trans_le (hy n))
  have hsum : Summable fun n => ∫ y, ‖primeAtomTerm F G n y‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_primeAtomMajorant C A).mul_left (∫ y, |G y|))
    rw [← integral_mul_const]
    exact integral_mono_ae (hTi n).norm (hG1.abs.mul_const _)
      (hbd.mono fun y hy => (Real.norm_eq_abs _).trans_le (hy n))
  have htsum := integral_tsum_of_summable_integral_norm hTi hsum
  have hwave : (fun y => ∑' n, primeAtomTerm F G n y) = fun y => G y * statePrimeWave F y := by
    ext y; simp only [primeAtomTerm, statePrimeWave]; rw [tsum_mul_left]
  rw [hwave] at htsum
  have hPb : ∀ᵐ y, y ∈ Icc (-(2 * A)) 0 →
      |statePrimeWave F y| ≤ ∑' n, primeAtomMajorant C A n := by
    filter_upwards [hatom] with y hy hyA
    rw [← Real.norm_eq_abs]
    exact tsum_of_norm_bounded (summable_primeAtomMajorant C A).hasSum fun n => by
      rw [Real.norm_eq_abs]; exact hy hyA n
  have hint := integrable_mul_of_window hG1 (measurable_statePrimeWave hFm).aestronglyMeasurable
    hGA hPb
  have hpair1 : ∀ n : ℕ, primePairTerm F G n = ∫ y, primeAtomTerm F G n y := by
    intro n
    have ha : Integrable fun y => F (y + Real.log n) * G y :=
      integrable_bdd_mul hG1 (hFm.comp (measurable_add_const _)).aestronglyMeasurable
        (ae_comp_add_right hCb _)
    have hb : Integrable fun y => F (y - Real.log n) * G y :=
      integrable_bdd_mul hG1 (hFm.comp (measurable_sub_const _)).aestronglyMeasurable
        (ae_comp_sub_right hCb _)
    have e1 : (∫ t, F t * G (t - Real.log n)) = ∫ y, F (y + Real.log n) * G y := by
      rw [← integral_add_right_eq_self (fun t => F t * G (t - Real.log n)) (Real.log n)]
      simp only [add_sub_cancel_right]
    have e2 : (∫ t, F t * G (t + Real.log n)) = ∫ y, F (y - Real.log n) * G y := by
      rw [← integral_sub_right_eq_self (fun t => F t * G (t + Real.log n)) (Real.log n)]
      simp only [sub_add_cancel]
    rw [primePairTerm, e1, e2, ← integral_add ha hb, ← integral_const_mul]
    congr 1; ext y; simp only [primeAtomTerm]; ring
  have hpair2 : ∀ n : ℕ, primePairTerm G F n = ∫ y, primeAtomTerm F G n y := by
    intro n
    have ha : Integrable fun t => G t * F (t - Real.log n) :=
      hG1.mul_bdd (hFm.comp (measurable_sub_const _)).aestronglyMeasurable
        ((ae_comp_sub_right hCb _).mono fun y hy => (Real.norm_eq_abs _).trans_le hy)
    have hb : Integrable fun t => G t * F (t + Real.log n) :=
      hG1.mul_bdd (hFm.comp (measurable_add_const _)).aestronglyMeasurable
        ((ae_comp_add_right hCb _).mono fun y hy => (Real.norm_eq_abs _).trans_le hy)
    rw [primePairTerm, ← integral_add ha hb, ← integral_const_mul]
    congr 1; ext y; simp only [primeAtomTerm]; ring
  refine ⟨hint, ?_, ?_⟩
  · rw [primeMixedForm, ← htsum]; exact tsum_congr hpair1
  · rw [primeMixedForm, ← htsum]; exact tsum_congr hpair2

/-! ### Pole and confinement -/

/-- The pole wave `2 c(F) cosh(y/2) − 2 s(F) sinh(y/2)`. -/
def poleWave (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * coshHalfMoment F * Real.cosh (y / 2) - 2 * sinhHalfMoment F * Real.sinh (y / 2)

theorem continuous_poleWave (F : ℝ → ℝ) : Continuous (poleWave F) := by
  unfold poleWave; fun_prop

private theorem abs_poleWave_le (F : ℝ → ℝ) {A y : ℝ} (hy : y ∈ Icc (-(2 * A)) 0) :
    |poleWave F y| ≤ (2 * |coshHalfMoment F| + 2 * |sinhHalfMoment F|) * Real.exp A := by
  have hyA : |y| / 2 ≤ A := by rw [abs_of_nonpos hy.2]; linarith [hy.1]
  have hc := (abs_cosh_half_le_exp y).trans (Real.exp_le_exp.mpr hyA)
  have hs := (abs_sinh_half_le_exp y).trans (Real.exp_le_exp.mpr hyA)
  unfold poleWave
  calc _ ≤ |2 * coshHalfMoment F * Real.cosh (y / 2)| +
        |2 * sinhHalfMoment F * Real.sinh (y / 2)| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ = 2 * |coshHalfMoment F| * |Real.cosh (y / 2)| +
        2 * |sinhHalfMoment F| * |Real.sinh (y / 2)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
    _ ≤ 2 * |coshHalfMoment F| * Real.exp A + 2 * |sinhHalfMoment F| * Real.exp A := by gcongr
    _ = _ := by ring

private theorem pole_pairing_eq {F G χ : ℝ → ℝ} (hG1 : Integrable G)
    (hχm : Measurable χ) (hχ : ∀ u, |χ u| ≤ 1) {A : ℝ}
    (hGA : ∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0) :
    Integrable (fun y => G y * (χ y * poleWave F y)) ∧
      2 * coshHalfMoment F * coshHalfMoment (fun u => χ u * G u) -
          2 * sinhHalfMoment F * sinhHalfMoment (fun u => χ u * G u) =
        ∫ y, G y * (χ y * poleWave F y) := by
  have hχG1 : Integrable fun y => χ y * G y :=
    integrable_bdd_mul hG1 hχm.aestronglyMeasurable (ae_of_all _ hχ)
  have hwin : ∀ {k : ℝ → ℝ}, Continuous k → (∀ u, |k u| ≤ Real.exp (|u| / 2)) →
      Integrable fun y => χ y * G y * k y := by
    intro k hk hkb
    refine integrable_mul_of_window (G := fun y => χ y * G y) (K := Real.exp A) hχG1
      hk.measurable.aestronglyMeasurable (fun y hy => hGA y (right_ne_zero_of_mul hy))
      (ae_of_all _ fun y hy => (hkb y).trans (Real.exp_le_exp.mpr ?_))
    rw [abs_of_nonpos hy.2]; linarith [hy.1]
  have hc : Integrable fun y => χ y * G y * Real.cosh (y / 2) :=
    hwin (by fun_prop) abs_cosh_half_le_exp
  have hs : Integrable fun y => χ y * G y * Real.sinh (y / 2) :=
    hwin (by fun_prop) abs_sinh_half_le_exp
  have hP : Integrable fun y => G y * (χ y * poleWave F y) := by
    refine ((hc.const_mul (2 * coshHalfMoment F)).sub
      (hs.const_mul (2 * sinhHalfMoment F))).congr (ae_of_all _ fun y => ?_)
    simp only [poleWave, Pi.sub_apply]; ring
  refine ⟨hP, ?_⟩
  have ec : coshHalfMoment (fun u => χ u * G u) = ∫ x, χ x * G x * Real.cosh (x / 2) := rfl
  have es : sinhHalfMoment (fun u => χ u * G u) = ∫ x, χ x * G x * Real.sinh (x / 2) := rfl
  rw [ec, es, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hc.const_mul _) (hs.const_mul _)]
  congr 1; ext y; simp only [poleWave]; ring

/-- The confinement wave `a(R) χ(y) F(y) e^{−8y}` on `y < 0`. -/
def confinementWave (R : ℝ) (χ F : ℝ → ℝ) (y : ℝ) : ℝ :=
  (Iio 0).indicator (fun y => criticalAliasCoefficient R * (χ y * F y * Real.exp (-(8 * y)))) y

theorem measurable_confinementWave {R : ℝ} {χ F : ℝ → ℝ} (hχm : Measurable χ)
    (hFm : Measurable F) : Measurable (confinementWave R χ F) :=
  (measurable_const.mul ((hχm.mul hFm).mul
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-(8 * y))).measurable)).indicator
    measurableSet_Iio

private theorem confinement_pairing_eq (R : ℝ) (F G χ : ℝ → ℝ) :
    criticalAliasCoefficient R * (∫ u in Iio 0, F u * (χ u * G u) * Real.exp (-(8 * u))) =
      ∫ y, G y * confinementWave R χ F y := by
  rw [← integral_const_mul, ← integral_indicator measurableSet_Iio]
  congr 1; ext y
  simp only [confinementWave, Set.indicator_apply]
  split_ifs <;> ring

private theorem abs_confinementWave_le {R : ℝ} {χ F : ℝ → ℝ} (hχ : ∀ u, |χ u| ≤ 1)
    {C A y : ℝ} (hy : y ∈ Icc (-(2 * A)) 0) (hF : |F y| ≤ C) :
    |confinementWave R χ F y| ≤ |criticalAliasCoefficient R| * C * Real.exp (16 * A) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hF
  have hχy := hχ y
  simp only [confinementWave, Set.indicator_apply]
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(8 * y)) ≤ Real.exp (16 * A) := Real.exp_le_exp.mpr (by linarith [hy.1])
    calc |criticalAliasCoefficient R| * (|χ y| * |F y| * Real.exp (-(8 * y)))
        ≤ |criticalAliasCoefficient R| * (1 * C * Real.exp (16 * A)) := by gcongr
      _ = _ := by ring
  · rw [abs_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) hC) (Real.exp_pos _).le

/-! ### The window equation -/

/-- The forcing of the cut profile `χF` in the logarithmic window equation. -/
def cutForcing (R : ℝ) (χ F : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 - 2 * gammaHardyPhaseRate 0) * (χ y * F y) + χ y * statePrimeWave F y -
    χ y * poleWave F y - confinementWave R χ F y + levyCommutator χ F y -
    remainderAverage (fun u => χ u * F u) y

theorem measurable_cutForcing {R : ℝ} {χ F : ℝ → ℝ} (hχm : Measurable χ) (hFm : Measurable F) :
    Measurable (cutForcing R χ F) :=
  (((((measurable_const.mul (hχm.mul hFm)).add (hχm.mul (measurable_statePrimeWave hFm))).sub
    (hχm.mul (continuous_poleWave F).measurable)).sub (measurable_confinementWave hχm hFm)).add
    (stronglyMeasurable_levyCommutator hχm hFm).measurable).sub
    (stronglyMeasurable_remainderAverage (hχm.mul hFm)).measurable

private theorem lipschitz_const_nonneg {χ : ℝ → ℝ} {Λ : ℝ}
    (hχL : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|) : 0 ≤ Λ := by
  have h := (abs_nonneg _).trans (hχL 0 1)
  rwa [zero_sub, abs_neg, abs_one, mul_one] at h

/-- **The forcing is essentially bounded on the window.** -/
theorem cutForcing_bounded {R : ℝ} {F χ : ℝ → ℝ} (hFd : CriticalHalfLineEnergyDomain F)
    {C A : ℝ} (hC : 0 ≤ C) (hCe : ∀ᵐ v, |F v| ≤ C * Real.exp v) (hχ : ∀ u, |χ u| ≤ 1)
    {Λ : ℝ} (hχL : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|) :
    ∃ K : ℝ, ∀ᵐ y, y ∈ Icc (-(2 * A)) 0 → |cutForcing R χ F y| ≤ K := by
  have hΛ0 := lipschitz_const_nonneg hχL
  have hCb := ae_abs_le_of_abs_le_exp hC hFd.support hCe
  have hWb : ∀ᵐ u, |χ u * F u| ≤ C := hCb.mono fun u hu => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hχ u)).trans hu
  have hpt : ∀ᵐ y, ∀ n : ℕ, |F (y - Real.log n)| ≤ C * Real.exp (y - Real.log n) ∧
      |F (y + Real.log n)| ≤ C * Real.exp (y + Real.log n) :=
    ae_all_iff.mpr fun n => (ae_comp_sub_right hCe _).and (ae_comp_add_right hCe _)
  refine ⟨|1 - 2 * gammaHardyPhaseRate 0| * C + ∑' n, primeAtomMajorant C A n +
    (2 * |coshHalfMoment F| + 2 * |sinhHalfMoment F|) * Real.exp A +
    |criticalAliasCoefficient R| * C * Real.exp (16 * A) +
    2 * C * (∫ t in Ioi 0, archLevyDensity t * min (Λ * t) 2) +
    4 * C * ∫ t in Ioi 0, archLogRemainder t, ?_⟩
  filter_upwards [hCb, hWb, hpt] with y hy hyW hyP hyA
  have b1 : |(1 - 2 * gammaHardyPhaseRate 0) * (χ y * F y)| ≤
      |1 - 2 * gammaHardyPhaseRate 0| * C := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hyW (abs_nonneg _)
  have b2 : |χ y * statePrimeWave F y| ≤ ∑' n, primeAtomMajorant C A n := by
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) (hχ y)).trans ?_
    rw [← Real.norm_eq_abs]
    exact tsum_of_norm_bounded (summable_primeAtomMajorant C A).hasSum fun n => by
      rw [Real.norm_eq_abs]; exact abs_primeAtom_le hFd.support hyA (hyP n).1 (hyP n).2 hC
  have b3 : |χ y * poleWave F y| ≤
      (2 * |coshHalfMoment F| + 2 * |sinhHalfMoment F|) * Real.exp A := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hχ y)).trans (abs_poleWave_le F hyA)
  have b4 : |confinementWave R χ F y| ≤ |criticalAliasCoefficient R| * C * Real.exp (16 * A) :=
    abs_confinementWave_le hχ hyA hy
  have b5 := abs_levyCommutator_le hχ hΛ0 hχL hCb y
  have b6 := abs_remainderAverage_le hWb hyW
  unfold cutForcing
  rw [abs_le] at b1 b2 b3 b4 b5 b6 ⊢
  constructor <;>
    linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2]

/-- **The cut profile solves the logarithmic window equation.** If `F` solves the weak equation,
`|F(u)| ≤ C e^u` and `χ` is a Lipschitz multiplier with `|χ| ≤ 1`, then for every test `G` of the
energy domain carried by `[−2A, 0]`
`∫ G χF + ∫_{t>0} ν(t) ∫ ΔG ΔχF = ∫ G · cutForcing R χ F`. -/
theorem cut_logarithmic_equation {R : ℝ} {F χ G : ℝ → ℝ} (hFd : CriticalHalfLineEnergyDomain F)
    (hweak : ∀ H : ℝ → ℝ, CriticalHalfLineEnergyDomain H → criticalHalfLineMixedEnergy R F H = 0)
    {C A : ℝ} (hC : 0 ≤ C) (hCe : ∀ᵐ v, |F v| ≤ C * Real.exp v)
    (hχm : Measurable χ) (hχ : ∀ u, |χ u| ≤ 1) {Λ : ℝ} (hχL : ∀ u v, |χ u - χ v| ≤ Λ * |u - v|)
    (hG : CriticalHalfLineEnergyDomain G) (hGA : ∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0) :
    (∫ u, G u * (χ u * F u)) + (∫ t in Ioi 0, logReferenceLevyDensity t *
        ∫ u, (G u - G (u + t)) * (χ u * F u - χ (u + t) * F (u + t))) =
      ∫ u, G u * cutForcing R χ F u := by
  have hFm := hFd.meas
  have hΛ0 := lipschitz_const_nonneg hχL
  have hCb := ae_abs_le_of_abs_le_exp hC hFd.support hCe
  have hWd := criticalHalfLineEnergyDomain_lipschitz_mul hFd hχm hχ hχL
  have hχG := criticalHalfLineEnergyDomain_lipschitz_mul hG hχm hχ hχL
  have hWb : ∀ᵐ u, |χ u * F u| ≤ C := hCb.mono fun u hu => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hχ u)).trans hu
  have hχGA : ∀ y, χ y * G y ≠ 0 → y ∈ Icc (-(2 * A)) 0 :=
    fun y hy => hGA y (right_ne_zero_of_mul hy)
  obtain ⟨hrI, hrem⟩ := integral_archLogRemainder_jump (W := fun u => χ u * F u) hG.meas
    hG.integrable hG.memLp_real (hχm.mul hFm) hWd.memLp_real hWb
  have hsplit : (∫ t in Ioi 0, logReferenceLevyDensity t *
        ∫ u, (G u - G (u + t)) * (χ u * F u - χ (u + t) * F (u + t))) =
      levyMixed G (fun u => χ u * F u) - ∫ t in Ioi 0, archLogRemainder t *
        ∫ u, (G u - G (u + t)) * (χ u * F u - χ (u + t) * F (u + t)) := by
    rw [levyMixed, ← integral_sub (integrableOn_levyMixedIntegrand hG hWd) hrI]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [archLogRemainder]
    ring
  have hsymm : levyMixed G (fun u => χ u * F u) = levyMixed (fun u => χ u * F u) G := by
    simp only [levyMixed]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    exact integral_congr_ae (ae_of_all _ fun u => mul_comm _ _)
  have hcomm := levyMixed_mul_left_sub_mul_right hFd hG hχm hχ hχL hCb
  have hlevy := gammaMixedForm_eq_levy hFd hχG
  have hE := hweak _ hχG
  simp only [criticalHalfLineMixedEnergy] at hE
  obtain ⟨hPi, hP1, hP2⟩ := primeMixedForm_eq_integral_statePrimeWave
    (G := fun u => χ u * G u) hFm hC hCe hFd.support (hχm.mul hG.meas) hχG.integrable hχGA
  obtain ⟨i3, hpole⟩ := pole_pairing_eq (F := F) hG.integrable hχm hχ hGA
  have hconf := confinement_pairing_eq R F G χ
  have hmass : (∫ u, F u * (χ u * G u)) = ∫ u, G u * (χ u * F u) :=
    integral_congr_ae (ae_of_all _ fun u =>
      (by ring : F u * (χ u * G u) = G u * (χ u * F u)))
  rw [hmass] at hlevy
  have hPw : (∫ y, χ y * G y * statePrimeWave F y) = ∫ y, G y * (χ y * statePrimeWave F y) :=
    integral_congr_ae (ae_of_all _ fun y =>
      (by ring : χ y * G y * statePrimeWave F y = G y * (χ y * statePrimeWave F y)))
  have i1 : Integrable fun u => G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u)) :=
    ((integrable_mul_of_memLp hG.memLp_real hWd.memLp_real).const_mul
      (1 - 2 * gammaHardyPhaseRate 0)).congr (ae_of_all _ fun u =>
        (by ring : (1 - 2 * gammaHardyPhaseRate 0) * (G u * (χ u * F u)) =
          G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u))))
  have i2 : Integrable fun u => G u * (χ u * statePrimeWave F u) :=
    hPi.congr (ae_of_all _ fun y =>
      (by ring : χ y * G y * statePrimeWave F y = G y * (χ y * statePrimeWave F y)))
  have i4 : Integrable fun u => G u * confinementWave R χ F u :=
    integrable_mul_of_window hG.integrable (measurable_confinementWave hχm hFm).aestronglyMeasurable
      hGA (hCb.mono fun y hy hyA => abs_confinementWave_le hχ hyA hy)
  have i5 : Integrable fun u => G u * levyCommutator χ F u :=
    integrable_mul_of_window hG.integrable
      (stronglyMeasurable_levyCommutator hχm hFm).aestronglyMeasurable hGA
      (ae_of_all _ fun y _ => abs_levyCommutator_le hχ hΛ0 hχL hCb y)
  have i6 : Integrable fun u => G u * remainderAverage (fun u => χ u * F u) u :=
    integrable_mul_of_window hG.integrable
      (stronglyMeasurable_remainderAverage (hχm.mul hFm)).aestronglyMeasurable hGA
      (hWb.mono fun y hy _ => abs_remainderAverage_le hWb hy)
  have i12 : Integrable fun u => G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u)) +
      G u * (χ u * statePrimeWave F u) := i1.add i2
  have i123 : Integrable fun u => G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u)) +
      G u * (χ u * statePrimeWave F u) - G u * (χ u * poleWave F u) := i12.sub i3
  have i1234 : Integrable fun u => G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u)) +
      G u * (χ u * statePrimeWave F u) - G u * (χ u * poleWave F u) -
        G u * confinementWave R χ F u := i123.sub i4
  have i12345 : Integrable fun u => G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u)) +
      G u * (χ u * statePrimeWave F u) - G u * (χ u * poleWave F u) -
        G u * confinementWave R χ F u + G u * levyCommutator χ F u := i1234.add i5
  have hR : (∫ u, G u * cutForcing R χ F u) =
      (∫ u, G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u))) +
        (∫ u, G u * (χ u * statePrimeWave F u)) - (∫ u, G u * (χ u * poleWave F u)) -
        (∫ u, G u * confinementWave R χ F u) + (∫ u, G u * levyCommutator χ F u) -
        ∫ u, G u * remainderAverage (fun u => χ u * F u) u := by
    rw [← integral_add i1 i2, ← integral_sub i12 i3, ← integral_sub i123 i4,
      ← integral_add i1234 i5, ← integral_sub i12345 i6]
    congr 1; ext u; simp only [cutForcing]; ring
  have hT1 : (∫ u, G u * ((1 - 2 * gammaHardyPhaseRate 0) * (χ u * F u))) =
      (1 - 2 * gammaHardyPhaseRate 0) * ∫ u, G u * (χ u * F u) := by
    rw [← integral_const_mul]; congr 1; ext u; ring
  rw [hsplit, hsymm, hrem, hR, hT1]
  linarith [hcomm, hlevy, hE, hP1, hP2, hpole, hconf, hPw]

/-- **The cut critical state solves the logarithmic window equation** with a forcing that is
essentially bounded on `[−2A, 0]`. -/
theorem criticalState_cut_logarithmic_equation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {A : ℝ} (hA : 0 < A) :
    (∃ K : ℝ, ∀ᵐ y, y ∈ Icc (-(2 * A)) 0 → |cutForcing W₀ (wallWindowCutoff A) F y| ≤ K) ∧
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → (∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0) →
        (∫ u, G u * (wallWindowCutoff A u * F u)) + (∫ t in Ioi 0, logReferenceLevyDensity t *
            ∫ u, (G u - G (u + t)) * (wallWindowCutoff A u * F u -
              wallWindowCutoff A (u + t) * F (u + t))) =
          ∫ u, G u * cutForcing W₀ (wallWindowCutoff A) F u := by
  have hFd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC, hCe⟩ := criticalState_ae_abs_le_exp hW hthreshold hF
  exact ⟨cutForcing_bounded hFd hC hCe (abs_wallWindowCutoff_le A) (abs_wallWindowCutoff_sub_le hA),
    fun G hG hGA => cut_logarithmic_equation hFd
      (fun H hH => criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hH) hC hCe
      (measurable_wallWindowCutoff A) (abs_wallWindowCutoff_le A)
      (abs_wallWindowCutoff_sub_le hA) hG hGA⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
