import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyOperatorIsConstantOnTheInverseRootLogarithm

/-!
# Bounded profiles decreasing towards the wall lie in the energy domain

Let `G` be measurable with `0 ≤ G ≤ B`, carried by a collar `(−k, 0)` and nonincreasing on it.
No continuity is assumed: `G` may jump at `−k`, and it may have any modulus at the wall.

**Theorem** (`integral_sq_increment_le_of_antitone_collar`). For every `x > 0`,
`∫ (G(u) − G(u+x))² du ≤ 2 B² x`.

**Theorem** (`criticalHalfLineEnergyDomain_of_antitone_collar`). `G` lies in the energy domain.

Mechanism. The increment `d = G(u) − G(u+x)` is negative only for `−k−x < u ≤ −k`, where the
profile is entered from the left. Hence `d² ≤ B d + 2B² 1_{(−k−x, −k]}`, and `∫ d = 0` by
translation invariance. The Lévy density satisfies `ω(x) x ≤ 1` near the origin, so the jump
energy `∫ ω(x) ∫ d² du dx` converges: a linear modulus of the increment energy is enough, where a
Lipschitz profile has a quadratic one.

The inverse root logarithm of a collar and the ramp of a collar (`collarRamp`) are such profiles.
The cutoff Lévy operators are linear on square integrable profiles (`cutoffLevy_linear`) and
bounded below by `−4` on the ramp (`neg_four_le_cutoffLevy_collarRamp`).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The increment energy -/

theorem integrable_of_bounded_collar {G : ℝ → ℝ} {k B : ℝ} (hGm : Measurable G)
    (hG0 : ∀ u, 0 ≤ G u) (hGB : ∀ u, G u ≤ B) (hleft : ∀ u, u ≤ -k → G u = 0)
    (hright : ∀ u, 0 ≤ u → G u = 0) : Integrable G := by
  have hind : Integrable ((Ioo (-k) (0 : ℝ)).indicator fun _ : ℝ => B) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => B) (Icc (-k) 0)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  refine hind.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hG0 u)]
  by_cases hu : u ∈ Ioo (-k) (0 : ℝ)
  · rw [indicator_of_mem hu]
    exact hGB u
  · rw [indicator_of_notMem hu]
    rcases le_or_gt u (-k) with h | h
    · exact (hleft u h).le
    · exact (hright u (not_lt.mp fun h0 => hu ⟨h, h0⟩)).le

/-- **The increment energy has a linear modulus**: `∫ (G(u) − G(u+x))² du ≤ 2B² x`. -/
theorem integral_sq_increment_le_of_antitone_collar {G : ℝ → ℝ} {k B : ℝ} (hGm : Measurable G)
    (hG1 : Integrable G) (hG0 : ∀ u, 0 ≤ G u) (hGB : ∀ u, G u ≤ B)
    (hleft : ∀ u, u ≤ -k → G u = 0) (hright : ∀ u, 0 ≤ u → G u = 0)
    (hanti : ∀ u v, -k < u → u ≤ v → v < 0 → G v ≤ G u) {x : ℝ} (hx : 0 < x) :
    ∫ u, (G u - G (u + x)) ^ 2 ≤ 2 * B ^ 2 * x := by
  have hB0 : 0 ≤ B := (hG0 0).trans (hGB 0)
  have hGx : Integrable fun u => G (u + x) := hG1.comp_add_right x
  have hind : Integrable ((Ioc (-k - x) (-k)).indicator fun _ : ℝ => (1 : ℝ)) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ))
      (Icc (-k - x) (-k))).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  -- the increment is negative only where the profile is entered from the left
  have hpt : ∀ u, (G u - G (u + x)) ^ 2 ≤
      B * (G u - G (u + x)) + 2 * B ^ 2 * (Ioc (-k - x) (-k)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    have ha := hG0 u
    have hb := hG0 (u + x)
    have ha' := hGB u
    have hb' := hGB (u + x)
    have hind0 : 0 ≤ (Ioc (-k - x) (-k)).indicator (fun _ => (1 : ℝ)) u :=
      indicator_nonneg (fun _ _ => zero_le_one) u
    rcases le_or_gt 0 (G u - G (u + x)) with hd | hd
    · nlinarith only [mul_nonneg hd
        (by linarith only [ha', hb] : (0 : ℝ) ≤ B - (G u - G (u + x))),
        mul_nonneg (sq_nonneg B) hind0]
    · have hmem : u ∈ Ioc (-k - x) (-k) := by
        have hne : G (u + x) ≠ 0 := by
          intro h0
          rw [h0] at hd
          linarith only [hd, ha]
        have h1 : -k < u + x := by
          by_contra h
          exact hne (hleft _ (not_lt.mp h))
        have h2 : u + x < 0 := by
          by_contra h
          exact hne (hright _ (not_lt.mp h))
        have h3 : u ≤ -k := by
          by_contra h
          have h4 := hanti u (u + x) (not_le.mp h) (by linarith only [hx]) h2
          linarith only [h4, hd]
        exact ⟨by linarith only [h1], h3⟩
      rw [indicator_of_mem hmem]
      nlinarith only [mul_nonneg (by linarith only [ha, hb'] : (0 : ℝ) ≤ B + (G u - G (u + x)))
        (by linarith only [hd] : (0 : ℝ) ≤ -(G u - G (u + x))),
        mul_nonneg hB0 (by linarith only [ha, hb'] : (0 : ℝ) ≤ B + (G u - G (u + x)))]
  have hsum : Integrable fun u => B * (G u + G (u + x)) := (hG1.add hGx).const_mul B
  have hi1 : Integrable fun u => (G u - G (u + x)) ^ 2 := by
    refine hsum.mono'
      ((hGm.sub (hGm.comp (measurable_id.add_const x))).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [mul_nonneg (hG0 u) (sub_nonneg.mpr (hGB u)),
      mul_nonneg (hG0 (u + x)) (sub_nonneg.mpr (hGB (u + x))), mul_nonneg (hG0 u) (hG0 (u + x))]
  have hd1 : Integrable fun u => B * (G u - G (u + x)) := (hG1.sub hGx).const_mul B
  have hd2 : Integrable fun u =>
      2 * B ^ 2 * (Ioc (-k - x) (-k)).indicator (fun _ => (1 : ℝ)) u := hind.const_mul (2 * B ^ 2)
  have h : ∫ u, (G u - G (u + x)) ^ 2 ≤ ∫ u, (B * (G u - G (u + x)) +
      2 * B ^ 2 * (Ioc (-k - x) (-k)).indicator (fun _ => (1 : ℝ)) u) :=
    integral_mono hi1 (hd1.add hd2) hpt
  have e : ∫ u, (B * (G u - G (u + x)) +
      2 * B ^ 2 * (Ioc (-k - x) (-k)).indicator (fun _ => (1 : ℝ)) u) = 2 * B ^ 2 * x := by
    rw [integral_add hd1 hd2, integral_const_mul, integral_const_mul, integral_sub hG1 hGx,
      integral_add_right_eq_self G x, integral_indicator measurableSet_Ioc, setIntegral_const,
      Real.volume_real_Ioc_of_le (by linarith only [hx]), smul_eq_mul]
    ring
  exact h.trans e.le

/-- **Bounded profiles of a collar decreasing towards the wall lie in the energy domain.** -/
theorem criticalHalfLineEnergyDomain_of_antitone_collar {G : ℝ → ℝ} {k B : ℝ}
    (hGm : Measurable G) (hG0 : ∀ u, 0 ≤ G u) (hGB : ∀ u, G u ≤ B)
    (hleft : ∀ u, u ≤ -k → G u = 0) (hright : ∀ u, 0 ≤ u → G u = 0)
    (hanti : ∀ u v, -k < u → u ≤ v → v < 0 → G v ≤ G u) : CriticalHalfLineEnergyDomain G := by
  have hB0 : 0 ≤ B := (hG0 0).trans (hGB 0)
  have hG1 := integrable_of_bounded_collar hGm hG0 hGB hleft hright
  have hsq : Integrable fun u => G u ^ 2 := by
    refine (hG1.const_mul B).mono' (hGm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [mul_nonneg (hG0 u) (sub_nonneg.mpr (hGB u))]
  have hexp : Integrable fun u => G u ^ 2 * Real.exp (-(8 * u)) := by
    refine (hsq.const_mul (Real.exp (8 * k))).mono'
      ((hGm.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le), mul_comm]
    rcases le_or_gt u (-k) with h | h
    · have h0 : G u = 0 := hleft u h
      rw [h0]
      norm_num
    · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [h])) (sq_nonneg _)
  refine ⟨hGm, hG1, hsq, hexp, hright, ?_⟩
  apply integrable_gamma_of_lintegral_levy_ne_top hG1 hsq
  have hS0 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hGmem : MemLp G 2 volume := (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr hsq
  have hD : IntegrableOn
      (fun x : ℝ => (6 * B ^ 2 + 8 * ∫ u, G u ^ 2) * Real.exp (-(x / 2))) (Ioi 0) :=
    integrableOn_exp_neg_half.const_mul _
  have hle : ∀ x ∈ Ioi (0 : ℝ), archLevyDensity x * (∫ u, (G u - G (u + x)) ^ 2) ≤
      (6 * B ^ 2 + 8 * ∫ u, G u ^ 2) * Real.exp (-(x / 2)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hω := (archLevyDensity_pos hx0).le
    have he := Real.exp_pos (-(x / 2))
    have hE0 : 0 ≤ ∫ u, (G u - G (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    rcases le_total x 1 with h1 | h1
    · -- short jumps: the linear modulus against `ω(x) x ≤ 1`
      have hE := integral_sq_increment_le_of_antitone_collar hGm hG1 hG0 hGB hleft hright hanti hx0
      have hωx := archLevyDensity_mul_self_le_one hx0 (by linarith only [h1])
      have hexp2 : (1 : ℝ) / 2 ≤ Real.exp (-(x / 2)) := by
        have h := Real.add_one_le_exp (-(x / 2))
        linarith only [h, h1]
      calc archLevyDensity x * (∫ u, (G u - G (u + x)) ^ 2)
          ≤ archLevyDensity x * (2 * B ^ 2 * x) := mul_le_mul_of_nonneg_left hE hω
        _ = 2 * B ^ 2 * (archLevyDensity x * x) := by ring
        _ ≤ 2 * B ^ 2 * 1 := mul_le_mul_of_nonneg_left hωx (by positivity)
        _ ≤ (6 * B ^ 2 + 8 * ∫ u, G u ^ 2) * Real.exp (-(x / 2)) := by
            nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (sq_nonneg B))
              (sub_nonneg.mpr hexp2), mul_nonneg hS0 he.le, sq_nonneg B]
    · -- long jumps: the mass against the exponential decay of `ω`
      have hfar := archLevyDensity_le_far h1
      have hsx : Integrable fun u => G (u + x) ^ 2 := hsq.comp_add_right x
      have hshift : (∫ u, G (u + x) ^ 2) = ∫ u, G u ^ 2 :=
        integral_add_right_eq_self (fun v => G v ^ 2) x
      have hi : Integrable fun u => (G u - G (u + x)) ^ 2 :=
        integrable_sq_of_memLp (hGmem.sub (memLp_two_shift hGmem x))
      have hd1 : Integrable fun u => 2 * G u ^ 2 := hsq.const_mul 2
      have hd2 : Integrable fun u => 2 * G (u + x) ^ 2 := hsx.const_mul 2
      have h : ∫ u, (G u - G (u + x)) ^ 2 ≤ ∫ u, (2 * G u ^ 2 + 2 * G (u + x) ^ 2) :=
        integral_mono hi (hd1.add hd2) fun u => by
          show (G u - G (u + x)) ^ 2 ≤ 2 * G u ^ 2 + 2 * G (u + x) ^ 2
          nlinarith only [sq_nonneg (G u + G (u + x))]
      rw [integral_add hd1 hd2, integral_const_mul, integral_const_mul, hshift] at h
      have hE : ∫ u, (G u - G (u + x)) ^ 2 ≤ 4 * ∫ u, G u ^ 2 := by linarith only [h]
      calc archLevyDensity x * (∫ u, (G u - G (u + x)) ^ 2)
          ≤ 2 * Real.exp (-(x / 2)) * (4 * ∫ u, G u ^ 2) :=
            mul_le_mul hfar hE hE0 (by positivity)
        _ ≤ (6 * B ^ 2 + 8 * ∫ u, G u ^ 2) * Real.exp (-(x / 2)) := by
            nlinarith only [mul_nonneg (sq_nonneg B) he.le]
  have hDnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x : ℝ =>
      (6 * B ^ 2 + 8 * ∫ u, G u ^ 2) * Real.exp (-(x / 2)) :=
    Eventually.of_forall fun x => mul_nonneg
      (add_nonneg (by positivity) (mul_nonneg (by norm_num) hS0)) (Real.exp_pos _).le
  refine (lt_of_le_of_lt (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono
    fun x hx => ENNReal.ofReal_le_ofReal (hle x hx))) ?_).ne
  rw [← ofReal_integral_eq_lintegral_ofReal hD hDnn]
  exact ENNReal.ofReal_lt_top

theorem criticalHalfLineEnergyDomain_wallLogProfile {k : ℝ} (hk4 : k ≤ 1 / 4) :
    CriticalHalfLineEnergyDomain (wallLogProfile k) :=
  criticalHalfLineEnergyDomain_of_antitone_collar (measurable_wallLogProfile k)
    (wallLogProfile_nonneg k) (wallLogProfile_le_one hk4) (fun _ h => wallLogProfile_of_le h)
    (fun _ h => wallLogProfile_of_nonneg h) fun u v hu huv hv => by
      rw [wallLogProfile_of_mem hu (lt_of_le_of_lt huv hv),
        wallLogProfile_of_mem (lt_of_lt_of_le hu huv) hv]
      exact inv_wallRootLog_mono (by linarith only [hv]) (by linarith only [huv])
        (by linarith only [hu, hk4])

/-! ### The ramp of a collar -/

/-- The ramp of the collar: `0` on `[−k/4, 0)`, `1` on `(−k, −k/2]`, linear in between, and
`0` outside the collar. -/
def collarRamp (k u : ℝ) : ℝ := if -k < u ∧ u < 0 then min (max (-(4 / k * u) - 1) 0) 1 else 0

theorem collarRamp_of_mem {k u : ℝ} (h1 : -k < u) (h2 : u < 0) :
    collarRamp k u = min (max (-(4 / k * u) - 1) 0) 1 := if_pos ⟨h1, h2⟩

theorem collarRamp_of_le {k u : ℝ} (h : u ≤ -k) : collarRamp k u = 0 :=
  if_neg fun h' => absurd h'.1 (not_lt.mpr h)

theorem collarRamp_of_nonneg {k u : ℝ} (h : 0 ≤ u) : collarRamp k u = 0 :=
  if_neg fun h' => absurd h'.2 (not_lt.mpr h)

theorem measurable_collarRamp (k : ℝ) : Measurable (collarRamp k) := by
  show Measurable fun u : ℝ => if -k < u ∧ u < 0 then min (max (-(4 / k * u) - 1) 0) 1 else 0
  exact Measurable.ite (measurableSet_Ioo : MeasurableSet (Ioo (-k) (0 : ℝ)))
    ((((measurable_id.const_mul (4 / k)).neg.sub_const 1).max measurable_const).min
      measurable_const) measurable_const

theorem collarRamp_nonneg (k u : ℝ) : 0 ≤ collarRamp k u := by
  by_cases h : -k < u ∧ u < 0
  · rw [collarRamp, if_pos h]
    exact le_min (le_max_right _ _) zero_le_one
  · simp only [collarRamp, if_neg h, le_refl]

theorem collarRamp_le_one (k u : ℝ) : collarRamp k u ≤ 1 := by
  by_cases h : -k < u ∧ u < 0
  · rw [collarRamp, if_pos h]
    exact min_le_right _ _
  · simp only [collarRamp, if_neg h, zero_le_one]

theorem abs_collarRamp_le_one (k u : ℝ) : |collarRamp k u| ≤ 1 := by
  rw [abs_of_nonneg (collarRamp_nonneg k u)]
  exact collarRamp_le_one k u

/-- The ramp vanishes on the quarter of the collar next to the wall. -/
theorem collarRamp_eq_zero {k u : ℝ} (hk : 0 < k) (h1 : -(k / 4) ≤ u) (h2 : u < 0) :
    collarRamp k u = 0 := by
  have e : 4 / k * (k / 4) = 1 := by
    rw [div_mul_div_comm, mul_comm 4 k, div_self (by positivity)]
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 / k)
  rw [mul_neg, e] at h3
  rw [collarRamp_of_mem (by linarith only [h1, hk]) h2,
    max_eq_right (by linarith only [h3]), min_eq_left zero_le_one]

/-- The ramp equals one on the outer half of the collar. -/
theorem collarRamp_eq_one {k u : ℝ} (hk : 0 < k) (h1 : -k < u) (h2 : u ≤ -(k / 2)) :
    collarRamp k u = 1 := by
  have e : 4 / k * (k / 2) = 2 := by
    rw [div_mul_div_comm, div_eq_iff (by positivity)]
    ring
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 / k)
  rw [mul_neg, e] at h3
  have h4 : (1 : ℝ) ≤ -(4 / k * u) - 1 := by linarith only [h3]
  rw [collarRamp_of_mem h1 (by linarith only [h2, hk]),
    max_eq_left (le_trans zero_le_one h4), min_eq_right h4]

theorem collarRamp_anti {k u v : ℝ} (hk : 0 < k) (hu : -k < u) (huv : u ≤ v) (hv : v < 0) :
    collarRamp k v ≤ collarRamp k u := by
  have h3 := mul_le_mul_of_nonneg_left huv (by positivity : (0 : ℝ) ≤ 4 / k)
  rw [collarRamp_of_mem (lt_of_lt_of_le hu huv) hv, collarRamp_of_mem hu (lt_of_le_of_lt huv hv)]
  exact min_le_min (max_le_max (by linarith only [h3]) le_rfl) le_rfl

theorem collarRamp_sub_le {k u v : ℝ} (hk : 0 < k) (hu : -k < u) (hu0 : u < 0) (hv : -k < v)
    (hv0 : v < 0) : collarRamp k u - collarRamp k v ≤ 4 / k * |u - v| := by
  have h4k : 0 < 4 / k := by positivity
  rw [collarRamp_of_mem hu hu0, collarRamp_of_mem hv hv0]
  calc min (max (-(4 / k * u) - 1) 0) 1 - min (max (-(4 / k * v) - 1) 0) 1
      ≤ |min (max (-(4 / k * u) - 1) 0) 1 - min (max (-(4 / k * v) - 1) 0) 1| := le_abs_self _
    _ ≤ max |max (-(4 / k * u) - 1) 0 - max (-(4 / k * v) - 1) 0| |(1 : ℝ) - 1| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = |max (-(4 / k * u) - 1) 0 - max (-(4 / k * v) - 1) 0| := by
        rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    _ ≤ |-(4 / k * u) - 1 - (-(4 / k * v) - 1)| := abs_max_sub_max_le_abs _ _ _
    _ = 4 / k * |u - v| := by
        rw [show -(4 / k * u) - 1 - (-(4 / k * v) - 1) = -(4 / k) * (u - v) by ring, abs_mul,
          abs_neg, abs_of_pos h4k]

theorem criticalHalfLineEnergyDomain_collarRamp {k : ℝ} (hk : 0 < k) :
    CriticalHalfLineEnergyDomain (collarRamp k) :=
  criticalHalfLineEnergyDomain_of_antitone_collar (measurable_collarRamp k)
    (collarRamp_nonneg k) (collarRamp_le_one k) (fun _ h => collarRamp_of_le h)
    (fun _ h => collarRamp_of_nonneg h) fun _ _ hu huv hv => collarRamp_anti hk hu huv hv

/-! ### The cutoff operators on the barrier pieces -/

/-- The cutoff Lévy operator is linear on square integrable profiles. -/
theorem cutoffLevy_linear {δ : ℝ} (hδ : 0 < δ) {X Y : ℝ → ℝ} (hXm : Measurable X)
    (hX2 : Integrable fun u => X u ^ 2) (hYm : Measurable Y) (hY2 : Integrable fun u => Y u ^ 2)
    (a b u : ℝ) :
    cutoffLevy δ (fun v => a * X v + b * Y v) u = a * cutoffLevy δ X u + b * cutoffLevy δ Y u := by
  have hX := (integrable_symCutoffKernel_mul_translate hδ hXm hX2 u).const_mul a
  have hY := (integrable_symCutoffKernel_mul_translate hδ hYm hY2 u).const_mul b
  have e : lineConvolution (symCutoffKernel δ) (fun v => a * X v + b * Y v) u =
      a * lineConvolution (symCutoffKernel δ) X u + b * lineConvolution (symCutoffKernel δ) Y u := by
    unfold lineConvolution
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hX hY]
    exact integral_congr_ae (Eventually.of_forall fun s => by dsimp only; ring)
  unfold cutoffLevy
  rw [e]
  ring

/-- **The ramp costs at most `4`.** Left of the wall the cutoff operator of the ramp is bounded
below: the ramp increases away from the wall with slope `4/k`, and `ω(h) h ≤ 1`. -/
theorem neg_four_le_cutoffLevy_collarRamp {k δ t : ℝ} (hk2 : k ≤ 2) (hδ : 0 < δ) (hδt : δ ≤ t)
    (htk : t < k) : -4 ≤ cutoffLevy δ (collarRamp k) (-t) := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  have hk : 0 < k := lt_trans ht htk
  have hδk : δ ≤ k := by linarith only [hδt, htk]
  rw [cutoffLevy_eq_rows hδ (measurable_collarRamp k) (abs_collarRamp_le_one k) (-t)]
  -- towards the wall the ramp decreases
  have hin : 0 ≤ ∫ h in Ioi δ, archLevyDensity h *
      (collarRamp k (-t) - collarRamp k (-t + h)) := by
    refine setIntegral_nonneg measurableSet_Ioi fun h hh => ?_
    have hh0 : 0 < h := lt_trans hδ hh
    refine mul_nonneg (archLevyDensity_pos hh0).le (sub_nonneg.mpr ?_)
    rcases le_or_gt 0 (-t + h) with h0 | h0
    · rw [collarRamp_of_nonneg h0]
      exact collarRamp_nonneg k _
    · exact collarRamp_anti hk (by linarith only [htk]) (by linarith only [hh0]) h0
  have hm : Measurable fun h : ℝ => collarRamp k (-t) - collarRamp k (-t - h) :=
    measurable_const.sub ((measurable_collarRamp k).comp (measurable_const.sub measurable_id))
  have hint : IntegrableOn
      (fun h : ℝ => archLevyDensity h * (collarRamp k (-t) - collarRamp k (-t - h))) (Ioi δ) :=
    integrableOn_archLevyDensity_mul_of_bounded hδ hm (B := 1) fun h =>
      abs_le.mpr ⟨by linarith only [collarRamp_nonneg k (-t), collarRamp_le_one k (-t - h)],
        by linarith only [collarRamp_le_one k (-t), collarRamp_nonneg k (-t - h)]⟩
  have hint' := hint.mono_set (Ioi_subset_Ioi hδk)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint hint'
  have hfar : 0 ≤ ∫ h in Ioi k, archLevyDensity h *
      (collarRamp k (-t) - collarRamp k (-t - h)) := by
    refine setIntegral_nonneg measurableSet_Ioi fun h hh => ?_
    have hh' : k < h := hh
    rw [collarRamp_of_le (by linarith only [hh', ht] : -t - h ≤ -k), sub_zero]
    exact mul_nonneg (archLevyDensity_pos (lt_trans hk hh')).le (collarRamp_nonneg k _)
  have hni : IntervalIntegrable
      (fun h : ℝ => archLevyDensity h * (collarRamp k (-t) - collarRamp k (-t - h))) volume δ k :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδk).mpr (hint.mono_set Ioc_subset_Ioi_self)
  have hpt : ∀ h ∈ Icc δ k,
      -(4 / k) ≤ archLevyDensity h * (collarRamp k (-t) - collarRamp k (-t - h)) := by
    intro h hh
    have hh0 : 0 < h := lt_of_lt_of_le hδ hh.1
    have hω0 := (archLevyDensity_pos hh0).le
    have hωh := archLevyDensity_mul_self_le_one hh0 (by linarith only [hh.2, hk2])
    have h4k : (0 : ℝ) ≤ 4 / k := by positivity
    rcases le_or_gt (-t - h) (-k) with hout | hins
    · rw [collarRamp_of_le hout, sub_zero]
      have h0 := mul_nonneg hω0 (collarRamp_nonneg k (-t))
      linarith only [h0, h4k]
    · have hl := collarRamp_sub_le hk hins (by linarith only [ht, hh0]) (by linarith only [htk])
        (by linarith only [ht] : -t < 0)
      rw [show -t - h - -t = -h by ring, abs_neg, abs_of_pos hh0] at hl
      have h3 : archLevyDensity h * (-(4 / k * h)) ≤
          archLevyDensity h * (collarRamp k (-t) - collarRamp k (-t - h)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hl]) hω0
      have h4 : archLevyDensity h * h * (4 / k) ≤ 1 * (4 / k) :=
        mul_le_mul_of_nonneg_right hωh h4k
      have e3 : archLevyDensity h * (-(4 / k * h)) = -(archLevyDensity h * h * (4 / k)) := by ring
      linarith only [h3, h4, e3]
  have hnear : -4 ≤ ∫ h in δ..k, archLevyDensity h *
      (collarRamp k (-t) - collarRamp k (-t - h)) := by
    have h1 := intervalIntegral.integral_mono_on hδk
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -(4 / k)) volume δ k) hni hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have e1 : k * (4 / k) = 4 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hk.ne']
    have e2 : (k - δ) * -(4 / k) = -(k * (4 / k)) + δ * (4 / k) := by ring
    have h0 : 0 ≤ δ * (4 / k) := by positivity
    linarith only [h1, e1, e2, h0]
  rw [← hsplit]
  linarith only [hin, hnear, hfar]

end GaloisForLFunctions.ExclusionOfTheCriticalState
