import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeHeadHasAnAveragedLeadingTerm
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers

/-!
# Singular profiles: the prime head has no leading term on the whole energy domain

The leading term of `t · ŜF(−t)` is an Abel mean of the right averages of `F` at the prime points
(`mul_primeHead_neg_eq_integral`). Point values at `−log n` are not part of the energy domain `H`, and
the leading term need not exist.

**The profiles.** For `0 ≤ α < ½`, `F_α(u) = (u + log 2)^{−α}` for `u + log 2 ∈ (0, 1/4]`, zero elsewhere
(`singularProfile α`): singular from the right at the prime point `−log 2`, supported in `u < 0`.

* `F_α ∈ H` (`criticalHalfLineEnergyDomain_singularProfile`). The Gamma condition comes from the jump
  energy `∫_{x>0} ω(x) ∫ (F(u) − F(u+x))² du dx`. With `g` nonincreasing on `(0, ∞)`, the shift difference
  is split at `0` and `x`: `∫ (g(v) − g(v+x))² ≤ 2∫_0^x g² + x g(x)² ≤ (2/(1−2α) + 1) x^{1−2α}` for
  `x ≤ 1/4`, while `ω(x) ≤ 1/x` near `0` and `ω(x) ≤ 3e^{−x/2}` away from it.
* `‖t · ŜF_α(−t)‖ ≥ c t^α` (`mul_rpow_le_norm_mul_primeHead_neg_singularProfile`): every Abel integral is
  nonnegative, and the one at `−log 2` is `≥ e^{−1} t^{α−1}/(1−α)`.

Consequences. Some profile of `H` has no limit of `t · ŜF(−t)`
(`exists_profile_without_primeHead_limit`), so a leading term needs a hypothesis on the
prime-averaged profile (`tendsto_mul_primeHead_neg_of_primeAveragedProfile`). The unconditional bound
`‖t · ŜF(−t)‖ = o(t^{1/2})` for every `F ∈ H` (`tendsto_sqrt_mul_primeHead_neg`) is sharp: every exponent
`α < ½` is attained (`primeHead_neg_growth_exponent_half_is_sharp`).
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem atom_nonneg_sg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem vonMangoldtAtom_two_pos : 0 < vonMangoldtAtom 2 := by
  unfold vonMangoldtAtom
  rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- The base profile `g_α(v) = v^{−α}` on `(0, 1/4]`, zero elsewhere. -/
def singularBase (α : ℝ) : ℝ → ℝ := (Ioc (0 : ℝ) (1 / 4)).indicator fun v => v ^ (-α)

/-- The profile `F_α(u) = g_α(u + log 2)`, singular from the right at the prime point `−log 2`. -/
def singularProfile (α : ℝ) (u : ℝ) : ℝ := singularBase α (u + Real.log 2)

/-! ### The base profile -/

section Base

variable {α : ℝ}

theorem singularBase_of_mem {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) (1 / 4)) :
    singularBase α v = v ^ (-α) := by
  unfold singularBase; rw [Set.indicator_apply, if_pos hv]

theorem singularBase_of_not_mem {v : ℝ} (hv : v ∉ Ioc (0 : ℝ) (1 / 4)) : singularBase α v = 0 := by
  unfold singularBase; rw [Set.indicator_apply, if_neg hv]

theorem singularBase_nonneg (v : ℝ) : 0 ≤ singularBase α v := by
  by_cases hv : v ∈ Ioc (0 : ℝ) (1 / 4)
  · rw [singularBase_of_mem hv]; exact Real.rpow_nonneg hv.1.le _
  · rw [singularBase_of_not_mem hv]

theorem singularBase_le {v : ℝ} (hv : 0 < v) : singularBase α v ≤ v ^ (-α) := by
  by_cases h : v ∈ Ioc (0 : ℝ) (1 / 4)
  · rw [singularBase_of_mem h]
  · rw [singularBase_of_not_mem h]; exact Real.rpow_nonneg hv.le _

theorem singularBase_eq_zero_of_nonpos {v : ℝ} (hv : v ≤ 0) : singularBase α v = 0 :=
  singularBase_of_not_mem fun h => absurd h.1 (not_lt.mpr hv)

/-- `g_α` is nonincreasing on `(0, ∞)`. -/
theorem singularBase_anti (hα0 : 0 ≤ α) {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) :
    singularBase α w ≤ singularBase α v := by
  by_cases hw : w ∈ Ioc (0 : ℝ) (1 / 4)
  · rw [singularBase_of_mem hw, singularBase_of_mem ⟨hv, hvw.trans hw.2⟩]
    exact Real.rpow_le_rpow_of_nonpos hv hvw (by linarith)
  · rw [singularBase_of_not_mem hw]; exact singularBase_nonneg v

theorem sq_singularBase (v : ℝ) :
    singularBase α v ^ 2 = (Ioc (0 : ℝ) (1 / 4)).indicator (fun v => v ^ (-(2 * α))) v := by
  by_cases hv : v ∈ Ioc (0 : ℝ) (1 / 4)
  · rw [singularBase_of_mem hv, Set.indicator_apply, if_pos hv, ← Real.rpow_natCast,
      ← Real.rpow_mul hv.1.le]
    congr 1; push_cast; ring
  · rw [singularBase_of_not_mem hv, Set.indicator_apply, if_neg hv]; norm_num

theorem integrableOn_rpow_Ioc {r : ℝ} (hr : -1 < r) (b : ℝ) :
    IntegrableOn (fun v : ℝ => v ^ r) (Ioc 0 b) :=
  (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) hr).1

theorem measurable_singularBase : Measurable (singularBase α) :=
  (by fun_prop : Measurable fun v : ℝ => v ^ (-α)).indicator measurableSet_Ioc

theorem integrable_singularBase (hα : α < 1 / 2) : Integrable (singularBase α) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_rpow_Ioc (by linarith) _)

theorem integrable_sq_singularBase (hα : α < 1 / 2) :
    Integrable fun v => singularBase α v ^ 2 := by
  simp_rw [sq_singularBase]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_rpow_Ioc (by linarith) _)

theorem rpow_neg_sq {x : ℝ} (hx : 0 < x) : (x ^ (-α)) ^ 2 = x ^ (-(2 * α)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring

theorem mul_rpow_neg_two {x : ℝ} (hx : 0 < x) : x * x ^ (-(2 * α)) = x ^ (1 - 2 * α) := by
  have h := Real.rpow_add hx (1 : ℝ) (-(2 * α))
  rw [Real.rpow_one] at h
  rw [← h, sub_eq_add_neg]

/-- `∫_0^x g_α² = x^{1−2α}/(1−2α)` for `x ≤ 1/4`. -/
theorem integral_sq_singularBase_Ioc (hα : α < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    ∫ v in Ioc 0 x, singularBase α v ^ 2 = x ^ (1 - 2 * α) / (1 - 2 * α) := by
  have e : ∀ v ∈ Ioc 0 x, singularBase α v ^ 2 = v ^ (-(2 * α)) := fun v hv => by
    rw [sq_singularBase, Set.indicator_apply, if_pos ⟨hv.1, hv.2.trans hx⟩]
  rw [setIntegral_congr_fun measurableSet_Ioc e, ← intervalIntegral.integral_of_le hx0,
    integral_rpow (Or.inl (by linarith)), show -(2 * α) + 1 = 1 - 2 * α by ring,
    Real.zero_rpow (by linarith : (0 : ℝ) < 1 - 2 * α).ne', sub_zero]

theorem integrable_sq_sub_shift (hα : α < 1 / 2) (x : ℝ) :
    Integrable fun v => (singularBase α v - singularBase α (v + x)) ^ 2 := by
  have hg2 := integrable_sq_singularBase hα
  refine ((hg2.add (hg2.comp_add_right x)).const_mul 2).mono'
    ((measurable_singularBase.sub (measurable_singularBase.comp (measurable_add_const x))).pow_const
      2).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show _ ≤ 2 * (singularBase α v ^ 2 + singularBase α (v + x) ^ 2)
  nlinarith [sq_nonneg (singularBase α v + singularBase α (v + x))]

theorem integral_sq_sub_shift_le_four (hα : α < 1 / 2) (x : ℝ) :
    ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2 ≤ 4 * ∫ v, singularBase α v ^ 2 := by
  have hg2 := integrable_sq_singularBase hα
  have hgx2 : Integrable fun v => singularBase α (v + x) ^ 2 := hg2.comp_add_right x
  calc ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2
      ≤ ∫ v, 2 * (singularBase α v ^ 2 + singularBase α (v + x) ^ 2) :=
        integral_mono (integrable_sq_sub_shift hα x) ((hg2.add hgx2).const_mul 2) fun v => by
          nlinarith [sq_nonneg (singularBase α v + singularBase α (v + x))]
    _ = 4 * ∫ v, singularBase α v ^ 2 := by
        rw [integral_const_mul, integral_add hg2 hgx2,
          integral_add_right_eq_self (fun v => singularBase α v ^ 2) x]
        ring

/-- **The shift difference of `g_α` is `O(x^{1−2α})`.** Split at `0` and `x`: left of `x` the difference is
at most the larger value, right of `x` it is at most `g(x)` times the nonnegative difference, whose
integral telescopes to `∫_x^{2x} g`. -/
theorem integral_sq_sub_shift_le (hα0 : 0 ≤ α) (hα : α < 1 / 2) {x : ℝ} (hx : 0 < x)
    (hx4 : x ≤ 1 / 4) :
    ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2 ≤
      (2 / (1 - 2 * α) + 1) * x ^ (1 - 2 * α) := by
  have hg1 := integrable_singularBase hα
  have hg2 := integrable_sq_singularBase hα
  have hgx1 : Integrable fun v => singularBase α (v + x) := hg1.comp_add_right x
  have hgx2 : Integrable fun v => singularBase α (v + x) ^ 2 := hg2.comp_add_right x
  obtain ⟨m1, hm1⟩ : ∃ m : ℝ → ℝ,
      m = (Ioc (-x) 0).indicator fun v => singularBase α (v + x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m : ℝ → ℝ, m = (Ioc 0 x).indicator fun v => singularBase α v ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m : ℝ → ℝ, m = (Ioi x).indicator fun v =>
      singularBase α x * (singularBase α v - singularBase α (v + x)) := ⟨_, rfl⟩
  have i1 : Integrable m1 := by rw [hm1]; exact hgx2.indicator measurableSet_Ioc
  have i2 : Integrable m2 := by rw [hm2]; exact hg2.indicator measurableSet_Ioc
  have i3 : Integrable m3 := by
    rw [hm3]; exact ((hg1.sub hgx1).const_mul _).indicator measurableSet_Ioi
  have i12 : Integrable fun v => m1 v + m2 v := i1.add i2
  -- the pointwise majorant
  have hpt : ∀ v, (singularBase α v - singularBase α (v + x)) ^ 2 ≤ m1 v + m2 v + m3 v := by
    intro v
    simp only [hm1, hm2, hm3, Set.indicator_apply, mem_Ioc, mem_Ioi]
    rcases le_or_gt v (-x) with h1 | h1
    · rw [singularBase_eq_zero_of_nonpos (by linarith : v ≤ 0),
        singularBase_eq_zero_of_nonpos (by linarith : v + x ≤ 0)]
      simp
    rcases le_or_gt v 0 with h2 | h2
    · have n2 : ¬ (0 < v ∧ v ≤ x) := fun h => by linarith [h.1]
      rw [if_pos ⟨h1, h2⟩, if_neg n2, if_neg (not_lt.mpr (by linarith)),
        singularBase_eq_zero_of_nonpos h2]
      nlinarith [sq_nonneg (singularBase α (v + x))]
    have n1 : ¬ (-x < v ∧ v ≤ 0) := fun h => by linarith [h.2]
    have hb0 := singularBase_nonneg (α := α) (v + x)
    have hba := singularBase_anti hα0 h2 (by linarith : v ≤ v + x)
    rcases le_or_gt v x with h3 | h3
    · rw [if_neg n1, if_pos ⟨h2, h3⟩, if_neg (not_lt.mpr h3)]
      nlinarith [mul_le_mul_of_nonneg_left hba hb0]
    · have n2 : ¬ (0 < v ∧ v ≤ x) := fun h => by linarith [h.2]
      have hax := singularBase_anti hα0 hx h3.le
      rw [if_neg n1, if_neg n2, if_pos h3]
      nlinarith [mul_le_mul_of_nonneg_right
        (show singularBase α v - singularBase α (v + x) ≤ singularBase α x by linarith)
        (show 0 ≤ singularBase α v - singularBase α (v + x) by linarith)]
  -- the three integrals
  have I1 : ∫ v, m1 v = ∫ v in Ioc 0 x, singularBase α v ^ 2 := by
    have e1 : ∀ v, m1 v = (Ioc 0 x).indicator (fun w => singularBase α w ^ 2) (v + x) :=
      fun v => by
        rw [hm1]
        simp only [Set.indicator_apply, mem_Ioc]
        by_cases h : -x < v ∧ v ≤ 0
        · rw [if_pos h, if_pos (⟨by linarith [h.1], by linarith [h.2]⟩ : 0 < v + x ∧ v + x ≤ x)]
        · rw [if_neg h, if_neg (fun h' : 0 < v + x ∧ v + x ≤ x =>
            h ⟨by linarith [h'.1], by linarith [h'.2]⟩)]
    simp_rw [e1]
    rw [integral_add_right_eq_self ((Ioc 0 x).indicator fun w => singularBase α w ^ 2) x,
      integral_indicator measurableSet_Ioc]
  have I2 : ∫ v, m2 v = ∫ v in Ioc 0 x, singularBase α v ^ 2 := by
    rw [hm2, integral_indicator measurableSet_Ioc]
  have I3 : ∫ v, m3 v ≤ x ^ (1 - 2 * α) := by
    -- the shifted tail
    have T : ∫ v in Ioi x, singularBase α (v + x) = ∫ v in Ioi (x + x), singularBase α v := by
      have e3 : ∀ v, (Ioi x).indicator (fun v => singularBase α (v + x)) v =
          (Ioi (x + x)).indicator (singularBase α) (v + x) := fun v => by
        simp only [Set.indicator_apply, mem_Ioi]
        by_cases h : x < v
        · rw [if_pos h, if_pos (by linarith : x + x < v + x)]
        · rw [if_neg h, if_neg (fun h' : x + x < v + x => h (by linarith))]
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
      simp_rw [e3]
      exact integral_add_right_eq_self ((Ioi (x + x)).indicator (singularBase α)) x
    have U : ∫ v in Ioi x, singularBase α v =
        (∫ v in Ioc x (x + x), singularBase α v) + ∫ v in Ioi (x + x), singularBase α v := by
      have hdisj : Disjoint (Ioc x (x + x)) (Ioi (x + x)) :=
        Set.disjoint_left.mpr fun v hv1 hv2 => (not_lt.mpr hv1.2) hv2
      have h := setIntegral_union (μ := volume) (f := singularBase α) hdisj measurableSet_Ioi
        hg1.integrableOn hg1.integrableOn
      rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at h
      exact h
    have hIoc : ∫ v in Ioc x (x + x), singularBase α v ≤ x * singularBase α x := by
      calc ∫ v in Ioc x (x + x), singularBase α v ≤ ∫ _ in Ioc x (x + x), singularBase α x :=
            setIntegral_mono_on hg1.integrableOn continuous_const.integrableOn_Ioc
              measurableSet_Ioc fun v hv => singularBase_anti hα0 hx hv.1.le
        _ = x * singularBase α x := by
            rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const,
              smul_eq_mul]
            ring
    have hsq : singularBase α x ^ 2 ≤ x ^ (-(2 * α)) := by
      rw [← rpow_neg_sq hx]
      nlinarith [singularBase_nonneg (α := α) x, singularBase_le (α := α) hx]
    rw [hm3, integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_sub hg1.integrableOn hgx1.integrableOn, T, U, add_sub_cancel_right]
    calc singularBase α x * ∫ v in Ioc x (x + x), singularBase α v
        ≤ singularBase α x * (x * singularBase α x) :=
          mul_le_mul_of_nonneg_left hIoc (singularBase_nonneg x)
      _ = x * singularBase α x ^ 2 := by ring
      _ ≤ x * x ^ (-(2 * α)) := mul_le_mul_of_nonneg_left hsq hx.le
      _ = x ^ (1 - 2 * α) := mul_rpow_neg_two hx
  have hIoc2 := integral_sq_singularBase_Ioc hα hx.le hx4
  calc ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2 ≤ ∫ v, (m1 v + m2 v + m3 v) :=
        integral_mono (integrable_sq_sub_shift hα x) (i12.add i3) hpt
    _ = (∫ v, m1 v) + (∫ v, m2 v) + ∫ v, m3 v := by rw [integral_add i12 i3, integral_add i1 i2]
    _ ≤ x ^ (1 - 2 * α) / (1 - 2 * α) + x ^ (1 - 2 * α) / (1 - 2 * α) + x ^ (1 - 2 * α) := by
        rw [I1, I2, hIoc2]; linarith
    _ = (2 / (1 - 2 * α) + 1) * x ^ (1 - 2 * α) := by ring

end Base

/-! ### The Lévy density -/

theorem archLevyDensity_le_inv {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 1 / 2) :
    archLevyDensity x ≤ 1 / x := by
  unfold archLevyDensity
  have he : Real.exp (-2 * x) * (1 + 2 * x) ≤ 1 := by
    have h1 := Real.add_one_le_exp (2 * x)
    have h2 : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-2 * x)).le]
  have hden : x ≤ 1 - Real.exp (-2 * x) := by
    nlinarith [mul_nonneg hx.le (by linarith : (0 : ℝ) ≤ 1 - 2 * x), Real.exp_pos (-2 * x)]
  have hhalf : Real.exp (-x / 2) ≤ 1 :=
    (Real.exp_le_exp.mpr (by linarith : -x / 2 ≤ 0)).trans_eq Real.exp_zero
  rw [div_le_div_iff₀ (by linarith) hx]
  nlinarith [mul_le_mul_of_nonneg_right hhalf hx.le]

theorem archLevyDensity_le_exp {x : ℝ} (hx : 1 / 4 < x) :
    archLevyDensity x ≤ 3 * Real.exp (-(x / 2)) := by
  unfold archLevyDensity
  have h1 : Real.exp (-2 * x) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(1 / 2)) ≤ 2 / 3 := by
    have h3 := Real.add_one_le_exp (1 / 2)
    have h4 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(1 / 2))).le]
  rw [neg_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) / 3 ≤ 1 - Real.exp (-2 * x) by linarith)
    (Real.exp_pos (-(x / 2))).le]

/-! ### The profile lies in the energy domain -/

section Profile

variable {α : ℝ}

theorem measurable_singularProfile : Measurable (singularProfile α) :=
  measurable_singularBase.comp (measurable_add_const _)

theorem singularProfile_nonneg (u : ℝ) : 0 ≤ singularProfile α u := singularBase_nonneg _

theorem integral_sq_sub_shift_singularProfile (x : ℝ) :
    ∫ u, (singularProfile α u - singularProfile α (u + x)) ^ 2 =
      ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2 := by
  show ∫ u, (singularBase α (u + Real.log 2) - singularBase α (u + x + Real.log 2)) ^ 2 = _
  simp_rw [show ∀ u, u + x + Real.log 2 = u + Real.log 2 + x from fun u => by ring]
  exact integral_add_right_eq_self (fun v => (singularBase α v - singularBase α (v + x)) ^ 2) _

/-- **Finite jump energy.** -/
theorem integrableOn_levy_singularProfile (hα0 : 0 ≤ α) (hα : α < 1 / 2) :
    IntegrableOn (fun x => archLevyDensity x *
      ∫ u, (singularProfile α u - singularProfile α (u + x)) ^ 2) (Ioi 0) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c, c = ∫ v, singularBase α v ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c₀ := by rw [hc₀]; exact integral_nonneg fun v => sq_nonneg _
  have hJ0 : ∀ x, 0 ≤ ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2 :=
    fun x => integral_nonneg fun v => sq_nonneg _
  have hmaj : IntegrableOn (fun x => (Ioc (0 : ℝ) (1 / 4)).indicator
      (fun x => (2 / (1 - 2 * α) + 1) * x ^ (-(2 * α))) x + 12 * c₀ * Real.exp (-(x / 2)))
      (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr
      ((integrableOn_rpow_Ioc (by linarith) _).const_mul _)).integrableOn.add
      (integrableOn_exp_neg_half.const_mul _)
  have hjm : Measurable fun p : ℝ × ℝ =>
      (singularProfile α p.2 - singularProfile α (p.2 + p.1)) ^ 2 :=
    ((measurable_singularProfile.comp measurable_snd).sub
      (measurable_singularProfile.comp (measurable_snd.add measurable_fst))).pow_const 2
  refine hmaj.mono' (measurable_archLevyDensity.aestronglyMeasurable.mul
    hjm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable).restrict
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
  have hx0 : (0 : ℝ) < x := hx
  rw [integral_sq_sub_shift_singularProfile, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (archLevyDensity_pos hx0).le (hJ0 x))]
  rcases le_or_gt x (1 / 4) with h | h
  · rw [Set.indicator_apply, if_pos ⟨hx0, h⟩]
    calc archLevyDensity x * ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2
        ≤ 1 / x * ((2 / (1 - 2 * α) + 1) * x ^ (1 - 2 * α)) :=
          mul_le_mul (archLevyDensity_le_inv hx0 (by linarith))
            (integral_sq_sub_shift_le hα0 hα hx0 h) (hJ0 x) (one_div_pos.mpr hx0).le
      _ = (2 / (1 - 2 * α) + 1) * (1 / x * (x * x ^ (-(2 * α)))) := by
          rw [mul_rpow_neg_two hx0]; ring
      _ = (2 / (1 - 2 * α) + 1) * x ^ (-(2 * α)) := by
          rw [← mul_assoc (1 / x), one_div_mul_cancel hx0.ne', one_mul]
      _ ≤ (2 / (1 - 2 * α) + 1) * x ^ (-(2 * α)) + 12 * c₀ * Real.exp (-(x / 2)) :=
          le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hc0) (Real.exp_pos _).le)
  · rw [Set.indicator_apply, if_neg (fun h' => by linarith [h'.2]), zero_add]
    have h4 : ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2 ≤ 4 * c₀ := by
      rw [hc₀]; exact integral_sq_sub_shift_le_four hα x
    calc archLevyDensity x * ∫ v, (singularBase α v - singularBase α (v + x)) ^ 2
        ≤ 3 * Real.exp (-(x / 2)) * (4 * c₀) :=
          mul_le_mul (archLevyDensity_le_exp h) h4 (hJ0 x) (by positivity)
      _ = 12 * c₀ * Real.exp (-(x / 2)) := by ring

/-- **The singular profile lies in the energy domain.** -/
theorem criticalHalfLineEnergyDomain_singularProfile (hα0 : 0 ≤ α) (hα : α < 1 / 2) :
    CriticalHalfLineEnergyDomain (singularProfile α) := by
  have h1 : Integrable (singularProfile α) := (integrable_singularBase hα).comp_add_right _
  have h2 : Integrable fun u => singularProfile α u ^ 2 :=
    (integrable_sq_singularBase hα).comp_add_right (Real.log 2)
  have hlog : 1 / 4 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  refine ⟨measurable_singularProfile, h1, h2, ?_,
    fun u hu => singularBase_of_not_mem fun h => by linarith [h.2], ?_⟩
  · refine (h2.const_mul (Real.exp (8 * Real.log 2))).mono'
      ((measurable_singularProfile.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    by_cases h : u + Real.log 2 ∈ Ioc (0 : ℝ) (1 / 4)
    · have he : Real.exp (-(8 * u)) ≤ Real.exp (8 * Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith [h.1])
      nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg (singularProfile α u))]
    · have h0 : singularProfile α u = 0 := singularBase_of_not_mem h
      rw [h0]; simp
  · exact integrable_gamma_of_lintegral_levy_ne_top h1 h2
      (integrableOn_levy_singularProfile hα0 hα).lintegral_lt_top.ne

/-! ### Growth of the prime head -/

theorem abelHead_singularProfile_two (t : ℝ) :
    abelHead (singularProfile α) t (Real.log 2) =
      ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * singularBase α v := by
  rw [abelHead_eq_shift]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [singularProfile, sub_add_cancel]

/-- The Abel integral at `−log 2` is at least `e^{−1} t^{α−1}/(1 − α)`. -/
theorem mul_abelHead_singularProfile_ge (hα : α < 1 / 2) {t : ℝ} (ht : 4 ≤ t) :
    Real.exp (-1) / (1 - α) * t ^ α ≤ t * abelHead (singularProfile α) t (Real.log 2) := by
  have htpos : 0 < t := by linarith
  have hti : 0 < 1 / t := one_div_pos.mpr htpos
  have hti4 : 1 / t ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) ht
  rw [abelHead_singularProfile_two]
  have hint : IntegrableOn (fun v => Real.exp (-(t * v)) * singularBase α v) (Ioi 0) := by
    refine (integrable_singularBase hα).integrableOn.mono'
      (((by fun_prop : Measurable fun v : ℝ => Real.exp (-(t * v))).mul
        measurable_singularBase).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (singularBase_nonneg v)]
    exact mul_le_of_le_one_left (singularBase_nonneg v) ((Real.exp_le_exp.mpr
      (by nlinarith [mul_pos htpos (show (0 : ℝ) < v from hv)] : -(t * v) ≤ 0)).trans_eq
        Real.exp_zero)
  have hsub : Real.exp (-1) * ((1 / t) ^ (1 - α) / (1 - α)) ≤
      ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * singularBase α v := by
    have hval : ∫ v in Ioc 0 (1 / t), Real.exp (-1) * v ^ (-α) =
        Real.exp (-1) * ((1 / t) ^ (1 - α) / (1 - α)) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hti.le,
        integral_rpow (Or.inl (by linarith)), show -α + 1 = 1 - α by ring,
        Real.zero_rpow (by linarith : (0 : ℝ) < 1 - α).ne', sub_zero]
    rw [← hval]
    calc ∫ v in Ioc 0 (1 / t), Real.exp (-1) * v ^ (-α)
        ≤ ∫ v in Ioc 0 (1 / t), Real.exp (-(t * v)) * singularBase α v := by
          refine setIntegral_mono_on ((integrableOn_rpow_Ioc (by linarith) _).const_mul _)
            (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun v hv => ?_
          rw [singularBase_of_mem ⟨hv.1, hv.2.trans hti4⟩]
          have htv : t * v ≤ 1 := by
            have := mul_le_mul_of_nonneg_left hv.2 htpos.le
            rwa [mul_one_div_cancel htpos.ne'] at this
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
            (Real.rpow_nonneg hv.1.le _)
      _ ≤ ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * singularBase α v :=
          setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun v _ => mul_nonneg (Real.exp_pos _).le (singularBase_nonneg v)))
            Ioc_subset_Ioi_self.eventuallyLE
  have key : t * (1 / t) ^ (1 - α) = t ^ α := by
    rw [one_div, Real.inv_rpow htpos.le, ← div_eq_mul_inv,
      div_eq_iff (Real.rpow_pos_of_pos htpos _).ne', ← Real.rpow_add htpos,
      show α + (1 - α) = (1 : ℝ) by ring, Real.rpow_one]
  calc Real.exp (-1) / (1 - α) * t ^ α
      = t * (Real.exp (-1) * ((1 / t) ^ (1 - α) / (1 - α))) := by rw [← key]; ring
    _ ≤ t * ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * singularBase α v :=
        mul_le_mul_of_nonneg_left hsub htpos.le

theorem abelHead_singularProfile_nonneg (t L : ℝ) : 0 ≤ abelHead (singularProfile α) t L :=
  setIntegral_nonneg measurableSet_Ioi fun u _ =>
    mul_nonneg (Real.exp_pos _).le (singularProfile_nonneg u)

/-- Off `−log 2` the Abel integrals decay like `(2/n)^t`. -/
theorem abelHead_singularProfile_le (hα : α < 1 / 2) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    abelHead (singularProfile α) t (Real.log n) ≤
      Real.exp (-(t * Real.log n)) * Real.exp (t * Real.log 2) * ∫ u, singularProfile α u := by
  have h1 : Integrable (singularProfile α) := (integrable_singularBase hα).comp_add_right _
  unfold abelHead
  have hint : IntegrableOn (fun u => Real.exp (-(t * (Real.log n + u))) * singularProfile α u)
      (Ioi (-Real.log n)) := by
    refine h1.integrableOn.mono' (((by fun_prop : Measurable fun u : ℝ =>
      Real.exp (-(t * (Real.log n + u)))).mul measurable_singularProfile).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_))
    have hu' : 0 < Real.log n + u := by have : -Real.log n < u := hu; linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (singularProfile_nonneg u)]
    exact mul_le_of_le_one_left (singularProfile_nonneg u) ((Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg ht hu'.le] : -(t * (Real.log n + u)) ≤ 0)).trans_eq Real.exp_zero)
  calc ∫ u in Ioi (-Real.log n), Real.exp (-(t * (Real.log n + u))) * singularProfile α u
      ≤ ∫ u in Ioi (-Real.log n),
          Real.exp (-(t * Real.log n)) * Real.exp (t * Real.log 2) * singularProfile α u := by
        refine setIntegral_mono_on hint (h1.integrableOn.const_mul _) measurableSet_Ioi
          fun u _ => ?_
        by_cases h : u + Real.log 2 ∈ Ioc (0 : ℝ) (1 / 4)
        · have he : Real.exp (-(t * (Real.log n + u))) ≤
              Real.exp (-(t * Real.log n)) * Real.exp (t * Real.log 2) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ht h.1.le])
          exact mul_le_mul_of_nonneg_right he (singularProfile_nonneg u)
        · have h0 : singularProfile α u = 0 := singularBase_of_not_mem h
          rw [h0]; simp
    _ ≤ Real.exp (-(t * Real.log n)) * Real.exp (t * Real.log 2) * ∫ u, singularProfile α u := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (setIntegral_le_integral h1
          (Eventually.of_forall singularProfile_nonneg)) (by positivity)

/-- **The scaled prime head of `F_α` grows at least like `t^α`.** -/
theorem mul_rpow_le_norm_mul_primeHead_neg_singularProfile (hα : α < 1 / 2) {t : ℝ}
    (ht : 4 ≤ t) :
    vonMangoldtAtom 2 * (Real.exp (-1) / (1 - α)) * t ^ α ≤
      ‖(t : ℂ) * primeHead (singularProfile α) (-(t : ℂ))‖ := by
  have htpos : 0 < t := by linarith
  have hsum : Summable fun n : ℕ =>
      vonMangoldtAtom n * abelHead (singularProfile α) t (Real.log n) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (atom_nonneg_sg n) (abelHead_singularProfile_nonneg t _)) (fun n => ?_)
      ((summable_primeHead_damping (c := t) (by linarith)).mul_right
        (Real.exp (t * Real.log 2) * ∫ u, singularProfile α u))
    calc vonMangoldtAtom n * abelHead (singularProfile α) t (Real.log n)
        ≤ vonMangoldtAtom n * (Real.exp (-(t * Real.log n)) * Real.exp (t * Real.log 2) *
            ∫ u, singularProfile α u) :=
          mul_le_mul_of_nonneg_left (abelHead_singularProfile_le hα htpos.le n) (atom_nonneg_sg n)
      _ = vonMangoldtAtom n * Real.exp (-t * Real.log n) *
            (Real.exp (t * Real.log 2) * ∫ u, singularProfile α u) := by rw [neg_mul]; ring
  have hle := sum_le_hasSum {2} (fun j _ => mul_nonneg (atom_nonneg_sg j)
    (abelHead_singularProfile_nonneg t _)) hsum.hasSum
  rw [Finset.sum_singleton] at hle
  have hlow := mul_abelHead_singularProfile_ge hα ht
  rw [primeHead_neg_ofReal, ← Complex.ofReal_tsum, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs]
  calc vonMangoldtAtom 2 * (Real.exp (-1) / (1 - α)) * t ^ α
      ≤ vonMangoldtAtom 2 * (t * abelHead (singularProfile α) t (Real.log 2)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlow vonMangoldtAtom_two_pos.le
    _ = t * (vonMangoldtAtom 2 * abelHead (singularProfile α) t (Real.log ((2 : ℕ) : ℝ))) := by
        push_cast; ring
    _ ≤ t * ∑' n : ℕ, vonMangoldtAtom n * abelHead (singularProfile α) t (Real.log n) :=
        mul_le_mul_of_nonneg_left hle htpos.le
    _ ≤ |t * ∑' n : ℕ, vonMangoldtAtom n * abelHead (singularProfile α) t (Real.log n)| :=
        le_abs_self _

end Profile

/-- **The exponent ½ of the unconditional bound is sharp.** For every `F ∈ H`,
`‖t · ŜF(−t)‖ = o(t^{1/2})` (`tendsto_sqrt_mul_primeHead_neg`); for every `α < ½` some `F ∈ H` has
`‖t · ŜF(−t)‖ ≥ c t^α`. -/
theorem primeHead_neg_growth_exponent_half_is_sharp {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1 / 2) :
    ∃ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F ∧ ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, 4 ≤ t → c * t ^ α ≤ ‖(t : ℂ) * primeHead F (-(t : ℂ))‖ :=
  ⟨singularProfile α, criticalHalfLineEnergyDomain_singularProfile hα0 hα,
    vonMangoldtAtom 2 * (Real.exp (-1) / (1 - α)),
    mul_pos vonMangoldtAtom_two_pos (div_pos (Real.exp_pos _) (by linarith)),
    fun _ ht => mul_rpow_le_norm_mul_primeHead_neg_singularProfile hα ht⟩

/-- **No leading term on the whole energy domain.** Some profile of `H` has no limit of
`t · ŜF(−t)` as `t → ∞`. -/
theorem exists_profile_without_primeHead_limit :
    ∃ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F ∧
      ∀ ℓ : ℂ, ¬ Tendsto (fun t : ℝ => (t : ℂ) * primeHead F (-(t : ℂ))) atTop (𝓝 ℓ) := by
  obtain ⟨F, hF, c, hc, hlow⟩ :=
    primeHead_neg_growth_exponent_half_is_sharp (α := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨F, hF, fun ℓ h => not_tendsto_nhds_of_tendsto_atTop ?_ ‖ℓ‖ h.norm⟩
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 4).mono fun t ht => hlow t ht)
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_atTop hc)

#print axioms primeHead_neg_growth_exponent_half_is_sharp
#print axioms exists_profile_without_primeHead_limit

end GaloisForLFunctions.ExclusionOfTheCriticalState
