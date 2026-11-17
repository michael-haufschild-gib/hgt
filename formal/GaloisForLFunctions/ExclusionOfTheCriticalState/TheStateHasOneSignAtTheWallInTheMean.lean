import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeSideBeyondTheWallIsTheDefectOfTheTranslatedState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheBeyondWallProfileIsTheCollarWaveMinusThePrimeWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheCriticalStateHasVanishingAverageWallMass
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap

/-!
# At the wall the state has one sign in the mean

Let `F` be the critical state, `a` the alias coefficient and `F⁺` the profile beyond the wall. Put

  `Φ(x) = ∫_{v>0} F(−v)/(x + v) dv` (Stieltjes potential, `x > 0`),
  `L(k) = ∫_{v>k} F(−v)/v dv` (logarithmic moment left of `−k`).

* **The prime side at the wall is the Stieltjes potential of the state.** For almost every
  `0 < x < 1`, `|a F⁺(x) + Φ(x)/2| ≤ B`
  (`criticalState_exists_ae_norm_beyondWall_add_wallPotential_le`): the collar kernel is
  `κ(t) = −1/(2t) + O(e^{t/2})`, the pole mode is bounded, and the prime wave
  `Σ_n Λ(n) n^{−½} F(x − log n)` is bounded because `|F(u)| ≤ C e^{2u}` and `Σ Λ(n) n^{−2} < ∞`.
* **The law of the wall** (`criticalState_tendsto_terminalMean_mul_wallLogMoment`).
  `(k⁻¹ ∫_{−k}^0 F) · L(k) → 16 a ∫ F² e^{−8u}` as `k → 0⁺`.
* **One sign** (`criticalState_exists_sign_at_wall`). There is `s = ±1` with `s ∫_{−k}^0 F > 0` and
  `s L(k) > 0` for every small `k > 0`: the terminal mean of the state does not change sign, although
  the state changes sign on every left ray.
* **Logarithmic rates.** `L(k)² ≥ c log(2/k)` (`criticalState_eventually_log_le_sq_wallLogMoment`):
  `F(u)/u` is not integrable at the wall. `∫_0^k |F⁺|² ≥ c k log(2/k)`
  (`criticalState_eventually_log_le_integral_sq_beyondWallProfile`): the prime side is unbounded at
  the wall.

Mechanism. The wall law `k⁻¹ ∫_0^k F⁺(x) F(x − k) dx → −8 ∫ F² e^{−8u}` with `a F⁺ = −Φ/2 + O(1)` gives
`k⁻¹ ∫_0^k Φ(x) F(x − k) dx → 16 a ∫ F² e^{−8u}`; the bounded part pairs with `∫_{−k}^0 |F|`, which is
`o(k)` because the mean square of the state vanishes at the wall. On `0 < x < k`,
`|Φ(x) − L(k)| ≤ C + 4C (k/x)^{1/4}`: beyond `k` the kernels `1/(x + v)` and `1/v` differ by at most
`k/v²`, and below `k`, `1/(x + v) ≤ x^{−1/4} v^{−3/4}`. Cauchy–Schwarz against `F(x − k)` replaces
`Φ` by `L(k)`. The sign follows from the continuity of `L`, the rates from the logarithmic gain of
the terminal mass and from the uncertainty inequality at the wall.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower CanonicalSystemOfTheWindowTower
  SpacingScaleHarmonicAnalysis

/-! ### Translation, reflection and the Stieltjes kernel -/

theorem ae_comp_sub_right {p : ℝ → Prop} (h : ∀ᵐ u : ℝ, p u) (c : ℝ) : ∀ᵐ x : ℝ, p (x - c) :=
  (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae h

theorem ae_comp_neg {p : ℝ → Prop} (h : ∀ᵐ u : ℝ, p u) : ∀ᵐ v : ℝ, p (-v) :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h

theorem setIntegral_Ioo_comp_sub (g : ℝ → ℝ) (k : ℝ) :
    ∫ x in Ioo (0 : ℝ) k, g (x - k) = ∫ u in Ioo (-k) 0, g u := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo,
    ← integral_sub_right_eq_self (fun u : ℝ => Set.indicator (Ioo (-k) 0) g u) k]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show Set.indicator (Ioo (0 : ℝ) k) (fun x => g (x - k)) x = Set.indicator (Ioo (-k) 0) g (x - k)
  by_cases hx : x ∈ Ioo (0 : ℝ) k
  · have hx' : x - k ∈ Ioo (-k) 0 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · have hx' : x - k ∉ Ioo (-k) 0 := fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

/-- Weighted arithmetic–geometric mean for the Stieltjes kernel: `1/(x + v) ≤ x^{−1/4} v^{−3/4}`. -/
theorem inv_add_le_rpow_mul_rpow {x v : ℝ} (hx : 0 < x) (hv : 0 < v) :
    (x + v)⁻¹ ≤ x ^ (-(1 / 4 : ℝ)) * v ^ (-(3 / 4 : ℝ)) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) hx.le hv.le (by norm_num)
  have hpos : 0 < x ^ (1 / 4 : ℝ) * v ^ (3 / 4 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hv _)
  have hle : x ^ (1 / 4 : ℝ) * v ^ (3 / 4 : ℝ) ≤ x + v := by linarith
  rw [Real.rpow_neg hx.le, Real.rpow_neg hv.le, ← mul_inv]
  exact inv_anti₀ hpos hle

theorem integrableOn_Ioc_zero_rpow {r : ℝ} (hr : -1 < r) {k : ℝ} (hk : 0 ≤ k) :
    IntegrableOn (fun v : ℝ => v ^ r) (Ioc 0 k) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hk).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

theorem integral_Ioc_rpow_neg_three_quarters {k : ℝ} (hk : 0 < k) :
    ∫ v in Ioc (0 : ℝ) k, v ^ (-(3 / 4 : ℝ)) = 4 * k ^ (1 / 4 : ℝ) := by
  rw [← intervalIntegral.integral_of_le hk.le, integral_rpow (Or.inl (by norm_num))]
  have e : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num), sub_zero]
  ring

theorem integral_Ioo_rpow_neg_half {k : ℝ} (hk : 0 < k) :
    ∫ x in Ioo (0 : ℝ) k, x ^ (-(1 / 2 : ℝ)) = 2 * k ^ (1 / 2 : ℝ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hk.le,
    integral_rpow (Or.inl (by norm_num))]
  have e : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
  rw [e, Real.zero_rpow (by norm_num), sub_zero]
  ring

theorem integral_Ioi_rpow_neg_two_eq_inv {k : ℝ} (hk : 0 < k) :
    ∫ v in Ioi k, v ^ (-(2 : ℝ)) = k⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) hk]
  have e : (-(2 : ℝ) + 1) = -1 := by norm_num
  rw [e, Real.rpow_neg_one]
  ring

theorem integral_Ioo_one {k : ℝ} (hk : 0 ≤ k) : ∫ _x in Ioo (-k) (0 : ℝ), (1 : ℝ) = k := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

/-- Near part: a bounded density against the Stieltjes kernel over `(0, k]`. -/
theorem abs_setIntegral_Ioc_div_add_le {f : ℝ → ℝ} {C : ℝ} (hb : ∀ᵐ v : ℝ, |f v| ≤ C) {x k : ℝ}
    (hx : 0 < x) (hk : 0 < k) :
    |∫ v in Ioc (0 : ℝ) k, f v / (x + v)| ≤ 4 * C * k ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) := by
  have hbound : IntegrableOn (fun v : ℝ => C * x ^ (-(1 / 4 : ℝ)) * v ^ (-(3 / 4 : ℝ))) (Ioc 0 k) :=
    (integrableOn_Ioc_zero_rpow (by norm_num) hk.le).const_mul _
  have hle : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) k)),
      ‖f v / (x + v)‖ ≤ C * x ^ (-(1 / 4 : ℝ)) * v ^ (-(3 / 4 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioc] with v hv hmem
    have hv0 : 0 < v := hmem.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (add_pos hx hv0), div_eq_mul_inv]
    calc |f v| * (x + v)⁻¹ ≤ C * (x ^ (-(1 / 4 : ℝ)) * v ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul hv (inv_add_le_rpow_mul_rpow hx hv0) (inv_nonneg.mpr (add_pos hx hv0).le)
            ((abs_nonneg _).trans hv)
      _ = C * x ^ (-(1 / 4 : ℝ)) * v ^ (-(3 / 4 : ℝ)) := by ring
  have h := norm_integral_le_of_norm_le hbound hle
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioc_rpow_neg_three_quarters hk] at h
  calc |∫ v in Ioc (0 : ℝ) k, f v / (x + v)| ≤ C * x ^ (-(1 / 4 : ℝ)) * (4 * k ^ (1 / 4 : ℝ)) := h
    _ = 4 * C * k ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) := by ring

/-- Far part: moving the pole of the Stieltjes kernel from `−x` to `0` costs a bounded amount. -/
theorem abs_setIntegral_Ioi_div_sub_le {f : ℝ → ℝ} {C : ℝ} (hb : ∀ᵐ v : ℝ, |f v| ≤ C) {x k : ℝ}
    (hx : 0 < x) (hxk : x ≤ k) : |∫ v in Ioi k, (f v / (x + v) - f v / v)| ≤ C := by
  have hk : 0 < k := hx.trans_le hxk
  have hbound : IntegrableOn (fun v : ℝ => C * k * v ^ (-(2 : ℝ))) (Ioi k) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hk).const_mul _
  have hle : ∀ᵐ v ∂(volume.restrict (Ioi k)),
      ‖f v / (x + v) - f v / v‖ ≤ C * k * v ^ (-(2 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioi] with v hv hmem
    have hv0 : 0 < v := hk.trans hmem
    have hC : 0 ≤ C := (abs_nonneg _).trans hv
    have hxv : x + v ≠ 0 := (add_pos hx hv0).ne'
    have hv' : v ≠ 0 := hv0.ne'
    have e : f v / (x + v) - f v / v = -(f v * x / ((x + v) * v)) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_neg, abs_div, abs_mul, abs_of_pos hx,
      abs_of_pos (mul_pos (add_pos hx hv0) hv0), Real.rpow_neg hv0.le, Real.rpow_two]
    calc |f v| * x / ((x + v) * v) ≤ C * k / (v * v) :=
          div_le_div₀ (mul_nonneg hC hk.le) (mul_le_mul hv hxk hx.le hC) (mul_pos hv0 hv0)
            (mul_le_mul_of_nonneg_right (by linarith) hv0.le)
      _ = C * k * (v ^ 2)⁻¹ := by rw [sq, div_eq_mul_inv]
  have h := norm_integral_le_of_norm_le hbound hle
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_neg_two_eq_inv hk] at h
  calc |∫ v in Ioi k, (f v / (x + v) - f v / v)| ≤ C * k * k⁻¹ := h
    _ = C := by field_simp

/-! ### The Stieltjes potential and the logarithmic moment of a profile -/

/-- The Stieltjes potential of a profile right of the wall: `Φ_F(x) = ∫_{v>0} F(−v)/(x + v) dv`. -/
def wallPotential (F : ℝ → ℝ) (x : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), F (-v) / (x + v)

/-- The logarithmic moment of a profile left of `−k`: `L_F(k) = ∫_{v>k} F(−v)/v dv`. -/
def wallLogMoment (F : ℝ → ℝ) (k : ℝ) : ℝ := ∫ v in Ioi k, F (-v) / v

theorem measurable_wallPotential {F : ℝ → ℝ} (hF : Measurable F) : Measurable (wallPotential F) := by
  have h : StronglyMeasurable (fun p : ℝ × ℝ => F (-p.2) / (p.1 + p.2)) :=
    ((hF.comp measurable_snd.neg).div (measurable_fst.add measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem integrableOn_div_add {f : ℝ → ℝ} (hfm : Measurable f) (hfi : Integrable f) {x : ℝ}
    (hx : 0 < x) : IntegrableOn (fun v => f v / (x + v)) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (hfi.abs.div_const x).integrableOn
    (hfm.div (measurable_const.add measurable_id)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (add_pos hx hv0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hx (by linarith)

theorem integrableOn_div_self {f : ℝ → ℝ} (hfm : Measurable f) (hfi : Integrable f) {k : ℝ}
    (hk : 0 < k) : IntegrableOn (fun v => f v / v) (Ioi k) := by
  refine Integrable.mono' (hfi.abs.div_const k).integrableOn
    (hfm.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := hk.trans hv
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hv0]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hk (le_of_lt hv)

/-- On `(0, k]` the Stieltjes potential of a bounded integrable profile is its logarithmic moment
left of `−k` up to `C + 4C (k/x)^{1/4}`. -/
theorem abs_wallPotential_sub_wallLogMoment_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hFi : Integrable F) {C : ℝ} (hb : ∀ᵐ u : ℝ, |F u| ≤ C) {x k : ℝ} (hx : 0 < x)
    (hxk : x ≤ k) :
    |wallPotential F x - wallLogMoment F k| ≤
      C + 4 * C * k ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) := by
  have hk : 0 < k := hx.trans_le hxk
  have hfm : Measurable fun v : ℝ => F (-v) := hFm.comp measurable_neg
  have hfi : Integrable fun v : ℝ => F (-v) := hFi.comp_neg
  have hb' : ∀ᵐ v : ℝ, |F (-v)| ≤ C := ae_comp_neg hb
  have hI1 := integrableOn_div_add hfm hfi hx
  have hI2 := integrableOn_div_self hfm hfi hk
  have hsplit : wallPotential F x =
      (∫ v in Ioc (0 : ℝ) k, F (-v) / (x + v)) + ∫ v in Ioi k, F (-v) / (x + v) := by
    unfold wallPotential
    rw [← Ioc_union_Ioi_eq_Ioi hk.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI1.mono_set Ioc_subset_Ioi_self) (hI1.mono_set (Ioi_subset_Ioi hk.le))]
  have hfar : (∫ v in Ioi k, F (-v) / (x + v)) - wallLogMoment F k =
      ∫ v in Ioi k, (F (-v) / (x + v) - F (-v) / v) := by
    unfold wallLogMoment
    rw [integral_sub (hI1.mono_set (Ioi_subset_Ioi hk.le)) hI2]
  have h1 := abs_le.mp (abs_setIntegral_Ioc_div_add_le hb' hx hk)
  have h2 := abs_setIntegral_Ioi_div_sub_le hb' hx hxk
  rw [← hfar] at h2
  have h2' := abs_le.mp h2
  rw [hsplit]
  exact abs_le.mpr ⟨by linarith [h1.1, h2'.1], by linarith [h1.2, h2'.2]⟩

/-- Cauchy–Schwarz on a terminal interval. -/
theorem sq_setIntegral_Ioo_le {G : ℝ → ℝ} (hGm : Measurable G) (hG2 : Integrable fun u => G u ^ 2)
    {k : ℝ} (hk : 0 ≤ k) :
    (∫ u in Ioo (-k) 0, G u) ^ 2 ≤ k * ∫ u in Ioo (-k) 0, G u ^ 2 := by
  have h := sq_integral_mul_le (μ := volume.restrict (Ioo (-k) (0 : ℝ))) (f := G)
    (g := fun _ => (1 : ℝ)) hGm.aestronglyMeasurable aestronglyMeasurable_const hG2.integrableOn
    (integrable_const _)
  simp only [mul_one, one_pow] at h
  rw [integral_Ioo_one hk] at h
  linarith

/-- The root mean square of a profile on the terminal interval `(−k, 0)`. -/
def terminalRootMeanSquare (F : ℝ → ℝ) (k : ℝ) : ℝ :=
  Real.sqrt ((∫ u in Ioo (-k) 0, F u ^ 2) / k)

theorem terminalRootMeanSquare_nonneg (F : ℝ → ℝ) (k : ℝ) : 0 ≤ terminalRootMeanSquare F k :=
  Real.sqrt_nonneg _

theorem sq_mul_terminalRootMeanSquare (F : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    (k * terminalRootMeanSquare F k) ^ 2 = k * ∫ u in Ioo (-k) 0, F u ^ 2 := by
  have hm : 0 ≤ ∫ u in Ioo (-k) 0, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  unfold terminalRootMeanSquare
  rw [mul_pow, Real.sq_sqrt (div_nonneg hm hk.le)]
  field_simp

/-- `∫_0^k |F(x − k)| dx ≤ k · rms_k(F)`. -/
theorem integral_abs_translate_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hF2 : Integrable fun u => F u ^ 2) {k : ℝ} (hk : 0 < k) :
    ∫ x in Ioo (0 : ℝ) k, |F (x - k)| ≤ k * terminalRootMeanSquare F k := by
  have h := sq_setIntegral_Ioo_le (G := fun u => |F u|) hFm.abs
    (hF2.congr (Eventually.of_forall fun u => (sq_abs (F u)).symm)) hk.le
  simp only [sq_abs] at h
  rw [setIntegral_Ioo_comp_sub (fun u => |F u|) k]
  rw [← sq_mul_terminalRootMeanSquare F hk] at h
  exact (sq_le_sq₀ (integral_nonneg fun u => abs_nonneg _)
    (mul_nonneg hk.le (terminalRootMeanSquare_nonneg F k))).mp h

theorem integrableOn_translate_mul_wallPotential {F : ℝ → ℝ} (hFm : Measurable F)
    (hFi : Integrable F) {C : ℝ} (hb : ∀ᵐ u : ℝ, |F u| ≤ C) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun x => F (x - k) * wallPotential F x) (Ioo (0 : ℝ) k) := by
  have hbd : IntegrableOn (fun x : ℝ => C * (|wallLogMoment F k| + C) +
      C * (4 * C * k ^ (1 / 4 : ℝ)) * x ^ (-(1 / 4 : ℝ))) (Ioo (0 : ℝ) k) :=
    (integrable_const _).add (((integrableOn_Ioc_zero_rpow (r := -(1 / 4 : ℝ)) (by norm_num)
      hk.le).mono_set Ioo_subset_Ioc_self).const_mul _)
  refine Integrable.mono' hbd ((hFm.comp (measurable_id.sub_const k)).mul
    (measurable_wallPotential hFm)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae (ae_comp_sub_right hb k),
    ae_restrict_mem measurableSet_Ioo] with x hbx hmem
  have hC : 0 ≤ C := (abs_nonneg _).trans hbx
  have hΦ := abs_wallPotential_sub_wallLogMoment_le hFm hFi hb hmem.1 hmem.2.le
  have hΦ' : |wallPotential F x| ≤
      |wallLogMoment F k| + (C + 4 * C * k ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ))) := by
    linarith [abs_sub_abs_le_abs_sub (wallPotential F x) (wallLogMoment F k)]
  rw [Real.norm_eq_abs, abs_mul]
  calc |F (x - k)| * |wallPotential F x|
      ≤ C * (|wallLogMoment F k| + (C + 4 * C * k ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)))) :=
        mul_le_mul hbx hΦ' (abs_nonneg _) hC
    _ = C * (|wallLogMoment F k| + C) + C * (4 * C * k ^ (1 / 4 : ℝ)) * x ^ (-(1 / 4 : ℝ)) := by
        ring

/-- **The potential against the translated profile is the terminal mean times the logarithmic
moment**, up to `7C k · rms_k(F)`, for a profile bounded by `C`. -/
theorem abs_integral_translate_mul_wallPotential_sub_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hFi : Integrable F) (hF2 : Integrable fun u => F u ^ 2) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ u : ℝ, |F u| ≤ C) {k : ℝ} (hk : 0 < k) :
    |(∫ x in Ioo (0 : ℝ) k, F (x - k) * wallPotential F x) -
        (∫ u in Ioo (-k) 0, F u) * wallLogMoment F k| ≤
      7 * C * (k * terminalRootMeanSquare F k) := by
  have hm : 0 ≤ ∫ u in Ioo (-k) 0, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hkT := sq_mul_terminalRootMeanSquare F hk
  have hTnn : 0 ≤ k * terminalRootMeanSquare F k :=
    mul_nonneg hk.le (terminalRootMeanSquare_nonneg F k)
  have hbk : ∀ᵐ x : ℝ, |F (x - k)| ≤ C := ae_comp_sub_right hb k
  have hFk : IntegrableOn (fun x => F (x - k)) (Ioo (0 : ℝ) k) :=
    (hFi.comp_sub_right k).integrableOn
  have hFkm : Measurable fun x : ℝ => F (x - k) := hFm.comp (measurable_id.sub_const k)
  have hI1 := integral_abs_translate_le hFm hF2 hk
  -- the weight `x^{−1/4}` is square integrable on `(0, k)`
  have hrm : Measurable fun x : ℝ => x ^ (-(1 / 4 : ℝ)) := measurable_id.pow_const _
  have hsq : ∀ x ∈ Ioo (0 : ℝ) k, (x ^ (-(1 / 4 : ℝ))) ^ 2 = x ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    norm_num
  have hr2 : IntegrableOn (fun x : ℝ => (x ^ (-(1 / 4 : ℝ))) ^ 2) (Ioo (0 : ℝ) k) :=
    ((integrableOn_Ioc_zero_rpow (r := -(1 / 2 : ℝ)) (by norm_num) hk.le).mono_set
      Ioo_subset_Ioc_self).congr_fun (fun x hx => (hsq x hx).symm) measurableSet_Ioo
  have hg2 : IntegrableOn (fun x : ℝ => |F (x - k)| ^ 2) (Ioo (0 : ℝ) k) :=
    ((hF2.comp_sub_right k).integrableOn).congr (Eventually.of_forall fun x => (sq_abs _).symm)
  have hcs := sq_integral_mul_le (μ := volume.restrict (Ioo (0 : ℝ) k))
    (f := fun x => |F (x - k)|) (g := fun x => x ^ (-(1 / 4 : ℝ)))
    hFkm.abs.aestronglyMeasurable hrm.aestronglyMeasurable hg2 hr2
  have hF2k : ∫ x in Ioo (0 : ℝ) k, |F (x - k)| ^ 2 = ∫ u in Ioo (-k) 0, F u ^ 2 := by
    simp only [sq_abs]
    exact setIntegral_Ioo_comp_sub (fun u => F u ^ 2) k
  have hr2v : ∫ x in Ioo (0 : ℝ) k, (x ^ (-(1 / 4 : ℝ))) ^ 2 = 2 * k ^ (1 / 2 : ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hsq, integral_Ioo_rpow_neg_half hk]
  rw [hF2k, hr2v] at hcs
  have hq2 : (k ^ (1 / 4 : ℝ)) ^ 2 = k ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le]
    norm_num
  have hhh : k ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ) = k := by
    rw [← Real.rpow_add hk]
    norm_num
  have hI2 : k ^ (1 / 4 : ℝ) * (∫ x in Ioo (0 : ℝ) k, |F (x - k)| * x ^ (-(1 / 4 : ℝ))) ≤
      3 / 2 * (k * terminalRootMeanSquare F k) := by
    have hI2nn : 0 ≤ ∫ x in Ioo (0 : ℝ) k, |F (x - k)| * x ^ (-(1 / 4 : ℝ)) :=
      setIntegral_nonneg measurableSet_Ioo fun x hx =>
        mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.1.le _)
    have hsq2 : (k ^ (1 / 4 : ℝ) * ∫ x in Ioo (0 : ℝ) k, |F (x - k)| * x ^ (-(1 / 4 : ℝ))) ^ 2 ≤
        (3 / 2 * (k * terminalRootMeanSquare F k)) ^ 2 := by
      rw [mul_pow, hq2, mul_pow, hkT]
      calc k ^ (1 / 2 : ℝ) * (∫ x in Ioo (0 : ℝ) k, |F (x - k)| * x ^ (-(1 / 4 : ℝ))) ^ 2
          ≤ k ^ (1 / 2 : ℝ) * ((∫ u in Ioo (-k) 0, F u ^ 2) * (2 * k ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hcs (Real.rpow_nonneg hk.le _)
        _ = 2 * (∫ u in Ioo (-k) 0, F u ^ 2) * (k ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ)) := by ring
        _ = 2 * (∫ u in Ioo (-k) 0, F u ^ 2) * k := by rw [hhh]
        _ ≤ (3 / 2) ^ 2 * (k * ∫ u in Ioo (-k) 0, F u ^ 2) := by
            nlinarith [mul_nonneg hk.le hm]
    exact (sq_le_sq₀ (mul_nonneg (Real.rpow_nonneg hk.le _) hI2nn)
      (mul_nonneg (by norm_num) hTnn)).mp hsq2
  -- the difference as one integral over the collar
  have hint := integrableOn_translate_mul_wallPotential hFm hFi hb hk
  have e1 : (∫ u in Ioo (-k) 0, F u) = ∫ x in Ioo (0 : ℝ) k, F (x - k) :=
    (setIntegral_Ioo_comp_sub F k).symm
  rw [e1, ← integral_mul_const, ← integral_sub hint (hFk.mul_const _)]
  have hprod : IntegrableOn (fun x : ℝ => |F (x - k)| * x ^ (-(1 / 4 : ℝ))) (Ioo (0 : ℝ) k) := by
    refine Integrable.mono' (((integrableOn_Ioc_zero_rpow (r := -(1 / 4 : ℝ)) (by norm_num)
      hk.le).mono_set Ioo_subset_Ioc_self).const_mul C) (hFkm.abs.mul hrm).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae hbk, ae_restrict_mem measurableSet_Ioo] with x hx hmem
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hmem.1.le _)]
    exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hmem.1.le _)
  have hle : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) k)),
      ‖F (x - k) * wallPotential F x - F (x - k) * wallLogMoment F k‖ ≤
        C * |F (x - k)| + 4 * C * k ^ (1 / 4 : ℝ) * (|F (x - k)| * x ^ (-(1 / 4 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hmem
    have hΦ := abs_wallPotential_sub_wallLogMoment_le hFm hFi hb hmem.1 hmem.2.le
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    calc |F (x - k)| * |wallPotential F x - wallLogMoment F k|
        ≤ |F (x - k)| * (C + 4 * C * k ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hΦ (abs_nonneg _)
      _ = C * |F (x - k)| + 4 * C * k ^ (1 / 4 : ℝ) * (|F (x - k)| * x ^ (-(1 / 4 : ℝ))) := by
          ring
  have hbd : IntegrableOn (fun x : ℝ => C * |F (x - k)| +
      4 * C * k ^ (1 / 4 : ℝ) * (|F (x - k)| * x ^ (-(1 / 4 : ℝ)))) (Ioo (0 : ℝ) k) :=
    (hFk.abs.const_mul C).add (hprod.const_mul (4 * C * k ^ (1 / 4 : ℝ)))
  have h := norm_integral_le_of_norm_le hbd hle
  rw [Real.norm_eq_abs, integral_add (hFk.abs.const_mul C)
    (hprod.const_mul (4 * C * k ^ (1 / 4 : ℝ))), integral_const_mul, integral_const_mul] at h
  have h1 := mul_le_mul_of_nonneg_left hI1 hC
  have h2 := mul_le_mul_of_nonneg_left hI2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
  have e2 : 4 * C * k ^ (1 / 4 : ℝ) * (∫ x in Ioo (0 : ℝ) k, |F (x - k)| * x ^ (-(1 / 4 : ℝ))) =
      4 * C * (k ^ (1 / 4 : ℝ) * ∫ x in Ioo (0 : ℝ) k, |F (x - k)| * x ^ (-(1 / 4 : ℝ))) := by
    ring
  rw [e2] at h
  linarith

/-- The logarithmic moment is continuous in `k > 0`. -/
theorem continuousOn_wallLogMoment {F : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F) :
    ContinuousOn (wallLogMoment F) (Ioi (0 : ℝ)) := by
  intro k₀ hk₀
  have hk₀' : (0 : ℝ) < k₀ := hk₀
  have hc0 : 0 < k₀ / 2 := by positivity
  have hfm : Measurable fun v : ℝ => F (-v) := hFm.comp measurable_neg
  have hfi : Integrable fun v : ℝ => F (-v) := hFi.comp_neg
  have hg := integrableOn_div_self hfm hfi hc0
  have hg₀ : Integrable (Set.indicator (Ioi (k₀ / 2)) fun v : ℝ => F (-v) / v) :=
    hg.integrable_indicator measurableSet_Ioi
  have hcont : Continuous fun k : ℝ => (∫ v in Ioi (k₀ / 2), F (-v) / v) -
      ∫ v in (k₀ / 2)..k, Set.indicator (Ioi (k₀ / 2)) (fun v : ℝ => F (-v) / v) v :=
    continuous_const.sub
      (intervalIntegral.continuous_primitive (fun a b => hg₀.intervalIntegrable) (k₀ / 2))
  have heq : ∀ k : ℝ, k₀ / 2 < k → wallLogMoment F k = (∫ v in Ioi (k₀ / 2), F (-v) / v) -
      ∫ v in (k₀ / 2)..k, Set.indicator (Ioi (k₀ / 2)) (fun v : ℝ => F (-v) / v) v := by
    intro k hk
    have h1 : (∫ v in (k₀ / 2)..k, Set.indicator (Ioi (k₀ / 2)) (fun v : ℝ => F (-v) / v) v) =
        ∫ v in Ioc (k₀ / 2) k, F (-v) / v := by
      rw [intervalIntegral.integral_of_le hk.le]
      exact setIntegral_congr_fun measurableSet_Ioc fun v hv =>
        Set.indicator_of_mem (show v ∈ Ioi (k₀ / 2) from hv.1) _
    have h2 : (∫ v in Ioi (k₀ / 2), F (-v) / v) =
        (∫ v in Ioc (k₀ / 2) k, F (-v) / v) + ∫ v in Ioi k, F (-v) / v := by
      rw [← Ioc_union_Ioi_eq_Ioi hk.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi (hg.mono_set Ioc_subset_Ioi_self) (hg.mono_set (Ioi_subset_Ioi hk.le))]
    unfold wallLogMoment
    rw [h1, h2]
    ring
  have hev : (fun k : ℝ => (∫ v in Ioi (k₀ / 2), F (-v) / v) -
      ∫ v in (k₀ / 2)..k, Set.indicator (Ioi (k₀ / 2)) (fun v : ℝ => F (-v) / v) v) =ᶠ[𝓝 k₀]
        wallLogMoment F := by
    filter_upwards [Ioi_mem_nhds (show k₀ / 2 < k₀ by linarith)] with k hk
    exact (heq k hk).symm
  exact (hcont.continuousAt.congr hev).continuousWithinAt

/-! ### The collar kernel at the wall -/

theorem measurable_collarKernel : Measurable collarKernel := by
  show Measurable fun x : ℝ => Real.exp (x / 2) - Real.exp (-x / 2) / (Real.exp (2 * x) - 1)
  fun_prop

/-- **The collar kernel at the wall.** `|κ(t) + 1/(2t)| ≤ 3 e^{t/2}` for `t > 0`. -/
theorem abs_collarKernel_add_inv_le {t : ℝ} (ht : 0 < t) :
    |collarKernel t + 1 / (2 * t)| ≤ 3 * Real.exp (t / 2) := by
  have he1 : 1 ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
  rcases le_or_gt t 1 with ht1 | ht1
  · have h1 := archLevyDensity_ge_inv_two_mul ht ht1
    have h2 := archLevyDensity_le_inv_two_mul_add ht ht1
    have hκ := two_mul_cosh_sub_archLevyDensity ht
    have hcosh : 2 * Real.cosh (t / 2) = Real.exp (t / 2) + Real.exp (-(t / 2)) := by
      rw [Real.cosh_eq]
      ring
    have hen : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hen0 : 0 < Real.exp (-(t / 2)) := Real.exp_pos _
    have hhalf : Real.exp (1 / 2) ≤ 2 := by
      have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
      have e : Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [← hκ, hcosh]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h2t : 2 * t + 1 ≤ Real.exp (2 * t) := Real.add_one_le_exp (2 * t)
    have hden : 0 < Real.exp (2 * t) - 1 := by linarith
    have hnum : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hq0 : 0 ≤ Real.exp (-t / 2) / (Real.exp (2 * t) - 1) :=
      div_nonneg (Real.exp_pos _).le hden.le
    have hq1 : Real.exp (-t / 2) / (Real.exp (2 * t) - 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      linarith
    have hinv0 : 0 < 1 / (2 * t) := by positivity
    have hinv1 : 1 / (2 * t) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    unfold collarKernel
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For a profile carried by `u < 0` the Stieltjes potential is `∫ F(u)/(x − u) du`. -/
theorem wallPotential_eq_integral {F : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) (x : ℝ) :
    wallPotential F x = ∫ u, F u / (x - u) := by
  unfold wallPotential
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
    have hv' : v ≤ 0 := not_lt.mp (show ¬ (0 : ℝ) < v from hv)
    rw [hF (-v) (by linarith), zero_div]]
  rw [← integral_neg_eq_self (fun u : ℝ => F u / (x - u)) volume]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  show F (-v) / (x + v) = F (-v) / (x - -v)
  rw [sub_neg_eq_add]

/-- **The collar wave at the wall is minus half the Stieltjes potential**, up to
`3 e^{x/2} ∫ |F| e^{−u/2}`. -/
theorem abs_collarWave_add_half_wallPotential_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {x : ℝ} (hx : 0 < x) :
    |collarWave F x + 1 / 2 * wallPotential F x| ≤
      3 * Real.exp (x / 2) * ∫ u, |F u| * Real.exp (-(1 / 2) * u) := by
  have hM := integrable_abs_mul_exp_of_domain hF (c := -(1 / 2)) (by norm_num)
  have hGm : Measurable fun u : ℝ => F u * (collarKernel (x - u) + 1 / 2 * (1 / (x - u))) :=
    hF.meas.mul ((measurable_collarKernel.comp (measurable_const.sub measurable_id)).add
      (measurable_const.mul (measurable_const.div (measurable_const.sub measurable_id))))
  have hGle : ∀ u : ℝ, ‖F u * (collarKernel (x - u) + 1 / 2 * (1 / (x - u)))‖ ≤
      3 * Real.exp (x / 2) * (|F u| * Real.exp (-(1 / 2) * u)) := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu, zero_mul, norm_zero, abs_zero, zero_mul, mul_zero]
    · have hk := abs_collarKernel_add_inv_le (show 0 < x - u by linarith)
      have e2 : (1 : ℝ) / 2 * (1 / (x - u)) = 1 / (2 * (x - u)) := by
        rw [one_div, one_div, one_div, mul_inv]
      have he : Real.exp ((x - u) / 2) = Real.exp (x / 2) * Real.exp (-(1 / 2) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.norm_eq_abs, abs_mul, e2]
      calc |F u| * |collarKernel (x - u) + 1 / (2 * (x - u))|
          ≤ |F u| * (3 * Real.exp ((x - u) / 2)) := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
        _ = 3 * Real.exp (x / 2) * (|F u| * Real.exp (-(1 / 2) * u)) := by
            rw [he]
            ring
  have hG : Integrable fun u : ℝ => F u * (collarKernel (x - u) + 1 / 2 * (1 / (x - u))) :=
    Integrable.mono' (hM.const_mul _) hGm.aestronglyMeasurable (Eventually.of_forall hGle)
  have hP : Integrable fun u : ℝ => F u / (x - u) := by
    refine Integrable.mono' (hF.integrable.abs.div_const x)
      (hF.meas.div (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu, zero_div, norm_zero, abs_zero, zero_div]
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < x - u by linarith)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hx (by linarith)
  have hsplit : ∀ u : ℝ, F u * collarKernel (x - u) =
      F u * (collarKernel (x - u) + 1 / 2 * (1 / (x - u))) - 1 / 2 * (F u / (x - u)) := by
    intro u
    ring
  have hval : collarWave F x + 1 / 2 * wallPotential F x =
      ∫ u, F u * (collarKernel (x - u) + 1 / 2 * (1 / (x - u))) := by
    unfold collarWave
    rw [integral_congr_ae (Eventually.of_forall hsplit), integral_sub hG (hP.const_mul _),
      integral_const_mul, wallPotential_eq_integral hF.support]
    ring
  rw [hval]
  have h := norm_integral_le_of_norm_le (hM.const_mul (3 * Real.exp (x / 2)))
    (Eventually.of_forall hGle)
  rwa [Real.norm_eq_abs, integral_const_mul] at h

/-- **The prime wave is bounded at the wall.** If `|F(u)| ≤ C e^{2u}` almost everywhere, then for
almost every `x`, `|Σ_n Λ(n) n^{−½} F(x − log n)| ≤ C e^{2x} Σ_n Λ(n) n^{−2}`. -/
theorem ae_norm_primeWave_le {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ u : ℝ, |F u| ≤ C * Real.exp (2 * u)) :
    ∀ᵐ x : ℝ, ‖∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖ ≤
      C * Real.exp (2 * x) *
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hall : ∀ᵐ x : ℝ, ∀ n : ℕ,
      |F (x - Real.log n)| ≤ C * Real.exp (2 * (x - Real.log n)) :=
    ae_all_iff.mpr fun n => ae_comp_sub_right hb (Real.log n)
  have hS : Summable fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
    _root_.RHTower.summable_vonMangoldt_mul_rpow (by norm_num)
  filter_upwards [hall] with x hx
  have hterm : ∀ n : ℕ, ‖(primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖ ≤
      C * Real.exp (2 * x) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) := by
    intro n
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hn : 2 ≤ n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hsqrt : 1 ≤ Real.sqrt n := by
        rw [Real.one_le_sqrt]
        exact_mod_cast (by omega : 1 ≤ n)
      have hpa : |primeAtom n| ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        unfold primeAtom
        rw [if_pos hn, abs_of_nonneg (div_nonneg hΛ (Real.sqrt_nonneg _))]
        exact div_le_self hΛ hsqrt
      have he : Real.exp (2 * (x - Real.log n)) = Real.exp (2 * x) * (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
        congr 1
        ring
      calc |primeAtom n| * |F (x - Real.log n)|
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (C * Real.exp (2 * (x - Real.log n))) :=
            mul_le_mul hpa (hx n) (abs_nonneg _) hΛ
        _ = C * Real.exp (2 * x) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) := by
            rw [he]
            ring
    · have hpa : primeAtom n = 0 := by
        unfold primeAtom
        rw [if_neg hn]
      rw [hpa, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le)
        (mul_nonneg hΛ (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hsn : Summable fun n : ℕ => ‖(primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hS.mul_left _)
  calc ‖∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖
      ≤ ∑' n : ℕ, ‖(primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, C * Real.exp (2 * x) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Summable.tsum_le_tsum hterm hsn (hS.mul_left _)
    _ = C * Real.exp (2 * x) *
          ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := tsum_mul_left

/-! ### The prime side at the wall -/

/-- **The prime side at the wall is the Stieltjes potential of the state.** For almost every
`0 < x < 1`, `|a F⁺(x) + Φ(x)/2| ≤ B`. -/
theorem criticalState_exists_ae_norm_beyondWall_add_wallPotential_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ‖(criticalAliasCoefficient W₀ : ℂ) *
          beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ)‖ ≤ B := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC, hb⟩ := (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).1 2
    (by norm_num) (by norm_num)
  have hI : 0 ≤ ∫ u, |F u| * Real.exp (-(1 / 2) * u) :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hS : 0 ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
    tsum_nonneg fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine ⟨3 * Real.exp (1 / 2) * (∫ u, |F u| * Real.exp (-(1 / 2) * u)) +
    C * Real.exp 2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)),
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hI)
      (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hS), ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      (beyondWallProfile_collarForm hW hd),
    ae_restrict_of_ae (ae_norm_primeWave_le hC hb),
    ae_restrict_mem measurableSet_Ioo] with x hx hp hmem
  have hcw := abs_collarWave_add_half_wallPotential_le hd hmem.1
  have e : (criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
      ((1 / 2 * wallPotential F x : ℝ) : ℂ) =
      ((collarWave F x + 1 / 2 * wallPotential F x : ℝ) : ℂ) -
        ∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ) := by
    rw [hx]
    push_cast
    ring
  have h1 : Real.exp (x / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [hmem.2])
  have h2 : Real.exp (2 * x) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith [hmem.2])
  calc ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ)‖
      = ‖((collarWave F x + 1 / 2 * wallPotential F x : ℝ) : ℂ) -
          ∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖ := by rw [e]
    _ ≤ ‖((collarWave F x + 1 / 2 * wallPotential F x : ℝ) : ℂ)‖ +
          ‖∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 3 * Real.exp (x / 2) * (∫ u, |F u| * Real.exp (-(1 / 2) * u)) +
          C * Real.exp (2 * x) *
            ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add hcw hp
    _ ≤ 3 * Real.exp (1 / 2) * (∫ u, |F u| * Real.exp (-(1 / 2) * u)) +
          C * Real.exp 2 *
            ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hI)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hS)

/-- The pairing of the profile beyond the wall with a translated profile only sees `(0, k)`. -/
theorem beyondWallPairing_translate_eq_setIntegral (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (k : ℝ) :
    beyondWallPairing W₀ hF (cx fun x => F (x - k)) =
      ∫ x in Ioo (0 : ℝ) k, (F (x - k) : ℂ) * beyondWallProfile W₀ hF x := by
  unfold beyondWallPairing
  show (∫ x in Ioi (0 : ℝ), ((F (x - k) : ℝ) : ℂ) * beyondWallProfile W₀ hF x) = _
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
    fun x hx => ?_
  have hxk : k ≤ x := by
    by_contra h
    exact hx.2 ⟨hx.1, not_le.mp h⟩
  rw [hF.support (x - k) (by linarith), Complex.ofReal_zero, zero_mul]

/-- **The wall pairing through the potential.** If `|a F⁺ + Φ/2| ≤ B` on `(0, 1)` and `k ≤ 1`,
then `|a ∫_0^k F⁺(x) F(x − k) dx + ½ ∫_0^k Φ(x) F(x − k) dx| ≤ B ∫_0^k |F(x − k)| dx`. -/
theorem norm_wallPairing_add_half_wallPotential_le (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {B : ℝ}
    (hBae : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ)‖ ≤ B)
    {C : ℝ} (hb : ∀ᵐ u : ℝ, |F u| ≤ C) {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallPairing W₀ hF (cx fun x => F (x - k)) +
        (1 / 2 : ℂ) * ((∫ x in Ioo (0 : ℝ) k, F (x - k) * wallPotential F x : ℝ) : ℂ)‖ ≤
      B * ∫ x in Ioo (0 : ℝ) k, |F (x - k)| := by
  have hFkm : Measurable fun x : ℝ => F (x - k) := hF.meas.comp (measurable_id.sub_const k)
  have hFk : IntegrableOn (fun x => F (x - k)) (Ioo (0 : ℝ) k) :=
    (hF.integrable.comp_sub_right k).integrableOn
  have hint2 := integrableOn_translate_mul_wallPotential hF.meas hF.integrable hb hk
  have hPm : AEStronglyMeasurable (beyondWallProfile W₀ hF) (volume.restrict (Ioo (0 : ℝ) k)) :=
    (aestronglyMeasurable_beyondWallProfile W₀ hF).mono_measure
      (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
  have hint1 : IntegrableOn (fun x => (F (x - k) : ℂ) * beyondWallProfile W₀ hF x)
      (Ioo (0 : ℝ) k) := by
    have hdom : IntegrableOn (fun x : ℝ => F (x - k) ^ 2 + ‖beyondWallProfile W₀ hF x‖ ^ 2)
        (Ioo (0 : ℝ) k) :=
      ((hF.sq.comp_sub_right k).integrableOn).add (integrableOn_sq_beyondWallProfile W₀ hF k)
    refine Integrable.mono' hdom
      ((Complex.measurable_ofReal.comp hFkm).aestronglyMeasurable.mul hPm)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|F (x - k)| - ‖beyondWallProfile W₀ hF x‖), sq_abs (F (x - k)),
      mul_nonneg (abs_nonneg (F (x - k))) (norm_nonneg (beyondWallProfile W₀ hF x))]
  have hcast : (∫ x in Ioo (0 : ℝ) k, ((F (x - k) * wallPotential F x : ℝ) : ℂ)) =
      ((∫ x in Ioo (0 : ℝ) k, F (x - k) * wallPotential F x : ℝ) : ℂ) := integral_ofReal
  have hint2c : IntegrableOn (fun x => ((F (x - k) * wallPotential F x : ℝ) : ℂ))
      (Ioo (0 : ℝ) k) := hint2.ofReal
  have hcomb : (criticalAliasCoefficient W₀ : ℂ) *
        (∫ x in Ioo (0 : ℝ) k, (F (x - k) : ℂ) * beyondWallProfile W₀ hF x) +
      (1 / 2 : ℂ) * ((∫ x in Ioo (0 : ℝ) k, F (x - k) * wallPotential F x : ℝ) : ℂ) =
      ∫ x in Ioo (0 : ℝ) k, (F (x - k) : ℂ) *
        ((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x +
          ((1 / 2 * wallPotential F x : ℝ) : ℂ)) := by
    rw [← hcast, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint1.const_mul _) (hint2c.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (criticalAliasCoefficient W₀ : ℂ) * ((F (x - k) : ℂ) * beyondWallProfile W₀ hF x) +
        (1 / 2 : ℂ) * ((F (x - k) * wallPotential F x : ℝ) : ℂ) =
      (F (x - k) : ℂ) * ((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ))
    push_cast
    ring
  rw [beyondWallPairing_translate_eq_setIntegral, hcomb]
  have hle : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) k)),
      ‖(F (x - k) : ℂ) * ((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ))‖ ≤ B * |F (x - k)| := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hk1) hBae]
      with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have h := norm_integral_le_of_norm_le (hFk.abs.const_mul B) hle
  rwa [integral_const_mul] at h

theorem wall_error_identity (m L J k : ℝ) (a P : ℂ) (hk : (k : ℂ) ≠ 0) :
    ((m / k * L : ℝ) : ℂ) - -(2 * a) * (P / (k : ℂ)) =
      (k : ℂ)⁻¹ * (((m * L - J : ℝ) : ℂ) +
        ((a * P + (1 / 2 : ℂ) * (J : ℂ)) + (a * P + (1 / 2 : ℂ) * (J : ℂ)))) := by
  push_cast
  field_simp
  ring

/-! ### The law of the wall -/

theorem criticalState_exponentialMass_pos {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : 0 < ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
  have ha := criticalAliasCoefficient_positive hW
  have hneg := criticalState_zeroNorm_limit_neg hW hF
  by_contra h
  linarith [mul_nonneg ha.le (neg_nonneg.mpr (not_lt.mp h))]

/-- The root mean square of the state on `(−k, 0)` tends to zero with `k`. -/
theorem criticalState_tendsto_terminalRootMeanSquare {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (terminalRootMeanSquare F) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (criticalState_terminal_average_tendsto_zero hW hthreshold hF)
  rw [Real.sqrt_zero] at h
  exact h

/-- **The law of the wall.** For the critical state,
`(k⁻¹ ∫_{−k}^0 F) · ∫_{v>k} F(−v)/v dv → 16 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem criticalState_tendsto_terminalMean_mul_wallLogMoment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => (∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k) (𝓝[>] 0)
      (𝓝 (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC, hbexp⟩ := (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).1 2
    (by norm_num) (by norm_num)
  have hb : ∀ᵐ u : ℝ, |F u| ≤ C := by
    filter_upwards [hbexp] with u hu
    rcases le_or_gt 0 u with h0 | h0
    · rw [hd.support u h0, abs_zero]
      exact hC
    · have h1 : Real.exp (2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      exact hu.trans (by nlinarith)
  obtain ⟨B, hB, hBae⟩ :=
    criticalState_exists_ae_norm_beyondWall_add_wallPotential_le hW hthreshold hF
  have hT := criticalState_tendsto_terminalRootMeanSquare hW hthreshold hF
  have hP := criticalState_tendsto_beyondWallPairing_div hW hthreshold hF
  have hmain : ∀ᶠ k : ℝ in 𝓝[>] 0,
      ‖(((∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k : ℝ) : ℂ) -
        -(2 * (criticalAliasCoefficient W₀ : ℂ)) *
          (beyondWallPairing W₀ hd (cx fun x => F (x - k)) / (k : ℂ))‖ ≤
        (2 * B + 7 * C) * terminalRootMeanSquare F k := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk hk1
    have hk0 : (0 : ℝ) < k := hk
    have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk0.ne'
    have e1 := norm_wallPairing_add_half_wallPotential_le W₀ hd hBae hb hk0 (le_of_lt hk1)
    have e2 := abs_integral_translate_mul_wallPotential_sub_le hd.meas hd.integrable hd.sq hC hb hk0
    have e3 := integral_abs_translate_le hd.meas hd.sq hk0
    have hn1 : ‖(((∫ u in Ioo (-k) 0, F u) * wallLogMoment F k -
        ∫ x in Ioo (0 : ℝ) k, F (x - k) * wallPotential F x : ℝ) : ℂ)‖ ≤
        7 * C * (k * terminalRootMeanSquare F k) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact e2
    have hn2 := e1.trans (mul_le_mul_of_nonneg_left e3 hB)
    rw [wall_error_identity _ _ (∫ x in Ioo (0 : ℝ) k, F (x - k) * wallPotential F x) _ _ _ hkc,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hk0.le]
    have hsum := (norm_add_le _ _).trans (add_le_add hn1 ((norm_add_le _ _).trans
      (add_le_add hn2 hn2)))
    calc k⁻¹ * _ ≤ k⁻¹ * (7 * C * (k * terminalRootMeanSquare F k) +
          (B * (k * terminalRootMeanSquare F k) + B * (k * terminalRootMeanSquare F k))) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hk0.le)
      _ = (2 * B + 7 * C) * terminalRootMeanSquare F k := by
          field_simp
          ring
  have hzero : Tendsto (fun k : ℝ => (2 * B + 7 * C) * terminalRootMeanSquare F k) (𝓝[>] 0)
      (𝓝 0) := by
    have h := hT.const_mul (2 * B + 7 * C)
    rwa [mul_zero] at h
  have hsum := (squeeze_zero_norm' hmain hzero).add
    (hP.const_mul (-(2 * (criticalAliasCoefficient W₀ : ℂ))))
  have hval : (0 : ℂ) + -(2 * (criticalAliasCoefficient W₀ : ℂ)) *
      ((-(8 * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ) =
      ((16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval] at hsum
  have hre := (Complex.continuous_re.tendsto _).comp (hsum.congr fun k => sub_add_cancel _ _)
  rw [Complex.ofReal_re] at hre
  exact hre.congr fun k => Complex.ofReal_re _

/-- For every small `k > 0` the terminal mass and the logarithmic moment have the same sign. -/
theorem criticalState_eventually_terminalMean_mul_wallLogMoment_pos {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∀ᶠ k : ℝ in 𝓝[>] 0, 0 < (∫ u in Ioo (-k) 0, F u) * wallLogMoment F k := by
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  have hlim := criticalState_tendsto_terminalMean_mul_wallLogMoment hW hthreshold hF
  filter_upwards [hlim.eventually (lt_mem_nhds (mul_pos (mul_pos (by norm_num) ha) hM)),
    self_mem_nhdsWithin] with k hk hk0
  have hk0' : (0 : ℝ) < k := hk0
  have e : (∫ u in Ioo (-k) 0, F u) * wallLogMoment F k =
      k * ((∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k) := by
    field_simp
  rw [e]
  exact mul_pos hk0' hk

/-- **The state has one sign at the wall in the mean.** There is a sign `s = ±1` such that for
every small `k > 0` both `s ∫_{−k}^0 F > 0` and `s ∫_{v>k} F(−v)/v dv > 0`. -/
theorem criticalState_exists_sign_at_wall {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ᶠ k : ℝ in 𝓝[>] 0,
      0 < s * ∫ u in Ioo (-k) 0, F u ∧ 0 < s * wallLogMoment F k := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hpos := criticalState_eventually_terminalMean_mul_wallLogMoment_pos hW hthreshold hF
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpos)
  have hprod : ∀ k : ℝ, 0 < k → k < δ →
      0 < (∫ u in Ioo (-k) 0, F u) * wallLogMoment F k := by
    intro k hk hkδ
    exact hδP (by rw [Real.dist_eq, sub_zero, abs_of_pos hk]; exact hkδ) hk
  have hcont : ContinuousOn (wallLogMoment F) (Ioo (0 : ℝ) δ) :=
    (continuousOn_wallLogMoment hd.meas hd.integrable).mono Ioo_subset_Ioi_self
  have hne : ∀ k ∈ Ioo (0 : ℝ) δ, wallLogMoment F k ≠ 0 := by
    intro k hk h0
    have h := hprod k hk.1 hk.2
    rw [h0, mul_zero] at h
    exact lt_irrefl _ h
  have hk₀ : δ / 2 ∈ Ioo (0 : ℝ) δ := ⟨by positivity, by linarith⟩
  have hev : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ k ∈ Ioo (0 : ℝ) δ, 0 < s * wallLogMoment F k) →
      ∀ᶠ k : ℝ in 𝓝[>] 0, 0 < s * ∫ u in Ioo (-k) 0, F u ∧ 0 < s * wallLogMoment F k := by
    intro s hs1 hs
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)]
      with k hk hkδ
    have hL := hs k ⟨hk, hkδ⟩
    have hp := hprod k hk hkδ
    have hsq : (s * ∫ u in Ioo (-k) 0, F u) * (s * wallLogMoment F k) =
        (∫ u in Ioo (-k) 0, F u) * wallLogMoment F k := by
      rcases hs1 with h | h <;> rw [h] <;> ring
    rw [← hsq] at hp
    exact ⟨(pos_iff_pos_of_mul_pos hp).mpr hL, hL⟩
  rcases lt_or_gt_of_ne (hne _ hk₀) with hneg | hposL
  · refine ⟨-1, Or.inr rfl, hev (-1) (Or.inr rfl) fun k hk => ?_⟩
    by_contra hcon
    have hLk : 0 < wallLogMoment F k :=
      lt_of_le_of_ne (by linarith [not_lt.mp hcon]) (Ne.symm (hne k hk))
    obtain ⟨c, hc, hc0⟩ := isPreconnected_Ioo.intermediate_value hk₀ hk hcont
      ⟨hneg.le, hLk.le⟩
    exact hne c hc hc0
  · refine ⟨1, Or.inl rfl, hev 1 (Or.inl rfl) fun k hk => ?_⟩
    by_contra hcon
    have hLk : wallLogMoment F k < 0 :=
      lt_of_le_of_ne (by linarith [not_lt.mp hcon]) (hne k hk)
    obtain ⟨c, hc, hc0⟩ := isPreconnected_Ioo.intermediate_value hk hk₀ hcont
      ⟨hLk.le, hposL.le⟩
    exact hne c hc hc0

/-! ### Logarithmic rates at the wall -/

/-- **The logarithmic moment diverges.** `(∫_{v>k} F(−v)/v dv)² ≥ c log(2/k)` for small `k`. -/
theorem criticalState_eventually_log_le_sq_wallLogMoment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℝ in 𝓝[>] 0, c * Real.log (2 / k) ≤ wallLogMoment F k ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  obtain ⟨C₀, hC₀, hlog⟩ := criticalState_terminal_square_mass_logarithmic_gain hW hthreshold hF
  have hlim := criticalState_tendsto_terminalMean_mul_wallLogMoment hW hthreshold hF
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 16 * criticalAliasCoefficient W₀ *
      ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  rw [← hℓ] at hlim
  have hℓ0 : 0 < ℓ := by
    rw [hℓ]
    exact mul_pos (mul_pos (by norm_num) ha) hM
  refine ⟨(ℓ / 2) ^ 2 / C₀, by positivity, ?_⟩
  filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hℓ0)), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk hk0 hk1
  have hk0' : (0 : ℝ) < k := hk0
  have hk1' : k < 1 := hk1
  have hlog0 : 0 ≤ Real.log (2 / k) :=
    Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith)
  have hcs := sq_setIntegral_Ioo_le hd.meas hd.sq hk0'.le
  have hm := hlog k hk0' hk1'.le
  have h1 : (ℓ / 2) ^ 2 ≤ ((∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hk.le 2
  have h2 : Real.log (2 / k) * ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 ≤ C₀ := by
    have h3 : Real.log (2 / k) * (∫ u in Ioo (-k) 0, F u) ^ 2 ≤ C₀ * k ^ 2 := by
      calc Real.log (2 / k) * (∫ u in Ioo (-k) 0, F u) ^ 2
          ≤ Real.log (2 / k) * (k * ∫ u in Ioo (-k) 0, F u ^ 2) :=
            mul_le_mul_of_nonneg_left hcs hlog0
        _ = k * (Real.log (2 / k) * ∫ u in Ioo (-k) 0, F u ^ 2) := by ring
        _ ≤ k * (C₀ * k) := mul_le_mul_of_nonneg_left hm hk0'.le
        _ = C₀ * k ^ 2 := by ring
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    exact h3
  rw [div_mul_eq_mul_div, div_le_iff₀ hC₀]
  calc (ℓ / 2) ^ 2 * Real.log (2 / k)
      ≤ ((∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k) ^ 2 * Real.log (2 / k) :=
        mul_le_mul_of_nonneg_right h1 hlog0
    _ = wallLogMoment F k ^ 2 * (Real.log (2 / k) * ((∫ u in Ioo (-k) 0, F u) / k) ^ 2) := by
        ring
    _ ≤ wallLogMoment F k ^ 2 * C₀ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- **The prime side is logarithmically large at the wall.** `∫_0^k |F⁺|² ≥ c k log(2/k)` for
small `k`: the uncertainty inequality at the wall against the logarithmic gain of the terminal
mass of the state. -/
theorem criticalState_eventually_log_le_integral_sq_beyondWallProfile {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℝ in 𝓝[>] 0, c * (k * Real.log (2 / k)) ≤
      ∫ x in Ioo (0 : ℝ) k,
        ‖beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x‖ ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hM := criticalState_exponentialMass_pos hW hF
  obtain ⟨C₀, hC₀, hlog⟩ := criticalState_terminal_square_mass_logarithmic_gain hW hthreshold hF
  have hA : Tendsto (fun k : ℝ => criticalHalfLineExponentialPair F (fun u => F (u + k)))
      (𝓝[>] 0) (𝓝 (criticalHalfLineExponentialPair F (fun u => F (u + 0)))) :=
    ((continuous_exponentialPair_translate hd).tendsto 0).mono_left nhdsWithin_le_nhds
  have e0 : criticalHalfLineExponentialPair F (fun u => F (u + 0)) =
      ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
    simp only [add_zero]
    exact criticalHalfLineExponentialPair_self F
  rw [e0] at hA
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  rw [← hMdef] at hA hM
  refine ⟨4 * M ^ 2 / C₀, by positivity, ?_⟩
  filter_upwards [hA.eventually (lt_mem_nhds (half_lt_self hM)), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))]
    with k hAk hk0 hk8
  have hk0' : (0 : ℝ) < k := hk0
  have hk8' : k < 1 / 8 := hk8
  have hlog0 : 0 ≤ Real.log (2 / k) :=
    Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith)
  have hu := criticalState_wall_uncertainty hW hthreshold hF hk0'.le
  have hm := hlog k hk0' (by linarith)
  have hexp : 4 * k ≤ 1 - Real.exp (-(8 * k)) := by
    have h := Real.add_one_le_exp (8 * k)
    have e : Real.exp (-(8 * k)) * Real.exp (8 * k) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hpos := Real.exp_pos (-(8 * k))
    have h1 : Real.exp (-(8 * k)) * (8 * k + 1) ≤ 1 := by
      have h' := mul_le_mul_of_nonneg_left h hpos.le
      rwa [e] at h'
    have h2 : (1 : ℝ) ≤ (1 - 4 * k) * (8 * k + 1) := by nlinarith
    have h3 := le_of_mul_le_mul_right (h1.trans h2) (by linarith : (0 : ℝ) < 8 * k + 1)
    linarith
  have hI : 0 ≤ ∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hprod : 4 * k * (M / 2) ≤ (1 - Real.exp (-(8 * k))) *
      criticalHalfLineExponentialPair F (fun u => F (u + k)) :=
    mul_le_mul hexp hAk.le (by positivity) (by linarith)
  have hsq := (pow_le_pow_left₀ (by positivity) hprod 2).trans hu
  have h3 : (4 * k * (M / 2)) ^ 2 * Real.log (2 / k) ≤
      (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) * (C₀ * k) := by
    calc (4 * k * (M / 2)) ^ 2 * Real.log (2 / k)
        ≤ (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) *
            (∫ u in Ioo (-k) 0, F u ^ 2) * Real.log (2 / k) :=
          mul_le_mul_of_nonneg_right hsq hlog0
      _ = (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) *
            (Real.log (2 / k) * ∫ u in Ioo (-k) 0, F u ^ 2) := by ring
      _ ≤ (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) * (C₀ * k) :=
          mul_le_mul_of_nonneg_left hm hI
  rw [div_mul_eq_mul_div, div_le_iff₀ hC₀]
  have h4 : 4 * M ^ 2 * (k * Real.log (2 / k)) * k ≤
      (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) * C₀ * k := by
    calc 4 * M ^ 2 * (k * Real.log (2 / k)) * k
        = (4 * k * (M / 2)) ^ 2 * Real.log (2 / k) := by ring
      _ ≤ (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) * (C₀ * k) := h3
      _ = (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) * C₀ * k := by ring
  exact le_of_mul_le_mul_right h4 hk0'

end GaloisForLFunctions.ExclusionOfTheCriticalState
