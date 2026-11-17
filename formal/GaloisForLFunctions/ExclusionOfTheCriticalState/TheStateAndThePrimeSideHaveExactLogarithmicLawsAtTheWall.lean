import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasOneSignAtTheWallInTheMean

/-!
# The state and the prime side have exact logarithmic laws at the wall

Let `F` be the critical state, `a` the alias coefficient, `M = ∫ F² e^{−8u}`, `F⁺` the profile
beyond the wall, `μ(k) = k⁻¹ ∫_{−k}^0 F` the terminal mean and `L(k) = ∫_{v>k} F(−v)/v dv` the
logarithmic moment. With the sign `s = ±1` of the state at the wall:

* `L(k)² / log(1/k) → 32 a M` (`criticalState_tendsto_sq_wallLogMoment_div_log`);
* `μ(k)² log(1/k) → 8 a M` (`criticalState_tendsto_sq_terminalMean_mul_log`);
* `μ(k) √log(1/k) → s √(8aM)` and `L(k) / √log(1/k) → 2s √(8aM)` (`criticalState_wall_laws`);
* `|a F⁺(x) + L(x)/2| ≤ B` for almost every `0 < x < 1`
  (`criticalState_exists_ae_norm_beyondWall_add_wallLogMoment_le`), hence
  `a F⁺(x) / √log(1/x) → −s √(8aM)` essentially as `x → 0⁺` (`criticalState_wall_laws`);
* `∫_{−k}^0 F² ≥ c k / log(2/k)` for small `k`
  (`criticalState_eventually_le_log_mul_terminal_square_mass`): the logarithmic gain of the terminal
  mass is sharp.

Mechanism. Fubini on `v < h` gives `L(k) = R(k) − μ(k)` with
`R(k) = ∫_{h>k} (∫_{−h}^0 F) h⁻² dh`, a differentiable function with `R′(k) = −μ(k)/k`. The law of the
wall `μ L → 16 a M` and `μ → 0` give `R μ → ℓ = 16 a M`. Then `(R² + 2c log k)′ = −2(Rμ − c)/k` has
a sign near `0⁺` for every `c ≠ ℓ`, so `R² / log(1/k) → 2ℓ`; the same holds for `L`, and
`μ² log(1/k) = (μL)² / (L² / log(1/k)) → ℓ/2`. On the prime side, `a F⁺ = −Φ/2 + O(1)` with the
Stieltjes potential `Φ`, and `|Φ(x) − L(x)| ≤ 5C`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Integration by parts against a tail weight -/

/-- **Integration by parts against a tail weight** (Fubini on the region `v < h`):
`∫_{v>k} f(v) (∫_{h>v} w) dv = ∫_{h>k} (∫_k^h f) w(h) dh`. -/
theorem integral_Ioi_mul_integral_Ioi_eq {f w : ℝ → ℝ} {k : ℝ} (hf : IntegrableOn f (Ioi k))
    (hw : IntegrableOn w (Ioi k)) :
    ∫ v in Ioi k, f v * (∫ h in Ioi v, w h) = ∫ h in Ioi k, (∫ v in Ioo k h, f v) * w h := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ × ℝ → ℝ,
      G = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * w p.2) := ⟨_, rfl⟩
  have hGi : Integrable G ((volume.restrict (Ioi k)).prod (volume.restrict (Ioi k))) := by
    rw [hG]
    exact (Integrable.mul_prod hf hw).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hG1 : ∀ v h : ℝ, G (v, h) = (Ioi v).indicator (fun h => f v * w h) h := by
    intro v h
    rw [hG]
    by_cases hvh : v < h
    · rw [Set.indicator_of_mem (show (v, h) ∈ {p : ℝ × ℝ | p.1 < p.2} from hvh),
        Set.indicator_of_mem (show h ∈ Ioi v from hvh)]
    · rw [Set.indicator_of_notMem (show (v, h) ∉ {p : ℝ × ℝ | p.1 < p.2} from hvh),
        Set.indicator_of_notMem (show h ∉ Ioi v from hvh)]
  have hG2 : ∀ v h : ℝ, G (v, h) = (Iio h).indicator (fun v => f v * w h) v := by
    intro v h
    rw [hG]
    by_cases hvh : v < h
    · rw [Set.indicator_of_mem (show (v, h) ∈ {p : ℝ × ℝ | p.1 < p.2} from hvh),
        Set.indicator_of_mem (show v ∈ Iio h from hvh)]
    · rw [Set.indicator_of_notMem (show (v, h) ∉ {p : ℝ × ℝ | p.1 < p.2} from hvh),
        Set.indicator_of_notMem (show v ∉ Iio h from hvh)]
  have hl : ∀ v ∈ Ioi k, (∫ h in Ioi k, G (v, h)) = f v * ∫ h in Ioi v, w h := by
    intro v hv
    simp only [hG1]
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi (le_of_lt hv)),
      integral_const_mul]
  have hr : ∀ h ∈ Ioi k, (∫ v in Ioi k, G (v, h)) = (∫ v in Ioo k h, f v) * w h := by
    intro h _
    simp only [hG2]
    rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, integral_mul_const]
  calc ∫ v in Ioi k, f v * (∫ h in Ioi v, w h)
      = ∫ v in Ioi k, ∫ h in Ioi k, G (v, h) := (setIntegral_congr_fun measurableSet_Ioi hl).symm
    _ = ∫ h in Ioi k, ∫ v in Ioi k, G (v, h) := integral_integral_swap hGi
    _ = ∫ h in Ioi k, (∫ v in Ioo k h, f v) * w h := setIntegral_congr_fun measurableSet_Ioi hr

/-! ### The terminal mass as a primitive -/

theorem setIntegral_Ioo_neg (g : ℝ → ℝ) (a b : ℝ) :
    ∫ v in Ioo a b, g (-v) = ∫ u in Ioo (-b) (-a), g u := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo,
    ← integral_neg_eq_self (fun u : ℝ => Set.indicator (Ioo (-b) (-a)) g u) volume]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  show Set.indicator (Ioo a b) (fun v => g (-v)) v = Set.indicator (Ioo (-b) (-a)) g (-v)
  by_cases hv : v ∈ Ioo a b
  · have hv' : -v ∈ Ioo (-b) (-a) := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv']
  · have hv' : -v ∉ Ioo (-b) (-a) := fun h => hv ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']

/-- The signed terminal mass `∫_{−h}^0 F` is the primitive of the reflected profile. -/
theorem terminalMass_eq_intervalIntegral (F : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ u in Ioo (-h) 0, F u = ∫ v in (0 : ℝ)..h, F (-v) := by
  rw [intervalIntegral.integral_of_le hh, integral_Ioc_eq_integral_Ioo, setIntegral_Ioo_neg F 0 h,
    neg_zero]

theorem continuousOn_terminalMass {F : ℝ → ℝ} (hFi : Integrable F) :
    ContinuousOn (fun h : ℝ => ∫ u in Ioo (-h) 0, F u) (Ici 0) := by
  have hc : Continuous fun h : ℝ => ∫ v in (0 : ℝ)..h, F (-v) :=
    intervalIntegral.continuous_primitive (fun a b => hFi.comp_neg.intervalIntegrable) 0
  exact hc.continuousOn.congr fun h hh => terminalMass_eq_intervalIntegral F hh

theorem abs_terminalMass_le {F : ℝ → ℝ} (hFi : Integrable F) (h : ℝ) :
    |∫ u in Ioo (-h) 0, F u| ≤ ∫ u, |F u| :=
  abs_integral_le_integral_abs.trans
    (setIntegral_le_integral hFi.abs (Eventually.of_forall fun _ => abs_nonneg _))

theorem setIntegral_Ioo_neg_eq_sub {F : ℝ → ℝ} (hFi : Integrable F) {k h : ℝ} (hk : 0 ≤ k)
    (hkh : k ≤ h) :
    ∫ v in Ioo k h, F (-v) = (∫ u in Ioo (-h) 0, F u) - ∫ u in Ioo (-k) 0, F u := by
  have hfi : Integrable fun v : ℝ => F (-v) := hFi.comp_neg
  rw [terminalMass_eq_intervalIntegral F (hk.trans hkh), terminalMass_eq_intervalIntegral F hk,
    intervalIntegral.integral_interval_sub_left hfi.intervalIntegrable hfi.intervalIntegrable,
    intervalIntegral.integral_of_le hkh, integral_Ioc_eq_integral_Ioo]

theorem rpow_neg_two_eq_inv_sq {h : ℝ} (hh : 0 < h) : h ^ (-(2 : ℝ)) = (h ^ 2)⁻¹ := by
  rw [Real.rpow_neg hh.le, Real.rpow_two]

/-! ### The moment of the terminal means -/

/-- The moment of the terminal means: `R_F(k) = ∫_{h>k} (∫_{−h}^0 F) h⁻² dh`. -/
def wallMeanMoment (F : ℝ → ℝ) (k : ℝ) : ℝ := ∫ h in Ioi k, (∫ u in Ioo (-h) 0, F u) / h ^ 2

theorem continuousOn_terminalMass_div_sq {F : ℝ → ℝ} (hFi : Integrable F) :
    ContinuousOn (fun h : ℝ => (∫ u in Ioo (-h) 0, F u) / h ^ 2) (Ioi 0) :=
  ((continuousOn_terminalMass hFi).mono Ioi_subset_Ici_self).div
    (continuous_id.pow 2).continuousOn fun _ hh => pow_ne_zero 2 (ne_of_gt hh)

theorem integrableOn_terminalMass_div_sq {F : ℝ → ℝ} (hFi : Integrable F) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun h : ℝ => (∫ u in Ioo (-h) 0, F u) / h ^ 2) (Ioi k) := by
  have hdom : IntegrableOn (fun h : ℝ => (∫ u, |F u|) * h ^ (-(2 : ℝ))) (Ioi k) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hk).const_mul _
  refine Integrable.mono' hdom (((continuousOn_terminalMass_div_sq hFi).mono
    (Ioi_subset_Ioi hk.le)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : 0 < h := hk.trans hh
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hh0 2), div_eq_mul_inv, rpow_neg_two_eq_inv_sq hh0]
  exact mul_le_mul_of_nonneg_right (abs_terminalMass_le hFi h) (inv_nonneg.mpr (pow_pos hh0 2).le)

/-- **The logarithmic moment is the moment of the terminal means minus the terminal mean**:
`∫_{v>k} F(−v)/v dv = ∫_{h>k} (∫_{−h}^0 F) h⁻² dh − k⁻¹ ∫_{−k}^0 F`. -/
theorem wallLogMoment_eq_wallMeanMoment_sub {F : ℝ → ℝ} (hFi : Integrable F) {k : ℝ}
    (hk : 0 < k) :
    wallLogMoment F k = wallMeanMoment F k - (∫ u in Ioo (-k) 0, F u) / k := by
  have hfi : Integrable fun v : ℝ => F (-v) := hFi.comp_neg
  have hw : IntegrableOn (fun h : ℝ => h ^ (-(2 : ℝ))) (Ioi k) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hk
  have hswap := integral_Ioi_mul_integral_Ioi_eq (f := fun v => F (-v))
    (w := fun h => h ^ (-(2 : ℝ))) hfi.integrableOn hw
  have hL : wallLogMoment F k = ∫ v in Ioi k, F (-v) * ∫ h in Ioi v, h ^ (-(2 : ℝ)) := by
    unfold wallLogMoment
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    show F (-v) / v = F (-v) * ∫ h in Ioi v, h ^ (-(2 : ℝ))
    rw [integral_Ioi_rpow_neg_two_eq_inv (hk.trans hv), div_eq_mul_inv]
  have hinner : ∀ h ∈ Ioi k, (∫ v in Ioo k h, F (-v)) * h ^ (-(2 : ℝ)) =
      (∫ u in Ioo (-h) 0, F u) / h ^ 2 - (∫ u in Ioo (-k) 0, F u) * h ^ (-(2 : ℝ)) := by
    intro h hh
    rw [setIntegral_Ioo_neg_eq_sub hFi hk.le (le_of_lt hh), sub_mul,
      rpow_neg_two_eq_inv_sq (hk.trans hh), div_eq_mul_inv]
  unfold wallMeanMoment
  rw [hL, hswap, setIntegral_congr_fun measurableSet_Ioi hinner,
    integral_sub (integrableOn_terminalMass_div_sq hFi hk) (hw.const_mul _), integral_const_mul,
    integral_Ioi_rpow_neg_two_eq_inv hk, div_eq_mul_inv]

/-- The moment of the terminal means is differentiable: `R′(k) = −k⁻² ∫_{−k}^0 F`. -/
theorem hasDerivAt_wallMeanMoment {F : ℝ → ℝ} (hFi : Integrable F) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (wallMeanMoment F) (-((∫ u in Ioo (-k) 0, F u) / k ^ 2)) k := by
  have hc : 0 < k / 2 := by positivity
  have hck : k / 2 < k := half_lt_self hk
  have hgc := continuousOn_terminalMass_div_sq hFi
  have hgi := integrableOn_terminalMass_div_sq hFi hc
  have heq : ∀ x : ℝ, k / 2 < x → wallMeanMoment F x = wallMeanMoment F (k / 2) -
      ∫ h in (k / 2)..x, (∫ u in Ioo (-h) 0, F u) / h ^ 2 := by
    intro x hx
    have h2 : (∫ h in Ioi (k / 2), (∫ u in Ioo (-h) 0, F u) / h ^ 2) =
        (∫ h in Ioc (k / 2) x, (∫ u in Ioo (-h) 0, F u) / h ^ 2) +
          ∫ h in Ioi x, (∫ u in Ioo (-h) 0, F u) / h ^ 2 := by
      rw [← Ioc_union_Ioi_eq_Ioi hx.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi (hgi.mono_set Ioc_subset_Ioi_self) (hgi.mono_set (Ioi_subset_Ioi hx.le))]
    unfold wallMeanMoment
    rw [intervalIntegral.integral_of_le hx.le, h2]
    ring
  have hderiv : HasDerivAt (fun x => ∫ h in (k / 2)..x, (∫ u in Ioo (-h) 0, F u) / h ^ 2)
      ((∫ u in Ioo (-k) 0, F u) / k ^ 2) k :=
    intervalIntegral.integral_hasDerivAt_right
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hck.le).mpr
        (hgi.mono_set Ioc_subset_Ioi_self))
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hgc k hk)
      (hgc.continuousAt (Ioi_mem_nhds hk))
  have h1 : HasDerivAt (fun x => wallMeanMoment F (k / 2) -
      ∫ h in (k / 2)..x, (∫ u in Ioo (-h) 0, F u) / h ^ 2)
      (0 - (∫ u in Ioo (-k) 0, F u) / k ^ 2) k :=
    (hasDerivAt_const k _).sub hderiv
  rw [zero_sub] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hck] with x hx
  exact heq x hx

/-! ### A logarithmic growth law -/

theorem tendsto_log_one_div_nhdsGT_zero :
    Tendsto (fun k : ℝ => Real.log (1 / k)) (𝓝[>] 0) atTop :=
  (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun k => by
    show -Real.log k = Real.log (1 / k)
    rw [one_div, Real.log_inv]

theorem hasDerivAt_mul_self_add_log {R m : ℝ → ℝ} {c k : ℝ} (hk : 0 < k)
    (hR : HasDerivAt R (-(m k / k)) k) :
    HasDerivAt (fun x => R x * R x + 2 * c * Real.log x) (-(2 * (R k * m k - c) / k)) k := by
  have h : HasDerivAt (fun x => R x * R x + 2 * c * Real.log x)
      (-(m k / k) * R k + R k * -(m k / k) + 2 * c * k⁻¹) k :=
    (hR.mul hR).add ((Real.hasDerivAt_log hk.ne').const_mul (2 * c))
  have e : -(m k / k) * R k + R k * -(m k / k) + 2 * c * k⁻¹ = -(2 * (R k * m k - c) / k) := by
    simp only [div_eq_mul_inv]
    ring
  rwa [e] at h

/-- If `R′ = −m/k` and `c ≤ R m` on `(0, δ)`, then `R² + 2c log k` decreases there. -/
theorem antitoneOn_sq_add_log {R m : ℝ → ℝ} {δ c : ℝ}
    (hR : ∀ k ∈ Ioo (0 : ℝ) δ, HasDerivAt R (-(m k / k)) k)
    (hc : ∀ k ∈ Ioo (0 : ℝ) δ, c ≤ R k * m k) :
    AntitoneOn (fun k => R k * R k + 2 * c * Real.log k) (Ioo 0 δ) := by
  have hd := fun k (hk : k ∈ Ioo (0 : ℝ) δ) => hasDerivAt_mul_self_add_log (c := c) hk.1 (hR k hk)
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 δ)
    (fun k hk => (hd k hk).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Ioo]
    exact fun k hk => (hd k hk).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro k hk
    rw [(hd k hk).deriv]
    exact neg_nonpos.mpr (div_nonneg (by linarith [hc k hk]) hk.1.le)

/-- If `R′ = −m/k` and `R m ≤ c` on `(0, δ)`, then `R² + 2c log k` increases there. -/
theorem monotoneOn_sq_add_log {R m : ℝ → ℝ} {δ c : ℝ}
    (hR : ∀ k ∈ Ioo (0 : ℝ) δ, HasDerivAt R (-(m k / k)) k)
    (hc : ∀ k ∈ Ioo (0 : ℝ) δ, R k * m k ≤ c) :
    MonotoneOn (fun k => R k * R k + 2 * c * Real.log k) (Ioo 0 δ) := by
  have hd := fun k (hk : k ∈ Ioo (0 : ℝ) δ) => hasDerivAt_mul_self_add_log (c := c) hk.1 (hR k hk)
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 δ)
    (fun k hk => (hd k hk).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Ioo]
    exact fun k hk => (hd k hk).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro k hk
    rw [(hd k hk).deriv]
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [hc k hk]) hk.1.le)

/-- **Logarithmic growth law.** If `R′(k) = −m(k)/k` near `0⁺` and `R(k) m(k) → ℓ`, then
`R(k)² / log(1/k) → 2ℓ`: the function `R² + 2c log k` is monotone for every `c ≠ ℓ`. -/
theorem tendsto_sq_div_log_of_hasDerivAt {R m : ℝ → ℝ} {δ ℓ : ℝ} (hδ : 0 < δ)
    (hR : ∀ k ∈ Ioo (0 : ℝ) δ, HasDerivAt R (-(m k / k)) k)
    (hlim : Tendsto (fun k => R k * m k) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun k => R k ^ 2 / Real.log (1 / k)) (𝓝[>] 0) (𝓝 (2 * ℓ)) := by
  have hlog : Tendsto Real.log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsGT_zero
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 * ℓ + a) / 4 := ⟨_, rfl⟩
    have hcℓ : c < ℓ := by rw [hc]; linarith
    have hd : 0 < 2 * c - a := by rw [hc]; linarith
    obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp (hlim.eventually (lt_mem_nhds hcℓ)))
    have hmin : 0 < min η δ := lt_min hη hδ
    have hanti : AntitoneOn (fun k => R k * R k + 2 * c * Real.log k) (Ioo 0 (min η δ)) :=
      antitoneOn_sq_add_log (fun k hk => hR k ⟨hk.1, hk.2.trans_le (min_le_right _ _)⟩)
        fun k hk => (hηP (by
          rw [Real.dist_eq, sub_zero, abs_of_pos hk.1]
          exact hk.2.trans_le (min_le_left _ _)) hk.1).le
    have hk₀ : min η δ / 2 ∈ Ioo (0 : ℝ) (min η δ) := ⟨half_pos hmin, half_lt_self hmin⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hk₀.1),
      hlog.eventually (eventually_lt_atBot (min 0
        ((R (min η δ / 2) * R (min η δ / 2) + 2 * c * Real.log (min η δ / 2)) / (2 * c - a))))]
      with k hk hkk hlk
    have hk0 : (0 : ℝ) < k := hk
    have hkk' : k < min η δ / 2 := hkk
    have hmono : R (min η δ / 2) * R (min η δ / 2) + 2 * c * Real.log (min η δ / 2) ≤
        R k * R k + 2 * c * Real.log k := hanti ⟨hk0, hkk'.trans hk₀.2⟩ hk₀ hkk'.le
    have hl0 : Real.log k < 0 := hlk.trans_le (min_le_left _ _)
    have hl1 := (lt_div_iff₀ hd).mp (hlk.trans_le (min_le_right _ _))
    have hlogpos : 0 < Real.log (1 / k) := by
      rw [one_div, Real.log_inv]
      linarith
    rw [lt_div_iff₀ hlogpos, one_div, Real.log_inv]
    nlinarith [hmono, hl1]
  · obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 * ℓ + b) / 4 := ⟨_, rfl⟩
    have hcℓ : ℓ < c := by rw [hc]; linarith
    have hd : 0 < b - 2 * c := by rw [hc]; linarith
    obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp (hlim.eventually (gt_mem_nhds hcℓ)))
    have hmin : 0 < min η δ := lt_min hη hδ
    have hmon : MonotoneOn (fun k => R k * R k + 2 * c * Real.log k) (Ioo 0 (min η δ)) :=
      monotoneOn_sq_add_log (fun k hk => hR k ⟨hk.1, hk.2.trans_le (min_le_right _ _)⟩)
        fun k hk => (hηP (by
          rw [Real.dist_eq, sub_zero, abs_of_pos hk.1]
          exact hk.2.trans_le (min_le_left _ _)) hk.1).le
    have hk₀ : min η δ / 2 ∈ Ioo (0 : ℝ) (min η δ) := ⟨half_pos hmin, half_lt_self hmin⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hk₀.1),
      hlog.eventually (eventually_lt_atBot (min 0
        (-(R (min η δ / 2) * R (min η δ / 2) + 2 * c * Real.log (min η δ / 2)) / (b - 2 * c))))]
      with k hk hkk hlk
    have hk0 : (0 : ℝ) < k := hk
    have hkk' : k < min η δ / 2 := hkk
    have hmono : R k * R k + 2 * c * Real.log k ≤
        R (min η δ / 2) * R (min η δ / 2) + 2 * c * Real.log (min η δ / 2) :=
      hmon ⟨hk0, hkk'.trans hk₀.2⟩ hk₀ hkk'.le
    have hl0 : Real.log k < 0 := hlk.trans_le (min_le_left _ _)
    have hl1 := (lt_div_iff₀ hd).mp (hlk.trans_le (min_le_right _ _))
    have hlogpos : 0 < Real.log (1 / k) := by
      rw [one_div, Real.log_inv]
      linarith
    rw [div_lt_iff₀ hlogpos, one_div, Real.log_inv]
    nlinarith [hmono, hl1]

/-! ### The critical state at the wall -/

theorem criticalState_exists_ae_abs_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ u : ℝ, |F u| ≤ C := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC, hbexp⟩ := (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).1 2
    (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbexp] with u hu
  rcases le_or_gt 0 u with h0 | h0
  · rw [hd.support u h0, abs_zero]
    exact hC
  · have h1 : Real.exp (2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact hu.trans (by nlinarith)

/-- The terminal mean of the state tends to zero at the wall. -/
theorem criticalState_tendsto_terminalMean {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => (∫ u in Ioo (-k) 0, F u) / k) (𝓝[>] 0) (𝓝 0) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine squeeze_zero_norm' ?_ (criticalState_tendsto_terminalRootMeanSquare hW hthreshold hF)
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : (0 : ℝ) < k := hk
  have hcs := sq_setIntegral_Ioo_le hd.meas hd.sq hk0.le
  rw [← sq_mul_terminalRootMeanSquare F hk0] at hcs
  have h1 := abs_le_of_sq_le_sq hcs (mul_nonneg hk0.le (terminalRootMeanSquare_nonneg F k))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk0, div_le_iff₀ hk0]
  linarith

/-- `R(k) μ(k) → 16 a ∫ F² e^{−8u}`: the law of the wall for the moment of the terminal means. -/
theorem criticalState_tendsto_wallMeanMoment_mul_terminalMean {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => wallMeanMoment F k * ((∫ u in Ioo (-k) 0, F u) / k)) (𝓝[>] 0)
      (𝓝 (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hmean := criticalState_tendsto_terminalMean hW hthreshold hF
  have h := (criticalState_tendsto_terminalMean_mul_wallLogMoment hW hthreshold hF).add
    (hmean.pow 2)
  have e : (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) + 0 ^ 2 = (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [wallLogMoment_eq_wallMeanMoment_sub hd.integrable hk]
  ring

theorem criticalState_tendsto_sq_wallMeanMoment_div_log {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => wallMeanMoment F k ^ 2 / Real.log (1 / k)) (𝓝[>] 0)
      (𝓝 (2 * (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine tendsto_sq_div_log_of_hasDerivAt (m := fun k => (∫ u in Ioo (-k) 0, F u) / k) one_pos
    (fun k hk => ?_) (criticalState_tendsto_wallMeanMoment_mul_terminalMean hW hthreshold hF)
  have h := hasDerivAt_wallMeanMoment hd.integrable hk.1
  have e : (∫ u in Ioo (-k) 0, F u) / k / k = (∫ u in Ioo (-k) 0, F u) / k ^ 2 := by
    rw [div_div, sq]
  show HasDerivAt (wallMeanMoment F) (-((∫ u in Ioo (-k) 0, F u) / k / k)) k
  rw [e]
  exact h

/-- **The logarithmic moment has an exact logarithmic law.**
`(∫_{v>k} F(−v)/v dv)² / log(1/k) → 32 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem criticalState_tendsto_sq_wallLogMoment_div_log {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => wallLogMoment F k ^ 2 / Real.log (1 / k)) (𝓝[>] 0)
      (𝓝 (32 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hmean := criticalState_tendsto_terminalMean hW hthreshold hF
  have hRm := criticalState_tendsto_wallMeanMoment_mul_terminalMean hW hthreshold hF
  have hcorr := ((hRm.const_mul 2).sub (hmean.pow 2)).div_atTop tendsto_log_one_div_nhdsGT_zero
  have h := (criticalState_tendsto_sq_wallMeanMoment_div_log hW hthreshold hF).sub hcorr
  have e : 2 * (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) - 0 = (32 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [wallLogMoment_eq_wallMeanMoment_sub hd.integrable hk]
  ring

/-- **The terminal mean has an exact logarithmic law.**
`(k⁻¹ ∫_{−k}^0 F)² log(1/k) → 8 a ∫ F² e^{−8u}` as `k → 0⁺`. -/
theorem criticalState_tendsto_sq_terminalMean_mul_log {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k)) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  have hne : (32 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) ≠ 0 := (mul_pos (mul_pos (by norm_num) ha) hM).ne'
  have hP := criticalState_tendsto_terminalMean_mul_wallLogMoment hW hthreshold hF
  have h := (hP.pow 2).div (criticalState_tendsto_sq_wallLogMoment_div_log hW hthreshold hF) hne
  have e : (16 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) ^ 2 / (32 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) = (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by
    rw [div_eq_iff hne]
    ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [criticalState_eventually_terminalMean_mul_wallLogMoment_pos hW hthreshold hF,
    self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with k hpos hk hk1
  have hL0 : wallLogMoment F k ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hlg : Real.log (1 / k) ≠ 0 := (Real.log_pos (one_lt_one_div hk hk1)).ne'
  show ((∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k) ^ 2 /
      (wallLogMoment F k ^ 2 / Real.log (1 / k)) =
    ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k)
  generalize (∫ u in Ioo (-k) 0, F u) / k = μ
  field_simp

/-- **The prime side at the wall is minus half the logarithmic moment of the state.** For almost
every `0 < x < 1`, `|a F⁺(x) + ½ ∫_{v>x} F(−v)/v dv| ≤ B`. -/
theorem criticalState_exists_ae_norm_beyondWall_add_wallLogMoment_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ‖(criticalAliasCoefficient W₀ : ℂ) *
          beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x +
        ((1 / 2 * wallLogMoment F x : ℝ) : ℂ)‖ ≤ B := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC, hb⟩ := criticalState_exists_ae_abs_le hW hthreshold hF
  obtain ⟨B, hB, hBae⟩ :=
    criticalState_exists_ae_norm_beyondWall_add_wallPotential_le hW hthreshold hF
  refine ⟨B + 5 / 2 * C, add_nonneg hB (mul_nonneg (by norm_num) hC), ?_⟩
  filter_upwards [hBae, ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hΦ := abs_wallPotential_sub_wallLogMoment_le hd.meas hd.integrable hb hmem.1 le_rfl
  have e1 : x ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hmem.1]
    norm_num
  have e2 : C + 4 * C * x ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) = 5 * C := by
    rw [mul_assoc, e1]
    ring
  rw [e2] at hΦ
  have e : (criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
      ((1 / 2 * wallLogMoment F x : ℝ) : ℂ) =
      ((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ)) -
        ((1 / 2 * (wallPotential F x - wallLogMoment F x) : ℝ) : ℂ) := by
    push_cast
    ring
  have hn : ‖((1 / 2 * (wallPotential F x - wallLogMoment F x) : ℝ) : ℂ)‖ ≤ 5 / 2 * C := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  show ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
      ((1 / 2 * wallLogMoment F x : ℝ) : ℂ)‖ ≤ B + 5 / 2 * C
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add hx hn)

/-- If `L(k)/√log(1/k) → 2c`, then `a F⁺(x)/√log(1/x) → −c` essentially as `x → 0⁺`. -/
theorem criticalState_ae_tendsto_beyondWall_of_wallLogMoment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hL : Tendsto (fun k : ℝ => wallLogMoment F k / Real.sqrt (Real.log (1 / k))) (𝓝[>] 0)
      (𝓝 (2 * c))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
      ‖(criticalAliasCoefficient W₀ : ℂ) *
          beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x /
            ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) + ((c : ℝ) : ℂ)‖ < ε := by
  intro ε hε
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨B, hB, hBae⟩ :=
    criticalState_exists_ae_norm_beyondWall_add_wallLogMoment_le hW hthreshold hF
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.log (1 / x))) (𝓝[>] 0) atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_log_one_div_nhdsGT_zero
  have hB0 : Tendsto (fun x : ℝ => B / Real.sqrt (Real.log (1 / x))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0, B / Real.sqrt (Real.log (1 / x)) < ε / 2 ∧
      dist (wallLogMoment F x / Real.sqrt (Real.log (1 / x))) (2 * c) < ε ∧
        0 < Real.sqrt (Real.log (1 / x)) :=
    (hB0.eventually (gt_mem_nhds (half_pos hε))).and
      ((Metric.tendsto_nhds.mp hL ε hε).and (hsqrt.eventually (eventually_gt_atTop 0)))
  obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl (min_le_right η 1)) hBae,
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  obtain ⟨h1, h2, h3⟩ := hηP (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmem.1]
    exact hmem.2.trans_le (min_le_left _ _)) hmem.1
  rw [Real.dist_eq] at h2
  have hwc : ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h3.ne'
  have e : (criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x /
        ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) + ((c : ℝ) : ℂ) =
      ((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
          ((1 / 2 * wallLogMoment F x : ℝ) : ℂ)) / ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) -
        ((1 / 2 * (wallLogMoment F x / Real.sqrt (Real.log (1 / x)) - 2 * c) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  have hn1 : ‖((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
      ((1 / 2 * wallLogMoment F x : ℝ) : ℂ)) / ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ)‖ ≤
      B / Real.sqrt (Real.log (1 / x)) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h3.le]
    exact div_le_div_of_nonneg_right hx h3.le
  have hn2 : ‖((1 / 2 * (wallLogMoment F x / Real.sqrt (Real.log (1 / x)) - 2 * c) : ℝ) : ℂ)‖ =
      1 / 2 * |wallLogMoment F x / Real.sqrt (Real.log (1 / x)) - 2 * c| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  show ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x /
      ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) + ((c : ℝ) : ℂ)‖ < ε
  rw [e]
  calc _ ≤ ‖((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
          ((1 / 2 * wallLogMoment F x : ℝ) : ℂ)) / ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ)‖ +
        ‖((1 / 2 * (wallLogMoment F x / Real.sqrt (Real.log (1 / x)) - 2 * c) : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ B / Real.sqrt (Real.log (1 / x)) +
        1 / 2 * |wallLogMoment F x / Real.sqrt (Real.log (1 / x)) - 2 * c| :=
        add_le_add hn1 hn2.le
    _ < ε := by linarith

/-- **The laws of the wall.** There is a sign `s = ±1`, the sign of the terminal mass
`∫_{−k}^0 F` and of the logarithmic moment for small `k`, such that with `M = ∫ F² e^{−8u}`:
`(k⁻¹ ∫_{−k}^0 F) √log(1/k) → s √(8aM)`, `(∫_{v>k} F(−v)/v dv) / √log(1/k) → 2s √(8aM)`, and
`a F⁺(x) / √log(1/x) → −s √(8aM)` essentially as `x → 0⁺`. -/
theorem criticalState_wall_laws {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (∀ᶠ k : ℝ in 𝓝[>] 0, 0 < s * ∫ u in Ioo (-k) 0, F u ∧ 0 < s * wallLogMoment F k) ∧
      Tendsto (fun k : ℝ => (∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k)))
        (𝓝[>] 0) (𝓝 (s * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) ∧
      Tendsto (fun k : ℝ => wallLogMoment F k / Real.sqrt (Real.log (1 / k)))
        (𝓝[>] 0) (𝓝 (2 * (s * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
        ‖(criticalAliasCoefficient W₀ : ℂ) *
            beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x /
              ((Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) +
          ((s * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ)‖ < ε := by
  obtain ⟨s, hs, hev⟩ := criticalState_exists_sign_at_wall hW hthreshold hF
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have habs : |s| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hmeanLaw : Tendsto
      (fun k : ℝ => (∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k)))
      (𝓝[>] 0) (𝓝 (s * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
    have h6 := (Real.continuous_sqrt.tendsto _).comp
      (criticalState_tendsto_sq_terminalMean_mul_log hW hthreshold hF)
    have h7 : Tendsto (fun k : ℝ =>
        s * ((∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k))))
        (𝓝[>] 0) (𝓝 (Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
      refine h6.congr' ?_
      filter_upwards [hev, self_mem_nhdsWithin] with k hk hk0
      have hk0' : (0 : ℝ) < k := hk0
      have hpos : 0 < s * ((∫ u in Ioo (-k) 0, F u) / k) := by
        rw [← mul_div_assoc]
        exact div_pos hk.1 hk0'
      show Real.sqrt (((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k)) =
        s * ((∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k)))
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, ← mul_assoc]
      congr 1
      rw [← abs_of_pos hpos, abs_mul, habs, one_mul]
    refine (h7.const_mul s).congr fun k => ?_
    rw [← mul_assoc, hss, one_mul]
  have hLLaw : Tendsto (fun k : ℝ => wallLogMoment F k / Real.sqrt (Real.log (1 / k)))
      (𝓝[>] 0) (𝓝 (2 * (s * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))))) := by
    have h6 := (Real.continuous_sqrt.tendsto _).comp
      (criticalState_tendsto_sq_wallLogMoment_div_log hW hthreshold hF)
    have e32 : Real.sqrt (32 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) = 2 * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by
      have e : (32 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) = 2 ^ 2 * (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by ring
      rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [e32] at h6
    have h7 : Tendsto (fun k : ℝ => s * (wallLogMoment F k / Real.sqrt (Real.log (1 / k))))
        (𝓝[>] 0) (𝓝 (2 * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
      refine h6.congr' ?_
      filter_upwards [hev] with k hk
      show Real.sqrt (wallLogMoment F k ^ 2 / Real.log (1 / k)) =
        s * (wallLogMoment F k / Real.sqrt (Real.log (1 / k)))
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, ← mul_div_assoc]
      congr 1
      rw [← abs_of_pos hk.2, abs_mul, habs, one_mul]
    have h8 := h7.const_mul s
    have e8 : s * (2 * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) = 2 * (s * Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by ring
    rw [e8] at h8
    refine h8.congr fun k => ?_
    rw [← mul_assoc, hss, one_mul]
  exact ⟨s, hs, hev, hmeanLaw, hLLaw,
    criticalState_ae_tendsto_beyondWall_of_wallLogMoment hW hthreshold hF hLLaw⟩

/-- **The logarithmic gain of the terminal mass is sharp.** `log(2/k) ∫_{−k}^0 F² ≥ c k` for
small `k`, with `c = 4 a ∫ F² e^{−8u}`. -/
theorem criticalState_eventually_le_log_mul_terminal_square_mass {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℝ in 𝓝[>] 0,
      c * k ≤ Real.log (2 / k) * ∫ u in Ioo (-k) 0, F u ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  have haM : 0 < criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := mul_pos ha hM
  refine ⟨(4 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))), mul_pos (mul_pos (by norm_num) ha) hM, ?_⟩
  filter_upwards [(criticalState_tendsto_sq_terminalMean_mul_log hW hthreshold hF).eventually
      (lt_mem_nhds (show (4 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) < (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) by linarith)),
    self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with k hk hk0 hk1
  have hk0' : (0 : ℝ) < k := hk0
  have hcs := sq_setIntegral_Ioo_le hd.meas hd.sq hk0'.le
  have hlg : 0 < Real.log (1 / k) := Real.log_pos (one_lt_one_div hk0' hk1)
  have hlg2 : Real.log (1 / k) ≤ Real.log (2 / k) :=
    Real.log_le_log (one_div_pos.mpr hk0') (div_le_div_of_nonneg_right (by norm_num) hk0'.le)
  have hm : 0 ≤ ∫ u in Ioo (-k) 0, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hmean : ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 ≤ (∫ u in Ioo (-k) 0, F u ^ 2) / k := by
    rw [div_pow, div_le_div_iff₀ (pow_pos hk0' 2) hk0']
    calc (∫ u in Ioo (-k) 0, F u) ^ 2 * k
        ≤ (k * ∫ u in Ioo (-k) 0, F u ^ 2) * k := mul_le_mul_of_nonneg_right hcs hk0'.le
      _ = (∫ u in Ioo (-k) 0, F u ^ 2) * k ^ 2 := by ring
  calc (4 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) * k
      ≤ ((∫ u in Ioo (-k) 0, F u) / k) ^ 2 * Real.log (1 / k) * k :=
        mul_le_mul_of_nonneg_right hk.le hk0'.le
    _ ≤ (∫ u in Ioo (-k) 0, F u ^ 2) / k * Real.log (1 / k) * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmean hlg.le) hk0'.le
    _ = Real.log (1 / k) * ∫ u in Ioo (-k) 0, F u ^ 2 := by field_simp
    _ ≤ Real.log (2 / k) * ∫ u in Ioo (-k) 0, F u ^ 2 := mul_le_mul_of_nonneg_right hlg2 hm

end GaloisForLFunctions.ExclusionOfTheCriticalState
