import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfATwistIsItsSpectrum
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermOfAPeriodicTwist

/-!
# The second-order term of every periodic twist

The energy of a horizon window twisted by a mean-zero `M`-periodic weight `χ` is its spectrum
(`abs_twistEnergy_sub_le`): the mode `k/M` contributes `|χ̂(k)|²` times the window averages of the
shifted densities `D_u(s) = Σ_{n≥0} |φ̂(2πs(n + u))|²`, `u = k/M, 1 − k/M`. This file computes their
second-order limit for every profile with a regular spectral tail `x^β T(x) → A_φ`,
`T(x) = ∫_x^∞ |φ̂(2πt)|² dt`:

* **Every shifted density is the dilation derivative of a shifted bulk**
  (`hasDerivAt_twistBulk`): `D_u = −E_u'`, `E_u(s) = Σ_{n≥0} T(s(n + u))/(n + u)`.
* **The shifted bulk has a Hurwitz limit** (`tendsto_rpow_mul_twistBulk`):
  `s^β E_u(s) → A_φ ζ(β + 1, u)`, `ζ(k, u) = Σ_{n≥0} (n + u)^{−k}` the Hurwitz sum.
* **A density that is the dilation derivative of a regular bulk** has window limit `β J`
  (`tendsto_rpow_mul_densityAlias`), for every density, not only the aliasing of the atom grid.
* **The second-order term of a periodic twist** (`periodicTwist_layer_criticalCurve_of_regularTail`):
  along `c^{β+1}/log N → K`,

  `c⁻¹⟨W x, x⟩/∫g² → (βA_φ/(K∫φ²)) Σ_{0<k<M} |χ̂(k)|² (ζ(β+1, k/M) + ζ(β+1, 1 − k/M)) ‖H‖²_{−(β+1)}`.

  With `J = (2A_φ/∫φ²) ζ(β + 1)` the coefficient is `βJ/K` times the **spectral constant**
  `Σ_k |χ̂(k)|² (ζ(β+1, k/M) + ζ(β+1, 1 − k/M))/(2ζ(β+1))`. For the Ramanujan sum `c_m`,
  `|χ̂(k)|² = [(k, m) = 1]` and the spectral constant is the Jordan totient `J_{β+1}(m)`.
* **Every nonzero twist is coercive at second order** (`twistSpectralConstant_ge`): the spectral
  sum is at least `2 M⁻¹ Σ_{n<M} χ(n)²` (Parseval and `ζ(k, u) ≥ 1` on `(0, 1]`).
* **The tilted spline** (`periodicTwist_layer_criticalCurve_exact`): `β = 7`, `A_φ` the tail
  constant.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### The window limit of a density with a regular bulk -/

/-- The window weight `h(log x)² a(c max(x, e^{−A}))` of a density `a`. -/
def densityWindow (a h : ℝ → ℝ) (A c x : ℝ) : ℝ :=
  logProfile (fun y => h y ^ 2) x * a (c * max x (Real.exp (-A)))

theorem densityAlias_eq_riemann (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (a : ℝ → ℝ) (c : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    densityAlias a h c N = (N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, densityWindow a h A c (r / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  unfold densityAlias
  congr 1
  refine sum_congr rfl fun r hr => ?_
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hx : (0 : ℝ) < r / N := div_pos hr0 hN0
  have hlog : Real.log (r / N) = Real.log r - Real.log N := Real.log_div hr0.ne' hN0.ne'
  unfold densityWindow
  by_cases hw : Real.exp (-A) ≤ (r : ℝ) / N
  · rw [max_eq_left hw, logProfile, if_pos hx, hlog, show c * r / N = c * (r / N) by ring]
  · have hlt : Real.log r - Real.log N < -A := by
      rw [← hlog, Real.log_lt_iff_lt_exp hx]; exact not_le.mp hw
    have hz : h (Real.log r - Real.log N) = 0 := hsupp _ fun hm => by linarith [hm.1]
    rw [logProfile_eq_zero_of_lt hgs (not_le.mp hw), hz]; ring

/-- The window weight of a density is Lipschitz on `[0, 1]` with constant `L_F B_a + B_F L_a c`. -/
theorem abs_densityWindow_sub_le {a : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |h y ^ 2| ≤ Bg)
    {Lg : NNReal} (hLg : LipschitzWith Lg fun y => h y ^ 2) {Ba La : ℝ}
    (hBa : ∀ s, Real.exp (-A) ≤ s → |a s| ≤ Ba) (hLa0 : 0 ≤ La)
    (hLa : ∀ s s', Real.exp (-A) ≤ s → Real.exp (-A) ≤ s' → |a s - a s'| ≤ La * |s - s'|)
    {c : ℝ} (hc : 1 ≤ c) (x x' : ℝ) :
    |densityWindow a h A c x - densityWindow a h A c x'| ≤
      ((Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * (La * c)) * |x - x'| := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hge : ∀ z, Real.exp (-A) ≤ c * max z (Real.exp (-A)) := fun z =>
    le_trans (le_max_right z _) (le_mul_of_one_le_left (le_trans (Real.exp_pos _).le
      (le_max_right z _)) hc)
  have hF := abs_logProfile_sub_le hg2 hgs hA hBg hLg x x'
  have hFb := abs_logProfile_le hBg x'
  have hab := hBa _ (hge x)
  have hda := hLa _ _ (hge x) (hge x')
  rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < c)] at hda
  have hmax := abs_max_sub_max_le_abs x x' (Real.exp (-A))
  unfold densityWindow
  have e : logProfile (fun y => h y ^ 2) x * a (c * max x (Real.exp (-A))) -
      logProfile (fun y => h y ^ 2) x' * a (c * max x' (Real.exp (-A))) =
      (logProfile (fun y => h y ^ 2) x - logProfile (fun y => h y ^ 2) x') *
        a (c * max x (Real.exp (-A))) + logProfile (fun y => h y ^ 2) x' *
        (a (c * max x (Real.exp (-A))) - a (c * max x' (Real.exp (-A)))) := by
    ring
  rw [e]
  calc _ ≤ |logProfile (fun y => h y ^ 2) x - logProfile (fun y => h y ^ 2) x'| *
        |a (c * max x (Real.exp (-A)))| + Bg *
          |a (c * max x (Real.exp (-A))) - a (c * max x' (Real.exp (-A)))| := by
        refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
    _ ≤ ((Lg : ℝ) * Real.exp (2 * A) * |x - x'|) * Ba + Bg * (La * (c * |x - x'|)) := by
        gcongr
        exact hda.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ c)) hLa0)
    _ = _ := by ring

/-- **Integration by parts against the bulk**: if `E' = −a` on `(0, ∞)`, then with `ℓ = e^{−A−1}`,
`∫_0^1 h(log x)² a(cx) dx = c⁻¹ ∫_ℓ^1 F'(x) E(cx) dx`, `F(x) = h(log x)²`. -/
theorem integral_densityWindow_eq {a E : ℝ → ℝ} (hder : ∀ s, 0 < s → HasDerivAt E (-a s) s)
    (hcont : ContinuousOn a (Set.Ioi 0)) (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {c : ℝ} (hc : 0 < c) :
    ∫ x in (0 : ℝ)..1, densityWindow a h A c x =
      c⁻¹ * ∫ x in Real.exp (-A - 1)..1, logProfileDeriv (fun y => h y ^ 2) x * E (c * x) := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨B, L, -, hL⟩ := exists_bound_lipschitz hg2 hgs
  have hg0 : (fun y => h y ^ 2) 0 = 0 := horizon_zero_at_zero hgs hL
  set ℓ := Real.exp (-A - 1) with hℓ
  have hℓ0 : 0 < ℓ := Real.exp_pos _
  have hℓA : ℓ < Real.exp (-A) := Real.exp_lt_exp.mpr (by linarith)
  have hℓ1 : ℓ ≤ 1 := le_of_lt (lt_of_lt_of_le hℓA (Real.exp_le_one_iff.mpr (by linarith)))
  have hlow : ∀ x, x < Real.exp (-A) → densityWindow a h A c x = 0 := fun x hx => by
    rw [densityWindow, logProfile_eq_zero_of_lt hgs hx, zero_mul]
  have hG : Continuous (densityWindow a h A c) := by
    have hFc : Continuous (logProfile (fun y => h y ^ 2)) :=
      continuous_iff_continuousAt.mpr fun x => (hasDerivAt_logProfile hg2 hgs x).continuousAt
    refine hFc.mul ?_
    refine ContinuousOn.comp_continuous (s := Set.Ioi 0) hcont
      (continuous_const.mul (continuous_id.max continuous_const)) fun x => ?_
    exact mul_pos hc (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))
  have hsplit : ∫ x in (0 : ℝ)..1, densityWindow a h A c x =
      ∫ x in ℓ..1, logProfile (fun y => h y ^ 2) x * a (c * x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := ℓ) (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
    have h0 : ∫ x in (0 : ℝ)..ℓ, densityWindow a h A c x = 0 := by
      rw [intervalIntegral.integral_of_le hℓ0.le]
      exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => hlow x (lt_of_le_of_lt hx.2 hℓA)
    rw [h0, zero_add]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hℓ1] at hx
    by_cases hw : Real.exp (-A) ≤ x
    · simp only [densityWindow, max_eq_left hw]
    · rw [hlow x (not_le.mp hw), logProfile_eq_zero_of_lt hgs (not_le.mp hw), zero_mul]
  have hu : ∀ x ∈ Set.uIcc ℓ 1, HasDerivAt (logProfile (fun y => h y ^ 2))
      (logProfileDeriv (fun y => h y ^ 2) x) x := fun x _ => hasDerivAt_logProfile hg2 hgs x
  have hv : ∀ x ∈ Set.uIcc ℓ 1, HasDerivAt (fun x => E (c * x)) (c * (-a (c * x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hℓ1] at hx
    have hx0 : 0 < c * x := mul_pos hc (lt_of_lt_of_le hℓ0 hx.1)
    have := (hder _ hx0).comp x ((hasDerivAt_id x).const_mul c)
    exact this.congr_deriv (by simp only [mul_one]; ring)
  have hu' : IntervalIntegrable (logProfileDeriv (fun y => h y ^ 2)) volume ℓ 1 :=
    (continuous_logProfileDeriv hg2 hgs).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x => c * (-a (c * x))) volume ℓ 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.neg ?_)
    refine hcont.comp (continuousOn_const.mul continuousOn_id) fun x hx => ?_
    rw [Set.uIcc_of_le hℓ1] at hx
    exact mul_pos hc (lt_of_lt_of_le hℓ0 hx.1)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [logProfile_eq_zero_of_one_le hgs hg0 le_rfl, logProfile_eq_zero_of_lt hgs hℓA, zero_mul,
    zero_mul, sub_zero, zero_sub] at hibp
  have hlhs : ∫ x in ℓ..1, logProfile (fun y => h y ^ 2) x * (c * (-a (c * x))) =
      -c * ∫ x in ℓ..1, logProfile (fun y => h y ^ 2) x * a (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [hlhs] at hibp
  rw [hsplit]
  have hc0 : c ≠ 0 := hc.ne'
  field_simp
  linarith

/-- A density that is Lipschitz on every `[s₀, ∞)` is continuous on `(0, ∞)`. -/
theorem continuousOn_of_lipschitz_tail {a : ℝ → ℝ}
    (hreg : ∀ s₀, 0 < s₀ → ∃ Ba La : ℝ, (∀ s, s₀ ≤ s → |a s| ≤ Ba) ∧
      ∀ s s', s₀ ≤ s → s₀ ≤ s' → |a s - a s'| ≤ La * |s - s'|) :
    ContinuousOn a (Set.Ioi 0) := by
  intro s hs
  have hs0 : 0 < s := hs
  obtain ⟨-, La, -, hL⟩ := hreg (s / 2) (by linarith)
  refine ContinuousAt.continuousWithinAt ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hpos : 0 < |La| + 1 := by positivity
  refine ⟨min (s / 2) (ε / (|La| + 1)), by positivity, fun {t} ht => ?_⟩
  rw [Real.dist_eq] at ht ⊢
  have ht1 : s / 2 ≤ t := by
    have := lt_of_lt_of_le ht (min_le_left _ _)
    rw [abs_lt] at this; linarith
  have h2 : |t - s| < ε / (|La| + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  rw [lt_div_iff₀ hpos, mul_comm] at h2
  calc |a t - a s| ≤ La * |t - s| := hL t s ht1 (by linarith)
    _ ≤ (|La| + 1) * |t - s| :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self La]) (abs_nonneg _)
    _ < ε := h2

/-- **The window limit of a density with a regular bulk.** If `E' = −a` on `(0, ∞)`, `a` is bounded
and Lipschitz on every `[s₀, ∞)` and `s^β E(s) → J`, then along `c → ∞`, `c^{β+2}/N → 0`:
`c^{β+1} N⁻¹ Σ_n h(log(n/N))² a(cn/N) → β J ∫ e^{−βy} h(y)² dy`. -/
theorem tendsto_rpow_mul_densityAlias {a E : ℝ → ℝ} {β J : ℝ}
    (hder : ∀ s, 0 < s → HasDerivAt E (-a s) s)
    (hreg : ∀ s₀, 0 < s₀ → ∃ Ba La : ℝ, (∀ s, s₀ ≤ s → |a s| ≤ Ba) ∧
      ∀ s s', s₀ ≤ s → s₀ ≤ s' → |a s - a s'| ≤ La * |s - s'|)
    (hE : Tendsto (fun s => s ^ β * E s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ (β + 2) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N ^ (β + 1) * densityAlias a h (c N) N) atTop
      (𝓝 (J * (β * ∫ y, Real.exp (-(β * y)) * h y ^ 2))) := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg2 hgs
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hgs) hg2 (by norm_num)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  set s₀ := Real.exp (-A) with hs₀
  have hs₀0 : 0 < s₀ := Real.exp_pos _
  obtain ⟨Ba, La, hBa, hLa⟩ := hreg s₀ hs₀0
  have hBa0 : 0 ≤ Ba := (abs_nonneg _).trans (hBa s₀ le_rfl)
  have hLa0 : 0 ≤ La := by
    have := hLa s₀ (s₀ + 1) le_rfl (by linarith)
    rw [sub_add_cancel_left, abs_neg, abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  set D := (Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * La with hD
  have hacont := continuousOn_of_lipschitz_tail hreg
  have hEc : ContinuousOn E (Set.Ioi 0) := fun s hs =>
    (hder s hs).continuousAt.continuousWithinAt
  set ℓ := Real.exp (-A - 1) with hℓ
  have hℓ0 : 0 < ℓ := Real.exp_pos _
  have hℓ1 : ℓ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hW := tendsto_window_bulk hE hEc (continuous_logProfileDeriv hg2 hgs) hℓ0 hℓ1 hcinf
  rw [integral_logProfileDeriv_mul_rpow hh hA hsupp β] at hW
  have herr : Tendsto (fun N : ℕ => c N ^ (β + 1) * densityAlias a h (c N) N -
      c N ^ β * ∫ x in ℓ..1, logProfileDeriv (fun y => h y ^ 2) x * E (c N * x)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((hcN.const_mul D).trans (by rw [mul_zero]))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hlip := abs_densityWindow_sub_le hh hsupp hA hBg hLg hBa hLa0 hLa (hc1 N)
    have hK0 : 0 ≤ (Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * (La * c N) := by positivity
    have hR := abs_riemann_sub_le_of_lipschitz hK0 hlip hN
    rw [integral_densityWindow_eq hder hacont hh hsupp hA hc0] at hR
    have hal := densityAlias_eq_riemann hsupp a (c N) hN (A := A)
    have hcβ : c N ^ (β + 1) = c N ^ β * c N := by rw [Real.rpow_add hc0, Real.rpow_one]
    have hcβ2 : c N ^ (β + 2) = c N ^ (β + 1) * c N := by
      rw [show β + 2 = (β + 1) + 1 by ring, Real.rpow_add hc0, Real.rpow_one]
    have hpos : 0 < c N ^ (β + 1) := Real.rpow_pos_of_pos hc0 _
    set R := (N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, densityWindow a h A (c N) (r / N) with hRdef
    set W := ∫ x in ℓ..1, logProfileDeriv (fun y => h y ^ 2) x * E (c N * x) with hWdef
    have heq : c N ^ (β + 1) * densityAlias a h (c N) N - c N ^ β * W =
        c N ^ (β + 1) * (R - (c N)⁻¹ * W) := by
      rw [hal, hcβ]; field_simp
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    calc c N ^ (β + 1) * |R - (c N)⁻¹ * W| ≤
          c N ^ (β + 1) * (((Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * (La * c N)) / N) :=
          mul_le_mul_of_nonneg_left hR hpos.le
      _ ≤ c N ^ (β + 1) * (((Lg : ℝ) * Real.exp (2 * A) * Ba * c N + Bg * (La * c N)) / N) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hN0.le) hpos.le
          have := le_mul_of_one_le_right (by positivity : 0 ≤ (Lg : ℝ) * Real.exp (2 * A) * Ba)
            (hc1 N)
          linarith
      _ = D * (c N ^ (β + 2) / N) := by rw [hD, hcβ2]; field_simp
  have := herr.add hW
  rw [zero_add] at this
  exact this.congr fun N => by ring

/-! ### The shifted densities -/

theorem shift_mul_succ_le {u : ℝ} (hu1 : u ≤ 1) (n : ℕ) : u * ((n : ℝ) + 1) ≤ (n : ℝ) + u := by
  have := mul_le_of_le_one_left (Nat.cast_nonneg (α := ℝ) n) hu1
  rw [mul_add, mul_one]; linarith

/-- A harmonic of the shifted grid: `|φ̂(2πs(n+u))|² ≤ C_φ (2π s₀ u)^{−p} (n + 1)^{−p}`. -/
theorem shellSpectrum_shift_le {Cφ p : ℝ} (hp : 0 ≤ p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (n : ℕ) :
    shellSpectrum φ (s * ((n : ℝ) + u)) ≤
      Cφ * (2 * Real.pi * (s₀ * u)) ^ (-p) * ((n : ℝ) + 1) ^ (-p) := by
  have hpi := Real.pi_pos
  have h := hdecay (2 * Real.pi * (s * ((n : ℝ) + u)))
  have hr := one_add_rpow_neg_le (q := p) hp (mul_pos hs₀ hu0) n
  have hle : ((n : ℝ) + 1) * (s₀ * u) ≤ s * ((n : ℝ) + u) := by
    have h1 := shift_mul_succ_le hu1 n
    have h2 : s₀ * ((n : ℝ) + u) ≤ s * ((n : ℝ) + u) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    nlinarith
  have hmono : (1 + |2 * Real.pi * (s * ((n : ℝ) + u))|) ^ (-p) ≤
      (1 + 2 * Real.pi * (((n : ℝ) + 1) * (s₀ * u))) ^ (-p) := by
    rw [abs_of_nonneg (by have := lt_of_lt_of_le hs₀ hs; positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  calc shellSpectrum φ (s * ((n : ℝ) + u)) ≤
        Cφ * (1 + |2 * Real.pi * (s * ((n : ℝ) + u))|) ^ (-p) := h
    _ ≤ Cφ * ((2 * Real.pi * (s₀ * u)) ^ (-p) * ((n : ℝ) + 1) ^ (-p)) :=
        mul_le_mul_of_nonneg_left (hmono.trans hr) hCφ
    _ = _ := by ring

/-- **The shifted density is bounded and Lipschitz on every `[s₀, ∞)`** (`p > 4`). -/
theorem twistDensity_regular {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ Ba La : ℝ, (∀ s, s₀ ≤ s → |twistDensity φ u s| ≤ Ba) ∧
      ∀ s s', s₀ ≤ s → s₀ ≤ s' → |twistDensity φ u s - twistDensity φ u s'| ≤ La * |s - s'| := by
  have hpi := Real.pi_pos
  have hI : 0 ≤ ∫ v, |φ v| := integral_nonneg fun v => abs_nonneg _
  set Cb := Cφ * (2 * Real.pi * (s₀ * u)) ^ (-p) with hCb
  set CL := 4 * Real.pi * Real.sqrt Cφ * (∫ v, |φ v|) * (2 * Real.pi * (s₀ * u)) ^ (-p / 2)
    with hCL
  have hCL0 : 0 ≤ CL := by positivity
  have hsb : Summable fun n : ℕ => Cb * ((n : ℝ) + 1) ^ (-p) :=
    (summable_succ_rpow (by linarith)).mul_left _
  have hsL : Summable fun n : ℕ => CL * ((n : ℝ) + 1) ^ (1 - p / 2) :=
    (summable_succ_rpow (by linarith)).mul_left _
  have hbd : ∀ s, s₀ ≤ s → ∀ n : ℕ, shellSpectrum φ (s * ((n : ℝ) + u)) ≤
      Cb * ((n : ℝ) + 1) ^ (-p) := fun s hs n =>
    shellSpectrum_shift_le (by linarith) hCφ hdecay hu0 hu1 hs₀ hs n
  have hsum : ∀ s, s₀ ≤ s → Summable fun n : ℕ => shellSpectrum φ (s * ((n : ℝ) + u)) :=
    fun s hs => hsb.of_nonneg_of_le (fun n => shellSpectrum_nonneg _) (hbd s hs)
  refine ⟨∑' n : ℕ, Cb * ((n : ℝ) + 1) ^ (-p), ∑' n : ℕ, CL * ((n : ℝ) + 1) ^ (1 - p / 2),
    fun s hs => ?_, fun s s' hs hs' => ?_⟩
  · have h0 : 0 ≤ twistDensity φ u s := tsum_nonneg fun n => shellSpectrum_nonneg _
    rw [abs_of_nonneg h0]
    exact (hsum s hs).tsum_le_tsum (hbd s hs) hsb
  · have hterm : ∀ n : ℕ, ‖shellSpectrum φ (s * ((n : ℝ) + u)) -
        shellSpectrum φ (s' * ((n : ℝ) + u))‖ ≤ CL * ((n : ℝ) + 1) ^ (1 - p / 2) * |s - s'| := by
      intro n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnu : (0 : ℝ) < (n : ℝ) + u := by positivity
      have hT : (0 : ℝ) ≤ ((n : ℝ) + 1) * (s₀ * u) := by positivity
      have hle : ∀ t, s₀ ≤ t → ((n : ℝ) + 1) * (s₀ * u) ≤ t * ((n : ℝ) + u) := fun t ht => by
        have h1 := shift_mul_succ_le hu1 n
        have h2 : s₀ * ((n : ℝ) + u) ≤ t * ((n : ℝ) + u) :=
          mul_le_mul_of_nonneg_right ht hnu.le
        nlinarith
      have hd := abs_shellSpectrum_sub_le hφ.continuous hφsupp hCφ (by linarith) hdecay hT
        (hle s hs) (hle s' hs')
      have hr := one_add_rpow_neg_le (q := p / 2) (by linarith) (mul_pos hs₀ hu0) n
      rw [show -(p / 2) = -p / 2 by ring] at hr
      rw [Real.norm_eq_abs]
      refine hd.trans ?_
      rw [← sub_mul, abs_mul, abs_of_pos hnu]
      have e : ((n : ℝ) + 1) ^ (1 - p / 2) = ((n : ℝ) + 1) ^ (-p / 2) * ((n : ℝ) + 1) := by
        rw [show (1 : ℝ) - p / 2 = -p / 2 + 1 by ring, Real.rpow_add hn1, Real.rpow_one]
      have hnu1 : (n : ℝ) + u ≤ (n : ℝ) + 1 := by linarith
      rw [e, hCL]
      calc 4 * Real.pi * Real.sqrt Cφ * (∫ v, |φ v|) *
            (1 + 2 * Real.pi * (((n : ℝ) + 1) * (s₀ * u))) ^ (-p / 2) * (|s - s'| * ((n : ℝ) + u))
          ≤ 4 * Real.pi * Real.sqrt Cφ * (∫ v, |φ v|) *
            ((2 * Real.pi * (s₀ * u)) ^ (-p / 2) * ((n : ℝ) + 1) ^ (-p / 2)) *
              (|s - s'| * ((n : ℝ) + 1)) := by
            gcongr
        _ = _ := by ring
    have hsn : Summable fun n : ℕ => ‖shellSpectrum φ (s * ((n : ℝ) + u)) -
        shellSpectrum φ (s' * ((n : ℝ) + u))‖ :=
      (hsL.mul_right |s - s'|).of_nonneg_of_le (fun n => norm_nonneg _) hterm
    unfold twistDensity
    rw [← (hsum s hs).tsum_sub (hsum s' hs'), ← Real.norm_eq_abs]
    calc ‖∑' n : ℕ, (shellSpectrum φ (s * ((n : ℝ) + u)) - shellSpectrum φ (s' * ((n : ℝ) + u)))‖
        ≤ ∑' n : ℕ, ‖shellSpectrum φ (s * ((n : ℝ) + u)) - shellSpectrum φ (s' * ((n : ℝ) + u))‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' n : ℕ, CL * ((n : ℝ) + 1) ^ (1 - p / 2) * |s - s'| :=
          hsn.tsum_le_tsum hterm (hsL.mul_right _)
      _ = _ := by rw [tsum_mul_right]

/-! ### The shifted bulk -/

/-- The shifted bulk `E_u(s) = Σ_{n ≥ 0} T(s(n + u))/(n + u)`, `T` the spectral tail. -/
def twistBulk (φ : ℝ → ℝ) (u s : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticDegenerationTheory.spectralTail φ (s * ((n : ℝ) + u)) / ((n : ℝ) + u)

/-- The Hurwitz sum `ζ(k, u) = Σ_{n ≥ 0} (n + u)^{−k}`. -/
def hurwitzSum (k u : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + u) ^ (-k)

theorem summable_shift_rpow {k u : ℝ} (hk : 1 < k) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    Summable fun n : ℕ => ((n : ℝ) + u) ^ (-k) := by
  refine ((summable_succ_rpow (r := -k) (by linarith)).mul_left (u ^ (-k))).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  rw [← Real.mul_rpow hu0.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (shift_mul_succ_le hu1 n) (by linarith)

theorem one_le_hurwitzSum {k u : ℝ} (hk : 1 < k) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    1 ≤ hurwitzSum k u := by
  have h0 : (1 : ℝ) ≤ ((0 : ℕ) + u) ^ (-k) := by
    rw [Nat.cast_zero, zero_add]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by linarith)
  exact h0.trans ((summable_shift_rpow hk hu0 hu1).le_tsum 0 fun j _ => by positivity)

/-- `T(x) = T(0) − ∫_0^x |φ̂(2πt)|² dt`. -/
theorem spectralTail_eq_sub (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x : ℝ) : ArithmeticDegenerationTheory.spectralTail φ x =
      ArithmeticDegenerationTheory.spectralTail φ 0 - ∫ t in (0 : ℝ)..x, shellSpectrum φ t := by
  have hint := ArithmeticDegenerationTheory.integrable_shellSpectrum hφ hφsupp
  unfold ArithmeticDegenerationTheory.spectralTail
  rcases le_total 0 x with hx | hx
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hx, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hint.integrableOn hint.integrableOn, intervalIntegral.integral_of_le hx]
    ring
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hx, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hint.integrableOn hint.integrableOn, intervalIntegral.integral_symm,
      intervalIntegral.integral_of_le hx]
    ring

/-- The spectral tail has derivative `−|φ̂(2πx)|²`. -/
theorem hasDerivAt_spectralTail (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x : ℝ) : HasDerivAt (ArithmeticDegenerationTheory.spectralTail φ) (-shellSpectrum φ x) x := by
  have hc := continuous_shellSpectrum hφ.continuous (hasCompactSupport_profile hφsupp)
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have := (hasDerivAt_const x (ArithmeticDegenerationTheory.spectralTail φ 0)).sub hd
  rw [zero_sub] at this
  have hfun : ArithmeticDegenerationTheory.spectralTail φ = fun y =>
      ArithmeticDegenerationTheory.spectralTail φ 0 - ∫ t in (0 : ℝ)..y, shellSpectrum φ t :=
    funext (spectralTail_eq_sub hφ hφsupp)
  rw [hfun]
  exact this

/-- A regular tail is bounded by `B x^{−β}` on `(0, ∞)`. -/
theorem exists_spectralTail_le_rpow (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 < x → ArithmeticDegenerationTheory.spectralTail φ x ≤ B * x ^ (-β) := by
  obtain ⟨B, hB0, hB⟩ := ArithmeticDegenerationTheory.exists_rpow_mul_spectralTail_le hφ hφsupp hβ hT
  set I₀ := ∫ t, shellSpectrum φ t
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun t => shellSpectrum_nonneg t
  refine ⟨max B I₀, le_max_of_le_left hB0, fun x hx => ?_⟩
  have hxβ : 0 < x ^ (-β) := Real.rpow_pos_of_pos hx _
  rcases le_total 1 x with h1 | h1
  · have hb := hB x h1
    have e : ArithmeticDegenerationTheory.spectralTail φ x =
        x ^ (-β) * (x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) := by
      rw [← mul_assoc, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, one_mul]
    rw [e, mul_comm (max B I₀)]
    exact mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) hxβ.le
  · have h1' : 1 ≤ x ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx h1 (by linarith)
    calc ArithmeticDegenerationTheory.spectralTail φ x ≤ I₀ :=
          ArithmeticDegenerationTheory.spectralTail_le_integral hφ hφsupp x
      _ ≤ max B I₀ := le_max_right _ _
      _ ≤ max B I₀ * x ^ (-β) := le_mul_of_one_le_right (le_max_of_le_left hB0) h1'

/-- **The shifted density is the dilation derivative of the shifted bulk**: `E_u' = −D_u`. -/
theorem hasDerivAt_twistBulk (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (twistBulk φ u) (-twistDensity φ u s) s := by
  obtain ⟨B, hB0, hB⟩ := exists_spectralTail_le_rpow hφ hφsupp hβ hT
  have hs2 : s / 2 < s := by linarith
  have hsum0 : Summable fun n : ℕ =>
      ArithmeticDegenerationTheory.spectralTail φ (s * ((n : ℝ) + u)) / ((n : ℝ) + u) := by
    refine ((summable_shift_rpow (k := β + 1) (by linarith) hu0 hu1).mul_left
      (B * s ^ (-β))).of_nonneg_of_le (fun n => ?_) fun n => ?_
    · have : (0 : ℝ) < (n : ℝ) + u := by positivity
      exact div_nonneg (ArithmeticDegenerationTheory.spectralTail_nonneg _) this.le
    · have hn : (0 : ℝ) < (n : ℝ) + u := by positivity
      have hb := hB _ (mul_pos hs hn)
      rw [Real.mul_rpow hs.le hn.le] at hb
      rw [div_le_iff₀ hn]
      calc ArithmeticDegenerationTheory.spectralTail φ (s * ((n : ℝ) + u)) ≤
            B * (s ^ (-β) * ((n : ℝ) + u) ^ (-β)) := hb
        _ = B * s ^ (-β) * (((n : ℝ) + u) ^ (-(β + 1)) * ((n : ℝ) + u)) := by
            rw [show -(β + 1) = -β + -1 by ring, Real.rpow_add hn, Real.rpow_neg_one,
              mul_assoc (((n : ℝ) + u) ^ (-β)), inv_mul_cancel₀ hn.ne']
            ring
        _ = _ := by ring
  have hd := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => Cφ * (2 * Real.pi * (s / 2 * u)) ^ (-p) * ((n : ℝ) + 1) ^ (-p))
    (g := fun (n : ℕ) (y : ℝ) =>
      ArithmeticDegenerationTheory.spectralTail φ (y * ((n : ℝ) + u)) / ((n : ℝ) + u))
    (g' := fun (n : ℕ) (y : ℝ) => -shellSpectrum φ (y * ((n : ℝ) + u)))
    (t := Set.Ioi (s / 2)) (y₀ := s) (y := s)
    ((summable_succ_rpow (by linarith)).mul_left _) isOpen_Ioi isPreconnected_Ioi
    (fun n y _ => by
      have hn : (0 : ℝ) < (n : ℝ) + u := by positivity
      refine (((hasDerivAt_spectralTail hφ hφsupp (y * ((n : ℝ) + u))).comp y
        (hasDerivAt_mul_const ((n : ℝ) + u))).div_const ((n : ℝ) + u)).congr_deriv ?_
      rw [mul_div_assoc, div_self hn.ne', mul_one])
    (fun n y hy => by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (shellSpectrum_nonneg _)]
      exact shellSpectrum_shift_le (by linarith) hCφ hdecay hu0 hu1 (by linarith : 0 < s / 2)
        (le_of_lt hy) n)
    hs2 hsum0 hs2
  have e : (∑' n : ℕ, -shellSpectrum φ (s * ((n : ℝ) + u))) = -twistDensity φ u s := by
    rw [tsum_neg]; rfl
  rw [e] at hd
  exact hd

/-- **The shifted bulk has a Hurwitz limit**: `s^β E_u(s) → A_φ ζ(β + 1, u)`. -/
theorem tendsto_rpow_mul_twistBulk (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    Tendsto (fun s => s ^ β * twistBulk φ u s) atTop (𝓝 (Aφ * hurwitzSum (β + 1) u)) := by
  obtain ⟨B, hB0, hB⟩ := ArithmeticDegenerationTheory.exists_rpow_mul_spectralTail_le hφ hφsupp hβ hT
  have hsum := summable_shift_rpow (k := β + 1) (by linarith) hu0 hu1
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun s (n : ℕ) => ((n : ℝ) + u) ^ (-(β + 1)) *
      ((s * ((n : ℝ) + u)) ^ β * ArithmeticDegenerationTheory.spectralTail φ (s * ((n : ℝ) + u))))
    (g := fun n => ((n : ℝ) + u) ^ (-(β + 1)) * Aφ)
    (bound := fun n => ((n : ℝ) + u) ^ (-(β + 1)) * B)
    (hsum.mul_right B)
    (fun n => by
      have hn : (0 : ℝ) < (n : ℝ) + u := by positivity
      exact (hT.comp (tendsto_id.atTop_mul_const hn)).const_mul _)
    (by
      filter_upwards [eventually_ge_atTop u⁻¹] with s hs n
      have hn : (0 : ℝ) < (n : ℝ) + u := by positivity
      have hs0 : 0 < s := lt_of_lt_of_le (inv_pos.mpr hu0) hs
      have hx : 1 ≤ s * ((n : ℝ) + u) := by
        have h1 : 1 ≤ s * u := by rwa [inv_le_iff_one_le_mul₀ hu0] at hs
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hpos : 0 ≤ (s * ((n : ℝ) + u)) ^ β *
          ArithmeticDegenerationTheory.spectralTail φ (s * ((n : ℝ) + u)) :=
        mul_nonneg (by positivity) (ArithmeticDegenerationTheory.spectralTail_nonneg _)
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      exact hB _ hx)
  have heq : ∀ᶠ s in atTop, (∑' n : ℕ, ((n : ℝ) + u) ^ (-(β + 1)) *
      ((s * ((n : ℝ) + u)) ^ β * ArithmeticDegenerationTheory.spectralTail φ (s * ((n : ℝ) + u)))) =
        s ^ β * twistBulk φ u s := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    unfold twistBulk
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hn : (0 : ℝ) < (n : ℝ) + u := by positivity
    have hnβ : ((n : ℝ) + u) ^ β ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
    rw [Real.mul_rpow hs.le hn.le, Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one]
    field_simp
  have hval : (∑' n : ℕ, ((n : ℝ) + u) ^ (-(β + 1)) * Aφ) = Aφ * hurwitzSum (β + 1) u := by
    rw [hurwitzSum, tsum_mul_right, mul_comm]
  rw [hval] at hlim
  exact hlim.congr' heq

/-- **The window limit of a shifted density** along the critical curve:
`log N · 𝒜^{(u)}_N → K⁻¹ A_φ ζ(β + 1, u) β ∫ e^{−βy} h²`. -/
theorem tendsto_log_mul_twistDensityAlias (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    Tendsto (fun N : ℕ => Real.log N * densityAlias (twistDensity φ u) h (c N) N) atTop
      (𝓝 (K⁻¹ * (Aφ * hurwitzSum (β + 1) u * (β * ∫ y, Real.exp (-(β * y)) * h y ^ 2)))) := by
  obtain ⟨hcinf, -, hcN⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  rw [show β + 1 + 1 = β + 2 by ring] at hcN
  have h2 := tendsto_rpow_mul_densityAlias (a := twistDensity φ u) (E := twistBulk φ u)
    (fun s hs => hasDerivAt_twistBulk hφ hφsupp (by linarith) hCφ hdecay hβ hT hu0 hu1 hs)
    (fun s₀ hs₀ => twistDensity_regular hq hCφ hφ hφsupp hdecay hu0 hu1 hs₀)
    (tendsto_rpow_mul_twistBulk hφ hφsupp hβ hT hu0 hu1) hh hA hsupp hc1 hcinf hcN
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (β + 1)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  refine (hinv.mul h2).congr fun N => ?_
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hcp : c N ^ (β + 1) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  field_simp

/-! ### The second-order term -/

/-- The spectral sum `Σ_{0<k<M} |χ̂(k)|² (ζ(k', k/M) + ζ(k', 1 − k/M))` of a twist at exponent `k'`. -/
def twistSpectralSum (k' : ℝ) (χ : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 M, twistPower χ M k *
    (hurwitzSum k' ((k : ℝ) / M) + hurwitzSum k' (1 - (k : ℝ) / M))

theorem shifts_mem {M k : ℕ} (hk : k ∈ Ico 1 M) :
    (0 < (k : ℝ) / M ∧ (k : ℝ) / M ≤ 1) ∧ (0 < 1 - (k : ℝ) / M ∧ 1 - (k : ℝ) / M ≤ 1) := by
  obtain ⟨hk1, hkM⟩ := Finset.mem_Ico.mp hk
  have hM : (0 : ℝ) < M := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hkM)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hlt : (k : ℝ) / M < 1 := by rw [div_lt_one hM]; exact_mod_cast hkM
  have hpos : 0 < (k : ℝ) / M := div_pos hk0 hM
  exact ⟨⟨hpos, hlt.le⟩, ⟨by linarith, by linarith⟩⟩

/-- **Every nonzero twist is coercive at second order**: the spectral sum is at least
`2 M⁻¹ Σ_{n<M} χ(n)²`. -/
theorem twistSpectralSum_ge {k' : ℝ} (hk' : 1 < k') {χ : ℕ → ℝ} {M : ℕ}
    (hχ : MeanZeroTwist χ M) :
    2 * ((M : ℝ)⁻¹ * ∑ n ∈ range M, χ n ^ 2) ≤ twistSpectralSum k' χ M := by
  rw [← sum_twistPower hχ, Finset.mul_sum, twistSpectralSum]
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := shifts_mem hk
  have := add_le_add (one_le_hurwitzSum hk' h1 h2) (one_le_hurwitzSum hk' h3 h4)
  have hw := twistPower_nonneg χ M k
  nlinarith

/-- **The second-order term of every periodic twist.** For a `C²` profile on `[0, 1]` with
`|φ̂(u)|² ≤ C_φ(1 + |u|)^{−q}`, `q > 4`, and a regular spectral tail `x^β T(x) → A_φ`, and every
mean-zero `M`-periodic twist `χ`: along `c^{β+1}/log N → K`,
`c⁻¹⟨W x, x⟩/∫g² → (β A_φ/(K ∫φ²)) Σ_{0<k<M} |χ̂(k)|² (ζ(β+1, k/M) + ζ(β+1, 1 − k/M)) ‖H‖²_{−(β+1)}`. -/
theorem periodicTwist_layer_criticalCurve_of_regularTail (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) * twistSpectralSum (β + 1) χ M *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hsharp := twisted_layer_sharp_of_energy hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp hc1 hcinf
    hclog hχ (twistAlias φ h χ M) (abs_twistEnergy_sub_le hφ hφsupp hh hA hsupp hχ)
    (exists_periodicLow_energy_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay hh hA hsupp hχ)
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  set M₀ := ∫ u, φ u ^ 2 with hM₀
  have hlim : ∀ u, 0 < u → u ≤ 1 → Tendsto (fun N : ℕ =>
      Real.log N * densityAlias (twistDensity φ u) h (c N) N) atTop
      (𝓝 (K⁻¹ * (Aφ * hurwitzSum (β + 1) u * (β * I)))) := fun u hu0 hu1 =>
    tendsto_log_mul_twistDensityAlias hφ hφsupp hq hCφ hdecay hβ hT hh hA hsupp hc1 hK hcrit hu0 hu1
  have hterm : Tendsto (fun N : ℕ => Real.log N / M₀ * twistAlias φ h χ M (c N) N) atTop
      (𝓝 (∑ k ∈ Ico 1 M, M₀⁻¹ * (twistPower χ M k *
        (K⁻¹ * (Aφ * hurwitzSum (β + 1) ((k : ℝ) / M) * (β * I)) +
          K⁻¹ * (Aφ * hurwitzSum (β + 1) (1 - (k : ℝ) / M) * (β * I)))))) := by
    have := tendsto_finsetSum (Ico 1 M) fun k hk => by
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := shifts_mem hk
      exact (((hlim _ h1 h2).add (hlim _ h3 h4)).const_mul (twistPower χ M k)).const_mul M₀⁻¹
    refine this.congr fun N => ?_
    rw [twistAlias, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : ∑ k ∈ Ico 1 M, M₀⁻¹ * (twistPower χ M k *
      (K⁻¹ * (Aφ * hurwitzSum (β + 1) ((k : ℝ) / M) * (β * I)) +
        K⁻¹ * (Aφ * hurwitzSum (β + 1) (1 - (k : ℝ) / M) * (β * I)))) =
      β * Aφ / (K * M₀) * twistSpectralSum (β + 1) χ M * I := by
    rw [twistSpectralSum, Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun k _ => ?_
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

/-- **The tilted spline.** Along `c⁸/log N → K`, the window twisted by any mean-zero `M`-periodic
`χ` has `c⁻¹⟨W x, x⟩/∫g² → (7A/(K∫φ²)) Σ_{0<k<M} |χ̂(k)|² (ζ(8, k/M) + ζ(8, 1 − k/M)) ‖H‖²_{−8}`,
`A` the tail constant of the tilted spline. -/
theorem periodicTwist_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K))
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
      atTop (𝓝 (7 * ArithmeticDegenerationTheory.tiltedTailConstant /
        (K * ∫ u, tiltedUnitSpline u ^ 2) * twistSpectralSum 8 χ M *
          ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := periodicTwist_layer_criticalCurve_of_regularTail contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num)
    ArithmeticDegenerationTheory.tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline
    hh hA hsupp hc1 hK hcrit' hχ
  have h8 : ((7 : ℝ) + 1) = 8 := by norm_num
  rw [h8] at hlim
  exact hlim

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
