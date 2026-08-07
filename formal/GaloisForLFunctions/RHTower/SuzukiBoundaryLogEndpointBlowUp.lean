import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilForm

/-!
# The endpoint logarithm of the restricted Weil form

The finite part of the Cauchy kernel splits into a divided-difference integral and the exact term
`u(x) log (a² − x²)`.  For a Lipschitz weight the divided difference is *bounded* on the whole
aperture, by the Lipschitz constant times the length, so the entire endpoint behaviour of the form's
representative sits in the logarithm.  Consequently, for a weight that is positive at the right
endpoint — the exponential is the case Suzuki's source uses — the representative of `−½` times the
finite part diverges to `+∞` there, and therefore cannot be a scalar multiple of a bounded weight.

Nothing here needs an unbounded operator: the statements are about `cauchyFinitePart`, which is an
explicit pair of interval integrals.
-/

open MeasureTheory intervalIntegral Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The divided-difference part of the finite part. -/
def cauchyDividedDifference (a x : ℝ) (u : ℝ → ℝ) : ℝ :=
  (∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) + ∫ y in x..a, (u y - u x) * (y - x)⁻¹

theorem cauchyFinitePart_eq_dividedDifference_add (a x : ℝ) (u : ℝ → ℝ) :
    cauchyFinitePart a x u = cauchyDividedDifference a x u + u x * Real.log (a ^ 2 - x ^ 2) := by
  rw [cauchyFinitePart, cauchyDividedDifference]

/-! ## The divided difference is bounded -/

private theorem abs_dividedDifference_integrand_le {u : ℝ → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (x y : ℝ) :
    |(u y - u x) * (x - y)⁻¹| ≤ L := by
  rcases eq_or_ne y x with rfl | hne
  · simp
  · have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hlip : |u y - u x| ≤ (L : ℝ) * |y - x| := by
      have := hu.dist_le_mul y x
      simpa [Real.dist_eq] using this
    rw [abs_mul, abs_inv]
    have hpos : 0 < |x - y| := abs_pos.mpr hxy
    have habs : |x - y| = |y - x| := abs_sub_comm x y
    rw [habs] at hpos
    rw [habs, inv_eq_one_div, ← div_eq_mul_one_div, div_le_iff₀ hpos]
    exact hlip

/-- **Uniform bound on the divided difference.**  A Lipschitz weight makes the divided-difference
part of the finite part bounded by the Lipschitz constant times the aperture length, uniformly in
the interior point. -/
theorem abs_cauchyDividedDifference_le {a x : ℝ} {u : ℝ → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (_ha : 0 ≤ a) (hxa : -a ≤ x) (hax : x ≤ a) :
    |cauchyDividedDifference a x u| ≤ 2 * a * L := by
  have hleftN : ‖∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹‖ ≤ (L : ℝ) * |x - -a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => by
      simpa [Real.norm_eq_abs] using abs_dividedDifference_integrand_le hu x y
  have hrightN : ‖∫ y in x..a, (u y - u x) * (y - x)⁻¹‖ ≤ (L : ℝ) * |a - x| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => by
      have hb := abs_dividedDifference_integrand_le hu x y
      have hswap : |(u y - u x) * (y - x)⁻¹| = |(u y - u x) * (x - y)⁻¹| := by
        rw [abs_mul, abs_mul, abs_inv, abs_inv, abs_sub_comm y x]
      rw [Real.norm_eq_abs, hswap]
      exact hb
  rw [Real.norm_eq_abs] at hleftN hrightN
  have h1 : |x - -a| = x + a := by
    rw [abs_of_nonneg (by linarith)]; ring
  have h2 : |a - x| = a - x := abs_of_nonneg (by linarith)
  rw [h1] at hleftN
  rw [h2] at hrightN
  have htri := abs_add_le (∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹)
    (∫ y in x..a, (u y - u x) * (y - x)⁻¹)
  rw [cauchyDividedDifference]
  nlinarith [htri, hleftN, hrightN, NNReal.coe_nonneg L]

/-! ## The endpoint blow-up -/

private theorem tendsto_log_aperture (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.log (a ^ 2 - x ^ 2)) (𝓝[<] a) atBot := by
  have hinner : Tendsto (fun x : ℝ => a ^ 2 - x ^ 2) (𝓝[<] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => a ^ 2 - x ^ 2) (𝓝[<] a) (𝓝 (a ^ 2 - a ^ 2)) :=
        ((continuous_const.sub (continuous_pow 2)).tendsto a).mono_left nhdsWithin_le_nhds
      simpa using this
    · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds (by linarith : -a < a))] with x hx hx'
      have hx1 : x < a := hx
      have hgoal : (0 : ℝ) < a ^ 2 - x ^ 2 := by nlinarith [hx1, hx']
      exact hgoal
  exact Real.tendsto_log_nhdsGT_zero.comp hinner

/-- **Endpoint blow-up.**  For a Lipschitz weight that is positive at the right endpoint, minus one
half of the Cauchy finite part diverges to `+∞` there.  This is the exact source of the endpoint
logarithmic singularity of the restricted Weil form's representative. -/
theorem tendsto_neg_half_cauchyFinitePart_atTop {a : ℝ} {u : ℝ → ℝ} {L : NNReal}
    (ha : 0 < a) (hu : LipschitzWith L u) (hpos : 0 < u a) :
    Tendsto (fun x : ℝ => -(1 / 2) * cauchyFinitePart a x u) (𝓝[<] a) atTop := by
  have hcont : ContinuousWithinAt u (Iio a) a := (hu.continuous.continuousAt).continuousWithinAt
  have hlog := tendsto_log_aperture a ha
  have hutend : Tendsto u (𝓝[<] a) (𝓝 (u a)) := hcont
  have hmul : Tendsto (fun x : ℝ => u x * Real.log (a ^ 2 - x ^ 2)) (𝓝[<] a) atBot :=
    Filter.Tendsto.pos_mul_atBot hpos hutend hlog
  have hbound : ∀ᶠ x in 𝓝[<] a, |cauchyDividedDifference a x u| ≤ 2 * a * L := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds (by linarith : -a < a))] with x hx hx'
    exact abs_cauchyDividedDifference_le hu ha.le (le_of_lt hx') (le_of_lt hx)
  have hshift : Tendsto (fun x : ℝ => u x * Real.log (a ^ 2 - x ^ 2) + 2 * a * (L : ℝ))
      (𝓝[<] a) atBot := tendsto_atBot_add_const_right _ (2 * a * (L : ℝ)) hmul
  have hsum : Tendsto (fun x : ℝ => cauchyFinitePart a x u) (𝓝[<] a) atBot := by
    refine tendsto_atBot_mono' _ ?_ hshift
    filter_upwards [hbound] with x hx
    rw [cauchyFinitePart_eq_dividedDifference_add]
    have hb := abs_le.mp hx
    linarith [hb.2]
  have hconst : Tendsto (fun _ : ℝ => (-(1 / 2) : ℝ)) (𝓝[<] a) (𝓝 (-(1 / 2))) :=
    tendsto_const_nhds
  exact Filter.Tendsto.neg_mul_atBot (by norm_num) hconst hsum

/-- **Not a scalar multiple.**  A bounded weight cannot represent minus one half of the Cauchy
finite part of a Lipschitz weight positive at the endpoint, since the latter is unbounded there. -/
theorem not_bounded_of_tendsto_neg_half_cauchyFinitePart {a : ℝ} {u w : ℝ → ℝ} {L : NNReal}
    (ha : 0 < a) (hu : LipschitzWith L u) (hpos : 0 < u a) {C : ℝ}
    (hw : ∀ x, |w x| ≤ C)
    (heq : ∀ x, -(1 / 2) * cauchyFinitePart a x u = w x) : False := by
  have hdiv := tendsto_neg_half_cauchyFinitePart_atTop ha hu hpos
  have hle : ∀ᶠ x in 𝓝[<] a, C + 1 ≤ -(1 / 2) * cauchyFinitePart a x u :=
    hdiv.eventually_ge_atTop (C + 1)
  obtain ⟨x, hx⟩ := hle.exists
  rw [heq x] at hx
  have := hw x
  have := abs_le.mp this
  linarith [this.2]

end GaloisForLFunctions.RHTower
