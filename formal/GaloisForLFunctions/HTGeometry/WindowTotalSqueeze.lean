import Mathlib

/-!
# Recovering a total mass from window masses and a uniform tail bound

If a family of nonnegative totals `N i` has window masses `W K i` with

`W K i ≤ N i`  and  `N i (1 − M/K²) ≤ W K i` ,

and each window mass converges to `G K` along the filter while `G K → A` as the window grows, then
the totals converge to `A`.  The second inequality is Chebyshev with a uniform second-moment bound
`M`; the first is monotonicity of the integral.

The point is that no uniform convergence on the whole line is needed: convergence on each fixed
window plus a tail bound that is uniform in the family already pins the total.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The Gaussian mass on a window tends to the total Gaussian mass. -/
theorem tendsto_gaussianWindow :
    Tendsto (fun K : ℝ => ∫ x in (-K)..K, Real.exp (-(x ^ 2))) atTop
      (𝓝 (Real.sqrt Real.pi)) := by
  have hint : MeasureTheory.Integrable fun x : ℝ => Real.exp (-(x ^ 2)) := by
    have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
    simpa using this
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hint
    (Filter.tendsto_neg_atBot_iff.2 Filter.tendsto_id) Filter.tendsto_id
  have hval : (∫ x : ℝ, Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
    have := integral_gaussian (1 : ℝ)
    simpa using this
  rwa [hval] at hlim

/-- **Window squeeze.**  Window convergence plus a uniform Chebyshev tail bound determines the
total. -/
theorem tendsto_total_of_window {ι : Type*} {L : Filter ι}
    {N : ι → ℝ} {W : ℝ → ι → ℝ} {G : ℝ → ℝ} {A M : ℝ}
    (hM : 0 < M)
    (hWle : ∀ K, 0 < K → M < K ^ 2 → ∀ᶠ i in L, W K i ≤ N i)
    (hWge : ∀ K, 0 < K → M < K ^ 2 → ∀ᶠ i in L, N i * (1 - M / K ^ 2) ≤ W K i)
    (hWlim : ∀ K, 0 < K → M < K ^ 2 → Tendsto (fun i => W K i) L (𝓝 (G K)))
    (hGlim : Tendsto G atTop (𝓝 A)) :
    Tendsto N L (𝓝 A) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower half
    obtain ⟨K, hK, hKpos, hKM⟩ : ∃ K : ℝ, b < G K ∧ 0 < K ∧ M < K ^ 2 := by
      have hsq : Tendsto (fun K : ℝ => K ^ 2) atTop atTop :=
        tendsto_pow_atTop (n := 2) (Nat.succ_ne_zero 1)
      obtain ⟨K, hKa, hKb, hKc⟩ :=
        ((hGlim.eventually (eventually_gt_nhds hb)).and
          ((eventually_gt_atTop (0 : ℝ)).and (hsq.eventually_gt_atTop M))).exists
      exact ⟨K, hKa, hKb, hKc⟩
    filter_upwards [(hWlim K hKpos hKM).eventually (eventually_gt_nhds hK),
      hWle K hKpos hKM] with i hi hle
    exact lt_of_lt_of_le hi hle
  · -- upper half
    have hfac : Tendsto (fun K : ℝ => b * (1 - M / K ^ 2)) atTop (𝓝 (b * (1 - 0))) := by
      have hK2 : Tendsto (fun K : ℝ => M / K ^ 2) atTop (𝓝 0) := by
        have hsq : Tendsto (fun K : ℝ => K ^ 2) atTop atTop :=
          tendsto_pow_atTop (n := 2) (Nat.succ_ne_zero 1)
        exact tendsto_const_nhds.div_atTop hsq
      exact (tendsto_const_nhds.sub hK2).const_mul b
    have hgap : Tendsto (fun K : ℝ => b * (1 - M / K ^ 2) - G K) atTop (𝓝 (b * (1 - 0) - A)) :=
      hfac.sub hGlim
    have hbpos : 0 < b * (1 - 0) - A := by simpa using sub_pos.2 hb
    obtain ⟨K, hK1, hK2, hKpos⟩ :
        ∃ K : ℝ, M < K ^ 2 ∧ G K < b * (1 - M / K ^ 2) ∧ 0 < K := by
      have hpos := hgap.eventually (eventually_gt_nhds hbpos)
      have hbig : ∀ᶠ K : ℝ in atTop, M < K ^ 2 := by
        have hsq : Tendsto (fun K : ℝ => K ^ 2) atTop atTop :=
          tendsto_pow_atTop (n := 2) (Nat.succ_ne_zero 1)
        exact hsq.eventually_gt_atTop M
      obtain ⟨K, hKa, hKb, hKc⟩ := (hpos.and (hbig.and (eventually_gt_atTop (0 : ℝ)))).exists
      exact ⟨K, hKb, by linarith [hKa], hKc⟩
    have hfacpos : (0 : ℝ) < 1 - M / K ^ 2 := by
      have hKsq : (0 : ℝ) < K ^ 2 := lt_trans hM hK1
      rw [sub_pos, div_lt_one hKsq]
      exact hK1
    filter_upwards [(hWlim K hKpos hK1).eventually (eventually_lt_nhds hK2),
      hWge K hKpos hK1] with i hi hle
    have : N i * (1 - M / K ^ 2) < b * (1 - M / K ^ 2) := lt_of_le_of_lt hle hi
    exact lt_of_mul_lt_mul_right (by linarith [this]) hfacpos.le

/-- **Chebyshev tail.**  Outside a symmetric window the mass is controlled by the second moment:
the difference between the total and the window mass is at most `K⁻²` times the total second
moment. -/
theorem window_tail_le_of_secondMoment {f : ℝ → ℝ} {K R : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (hf : Continuous f) :
    (∫ x in (-R)..R, f x ^ 2) - (∫ x in (-K)..K, f x ^ 2)
      ≤ (1 / K ^ 2) * ∫ x in (-R)..R, x ^ 2 * f x ^ 2 := by
  have hsq : Continuous fun x : ℝ => f x ^ 2 := hf.pow 2
  have hmom : Continuous fun x : ℝ => x ^ 2 * f x ^ 2 := (continuous_pow 2).mul hsq
  have hKR' : -R ≤ -K := neg_le_neg hKR
  have hKK : -K ≤ K := by linarith
  -- split both integrals at `±K`
  have hsplitL : (∫ x in (-R)..(-K), f x ^ 2) + ∫ x in (-K)..K, f x ^ 2
      = ∫ x in (-R)..K, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hsq.intervalIntegrable _ _)
      (hsq.intervalIntegrable _ _)
  have hsplitR : (∫ x in (-R)..K, f x ^ 2) + ∫ x in K..R, f x ^ 2
      = ∫ x in (-R)..R, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hsq.intervalIntegrable _ _)
      (hsq.intervalIntegrable _ _)
  have hsplitL' : (∫ x in (-R)..(-K), x ^ 2 * f x ^ 2) + ∫ x in (-K)..K, x ^ 2 * f x ^ 2
      = ∫ x in (-R)..K, x ^ 2 * f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hmom.intervalIntegrable _ _)
      (hmom.intervalIntegrable _ _)
  have hsplitR' : (∫ x in (-R)..K, x ^ 2 * f x ^ 2) + ∫ x in K..R, x ^ 2 * f x ^ 2
      = ∫ x in (-R)..R, x ^ 2 * f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hmom.intervalIntegrable _ _)
      (hmom.intervalIntegrable _ _)
  -- pointwise domination on each tail
  have hdom : ∀ x : ℝ, K ^ 2 ≤ x ^ 2 → f x ^ 2 ≤ 1 / K ^ 2 * (x ^ 2 * f x ^ 2) := by
    intro x hx
    have hK2 : (0 : ℝ) < K ^ 2 := by positivity
    have : (1 : ℝ) ≤ x ^ 2 / K ^ 2 := (le_div_iff₀ hK2).2 (by linarith)
    have hfx : (0 : ℝ) ≤ f x ^ 2 := sq_nonneg _
    calc f x ^ 2 = 1 * f x ^ 2 := (one_mul _).symm
      _ ≤ (x ^ 2 / K ^ 2) * f x ^ 2 := by exact mul_le_mul_of_nonneg_right this hfx
      _ = 1 / K ^ 2 * (x ^ 2 * f x ^ 2) := by ring
  have hleft : (∫ x in (-R)..(-K), f x ^ 2)
      ≤ 1 / K ^ 2 * ∫ x in (-R)..(-K), x ^ 2 * f x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hKR' (hsq.intervalIntegrable _ _)
      ((continuous_const.mul hmom).intervalIntegrable _ _) ?_
    intro x hx
    refine hdom x ?_
    have hx2 : x ≤ -K := hx.2
    nlinarith [hx2, hK]
  have hright : (∫ x in K..R, f x ^ 2)
      ≤ 1 / K ^ 2 * ∫ x in K..R, x ^ 2 * f x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hKR (hsq.intervalIntegrable _ _)
      ((continuous_const.mul hmom).intervalIntegrable _ _) ?_
    intro x hx
    exact hdom x (by nlinarith [hx.1, hK])
  have hmid : (0 : ℝ) ≤ ∫ x in (-K)..K, x ^ 2 * f x ^ 2 :=
    intervalIntegral.integral_nonneg hKK (fun x _ => by positivity)
  have hK2 : (0 : ℝ) < 1 / K ^ 2 := by positivity
  nlinarith [hleft, hright, hmid, hsplitL, hsplitR, hsplitL', hsplitR', hK2]

/-- A symmetric window carries at most the total mass of a nonnegative integrand. -/
theorem window_le_total {f : ℝ → ℝ} {K R : ℝ}
    (hKR : K ≤ R) (hf : Continuous f) :
    (∫ x in (-K)..K, f x ^ 2) ≤ ∫ x in (-R)..R, f x ^ 2 := by
  have hsq : Continuous fun x : ℝ => f x ^ 2 := hf.pow 2
  have hKR' : -R ≤ -K := neg_le_neg hKR
  have hsplitL : (∫ x in (-R)..(-K), f x ^ 2) + ∫ x in (-K)..K, f x ^ 2
      = ∫ x in (-R)..K, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hsq.intervalIntegrable _ _)
      (hsq.intervalIntegrable _ _)
  have hsplitR : (∫ x in (-R)..K, f x ^ 2) + ∫ x in K..R, f x ^ 2
      = ∫ x in (-R)..R, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hsq.intervalIntegrable _ _)
      (hsq.intervalIntegrable _ _)
  have hleft : (0 : ℝ) ≤ ∫ x in (-R)..(-K), f x ^ 2 :=
    intervalIntegral.integral_nonneg hKR' (fun x _ => sq_nonneg _)
  have hright : (0 : ℝ) ≤ ∫ x in K..R, f x ^ 2 :=
    intervalIntegral.integral_nonneg hKR (fun x _ => sq_nonneg _)
  linarith [hsplitL, hsplitR, hleft, hright]

/-- **Tail bound for a symmetric window pairing.**  Two functions with controlled second moments
have window pairings that differ from the total pairing by at most `K⁻²` times the total second
moments. -/
theorem abs_window_pairing_sub_le_of_secondMoment {f g : ℝ → ℝ} {K R : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (hf : Continuous f) (hg : Continuous g) :
    |(∫ x in (-R)..R, f x * g x) - ∫ x in (-K)..K, f x * g x|
      ≤ (1 / (2 * K ^ 2))
        * ((∫ x in (-R)..R, x ^ 2 * f x ^ 2) + ∫ x in (-R)..R, x ^ 2 * g x ^ 2) := by
  have hprod : Continuous fun x : ℝ => f x * g x := hf.mul hg
  have hmom : Continuous fun x : ℝ =>
      1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) :=
    continuous_const.mul (((continuous_pow 2).mul (hf.pow 2)).add
      ((continuous_pow 2).mul (hg.pow 2)))
  have hKR' : -R ≤ -K := neg_le_neg hKR
  have hKK : -K ≤ K := by linarith
  have hdom : ∀ x : ℝ, K ^ 2 ≤ x ^ 2 →
      |f x * g x| ≤ 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) := by
    intro x hx
    have hK2 : (0 : ℝ) < 2 * K ^ 2 := by positivity
    have hbase : |f x * g x| ≤ (f x ^ 2 + g x ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x),
        abs_nonneg (f x), abs_nonneg (g x)]
    have h1 : K ^ 2 * f x ^ 2 ≤ x ^ 2 * f x ^ 2 :=
      mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    have h2 : K ^ 2 * g x ^ 2 ≤ x ^ 2 * g x ^ 2 :=
      mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    have hscale : (f x ^ 2 + g x ^ 2) / 2
        ≤ 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hK2]
      nlinarith [h1, h2]
    exact le_trans hbase hscale
  have hsL : (∫ x in (-R)..(-K), f x * g x) + ∫ x in (-K)..K, f x * g x
      = ∫ x in (-R)..K, f x * g x :=
    intervalIntegral.integral_add_adjacent_intervals (hprod.intervalIntegrable _ _)
      (hprod.intervalIntegrable _ _)
  have hsR : (∫ x in (-R)..K, f x * g x) + ∫ x in K..R, f x * g x
      = ∫ x in (-R)..R, f x * g x :=
    intervalIntegral.integral_add_adjacent_intervals (hprod.intervalIntegrable _ _)
      (hprod.intervalIntegrable _ _)
  have hmL : (∫ x in (-R)..(-K), 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2))
      + ∫ x in (-K)..K, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2)
      = ∫ x in (-R)..K, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) :=
    intervalIntegral.integral_add_adjacent_intervals (hmom.intervalIntegrable _ _)
      (hmom.intervalIntegrable _ _)
  have hmR : (∫ x in (-R)..K, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2))
      + ∫ x in K..R, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2)
      = ∫ x in (-R)..R, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) :=
    intervalIntegral.integral_add_adjacent_intervals (hmom.intervalIntegrable _ _)
      (hmom.intervalIntegrable _ _)
  have hleft : |∫ x in (-R)..(-K), f x * g x|
      ≤ ∫ x in (-R)..(-K), 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hKR') ?_
    refine intervalIntegral.integral_mono_on hKR' ((hprod.abs).intervalIntegrable _ _)
      (hmom.intervalIntegrable _ _) (fun x hx => hdom x ?_)
    nlinarith [hx.2, hK]
  have hright : |∫ x in K..R, f x * g x|
      ≤ ∫ x in K..R, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hKR) ?_
    refine intervalIntegral.integral_mono_on hKR ((hprod.abs).intervalIntegrable _ _)
      (hmom.intervalIntegrable _ _) (fun x hx => hdom x ?_)
    nlinarith [hx.1, hK]
  have hmid : (0 : ℝ) ≤ ∫ x in (-K)..K, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2) :=
    intervalIntegral.integral_nonneg hKK (fun x _ => by positivity)
  have hfull : (∫ x in (-R)..R, 1 / (2 * K ^ 2) * (x ^ 2 * f x ^ 2 + x ^ 2 * g x ^ 2))
      = (1 / (2 * K ^ 2))
        * ((∫ x in (-R)..R, x ^ 2 * f x ^ 2) + ∫ x in (-R)..R, x ^ 2 * g x ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_add
      (((continuous_pow 2).mul (hf.pow 2)).intervalIntegrable _ _)
      (((continuous_pow 2).mul (hg.pow 2)).intervalIntegrable _ _)
  have hdiff : (∫ x in (-R)..R, f x * g x) - ∫ x in (-K)..K, f x * g x
      = (∫ x in (-R)..(-K), f x * g x) + ∫ x in K..R, f x * g x := by
    linarith [hsL, hsR]
  rw [hdiff]
  refine le_trans (abs_add_le _ _) ?_
  linarith [hleft, hright, hmid, hmL, hmR, hfull]

/-- **Uniform total mass from a window bound.**  A pointwise bound on a fixed window, together with
a second-moment estimate, caps the total mass — with a constant that does not depend on the outer
radius. -/
theorem total_mass_le_of_window_bound {f : ℝ → ℝ} {S K B mu : ℝ}
    (hK : 0 < K) (hKS : K ≤ S) (hf : Continuous f)
    (hB : ∀ x ∈ Set.Icc (-K) K, |f x| ≤ B)
    (hmom : (∫ x in (-S)..S, x ^ 2 * f x ^ 2) ≤ mu * ∫ x in (-S)..S, f x ^ 2) :
    (∫ x in (-S)..S, f x ^ 2) * (1 - mu / K ^ 2) ≤ 2 * K * B ^ 2 := by
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have hKK : (-K : ℝ) ≤ K := by linarith
  -- the window mass is at most `2K B²`
  have hwin : (∫ x in (-K)..K, f x ^ 2) ≤ 2 * K * B ^ 2 := by
    have hconst : (∫ x in (-K)..K, B ^ 2) = 2 * K * B ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on hKK ((hf.pow 2).intervalIntegrable _ _)
      intervalIntegrable_const fun x hx => ?_
    have hbx := hB x hx
    nlinarith [abs_nonneg (f x), sq_abs (f x), hbx]
  -- Chebyshev bounds the tail
  have htail := window_tail_le_of_secondMoment hK hKS hf
  have hstep : (∫ x in (-S)..S, f x ^ 2) - (∫ x in (-K)..K, f x ^ 2)
      ≤ (1 / K ^ 2) * (mu * ∫ x in (-S)..S, f x ^ 2) := by
    refine le_trans htail ?_
    exact mul_le_mul_of_nonneg_left hmom (by positivity)
  have hdiv : (1 / K ^ 2) * (mu * ∫ x in (-S)..S, f x ^ 2)
      = (mu / K ^ 2) * ∫ x in (-S)..S, f x ^ 2 := by
    field_simp
  rw [hdiv] at hstep
  nlinarith [hstep, hwin]

end GaloisForLFunctions.HTGeometry
