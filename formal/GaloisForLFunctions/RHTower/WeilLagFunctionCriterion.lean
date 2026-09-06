import GaloisForLFunctions.RHTower.WeilLagFunction
import Mathlib.Topology.DiscreteSubset

/-!
# The lag criterion: `RH ⟺ Φ is bounded`

`Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` is bounded on `ℝ` if and only if the Riemann hypothesis holds.
Under RH, `|Φ| ≤ Φ(0)`.  Conversely, if `Φ` is bounded, its Mellin transform
`F(s) = ∫_0^∞ Φ(L) e^{−sL} dL` is holomorphic on `0 < Re s < 2`, while for `Re s > ½` it equals the
Mittag-Leffler series `G(s) = Σ_ρ (ρ(1−ρ))^{−1}/(s − (ρ − ½))`.  An off-line zero `ρ₀` with
`Re ρ₀ > ½`, chosen with maximal real part among the (finitely many) zeros on its horizontal line,
gives a pole `p₀ = ρ₀ − ½` of `G` in `0 < Re < ½` whose horizontal ray to the right is pole-free;
the identity theorem along that ray transports `F = G` down to the pole, where `G` is unbounded and
`F` is continuous.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The zero set of `ξ` -/

theorem xi_analyticAt (z : ℂ) : AnalyticAt ℂ xi z := xi_differentiable.analyticAt z

theorem xi_not_eventually_zero (ρ : ℂ) : ¬ ∀ᶠ z in 𝓝 ρ, xi z = 0 := by
  intro h
  have hall : AnalyticOnNhd ℂ xi Set.univ := fun z _ => xi_analyticAt z
  have := hall.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ ρ) h
  have h1 := this (Set.mem_univ 1)
  rw [xi_one] at h1
  norm_num at h1

/-- Zeros of `ξ` are isolated. -/
theorem xi_zero_isolated {ρ : ℂ} (_hρ : xi ρ = 0) :
    ∃ ε > 0, ∀ z : ℂ, xi z = 0 → dist z ρ < ε → z = ρ := by
  rcases (xi_analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (xi_not_eventually_zero ρ)
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hball⟩ := h
    refine ⟨ε, hε, fun z hz hd => by_contra fun hne => ?_⟩
    exact hball hd (by simpa using hne) hz

/-- The zero set of `ξ`. -/
def xiZeroSet : Set ℂ := {z | xi z = 0}

theorem isClosed_xiZeroSet : IsClosed xiZeroSet :=
  isClosed_eq xi_differentiable.continuous continuous_const

theorem isDiscrete_xiZeroSet : IsDiscrete xiZeroSet := by
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  obtain ⟨ε, hε, hiso⟩ := xi_zero_isolated hx
  rw [Filter.inf_principal_eq_bot, ← Filter.eventually_mem_set, eventually_nhdsWithin_iff,
    Metric.eventually_nhds_iff]
  refine ⟨ε, hε, fun y hy hne hyZ => ?_⟩
  exact (by simpa using hne : y ≠ x) (hiso y hyZ hy)

theorem finite_xiZeroSet_inter {K : Set ℂ} (hK : IsCompact K) : (xiZeroSet ∩ K).Finite :=
  (hK.inter_left isClosed_xiZeroSet).finite (isDiscrete_xiZeroSet.mono inter_subset_left)

/-- A zero of `ξ` has positive divisor multiplicity. -/
theorem xi_divisor_pos_of_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    0 < (MeromorphicOn.divisor xi Set.univ) ρ := by
  rw [MeromorphicOn.divisor_apply (fun z _ => (xi_analyticAt z).meromorphicAt) (Set.mem_univ ρ),
    (xi_analyticAt ρ).meromorphicOrderAt_eq]
  have hne : analyticOrderAt xi ρ ≠ 0 := (xi_analyticAt ρ).analyticOrderAt_ne_zero.mpr hρ
  have htop : analyticOrderAt xi ρ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact xi_not_eventually_zero ρ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at hne ⊢
  have hn0 : n ≠ 0 := by rintro rfl; exact hne rfl
  rw [ENat.map_coe, WithTop.untop₀_coe]
  exact_mod_cast Nat.pos_of_ne_zero hn0

/-- Every zero of `ξ` is the value of a copy. -/
theorem exists_xiZeroCopy_of_xi_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    ∃ q : XiZeroCopy, (q.1 : ℂ) = ρ := by
  have hpos := xi_divisor_pos_of_eq_zero hρ
  have hmem : ρ ∈ (MeromorphicOn.divisor xi Set.univ).support := Function.mem_support.mpr hpos.ne'
  exact ⟨⟨⟨ρ, hmem⟩, ⟨0, Int.lt_toNat.mpr (by simpa using hpos)⟩⟩, rfl⟩

/-- If RH fails, some copy has real part greater than `½`. -/
theorem exists_xiZeroCopy_re_gt_half_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 1 / 2 < ((q.1 : ℂ)).re := by
  unfold RiemannHypothesis at h
  push Not at h
  obtain ⟨s, hζ, htriv, h1, hre⟩ := h
  have hxi : xi s = 0 := xi_eq_zero_of_zeta_eq_zero hζ (fun ⟨n, hn⟩ => htriv n hn) h1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · refine ⟨xiZeroCopyReflectEquiv q, ?_⟩
    rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re, hq]
    linarith
  · exact ⟨q, by rw [hq]; exact hgt⟩

/-! ## The Mittag-Leffler series -/

/-- The pole `ρ − ½` of a copy. -/
def lagPole (q : XiZeroCopy) : ℂ := (q.1 : ℂ) - 1 / 2

/-- The weight `1/(ρ(1−ρ))` of a copy. -/
def lagWeight (q : XiZeroCopy) : ℂ := 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

/-- `G(s) = Σ_ρ (ρ(1−ρ))^{−1}/(s − (ρ − ½))`. -/
def lagPoleSeries (s : ℂ) : ℂ := ∑' q : XiZeroCopy, lagWeight q / (s - lagPole q)

theorem summable_norm_lagWeight : Summable (fun q : XiZeroCopy => ‖lagWeight q‖) :=
  summable_inv_mul_one_sub.norm

theorem lagPole_add_half (q : XiZeroCopy) : lagPole q + 1 / 2 = (q.1 : ℂ) := by
  unfold lagPole; ring

theorem lagPole_re_lt_half (q : XiZeroCopy) : (lagPole q).re < 1 / 2 := by
  unfold lagPole
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  linarith [xiZeroCopy_re_lt_one q]

theorem lagPole_re_gt (q : XiZeroCopy) : -1 / 2 < (lagPole q).re := by
  unfold lagPole
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  linarith [xiZeroCopy_re_pos q]

/-- Away from the poles the series is differentiable. -/
theorem differentiableAt_lagPoleSeries {s₁ : ℂ} (h : xi (s₁ + 1 / 2) ≠ 0) :
    DifferentiableAt ℂ lagPoleSeries s₁ := by
  have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (s₁ + 1 / 2) h
  -- every pole is at distance ≥ δ/2 from every point of `ball s₁ (δ/2)`
  have hfar : ∀ s ∈ Metric.ball s₁ (δ / 2), ∀ q : XiZeroCopy, δ / 2 ≤ ‖s - lagPole q‖ := by
    intro s hs q
    have hq : (q.1 : ℂ) ∉ Metric.ball (s₁ + 1 / 2) δ := fun hmem =>
      hball hmem (xi_xiZeroCopy_eq_zero q)
    rw [Metric.mem_ball, not_lt, Complex.dist_eq] at hq
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have e : s - lagPole q = ((q.1 : ℂ) - (s₁ + 1 / 2)) * (-1) + (s - s₁) := by
      unfold lagPole; ring
    rw [e]
    have := norm_add_le (((q.1 : ℂ) - (s₁ + 1 / 2)) * (-1)) (s - s₁)
    rw [norm_mul, norm_neg, norm_one, mul_one] at this
    have h2 := norm_sub_norm_le (((q.1 : ℂ) - (s₁ + 1 / 2)) * (-1)) (-(s - s₁))
    rw [norm_mul, norm_neg, norm_one, mul_one, norm_neg, sub_neg_eq_add] at h2
    linarith
  have hdiff : DifferentiableOn ℂ lagPoleSeries (Metric.ball s₁ (δ / 2)) := by
    unfold lagPoleSeries
    refine differentiableOn_tsum_of_summable_norm
      (u := fun q => ‖lagWeight q‖ * (2 / δ)) (summable_norm_lagWeight.mul_right _) (fun q => ?_)
      Metric.isOpen_ball (fun q s hs => ?_)
    · refine (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _))
        fun s hs => ?_
      have := hfar s hs q
      intro h0
      rw [h0, norm_zero] at this
      linarith
    · rw [norm_div]
      have := hfar s hs q
      have hpos : 0 < ‖s - lagPole q‖ := by linarith
      rw [div_le_iff₀ hpos]
      calc ‖lagWeight q‖ = ‖lagWeight q‖ * (2 / δ) * (δ / 2) := by field_simp
        _ ≤ ‖lagWeight q‖ * (2 / δ) * ‖s - lagPole q‖ := by gcongr
  exact hdiff.differentiableAt (Metric.ball_mem_nhds _ (by positivity))

/-- Near a pole the series is unbounded: `‖G(p₀ + t)‖ ≥ ‖w₀‖/t − C` for small `t > 0`. -/
theorem norm_lagPoleSeries_ge (q₀ : XiZeroCopy) :
    ∃ ε > 0, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < ε →
      ‖lagWeight q₀‖ / t - C ≤ ‖lagPoleSeries (lagPole q₀ + t)‖ := by
  obtain ⟨ε, hε, hiso⟩ := xi_zero_isolated (xi_xiZeroCopy_eq_zero q₀)
  refine ⟨ε / 2, by positivity, (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖, fun t ht htε => ?_⟩
  set S : Set XiZeroCopy := {q | q.1 = q₀.1} with hS
  -- distances: copies off `S` have poles at distance ≥ ε/2 from `p₀ + t`
  have hoff : ∀ q : XiZeroCopy, q ∉ S → ε / 2 ≤ ‖lagPole q₀ + t - lagPole q‖ := by
    intro q hq
    have hne : (q.1 : ℂ) ≠ (q₀.1 : ℂ) := fun h => hq (Subtype.ext h)
    have hdist : ε ≤ dist (q.1 : ℂ) (q₀.1 : ℂ) := by
      by_contra hlt
      exact hne (hiso _ (xi_xiZeroCopy_eq_zero q) (not_le.mp hlt))
    rw [Complex.dist_eq] at hdist
    have e : lagPole q₀ + t - lagPole q = -((q.1 : ℂ) - (q₀.1 : ℂ)) + t := by unfold lagPole; ring
    rw [e]
    have h2 := norm_sub_norm_le (-((q.1 : ℂ) - (q₀.1 : ℂ))) (-(t : ℂ))
    rw [norm_neg, norm_neg, sub_neg_eq_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at h2
    linarith
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- summability of the full series at `p₀ + t`
  have hsumm : Summable (fun q : XiZeroCopy => lagWeight q / (lagPole q₀ + t - lagPole q)) := by
    refine Summable.of_norm_bounded
      (g := fun q => ‖lagWeight q‖ * max (1 / t) (2 / ε)) (summable_norm_lagWeight.mul_right _)
      fun q => ?_
    rw [norm_div]
    by_cases hq : q ∈ S
    · have hq' : (q.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) hq
      have e : lagPole q₀ + t - lagPole q = t := by unfold lagPole; rw [hq']; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, div_eq_mul_one_div]
      gcongr
      exact le_max_left _ _
    · have := hoff q hq
      have hpos : 0 < ‖lagPole q₀ + t - lagPole q‖ := by linarith
      rw [div_le_iff₀ hpos]
      calc ‖lagWeight q‖ = ‖lagWeight q‖ * (2 / ε) * (ε / 2) := by field_simp
        _ ≤ ‖lagWeight q‖ * max (1 / t) (2 / ε) * ‖lagPole q₀ + t - lagPole q‖ := by
            gcongr
            exact le_max_right _ _
  unfold lagPoleSeries
  rw [← hsumm.tsum_subtype_add_tsum_subtype_compl S]
  -- the fibre sum is `card S • (w₀/t)`
  have hfib : ∀ q : S, lagWeight q.1 / (lagPole q₀ + t - lagPole q.1) = lagWeight q₀ / t := by
    intro q
    have hq' : (q.1.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) q.2
    unfold lagWeight lagPole
    rw [hq']
    ring
  rw [tsum_congr hfib, tsum_const]
  have hfin : Finite S := by
    refine Finite.of_injective
      (fun x : S => (⟨(x.1.2 : ℕ), lt_of_lt_of_eq x.1.2.isLt (by
        rw [show x.1.1 = q₀.1 from x.2])⟩ :
          Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)))))
      fun x y hxy => ?_
    have hv : (x.1.2 : ℕ) = (y.1.2 : ℕ) := by
      have := congrArg Fin.val hxy
      simpa using this
    apply Subtype.ext
    apply Sigma.ext
    · exact x.2.trans y.2.symm
    · have hx : x.1.1 = q₀.1 := x.2
      have hy : y.1.1 = q₀.1 := y.2
      exact (Fin.heq_ext_iff (by rw [hx, hy])).mpr hv
  have hne : Nonempty S := ⟨⟨q₀, rfl⟩⟩
  have hcard : 1 ≤ Nat.card S := Nat.card_pos
  -- the complementary sum is bounded by `C`
  have hcompl : ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖ ≤
      (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
    have hb : ∀ q : ↑Sᶜ, ‖lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖ ≤
        (2 / ε) * ‖lagWeight q.1‖ := by
      intro q
      have := hoff q.1 q.2
      have hpos : 0 < ‖lagPole q₀ + t - lagPole q.1‖ := by linarith
      rw [norm_div, div_le_iff₀ hpos]
      calc ‖lagWeight q.1‖ = (2 / ε) * ‖lagWeight q.1‖ * (ε / 2) := by field_simp
        _ ≤ (2 / ε) * ‖lagWeight q.1‖ * ‖lagPole q₀ + t - lagPole q.1‖ := by gcongr
    have hs1 : Summable (fun q : ↑Sᶜ => ‖lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖) :=
      (hsumm.norm.subtype _)
    have hs2 : Summable (fun q : ↑Sᶜ => (2 / ε) * ‖lagWeight q.1‖) :=
      (summable_norm_lagWeight.mul_left _).subtype _
    calc ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖
        ≤ ∑' q : ↑Sᶜ, ‖lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖ :=
          norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : ↑Sᶜ, (2 / ε) * ‖lagWeight q.1‖ := hs1.tsum_le_tsum hb hs2
      _ = (2 / ε) * ∑' q : ↑Sᶜ, ‖lagWeight q.1‖ := tsum_mul_left
      _ ≤ (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
          gcongr
          exact Summable.tsum_subtype_le (fun q : XiZeroCopy => ‖lagWeight q‖) Sᶜ
            (fun _ => norm_nonneg _) summable_norm_lagWeight
  have hmain : ‖lagWeight q₀‖ / t ≤ ‖Nat.card S • (lagWeight q₀ / t)‖ := by
    rw [nsmul_eq_mul, norm_mul, Complex.norm_natCast, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    have : (1 : ℝ) ≤ Nat.card S := by exact_mod_cast hcard
    calc ‖lagWeight q₀‖ / t = 1 * (‖lagWeight q₀‖ / t) := by ring
      _ ≤ (Nat.card S : ℝ) * (‖lagWeight q₀‖ / t) := by gcongr
  calc ‖lagWeight q₀‖ / t - (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖
      ≤ ‖Nat.card S • (lagWeight q₀ / t)‖ -
          ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖ := by linarith
    _ ≤ ‖Nat.card S • (lagWeight q₀ / t) +
          ∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)‖ := by
        have := norm_sub_norm_le (Nat.card S • (lagWeight q₀ / t))
          (-(∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + t - lagPole q.1)))
        rw [norm_neg, sub_neg_eq_add] at this
        exact this

/-! ## The Mellin transform of the lag function -/

theorem measurable_weilLagFunction : Measurable weilLagFunction := by
  unfold weilLagFunction
  refine Measurable.tsum fun q => ?_
  exact (Complex.measurable_exp.comp (Complex.measurable_ofReal.mul_const _)).div_const _

/-- The window `y ↦ Φ(−log y)` on `(0,1)`, extended by zero. -/
def lagWindow (y : ℝ) : ℂ :=
  Set.indicator (Ioo (0:ℝ) 1) (fun y => weilLagFunction (-Real.log y)) y

theorem measurable_lagWindow : Measurable lagWindow :=
  (measurable_weilLagFunction.comp Real.measurable_log.neg).indicator measurableSet_Ioo

theorem norm_lagWindow_le {M : ℝ} (hM : ∀ L, ‖weilLagFunction L‖ ≤ M) (y : ℝ) :
    ‖lagWindow y‖ ≤ M := by
  unfold lagWindow
  by_cases hy : y ∈ Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem hy]; exact hM _
  · rw [Set.indicator_of_notMem hy, norm_zero]; exact (norm_nonneg _).trans (hM 0)

theorem integral_Ioo_rpow {a : ℝ} (ha : -1 < a) : ∫ y in Ioo (0:ℝ) 1, y ^ a = 1 / (a + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl ha), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

theorem integrableOn_Ioo_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun y : ℝ => y ^ a) (Ioo (0:ℝ) 1) := by
  have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) ha)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  exact this.mono_set Ioo_subset_Ioc_self

/-- On `Re s > ½` the Mellin transform of the window is the Mittag-Leffler series. -/
theorem mellin_lagWindow {s : ℂ} (hs : 1 / 2 < s.re) : mellin lagWindow s = lagPoleSeries s := by
  unfold mellin lagWindow lagPoleSeries
  have hind : (fun y : ℝ => (y : ℂ) ^ (s - 1) •
      Set.indicator (Ioo (0:ℝ) 1) (fun y => weilLagFunction (-Real.log y)) y)
      = Set.indicator (Ioo (0:ℝ) 1)
          (fun y => ∑' q : XiZeroCopy, lagWeight q * (y : ℂ) ^ (s - 1 - lagPole q)) := by
    funext y
    by_cases hy : y ∈ Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, smul_eq_mul]
      unfold weilLagFunction
      rw [← tsum_mul_left]
      refine tsum_congr fun q => ?_
      have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.1.ne'
      have hlog : Complex.log (y : ℂ) = (Real.log y : ℂ) := (Complex.ofReal_log hy.1.le).symm
      have hexp : Complex.exp (((-Real.log y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) =
          (y : ℂ) ^ (-lagPole q) := by
        rw [Complex.cpow_def_of_ne_zero hy0, hlog]
        congr 1
        unfold lagPole
        push_cast
        ring
      rw [hexp, show (y : ℂ) ^ (s - 1 - lagPole q) = (y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-lagPole q) by
        rw [← Complex.cpow_add _ _ hy0]; ring_nf]
      unfold lagWeight
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
  rw [hind, setIntegral_indicator measurableSet_Ioo,
    show Ioi (0:ℝ) ∩ Ioo 0 1 = Ioo 0 1 from inter_eq_right.mpr Ioo_subset_Ioi_self]
  have hre : ∀ q : XiZeroCopy, -1 < (s - 1 - lagPole q).re := by
    intro q
    simp only [Complex.sub_re, Complex.one_re]
    linarith [lagPole_re_lt_half q]
  have hint : ∀ q : XiZeroCopy,
      IntegrableOn (fun y : ℝ => lagWeight q * (y : ℂ) ^ (s - 1 - lagPole q)) (Ioo (0:ℝ) 1) :=
    fun q => (integrableOn_Ioo_cpow (hre q)).const_mul _
  have hnorm : Summable (fun q : XiZeroCopy =>
      ∫ y in Ioo (0:ℝ) 1, ‖lagWeight q * (y : ℂ) ^ (s - 1 - lagPole q)‖) := by
    have ha : (-1 : ℝ) < s.re - 3 / 2 := by linarith
    have hK : ∀ q : XiZeroCopy, ∫ y in Ioo (0:ℝ) 1, ‖lagWeight q * (y : ℂ) ^ (s - 1 - lagPole q)‖
        ≤ ‖lagWeight q‖ * (1 / (s.re - 3 / 2 + 1)) := by
      intro q
      rw [← integral_Ioo_rpow ha, ← integral_const_mul]
      refine setIntegral_mono_on (hint q).norm ((integrableOn_Ioo_rpow ha).const_mul _)
        measurableSet_Ioo fun y hy => ?_
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy.1]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_ge hy.1 hy.2.le
      simp only [Complex.sub_re, Complex.one_re]
      linarith [lagPole_re_lt_half q]
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hK
      (summable_norm_lagWeight.mul_right _)
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  refine tsum_congr fun q => ?_
  rw [integral_const_mul, integral_Ioo_cpow (hre q)]
  congr 1
  ring

/-- If `Φ` is bounded, the Mellin transform of the window is holomorphic on `0 < Re s < 2`. -/
theorem differentiableAt_mellin_lagWindow {M : ℝ} (hM : ∀ L, ‖weilLagFunction L‖ ≤ M) {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) : DifferentiableAt ℂ (mellin lagWindow) s := by
  have hint : Integrable lagWindow := by
    unfold lagWindow
    rw [integrable_indicator_iff measurableSet_Ioo]
    refine Measure.integrableOn_of_bounded (M := M) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measurable_weilLagFunction.comp Real.measurable_log.neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hM _)
  refine mellin_differentiableAt_of_isBigO_rpow (a := 2) (b := 0)
    (hint.locallyIntegrable.locallyIntegrableOn (Ioi 0)) ?_ hs2 ?_ hs0
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with y hy
    have : lagWindow y = 0 :=
      Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hy)) _
    rw [this, norm_zero, zero_mul]
  · refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact norm_lagWindow_le hM y

/-! ## The criterion -/

/-- **Bounded lag function implies RH.** -/
theorem riemannHypothesis_of_weilLagFunction_bounded {M : ℝ}
    (hM : ∀ L, ‖weilLagFunction L‖ ≤ M) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : 1 / 2 < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := xiZeroCopy_re_lt_one q₀ |> fun h => by rwa [hq₀] at h
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  set p₀ : ℂ := lagPole q₀ with hp₀
  have hp₀re : p₀.re = ρ₀.re - 1 / 2 := by
    rw [hp₀]; unfold lagPole; rw [hq₀]; simp
  have hp₀pos : 0 < p₀.re := by rw [hp₀re]; linarith
  have hp₀half : p₀.re < 1 / 2 := by rw [hp₀re]; linarith
  -- the horizontal ray to the right of `p₀` carries no zero of `ξ(· + ½)`
  have hray : ∀ t : ℝ, 0 < t → xi (p₀ + t + 1 / 2) ≠ 0 := by
    intro t ht hzero
    have hval : p₀ + t + 1 / 2 = ρ₀ + t := by rw [hp₀]; unfold lagPole; rw [hq₀]; ring
    rw [hval] at hzero
    by_cases hle : (ρ₀ + t).re ≤ 1
    · have hmemK : ρ₀ + t ∈ xiZeroSet ∩ K := by
        refine ⟨hzero, ?_⟩
        rw [hK, Complex.mem_reProdIm]
        refine ⟨⟨?_, hle⟩, ?_⟩
        · simp only [Complex.add_re, Complex.ofReal_re]; linarith [hρ₀K.1.1]
        · simp only [Complex.add_im, Complex.ofReal_im, add_zero, him₀]; exact ⟨le_rfl, le_rfl⟩
      have := hmax _ hmemK (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
      simp only [Complex.add_re, Complex.ofReal_re] at this
      linarith
    · exact xi_ne_zero_of_one_le_re (not_le.mp hle).le hzero
  -- the two analytic functions along the ray
  set ℓ : ℝ → ℂ := fun t => p₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  set V : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 2} with hV
  have hVopen : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hFdiff : DifferentiableOn ℂ (mellin lagWindow) V := fun z hz =>
    (differentiableAt_mellin_lagWindow hM hz.1 hz.2).differentiableWithinAt
  set U : Set ℝ := Ioo (0:ℝ) (2 - p₀.re) with hU
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    simp only [hℓ, hV, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
    constructor <;> linarith [ht.1, ht.2]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => mellin lagWindow (ℓ t)) U := by
    intro t ht
    have hFz : AnalyticAt ℂ (mellin lagWindow) (ℓ t) :=
      hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))
    exact hFz.restrictScalars.comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => lagPoleSeries (ℓ t)) U := by
    intro t ht
    have hGz : AnalyticAt ℂ lagPoleSeries (ℓ t) := by
      have hne : xi (ℓ t + 1 / 2) ≠ 0 := hray t ht.1
      -- differentiable on a neighbourhood: all points near `ℓ t` avoid the zero set
      have hopen : IsOpen {z : ℂ | xi (z + 1 / 2) ≠ 0} :=
        isOpen_ne_fun (xi_differentiable.continuous.comp (continuous_id.add continuous_const))
          continuous_const
      refine DifferentiableOn.analyticAt (s := {z : ℂ | xi (z + 1 / 2) ≠ 0}) ?_ (hopen.mem_nhds hne)
      exact fun z hz => (differentiableAt_lagPoleSeries hz).differentiableWithinAt
    exact hGz.restrictScalars.comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h1U : (1 : ℝ) ∈ U := ⟨one_pos, by linarith⟩
  have hfg : (fun t : ℝ => mellin lagWindow (ℓ t)) =ᶠ[𝓝 (1:ℝ)]
      (fun t : ℝ => lagPoleSeries (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2))
      fun t ht => ?_
    apply mellin_lagWindow
    simp only [hℓ, Complex.add_re, Complex.ofReal_re]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h1U hfg
  -- continuity of `F` at `p₀`
  have hFcont : ContinuousAt (mellin lagWindow) p₀ :=
    (differentiableAt_mellin_lagWindow hM hp₀pos (by linarith)).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ)) (𝓝 0) (𝓝 (p₀ + ((0:ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    simpa using this
  have hcomp : Tendsto (fun t : ℝ => mellin lagWindow (ℓ t)) (𝓝 0) (𝓝 (mellin lagWindow p₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  -- the pole bound
  obtain ⟨ε, hε, C, hC⟩ := norm_lagPoleSeries_ge q₀
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hC'' : ∀ t : ℝ, 0 < t → t < ε →
      ‖lagWeight q₀‖ / t - C' ≤ ‖lagPoleSeries (lagPole q₀ + t)‖ :=
    fun t ht htε => le_trans (by linarith [le_max_left C 0]) (hC t ht htε)
  set B : ℝ := ‖mellin lagWindow p₀‖ + 1 with hB
  have hw : 0 < ‖lagWeight q₀‖ := by
    rw [norm_pos_iff]
    unfold lagWeight
    exact one_div_ne_zero (mul_ne_zero (xiZeroCopy_ne_zero q₀) (xiZeroCopy_one_sub_ne_zero q₀))
  have hBpos : 0 < B + C' + 1 := by positivity
  have h2p : 0 < 2 - p₀.re := by linarith
  have hw' : 0 < ‖lagWeight q₀‖ / (B + C' + 1) := div_pos hw hBpos
  set m : ℝ := min (min δ ε) (min (2 - p₀.re) (‖lagWeight q₀‖ / (B + C' + 1))) with hm
  have hmpos : 0 < m := lt_min (lt_min hδ hε) (lt_min h2p hw')
  set t₀ : ℝ := m / 2 with ht₀
  have ht₀pos : 0 < t₀ := half_pos hmpos
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hm2 : m ≤ 2 - p₀.re := (min_le_right _ _).trans (min_le_left _ _)
  have hmw : m ≤ ‖lagWeight q₀‖ / (B + C' + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have ht₀δ : t₀ < δ := by rw [ht₀]; linarith
  have ht₀ε : t₀ < ε := by rw [ht₀]; linarith
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, by rw [ht₀]; linarith⟩
  -- `F` is bounded by `B` at `ℓ t₀`
  have hFb : ‖mellin lagWindow (ℓ t₀)‖ ≤ B := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖mellin lagWindow (ℓ t₀)‖
        = ‖(mellin lagWindow (ℓ t₀) - mellin lagWindow p₀) + mellin lagWindow p₀‖ := by
          congr 1; ring
      _ ≤ ‖mellin lagWindow (ℓ t₀) - mellin lagWindow p₀‖ + ‖mellin lagWindow p₀‖ :=
          norm_add_le _ _
      _ ≤ 1 + ‖mellin lagWindow p₀‖ := by linarith
      _ = B := by rw [hB]; ring
  -- `G` exceeds `B` at `ℓ t₀`
  have hGb : B < ‖lagPoleSeries (ℓ t₀)‖ := by
    have h1 := hC'' t₀ ht₀pos ht₀ε
    have h2 : 2 * (B + C' + 1) ≤ ‖lagWeight q₀‖ / t₀ := by
      rw [le_div_iff₀ ht₀pos]
      calc 2 * (B + C' + 1) * t₀ ≤ 2 * (B + C' + 1) * (‖lagWeight q₀‖ / (B + C' + 1) / 2) := by
            gcongr
            rw [ht₀]; linarith
        _ = ‖lagWeight q₀‖ := by field_simp
    have hℓt : ℓ t₀ = lagPole q₀ + t₀ := rfl
    rw [hℓt]
    linarith
  have hEq : mellin lagWindow (ℓ t₀) = lagPoleSeries (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-- **The lag criterion.**  `RH ⟺ Φ is bounded`; under RH the bound is `Φ(0) = 2 + γ − log 4π`. -/
theorem riemannHypothesis_iff_weilLagFunction_bounded :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ L : ℝ, ‖weilLagFunction L‖ ≤ M :=
  ⟨fun h => ⟨poleSharpConstant, norm_weilLagFunction_le_of_riemannHypothesis h⟩,
    fun ⟨_, hM⟩ => riemannHypothesis_of_weilLagFunction_bounded hM⟩

end

end RHTower
