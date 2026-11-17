import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheStateIsContinuousWithAPointwiseLawAtTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasOneSignAtTheWallInTheMean

/-!
# The prime wave at the wall is the bounded order of the wall law

**The state is continuous** (`criticalState_exists_continuous_representative`). The critical state has
a representative `Φ` continuous on all of `ℝ`: on `u < 0` it is the glued Green representative of the
window theory, `Φ(u) → 0` at the wall because `Φ(u)² log(1/|u|)` converges, and `Φ = 0` on `[0, ∞)`.
Almost-everywhere bounds of a continuous function hold everywhere, so `|Φ(u)| ≤ C e^{2u}` for all `u`.

**The bounded order** (`criticalState_bounded_order_at_wall`). Beyond the wall
`a F⁺ = κ * F − Σ_n Λ(n) n^{−1/2} F(· − log n)` (collar wave minus prime wave), and the collar kernel
is `κ(t) = −1/(2t) + ρ(t)` with `ρ` continuous on `(0, ∞)` and `|ρ(t)| ≤ 3e^{t/2}`. With the Stieltjes
potential `W(x) = ∫_{v>0} F(−v)/(x + v) dv`, as `x → 0⁺` (essentially)

  `a F⁺(x) + W(x)/2 → ∫ F(u) ρ(−u) du − Σ_n Λ(n) n^{−1/2} Φ(−log n)`.

The first term is archimedean (dominated convergence, `tendsto_collarWave_add_half_wallPotential`).
The same holds with the logarithmic moment `L(x) = ∫_{v>x} F(−v)/v dv` in place of `W(x)`
(`criticalState_bounded_order_at_wall_logMoment`): after the scaling `v = xw`,
`W(x) − L(x) = ∫_{w>0} Φ(−xw) k(w) dw` with an integrable kernel `k`, and `Φ(0) = 0`.
The second is the **prime wave at the wall**: the series `Σ_n Λ(n) n^{−1/2} Φ(x − log n)` converges
uniformly on `x ≤ 1` (`|Φ(u)| ≤ C e^{2u}`, `Σ Λ(n) n^{−3/2} < ∞`), so it is continuous at the wall
(`continuousOn_primeWave`). The leading order `−W(x)/2` of the wall is the same for every model
state; the primes enter at the bounded order, through the values of the state at the points
`−log n`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations _root_.RHTower
open CanonicalSystemOfTheWindowTower (collarKernel)

/-! ### A continuous representative on the line -/

/-- A continuous function dominated almost everywhere by a continuous function is dominated
everywhere: the set where the bound fails is open and null. -/
private theorem le_of_ae_le_of_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ᵐ u ∂volume, f u ≤ g u) (u : ℝ) : f u ≤ g u := by
  by_contra hu
  have hpos := (isOpen_lt hg hf).measure_pos volume ⟨u, lt_of_not_ge hu⟩
  have hnull : volume {v | ¬ f v ≤ g v} = 0 := ae_iff.mp h
  simp only [not_le] at hnull
  exact hpos.ne' hnull

/-- **The critical state is continuous.** It has a representative `Φ` continuous on `ℝ`, zero on
`[0, ∞)`, with `|Φ(u)| ≤ C e^{2u}` everywhere and the pointwise law at the wall. -/
theorem criticalState_exists_continuous_representative {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∀ u, 0 ≤ u → Φ u = 0) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ u, |Φ u| ≤ C * Real.exp (2 * u)) ∧
      Tendsto (fun t : ℝ => Φ (-t) * Real.sqrt (Real.log (1 / t))) (𝓝[>] 0)
        (𝓝 (s * Real.sqrt (8 * criticalAliasCoefficient W₀ *
          ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) ∧
      Tendsto (fun t : ℝ => Φ (-t) ^ 2 * Real.log (1 / t)) (𝓝[>] 0)
        (𝓝 (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) ∧
      ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ t ∈ Ioo 0 k₀, 0 < s * Φ (-t) := by
  have hFd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨s, hs, Φ₀, hc₀, hF₀, hlaw, hsq, k₀, hk₀, hsign⟩ :=
    criticalState_continuous_pointwise_wall_law hW hthreshold hF
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ, Φ = fun u => if u < 0 then Φ₀ u else 0 := ⟨_, rfl⟩
  have hΦneg : ∀ u, u < 0 → Φ u = Φ₀ u := fun u hu => by simp [hΦdef, hu]
  have hΦpos : ∀ u, 0 ≤ u → Φ u = 0 := fun u hu => by simp [hΦdef, not_lt.mpr hu]
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, Set.mem_Ioi.mpr one_pos, subset_rfl⟩
  -- the state vanishes at the wall
  have h0sq : Tendsto (fun t : ℝ => Φ₀ (-t) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine (hsq.div_atTop hL).congr' ?_
    filter_upwards [hnear] with t ht
    have hlog : 0 < Real.log (1 / t) := Real.log_pos (by rw [lt_div_iff₀ ht.1]; linarith [ht.2])
    exact mul_div_cancel_right₀ _ hlog.ne'
  have h0 : Tendsto (fun t : ℝ => Φ₀ (-t)) (𝓝[>] 0) (𝓝 0) := by
    have habs : Tendsto (fun t : ℝ => |Φ₀ (-t)|) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h0sq
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using this
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hcont : Continuous Φ := by
    rw [continuous_iff_continuousAt]
    intro u₀
    rcases lt_trichotomy u₀ 0 with h | h | h
    · have hev : Φ₀ =ᶠ[𝓝 u₀] Φ := by
        filter_upwards [Iio_mem_nhds h] with u hu
        exact (hΦneg u hu).symm
      exact (hc₀.continuousAt (Iio_mem_nhds h)).congr hev
    · subst h
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hsub⟩ :=
        mem_nhdsGT_iff_exists_Ioo_subset.mp (h0.eventually (Metric.ball_mem_nhds 0 hε))
      refine ⟨δ, hδ, fun {x} hx => ?_⟩
      rw [hΦpos 0 le_rfl, Real.dist_eq, sub_zero]
      rw [Real.dist_eq, sub_zero] at hx
      rcases lt_or_ge x 0 with hx0 | hx0
      · have hm := hsub (show -x ∈ Ioo 0 δ from
          ⟨by linarith, by rw [abs_of_neg hx0] at hx; linarith⟩)
        simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, neg_neg] at hm
        rw [hΦneg x hx0]
        exact hm
      · rw [hΦpos x hx0, abs_zero]
        exact hε
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 u₀] Φ := by
        filter_upwards [Ioi_mem_nhds h] with u hu
        exact (hΦpos u (le_of_lt hu)).symm
      exact continuousAt_const.congr hev
  have hFΦ : F =ᵐ[volume] Φ := by
    filter_upwards [hF₀] with u hu
    rcases lt_or_ge u 0 with h | h
    · rw [hΦneg u h, hu]
    · rw [hΦpos u h, hFd.support u h]
  obtain ⟨C, hC, hCb⟩ :=
    (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).1 2 (by norm_num) (by norm_num)
  have hbound : ∀ u, |Φ u| ≤ C * Real.exp (2 * u) :=
    le_of_ae_le_of_continuous hcont.abs (by fun_prop)
      (by filter_upwards [hCb, hFΦ] with u h1 h2; rwa [← h2])
  refine ⟨s, hs, Φ, hcont, hFΦ, hΦpos, ⟨C, hC, hbound⟩, ?_, ?_, k₀, hk₀, fun t ht => ?_⟩
  · refine hlaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [hΦneg (-t) (neg_neg_of_pos ht)]
  · refine hsq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [hΦneg (-t) (neg_neg_of_pos ht)]
  · rw [hΦneg (-t) (neg_neg_of_pos ht.1)]
    exact hsign t ht

/-! ### The archimedean part of the wall -/

/-- The regular part `ρ(t) = κ(t) + 1/(2t)` of the collar kernel. -/
def collarRemainder (t : ℝ) : ℝ := collarKernel t + 1 / (2 * t)

theorem measurable_collarRemainder : Measurable collarRemainder :=
  measurable_collarKernel.add (measurable_const.div (measurable_const.mul measurable_id))

theorem continuousOn_collarRemainder : ContinuousOn collarRemainder (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hden : Real.exp (2 * t) - 1 ≠ 0 := by
    have := Real.add_one_lt_exp (show 2 * t ≠ 0 by positivity)
    linarith
  have h1 : ContinuousAt (fun t : ℝ => Real.exp (t / 2)) t := by fun_prop
  have h2 : ContinuousAt (fun t : ℝ => Real.exp (-t / 2)) t := by fun_prop
  have h3 : ContinuousAt (fun t : ℝ => Real.exp (2 * t) - 1) t := by fun_prop
  have h4 : ContinuousAt (fun t : ℝ => 2 * t) t := by fun_prop
  exact ((h1.sub (h2.div h3 hden)).add
    (continuousAt_const.div h4 (mul_ne_zero two_ne_zero ht0.ne'))).continuousWithinAt

/-- `κ * F + W/2 = ρ * F` beyond the wall. -/
theorem collarWave_add_half_wallPotential_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {x : ℝ} (hx : 0 < x) :
    collarWave F x + 1 / 2 * wallPotential F x = ∫ u, F u * collarRemainder (x - u) := by
  have hI1 : Integrable fun u => F u / (x - u) := by
    refine (hF.integrable.abs.div_const x).mono'
      (hF.meas.div (measurable_const.sub measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu, zero_div, norm_zero, abs_zero, zero_div]
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < x - u)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hx (by linarith)
  have hI2 : Integrable fun u => F u * collarRemainder (x - u) := by
    refine ((integrable_abs_mul_exp_of_domain hF (c := -(1 / 2)) (by norm_num)).const_mul
      (3 * Real.exp (x / 2))).mono'
      (hF.meas.mul (measurable_collarRemainder.comp
        (measurable_const.sub measurable_id))).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu, zero_mul, norm_zero, abs_zero, zero_mul, mul_zero]
    · have hb := abs_collarKernel_add_inv_le (show 0 < x - u by linarith)
      rw [Real.norm_eq_abs, abs_mul]
      calc |F u| * |collarRemainder (x - u)| ≤ |F u| * (3 * Real.exp ((x - u) / 2)) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = 3 * Real.exp (x / 2) * (|F u| * Real.exp (-(1 / 2) * u)) := by
            rw [show (x - u) / 2 = x / 2 + -(1 / 2) * u by ring, Real.exp_add]; ring
  have hκ : collarWave F x = (∫ u, F u * collarRemainder (x - u)) - 1 / 2 * ∫ u, F u / (x - u) := by
    rw [← integral_const_mul, ← integral_sub hI2 (hI1.const_mul _), collarWave]
    congr 1; ext u
    simp only [collarRemainder, mul_inv, div_eq_mul_inv]
    ring
  rw [hκ, wallPotential_eq_integral hF.support]
  ring

/-- **The archimedean part of the wall converges.** `κ * F(x) + W(x)/2 → ∫ F(u) ρ(−u) du`. -/
theorem tendsto_collarWave_add_half_wallPotential {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun x => collarWave F x + 1 / 2 * wallPotential F x) (𝓝[>] 0)
      (𝓝 (∫ u, F u * collarRemainder (-u))) := by
  have hm : Integrable fun u => |F u| * Real.exp (-(1 / 2) * u) :=
    integrable_abs_mul_exp_of_domain hF (by norm_num)
  have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 1 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, Set.mem_Ioi.mpr one_pos, subset_rfl⟩
  refine (tendsto_integral_filter_of_dominated_convergence
    (F := fun x u => F u * collarRemainder (x - u)) (f := fun u => F u * collarRemainder (-u))
    (fun u => 3 * Real.exp (1 / 2) * (|F u| * Real.exp (-(1 / 2) * u)))
    (Eventually.of_forall fun x => (hF.meas.mul (measurable_collarRemainder.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_ (hm.const_mul _)
    (ae_of_all _ fun u => ?_)).congr' ?_
  · filter_upwards [hnear] with x hx
    refine ae_of_all _ fun u => ?_
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu, zero_mul, norm_zero, abs_zero, zero_mul, mul_zero]
    · have hb := abs_collarKernel_add_inv_le (show 0 < x - u by linarith [hx.1])
      rw [Real.norm_eq_abs, abs_mul]
      calc |F u| * |collarRemainder (x - u)| ≤ |F u| * (3 * Real.exp ((x - u) / 2)) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ ≤ |F u| * (3 * (Real.exp (1 / 2) * Real.exp (-(1 / 2) * u))) := by
            gcongr
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith [hx.2])
        _ = 3 * Real.exp (1 / 2) * (|F u| * Real.exp (-(1 / 2) * u)) := by ring
  · rcases le_or_gt 0 u with hu | hu
    · simp only [hF.support u hu, zero_mul]
      exact tendsto_const_nhds
    · have hc : ContinuousAt collarRemainder (-u) :=
        continuousOn_collarRemainder.continuousAt (Ioi_mem_nhds (by linarith))
      have hsub : Tendsto (fun x : ℝ => x - u) (𝓝[>] 0) (𝓝 (-u)) := by
        have h := (continuous_sub_right u).tendsto (0 : ℝ)
        rw [zero_sub] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact (hc.tendsto.comp hsub).const_mul (F u)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (collarWave_add_half_wallPotential_eq hF hx).symm

/-! ### The prime wave at the wall -/

private theorem primeAtom_eq_vonMangoldtAtom (n : ℕ) : primeAtom n = vonMangoldtAtom n := by
  unfold primeAtom vonMangoldtAtom; rfl

/-- **The prime wave of a continuous profile is continuous up to the wall.** With
`|Φ(u)| ≤ C e^{2u}` the series `Σ_n Λ(n) n^{−1/2} Φ(x − log n)` converges uniformly on `x ≤ 1`. -/
theorem continuousOn_primeWave {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {C : ℝ}
    (hC : ∀ u, |Φ u| ≤ C * Real.exp (2 * u)) :
    ContinuousOn (fun x => ∑' n : ℕ, primeAtom n * Φ (x - Real.log n)) (Iic 1) := by
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0)
    rwa [mul_zero, Real.exp_zero, mul_one] at this
  refine continuousOn_tsum (u := fun n => vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) *
      (C * Real.exp 2))
    (fun n => (continuous_const.mul (hΦ.comp (continuous_id.sub continuous_const))).continuousOn)
    (summable_vonMangoldtAtom_mul_exp_neg_one_log.mul_right _) (fun n x hx => ?_)
  have hl := Real.log_natCast_nonneg n
  have hx1 : x ≤ 1 := hx
  rw [Real.norm_eq_abs, abs_mul, primeAtom_eq_vonMangoldtAtom,
    abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  have he : C * Real.exp (2 * (x - Real.log n)) ≤ C * Real.exp 2 * Real.exp (-(1 * Real.log n)) := by
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC0
  calc vonMangoldtAtom n * |Φ (x - Real.log n)| ≤
        vonMangoldtAtom n * (C * Real.exp 2 * Real.exp (-(1 * Real.log n))) :=
        mul_le_mul_of_nonneg_left ((hC _).trans he) (vonMangoldtAtom_nonneg n)
    _ = vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) * (C * Real.exp 2) := by ring

/-! ### The bounded order of the wall -/

/-- The bounded order of the wall for a given continuous representative `Φ` with
`|Φ(u)| ≤ C e^{2u}`: essentially as `x → 0⁺`,
`a F⁺(x) + W(x)/2 → ∫ F(u) ρ(−u) du − Σ_n Λ(n) n^{−1/2} Φ(−log n)`. -/
theorem criticalState_bounded_order_of_rep {W₀ : ℝ} (hW : 0 < W₀)
    {F : ℝ → ℝ} (hFd : CriticalHalfLineEnergyDomain F) {Φ : ℝ → ℝ} (hcont : Continuous Φ)
    (hFΦ : F =ᵐ[volume] Φ) {C : ℝ} (hbound : ∀ u, |Φ u| ≤ C * Real.exp (2 * u))
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
      ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hFd x +
          ((1 / 2 * wallPotential F x : ℝ) : ℂ) -
          (((∫ u, F u * collarRemainder (-u)) -
            ∑' n : ℕ, primeAtom n * Φ (-Real.log n) : ℝ) : ℂ)‖ < ε := by
  have h1 := tendsto_collarWave_add_half_wallPotential hFd
  have h2 : Tendsto (fun x => ∑' n : ℕ, primeAtom n * Φ (x - Real.log n)) (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, primeAtom n * Φ (-Real.log n))) := by
    have := ((continuousOn_primeWave hcont hbound).continuousAt
      (Iic_mem_nhds one_pos)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [zero_sub] using this
  have h3 := h1.sub h2
  obtain ⟨δ, hδ, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (h3.eventually (Metric.ball_mem_nhds _ hε))
  refine ⟨δ, hδ, ?_⟩
  have hcollar := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) δ ⊆ Ioi 0) (beyondWallProfile_collarForm hW hFd)
  have hwave : ∀ᵐ x ∂volume, ∀ n : ℕ, F (x - Real.log n) = Φ (x - Real.log n) :=
    ae_all_iff.mpr fun n =>
      (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae hFΦ
  filter_upwards [hcollar, ae_restrict_of_ae hwave, ae_restrict_mem measurableSet_Ioo]
    with x hx hxw hxI
  have hm := hsub hxI
  simp only [Set.mem_setOf_eq, Real.dist_eq] at hm
  have hP : (∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) =
      ((∑' n : ℕ, primeAtom n * Φ (x - Real.log n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => by rw [hxw n, Complex.ofReal_mul]
  rw [hx, hP, show ∀ a b c d e : ℝ, ((a : ℂ) - (b : ℂ) + ((c : ℝ) : ℂ) - (((d - e : ℝ)) : ℂ)) =
      (((a + c - b) - (d - e) : ℝ) : ℂ) from fun a b c d e => by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  convert hm using 2

/-- **The prime wave at the wall is the bounded order of the wall law.** For the continuous
representative `Φ` of the critical state, essentially as `x → 0⁺`,
`a F⁺(x) + W(x)/2 → ∫ F(u) ρ(−u) du − Σ_n Λ(n) n^{−1/2} Φ(−log n)`. -/
theorem criticalState_bounded_order_at_wall {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧ (∀ u, 0 ≤ u → Φ u = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
        ‖(criticalAliasCoefficient W₀ : ℂ) *
            beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x +
          ((1 / 2 * wallPotential F x : ℝ) : ℂ) -
          (((∫ u, F u * collarRemainder (-u)) -
            ∑' n : ℕ, primeAtom n * Φ (-Real.log n) : ℝ) : ℂ)‖ < ε := by
  obtain ⟨-, -, Φ, hcont, hFΦ, hΦpos, ⟨C, -, hbound⟩, -⟩ :=
    criticalState_exists_continuous_representative hW hthreshold hF
  exact ⟨Φ, hcont, hFΦ, hΦpos, fun ε hε =>
    criticalState_bounded_order_of_rep hW _ hcont hFΦ hbound hε⟩

/-! ### The logarithmic moment form -/

/-- The kernel comparing the Stieltjes potential with the logarithmic moment after the scaling
`v = xw`: `k(w) = 1/(1 + w) − 1_{w>1}/w`. -/
def wallCompareKernel (w : ℝ) : ℝ := 1 / (1 + w) - (Ioi (1 : ℝ)).indicator (fun w => 1 / w) w

theorem measurable_wallCompareKernel : Measurable wallCompareKernel :=
  (measurable_const.div (measurable_const.add measurable_id)).sub
    ((measurable_const.div measurable_id).indicator measurableSet_Ioi)

theorem integrableOn_wallCompareKernel : IntegrableOn wallCompareKernel (Ioi 0) := by
  have h1 : IntegrableOn wallCompareKernel (Ioc 0 1) := by
    refine (integrableOn_const (C := (1 : ℝ))
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono'
      measurable_wallCompareKernel.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    have hw1 : w ∉ Ioi (1 : ℝ) := fun h => (not_lt.mpr hw.2) h
    have hw0 : 0 < 1 + w := by linarith [hw.1]
    rw [wallCompareKernel, Set.indicator_of_notMem hw1, sub_zero, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hw0), div_le_one hw0]
    linarith [hw.1]
  have h2 : IntegrableOn wallCompareKernel (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) one_pos).mono'
      measurable_wallCompareKernel.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw1 : (1 : ℝ) < w := hw
    have hw0 : (0 : ℝ) < w := by linarith
    have hpos : 0 < w * (1 + w) := by positivity
    have e : 1 / (1 + w) - 1 / w = -(1 / (w * (1 + w))) := by
      field_simp
      ring
    rw [wallCompareKernel, Set.indicator_of_mem hw, Real.norm_eq_abs, e, abs_neg,
      abs_of_pos (one_div_pos.mpr hpos), Real.rpow_neg hw0.le, Real.rpow_two, one_div]
    exact inv_anti₀ (pow_pos hw0 2) (by nlinarith)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

/-- After the scaling `v = xw`, `W(x) − L(x) = ∫_{w>0} G(−xw) k(w) dw`. -/
private theorem wallPotential_sub_wallLogMoment_eq {G : ℝ → ℝ} (hGm : Measurable G)
    (hGi : Integrable G) {x : ℝ} (hx : 0 < x) :
    wallPotential G x - wallLogMoment G x =
      ∫ w in Ioi 0, G (-(x * w)) * wallCompareKernel w := by
  have hnm : Measurable fun v => G (-v) := hGm.comp measurable_neg
  have hni : Integrable fun v => G (-v) := hGi.comp_neg
  -- the Stieltjes potential
  have hW := integral_comp_mul_left_Ioi (fun v => G (-v) / (x + v)) 0 hx
  simp only [mul_zero] at hW
  have hWi : IntegrableOn (fun w => G (-(x * w)) / (1 + w)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun v => G (-v) / (x + v)) 0 hx).mpr
      (by rw [mul_zero]; exact integrableOn_div_add hnm hni hx)
    refine IntegrableOn.congr_fun (this.const_mul x) (fun w _ => ?_) measurableSet_Ioi
    show x * (G (-(x * w)) / (x + x * w)) = G (-(x * w)) / (1 + w)
    rw [show x + x * w = x * (1 + w) by ring, mul_div_assoc', mul_div_mul_left _ _ hx.ne']
  have hWe : wallPotential G x = ∫ w in Ioi 0, G (-(x * w)) / (1 + w) := by
    have e : wallPotential G x = x * ∫ w in Ioi 0, G (-(x * w)) / (x + x * w) := by
      rw [hW, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]; rfl
    rw [e, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    show x * (G (-(x * w)) / (x + x * w)) = G (-(x * w)) / (1 + w)
    rw [show x + x * w = x * (1 + w) by ring, mul_div_assoc', mul_div_mul_left _ _ hx.ne']
  -- the logarithmic moment
  have hL := integral_comp_mul_left_Ioi (fun v => G (-v) / v) 1 hx
  simp only [mul_one] at hL
  have hLi : IntegrableOn (fun w => G (-(x * w)) / w) (Ioi 1) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun v => G (-v) / v) 1 hx).mpr
      (by rw [mul_one]; exact integrableOn_div_self hnm hni hx)
    refine IntegrableOn.congr_fun (this.const_mul x) (fun w _ => ?_) measurableSet_Ioi
    show x * (G (-(x * w)) / (x * w)) = G (-(x * w)) / w
    rw [mul_div_assoc', mul_div_mul_left _ _ hx.ne']
  have hLe : wallLogMoment G x = ∫ w in Ioi 1, G (-(x * w)) / w := by
    have e : wallLogMoment G x = x * ∫ w in Ioi 1, G (-(x * w)) / (x * w) := by
      rw [hL, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]; rfl
    rw [e, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    show x * (G (-(x * w)) / (x * w)) = G (-(x * w)) / w
    rw [mul_div_assoc', mul_div_mul_left _ _ hx.ne']
  have hLind : (∫ w in Ioi 1, G (-(x * w)) / w) =
      ∫ w in Ioi 0, (Ioi (1 : ℝ)).indicator (fun w => G (-(x * w)) / w) w := by
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hLi' : IntegrableOn ((Ioi (1 : ℝ)).indicator fun w => G (-(x * w)) / w) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr hLi).integrableOn
  rw [hWe, hLe, hLind, ← integral_sub hWi hLi']
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  simp only [wallCompareKernel, Set.indicator_apply]
  split_ifs <;> ring

/-- **The potential and the logarithmic moment agree at the wall** for a profile with a continuous
representative vanishing at the wall. -/
theorem tendsto_wallPotential_sub_wallLogMoment {F Φ : ℝ → ℝ}
    (hFi : Integrable F) (hFΦ : F =ᵐ[volume] Φ) (hΦ : Continuous Φ) (hΦ0 : Φ 0 = 0) {C : ℝ}
    (hC : ∀ u, u ≤ 0 → |Φ u| ≤ C) :
    Tendsto (fun x => wallPotential F x - wallLogMoment F x) (𝓝[>] 0) (𝓝 0) := by
  have hΦm : Measurable Φ := hΦ.measurable
  have hΦi : Integrable Φ := hFi.congr hFΦ
  have hneg : ∀ᵐ v ∂volume, F (-v) = Φ (-v) := ae_comp_neg hFΦ
  have hWF : ∀ x, wallPotential F x = wallPotential Φ x := fun x =>
    integral_congr_ae (ae_restrict_of_ae (hneg.mono fun v hv => by
      show F (-v) / (x + v) = Φ (-v) / (x + v)
      rw [hv]))
  have hLF : ∀ x, wallLogMoment F x = wallLogMoment Φ x := fun x =>
    integral_congr_ae (ae_restrict_of_ae (hneg.mono fun v hv => by
      show F (-v) / v = Φ (-v) / v
      rw [hv]))
  have hk := integrableOn_wallCompareKernel
  have hlim : Tendsto (fun x : ℝ => ∫ w in Ioi 0, Φ (-(x * w)) * wallCompareKernel w) (𝓝[>] 0)
      (𝓝 (∫ _w in Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (F := fun x w => Φ (-(x * w)) * wallCompareKernel w) (f := fun _ => 0)
      (fun w => C * |wallCompareKernel w|)
      (Eventually.of_forall fun x => ((hΦ.comp (continuous_const.mul continuous_id).neg).measurable.mul
        measurable_wallCompareKernel).aestronglyMeasurable) ?_ (hk.abs.const_mul C) ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hxw : -(x * w) ≤ 0 := by
        have : 0 < x * w := mul_pos hx hw
        linarith
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC _ hxw) (abs_nonneg _)
    · refine ae_of_all _ fun w => ?_
      have ht : Tendsto (fun x : ℝ => -(x * w)) (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun x : ℝ => -(x * w)) (𝓝 0) (𝓝 0) :=
          Continuous.tendsto' (by fun_prop) 0 0 (by simp)
        exact h.mono_left nhdsWithin_le_nhds
      have := ((hΦ.tendsto 0).comp ht).mul_const (wallCompareKernel w)
      rwa [hΦ0, zero_mul] at this
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hWF, hLF, wallPotential_sub_wallLogMoment_eq hΦm hΦi hx]

/-- **The bounded order of the wall in logarithmic-moment form.** With
`L(x) = ∫_{v>x} F(−v)/v dv`, essentially as `x → 0⁺`,
`a F⁺(x) + L(x)/2 → ∫ F(u) ρ(−u) du − Σ_n Λ(n) n^{−1/2} Φ(−log n)`: the bounded remainder of the
logarithmic law of the wall converges, and its constant carries the prime wave at the wall. -/
theorem criticalState_bounded_order_at_wall_logMoment {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧ (∀ u, 0 ≤ u → Φ u = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
        ‖(criticalAliasCoefficient W₀ : ℂ) *
            beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x +
          ((1 / 2 * wallLogMoment F x : ℝ) : ℂ) -
          (((∫ u, F u * collarRemainder (-u)) -
            ∑' n : ℕ, primeAtom n * Φ (-Real.log n) : ℝ) : ℂ)‖ < ε := by
  have hFd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨-, -, Φ, hcont, hFΦ, hΦpos, ⟨C, hC0, hbound⟩, -⟩ :=
    criticalState_exists_continuous_representative hW hthreshold hF
  refine ⟨Φ, hcont, hFΦ, hΦpos, fun ε hε => ?_⟩
  have hCw : ∀ u, u ≤ 0 → |Φ u| ≤ C := fun u hu =>
    (hbound u).trans (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by linarith)))
  have hWL := tendsto_wallPotential_sub_wallLogMoment hFd.integrable hFΦ hcont
    (hΦpos 0 le_rfl) hCw
  obtain ⟨δ₁, hδ₁, hae⟩ := criticalState_bounded_order_of_rep hW hFd hcont hFΦ hbound
    (half_pos hε)
  obtain ⟨δ₂, hδ₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hWL.eventually (Metric.ball_mem_nhds 0 hε))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  have hae' := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo_right (min_le_left δ₁ δ₂)) hae
  filter_upwards [hae', ae_restrict_mem measurableSet_Ioo] with x hx hxI
  have hm := hsub ⟨hxI.1, hxI.2.trans_le (min_le_right _ _)⟩
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hm
  have e : (criticalAliasCoefficient W₀ : ℂ) *
        beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x +
      ((1 / 2 * wallLogMoment F x : ℝ) : ℂ) -
      (((∫ u, F u * collarRemainder (-u)) - ∑' n : ℕ, primeAtom n * Φ (-Real.log n) : ℝ) : ℂ) =
      ((criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hFd x +
        ((1 / 2 * wallPotential F x : ℝ) : ℂ) -
        (((∫ u, F u * collarRemainder (-u)) - ∑' n : ℕ, primeAtom n * Φ (-Real.log n) : ℝ) : ℂ)) -
      ((1 / 2 * (wallPotential F x - wallLogMoment F x) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  calc _ ≤ ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hFd x +
          ((1 / 2 * wallPotential F x : ℝ) : ℂ) -
          (((∫ u, F u * collarRemainder (-u)) - ∑' n : ℕ, primeAtom n * Φ (-Real.log n) : ℝ) : ℂ)‖ +
        ‖((1 / 2 * (wallPotential F x - wallLogMoment F x) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add hx ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
    _ = ε := by ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
