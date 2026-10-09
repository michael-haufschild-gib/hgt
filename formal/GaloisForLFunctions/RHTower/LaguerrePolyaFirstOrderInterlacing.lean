import GaloisForLFunctions.RHTower.LaguerreShiftInterlacing
import GaloisForLFunctions.RHTower.XiLaguerrePolyaFirstOrderPreimage
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus

/-!
# Interlacing for first-order Laguerre–Pólya images of entire functions

Let `ψ` be in the Laguerre–Pólya class and `c` real, and put `F = ψ − c ψ′`. If `F` is not
identically zero and vanishes at two real points `γ < γ′`, then `ψ` vanishes somewhere in
`[γ, γ′]` (`exists_zero_Icc_of_laguerrePolya_sub_smul_deriv`).

Proof: approximate `ψ` by real-rooted polynomials `p_n`. Hurwitz gives zeros of
`p_n − c p_n′` near `γ` and `γ′`, real because these polynomials are real-rooted. The polynomial
interlacing theorem `exists_root_Icc_of_sub_C_mul_derivative` then puts a zero of `p_n` between
them. If `ψ` had no zero on `[γ, γ′]`, it would have none on a slightly larger compact interval, and
neither would `p_n` for large `n`, by uniform convergence.
-/

open Polynomial Metric Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem polyEvalC_ofReal (p : ℝ[X]) (x : ℝ) : polyEvalC p (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  have h := aeval_algebraMap_apply ℂ x p
  rw [Complex.coe_algebraMap, aeval_def, eval₂_eq_eval_map] at h
  rw [polyEvalC_eq_eval_map, h, Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval]

/-- A complex zero of a real-rooted real polynomial is real. -/
theorem exists_real_of_polyEvalC_eq_zero {q : ℝ[X]} (hq : q.Splits) (hq0 : q ≠ 0) {w : ℂ}
    (hw : polyEvalC q w = 0) : ∃ x : ℝ, w = x ∧ q.eval x = 0 := by
  have hmem : w ∈ (q.map Complex.ofRealHom).roots := by
    rw [mem_roots_map hq0, ← eval_map]
    rw [polyEvalC_eq_eval_map] at hw
    exact hw
  rw [Splits.roots_map hq] at hmem
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hmem
  exact ⟨x, rfl, (mem_roots hq0).mp hx⟩

/-- **Interlacing for entire Laguerre–Pólya functions.** -/
theorem exists_zero_Icc_of_laguerrePolya_sub_smul_deriv {ψ : ℂ → ℂ}
    (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ) (c : ℝ)
    (hnz : ∃ z₀, ψ z₀ - (c : ℂ) * deriv ψ z₀ ≠ 0) {γ γ' : ℝ} (hγ : γ < γ')
    (h1 : ψ γ - (c : ℂ) * deriv ψ γ = 0) (h2 : ψ γ' - (c : ℂ) * deriv ψ γ' = 0) :
    ∃ x ∈ Icc γ γ', ψ x = 0 := by
  by_contra hnot
  push Not at hnot
  set F : ℂ → ℂ := fun z => ψ z - (c : ℂ) * deriv ψ z with hF
  obtain ⟨p, hsplit, hconv⟩ := hψ
  have hψd : Differentiable ℂ ψ :=
    LaguerrePolya.differentiable ⟨p, hsplit, hconv⟩
  have hFd : Differentiable ℂ F := by
    have hdd : Differentiable ℂ (deriv ψ) := by
      intro z
      exact ((hψd.analyticAt z).deriv).differentiableAt
    exact hψd.sub (hdd.const_mul _)
  -- isolation of the zeros of `F`
  have hisol : ∀ a : ℂ, F a = 0 → ∃ r₀ > 0, ∀ w, w ≠ a → dist w a < r₀ → F w ≠ 0 := by
    intro a ha
    rcases (hFd.analyticAt a).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨z₀, hz₀⟩ := hnz
      have hon : AnalyticOnNhd ℂ F univ := fun z _ => hFd.analyticAt z
      have hfreq : ∃ᶠ z in 𝓝[≠] a, F z = 0 :=
        (h.filter_mono nhdsWithin_le_nhds).frequently
      have := hon.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (mem_univ a) hfreq (mem_univ z₀)
      exact hz₀ this
    · obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp h
      obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
      exact ⟨r₀, hr₀, fun w hw hd => hUsub w (hball ⟨hd, hw⟩)⟩
  obtain ⟨r₁, hr₁, hiso₁⟩ := hisol γ h1
  obtain ⟨r₂, hr₂, hiso₂⟩ := hisol γ' h2
  -- `ψ` is nonzero on a thickened interval
  have hopen : IsOpen {x : ℝ | ψ x ≠ 0} :=
    isOpen_ne_fun (hψd.continuous.comp Complex.continuous_ofReal) continuous_const
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_Icc (a := γ) (b := γ')).exists_cthickening_subset_open
    hopen (fun x hx => hnot x hx)
  have hJ : ∀ x ∈ Icc (γ - δ) (γ' + δ), ψ x ≠ 0 := by
    intro x hx
    refine hthick (mem_cthickening_of_dist_le x (max γ (min x γ')) δ _ ⟨le_max_left _ _,
      max_le hγ.le (min_le_right _ _)⟩ ?_)
    rw [Real.dist_eq, abs_le]
    rcases le_total x γ with h | h
    · rw [min_eq_left (h.trans hγ.le), max_eq_left h]
      constructor <;> linarith [hx.1]
    · rcases le_total x γ' with h' | h'
      · rw [min_eq_left h', max_eq_right h]
        constructor <;> linarith
      · rw [min_eq_right h', max_eq_right hγ.le]
        constructor <;> linarith [hx.2]
  -- a uniform lower bound for `ψ` on the thickened interval
  have hKc : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc (γ - δ) (γ' + δ)) :=
    (isCompact_Icc).image Complex.continuous_ofReal
  have hKne : ((fun x : ℝ => (x : ℂ)) '' Icc (γ - δ) (γ' + δ)).Nonempty :=
    ⟨(γ : ℂ), γ, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hKne hψd.continuous.norm.continuousOn
  obtain ⟨x₀, hx₀, rfl⟩ := hz₀
  set m := ‖ψ x₀‖ with hm
  have hmpos : 0 < m := norm_pos_iff.mpr (hJ x₀ hx₀)
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ hKc
  have hev_poly : ∀ᶠ n in atTop, ∀ x ∈ Icc (γ - δ) (γ' + δ), (p n).eval x ≠ 0 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif m hmpos] with n hn x hx
    intro h0
    have hz := hn (x : ℂ) ⟨x, hx, rfl⟩
    rw [polyEvalC_ofReal, h0, Complex.ofReal_zero, dist_zero_right] at hz
    have := hmin ⟨x, hx, rfl⟩
    simp only [mem_setOf_eq] at this
    linarith
  -- Hurwitz near `γ` and `γ'`
  set r := min (min r₁ r₂) (min δ ((γ' - γ) / 4)) / 2 with hr
  have hrpos : 0 < r := by
    have : 0 < min (min r₁ r₂) (min δ ((γ' - γ) / 4)) :=
      lt_min (lt_min hr₁ hr₂) (lt_min hδ (by linarith))
    positivity
  have hr_lt₁ : r < r₁ := by
    have := min_le_left (min r₁ r₂) (min δ ((γ' - γ) / 4))
    have := min_le_left r₁ r₂
    linarith
  have hr_lt₂ : r < r₂ := by
    have := min_le_left (min r₁ r₂) (min δ ((γ' - γ) / 4))
    have := min_le_right r₁ r₂
    linarith
  have hr_δ : r ≤ δ := by
    have := min_le_right (min r₁ r₂) (min δ ((γ' - γ) / 4))
    have := min_le_left δ ((γ' - γ) / 4)
    linarith
  have hr_gap : r < (γ' - γ) / 2 := by
    have := min_le_right (min r₁ r₂) (min δ ((γ' - γ) / 4))
    have := min_le_right δ ((γ' - γ) / 4)
    linarith
  have hconvF : TendstoLocallyUniformly (fun n => polyEvalC (p n - C c * derivative (p n))) F
      atTop := by
    have hd := tendstoLocallyUniformly_iterate_deriv hconv
      (fun m => differentiable_polyEvalC (p m)) 1
    simp only [Function.iterate_one] at hd
    have hfun : (fun n => polyEvalC (p n - C c * derivative (p n))) =
        fun n z => polyEvalC (p n) z - (c : ℂ) * deriv (polyEvalC (p n)) z := by
      funext n z
      rw [deriv_polyEvalC]
      simp [polyEvalC, map_sub, map_mul]
    rw [hfun]
    exact hconv.sub ((uniformContinuous_const_smul (c : ℂ)).comp_tendstoLocallyUniformly hd)
  have hsph : ∀ a : ℂ, ∀ ρ : ℝ, (∀ w, w ≠ a → dist w a < ρ → F w ≠ 0) → r < ρ →
      ∀ w ∈ sphere a r, F w ≠ 0 := by
    intro a ρ hiso hrρ w hw
    rw [mem_sphere] at hw
    exact hiso w (fun h => by rw [h, dist_self] at hw; linarith) (by rw [hw]; exact hrρ)
  have hev₁ := eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconvF hFd
    (Eventually.of_forall fun n => differentiable_polyEvalC _) hrpos h1
    (hsph γ r₁ hiso₁ hr_lt₁)
  have hev₂ := eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconvF hFd
    (Eventually.of_forall fun n => differentiable_polyEvalC _) hrpos h2
    (hsph γ' r₂ hiso₂ hr_lt₂)
  obtain ⟨n, hpn, ⟨w, hw, hw0⟩, ⟨w', hw', hw'0⟩⟩ := (hev_poly.and (hev₁.and hev₂)).exists
  -- the approximant is a nonzero polynomial of positive degree
  have hγJ : γ ∈ Icc (γ - δ) (γ' + δ) := ⟨by linarith, by linarith⟩
  have hp0 : p n ≠ 0 := by
    intro h; exact hpn γ hγJ (by rw [h, eval_zero])
  have hQs := splits_sub_C_mul_derivative (hsplit n) c
  have hQ0 := sub_C_mul_derivative_ne_zero hp0 c
  obtain ⟨u, rfl, hu⟩ := exists_real_of_polyEvalC_eq_zero hQs hQ0 hw0
  obtain ⟨u', rfl, hu'⟩ := exists_real_of_polyEvalC_eq_zero hQs hQ0 hw'0
  rw [mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_le] at hw hw'
  have hdeg : 1 ≤ (p n).natDegree := by
    by_contra hd
    push Not at hd
    have hc : p n = C ((p n).coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    rw [hc, derivative_C, mul_zero, sub_zero, eval_C] at hu
    have := hpn γ hγJ
    rw [hc, eval_C] at this
    exact this hu
  have huu : u < u' := by linarith [hw.2, hw'.1]
  obtain ⟨x, hx, hx0⟩ := exists_root_Icc_of_sub_C_mul_derivative (hsplit n) hdeg huu hu hu'
  exact hpn x ⟨by linarith [hx.1, hw.1], by linarith [hx.2, hw'.2]⟩ hx0

end

end RHTower
