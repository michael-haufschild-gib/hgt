import GaloisForLFunctions.RHTower.XiRealRootedPolynomialPreimage
import GaloisForLFunctions.RHTower.LaguerreInequality

/-!
# `Ξ` is not a derivative of a Laguerre–Pólya function

No Laguerre–Pólya `F` has `F^{(m)} = Ξ` for `m ≥ 1` (`not_exists_laguerrePolya_iterate_deriv_preimage_XiC`).
Together with the first-order chains this excludes every nonconstant real-rooted polynomial
operator (`not_exists_laguerrePolya_firstOrderChain_iterate_deriv_preimage_XiC_of_ne`).

Proof for `m = 1`.  On the real line a Laguerre–Pólya `F` satisfies `F′² − FF″ ≥ 0`
(`re_laguerre_nonneg_of_laguerrePolya`), so `F′/F` is nonincreasing on every zero-free interval and
`F′` vanishes at most at one point of it, unless `F′` vanishes on a whole interval.  Since `F′ = Ξ`
has two zeros beyond every height (Hardy), `F` has real zeros beyond every height, and likewise
below every depth.  Hence `∫_ℝ Ξ = lim (F(x_n) − F(y_n)) = 0`, against `∫_ℝ Ξ = 2πΦ(0) > 0`.
-/

open Complex Polynomial Filter Topology Set MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **Laguerre inequality on the real line** for the Laguerre–Pólya class. -/
theorem re_laguerre_nonneg_of_laguerrePolya {F : ℂ → ℂ}
    (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) (x : ℝ) :
    0 ≤ (deriv F x).re ^ 2 - (F x).re * (deriv (deriv F) x).re := by
  obtain ⟨p, hsp, hconv⟩ := hF
  have hd : ∀ j, Tendsto (fun n => deriv^[j] (polyEvalC (p n)) (x : ℂ)) atTop
      (𝓝 (deriv^[j] F x)) := fun j =>
    (tendstoLocallyUniformlyOn_univ.mpr (tendstoLocallyUniformly_iterate_deriv hconv
      (fun n => differentiable_polyEvalC (p n)) j)).tendsto_at (mem_univ (x : ℂ))
  have hval : ∀ n j, deriv^[j] (polyEvalC (p n)) (x : ℂ) =
      (((derivative^[j] (p n)).eval x : ℝ) : ℂ) := by
    intro n j
    rw [iterate_deriv_polyEvalC, polyEvalC_ofReal]
  have h0 := (Complex.continuous_re.tendsto _).comp (hd 0)
  have h1 := (Complex.continuous_re.tendsto _).comp (hd 1)
  have h2 := (Complex.continuous_re.tendsto _).comp (hd 2)
  have hlim := (h1.pow 2).sub (h0.mul h2)
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ,
    Function.comp_apply] at hlim
  refine ge_of_tendsto' hlim fun n => ?_
  have hL := laguerreL1_eval_nonneg (hsp n) x
  have e0 := hval n 0
  have e1 := hval n 1
  have e2 := hval n 2
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ,
    Function.comp_apply] at e0 e1 e2
  rw [e0, e1, e2, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  simpa [laguerreL1, eval_sub, eval_pow, eval_mul] using hL

/-- `Ξ` does not vanish on any open interval. -/
theorem exists_Xi_ne_zero_Ioo {a b : ℝ} (hab : a < b) : ∃ x ∈ Ioo a b, Xi x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set c : ℝ := (a + b) / 2 with hc
  have hfreq : ∃ᶠ z in 𝓝[≠] (c : ℂ), XiC z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
    set δ : ℝ := min (ε / 2) ((b - a) / 4) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδb : δ ≤ (b - a) / 4 := min_le_right _ _
    refine ⟨((c + δ : ℝ) : ℂ), hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, show c + δ - c = δ by ring, abs_of_pos hδ0]
      exact hδε
    · intro heq
      have := congrArg Complex.re heq
      simp only [Complex.ofReal_re] at this
      linarith
    · rw [XiC_ofReal, hcon (c + δ) ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩,
        Complex.ofReal_zero]
  have h0 := XiC_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ _) hfreq (mem_univ (0 : ℂ))
  exact XiC_zero_ne h0

/-- If `F ∈ LP` and `F′ = cΞ` with real `c ≠ 0`, then `F` has a real zero beyond every height. -/
theorem exists_zero_gt_of_laguerrePolya_deriv_eq {F : ℂ → ℂ}
    (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) {c : ℝ} (hc : c ≠ 0)
    (hder : ∀ z, deriv F z = (c : ℂ) * XiC z) (T : ℝ) : ∃ x : ℝ, T < x ∧ F x = 0 := by
  obtain ⟨γ, γ', hT, hγγ', z1, z2⟩ := Littlewood.exists_two_Xi_zeros_gt T
  by_contra hcon
  push Not at hcon
  have hFd : Differentiable ℂ F := GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hF
  have hdd : Differentiable ℂ (deriv F) := fun z => ((hFd.analyticAt z).deriv).differentiableAt
  have hreal : ∀ x : ℝ, (F x).im = 0 := fun x => by
    simpa using Littlewood.im_iterate_deriv_eq_zero_of_laguerrePolya hF 0 x
  have hfre : ∀ x : ℝ, T < x → (F x).re ≠ 0 := fun x hx h0 =>
    hcon x hx (Complex.ext h0 (hreal x))
  set f : ℝ → ℝ := fun x => (F x).re with hf
  set f1 : ℝ → ℝ := fun x => (deriv F x).re with hf1
  set f2 : ℝ → ℝ := fun x => (deriv (deriv F) x).re with hf2
  have hd0 : ∀ x : ℝ, HasDerivAt f (f1 x) x := fun x => (hFd x).hasDerivAt.real_of_complex
  have hd1 : ∀ x : ℝ, HasDerivAt f1 (f2 x) x := fun x => (hdd x).hasDerivAt.real_of_complex
  have hf1Xi : ∀ x : ℝ, f1 x = c * Xi x := fun x => by
    simp only [hf1, hder, XiC_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- `g = f′/f` is antitone on `[γ, γ′]`
  set g : ℝ → ℝ := fun x => f1 x / f x with hg
  have hne : ∀ x ∈ Icc γ γ', f x ≠ 0 := fun x hx => hfre x (by linarith [hx.1])
  have hgd : ∀ x ∈ Icc γ γ', HasDerivAt g ((f2 x * f x - f1 x * f1 x) / f x ^ 2) x :=
    fun x hx => (hd1 x).div (hd0 x) (hne x hx)
  have hanti : AntitoneOn g (Icc γ γ') := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact HasDerivAt.continuousOn fun x hx => hgd x hx
    · intro x hx
      exact (hgd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hgd x (interior_subset hx)).deriv]
      have hL := re_laguerre_nonneg_of_laguerrePolya hF x
      refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
      simp only [hf, hf1, hf2] at hL ⊢
      nlinarith [hL]
  have hgγ : g γ = 0 := by simp [hg, hf1Xi, z1]
  have hgγ' : g γ' = 0 := by simp [hg, hf1Xi, z2]
  obtain ⟨x, hx, hxne⟩ := exists_Xi_ne_zero_Ioo hγγ'
  have hxI : x ∈ Icc γ γ' := Ioo_subset_Icc_self hx
  have hle1 : g x ≤ g γ := hanti (left_mem_Icc.mpr hγγ'.le) hxI hx.1.le
  have hle2 : g γ' ≤ g x := hanti hxI (right_mem_Icc.mpr hγγ'.le) hx.2.le
  have hgx : g x = 0 := by linarith
  have : f1 x = 0 := by
    have := hgx
    simp only [hg, div_eq_zero_iff] at this
    exact this.resolve_right (hne x hxI)
  rw [hf1Xi] at this
  exact hxne ((mul_eq_zero.mp this).resolve_left hc)

/-- **`Ξ` is not the derivative of a Laguerre–Pólya function.** -/
theorem not_exists_laguerrePolya_deriv_preimage_XiC :
    ¬ ∃ F : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya F ∧ ∀ z, deriv F z = XiC z := by
  rintro ⟨F, hF, hder⟩
  have hFd : Differentiable ℂ F := GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hF
  -- zeros beyond every height
  have hzp : ∀ T : ℝ, ∃ x : ℝ, T < x ∧ F x = 0 :=
    exists_zero_gt_of_laguerrePolya_deriv_eq hF one_ne_zero (fun z => by
      rw [hder, Complex.ofReal_one, one_mul])
  -- zeros below every depth, through `G(z) = F(−z)`
  have hG := KernelStrip.laguerrePolya_comp_neg hF
  have hGder : ∀ z, deriv (fun w => F (-w)) z = ((-1 : ℝ) : ℂ) * XiC z := by
    intro z
    rw [deriv_comp_neg, hder, XiC_even]
    push_cast; ring
  have hzn : ∀ T : ℝ, ∃ x : ℝ, x < -T ∧ F x = 0 := by
    intro T
    obtain ⟨x, hx, hx0⟩ := exists_zero_gt_of_laguerrePolya_deriv_eq hG (by norm_num) hGder T
    refine ⟨-x, by linarith, ?_⟩
    simpa using hx0
  -- the real restriction and FTC
  set f : ℝ → ℝ := fun x => (F x).re with hf
  have hd0 : ∀ x : ℝ, HasDerivAt f (Xi x) x := by
    intro x
    have h := (hFd x).hasDerivAt.real_of_complex
    have e : (deriv F x).re = Xi x := by rw [hder, XiC_ofReal, Complex.ofReal_re]
    rwa [e] at h
  have hFTC : ∀ x y : ℝ, ∫ t in y..x, Xi t = f x - f y := fun x y =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd0 t)
      (Littlewood.continuous_Xi.intervalIntegrable _ _)
  choose xs hxs hxs0 using fun n : ℕ => hzp n
  choose ys hys hys0 using fun n : ℕ => hzn n
  have hxt : Tendsto xs atTop atTop :=
    tendsto_atTop_mono (fun n => (hxs n).le) tendsto_natCast_atTop_atTop
  have hyt : Tendsto ys atTop atBot :=
    tendsto_atBot_mono (fun n => (hys n).le)
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hint : Integrable Xi := by
    have h := Littlewood.integrable_exp_mul_Xi (s := 0) (by simp [Real.pi_pos])
    simpa using h
  have hlim := intervalIntegral_tendsto_integral hint hyt hxt
  have hzeroInt : ∀ n, ∫ t in ys n..xs n, Xi t = 0 := by
    intro n
    rw [hFTC, hf]
    simp only [hxs0 n, hys0 n, Complex.zero_re, sub_zero]
  simp only [hzeroInt] at hlim
  have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
  have hpos := Littlewood.integral_Xi_pos
  linarith

/-- **`Ξ` is not an iterated derivative of a Laguerre–Pólya function.** -/
theorem not_exists_laguerrePolya_iterate_deriv_preimage_XiC {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ F : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya F ∧ deriv^[m] F = XiC := by
  rintro ⟨F, hF, heq⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine not_exists_laguerrePolya_deriv_preimage_XiC
    ⟨deriv^[k] F, laguerrePolya_iterate_deriv hF k, fun z => ?_⟩
  rw [← heq, add_comm, Function.iterate_succ_apply']

theorem firstOrderChain_of_forall_eq_zero {l : List ℝ} (hl : ∀ c ∈ l, c = 0) (g : ℂ → ℂ) :
    KernelStrip.firstOrderChain l g = g := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c = 0 := hl c List.mem_cons_self
    have ih' := ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')
    funext z
    simp only [KernelStrip.firstOrderChain, ih', hc, Complex.ofReal_zero, zero_mul, sub_zero]

/-- **LP-maximality of `Ξ` for every nonconstant real-rooted polynomial operator.**  For a list of
real numbers `c_i` and `m ≥ 0`, unless all `c_i` vanish and `m = 0`, no Laguerre–Pólya `f`
satisfies `(1 − c₁D)⋯(1 − c_nD) D^m f = Ξ`. -/
theorem not_exists_laguerrePolya_firstOrderChain_iterate_deriv_preimage_XiC_of_ne {l : List ℝ}
    {m : ℕ} (hnc : (∃ c ∈ l, c ≠ 0) ∨ 1 ≤ m) :
    ¬ ∃ f : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya f ∧
      KernelStrip.firstOrderChain l (deriv^[m] f) = XiC := by
  by_cases hl : ∃ c ∈ l, c ≠ 0
  · exact not_exists_laguerrePolya_firstOrderChain_iterate_deriv_preimage_XiC hl m
  · push Not at hl
    have hm : 1 ≤ m := hnc.resolve_left (by push Not; exact hl)
    rintro ⟨f, hf, heq⟩
    rw [firstOrderChain_of_forall_eq_zero hl] at heq
    exact not_exists_laguerrePolya_iterate_deriv_preimage_XiC hm ⟨f, hf, heq⟩

end RHTower
