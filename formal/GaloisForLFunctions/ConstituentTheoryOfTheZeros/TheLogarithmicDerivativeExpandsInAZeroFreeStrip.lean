import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienersLemmaOnAStrip
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The logarithmic derivative expands in a zero-free strip

Let `F(s) = Σ_q c(q) q^s` converge absolutely on the closed strip `τ₁ ≤ Re s ≤ τ₂` and have no
zero in the open strip. `F` may have zeros on both sides of the strip. Then:

* `F` is invertible in the Wiener algebra of every closed substrip
  (`StripWiener.isUnit_ofCoeff_of_zeroFree`): a character is the value of a twist
  `Σ c(q) ω(q) q^s` at a real point; the twist is a uniform limit of vertical translates of `F`,
  so a zero of the twist would plant a zero of a translate (sphere domination);
* one family `d` represents `1/F` on the whole open strip, absolutely on every closed substrip
  (`exists_inverse_expansion_of_zeroFree`);
* the same holds for the logarithmic derivative: `F'/F = Σ_q g(q) q^s`
  (`exists_logDeriv_expansion`), where `F'` has the coefficients `c(q) log q`
  (`deriv_expansion`, `WSummable.log_mul`).

For a Dirichlet polynomial this is the expansion of `D'/D` between two vertical lines that
separate its zeros; its scales are rationals of both sizes.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

variable {τ₁ τ₂ σ₁ σ₂ : ℝ} {c : PosRat → ℂ}

/-! ### Substrips -/

theorem stripWeight_mono (h1 : τ₁ ≤ σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ τ₂) (q : PosRat) :
    stripWeight σ₁ σ₂ q ≤ stripWeight τ₁ τ₂ q :=
  max_le (rpow_le_stripWeight h1 (h12.trans h2) q) (rpow_le_stripWeight (h1.trans h12) h2 q)

/-- Absolute convergence on a strip gives absolute convergence on every substrip. -/
theorem WSummable.mono (hc : WSummable τ₁ τ₂ c) (h1 : τ₁ ≤ σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ τ₂) :
    WSummable σ₁ σ₂ c :=
  Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le)
    (fun q => mul_le_mul_of_nonneg_left (stripWeight_mono h1 h12 h2 q) (norm_nonneg _)) hc

/-- Two absolutely convergent expansions that agree on a strip have the same coefficients. -/
theorem eq_of_expansion_eq (h12 : σ₁ ≤ σ₂) {c d : PosRat → ℂ} (hc : WSummable σ₁ σ₂ c)
    (hd : WSummable σ₁ σ₂ d)
    (h : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → expansion c s = expansion d s) : c = d := by
  have hz : c + (-1 : ℂ) • d = 0 := by
    refine eq_zero_of_expansion_eq_zero h12 (hc.add (hd.smul _)) fun s h₁ h₂ => ?_
    rw [expansion_add hc (hd.smul _) h₁ h₂, expansion_smul, h s h₁ h₂]
    ring
  funext q
  have hq := congrFun hz q
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hq
  linear_combination hq

/-! ### Holomorphy and the derivative -/

theorem isOpen_openStrip (τ₁ τ₂ : ℝ) : IsOpen {s : ℂ | τ₁ < s.re ∧ s.re < τ₂} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem isPreconnected_openStrip (τ₁ τ₂ : ℝ) : IsPreconnected {s : ℂ | τ₁ < s.re ∧ s.re < τ₂} :=
  ((convex_halfSpace_re_gt τ₁).inter (convex_halfSpace_re_lt τ₂)).isPreconnected

theorem differentiableAt_term (c : PosRat → ℂ) (q : PosRat) (s : ℂ) :
    DifferentiableAt ℂ (fun w => c q * q.cpow w) s :=
  (differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr q.toReal_pos.ne'))).const_mul (c q)

/-- An absolutely convergent expansion is holomorphic on the open strip. -/
theorem differentiableOn_expansion (hc : WSummable τ₁ τ₂ c) :
    DifferentiableOn ℂ (expansion c) {s : ℂ | τ₁ < s.re ∧ s.re < τ₂} :=
  Complex.differentiableOn_tsum_of_summable_norm hc
    (fun q s _ => (differentiableAt_term c q s).differentiableWithinAt) (isOpen_openStrip τ₁ τ₂)
    fun q _ hs => norm_term_le c hs.1.le hs.2.le q

/-- **The derivative of an expansion** has the coefficients `c(q) log q`. -/
theorem deriv_expansion (hc : WSummable τ₁ τ₂ c) {s : ℂ} (h₁ : τ₁ < s.re) (h₂ : s.re < τ₂) :
    deriv (expansion c) s = expansion (fun q => c q * ((q.log : ℝ) : ℂ)) s := by
  have h := Complex.hasSum_deriv_of_summable_norm hc
    (fun q s _ => (differentiableAt_term c q s).differentiableWithinAt) (isOpen_openStrip τ₁ τ₂)
    (fun q _ hs => norm_term_le c hs.1.le hs.2.le q) (show s ∈ {s : ℂ | τ₁ < s.re ∧ s.re < τ₂}
      from ⟨h₁, h₂⟩)
  have hterm : ∀ q : PosRat, deriv (fun w => c q * q.cpow w) s =
      c q * ((q.log : ℝ) : ℂ) * q.cpow s := by
    intro q
    have hne : (q.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr q.toReal_pos.ne'
    have hd := (((hasDerivAt_id s).const_cpow (Or.inl hne)).const_mul (c q)).deriv
    have hlog : Complex.log (q.toReal : ℂ) = ((q.log : ℝ) : ℂ) :=
      (Complex.ofReal_log q.toReal_pos.le).symm
    simp only [id] at hd
    rw [show (fun w => c q * q.cpow w) = fun w => c q * (q.toReal : ℂ) ^ w from rfl, hd, hlog,
      mul_one]
    unfold PosRat.cpow
    ring
  have h' : deriv (expansion c) s = ∑' q, deriv (fun w => c q * q.cpow w) s := h.tsum_eq.symm
  rw [h']
  unfold expansion
  exact tsum_congr hterm

/-- The coefficients `c(q) log q` of the derivative converge absolutely on every closed substrip
of the open strip. -/
theorem WSummable.log_mul (hc : WSummable τ₁ τ₂ c) (h1 : τ₁ < σ₁) (h12 : σ₁ ≤ σ₂)
    (h2 : σ₂ < τ₂) : WSummable σ₁ σ₂ fun q => c q * ((q.log : ℝ) : ℂ) := by
  set ε : ℝ := min (σ₁ - τ₁) (τ₂ - σ₂) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : τ₁ ≤ σ₁ - ε := by linarith [min_le_left (σ₁ - τ₁) (τ₂ - σ₂)]
  have hε2 : σ₂ + ε ≤ τ₂ := by linarith [min_le_right (σ₁ - τ₁) (τ₂ - σ₂)]
  have hkey : ∀ q : PosRat, |q.log| * stripWeight σ₁ σ₂ q ≤ ε⁻¹ * stripWeight τ₁ τ₂ q := by
    intro q
    have hx := q.toReal_pos
    rcases le_total 1 q.toReal with hq | hq
    · -- `q ≥ 1`: `log q ≤ q^ε/ε` and the weight is `q^σ₂`
      have hlog0 : 0 ≤ q.log := Real.log_nonneg hq
      have hlog : q.log ≤ q.toReal ^ ε / ε := Real.log_le_rpow_div hx.le hεpos
      have hw : stripWeight σ₁ σ₂ q ≤ q.toReal ^ σ₂ :=
        max_le (Real.rpow_le_rpow_of_exponent_le hq h12) le_rfl
      have hτ : q.toReal ^ (σ₂ + ε) ≤ stripWeight τ₁ τ₂ q :=
        (Real.rpow_le_rpow_of_exponent_le hq hε2).trans (le_max_right _ _)
      rw [abs_of_nonneg hlog0]
      calc q.log * stripWeight σ₁ σ₂ q ≤ q.toReal ^ ε / ε * q.toReal ^ σ₂ :=
            mul_le_mul hlog hw (stripWeight_pos σ₁ σ₂ q).le
              (div_nonneg (Real.rpow_nonneg hx.le _) hεpos.le)
        _ = ε⁻¹ * q.toReal ^ (σ₂ + ε) := by
            rw [Real.rpow_add hx]
            ring
        _ ≤ ε⁻¹ * stripWeight τ₁ τ₂ q := mul_le_mul_of_nonneg_left hτ (inv_pos.mpr hεpos).le
    · -- `q ≤ 1`: `−log q ≤ q^{−ε}/ε` and the weight is `q^σ₁`
      have hlog0 : q.log ≤ 0 := Real.log_nonpos hx.le hq
      have hinv : 0 ≤ (q.toReal)⁻¹ := (inv_pos.mpr hx).le
      have hlog : -q.log ≤ q.toReal ^ (-ε) / ε := by
        have h := Real.log_le_rpow_div hinv hεpos
        rwa [Real.log_inv, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at h
      have hw : stripWeight σ₁ σ₂ q ≤ q.toReal ^ σ₁ :=
        max_le le_rfl (Real.rpow_le_rpow_of_exponent_ge hx hq h12)
      have hτ : q.toReal ^ (σ₁ - ε) ≤ stripWeight τ₁ τ₂ q :=
        (Real.rpow_le_rpow_of_exponent_ge hx hq hε1).trans (le_max_left _ _)
      rw [abs_of_nonpos hlog0]
      calc -q.log * stripWeight σ₁ σ₂ q ≤ q.toReal ^ (-ε) / ε * q.toReal ^ σ₁ :=
            mul_le_mul hlog hw (stripWeight_pos σ₁ σ₂ q).le
              (div_nonneg (Real.rpow_nonneg hx.le _) hεpos.le)
        _ = ε⁻¹ * q.toReal ^ (σ₁ - ε) := by
            rw [sub_eq_add_neg, Real.rpow_add hx]
            ring
        _ ≤ ε⁻¹ * stripWeight τ₁ τ₂ q := mul_le_mul_of_nonneg_left hτ (inv_pos.mpr hεpos).le
  refine Summable.of_nonneg_of_le
    (fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le) (fun q => ?_)
    (hc.mul_left ε⁻¹)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  calc ‖c q‖ * (|q.log| * stripWeight σ₁ σ₂ q) ≤ ‖c q‖ * (ε⁻¹ * stripWeight τ₁ τ₂ q) :=
        mul_le_mul_of_nonneg_left (hkey q) (norm_nonneg _)
    _ = ε⁻¹ * (‖c q‖ * stripWeight τ₁ τ₂ q) := by ring

/-! ### A zero-free expansion is invertible on closed substrips -/

/-- **A zero-free expansion is a unit on every closed substrip.** If `Σ c(q) q^s` converges
absolutely on `τ₁ ≤ Re s ≤ τ₂` and has no zero in the open strip, it is invertible in
`𝒲[σ₁, σ₂]` for `τ₁ < σ₁ ≤ σ₂ < τ₂`. -/
theorem StripWiener.isUnit_ofCoeff_of_zeroFree [hσ : Fact (σ₁ ≤ σ₂)] (h1 : τ₁ < σ₁)
    (h2 : σ₂ < τ₂) (hc : WSummable τ₁ τ₂ c)
    (hzf : ∀ s : ℂ, τ₁ < s.re → s.re < τ₂ → expansion c s ≠ 0) :
    IsUnit (StripWiener.ofCoeff c (hc.mono h1.le hσ.out h2.le) : StripWiener σ₁ σ₂) := by
  by_contra hunit
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hunit
  obtain ⟨σ, ω, hσ1, hσ2, hω1, hωm, hval⟩ := StripWiener.exists_apply_eq_expansion_twist φ
  have hd : WSummable τ₁ τ₂ fun q => c q * ω q := hc.twist hω1
  -- the twist vanishes at the real point `σ` of the open strip
  have hzero : expansion (fun q => c q * ω q) (σ : ℂ) = 0 := by
    have h := hval (StripWiener.ofCoeff c (hc.mono h1.le hσ.out h2.le))
    rw [StripWiener.coeff_ofCoeff, hφ] at h
    exact h.symm
  set U : Set ℂ := {s : ℂ | τ₁ < s.re ∧ s.re < τ₂} with hU
  have hσU : (σ : ℂ) ∈ U := by
    show τ₁ < ((σ : ℂ)).re ∧ ((σ : ℂ)).re < τ₂
    rw [Complex.ofReal_re]
    exact ⟨by linarith, by linarith⟩
  have hdd := differentiableOn_expansion hd
  have hdan : AnalyticOnNhd ℂ (expansion fun q => c q * ω q) U :=
    hdd.analyticOnNhd (isOpen_openStrip τ₁ τ₂)
  rcases (hdan _ hσU).eventually_eq_zero_or_eventually_ne_zero with hz | hne
  · -- the twist vanishes identically: all coefficients vanish
    have hall := hdan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_openStrip τ₁ τ₂) hσU hz
    have hd0 : (fun q => c q * ω q) = 0 :=
      eq_zero_of_expansion_eq_zero hσ.out (hd.mono h1.le hσ.out h2.le) fun s hs₁ hs₂ =>
        hall (show s ∈ U from ⟨by linarith, by linarith⟩)
    have hc0 : c = 0 := funext fun q => by
      have hq := congrFun hd0 q
      rcases mul_eq_zero.mp hq with h0 | h0
      · exact h0
      · have := hω1 q
        rw [h0, norm_zero] at this
        exact absurd this zero_ne_one
    exact hzf (σ : ℂ) hσU.1 hσU.2 (by rw [hc0, expansion_zero])
  · -- an isolated zero of the twist: a sphere around it free of zeros, inside the strip
    obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp hne
    set r : ℝ := min (r₀ / 2) (min (σ - τ₁) (τ₂ - σ) / 2) with hr
    have hrpos : 0 < r := lt_min (by positivity) (by
      have : 0 < min (σ - τ₁) (τ₂ - σ) := lt_min (by linarith) (by linarith)
      positivity)
    have hr1 : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hr2 : r < σ - τ₁ := by
      have h := min_le_right (r₀ / 2) (min (σ - τ₁) (τ₂ - σ) / 2)
      have h' := min_le_left (σ - τ₁) (τ₂ - σ)
      have : 0 < σ - τ₁ := by linarith
      linarith
    have hr3 : r < τ₂ - σ := by
      have h := min_le_right (r₀ / 2) (min (σ - τ₁) (τ₂ - σ) / 2)
      have h' := min_le_right (σ - τ₁) (τ₂ - σ)
      have : 0 < τ₂ - σ := by linarith
      linarith
    have hsub : Metric.closedBall (σ : ℂ) r ⊆ U := by
      intro z hz
      have hre := abs_le.mp ((Complex.abs_re_le_norm (z - σ)).trans
        (mem_closedBall_iff_norm.mp hz))
      rw [Complex.sub_re, Complex.ofReal_re] at hre
      exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
    have hsphere : ∀ z ∈ Metric.sphere (σ : ℂ) r, expansion (fun q => c q * ω q) z ≠ 0 := by
      intro z hz
      refine hball ⟨?_, ?_⟩
      · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
        exact hr1
      · intro hzσ
        rw [Set.mem_singleton_iff.mp hzσ, Metric.mem_sphere, dist_self] at hz
        exact hrpos.ne hz
    -- the minimum of the twist on the sphere
    have hcont : ContinuousOn (fun z => ‖expansion (fun q => c q * ω q) z‖)
        (Metric.sphere (σ : ℂ) r) :=
      (hdd.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub)).norm
    obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere (σ : ℂ) r).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hrpos.le) hcont
    have hμ : 0 < ‖expansion (fun q => c q * ω q) w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
    -- a translate of the expansion within a third of the minimum of the twist
    obtain ⟨t, ht⟩ := exists_height_expansion_approx hc hω1 hωm (div_pos hμ (by norm_num :
      (0 : ℝ) < 3))
    have hshift : DifferentiableOn ℂ (fun z => expansion c (z + (t : ℂ) * Complex.I)) U := by
      refine (differentiableOn_expansion hc).comp
        (Differentiable.differentiableOn (by fun_prop)) fun z hz => ?_
      show τ₁ < (z + (t : ℂ) * Complex.I).re ∧ (z + (t : ℂ) * Complex.I).re < τ₂
      have : (z + (t : ℂ) * Complex.I).re = z.re := by simp
      rw [this]
      exact hz
    obtain ⟨z, hz, hz0⟩ := HTGeometry.exists_zero_of_sphere_domination
      (g := fun z => expansion c (z + (t : ℂ) * Complex.I) - expansion (fun q => c q * ω q) z)
      (h := expansion fun q => c q * ω q) hrpos
      ((hshift.sub hdd).diffContOnCl_ball hsub) (hdd.diffContOnCl_ball hsub) hzero
      (by
        show expansion c ((σ : ℂ) + (t : ℂ) * Complex.I) - expansion (fun q => c q * ω q) σ ≠ 0
        rw [hzero, sub_zero]
        refine hzf _ ?_ ?_
        · have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
          rw [this]
          linarith
        · have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
          rw [this]
          linarith)
      (fun z hz => by
        have hzU := hsub (Metric.sphere_subset_closedBall hz)
        have h3 := ht z hzU.1.le hzU.2.le
        have h4 := isMinOn_iff.mp hmin z hz
        show 3 * ‖expansion c (z + (t : ℂ) * Complex.I) - expansion (fun q => c q * ω q) z‖ ≤
          ‖expansion (fun q => c q * ω q) z‖
        linarith)
    have hzU := hsub hz
    have hz0' : expansion c (z + (t : ℂ) * Complex.I) = 0 := by
      have h : expansion c (z + (t : ℂ) * Complex.I) - expansion (fun q => c q * ω q) z +
          expansion (fun q => c q * ω q) z = 0 := hz0
      rwa [sub_add_cancel] at h
    have hre : (z + (t : ℂ) * Complex.I).re = z.re := by simp
    exact hzf _ (by rw [hre]; exact hzU.1) (by rw [hre]; exact hzU.2) hz0'

/-- The inverse of a zero-free expansion on one closed substrip. -/
theorem exists_inverse_expansion_on_substrip (h1 : τ₁ < σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ < τ₂)
    (hc : WSummable τ₁ τ₂ c) (hzf : ∀ s : ℂ, τ₁ < s.re → s.re < τ₂ → expansion c s ≠ 0) :
    ∃ d : PosRat → ℂ, WSummable σ₁ σ₂ d ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → expansion c s * expansion d s = 1 := by
  haveI : Fact (σ₁ ≤ σ₂) := ⟨h12⟩
  obtain ⟨g, hg⟩ := (StripWiener.isUnit_ofCoeff_of_zeroFree h1 h2 hc hzf).exists_right_inv
  refine ⟨g.coeff, g.wsummable_coeff, fun s h₁ h₂ => ?_⟩
  have hs := congrArg (fun F : StripWiener σ₁ σ₂ => F.eval ⟨s, h₁, h₂⟩) hg
  simp only [StripWiener.eval_mul, StripWiener.eval_one, StripWiener.eval_ofCoeff] at hs
  rw [← g.eval_eq ⟨s, h₁, h₂⟩]
  exact hs

/-- **The inverse of a zero-free expansion.** One family of coefficients represents `1/F` on the
whole open strip, absolutely on every closed substrip. -/
theorem exists_inverse_expansion_of_zeroFree (hτ : τ₁ < τ₂) (hc : WSummable τ₁ τ₂ c)
    (hzf : ∀ s : ℂ, τ₁ < s.re → s.re < τ₂ → expansion c s ≠ 0) :
    ∃ d : PosRat → ℂ, (∀ σ₁ σ₂ : ℝ, τ₁ < σ₁ → σ₁ ≤ σ₂ → σ₂ < τ₂ → WSummable σ₁ σ₂ d) ∧
      ∀ s : ℂ, τ₁ < s.re → s.re < τ₂ → expansion c s * expansion d s = 1 := by
  -- the inverse on the middle line
  set σ₀ : ℝ := (τ₁ + τ₂) / 2 with hσ₀
  have h0a : τ₁ < σ₀ := by rw [hσ₀]; linarith
  have h0b : σ₀ < τ₂ := by rw [hσ₀]; linarith
  obtain ⟨d, hd, hd1⟩ := exists_inverse_expansion_on_substrip h0a le_rfl h0b hc hzf
  -- on every closed substrip containing the middle line the inverse is the same family
  have hagree : ∀ α β : ℝ, τ₁ < α → α ≤ σ₀ → σ₀ ≤ β → β < τ₂ →
      WSummable α β d ∧ ∀ s : ℂ, α ≤ s.re → s.re ≤ β → expansion c s * expansion d s = 1 := by
    intro α β hα hα0 h0β hβ
    obtain ⟨d', hd', hd1'⟩ := exists_inverse_expansion_on_substrip hα (hα0.trans h0β) hβ hc hzf
    have heq : d' = d := by
      refine eq_of_expansion_eq le_rfl (hd'.mono hα0 le_rfl h0β) hd fun s h₁ h₂ => ?_
      have hs : s.re = σ₀ := le_antisymm h₂ h₁
      have hne : expansion c s ≠ 0 := hzf s (by rw [hs]; exact h0a) (by rw [hs]; exact h0b)
      have e1 := hd1' s (by rw [hs]; exact hα0) (by rw [hs]; exact h0β)
      have e2 := hd1 s h₁ h₂
      exact mul_left_cancel₀ hne (e1.trans e2.symm)
    rw [← heq]
    exact ⟨hd', hd1'⟩
  refine ⟨d, fun σ₁ σ₂ h1 h12 h2 => ?_, fun s h₁ h₂ => ?_⟩
  · exact (hagree (min σ₁ σ₀) (max σ₂ σ₀) (lt_min h1 h0a) (min_le_right _ _)
      (le_max_right _ _) (max_lt h2 h0b)).1.mono (min_le_left _ _) h12 (le_max_left _ _)
  · exact (hagree (min s.re σ₀) (max s.re σ₀) (lt_min h₁ h0a) (min_le_right _ _)
      (le_max_right _ _) (max_lt h₂ h0b)).2 s (min_le_left _ _) (le_max_left _ _)

/-- **The logarithmic derivative expands in a zero-free strip.** If `F(s) = Σ c(q) q^s` converges
absolutely on `τ₁ ≤ Re s ≤ τ₂` and has no zero in the open strip, there is one family `g` with
`F'/F = Σ g(q) q^s` on the open strip, absolutely convergent on every closed substrip. -/
theorem exists_logDeriv_expansion (hτ : τ₁ < τ₂) (hc : WSummable τ₁ τ₂ c)
    (hzf : ∀ s : ℂ, τ₁ < s.re → s.re < τ₂ → expansion c s ≠ 0) :
    ∃ g : PosRat → ℂ, (∀ σ₁ σ₂ : ℝ, τ₁ < σ₁ → σ₁ ≤ σ₂ → σ₂ < τ₂ → WSummable σ₁ σ₂ g) ∧
      ∀ s : ℂ, τ₁ < s.re → s.re < τ₂ →
        deriv (expansion c) s / expansion c s = expansion g s := by
  obtain ⟨d, hd, hd1⟩ := exists_inverse_expansion_of_zeroFree hτ hc hzf
  refine ⟨convolve (fun q => c q * ((q.log : ℝ) : ℂ)) d, fun σ₁ σ₂ h1 h12 h2 =>
    (wsummable_convolve (hc.log_mul h1 h12 h2) (hd σ₁ σ₂ h1 h12 h2)).1, fun s h₁ h₂ => ?_⟩
  rw [expansion_convolve (hc.log_mul h₁ le_rfl h₂) (hd s.re s.re h₁ le_rfl h₂) le_rfl le_rfl,
    ← deriv_expansion hc h₁ h₂, div_eq_mul_inv]
  congr 1
  exact (eq_inv_of_mul_eq_one_right (hd1 s h₁ h₂)).symm

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
