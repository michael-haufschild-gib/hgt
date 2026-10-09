import GaloisForLFunctions.RHTower.XiSliceCircleDecay
import GaloisForLFunctions.HTGeometry.GammaSuperPolynomialDecay
import GaloisForLFunctions.HTGeometry.PolynomialCriticalValues
import GaloisForLFunctions.RHTower.SuzukiCharacteristicEntireLimitNoGo
import GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion

/-!
# Nonzero critical values of actual Xi accumulate at zero

Gamma recurrence and the elementary positive-half-strip zeta bound give critical-line decay.
Arbitrarily high actual Xi zeros, compact zero isolation, and Rolle's theorem then produce
arbitrarily high real critical points of XiC with nonzero values arbitrarily close to zero.
Every real tail supplies infinitely many distinct such values. The affine change of coordinates
transfers the conclusion to Xi itself, unconditionally.

The decay proof uses no Fourier representation. This is an obstruction to finite critical-value
factorizations; it does not assert RH or surjectivity of the marked monodromy map.
-/

open Complex Filter
open scoped Topology

namespace RHTower

/-- Direct Gamma-recurrence bound on the critical line. -/
theorem norm_XiC_ofReal_le_gamma_cubic {t : ℝ} (ht : 2 ≤ t) :
    ‖XiC (t : ℂ)‖ ≤ 80 * Real.pi ^ (-(1 / 4 : ℝ)) *
      ‖((t / 2 : ℝ) : ℂ) ^ 3 * Gamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
  let s : ℂ := 1 / 2 + (t : ℂ) * I
  have ht0 : 0 ≤ t := by linarith
  have hs : 0 < s.re := by norm_num [s]
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hsn : ‖s‖ ≤ 2 * t := by
    calc
      ‖s‖ ≤ ‖(1 : ℂ) / 2‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + t := by simp [abs_of_nonneg ht0]
      _ ≤ 2 * t := by linarith
  have hsm : ‖s - 1‖ ≤ 2 * t := by
    have heq : s - 1 = -(1 / 2 : ℂ) + (t : ℂ) * I := by dsimp [s]; ring
    rw [heq]
    calc
      ‖-(1 / 2 : ℂ) + (t : ℂ) * I‖ ≤ ‖-(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + t := by simp [abs_of_nonneg ht0]
      _ ≤ 2 * t := by linarith
  have hpoly : ‖s * (s - 1) / 2‖ ≤ 2 * t ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_ofNat]
    calc
      ‖s‖ * ‖s - 1‖ / 2 ≤ (2 * t) * (2 * t) / 2 := by gcongr
      _ = 2 * t ^ 2 := by ring
  have hz : ‖riemannZeta s‖ ≤ 5 * t := by
    have h := norm_riemannZeta_le_of_re_pos (σ := 1 / 2) (t := t)
      (by norm_num) (by norm_num) (by simpa [abs_of_nonneg ht0] using ht)
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
    change ‖riemannZeta s‖ ≤ _ at h
    rw [abs_of_nonneg ht0] at h
    linarith
  have hhalf : s / 2 = (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    dsimp [s]; push_cast; ring
  have hfac := norm_xi_eq_factors hs hs1
  change ‖XiC (t : ℂ)‖ = _ at hfac
  rw [hhalf] at hfac
  have hre : s.re / 2 = (1 / 4 : ℝ) := by norm_num [s]
  rw [hre] at hfac
  calc
    ‖XiC (t : ℂ)‖ = ‖s * (s - 1) / 2‖ *
      (Real.pi ^ (-(1 / 4 : ℝ)) * ‖Gamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) *
      ‖riemannZeta s‖ := hfac
    _ ≤ (2 * t ^ 2) *
      (Real.pi ^ (-(1 / 4 : ℝ)) * ‖Gamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) *
      (5 * t) := by gcongr
    _ = _ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ t / 2 by positivity)]
      ring

/-- Critical-line decay from the Gamma integral and recurrence, without a Fourier step. -/
theorem tendsto_XiC_ofReal_atTop_via_gamma :
    Tendsto (fun t : ℝ => XiC (t : ℂ)) atTop (𝓝 0) := by
  have htop : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have hg := (GaloisForLFunctions.Gamma_vertical_tendsto_zero_mul_pow
    (σ := 1 / 4) (by norm_num) 3).comp htop
  have hb : Tendsto (fun t : ℝ => 80 * Real.pi ^ (-(1 / 4 : ℝ)) *
      ‖((t / 2 : ℝ) : ℂ) ^ 3 * Gamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖)
      atTop (𝓝 0) := by
    simpa using hg.norm.const_mul (80 * Real.pi ^ (-(1 / 4 : ℝ)))
  exact squeeze_zero_norm' (eventually_atTop.2 ⟨2, fun t ht =>
    norm_XiC_ofReal_le_gamma_cubic ht⟩) hb

/-- Arbitrarily high real critical points have nonzero values arbitrarily close to zero. -/
theorem exists_high_nonzero_small_XiC_critical_value (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, T < t ∧ deriv XiC (t : ℂ) = 0 ∧ 0 < ‖XiC (t : ℂ)‖ ∧
      ‖XiC (t : ℂ)‖ < ε := by
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖XiC (t : ℂ)‖ < ε :=
    tendsto_XiC_ofReal_atTop_via_gamma.norm.eventually_lt_const (by simpa using hε)
  obtain ⟨U, hU⟩ := eventually_atTop.1 hsmall
  obtain ⟨a, ha, ha0, hza, _⟩ :=
    DeletionMixedRefinement.exists_high_simple_critical_xi (max T U)
  obtain ⟨b, hab, _, hzb, _⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi a
  change XiC (a : ℂ) = 0 at hza
  change XiC (b : ℂ) = 0 at hzb
  obtain ⟨p, q, hap, _, hpq, hzp, hzq, hgap⟩ :=
    exists_positive_real_XiC_zero_gap_ge_of_two_zeros ha0 hab hza hzb
  obtain ⟨c, hc, hdc⟩ := exists_deriv_XiC_eq_zero_between_real_zeros hpq hzp hzq
  have hac : a < c := lt_of_le_of_lt hap hc.1
  exact ⟨c, lt_trans (lt_of_le_of_lt (le_max_left T U) ha) hac, hdc,
    norm_pos_iff.2 (hgap c hc), hU c (le_trans (le_max_right T U) (ha.trans hac).le)⟩

/-- Every real tail supplies infinitely many distinct nonzero critical values. -/
theorem infinite_XiC_nonzero_real_critical_values_above (T : ℝ) :
    Set.Infinite {w : ℂ | w ≠ 0 ∧ ∃ t : ℝ,
      T < t ∧ deriv XiC (t : ℂ) = 0 ∧ XiC (t : ℂ) = w} := by
  classical
  intro hfin
  let S : Finset ℝ := hfin.toFinset.image (fun w : ℂ => ‖w‖)
  obtain ⟨t, ht, hdt, hnt, _⟩ :=
    exists_high_nonzero_small_XiC_critical_value T (ε := 1) (by norm_num)
  have htmem : ‖XiC (t : ℂ)‖ ∈ S := by
    apply Finset.mem_image.2
    exact ⟨XiC (t : ℂ), hfin.mem_toFinset.2
      ⟨norm_pos_iff.1 hnt, t, ht, hdt, rfl⟩, rfl⟩
  have hSne : S.Nonempty := ⟨_, htmem⟩
  have hminmem : S.min' hSne ∈ S := Finset.min'_mem S hSne
  obtain ⟨w, hw, hweq⟩ := Finset.mem_image.1 hminmem
  have hpos : 0 < S.min' hSne := by
    rw [← hweq]
    exact norm_pos_iff.2 (hfin.mem_toFinset.1 hw).1
  obtain ⟨u, hu, hdu, hnu, husmall⟩ :=
    exists_high_nonzero_small_XiC_critical_value T hpos
  have humem : ‖XiC (u : ℂ)‖ ∈ S := by
    apply Finset.mem_image.2
    exact ⟨XiC (u : ℂ), hfin.mem_toFinset.2
      ⟨norm_pos_iff.1 hnu, u, hu, hdu, rfl⟩, rfl⟩
  exact (not_lt_of_ge (Finset.min'_le S _ humem)) husmall

/-- The same accumulation holds for the original Xi coordinate on its critical line. -/
theorem exists_high_nonzero_small_xi_critical_value (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ T < s.im ∧ deriv xi s = 0 ∧
      0 < ‖xi s‖ ∧ ‖xi s‖ < ε := by
  obtain ⟨t, ht, hdt, hnt, hsmall⟩ :=
    exists_high_nonzero_small_XiC_critical_value T hε
  let s : ℂ := 1 / 2 + (t : ℂ) * I
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) / 2 + z * I) I (t : ℂ) := by
    simpa [add_comm] using!
      ((hasDerivAt_id (t : ℂ)).mul_const I).const_add ((1 : ℂ) / 2)
  have hchain : deriv XiC (t : ℂ) = deriv xi s * I := by
    exact ((xi_differentiable s).hasDerivAt.comp (t : ℂ) hinner).deriv
  rw [hchain] at hdt
  refine ⟨s, by norm_num [s], by simpa [s] using ht,
    (mul_eq_zero.1 hdt).resolve_right I_ne_zero, hnt, hsmall⟩

/-- Actual Xi has infinitely many nonzero critical values; no RH hypothesis is used. -/
theorem infinite_xi_nonzero_critical_values :
    Set.Infinite {w : ℂ | w ≠ 0 ∧ ∃ s : ℂ, deriv xi s = 0 ∧ xi s = w} := by
  intro hfin
  have hsub : {w : ℂ | w ≠ 0 ∧ ∃ t : ℝ,
      (0 : ℝ) < t ∧ deriv XiC (t : ℂ) = 0 ∧ XiC (t : ℂ) = w} ⊆
      {w : ℂ | w ≠ 0 ∧ ∃ s : ℂ, deriv xi s = 0 ∧ xi s = w} := by
    rintro w ⟨hw, t, _, hdt, hval⟩
    let s : ℂ := 1 / 2 + (t : ℂ) * I
    have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) / 2 + z * I) I (t : ℂ) := by
      simpa [add_comm] using!
        ((hasDerivAt_id (t : ℂ)).mul_const I).const_add ((1 : ℂ) / 2)
    have hchain : deriv XiC (t : ℂ) = deriv xi s * I := by
      exact ((xi_differentiable s).hasDerivAt.comp (t : ℂ) hinner).deriv
    rw [hchain] at hdt
    exact ⟨hw, s, (mul_eq_zero.1 hdt).resolve_right I_ne_zero, hval⟩
  exact infinite_XiC_nonzero_real_critical_values_above 0 (hfin.subset hsub)

/-- Xi admits no polynomial inner factor with a finite-critical-value entire outer factor. -/
theorem xi_ne_comp_polynomial_of_finite_critical_values {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hcrit : (F '' {z | deriv F z = 0}).Finite)
    (P : Polynomial ℂ) : xi ≠ fun z => F (P.eval z) := by
  intro heq
  have hfinite := GaloisForLFunctions.HTGeometry.finite_critical_values_comp_polynomial
    hF hcrit P
  rw [← heq] at hfinite
  apply infinite_xi_nonzero_critical_values (hfinite.subset ?_)
  rintro w ⟨_, s, hs, hval⟩
  exact ⟨s, hs, hval⟩

end RHTower
