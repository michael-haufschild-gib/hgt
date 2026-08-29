import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus

/-!
# Real-rootedness is closed under coefficientwise limits of bounded degree

A nonzero real polynomial whose coefficients are the limits of the coefficients of real-rooted real
polynomials of bounded degree is itself real-rooted.  Bounded degree makes the coefficient limit a
locally uniform limit of the associated entire functions, and the Hurwitz closed-locus transfer
keeps the zeros on the real axis.
-/

open Polynomial Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A real polynomial that splits has only real complex roots. -/
theorem im_eq_zero_of_splits {p : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0) {z : ℂ}
    (hz : (aeval z p : ℂ) = 0) : z.im = 0 := by
  classical
  have hfac := hp.eq_prod_roots
  have hval : (aeval z p : ℂ)
      = (p.leadingCoeff : ℂ) * ((p.roots.map fun a : ℝ => z - (a : ℂ)).prod) := by
    conv_lhs => rw [hfac]
    rw [map_mul, map_multiset_prod, Multiset.map_map]
    simp
  rw [hval] at hz
  have hlc : (p.leadingCoeff : ℂ) ≠ 0 := by
    simpa using Polynomial.leadingCoeff_ne_zero.2 hp0
  have hprod : (p.roots.map fun a : ℝ => z - (a : ℂ)).prod = 0 := by
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h hlc
    · exact h
  rw [Multiset.prod_eq_zero_iff] at hprod
  obtain ⟨a, ha, hazero⟩ := Multiset.mem_map.1 hprod
  have : z = (a : ℂ) := by
    have := sub_eq_zero.1 hazero
    exact this
  rw [this]
  simp

/-- A real polynomial all of whose complex roots are real splits over `ℝ`. -/
theorem splits_of_forall_complex_root_real :
    ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n →
      (∀ z : ℂ, (aeval z q : ℂ) = 0 → z.im = 0) → q.Splits := by
  intro n
  induction n with
  | zero => intro q hq _; exact Polynomial.Splits.of_natDegree_le_one (by omega)
  | succ n ih =>
      intro q hq h
      by_cases hle : q.natDegree ≤ 1
      · exact Polynomial.Splits.of_natDegree_le_one hle
      push Not at hle
      have hq0 : q ≠ 0 := by
        intro h0
        rw [h0] at hle
        simp at hle
      have hmapdeg : (q.map (algebraMap ℝ ℂ)).natDegree = q.natDegree :=
        Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective q
      have hdegpos : 0 < (q.map (algebraMap ℝ ℂ)).degree := by
        rw [Polynomial.degree_eq_natDegree
          (by
            intro h0
            rw [Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective] at h0
            exact hq0 h0)]
        exact_mod_cast by omega
      obtain ⟨z, hz⟩ := Complex.exists_root hdegpos
      have hzq : (aeval z q : ℂ) = 0 := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]
        exact hz
      have him := h z hzq
      have hza : z = ((z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hroot : q.IsRoot z.re := by
        have hstep : q.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) z.re)
            = (algebraMap ℝ ℂ) (q.eval z.re) := Polynomial.eval₂_hom _ _
        have hz2 : q.eval₂ (algebraMap ℝ ℂ) z = 0 := by
          rw [← Polynomial.aeval_def]; exact hzq
        have harg : (algebraMap ℝ ℂ) z.re = z := by
          rw [Complex.coe_algebraMap]
          exact hza.symm
        rw [harg, hz2] at hstep
        exact (algebraMap ℝ ℂ).injective (by simpa using hstep.symm)
      obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.2 hroot
      have hg0 : g ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hg
        exact hq0 hg
      have hgdeg : g.natDegree ≤ n := by
        have hdeg : q.natDegree = 1 + g.natDegree := by
          rw [hg, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hg0,
            Polynomial.natDegree_X_sub_C]
        omega
      have hgh : ∀ z : ℂ, (aeval z g : ℂ) = 0 → z.im = 0 := by
        intro w hw
        refine h w ?_
        rw [hg, map_mul, hw, mul_zero]
      rw [hg]
      exact Polynomial.Splits.mul (Polynomial.Splits.X_sub_C _) (ih g hgdeg hgh)

theorem norm_aeval_sub_le {d : ℕ} {p q : ℝ[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    {z : ℂ} {R : ℝ} (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖(aeval z p : ℂ) - (aeval z q : ℂ)‖
      ≤ ∑ j ∈ Finset.range (d + 1), |p.coeff j - q.coeff j| * R ^ d := by
  have hpe : (aeval z p : ℂ) = ∑ j ∈ Finset.range (d + 1), (p.coeff j : ℂ) * z ^ j := by
    rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (show p.natDegree < d + 1 by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Algebra.smul_def]
  have hqe : (aeval z q : ℂ) = ∑ j ∈ Finset.range (d + 1), (q.coeff j : ℂ) * z ^ j := by
    rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (show q.natDegree < d + 1 by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Algebra.smul_def]
  rw [hpe, hqe, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  have hjd : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hzj : ‖z ^ j‖ ≤ R ^ d := by
    rw [norm_pow]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hz j) ?_
    exact pow_le_pow_right₀ hR hjd
  have hsub : ((p.coeff j : ℂ) * z ^ j - (q.coeff j : ℂ) * z ^ j)
      = ((p.coeff j - q.coeff j : ℝ) : ℂ) * z ^ j := by
    push_cast
    ring
  rw [hsub, norm_mul]
  have hc : ‖((p.coeff j - q.coeff j : ℝ) : ℂ)‖ = |p.coeff j - q.coeff j| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hc]
  exact mul_le_mul_of_nonneg_left hzj (abs_nonneg _)

/-- **Real-rootedness is closed under coefficientwise limits of bounded degree.** -/
theorem splits_of_tendsto_coeff {d : ℕ} {q : ℝ[X]} {qs : ℕ → ℝ[X]}
    (hdeg : ∀ m, (qs m).natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hsplit : ∀ m, (qs m).Splits)
    (hlim : ∀ j, Tendsto (fun m => (qs m).coeff j) atTop (𝓝 (q.coeff j)))
    (hq : q ≠ 0) : q.Splits := by
  classical
  refine splits_of_forall_complex_root_real d q hqdeg fun z hz => ?_
  set F : ℂ → ℂ := fun w => (aeval w q : ℂ) with hF
  set Fn : ℕ → ℂ → ℂ := fun m w => (aeval w (qs m) : ℂ) with hFn
  have hdiff : ∀ m, Differentiable ℂ (Fn m) := by
    intro m
    have : Fn m = fun w => ((qs m).map (algebraMap ℝ ℂ)).eval w := by
      funext w
      show (aeval w (qs m) : ℂ) = _
      rw [Polynomial.aeval_def, Polynomial.eval_map]
    rw [this]
    exact Polynomial.differentiable _
  have hFdiff : Differentiable ℂ F := by
    have : F = fun w => (q.map (algebraMap ℝ ℂ)).eval w := by
      funext w
      show (aeval w q : ℂ) = _
      rw [Polynomial.aeval_def, Polynomial.eval_map]
    rw [this]
    exact Polynomial.differentiable _
  have hconv : TendstoLocallyUniformly Fn F atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨R, hR1, hRK⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ w ∈ K, ‖w‖ ≤ R := by
      obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall 0
      refine ⟨max 1 C, le_max_left _ _, fun w hw => ?_⟩
      have := hC hw
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_right _ _)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hEtend : Tendsto
        (fun m => ∑ j ∈ Finset.range (d + 1), |(qs m).coeff j - q.coeff j| * R ^ d)
        atTop (𝓝 0) := by
      have : (0 : ℝ) = ∑ j ∈ Finset.range (d + 1), |q.coeff j - q.coeff j| * R ^ d := by
        simp
      rw [this]
      refine tendsto_finsetSum _ fun j _ => ?_
      exact ((hlim j).sub_const _).abs.mul_const _
    have hEv : ∀ᶠ m in atTop,
        ∑ j ∈ Finset.range (d + 1), |(qs m).coeff j - q.coeff j| * R ^ d < ε := by
      have := hEtend.eventually (gt_mem_nhds hε)
      simpa using this
    filter_upwards [hEv] with m hm w hw
    rw [dist_eq_norm]
    calc ‖F w - Fn m w‖ = ‖(aeval w q : ℂ) - (aeval w (qs m) : ℂ)‖ := rfl
      _ ≤ ∑ j ∈ Finset.range (d + 1), |q.coeff j - (qs m).coeff j| * R ^ d :=
          norm_aeval_sub_le hqdeg (hdeg m) hR1 (hRK w hw)
      _ = ∑ j ∈ Finset.range (d + 1), |(qs m).coeff j - q.coeff j| * R ^ d := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_sub_comm]
      _ < ε := hm
  obtain ⟨a, ha⟩ : ∃ a : ℂ, F a ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmap : q.map (algebraMap ℝ ℂ) = 0 := by
      refine Polynomial.funext fun x => ?_
      have hx : (aeval x q : ℂ) = 0 := hall x
      rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hx
      simp [hx]
    rw [Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective] at hmap
    exact hq hmap
  have hqne : ∀ᶠ m in atTop, qs m ≠ 0 := by
    obtain ⟨j0, hj0⟩ : ∃ j, q.coeff j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hq (Polynomial.ext fun j => by simp [hc j])
    filter_upwards [(hlim j0).eventually_ne hj0] with m hm h0
    exact hm (by simp [h0])
  have hzeroS : ∀ᶠ m in atTop, ∀ w : ℂ, Fn m w = 0 → w ∈ {w : ℂ | w.im = 0} := by
    filter_upwards [hqne] with m hm w hw
    exact im_eq_zero_of_splits (hsplit m) hm hw
  exact zero_mem_closed_of_tendstoLocallyUniformly (S := {w : ℂ | w.im = 0}) hconv
    (hFdiff.differentiableOn.analyticOnNhd isOpen_univ)
    (Filter.Eventually.of_forall hdiff)
    (isClosed_eq Complex.continuous_im continuous_const)
    hzeroS ha hz

end

end GaloisForLFunctions.HTGeometry
