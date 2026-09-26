import GaloisForLFunctions.HTGeometry.UnitPolygonClosure

/-!
# Greedy unit phases in `L²` of an interval

For continuous `g_n : ℝ → ℂ` and a finite index set `s`, there are unit scalars `u_n` with

  `∫₀^{2π} |Σ_{n∈s} u_n g_n|² ≤ Σ_{n∈s} ∫₀^{2π} |g_n|²`.

Adding one term: `∫|P + c g|² = ∫|P|² + |c|²∫|g|² + 2 Re(c ∫ \bar P g)`, and `c = -\overline{dir(∫ \bar P g)}`
makes the cross term `-2|∫ \bar P g| ≤ 0`.
-/

open Complex Real MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `L²` mass on `[0, 2π]`. -/
def circleMass (g : ℝ → ℂ) : ℝ := ∫ θ in (0 : ℝ)..2 * π, ‖g θ‖ ^ 2

theorem circleMass_nonneg (g : ℝ → ℂ) : 0 ≤ circleMass g :=
  intervalIntegral.integral_nonneg (by positivity) fun _ _ => sq_nonneg _

/-- The expansion of `|p + c g|²`. -/
theorem norm_add_mul_sq (p g c : ℂ) :
    ‖p + c * g‖ ^ 2 = ‖p‖ ^ 2 + ‖c‖ ^ 2 * ‖g‖ ^ 2 + 2 * (c * ((starRingEnd ℂ) p * g)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_mul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **One greedy step.** -/
theorem exists_unit_circleMass_add_le {P g : ℝ → ℂ} (hP : Continuous P) (hg : Continuous g) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ circleMass (fun θ => P θ + c * g θ) ≤ circleMass P + circleMass g := by
  set I₀ : ℂ := ∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (P θ) * g θ with hI₀
  refine ⟨-(starRingEnd ℂ) (unitDir I₀), by rw [norm_neg, RCLike.norm_conj, norm_unitDir], ?_⟩
  set c : ℂ := -(starRingEnd ℂ) (unitDir I₀) with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, norm_neg, RCLike.norm_conj, norm_unitDir]
  have hint1 : IntervalIntegrable (fun θ => ‖P θ‖ ^ 2) volume 0 (2 * π) :=
    (hP.norm.pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ => ‖c‖ ^ 2 * ‖g θ‖ ^ 2) volume 0 (2 * π) :=
    (continuous_const.mul (hg.norm.pow 2)).intervalIntegrable _ _
  have hcross_c : Continuous fun θ => c * ((starRingEnd ℂ) (P θ) * g θ) :=
    continuous_const.mul ((Complex.continuous_conj.comp hP).mul hg)
  have hint3 : IntervalIntegrable (fun θ => 2 * (c * ((starRingEnd ℂ) (P θ) * g θ)).re) volume 0 (2 * π) :=
    (continuous_const.mul (Complex.continuous_re.comp hcross_c)).intervalIntegrable _ _
  unfold circleMass
  simp_rw [norm_add_mul_sq]
  rw [intervalIntegral.integral_add (hint1.add hint2) hint3, intervalIntegral.integral_add hint1 hint2]
  have hcross : ∫ θ in (0 : ℝ)..2 * π, 2 * (c * ((starRingEnd ℂ) (P θ) * g θ)).re ≤ 0 := by
    rw [intervalIntegral.integral_const_mul]
    have hre : ∫ θ in (0 : ℝ)..2 * π, (c * ((starRingEnd ℂ) (P θ) * g θ)).re = (c * I₀).re := by
      have h := Complex.reCLM.intervalIntegral_comp_comm (hcross_c.intervalIntegrable (μ := volume) 0 (2 * π))
      simp only [Complex.reCLM_apply] at h
      rw [h, intervalIntegral.integral_const_mul]
    rw [hre]
    have hcI : c * I₀ = -((‖I₀‖ : ℝ) : ℂ) := by
      have hI : I₀ = unitDir I₀ * (‖I₀‖ : ℂ) := (unitDir_mul_norm I₀).symm
      have hu : (starRingEnd ℂ) (unitDir I₀) * unitDir I₀ = 1 := by
        rw [mul_comm, Complex.mul_conj', norm_unitDir]; simp
      rw [hc]
      linear_combination (-(starRingEnd ℂ) (unitDir I₀)) * hI + (-(‖I₀‖ : ℂ)) * hu
    rw [hcI]; simp
  rw [hc1, one_pow, intervalIntegral.integral_const_mul, one_mul]
  linarith

/-- **Greedy phases.** -/
theorem exists_unit_phases_circleMass_le (g : ℕ → ℝ → ℂ) (hg : ∀ n, Continuous (g n)) (s : Finset ℕ) :
    ∃ u : ℕ → ℂ, (∀ n, ‖u n‖ = 1) ∧
      circleMass (fun θ => ∑ n ∈ s, u n * g n θ) ≤ ∑ n ∈ s, circleMass (g n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    simp [circleMass]
  | insert m s hm ih =>
    obtain ⟨u, hu, hmass⟩ := ih
    have hP : Continuous fun θ => ∑ n ∈ s, u n * g n θ :=
      continuous_finsetSum _ fun n _ => continuous_const.mul (hg n)
    obtain ⟨c, hc, hstep⟩ := exists_unit_circleMass_add_le hP (hg m)
    refine ⟨Function.update u m c, fun n => ?_, ?_⟩
    · by_cases h : n = m
      · subst h; simp [hc]
      · simp [h, hu n]
    · rw [Finset.sum_insert hm]
      have hsum : (fun θ => ∑ n ∈ insert m s, Function.update u m c n * g n θ) =
          fun θ => (∑ n ∈ s, u n * g n θ) + c * g m θ := by
        funext θ
        rw [Finset.sum_insert hm, Function.update_self, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hm hn)]
      rw [hsum]
      linarith

end

end GaloisForLFunctions.HTGeometry
