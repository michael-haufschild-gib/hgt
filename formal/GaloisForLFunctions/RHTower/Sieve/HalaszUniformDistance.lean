import GaloisForLFunctions.RHTower.Sieve.HalaszPerronAssembly

/-!
# The damped estimate under a uniform distance hypothesis

A lower bound for the distance that is *uniform over the frequency range* — which is what
`min_{|t| ≤ T} D(f, n^{it}; z)²` is, and what the corpus's uniform frequency estimate supplies — makes
the damped bound hold at every frequency of the range.  No frequency is exceptional, so the integral
over `[-T, T]` is bounded by the damped size alone:

`2π ‖∑ₙ f(n)w(n)‖ ≤ damped · ((N+H)^σ/σ) · 2T + trivial · C · (π − 2 arctan T)`.

This is strictly sharper than the windowed form: the window term, which cost a factor `T·δ`, disappears
entirely.  It is the correct shape of the pointwise route.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

section

variable {f : ℕ → ℂ}

/-- **The damped bound holds at every frequency of the range.** -/
theorem norm_tsum_twistedSummand_le_damped_of_uniform
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) {T : ℝ}
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    {t : ℝ} (ht : |t| ≤ T) :
    ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖ ≤
      (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) := by
  have hsre : (1 : ℝ) < (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re := by
    rw [re_ofReal_add_mul_I]
    exact hσ
  have h := norm_tsum_twistedSummand_le_of_far hf1 hmul hbdd hsre hz hδ
    (by rw [im_ofReal_add_mul_I]; exact hunif t ht)
  rwa [re_ofReal_add_mul_I] at h

/-- **The window-free Perron estimate.**  Under a uniform distance lower bound on `[-T, T]` the whole
range contributes at the damped size, and only the kernel tail beyond `T` contributes at the trivial
size. -/
theorem norm_tsum_mul_smoothWeight_le_of_uniform
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {T : ℝ} (hT : 0 ≤ T)
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ∃ C : ℝ, 0 ≤ C ∧
      (2 * Real.pi) *
          ‖∑' n : ℕ, f n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ ≤
        ((N + H) ^ σ / σ) * ((1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2)) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
              (C * (Real.pi - 2 * Real.arctan T)) := by
  classical
  obtain ⟨C, hC0, hCbound⟩ :=
    exists_bound_mellin_smoothWeight_line hN hH (show (0 : ℝ) < σ by linarith)
  refine ⟨C, hC0, ?_⟩
  set damped : ℝ := (1 + 1 / (σ - 1)) *
    Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) with hdamped
  set triv : ℝ := (1 + 1 / (σ - 1)) * Real.exp (7 / 2) with htriv
  set K : ℝ := (N + H) ^ σ / σ with hK
  set F : ℝ → ℂ := fun y =>
    ∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) n with hF
  set W : ℝ → ℂ := fun y => perronKernel σ N H y with hW
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hdamped0 : 0 ≤ damped := by
    rw [hdamped]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have htriv0 : 0 ≤ triv := by
    rw [htriv]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) < N + H := by linarith
    positivity
  have hcontF : Continuous F := continuous_tsum_twistedSummand hbdd hσ
  have hFtriv : ∀ y : ℝ, ‖F y‖ ≤ triv := by
    intro y
    have h := norm_tsum_twistedSummand_le_trivial hf1 hmul hbdd
      (s := ((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
      (by rw [re_ofReal_add_mul_I]; exact hσ)
    rw [re_ofReal_add_mul_I] at h
    exact h
  have hWint : Integrable W :=
    verticalIntegrable_mellin_smoothWeight (σ := σ) hN hH hσ0
  have hWsup : ∀ y : ℝ, ‖W y‖ ≤ K := fun y => norm_perronKernel_le hN.le hH hσ0 y
  have hid := tsum_mul_smoothWeight_eq_integral (a := f) hbdd hf0 hN hH hσ
  have hprod : Integrable (fun y : ℝ => ‖F y‖ * ‖W y‖) := by
    refine Integrable.mono' (hWint.norm.const_mul triv) ?_ ?_
    · exact ((hcontF.norm.aestronglyMeasurable).mul hWint.norm.aestronglyMeasurable)
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hFtriv y) (norm_nonneg _)
  have hnorm : (2 * Real.pi) *
      ‖∑' n : ℕ, f n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
      ≤ ∫ y : ℝ, ‖F y‖ * ‖W y‖ := by
    have hsmul : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, f n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        = (2 * Real.pi) * ‖∑' n : ℕ, f n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hsmul, hid]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards with y
    simp only [hF, hW, twistedSummand, perronKernel, norm_mul]
  have hsplit : (∫ y : ℝ, ‖F y‖ * ‖W y‖)
      = (∫ y in Set.Icc (-T) T, ‖F y‖ * ‖W y‖)
        + ∫ y in (Set.Icc (-T) T)ᶜ, ‖F y‖ * ‖W y‖ :=
    (integral_add_compl measurableSet_Icc hprod).symm
  -- on the range the damped bound holds at every frequency
  have hrange : (∫ y in Set.Icc (-T) T, ‖F y‖ * ‖W y‖) ≤ K * damped * (2 * T) := by
    have hb : ∀ y ∈ Set.Icc (-T) T, ‖F y‖ * ‖W y‖ ≤ damped * K := by
      intro y hy
      have hy' : |y| ≤ T := by
        rw [abs_le]
        exact ⟨hy.1, hy.2⟩
      have h1 : ‖F y‖ ≤ damped :=
        norm_tsum_twistedSummand_le_damped_of_uniform hf1 hmul hbdd hσ hz hδ hunif hy'
      exact mul_le_mul h1 (hWsup y) (norm_nonneg _) hdamped0
    have hint2 : IntegrableOn (fun _ : ℝ => damped * K) (Set.Icc (-T) T) :=
      integrableOn_const (by simp [Real.volume_Icc])
    refine le_trans (setIntegral_mono_on hprod.integrableOn hint2 measurableSet_Icc hb) ?_
    rw [setIntegral_const, measureReal_def, smul_eq_mul, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    have hval : T - -T = 2 * T := by ring
    rw [hval]
    have hcomm : (2 * T) * (damped * K) = K * damped * (2 * T) := by ring
    rw [hcomm]
  -- beyond the range only the trivial bound and the kernel tail
  have htail : (∫ y in (Set.Icc (-T) T)ᶜ, ‖F y‖ * ‖W y‖)
      ≤ triv * (C * (Real.pi - 2 * Real.arctan T)) := by
    have hb : ∀ y ∈ (Set.Icc (-T) T)ᶜ, ‖F y‖ * ‖W y‖ ≤ triv * (C * (1 + y ^ 2)⁻¹) := by
      intro y _
      exact mul_le_mul (hFtriv y) (hCbound y) (norm_nonneg _) htriv0
    have hint2 : IntegrableOn (fun y : ℝ => triv * (C * (1 + y ^ 2)⁻¹))
        (Set.Icc (-T) T)ᶜ :=
      ((integrable_inv_one_add_sq.const_mul C).const_mul triv).integrableOn
    refine le_trans (setIntegral_mono_on hprod.integrableOn hint2 measurableSet_Icc.compl hb) ?_
    rw [integral_const_mul, integral_const_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC0) htriv0
    exact integral_compl_Icc_inv_one_add_sq_le hT
  linarith [hnorm, hsplit, hrange, htail]

end

end RHTower.Sieve
