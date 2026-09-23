import GaloisForLFunctions.RHTower.Sieve.HalaszIntegralBound
import GaloisForLFunctions.HTGeometry.SmoothWeightPerron

/-!
# The smoothed sum of a bounded multiplicative function

The smoothed Perron formula writes `2π ∑ₙ f(n) w(n)` as the vertical integral of the Dirichlet series
against the Mellin transform of the weight.  Splitting that integral at height `T` and using the two
sides of the Halász estimate — the mean-value bound on `[-T, T]` and the trivial bound beyond it —
gives

`2π ‖∑ₙ f(n)w(n)‖ ≤ Wsup · (Halász integral bound) + trivial · ∫_{|y| > T} ‖W‖`,

for any uniform bound `Wsup` on the kernel.  Both terms are explicit; the first carries the `e^{-δ²}`
saving, the second is controlled by the kernel's decay.

This is the assembly step: every ingredient is unconditional, and the only quantities left free are the
two kernel integrals, which the smooth-weight Mellin layer supplies.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

section

variable {f : ℕ → ℂ}

/-- The vertical Perron kernel: the Mellin transform of the smooth weight on the line `Re s = σ`. -/
noncomputable def perronKernel (σ N H : ℝ) (y : ℝ) : ℂ :=
  mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I)

/-- **The smoothed sum obeys the Halász bound.**  Perron inversion plus the two sides of the Halász
estimate. -/
theorem norm_tsum_mul_smoothWeight_le
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    (hWz : 0 < logSqWeight z) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {T : ℝ} (hT : 0 ≤ T) {Wsup : ℝ}
    (hWsup : ∀ y : ℝ, ‖perronKernel σ N H y‖ ≤ Wsup) :
    (2 * Real.pi) * ‖∑' n : ℕ, f n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ ≤
      Wsup * ((1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
              (2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z))))
        + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            ∫ y in (Set.Icc (-T) T)ᶜ, ‖perronKernel σ N H y‖ := by
  classical
  set triv : ℝ := (1 + 1 / (σ - 1)) * Real.exp (7 / 2) with htriv
  set F : ℝ → ℂ := fun y =>
    ∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) n with hF
  set W : ℝ → ℂ := fun y => perronKernel σ N H y with hW
  have hWsup0 : 0 ≤ Wsup := le_trans (norm_nonneg _) (hWsup 0)
  have htriv0 : 0 ≤ triv := by
    rw [htriv]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hcontF : Continuous F := continuous_tsum_twistedSummand hbdd hσ
  have hFbound : ∀ y : ℝ, ‖F y‖ ≤ triv := by
    intro y
    have h := norm_tsum_twistedSummand_le_trivial hf1 hmul hbdd
      (s := ((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
      (by rw [re_ofReal_add_mul_I]; exact hσ)
    rw [re_ofReal_add_mul_I] at h
    exact h
  have hWint : Integrable W :=
    verticalIntegrable_mellin_smoothWeight (σ := σ) hN hH (by linarith)
  -- the Perron identity
  have hid := tsum_mul_smoothWeight_eq_integral (a := f) hbdd hf0 hN hH hσ
  -- the integrand of the vertical integral
  have hprod : Integrable (fun y : ℝ => ‖F y‖ * ‖W y‖) := by
    refine Integrable.mono' (hWint.norm.const_mul triv) ?_ ?_
    · exact ((hcontF.norm.aestronglyMeasurable).mul hWint.norm.aestronglyMeasurable)
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hFbound y) (norm_nonneg _)
  -- pass to the modulus
  have hnorm : (2 * Real.pi) * ‖∑' n : ℕ, f n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
      ≤ ∫ y : ℝ, ‖F y‖ * ‖W y‖ := by
    have hsmul : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, f n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        = (2 * Real.pi) * ‖∑' n : ℕ, f n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hsmul, hid]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards with y
    simp only [hF, hW, twistedSummand, perronKernel, norm_mul]
  -- split the vertical integral at height `T`
  have hsplit : (∫ y : ℝ, ‖F y‖ * ‖W y‖)
      = (∫ y in Set.Icc (-T) T, ‖F y‖ * ‖W y‖)
        + ∫ y in (Set.Icc (-T) T)ᶜ, ‖F y‖ * ‖W y‖ :=
    (integral_add_compl measurableSet_Icc hprod).symm
  -- on the range, the mean-value bound
  have hrange : (∫ y in Set.Icc (-T) T, ‖F y‖ * ‖W y‖)
      ≤ Wsup * ∫ y in Set.Icc (-T) T, ‖F y‖ := by
    have hb : ∀ y ∈ Set.Icc (-T) T, ‖F y‖ * ‖W y‖ ≤ Wsup * ‖F y‖ := by
      intro y _
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hWsup y) (norm_nonneg _)
    have hint1 : IntegrableOn (fun y : ℝ => ‖F y‖ * ‖W y‖) (Set.Icc (-T) T) :=
      hprod.integrableOn
    have hint2 : IntegrableOn (fun y : ℝ => Wsup * ‖F y‖) (Set.Icc (-T) T) :=
      (hcontF.norm.integrableOn_Icc).const_mul Wsup
    refine le_trans (setIntegral_mono_on hint1 hint2 measurableSet_Icc hb) (le_of_eq ?_)
    exact integral_const_mul Wsup _
  -- beyond the range, the trivial bound
  have htail : (∫ y in (Set.Icc (-T) T)ᶜ, ‖F y‖ * ‖W y‖)
      ≤ triv * ∫ y in (Set.Icc (-T) T)ᶜ, ‖W y‖ := by
    have hb : ∀ y ∈ (Set.Icc (-T) T)ᶜ, ‖F y‖ * ‖W y‖ ≤ triv * ‖W y‖ := by
      intro y _
      exact mul_le_mul_of_nonneg_right (hFbound y) (norm_nonneg _)
    have hint1 : IntegrableOn (fun y : ℝ => ‖F y‖ * ‖W y‖) (Set.Icc (-T) T)ᶜ :=
      hprod.integrableOn
    have hint2 : IntegrableOn (fun y : ℝ => triv * ‖W y‖) (Set.Icc (-T) T)ᶜ :=
      (hWint.norm.integrableOn).const_mul triv
    refine le_trans (setIntegral_mono_on hint1 hint2 measurableSet_Icc.compl hb) (le_of_eq ?_)
    exact integral_const_mul triv _
  -- the mean-value bound on the range
  have hmean := integral_norm_tsum_twistedSummand_le hf1 hmul hbdd hσ hz2 hδ hWz hT
  have hWsupmul : Wsup * ∫ y in Set.Icc (-T) T, ‖F y‖ ≤
      Wsup * ((1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
              (2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z)))) :=
    mul_le_mul_of_nonneg_left hmean hWsup0
  linarith [hnorm, hsplit, hrange, htail, hWsupmul]

/-! ## The kernel bound instantiated -/

/-- **The vertical kernel is uniformly bounded by `(N+H)^σ / σ`.**  The cutoff has modulus at most one
and vanishes past `N + H`, so its Mellin transform obeys the trivial size bound on the whole line. -/
theorem norm_perronKernel_le {σ N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) (hσ : 0 < σ) (y : ℝ) :
    ‖perronKernel σ N H y‖ ≤ (N + H) ^ σ / σ := by
  have h := norm_mellin_smoothWeight_le_pow (N := N) (H := H) hN hH
    (s := ((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
    (by rw [re_ofReal_add_mul_I]; exact hσ)
  rw [re_ofReal_add_mul_I] at h
  exact h

/-- **The assembled bound with the kernel size made explicit.**  Only the kernel tail is left free, and
it is controlled by the quadratic decay of the transform. -/
theorem norm_tsum_mul_smoothWeight_le_explicit
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    (hWz : 0 < logSqWeight z) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {T : ℝ} (hT : 0 ≤ T) :
    (2 * Real.pi) *
        ‖∑' n : ℕ, f n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ ≤
      ((N + H) ^ σ / σ) * ((1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
              (2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z))))
        + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            ∫ y in (Set.Icc (-T) T)ᶜ, ‖perronKernel σ N H y‖ :=
  norm_tsum_mul_smoothWeight_le hf1 hmul hbdd hf0 hσ hz2 hδ hWz hN hH hT
    (fun y => norm_perronKernel_le hN.le hH (by linarith) y)


/-! ## The kernel tail -/

/-- The Cauchy tail: outside `[-T, T]` the reciprocal-quadratic majorant integrates to
`π − 2 arctan T`. -/
theorem integral_compl_Icc_inv_one_add_sq_le {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in (Set.Icc (-T) T)ᶜ, (1 + y ^ (2 : ℕ))⁻¹) ≤ Real.pi - 2 * Real.arctan T := by
  have hsub : (Set.Icc (-T) T)ᶜ ⊆ Set.Iic (-T) ∪ Set.Ioi T := by
    intro y hy
    rcases lt_or_ge y (-T) with h | h
    · exact Or.inl (le_of_lt h)
    · rcases lt_or_ge T y with h2 | h2
      · exact Or.inr h2
      · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hy
  have hdisj : Disjoint (Set.Iic (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro a ha hb
    have h1 : a ≤ -T := ha
    have h2 : T < a := hb
    linarith
  have hunion : (∫ y in Set.Iic (-T) ∪ Set.Ioi T, (1 + y ^ (2 : ℕ))⁻¹)
      = (∫ y in Set.Iic (-T), (1 + y ^ (2 : ℕ))⁻¹) + ∫ y in Set.Ioi T, (1 + y ^ (2 : ℕ))⁻¹ :=
    setIntegral_union hdisj measurableSet_Ioi
      integrable_inv_one_add_sq.integrableOn integrable_inv_one_add_sq.integrableOn
  have hmono : (∫ y in (Set.Icc (-T) T)ᶜ, (1 + y ^ (2 : ℕ))⁻¹)
      ≤ ∫ y in Set.Iic (-T) ∪ Set.Ioi T, (1 + y ^ (2 : ℕ))⁻¹ := by
    refine setIntegral_mono_set integrable_inv_one_add_sq.integrableOn ?_ hsub.eventuallyLE
    filter_upwards with y using by positivity
  refine le_trans hmono (le_of_eq ?_)
  rw [hunion, integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq, Real.arctan_neg]
  ring

/-- **The assembled bound with the kernel tail as a parameter.**  The `∃ C` of the assembled form hides
a bound for the Mellin kernel that depends only on `N`, `H`, `σ` — not on the coefficient sequence — so
it belongs in the hypotheses.  Stated this way the constant can be chosen once and used for every
sequence, which is what an asymptotic statement needs. -/
theorem norm_tsum_mul_smoothWeight_le_of_kernelBound
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    (hWz : 0 < logSqWeight z) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {T : ℝ} (hT : 0 ≤ T) {C : ℝ} (hC0 : 0 ≤ C)
    (hCbound : ∀ y : ℝ, ‖perronKernel σ N H y‖ ≤ C * (1 + y ^ (2 : ℕ))⁻¹) :
      (2 * Real.pi) *
          ‖∑' n : ℕ, f n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ ≤
        ((N + H) ^ σ / σ) * ((1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) * (2 * T)
            + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
              ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
                (2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z))))
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
              (C * (Real.pi - 2 * Real.arctan T)) := by
  have htriv0 : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hWint : Integrable (fun y : ℝ => perronKernel σ N H y) :=
    verticalIntegrable_mellin_smoothWeight (σ := σ) hN hH (by linarith)
  have htail : (∫ y in (Set.Icc (-T) T)ᶜ, ‖perronKernel σ N H y‖)
      ≤ C * (Real.pi - 2 * Real.arctan T) := by
    have hb : ∀ y ∈ (Set.Icc (-T) T)ᶜ, ‖perronKernel σ N H y‖ ≤ C * (1 + y ^ (2 : ℕ))⁻¹ :=
      fun y _ => hCbound y
    have hint1 : IntegrableOn (fun y : ℝ => ‖perronKernel σ N H y‖) (Set.Icc (-T) T)ᶜ :=
      hWint.norm.integrableOn
    have hint2 : IntegrableOn (fun y : ℝ => C * (1 + y ^ (2 : ℕ))⁻¹) (Set.Icc (-T) T)ᶜ :=
      (integrable_inv_one_add_sq.const_mul C).integrableOn
    refine le_trans (setIntegral_mono_on hint1 hint2 measurableSet_Icc.compl hb) ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_inv_one_add_sq_le hT) hC0
  have hmain := norm_tsum_mul_smoothWeight_le_explicit hf1 hmul hbdd hf0 hσ hz2 hδ hWz hN hH hT
  have hstep : (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
      ∫ y in (Set.Icc (-T) T)ᶜ, ‖perronKernel σ N H y‖
      ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) * (C * (Real.pi - 2 * Real.arctan T)) :=
    mul_le_mul_of_nonneg_left htail htriv0
  linarith

/-- **The assembled bound with both kernel quantities discharged.**  The instance at the Mellin kernel
bound. -/
theorem exists_norm_tsum_mul_smoothWeight_le
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    (hWz : 0 < logSqWeight z) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      (2 * Real.pi) *
          ‖∑' n : ℕ, f n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ ≤
        ((N + H) ^ σ / σ) * ((1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) * (2 * T)
            + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
              ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
                (2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z))))
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
              (C * (Real.pi - 2 * Real.arctan T)) := by
  obtain ⟨C, hC0, hCbound⟩ :=
    exists_bound_mellin_smoothWeight_line hN hH (show (0 : ℝ) < σ by linarith)
  exact ⟨C, hC0, norm_tsum_mul_smoothWeight_le_of_kernelBound hf1 hmul hbdd hf0 hσ hz2 hδ hWz
    hN hH hT hC0 hCbound⟩

end

end RHTower.Sieve
