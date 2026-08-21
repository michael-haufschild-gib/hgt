/-
# Chen--Gupta--Li `h_t`: all-order first Fourier-decay family

This module closes the `∀ j` first family in CGL Lemma 4.3.  It builds the
cutoff-only budget from literal Schwartz derivatives, then proves
`|ξ|^j |ĥ_t(ξ)| ≤ C_{w,j} (1 + |t|)^j` without an external analytic premise.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiMellinPhaseJets
import GaloisForLFunctions.RHTower.ChenGuptaLiHtFirstDecay

noncomputable section

namespace RHTower

open MeasureTheory
open scoped FourierTransform

def cglSchwartzDerivativeOrder (n : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ)^[n] f

theorem cglSchwartzDerivativeOrder_apply (n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    cglSchwartzDerivativeOrder n f x = iteratedDeriv n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [cglSchwartzDerivativeOrder, Function.iterate_succ_apply',
      SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
    congr 1
    funext y
    exact ih y

theorem cglMellinPhase_contDiffAt (t : ℝ) (x : CGLMellinPhaseInput) :
    ContDiffAt ℝ ⊤ (cglMellinPhase t) x.value := by
  unfold cglMellinPhase
  have hlog : ContDiffAt ℝ ⊤ Real.log x.value := Real.contDiffAt_log.mpr x.nonzero
  have hlogC : ContDiffAt ℝ ⊤ (fun y : ℝ => (Real.log y : ℂ)) x.value := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x.value hlog
  have harg : ContDiffAt ℝ ⊤ (fun y : ℝ =>
      (t : ℂ) * (Real.log y : ℂ) * Complex.I) x.value := by
    have ht : ContDiffAt ℝ ⊤ (fun _ : ℝ => (t : ℂ)) x.value := contDiffAt_const
    have hI : ContDiffAt ℝ ⊤ (fun _ : ℝ => Complex.I) x.value := contDiffAt_const
    simpa only [Pi.mul_apply] using ((ht.mul hlogC).mul hI)
  exact harg.cexp

theorem cglSchwartzDerivativeOrder_tsupport_subset (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    tsupport (cglSchwartzDerivativeOrder n f) ⊆ tsupport f := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [cglSchwartzDerivativeOrder, Function.iterate_succ_apply']
    exact (SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ)
      (cglSchwartzDerivativeOrder n f)).trans ih

def cglSmoothBumpHtDerivativeOrder (n : ℕ) (w : CGLSmoothBump) (t : ℝ) :
    SchwartzMap ℝ ℂ :=
  cglSchwartzDerivativeOrder n (cglSmoothBumpHt w t)

theorem cglSmoothBumpHtDerivativeOrder_apply (n : ℕ) (w : CGLSmoothBump) (t x : ℝ) :
    cglSmoothBumpHtDerivativeOrder n w t x =
      iteratedDeriv n (cglSmoothBumpHtValue w t) x := by
  rw [cglSmoothBumpHtDerivativeOrder, cglSchwartzDerivativeOrder_apply]
  rfl

theorem cglSmoothBumpHtDerivativeOrder_tsupport_subset (n : ℕ) (w : CGLSmoothBump) (t : ℝ) :
    tsupport (cglSmoothBumpHtDerivativeOrder n w t) ⊆ Set.Icc (1 : ℝ) 2 := by
  exact (cglSchwartzDerivativeOrder_tsupport_subset n (cglSmoothBumpHt w t)).trans
    (by
      change tsupport (cglSmoothBumpHtValue w t) ⊆ Set.Icc (1 : ℝ) 2
      exact cglSmoothBumpHtValue_tsupport_subset w t)

theorem cglSmoothBumpSquareDerivativeOrder_tsupport_subset (n : ℕ) (w : CGLSmoothBump) :
    tsupport (cglSchwartzDerivativeOrder n (cglSmoothBumpSquare w)) ⊆ Set.Icc (1 : ℝ) 2 := by
  apply (cglSchwartzDerivativeOrder_tsupport_subset n (cglSmoothBumpSquare w)).trans
  apply closure_minimal
  intro y hy
  by_contra hnot
  change cglSmoothBumpSquare w y ≠ 0 at hy
  rw [cglSmoothBumpSquare_apply, w.outside_support y hnot] at hy
  norm_num at hy
  exact isClosed_Icc

theorem iteratedDeriv_cglSmoothBumpHtValue_of_nonzero (w : CGLSmoothBump) (n : ℕ)
    (t : ℝ) (x : CGLMellinPhaseInput) :
    iteratedDeriv n (cglSmoothBumpHtValue w t) x.value =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x.value *
          cglPhaseJet (n - i) t x.value := by
  have hsquare : ContDiffAt ℝ n (cglSmoothBumpSquare w) x.value :=
    (cglSmoothBumpSquare w).contDiffAt n
  have hphase : ContDiffAt ℝ n (cglMellinPhase t) x.value :=
    (cglMellinPhase_contDiffAt t x).of_le (by simp)
  rw [show cglSmoothBumpHtValue w t =
      (cglSmoothBumpSquare w : ℝ → ℂ) * cglMellinPhase t by
        ext y
        simp only [Pi.mul_apply, cglSmoothBumpSquare_apply, cglSmoothBumpHtValue]]
  rw [iteratedDeriv_mul hsquare hphase]
  simp_rw [cglSchwartzDerivativeOrder_apply, iteratedDeriv_cglMellinPhase_of_nonzero]

theorem cglSmoothBumpHtDerivativeOrder_expand (w : CGLSmoothBump) (n : ℕ)
    (t x : ℝ) :
    cglSmoothBumpHtDerivativeOrder n w t x =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x *
          cglPhaseJet (n - i) t x := by
  by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
  · have hpos : x ≠ 0 := by linarith [hx.1]
    rw [cglSmoothBumpHtDerivativeOrder_apply]
    exact iteratedDeriv_cglSmoothBumpHtValue_of_nonzero w n t ⟨x, hpos⟩
  · have hleft : cglSmoothBumpHtDerivativeOrder n w t x = 0 := by
      by_contra hne
      apply hx
      apply cglSmoothBumpHtDerivativeOrder_tsupport_subset n w t
      apply subset_closure
      exact hne
    have hright : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x *
          cglPhaseJet (n - i) t x = 0 := by
      intro i hi
      have hzero : cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x = 0 := by
        by_contra hne
        apply hx
        apply cglSmoothBumpSquareDerivativeOrder_tsupport_subset i w
        apply subset_closure
        exact hne
      rw [hzero]
      ring
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact hright i hi

def cglSmoothBumpHtAllOrderEnvelope (w : CGLSmoothBump) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i * (n - i).factorial : ℕ) : ℝ) *
      ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖

theorem cgl_abs_inv_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    |x⁻¹| ≤ 1 := by
  rw [abs_of_nonneg (inv_nonneg.mpr (by linarith [hx.1]))]
  exact inv_le_one_of_one_le₀ hx.1

theorem cglSmoothBumpHtDerivativeOrder_summand_bound (w : CGLSmoothBump) (n i : ℕ)
    (t x : ℝ) :
    ‖(n.choose i : ℂ) * cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x *
        cglPhaseJet (n - i) t x‖ ≤
      (((n.choose i * (n - i).factorial : ℕ) : ℝ) *
        ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖) * (1 + |t|) ^ n := by
  by_cases hzero : cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x = 0
  · rw [hzero]
    simp
  · have hx : x ∈ Set.Icc (1 : ℝ) 2 := by
      apply cglSmoothBumpSquareDerivativeOrder_tsupport_subset i w
      apply subset_closure
      exact hzero
    have hinv : |x⁻¹| ≤ 1 := cgl_abs_inv_le_one_of_mem_Icc hx
    have hpowinv : |x⁻¹| ^ (n - i) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hinv
    have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hpow : (1 + |t|) ^ (n - i) ≤ (1 + |t|) ^ n :=
      pow_le_pow_right₀ hbase (Nat.sub_le _ _)
    have hphasebound : (n - i).factorial * (1 + |t|) ^ (n - i) * |x⁻¹| ^ (n - i) ≤
        (n - i).factorial * (1 + |t|) ^ n := by
      calc
        (n - i).factorial * (1 + |t|) ^ (n - i) * |x⁻¹| ^ (n - i) =
            (n - i).factorial *
              ((1 + |t|) ^ (n - i) * |x⁻¹| ^ (n - i)) := by ring
        _ ≤ (n - i).factorial * (1 + |t|) ^ n := by
          apply mul_le_mul_of_nonneg_left
          · calc
              (1 + |t|) ^ (n - i) * |x⁻¹| ^ (n - i) ≤
                  (1 + |t|) ^ (n - i) * 1 := by
                gcongr
              _ ≤ (1 + |t|) ^ n := by
                simpa using hpow
          · positivity
    have hjet := norm_cglPhaseJet_le (n - i) t x
    rw [norm_mul, norm_mul]
    norm_cast
    calc
      (n.choose i : ℝ) * ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖ *
          ‖cglPhaseJet (n - i) t x‖ ≤
        (n.choose i : ℝ) * ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖ *
          ((n - i).factorial * (1 + |t|) ^ (n - i) * |x⁻¹| ^ (n - i)) := by
        gcongr
      _ ≤ (n.choose i : ℝ) * ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖ *
          ((n - i).factorial * (1 + |t|) ^ n) := by
        gcongr
      _ = (((n.choose i * (n - i).factorial : ℕ) : ℝ) *
          ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖) * (1 + |t|) ^ n := by
        rw [Nat.cast_mul]
        ring

theorem norm_cglSmoothBumpHtDerivativeOrder_le_envelope (w : CGLSmoothBump) (n : ℕ)
    (t x : ℝ) :
    ‖cglSmoothBumpHtDerivativeOrder n w t x‖ ≤
      cglSmoothBumpHtAllOrderEnvelope w n x * (1 + |t|) ^ n := by
  rw [cglSmoothBumpHtDerivativeOrder_expand]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x *
          cglPhaseJet (n - i) t x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖(n.choose i : ℂ) * cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x *
            cglPhaseJet (n - i) t x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (((n.choose i * (n - i).factorial : ℕ) : ℝ) *
          ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖) * (1 + |t|) ^ n := by
      gcongr with i hi
      exact cglSmoothBumpHtDerivativeOrder_summand_bound w n i t x
    _ = cglSmoothBumpHtAllOrderEnvelope w n x * (1 + |t|) ^ n := by
      simp only [cglSmoothBumpHtAllOrderEnvelope, Finset.sum_mul]

def cglSmoothBumpHtAllOrderBudget (w : CGLSmoothBump) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ((n.choose i * (n - i).factorial : ℕ) : ℝ) *
    ∫ x : ℝ, ‖cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w) x‖

theorem cglSmoothBumpHtAllOrderEnvelope_integrable (w : CGLSmoothBump) (n : ℕ) :
    Integrable (cglSmoothBumpHtAllOrderEnvelope w n) := by
  unfold cglSmoothBumpHtAllOrderEnvelope
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  exact ((cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w)).integrable.norm).const_mul _

theorem integral_cglSmoothBumpHtAllOrderEnvelope (w : CGLSmoothBump) (n : ℕ) :
    ∫ x : ℝ, cglSmoothBumpHtAllOrderEnvelope w n x =
      cglSmoothBumpHtAllOrderBudget w n := by
  unfold cglSmoothBumpHtAllOrderEnvelope cglSmoothBumpHtAllOrderBudget
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
  · intro i hi
    exact ((cglSchwartzDerivativeOrder i (cglSmoothBumpSquare w)).integrable.norm).const_mul _

theorem integral_norm_cglSmoothBumpHtDerivativeOrder_le (w : CGLSmoothBump) (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, ‖cglSmoothBumpHtDerivativeOrder n w t x‖ ≤
      cglSmoothBumpHtAllOrderBudget w n * (1 + |t|) ^ n := by
  have hleft : Integrable (fun x : ℝ => ‖cglSmoothBumpHtDerivativeOrder n w t x‖) :=
    (cglSmoothBumpHtDerivativeOrder n w t).integrable.norm
  have hright : Integrable (fun x : ℝ =>
      cglSmoothBumpHtAllOrderEnvelope w n x * (1 + |t|) ^ n) :=
    (cglSmoothBumpHtAllOrderEnvelope_integrable w n).mul_const _
  calc
    ∫ x : ℝ, ‖cglSmoothBumpHtDerivativeOrder n w t x‖ ≤
        ∫ x : ℝ, cglSmoothBumpHtAllOrderEnvelope w n x * (1 + |t|) ^ n :=
      integral_mono hleft hright (norm_cglSmoothBumpHtDerivativeOrder_le_envelope w n t)
    _ = (∫ x : ℝ, cglSmoothBumpHtAllOrderEnvelope w n x) * (1 + |t|) ^ n := by
      rw [integral_mul_const]
    _ = cglSmoothBumpHtAllOrderBudget w n * (1 + |t|) ^ n := by
      rw [integral_cglSmoothBumpHtAllOrderEnvelope]

theorem cglSmoothBumpHtDerivativeOrder_eq_iteratedDeriv (w : CGLSmoothBump) (n : ℕ) (t : ℝ) :
    cglSmoothBumpHtDerivativeOrder n w t = iteratedDeriv n (cglSmoothBumpHt w t : ℝ → ℂ) := by
  ext x
  exact cglSmoothBumpHtDerivativeOrder_apply n w t x

theorem cglSmoothBumpHtDerivativeOrder_fourier (w : CGLSmoothBump) (n : ℕ) (t ξ : ℝ) :
    𝓕 (cglSmoothBumpHtDerivativeOrder n w t : ℝ → ℂ) ξ =
      (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ n * 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ := by
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      Integrable (iteratedDeriv k (cglSmoothBumpHt w t : ℝ → ℂ)) := by
    intro k hk
    rw [← cglSmoothBumpHtDerivativeOrder_eq_iteratedDeriv w k t]
    exact (cglSmoothBumpHtDerivativeOrder k w t).integrable
  have h := Real.fourier_iteratedDeriv (f := (cglSmoothBumpHt w t : ℝ → ℂ))
    (N := (⊤ : ℕ∞)) (n := n) ((cglSmoothBumpHt w t).smooth ⊤) hint le_top
  rw [← cglSmoothBumpHtDerivativeOrder_eq_iteratedDeriv w n t] at h
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun h ξ

theorem norm_cglSmoothBumpHtDerivativeOrder_fourier (w : CGLSmoothBump) (n : ℕ) (t ξ : ℝ) :
    (2 * Real.pi) ^ n * (|ξ| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) =
      ‖𝓕 (cglSmoothBumpHtDerivativeOrder n w t : ℝ → ℂ) ξ‖ := by
  rw [cglSmoothBumpHtDerivativeOrder_fourier, norm_mul, norm_pow]
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  norm_num [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  ring

theorem norm_fourier_cglSmoothBumpHtDerivativeOrder_le_integral (w : CGLSmoothBump)
    (n : ℕ) (t ξ : ℝ) :
    ‖𝓕 (cglSmoothBumpHtDerivativeOrder n w t : ℝ → ℂ) ξ‖ ≤
      ∫ x : ℝ, ‖cglSmoothBumpHtDerivativeOrder n w t x‖ := by
  have h := cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget
    (cglSmoothBumpHtDerivativeOrder n w t) 0 ξ
  rw [pow_zero, one_mul,
    show cglSchwartzFourierDecayBudget (cglSmoothBumpHtDerivativeOrder n w t) 0 =
      ∫ x : ℝ, ‖cglSmoothBumpHtDerivativeOrder n w t x‖ by
        simp [cglSchwartzFourierDecayBudget]] at h
  exact h

theorem cglSmoothBumpHt_allOrder_fourier_decay_linear (w : CGLSmoothBump) (n : ℕ)
    (t ξ : ℝ) :
    (2 * Real.pi) ^ n * (|ξ| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) ≤
      cglSmoothBumpHtAllOrderBudget w n * (1 + |t|) ^ n := by
  calc
    (2 * Real.pi) ^ n * (|ξ| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) =
        ‖𝓕 (cglSmoothBumpHtDerivativeOrder n w t : ℝ → ℂ) ξ‖ :=
      norm_cglSmoothBumpHtDerivativeOrder_fourier w n t ξ
    _ ≤ ∫ x : ℝ, ‖cglSmoothBumpHtDerivativeOrder n w t x‖ :=
      norm_fourier_cglSmoothBumpHtDerivativeOrder_le_integral w n t ξ
    _ ≤ cglSmoothBumpHtAllOrderBudget w n * (1 + |t|) ^ n :=
      integral_norm_cglSmoothBumpHtDerivativeOrder_le w n t

/-- The all-order first family of CGL Lemma 4.3. -/
theorem cglSmoothBumpHt_allOrder_fourier_decay (w : CGLSmoothBump) (n : ℕ)
    (t ξ : ℝ) :
    |ξ| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖ ≤
      (cglSmoothBumpHtAllOrderBudget w n / (2 * Real.pi) ^ n) * (1 + |t|) ^ n := by
  have hpos : 0 < (2 * Real.pi) ^ n := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  apply le_of_mul_le_mul_left _ hpos
  calc
    (2 * Real.pi) ^ n * (|ξ| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) ≤
        cglSmoothBumpHtAllOrderBudget w n * (1 + |t|) ^ n :=
      cglSmoothBumpHt_allOrder_fourier_decay_linear w n t ξ
    _ = (2 * Real.pi) ^ n *
        ((cglSmoothBumpHtAllOrderBudget w n / (2 * Real.pi) ^ n) * (1 + |t|) ^ n) := by
      field_simp [ne_of_gt hpos]

end RHTower
