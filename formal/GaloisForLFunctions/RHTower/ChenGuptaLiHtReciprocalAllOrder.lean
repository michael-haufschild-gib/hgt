/-
# Chen--Gupta--Li `h_t`: all-order reciprocal-parameter Fourier decay

This module completes the second family in CGL Lemma 4.3. It combines the
exact logarithmic Mellin--Fourier bridge, finite additive-phase jets, and a
closed Leibniz `L¹` budget to prove every reciprocal-parameter decay order.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLogPhaseJets
import GaloisForLFunctions.RHTower.ChenGuptaLiHtAllOrder

noncomputable section

namespace RHTower

open MeasureTheory
open scoped FourierTransform

theorem contDiff_cglLogAdditivePhase (xi : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cglLogAdditivePhase xi) := by
  unfold cglLogAdditivePhase
  have hexpR : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_id.neg
  have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (-2 * Real.pi * xi : ℝ)) :=
    contDiff_const
  have hargR : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => -2 * Real.pi * xi * Real.exp (-u)) :=
    hconst.mul hexpR
  have hargC : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ((-2 * Real.pi * xi * Real.exp (-u) : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hargR
  have hI : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => Complex.I) := contDiff_const
  exact (hargC.mul hI).cexp

def cglLogCutoffProfileDerivativeOrder (n : ℕ) (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  cglSchwartzDerivativeOrder n (cglLogCutoffProfileSchwartz w)

theorem cglLogCutoffProfileDerivativeOrder_apply (n : ℕ) (w : CGLSmoothBump) (u : ℝ) :
    cglLogCutoffProfileDerivativeOrder n w u = iteratedDeriv n (cglLogCutoffProfile w) u := by
  rw [cglLogCutoffProfileDerivativeOrder, cglSchwartzDerivativeOrder_apply]
  rfl

theorem cglLogCutoffProfileDerivativeOrder_tsupport_subset (n : ℕ) (w : CGLSmoothBump) :
    tsupport (cglLogCutoffProfileDerivativeOrder n w) ⊆ Set.Icc (-Real.log 2) 0 := by
  exact (cglSchwartzDerivativeOrder_tsupport_subset n (cglLogCutoffProfileSchwartz w)).trans
    (cglLogCutoffProfile_tsupport_subset w)

def cglLogFourierAmplitudeDerivativeOrder (n : ℕ) (w : CGLSmoothBump) (xi : ℝ) :
    SchwartzMap ℝ ℂ :=
  cglSchwartzDerivativeOrder n (cglLogFourierAmplitudeSchwartz w xi)

theorem cglLogFourierAmplitudeDerivativeOrder_apply (n : ℕ) (w : CGLSmoothBump)
    (xi u : ℝ) :
    cglLogFourierAmplitudeDerivativeOrder n w xi u =
      iteratedDeriv n (cglLogFourierAmplitude w xi) u := by
  rw [cglLogFourierAmplitudeDerivativeOrder, cglSchwartzDerivativeOrder_apply]
  rfl

theorem cglLogFourierAmplitude_tsupport_subset (w : CGLSmoothBump) (xi : ℝ) :
    tsupport (cglLogFourierAmplitudeSchwartz w xi) ⊆ Set.Icc (-Real.log 2) 0 := by
  apply closure_minimal
  intro u hu
  by_contra hnot
  change cglLogFourierAmplitude w xi u ≠ 0 at hu
  exact hu (cglLogFourierAmplitude_eq_zero_of_not_mem w xi u hnot)
  exact isClosed_Icc

theorem cglLogFourierAmplitudeDerivativeOrder_tsupport_subset (n : ℕ) (w : CGLSmoothBump)
    (xi : ℝ) :
    tsupport (cglLogFourierAmplitudeDerivativeOrder n w xi) ⊆ Set.Icc (-Real.log 2) 0 := by
  exact (cglSchwartzDerivativeOrder_tsupport_subset n (cglLogFourierAmplitudeSchwartz w xi)).trans
    (cglLogFourierAmplitude_tsupport_subset w xi)

theorem iteratedDeriv_cglLogFourierAmplitude (w : CGLSmoothBump) (n : ℕ) (xi u : ℝ) :
    iteratedDeriv n (cglLogFourierAmplitude w xi) u =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglLogCutoffProfileDerivativeOrder i w u *
          cglLogPhaseJet (n - i) xi u := by
  have hcut : ContDiffAt ℝ n (cglLogCutoffProfile w) u :=
    ((contDiff_cglLogCutoffProfile w).of_le
      (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hphase : ContDiffAt ℝ n (cglLogAdditivePhase xi) u :=
    ((contDiff_cglLogAdditivePhase xi).of_le
      (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)).contDiffAt
  rw [show cglLogFourierAmplitude w xi =
      cglLogCutoffProfile w * cglLogAdditivePhase xi by
        ext v
        exact cglLogFourierAmplitude_eq_cutoff_mul_phase w xi v]
  rw [iteratedDeriv_mul hcut hphase]
  simp_rw [cglLogCutoffProfileDerivativeOrder_apply, iteratedDeriv_cglLogAdditivePhase]

theorem cglLogFourierAmplitudeDerivativeOrder_expand (w : CGLSmoothBump) (n : ℕ)
    (xi u : ℝ) :
    cglLogFourierAmplitudeDerivativeOrder n w xi u =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglLogCutoffProfileDerivativeOrder i w u *
          cglLogPhaseJet (n - i) xi u := by
  by_cases hu : u ∈ Set.Icc (-Real.log 2) 0
  · rw [cglLogFourierAmplitudeDerivativeOrder_apply]
    exact iteratedDeriv_cglLogFourierAmplitude w n xi u
  · have hleft : cglLogFourierAmplitudeDerivativeOrder n w xi u = 0 := by
      by_contra hne
      apply hu
      apply cglLogFourierAmplitudeDerivativeOrder_tsupport_subset n w xi
      apply subset_closure
      exact hne
    have hright : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglLogCutoffProfileDerivativeOrder i w u *
          cglLogPhaseJet (n - i) xi u = 0 := by
      intro i hi
      have hzero : cglLogCutoffProfileDerivativeOrder i w u = 0 := by
        by_contra hne
        apply hu
        apply cglLogCutoffProfileDerivativeOrder_tsupport_subset i w
        apply subset_closure
        exact hne
      rw [hzero]
      ring
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact hright i hi

def cglLogFourierAmplitudeAllOrderEnvelope (w : CGLSmoothBump) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℝ) * cglLogPhasePolynomialBudget (n - i)) *
      ‖cglLogCutoffProfileDerivativeOrder i w u‖

theorem cglLogPhasePolynomialBudget_nonneg (n : ℕ) :
    0 ≤ cglLogPhasePolynomialBudget n := by
  unfold cglLogPhasePolynomialBudget
  positivity

theorem cglLogFourierAmplitudeDerivativeOrder_summand_bound (w : CGLSmoothBump)
    (n i : ℕ) (xi u : ℝ) :
    ‖(n.choose i : ℂ) * cglLogCutoffProfileDerivativeOrder i w u *
        cglLogPhaseJet (n - i) xi u‖ ≤
      (((n.choose i : ℝ) * cglLogPhasePolynomialBudget (n - i)) *
        ‖cglLogCutoffProfileDerivativeOrder i w u‖) * (1 + |xi|) ^ n := by
  by_cases hzero : cglLogCutoffProfileDerivativeOrder i w u = 0
  · rw [hzero]
    simp
  · have hu : u ∈ Set.Icc (-Real.log 2) 0 := by
      apply cglLogCutoffProfileDerivativeOrder_tsupport_subset i w
      apply subset_closure
      exact hzero
    have hjet := norm_cglLogPhaseJet_le (n - i) xi u hu
    have hbase : 1 ≤ 1 + |xi| := by linarith [abs_nonneg xi]
    have hpow : (1 + |xi|) ^ (n - i) ≤ (1 + |xi|) ^ n :=
      pow_le_pow_right₀ hbase (Nat.sub_le _ _)
    rw [norm_mul, norm_mul]
    norm_cast
    calc
      (n.choose i : ℝ) * ‖cglLogCutoffProfileDerivativeOrder i w u‖ *
          ‖cglLogPhaseJet (n - i) xi u‖ ≤
        (n.choose i : ℝ) * ‖cglLogCutoffProfileDerivativeOrder i w u‖ *
          (cglLogPhasePolynomialBudget (n - i) * (1 + |xi|) ^ (n - i)) := by
        gcongr
      _ = (((n.choose i : ℝ) * cglLogPhasePolynomialBudget (n - i)) *
          ‖cglLogCutoffProfileDerivativeOrder i w u‖) * (1 + |xi|) ^ (n - i) := by
        ring
      _ ≤ (((n.choose i : ℝ) * cglLogPhasePolynomialBudget (n - i)) *
          ‖cglLogCutoffProfileDerivativeOrder i w u‖) * (1 + |xi|) ^ n := by
        apply mul_le_mul_of_nonneg_left hpow
        exact mul_nonneg
          (mul_nonneg (by positivity) (cglLogPhasePolynomialBudget_nonneg _))
          (norm_nonneg _)

theorem norm_cglLogFourierAmplitudeDerivativeOrder_le_envelope (w : CGLSmoothBump) (n : ℕ)
    (xi u : ℝ) :
    ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖ ≤
      cglLogFourierAmplitudeAllOrderEnvelope w n u * (1 + |xi|) ^ n := by
  rw [cglLogFourierAmplitudeDerivativeOrder_expand]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * cglLogCutoffProfileDerivativeOrder i w u *
          cglLogPhaseJet (n - i) xi u‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖(n.choose i : ℂ) * cglLogCutoffProfileDerivativeOrder i w u *
            cglLogPhaseJet (n - i) xi u‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (((n.choose i : ℝ) * cglLogPhasePolynomialBudget (n - i)) *
          ‖cglLogCutoffProfileDerivativeOrder i w u‖) * (1 + |xi|) ^ n := by
      gcongr with i hi
      exact cglLogFourierAmplitudeDerivativeOrder_summand_bound w n i xi u
    _ = cglLogFourierAmplitudeAllOrderEnvelope w n u * (1 + |xi|) ^ n := by
      simp only [cglLogFourierAmplitudeAllOrderEnvelope, Finset.sum_mul]

def cglLogFourierAmplitudeAllOrderBudget (w : CGLSmoothBump) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℝ) * cglLogPhasePolynomialBudget (n - i)) *
      ∫ u : ℝ, ‖cglLogCutoffProfileDerivativeOrder i w u‖

theorem cglLogFourierAmplitudeAllOrderEnvelope_integrable (w : CGLSmoothBump) (n : ℕ) :
    Integrable (cglLogFourierAmplitudeAllOrderEnvelope w n) := by
  unfold cglLogFourierAmplitudeAllOrderEnvelope
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  exact ((cglLogCutoffProfileDerivativeOrder i w).integrable.norm).const_mul _

theorem integral_cglLogFourierAmplitudeAllOrderEnvelope (w : CGLSmoothBump) (n : ℕ) :
    ∫ u : ℝ, cglLogFourierAmplitudeAllOrderEnvelope w n u =
      cglLogFourierAmplitudeAllOrderBudget w n := by
  unfold cglLogFourierAmplitudeAllOrderEnvelope cglLogFourierAmplitudeAllOrderBudget
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
  · intro i hi
    exact ((cglLogCutoffProfileDerivativeOrder i w).integrable.norm).const_mul _

theorem integral_norm_cglLogFourierAmplitudeDerivativeOrder_le (w : CGLSmoothBump) (n : ℕ)
    (xi : ℝ) :
    ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w n * (1 + |xi|) ^ n := by
  have hleft : Integrable (fun u : ℝ => ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖) :=
    (cglLogFourierAmplitudeDerivativeOrder n w xi).integrable.norm
  have hright : Integrable (fun u : ℝ =>
      cglLogFourierAmplitudeAllOrderEnvelope w n u * (1 + |xi|) ^ n) :=
    (cglLogFourierAmplitudeAllOrderEnvelope_integrable w n).mul_const _
  calc
    ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖ ≤
        ∫ u : ℝ, cglLogFourierAmplitudeAllOrderEnvelope w n u * (1 + |xi|) ^ n :=
      integral_mono hleft hright (norm_cglLogFourierAmplitudeDerivativeOrder_le_envelope w n xi)
    _ = (∫ u : ℝ, cglLogFourierAmplitudeAllOrderEnvelope w n u) * (1 + |xi|) ^ n := by
      rw [integral_mul_const]
    _ = cglLogFourierAmplitudeAllOrderBudget w n * (1 + |xi|) ^ n := by
      rw [integral_cglLogFourierAmplitudeAllOrderEnvelope]

theorem cglLogFourierAmplitudeDerivativeOrder_eq_iteratedDeriv (w : CGLSmoothBump)
    (n : ℕ) (xi : ℝ) :
    cglLogFourierAmplitudeDerivativeOrder n w xi =
      iteratedDeriv n (cglLogFourierAmplitude w xi) := by
  ext u
  exact cglLogFourierAmplitudeDerivativeOrder_apply n w xi u

theorem cglLogFourierAmplitudeDerivativeOrder_fourier (w : CGLSmoothBump) (n : ℕ)
    (xi τ : ℝ) :
    𝓕 (cglLogFourierAmplitudeDerivativeOrder n w xi : ℝ → ℂ) τ =
      (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n * 𝓕 (cglLogFourierAmplitude w xi) τ := by
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      Integrable (iteratedDeriv k (cglLogFourierAmplitude w xi)) := by
    intro k hk
    rw [← cglLogFourierAmplitudeDerivativeOrder_eq_iteratedDeriv w k xi]
    exact (cglLogFourierAmplitudeDerivativeOrder k w xi).integrable
  have h := Real.fourier_iteratedDeriv (f := (cglLogFourierAmplitude w xi))
    (N := (⊤ : ℕ∞)) (n := n) ((cglLogFourierAmplitudeSchwartz w xi).smooth ⊤) hint le_top
  rw [← cglLogFourierAmplitudeDerivativeOrder_eq_iteratedDeriv w n xi] at h
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun h τ

theorem norm_cglLogFourierAmplitudeDerivativeOrder_fourier (w : CGLSmoothBump) (n : ℕ)
    (xi τ : ℝ) :
    (2 * Real.pi) ^ n * (|τ| ^ n * ‖𝓕 (cglLogFourierAmplitude w xi) τ‖) =
      ‖𝓕 (cglLogFourierAmplitudeDerivativeOrder n w xi : ℝ → ℂ) τ‖ := by
  rw [cglLogFourierAmplitudeDerivativeOrder_fourier, norm_mul, norm_pow]
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  norm_num [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  ring

theorem norm_fourier_cglLogFourierAmplitudeDerivativeOrder_le_integral (w : CGLSmoothBump)
    (n : ℕ) (xi τ : ℝ) :
    ‖𝓕 (cglLogFourierAmplitudeDerivativeOrder n w xi : ℝ → ℂ) τ‖ ≤
      ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖ := by
  have h := cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget
    (cglLogFourierAmplitudeDerivativeOrder n w xi) 0 τ
  rw [pow_zero, one_mul,
    show cglSchwartzFourierDecayBudget (cglLogFourierAmplitudeDerivativeOrder n w xi) 0 =
      ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖ by
        simp [cglSchwartzFourierDecayBudget]] at h
  exact h

theorem cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay_linear
    (w : CGLSmoothBump) (n : ℕ) (t xi : ℝ) :
    |t| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w n * (1 + |xi|) ^ n := by
  have hpos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let a : ℝ := 2 * Real.pi
  have ha : a = 2 * Real.pi := rfl
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact ne_of_gt hpos
  have hscale : (2 * Real.pi) ^ n * (|t| / (2 * Real.pi)) ^ n = |t| ^ n := by
    rw [← ha, div_pow]
    field_simp [ha0]
  calc
    |t| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖ =
        (2 * Real.pi) ^ n *
          (|t / (2 * Real.pi)| ^ n *
            ‖𝓕 (cglLogFourierAmplitude w xi) (t / (2 * Real.pi))‖) := by
      rw [cglSmoothBumpHt_fourier_eq_logFourier, abs_div, abs_of_pos hpos]
      simpa [mul_assoc] using congrArg (fun z : ℝ => z *
        ‖𝓕 (cglLogFourierAmplitude w xi) (t / (2 * Real.pi))‖) hscale.symm
    _ = ‖𝓕 (cglLogFourierAmplitudeDerivativeOrder n w xi : ℝ → ℂ)
          (t / (2 * Real.pi))‖ :=
      norm_cglLogFourierAmplitudeDerivativeOrder_fourier w n xi (t / (2 * Real.pi))
    _ ≤ ∫ u : ℝ, ‖cglLogFourierAmplitudeDerivativeOrder n w xi u‖ :=
      norm_fourier_cglLogFourierAmplitudeDerivativeOrder_le_integral w n xi _
    _ ≤ cglLogFourierAmplitudeAllOrderBudget w n * (1 + |xi|) ^ n :=
      integral_norm_cglLogFourierAmplitudeDerivativeOrder_le w n xi

/-- The complete reciprocal-parameter family in CGL Lemma 4.3. -/
theorem cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay
    (w : CGLSmoothBump) (n : ℕ) (t xi : ℝ) :
    |t| ^ n * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) xi‖ ≤
      cglLogFourierAmplitudeAllOrderBudget w n * (1 + |xi|) ^ n :=
  cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay_linear w n t xi

end RHTower
