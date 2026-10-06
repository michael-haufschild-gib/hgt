import GaloisForLFunctions.RHTower.ChiPrimeGaussianProgressionProfile
import GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets

/-!
# Source-derived uniform jets for the complete moving prime profile

The original W(ξx)V(x)/(1+l log x) has uniformly bounded spatial jets on
the full physical parameter box. All regularity comes from its literal
factors; no derivative budget is assumed.
-/

noncomputable section

namespace RHTower

open Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower

private theorem parameter_jet_smooth (k : ℕ) {f : (ℝ × ℝ) → ℝ → ℂ}
    {z : (ℝ × ℝ) × ℝ} (hf : ContDiffAt ℝ ∞ (Function.uncurry f) z) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × ℝ => iteratedDeriv k (f w.1) w.2) z := by
  induction k with
  | zero =>
    change ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × ℝ => f w.1 w.2) z at hf
    simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    have hcomp : ContDiffAt ℝ ∞
        (fun w : ((ℝ × ℝ) × ℝ) × ℝ => iteratedDeriv k (f w.1.1) w.2) (z, z.2) :=
      ih.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun w : (ℝ × ℝ) × ℝ => fderiv ℝ (iteratedDeriv k (f w.1)) w.2) z :=
      hcomp.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedDeriv_succ, deriv] using hd.clm_apply
      (contDiffAt_const (c := (1 : ℝ)))

private theorem joint_profile_smooth (ξ : ℝ) {l x : ℝ}
    (hl : 0 ≤ l) (hx : 1 ≤ x) :
    ContDiffAt ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => primeGaussianScaledLogProfile z.1.1 z.1.2 z.2)
      ((ξ, l), x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hV : ContDiffAt ℝ ∞ smoothAFECutoff x :=
    BAGTrace.contDiffOn_smoothAFECutoff_infty_pos.contDiffAt (Ioi_mem_nhds hx0)
  have hW : ContDiffAt ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => (bagPhysicalHeightWindow (z.1.1 * z.2) : ℂ))
      ((ξ, l), x) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (bagPhysicalHeightWindow.contDiff.contDiffAt.comp _
        (contDiffAt_fst.fst.mul contDiffAt_snd))
  have hlog : ContDiffAt ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => Real.log z.2) ((ξ, l), x) :=
    contDiffAt_snd.log hx0.ne'
  have hden : ContDiffAt ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => ((1 + z.1.2 * Real.log z.2 : ℝ) : ℂ))
      ((ξ, l), x) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_const.add (contDiffAt_fst.snd.mul hlog))
  have hn : (1 + l * Real.log x : ℝ) ≠ 0 :=
    ne_of_gt (by nlinarith [mul_nonneg hl (Real.log_nonneg hx)])
  simpa only [primeGaussianScaledLogProfile, primeGaussianScaledProfile,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
    Pi.inv_apply, Function.comp_def] using
    (hW.mul (hV.comp _ contDiffAt_snd)).mul
      (hden.inv (Complex.ofReal_ne_zero.mpr hn))

/-- Every spatial jet of the literal moving logarithmic profile is smooth at
every physical point, including both sharp band endpoints. -/
theorem primeGaussianScaledLogProfile_jet_contDiffAt (k : ℕ) (ξ : ℝ)
    {l x : ℝ} (hl : 0 ≤ l) (hx : 1 ≤ x) :
    ContDiffAt ℝ ∞ (iteratedDeriv k (primeGaussianScaledLogProfile ξ l)) x := by
  have h := parameter_jet_smooth k
    (f := fun a : ℝ × ℝ => primeGaussianScaledLogProfile a.1 a.2)
    (joint_profile_smooth ξ hl hx)
  exact h.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- One source constant bounds each fixed jet over ALL original physical
ratios and logarithmic parameters. In particular the first TWO jets are paid. -/
theorem exists_primeGaussianScaledLogProfile_jet_bound (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ ∈ Icc (1 / 2 : ℝ) 2, ∀ l ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ Icc (1 : ℝ) 2,
        ‖iteratedDeriv k (primeGaussianScaledLogProfile ξ l) x‖ ≤ B := by
  have hc : ContinuousOn
      (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv k
        (primeGaussianScaledLogProfile z.1.1 z.1.2) z.2)
      ((Icc (1 / 2 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (1 : ℝ) 2) := by
    intro z hz
    exact (parameter_jet_smooth k
      (f := fun a : ℝ × ℝ => primeGaussianScaledLogProfile a.1 a.2)
      (joint_profile_smooth z.1.1 hz.1.2.1 hz.2.1)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max B 0 + 1, by positivity, fun ξ hξ l hl x hx => ?_⟩
  exact (hB ((ξ, l), x) ⟨⟨hξ, hl⟩, hx⟩).trans (by linarith [le_max_left B 0])

end RHTower
