import GaloisForLFunctions.RHTower.DeningerArithmeticCompactOpen
import GaloisForLFunctions.RHTower.DeningerArithmeticJetDuality
import Mathlib.Topology.Sequences

/-!
# Continuous jets on the compact-open arithmetic source

Locally uniform convergence of holomorphic functions implies locally uniform convergence of every
fixed derivative.  Hence every point jet is a continuous linear functional on the compact-open
entire source.  At a Xi zero, jets below its analytic multiplicity annihilate the continuous Xi
differential.

These are the continuous local coordinates required for the conjectural jet-product
identification of reduced middle cohomology.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Every iterated derivative of a compact-open entire source is entire. -/
theorem deningerCompactOpenEntire_iteratedDeriv_differentiable
    (F : DeningerCompactOpenEntire) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k (F : ℂ → ℂ)) := by
  induction k with
  | zero =>
      rw [iteratedDeriv_zero]
      change Differentiable ℂ (F.1 : ℂ → ℂ)
      exact F.2
  | succ k hk =>
      rw [iteratedDeriv_succ]
      intro z
      have hderiv :=
        hk.differentiableOn.deriv isOpen_univ
      simpa only [differentiableWithinAt_univ] using
        hderiv z (Set.mem_univ z)

/--
Compact-open convergence of entire sources implies locally uniform convergence of every fixed
iterated derivative.
-/
theorem deningerCompactOpen_tendstoLocallyUniformly_iteratedDeriv
    {u : ℕ → DeningerCompactOpenEntire}
    {F : DeningerCompactOpenEntire}
    (hu : Tendsto u atTop (𝓝 F)) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun n z => iteratedDeriv k (u n : ℂ → ℂ) z)
      (iteratedDeriv k (F : ℂ → ℂ)) atTop Set.univ := by
  have huC :
      Tendsto (fun n => (u n).1) atTop (𝓝 F.1) :=
    (continuous_subtype_val.tendsto F).comp hu
  have hloc :
      TendstoLocallyUniformly
        (fun n z => u n z) F atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp huC
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using
        hloc.tendstoLocallyUniformlyOn
  | succ k hk =>
      have hdiff :
          ∀ᶠ n in atTop,
            DifferentiableOn ℂ
              (iteratedDeriv k (u n : ℂ → ℂ))
              Set.univ := by
        filter_upwards [] with n
        exact
          (deningerCompactOpenEntire_iteratedDeriv_differentiable
            (u n) k).differentiableOn
      have hnext := hk.deriv hdiff isOpen_univ
      simpa only [Function.comp_apply, iteratedDeriv_succ] using
        hnext

/-- A fixed point jet is continuous in the compact-open entire-source topology. -/
theorem continuous_deningerCompactOpenJet
    (alpha : ℂ) (k : ℕ) :
    Continuous
      (fun F : DeningerCompactOpenEntire =>
        iteratedDeriv k (F : ℂ → ℂ) alpha) := by
  rw [continuous_iff_seqContinuous]
  intro u F hu
  exact
    (deningerCompactOpen_tendstoLocallyUniformly_iteratedDeriv
      hu k).tendsto_at (Set.mem_univ alpha)

/-- Continuous `k`th jet evaluation at `alpha`. -/
def deningerCompactOpenJet (alpha : ℂ) (k : ℕ) :
    DeningerCompactOpenEntire →L[ℂ] ℂ where
  toLinearMap :=
    (deningerEntireJet alpha k).comp
      deningerCompactOpenEntireEquiv.toLinearMap
  cont := continuous_deningerCompactOpenJet alpha k

@[simp]
theorem deningerCompactOpenJet_apply
    (alpha : ℂ) (k : ℕ)
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenJet alpha k F =
      iteratedDeriv k (F : ℂ → ℂ) alpha :=
  rfl

/--
Every continuous jet below the Xi multiplicity annihilates the compact-open differential range.
-/
theorem deningerCompactOpenJet_XiMul_eq_zero
    (rho : XiDivisorSupport)
    {k : ℕ} (hk : k < xiSupportMultiplicity rho)
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenJet
        (xiSpectralPointSupport rho) k
        (deningerCompactOpenXiMul F) = 0 := by
  change
    deningerEntireJet
        (xiSpectralPointSupport rho) k
        (deningerCompactOpenEntireEquiv
          (deningerCompactOpenXiMul F)) = 0
  apply deningerEntireJet_eq_zero_of_mem_XiIdeal rho hk
  rw [deningerCompactOpenEntireEquiv_XiMul,
    deningerEntireXiIdeal, Ideal.mem_span_singleton']
  refine ⟨deningerCompactOpenEntireEquiv F, ?_⟩
  exact mul_comm _ _

end

end RHTower
