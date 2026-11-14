import GaloisForLFunctions.ConjugateDiagonalGeometry.GaussianZeroCopies
import GaloisForLFunctions.ConjugateDiagonalGeometry.GaussianCompensationKernel
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# Local off-line compensation for a large critical multiplicity

A critical atom contributes its full multiplicity to a centered Gaussian.
Negative contributions must lie off the critical line. The Gaussian tail is
controlled by the actual Lorentzian zero mass, leaving finitely many nearby
copies at a definite horizontal depth.
-/

open Complex Filter Topology Set
noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open RiemannGaussian _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-- The exact finite compensation inequality at a critical zero. All copies
on the right are actual zeta zeros with their analytic multiplicities. -/
theorem exists_gaussian_compensating_copies (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re = 1 / 2) {ε R : ℝ} (hε : 1 ≤ ε) (hR : 0 < R) :
    ∃ F : Finset (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity),
      (∀ q ∈ F, |q.1.1.im - ρ.1.im| ≤ R ∧
        Real.pi / (4 * ε * R) ≤ |q.1.1.re - 1 / 2|) ∧
      (analyticZetaZeroMultiplicity ρ : ℝ) ≤
        canonicalZetaGaussianZeroSum ε ρ.1.im + Real.exp (9 * ε / 64) * F.card +
          (2 * Real.exp (9 * ε / 64) * Real.exp (-(ε * R ^ 2 / 2))) * lorentzMass ρ.1.im := by
  classical
  have hε0 : 0 < ε := by linarith only [hε]
  let g (q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) : ℝ :=
    offAxisSingleContribution ε ρ.1.im q.1.1.im (1 / 2 - q.1.1.re)
  let w (q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) : ℝ :=
    1 / (1 + (ρ.1.im - q.1.1.im) ^ 2)
  let A : ℝ := Real.exp (9 * ε / 64)
  let κ : ℝ := 2 * A * Real.exp (-(ε * R ^ 2 / 2))
  have hA : 0 < A := Real.exp_pos _
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hw0 (q) : 0 ≤ w q := by dsimp [w]; positivity
  have hsum : HasSum g (canonicalZetaGaussianZeroSum ε ρ.1.im) := by
    simpa only [g, gaussianZeroSummand_re, Complex.ofReal_re] using
      Complex.hasSum_re (representsCanonicalZetaGaussianZeroSum_unconditional ε ρ.1.im hε0)
  have hw : Summable w := summable_gaussianZeroLorentz ρ.1.im
  let target : Finset (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :=
    ({ρ} : Finset NontrivialZetaZero).sigma
      (fun σ => (Finset.univ : Finset (Fin (analyticZetaZeroMultiplicity σ))))
  have htarget : target.card = analyticZetaZeroMultiplicity ρ := by simp [target]
  have hcenter (q) (hq : q ∈ target) : g q = 1 := by
    have hqρ : q.1 = ρ := Finset.mem_singleton.mp (Finset.mem_sigma.mp hq).1
    simp only [g, hqρ, hρ, offAxisSingleContribution, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero, Real.exp_zero, Real.cos_zero, mul_one]
  have hfinite := finite_gaussianZeroCopies_near ρ.1.im hR.le
  let bad := hfinite.toFinset.filter (fun q => g q < 0)
  have hbad (q) : q ∈ bad ↔ |q.1.1.im - ρ.1.im| ≤ R ∧ g q < 0 := by
    simp only [bad, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have henv (q) : |g q| ≤ A * Real.exp (-ε * (q.1.1.im - ρ.1.im) ^ 2) := by
    have hs := riemannZeta_zero_mem_quasiRH_strip q.1.zero_lt_re q.1.2.1
    have hd : |1 / 2 - q.1.1.re| ≤ 3 / 8 :=
      abs_le.mpr ⟨by linarith only [hs.2], by linarith only [hs.1]⟩
    exact abs_gaussianContribution_le_strip_envelope hε0.le hd ρ.1.im q.1.1.im
  have hglobal (q) : |g q| ≤ A := by
    have he : Real.exp (-ε * (q.1.1.im - ρ.1.im) ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by positivity)
    exact (henv q).trans (mul_le_of_le_one_right hA.le he)
  have htail (q) (hq : R ≤ |q.1.1.im - ρ.1.im|) : -κ * w q ≤ g q := by
    have he := gaussian_lorentz_tail_le hε hR.le hq
    have hb := (henv q).trans (mul_le_mul_of_nonneg_left he hA.le)
    have heq : A * ((2 * Real.exp (-(ε * R ^ 2 / 2))) /
        (1 + (q.1.1.im - ρ.1.im) ^ 2)) = κ * w q := by
      dsimp [κ, w]
      rw [sq_sub_comm ρ.1.im q.1.1.im]
      ring
    rw [heq] at hb
    simpa only [neg_mul] using (abs_le.mp hb).1
  have hpoint (q) : (if q ∈ target then (1 : ℝ) else 0) ≤
      g q + A * (if q ∈ bad then (1 : ℝ) else 0) + κ * w q := by
    have htw : 0 ≤ κ * w q := mul_nonneg hκ (hw0 q)
    by_cases ht : q ∈ target
    · rw [if_pos ht, hcenter q ht]
      split_ifs <;> nlinarith only [hA, htw]
    · rw [if_neg ht]
      by_cases hb : q ∈ bad
      · rw [if_pos hb, mul_one]
        have hg := (abs_le.mp (hglobal q)).1
        linarith only [hg, htw]
      · rw [if_neg hb, mul_zero, add_zero]
        by_cases hn : |q.1.1.im - ρ.1.im| ≤ R
        · have hg : 0 ≤ g q := le_of_not_gt (fun hneg => hb ((hbad q).mpr ⟨hn, hneg⟩))
          exact add_nonneg hg htw
        · have hg := htail q (le_of_lt (lt_of_not_ge hn))
          linarith only [hg]
  have hc := finite_gaussian_compensation_count target bad hsum.summable hw hpoint
  rw [htarget, hsum.tsum_eq, tsum_gaussianZeroLorentz] at hc
  refine ⟨bad, ?_, hc⟩
  intro q hq
  obtain ⟨hn, hneg⟩ := (hbad q).mp hq
  refine ⟨hn, ?_⟩
  have hd := gaussian_negative_depth_ge hε0 hR hn hneg
  simpa only [abs_sub_comm (1 / 2 : ℝ) q.1.1.re] using hd

end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.exists_gaussian_compensating_copies
