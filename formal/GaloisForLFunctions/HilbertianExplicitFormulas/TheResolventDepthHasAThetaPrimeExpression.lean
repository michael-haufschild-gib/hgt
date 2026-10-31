import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaReadingsRecoverCompactCurrents
import GaloisForLFunctions.HilbertianExplicitFormulas.TheXiResolventDepthIdentity
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap

/-!
# The resolvent depth as a theta–prime expression

A smooth source kernel agrees with `|4−ρ|⁻²` throughout the zero strip.
Compact cutoffs and finite integer theta prefixes recover its full divisor trace.
Both limits exist. The full depth is exactly seven halves of this source reading,
minus the archimedean logarithmic derivative, plus `Σ Λ(n)n⁻⁴`.
-/

open Complex Filter Topology MeasureTheory Set Metric RHTower Zeta23 ArithmeticFunction
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.ArithmeticElectrostatics

namespace GaloisForLFunctions.HilbertianExplicitFormulas

noncomputable section

/-- A smooth positive kernel equal to the squared Cauchy kernel throughout the zero strip. -/
def xiResolventSourceKernel (z : ℂ) : ℝ :=
  1 / (normSq (4 - z) + sourceCutoff 0 (z - 4))

private theorem kernel_denominator_pos (z : ℂ) :
    0 < normSq (4 - z) + sourceCutoff 0 (z - 4) := by
  by_cases hz : z = 4
  · subst z
    have h : sourceCutoff 0 (0 : ℂ) = 1 :=
      (sourceCutoff 0).one_of_mem_closedBall (by simp [sourceCutoff])
    simp only [sub_self, normSq_zero, h, zero_add, zero_lt_one]
  · exact add_pos_of_pos_of_nonneg
      (normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))) (sourceCutoff 0).nonneg

theorem contDiff_xiResolventSourceKernel : ContDiff ℝ 2 xiResolventSourceKernel := by
  have hnorm : ContDiff ℝ 2 (fun z : ℂ => normSq (4 - z)) := by
    simpa only [normSq_eq_norm_sq] using
      (ContDiff.norm_sq ℂ (contDiff_const.sub contDiff_id) :
        ContDiff ℝ 2 (fun z : ℂ => ‖4 - z‖ ^ 2))
  have hb : ContDiff ℝ 2 (fun z : ℂ => sourceCutoff 0 (z - 4)) :=
    (sourceCutoff 0).contDiff.comp (contDiff_id.sub contDiff_const)
  exact contDiff_const.div (hnorm.add hb) (fun z => (kernel_denominator_pos z).ne')

/-- The pole regularization is supported strictly to the right of the zero strip. -/
theorem xiResolventSourceKernel_eq_of_re_le_one {z : ℂ} (hz : z.re ≤ 1) :
    xiResolventSourceKernel z = 1 / normSq (4 - z) := by
  have hcut : sourceCutoff 0 (z - 4) = 0 := by
    apply (sourceCutoff 0).zero_of_le_dist
    rw [dist_zero_right]
    simp only [sourceCutoff, Nat.cast_zero, zero_add]
    have hn := (neg_le_abs (z - 4).re).trans (Complex.abs_re_le_norm (z - 4))
    norm_num [Complex.sub_re] at hn
    linarith only [hz, hn]
  simp only [xiResolventSourceKernel, hcut, add_zero]

private theorem summable_carrier_of_summable_copies {f : ℂ → ℝ}
    (hf : Summable (fun q : XiZeroCopy => f (q.1 : ℂ))) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * f ρ) := by
  apply xiDivisorZetaCarrierEquiv.summable_iff.mp
  refine hf.sigma.congr fun ρ => ?_
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

private theorem tsum_copies_eq_zetaSourceTrace {f : ℂ → ℝ}
    (hf : Summable (fun q : XiZeroCopy => f (q.1 : ℂ))) :
    (∑' q : XiZeroCopy, f (q.1 : ℂ)) = zetaSourceTrace f := by
  rw [hf.tsum_sigma, zetaSourceTrace, ← xiDivisorZetaCarrierEquiv.tsum_eq
    (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * f ρ)]
  apply tsum_congr
  intro ρ
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, xiDivisorZetaCarrierEquiv_multiplicity]
  rfl


/-- The smooth source weight is summable over the full multiplicity-exact Xi divisor. -/
theorem summable_xiResolventSourceKernel :
    Summable (fun q : XiZeroCopy => xiResolventSourceKernel (q.1 : ℂ)) := by
  refine (summable_xiSamePointResolvent (s := 4) (by norm_num)).congr fun q => ?_
  exact (xiResolventSourceKernel_eq_of_re_le_one (xiDivisorSupport_re_mem q.1).2.le).symm

theorem zetaSourceTrace_xiResolventSourceKernel :
    zetaSourceTrace xiResolventSourceKernel = xiSamePointResolvent 4 := by
  rw [← tsum_copies_eq_zetaSourceTrace summable_xiResolventSourceKernel,
    xiSamePointResolvent]
  exact tsum_congr fun q =>
    xiResolventSourceKernel_eq_of_re_le_one (xiDivisorSupport_re_mem q.1).2.le

/-- A finite integer theta-prefix reading with an independent compact source cutoff. -/
def xiResolventThetaReading (R n : ℕ) : ℝ :=
  finiteThetaSourceReading (fun z => sourceCutoff R z * xiResolventSourceKernel z) n

/-- Removing the theta regulator recovers the exact compact divisor trace. -/
theorem tendsto_xiResolventThetaReading (R : ℕ) :
    Tendsto (xiResolventThetaReading R) atTop
      (𝓝 (zetaSourceTrace (fun z => sourceCutoff R z * xiResolventSourceKernel z))) := by
  exact tendsto_finiteThetaSourceReading_compact _
    ((sourceCutoff R).contDiff.mul contDiff_xiResolventSourceKernel)
    (sourceCutoff R).hasCompactSupport.mul_right

/-- The compact source cutoffs exhaust the absolutely convergent same-point resolvent. -/
theorem tendsto_lim_xiResolventThetaReading :
    Tendsto (fun R : ℕ => atTop.limUnder (xiResolventThetaReading R)) atTop
      (𝓝 (xiSamePointResolvent 4)) := by
  have h := tendsto_cutoff_zetaSourceTrace xiResolventSourceKernel
    (summable_carrier_of_summable_copies summable_xiResolventSourceKernel)
  rw [zetaSourceTrace_xiResolventSourceKernel] at h
  exact h.congr fun R => (tendsto_xiResolventThetaReading R).limUnder_eq.symm

/-- The same-point reading defined entirely by finite theta prefixes and two limits. -/
def xiResolventThetaSamePoint : ℝ :=
  atTop.limUnder (fun R : ℕ => atTop.limUnder (xiResolventThetaReading R))

theorem xiResolventThetaSamePoint_eq :
    xiResolventThetaSamePoint = xiSamePointResolvent 4 :=
  tendsto_lim_xiResolventThetaReading.limUnder_eq

/-- Exact theta–prime expression for the full Xi depth at the real point four. -/
theorem xiResolventDepth_four_eq_thetaPrime :
    xiResolventDepth 4 = (7 / 2 : ℝ) * xiResolventThetaSamePoint -
      (logDeriv archFactor 4).re + ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-4 : ℝ) := by
  rw [xiResolventThetaSamePoint_eq]
  have h := xiResolventDepth_eq_samePoint_sub_arch_add_prime (s := 4) (by norm_num)
  norm_num at h ⊢
  exact h

theorem summable_vonMangoldt_four :
    Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-4 : ℝ)) :=
  summable_vonMangoldt_mul_rpow (by norm_num)

/-- The original same-point defect is the same theta–prime source expression. -/
theorem xiResolventDefect_four_eq_thetaPrime :
    (7 / 2 : ℝ) * xiSamePointResolvent 4 - (logDeriv xi 4).re =
      (7 / 2 : ℝ) * xiResolventThetaSamePoint - (logDeriv archFactor 4).re +
        ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-4 : ℝ) := by
  have h := sub_mul_xiSamePointResolvent_sub_logDeriv (s := 4) (by norm_num)
  norm_num at h
  exact h.trans xiResolventDepth_four_eq_thetaPrime

#print axioms xiResolventDepth_four_eq_thetaPrime
#print axioms xiResolventDefect_four_eq_thetaPrime

end

end GaloisForLFunctions.HilbertianExplicitFormulas
