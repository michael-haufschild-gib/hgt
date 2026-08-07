import GaloisForLFunctions.RHTower.BurnolSoninContinuousEvaluation

/-!
# The aperture-head splitting of the completed Mellin evaluation

An element of the extended Sonine space is constant on its aperture head, so its right Mellin
integral splits into an explicit elementary head term and a tail integral over `(a, ∞)`.  The head
term is `c · a^(1-w)/(1-w)`: an elementary function of `w` whose only singularity is the simple pole
at `w = 1`.  The tail integral converges absolutely for `Re w > 1/2` by Cauchy–Schwarz against the
`L²` tail.

This is the starting identity of Burnol's continuation of the completed Mellin transform off the
strip: the head term is already meromorphic on the whole plane, so all the analytic work is carried
by the tail.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The Mellin integral of the aperture head is elementary, with its only singularity the simple
pole at `w = 1`. -/
theorem integral_Ioc_soninMellinKernel {w : ℂ} (hhi : w.re < 1) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioc (0 : ℝ) a, soninMellinKernel w t) = (a : ℂ) ^ (1 - w) / (1 - w) := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : (1 - w).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have hr : (-1 : ℝ) < (-w).re := by
    rw [Complex.neg_re]; linarith
  have hint : (∫ t in (0 : ℝ)..a, ((t : ℂ) ^ (-w))) =
      ((a : ℂ) ^ (-w + 1) - ((0 : ℝ) : ℂ) ^ (-w + 1)) / (-w + 1) :=
    integral_cpow (Or.inl hr)
  have hzero : ((0 : ℝ) : ℂ) ^ (-w + 1) = 0 := by
    rw [Complex.ofReal_zero, Complex.zero_cpow (by
      intro h
      exact hne (by linear_combination h))]
  rw [← intervalIntegral.integral_of_le ha.le]
  simp only [soninMellinKernel]
  rw [hint, hzero, sub_zero, show (-w + 1 : ℂ) = 1 - w from by ring]

/-- **The aperture-head splitting.**  On the strip the completed Mellin evaluation of an extended
Sonine vector is its explicit head term plus the tail integral. -/
theorem soninMellinEvaluation_head_tail {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a : ℝ} (ha : 0 < a) (f : soninExtendedSpace a) {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) a)),
      ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ) t = c) :
    soninMellinEvaluation w ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ) =
      mellinCompletionFactor w *
        (c * ((a : ℂ) ^ (1 - w) / (1 - w)) +
          ∫ t in Ioi a, ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ) t *
            soninMellinKernel w t) := by
  set g : ℝ → ℂ := ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ) with hg
  have hhead : IntegrableOn (fun t => g t * soninMellinKernel w t) (Ioc (0 : ℝ) a) :=
    integrableOn_head_mul_kernel hhi ha hc
  have htail : IntegrableOn (fun t => g t * soninMellinKernel w t) (Ioi a) :=
    integrableOn_tail_mul_kernel hlo ha
      (memLp_restrict_Ioi (((f : soninExtendedSpace a) : evenSubspace) : SoninL2))
  have hsplit : (∫ t in Ioi (0 : ℝ), g t * soninMellinKernel w t) =
      (∫ t in Ioc (0 : ℝ) a, g t * soninMellinKernel w t) +
        ∫ t in Ioi a, g t * soninMellinKernel w t := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail
  have hheadval : (∫ t in Ioc (0 : ℝ) a, g t * soninMellinKernel w t) =
      c * ((a : ℂ) ^ (1 - w) / (1 - w)) := by
    have hIoo : (∫ t in Ioc (0 : ℝ) a, g t * soninMellinKernel w t) =
        ∫ t in Ioo (0 : ℝ) a, g t * soninMellinKernel w t := by
      rw [← integral_Ioc_eq_integral_Ioo]
    have hIooc : (∫ t in Ioo (0 : ℝ) a, g t * soninMellinKernel w t) =
        ∫ t in Ioo (0 : ℝ) a, c * soninMellinKernel w t := by
      refine integral_congr_ae ?_
      filter_upwards [hc] with t ht
      rw [ht]
    rw [hIoo, hIooc, integral_const_mul, integral_Ioc_eq_integral_Ioo.symm,
      integral_Ioc_soninMellinKernel hhi ha]
  rw [soninMellinEvaluation, hsplit, hheadval]

end RHTower
