import GaloisForLFunctions.SelbergClass.Primon.SemicircleBetaLaw
import GaloisForLFunctions.SelbergClass.Primon.KestenEdgeExpansion
import GaloisForLFunctions.HTGeometry.KLFactorizationSufficiency
import Mathlib.Topology.Order.ProjIcc

/-!
# The prime square law is a rational beta deformation

The squared Hecke coordinate has the beta law `Beta(1/2,3/2)` reweighted
by `M/(1+4a(1-u))`. The weight is extended continuously off `[0,1]` by
projection; its values there have no effect on the measure identity.
-/

open MeasureTheory ProbabilityTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Positive rational beta weight, continuously extended from the unit interval. -/
def kestenBetaWeight (p : Nat.Primes) (u : ℝ) : ℝ :=
  kestenEdgeScale p / (1 + 4 * kestenEdgeSlope p *
    (1 - (Set.projIcc (0 : ℝ) 1 (by norm_num) u : ℝ)))

private theorem betaWeight_denominator_pos (p : Nat.Primes) (u : ℝ) :
    0 < 1 + 4 * kestenEdgeSlope p *
      (1 - (Set.projIcc (0 : ℝ) 1 (by norm_num) u : ℝ)) := by
  have h := (Set.projIcc (0 : ℝ) 1 (by norm_num) u).property.2
  have hn := mul_nonneg
    (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (kestenEdgeSlope_pos p).le)
    (sub_nonneg.mpr h)
  linarith only [hn]

/-- The rational beta weight is globally continuous. -/
theorem continuous_kestenBetaWeight (p : Nat.Primes) : Continuous (kestenBetaWeight p) := by
  unfold kestenBetaWeight
  apply Continuous.div continuous_const
  · exact continuous_const.add ((continuous_const.mul continuous_const).mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_projIcc)))
  · intro u
    exact (betaWeight_denominator_pos p u).ne'

/-- The rational beta weight is strictly positive. -/
theorem kestenBetaWeight_pos (p : Nat.Primes) (u : ℝ) : 0 < kestenBetaWeight p u :=
  div_pos (kestenEdgeScale_pos p) (betaWeight_denominator_pos p u)

/-- On its support the weight has the explicit rational form. -/
theorem kestenBetaWeight_on_unit (p : Nat.Primes) (u : Icc (0 : ℝ) 1) :
    kestenBetaWeight p u = kestenEdgeScale p / (1 + 4 * kestenEdgeSlope p * (1 - (u : ℝ))) := by
  unfold kestenBetaWeight
  rw [Set.projIcc_of_mem _ u.property]

/-- The beta weight is bounded by the endpoint density ratio. -/
theorem kestenBetaWeight_le (p : Nat.Primes) (u : ℝ) :
    kestenBetaWeight p u ≤ kestenEdgeScale p := by
  unfold kestenBetaWeight
  apply (div_le_iff₀ (betaWeight_denominator_pos p u)).2
  have h := (Set.projIcc (0 : ℝ) 1 (by norm_num) u).property.2
  have hn : 0 ≤ kestenEdgeScale p * (4 * kestenEdgeSlope p *
      (1 - (Set.projIcc (0 : ℝ) 1 (by norm_num) u : ℝ))) := by
    exact mul_nonneg (kestenEdgeScale_pos p).le
      (mul_nonneg (mul_nonneg (by norm_num) (kestenEdgeSlope_pos p).le) (sub_nonneg.mpr h))
  nlinarith only [hn]

private theorem phaseHecke_mem (t : ℝ) : 2 * Real.cos (Real.pi * t) ∈ Icc (-2 : ℝ) 2 := by
  constructor
  · linarith only [Real.neg_one_le_cos (Real.pi * t)]
  · linarith only [Real.cos_le_one (Real.pi * t)]

/-- The rational beta weight pulls back to the exact prime-to-semicircle density ratio. -/
theorem kestenBetaWeight_phase (p : Nat.Primes) (t : ℝ) :
    semicirclePhaseDensity t * kestenBetaWeight p
      (heckeSquareCoordinate (2 * Real.cos (Real.pi * t))) = kestenMcKayDensity p t := by
  have hu := heckeSquareCoordinate_mem ⟨_, phaseHecke_mem t⟩
  have hw := kestenBetaWeight_on_unit p ⟨_, hu⟩
  change kestenBetaWeight p (heckeSquareCoordinate (2 * Real.cos (Real.pi * t))) = _ at hw
  rw [hw]
  have hd : 0 < 1 + kestenEdgeSlope p * phaseEdgeGap t := by
    have := kestenEdgeSlope_pos p
    have := phaseEdgeGap_nonneg t
    positivity
  have he : 1 + 4 * kestenEdgeSlope p *
      (1 - heckeSquareCoordinate (2 * Real.cos (Real.pi * t))) =
      1 + kestenEdgeSlope p * phaseEdgeGap t := by
    unfold heckeSquareCoordinate phaseEdgeGap
    ring
  rw [he]
  rw [← mul_div_assoc]
  apply (div_eq_iff hd.ne').2
  nlinarith only [kestenDensity_edge_identity p t]

/-- Actual probability law of the normalized square of the prime Hecke coordinate. -/
def kestenSquareLaw (p : Nat.Primes) : ProbabilityMeasure ℝ :=
  (kestenSpectralLaw p).map continuous_heckeSquareCoordinate.measurable.aemeasurable

/-- The prime spectral law is obtained by a likelihood ratio depending only on the square. -/
theorem kestenSpectralLaw_eq_semicircle_withDensity (p : Nat.Primes) :
    (kestenSpectralLaw p : Measure ℝ) = (semicircleSpectralLaw : Measure ℝ).withDensity
      ((fun u => ENNReal.ofReal (kestenBetaWeight p u)) ∘ heckeSquareCoordinate) := by
  change Measure.map (fun t => 2 * Real.cos (Real.pi * t))
    ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (kestenMcKayDensity p t))) =
    (Measure.map (fun t => 2 * Real.cos (Real.pi * t))
      ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal (semicirclePhaseDensity t)))).withDensity _
  rw [← map_withDensity_comp _ (by fun_prop)
      ((continuous_kestenBetaWeight p).measurable.ennreal_ofReal.comp
        continuous_heckeSquareCoordinate.measurable),
    ← withDensity_mul _ (by unfold semicirclePhaseDensity; fun_prop) (by
      exact (continuous_kestenBetaWeight p).measurable.ennreal_ofReal.comp
        (continuous_heckeSquareCoordinate.measurable.comp (by fun_prop)))]
  congr 1
  apply withDensity_congr_ae
  exact Eventually.of_forall fun t => by
    change ENNReal.ofReal (kestenMcKayDensity p t) =
      ENNReal.ofReal (semicirclePhaseDensity t) * ENNReal.ofReal
        (kestenBetaWeight p (heckeSquareCoordinate (2 * Real.cos (Real.pi * t))))
    rw [← ENNReal.ofReal_mul (show 0 ≤ semicirclePhaseDensity t by
      unfold semicirclePhaseDensity; positivity), kestenBetaWeight_phase]

/-- Exact measure identity: the prime square law is a positive rational beta deformation. -/
theorem kestenSquareLaw_eq_beta_withDensity (p : Nat.Primes) :
    (kestenSquareLaw p : Measure ℝ) = (betaMeasure (1 / 2) (3 / 2)).withDensity
      (fun u => ENNReal.ofReal (kestenBetaWeight p u)) := by
  change Measure.map heckeSquareCoordinate (kestenSpectralLaw p : Measure ℝ) = _
  rw [kestenSpectralLaw_eq_semicircle_withDensity,
    map_withDensity_comp _ continuous_heckeSquareCoordinate.measurable
      (continuous_kestenBetaWeight p).measurable.ennreal_ofReal]
  change (semicircleSquareLaw : Measure ℝ).withDensity _ = _
  rw [semicircleSquareLaw_eq_beta]

end
end GaloisForLFunctions.SelbergClass.Primon
