import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation

/-!
# Measurable P-G194 pairing colligation

The polarized Burnol aperture identity only uses continuity to obtain
measurability of its cross pairing.  This module exposes the exact L² form
needed by literal finite interval ports.
-/

open Complex Matrix Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cross-pairing integrability on the P half-line from the exact measurable L² hypotheses.
This is the only analytic input in P-G194 formerly supplied by continuity. -/
theorem integrableOn_star_mul_of_integrableOn_norm_sq_of_aestronglyMeasurable
    {f g : ℝ → ℂ}
    (hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0))
    (hg : IntegrableOn (fun u : ℝ => ‖g u‖ ^ (2 : ℕ)) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => star (f u) * g u) (Ioi 0) := by
  apply Integrable.mono' (hf.add hg)
  · exact hfmeas.star.mul hgmeas
  · filter_upwards with u
    change ‖star (f u) * g u‖ ≤ ‖f u‖ ^ (2 : ℕ) + ‖g u‖ ^ (2 : ℕ)
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖f u‖ - ‖g u‖), norm_nonneg (f u), norm_nonneg (g u)]

/-- Measurable L² form of P-G194.  It is the same literal three-channel identity as the
continuous theorem, with no density approximation and no change to its source pairing. -/
theorem routePBurnolApertureDamping_pairing_colligation_of_aestronglyMeasurable
    {c : ℝ} (hc : 0 ≤ c) {f g : ℝ → ℂ}
    (hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0))
    (hg : IntegrableOn (fun u : ℝ => ‖g u‖ ^ (2 : ℕ)) (Ioi 0)) :
    routePBurnolHalfLinePairing
        (routePBurnolForwardDampingShift c f)
        (routePBurnolForwardDampingShift c g) +
      routePBurnolHalfLinePairing
        (routePBurnolApertureBoundaryDefect c f)
        (routePBurnolApertureBoundaryDefect c g) +
      routePBurnolHalfLinePairing
        (routePBurnolApertureTailDefect c f)
        (routePBurnolApertureTailDefect c g) =
      routePBurnolHalfLinePairing f g := by
  let h : ℝ → ℂ := fun u => star (f u) * g u
  have hpair : IntegrableOn h (Ioi 0) :=
    integrableOn_star_mul_of_integrableOn_norm_sq_of_aestronglyMeasurable
      hfmeas hgmeas hf hg
  have hsubset : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hu))
  have hhead : IntegrableOn h (Ioc 0 c) := hpair.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn h (Ioi c) := hpair.mono_set hsubset
  have htransport : IntegrableOn
      (fun u : ℝ => (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) (Ioi c) := by
    apply Integrable.mono' htail.norm
    · have hweight : Measurable (fun u : ℝ => (((u - c) / u) ^ (2 : ℕ) : ℂ)) := by
        fun_prop
      exact hweight.aestronglyMeasurable.restrict.mul htail.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul]
      rw [norm_pow, Complex.norm_div, ← ofReal_sub,
        norm_real, norm_real, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr (mem_Ioi.mp hu)),
        Real.norm_eq_abs,
        abs_of_pos (lt_of_le_of_lt hc (mem_Ioi.mp hu))]
      have hw := routePBurnolApertureTailRatio_sq_le_one hc (mem_Ioi.mp hu)
      exact mul_le_of_le_one_left (norm_nonneg _) hw
  have hdefect : IntegrableOn
      (fun u : ℝ => (routePBurnolApertureTailDefectWeight c u : ℂ) * h u)
      (Ioi c) := by
    apply Integrable.mono' htail.norm
    · have hweight : Measurable
          (fun u : ℝ => (routePBurnolApertureTailDefectWeight c u : ℂ)) := by
        dsimp [routePBurnolApertureTailDefectWeight]
        fun_prop
      exact hweight.aestronglyMeasurable.restrict.mul htail.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hw0 := routePBurnolApertureTailDefectWeight_nonneg hc (mem_Ioi.mp hu)
      have hw1 := routePBurnolApertureTailDefectWeight_le_one hc (mem_Ioi.mp hu)
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      exact mul_le_of_le_one_left (norm_nonneg _) hw1
  have htailComplete :
      (∫ u : ℝ in Ioi c, (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) +
          ∫ u : ℝ in Ioi c,
            (routePBurnolApertureTailDefectWeight c u : ℂ) * h u =
        ∫ u : ℝ in Ioi c, h u := by
    rw [← integral_add htransport hdefect]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [routePBurnolApertureTailDefectWeight]
    push_cast
    ring
  have hsplit :
      (∫ u : ℝ in Ioc 0 c, h u) + ∫ u : ℝ in Ioi c, h u =
        ∫ u : ℝ in Ioi 0, h u := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail,
      Ioc_union_Ioi_eq_Ioi hc]
  rw [routePBurnolHalfLinePairing_forwardDampingShift_eq_tail hc,
    routePBurnolHalfLinePairing_boundaryDefect,
    routePBurnolHalfLinePairing_tailDefect hc,
    routePBurnolHalfLinePairing]
  change (∫ u : ℝ in Ioi c, (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) +
      (∫ u : ℝ in Ioc 0 c, h u) +
      (∫ u : ℝ in Ioi c,
        (routePBurnolApertureTailDefectWeight c u : ℂ) * h u) =
    ∫ u : ℝ in Ioi 0, h u
  calc
    _ = (∫ u : ℝ in Ioc 0 c, h u) +
        ((∫ u : ℝ in Ioi c, (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) +
          ∫ u : ℝ in Ioi c,
            (routePBurnolApertureTailDefectWeight c u : ℂ) * h u) := by ring
    _ = (∫ u : ℝ in Ioc 0 c, h u) + ∫ u : ℝ in Ioi c, h u := by
      rw [htailComplete]
    _ = ∫ u : ℝ in Ioi 0, h u := hsplit

end

end RHTower
