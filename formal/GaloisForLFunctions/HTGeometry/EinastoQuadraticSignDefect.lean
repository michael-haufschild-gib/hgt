import GaloisForLFunctions.HTGeometry.QuadraticCurvatureFieldAudit
import GaloisForLFunctions.HTGeometry.EinastoEnergyConditions

/-!
# Where the quadratic algebraic sign defect disappears in an Einasto halo

The difference between the algebraic R² terms in equations (6) and (26) of
arXiv:2608.23600 is -βR². Apply that defect to the corpus's actual Einasto
scalar curvature. It vanishes at exactly one positive radius, precisely the
already formalized outer boundary of the dominant-energy region. This audits
that algebraic term; it does not identify the full tensor equation with the
appendix's derivative expression for a varying-curvature metric.
-/
noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The exact difference of the two printed algebraic quadratic-curvature terms. -/
def quadraticAlgebraicSignDefect (f : ℝ → ℝ) (β r : ℝ) : ℝ :=
  -β * radialRicciScalar f r ^ (2 : ℕ)

/-- The defect agrees with the full constant-core discrepancy already audited. -/
theorem quadraticAlgebraicSignDefect_core (c β t : ℝ) :
    quadraticAlgebraicSignDefect (quadraticCoreMetric c) β (Real.exp t) =
      quadraticAppendixTT (quadraticCoreMetric c) β (Real.exp t) -
        quadraticCoreFieldTT c β (Real.exp t) := by
  rw [quadraticAppendixTT_discrepancy]
  unfold quadraticAlgebraicSignDefect
  rw [quadraticCoreMetric_ricci]

/-- Identify the new radial functional with the existing actual Einasto curvature. -/
theorem radialRicciScalar_einasto (d l a t : ℝ) :
    radialRicciScalar (einastoMetric d l a) (Real.exp t) = einastoRadialRicci d l a (Real.exp t) := by
  unfold radialRicciScalar einastoRadialRicci
  field_simp
  ring

/-- Curvature is a positive density factor times a single strictly ordered radial factor. -/
theorem einastoRadialRicci_factored (d l a t : ℝ) :
    einastoRadialRicci d l a (Real.exp t) =
      (8 * Real.pi * einastoDensity d l a (Real.exp t)) *
        (Real.exp (-a + (t - l) * Real.exp (-a)) - 4) := by
  rw [einastoRadialRicci_eq, einastoSlope_exponential]
  ring

/-- The actual curvature has one positive-radius zero, independent of the density scale. -/
theorem einastoRadialRicci_zero_iff (d l a t : ℝ) :
    einastoRadialRicci d l a (Real.exp t) = 0 ↔
      t = einastoPressureThreshold l a (Real.log 4) := by
  rw [einastoRadialRicci_factored, mul_eq_zero]
  have hp : 8 * Real.pi * einastoDensity d l a (Real.exp t) ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) (einastoDensity_pos d l a (Real.exp t)))
  simp only [hp, false_or, sub_eq_zero]
  have he : Real.exp (-a + (t - l) * Real.exp (-a)) = 4 ↔
      -a + (t - l) * Real.exp (-a) = Real.log 4 := by
    constructor
    · intro h
      exact Real.exp_injective (h.trans (Real.exp_log (by norm_num : (0 : ℝ) < 4)).symm)
    · intro h
      rw [h, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [he, einastoPressureThreshold, Real.exp_neg]
  have ha := Real.exp_pos a
  constructor
  · intro h
    have hh := congrArg (fun x : ℝ => x * Real.exp a) h
    field_simp at hh
    nlinarith
  · intro h
    subst t
    field_simp
    ring

/-- Existing energy inequalities locate the complete nonpositive-curvature region. -/
theorem einastoRadialRicci_nonpos_iff (d l a t : ℝ) :
    einastoRadialRicci d l a (Real.exp t) ≤ 0 ↔
      t ≤ einastoPressureThreshold l a (Real.log 4) := by
  rw [← einasto_dominant_energy_iff_Ricci_nonpos, einastoTangential_dominant_energy_iff]

theorem einastoRadialRicci_negative_iff (d l a t : ℝ) :
    einastoRadialRicci d l a (Real.exp t) < 0 ↔
      t < einastoPressureThreshold l a (Real.log 4) := by
  rw [lt_iff_le_and_ne, einastoRadialRicci_nonpos_iff, ne_eq, einastoRadialRicci_zero_iff,
    ← lt_iff_le_and_ne]

theorem einastoRadialRicci_positive_iff (d l a t : ℝ) :
    0 < einastoRadialRicci d l a (Real.exp t) ↔
      einastoPressureThreshold l a (Real.log 4) < t := by
  rw [← not_le, einastoRadialRicci_nonpos_iff, not_le]

/-- Positive quadratic coupling makes the algebraic discrepancy nonpositive everywhere. -/
theorem einastoQuadraticSignDefect_nonpos (d l a b t : ℝ) :
    quadraticAlgebraicSignDefect (einastoMetric d l a) (Real.exp b) (Real.exp t) ≤ 0 := by
  unfold quadraticAlgebraicSignDefect
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos b).le) (sq_nonneg _)

/-- The discrepancy disappears exactly at the dominant-energy boundary. -/
theorem einastoQuadraticSignDefect_zero_iff (d l a b t : ℝ) :
    quadraticAlgebraicSignDefect (einastoMetric d l a) (Real.exp b) (Real.exp t) = 0 ↔
      t = einastoPressureThreshold l a (Real.log 4) := by
  unfold quadraticAlgebraicSignDefect
  rw [radialRicciScalar_einasto, mul_eq_zero]
  simp only [neg_ne_zero.mpr (Real.exp_ne_zero b), false_or, sq_eq_zero_iff]
  exact einastoRadialRicci_zero_iff d l a t

/-- Away from that single sphere, the discrepancy is strictly negative. -/
theorem einastoQuadraticSignDefect_negative_iff (d l a b t : ℝ) :
    quadraticAlgebraicSignDefect (einastoMetric d l a) (Real.exp b) (Real.exp t) < 0 ↔
      t ≠ einastoPressureThreshold l a (Real.log 4) := by
  rw [lt_iff_le_and_ne]
  simp only [einastoQuadraticSignDefect_nonpos, true_and, ne_eq, einastoQuadraticSignDefect_zero_iff]

/-- Core density fixes a nonzero limiting defect for every positive coupling and density. -/
theorem einastoQuadraticSignDefect_core_limit (d l a b : ℝ) :
    Tendsto (fun t => quadraticAlgebraicSignDefect (einastoMetric d l a) (Real.exp b) (Real.exp t))
      atBot (𝓝 (-Real.exp b * (-32 * Real.pi * Real.exp d) ^ (2 : ℕ))) := by
  have he : (fun t => quadraticAlgebraicSignDefect (einastoMetric d l a) (Real.exp b) (Real.exp t)) =
      (fun t => -Real.exp b * einastoRadialRicci d l a (Real.exp t) ^ (2 : ℕ)) := by
    funext t
    unfold quadraticAlgebraicSignDefect
    rw [radialRicciScalar_einasto]
  rw [he]
  exact ((einastoRadialRicci_core_limit d l a).pow 2).const_mul (-Real.exp b)

end GaloisForLFunctions.HTGeometry
