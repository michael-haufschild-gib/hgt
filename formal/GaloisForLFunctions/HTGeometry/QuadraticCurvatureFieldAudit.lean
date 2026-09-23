import GaloisForLFunctions.HTGeometry.RadialPolynomialGravity

/-!
# A constant-curvature audit of the quadratic field equations

Source: https://arxiv.org/html/2608.23600v1, equations (6), (9), (13), (26).
For f(r)=1-c r², actual radial differentiation gives R=-12c and
8πρ_GR=3c=-R/4. Curvature derivatives vanish at every positive radius.
The n=2 specialization of (6) therefore cancels the algebraic correction,
whereas the printed minus sign in (26) leaves -βR² in the scaled density.

This is a consistency audit of the paper's scalar formulas, not a formalization
of its full tensor variation or a claim about its numerical results. The
positive survivor is exact quadratic-curvature cancellation on this family.
The regular radial inverse transports the discrepancy to a spurious quadratic
metric term. All theorem parameters are unrestricted data.
-/
noncomputable section
open Polynomial Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Actual scalar curvature has zero derivative on every positive core radius. -/
theorem quadraticCoreRicci_hasDerivAt (c t : ℝ) :
    HasDerivAt (radialRicciScalar (quadraticCoreMetric c)) 0 (Real.exp t) := by
  apply (hasDerivAt_const (Real.exp t) (-12 * c)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (Real.exp_pos t)] with r hr
  have h := quadraticCoreMetric_ricci c (Real.log r)
  simpa only [Real.exp_log hr] using h

theorem quadraticCoreRicci_derivative (c t : ℝ) :
    deriv (radialRicciScalar (quadraticCoreMetric c)) (Real.exp t) = 0 :=
  (quadraticCoreRicci_hasDerivAt c t).deriv

/-- The second curvature derivative also vanishes, including at any positive horizon. -/
theorem quadraticCoreRicci_second_derivative (c t : ℝ) :
    deriv (deriv (radialRicciScalar (quadraticCoreMetric c))) (Real.exp t) = 0 := by
  have h : HasDerivAt (deriv (radialRicciScalar (quadraticCoreMetric c))) 0 (Real.exp t) := by
    apply (hasDerivAt_const (Real.exp t) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (Real.exp_pos t)] with r hr
    have he := quadraticCoreRicci_derivative c (Real.log r)
    simpa only [Real.exp_log hr] using he
  exact h.deriv

/-- The mixed tt constant-curvature specialization of equation (6), scaled by 8π. -/
def quadraticCoreFieldTT (c β r : ℝ) : ℝ :=
  (1 + 2 * β * radialRicciScalar (quadraticCoreMetric c) r) *
      (8 * Real.pi * radialEinsteinDensity (quadraticCoreMetric c) r) +
    β * radialRicciScalar (quadraticCoreMetric c) r ^ (2 : ℕ) / 2

/-- Equation (26), transcribed with actual derivatives and its printed minus sign. -/
def quadraticAppendixTT (f : ℝ → ℝ) (β r : ℝ) : ℝ :=
  deriv (fun s => s * (1 - f s)) r / r ^ (2 : ℕ) * (1 + 2 * β * radialRicciScalar f r) -
    2 * β * f r * ((2 / r + deriv f r / (2 * f r)) * deriv (radialRicciScalar f) r +
      deriv (deriv (radialRicciScalar f)) r) - β * radialRicciScalar f r ^ (2 : ℕ) / 2

/-- The quadratic correction from the general field equation cancels identically. -/
theorem quadraticCoreFieldTT_cancellation (c β t : ℝ) :
    quadraticCoreFieldTT c β (Real.exp t) = 3 * c := by
  unfold quadraticCoreFieldTT
  rw [quadraticCoreMetric_ricci, quadraticCoreMetric_density]
  field_simp
  ring

/-- Differentiating r(1-f) directly recovers the core density numerator. -/
theorem quadraticCoreMetric_mass_derivative (c r : ℝ) :
    deriv (fun s => s * (1 - quadraticCoreMetric c s)) r = 3 * c * r ^ (2 : ℕ) := by
  have h := (hasDerivAt_id r).mul ((quadraticCoreMetric_hasDerivAt c r).const_sub 1)
  simp only [Pi.mul_def, id_eq] at h
  rw [h.deriv]
  simp only [one_mul, quadraticCoreMetric]
  ring

/-- The printed appendix retains a correction incompatible with equation (6). -/
theorem quadraticAppendixTT_core (c β t : ℝ) :
    quadraticAppendixTT (quadraticCoreMetric c) β (Real.exp t) = 3 * c - 144 * β * c ^ (2 : ℕ) := by
  unfold quadraticAppendixTT
  rw [quadraticCoreMetric_mass_derivative, quadraticCoreMetric_ricci,
    quadraticCoreRicci_derivative, quadraticCoreRicci_second_derivative]
  simp only [mul_zero, add_zero, sub_zero]
  field_simp
  ring

/-- The exact discrepancy is minus βR², in the density scaled by 8π. -/
theorem quadraticAppendixTT_discrepancy (c β t : ℝ) :
    quadraticAppendixTT (quadraticCoreMetric c) β (Real.exp t) -
      quadraticCoreFieldTT c β (Real.exp t) = -β * (-12 * c) ^ (2 : ℕ) := by
  rw [quadraticAppendixTT_core, quadraticCoreFieldTT_cancellation]
  ring

/-- A closed nondegenerate family witnesses strict disagreement of the two printed formulas. -/
theorem quadraticAppendixTT_strict_disagreement (k b t : ℝ) :
    quadraticAppendixTT (quadraticCoreMetric (Real.exp k)) (Real.exp b) (Real.exp t) <
      quadraticCoreFieldTT (Real.exp k) (Real.exp b) (Real.exp t) := by
  rw [quadraticAppendixTT_core, quadraticCoreFieldTT_cancellation]
  have h : 0 < 144 * Real.exp b * Real.exp k ^ (2 : ℕ) := by positivity
  linarith

/-- Full degeneracy classification for agreement, rather than a single counterexample. -/
theorem quadraticAppendixTT_agreement_iff (c β t : ℝ) :
    quadraticAppendixTT (quadraticCoreMetric c) β (Real.exp t) =
      quadraticCoreFieldTT c β (Real.exp t) ↔ β = 0 ∨ c = 0 := by
  rw [quadraticAppendixTT_core, quadraticCoreFieldTT_cancellation]
  constructor
  · intro h
    have hz : β * c ^ (2 : ℕ) = 0 := by linarith
    rcases mul_eq_zero.mp hz with hb | hc
    · exact Or.inl hb
    · exact Or.inr (sq_eq_zero_iff.mp hc)
  · rintro (rfl | rfl) <;> ring

/-- Actual first-order density source extracted from the appendix on a constant core. -/
theorem quadraticAppendixTT_source (c t : ℝ) :
    deriv (fun β => quadraticAppendixTT (quadraticCoreMetric c) β (Real.exp t) / (8 * Real.pi)) 0 =
      -18 * c ^ (2 : ℕ) / Real.pi := by
  have he : (fun β => quadraticAppendixTT (quadraticCoreMetric c) β (Real.exp t) / (8 * Real.pi)) =
      (fun β => (3 * c - 144 * β * c ^ (2 : ℕ)) / (8 * Real.pi)) := by
    funext β
    rw [quadraticAppendixTT_core]
  rw [he]
  have h := ((((hasDerivAt_id (0 : ℝ)).const_mul 144).mul_const (c ^ (2 : ℕ))).const_sub (3 * c)).div_const (8 * Real.pi)
  simp only [id_eq] at h
  rw [h.deriv]
  field_simp
  ring

/-- The source extracted from the general equation is identically zero on the same cores. -/
theorem quadraticCoreFieldTT_source (c t : ℝ) :
    deriv (fun β => quadraticCoreFieldTT c β (Real.exp t) / (8 * Real.pi)) 0 = 0 := by
  have he : (fun β => quadraticCoreFieldTT c β (Real.exp t) / (8 * Real.pi)) =
      (fun _ => 3 * c / (8 * Real.pi)) := by
    funext β
    rw [quadraticCoreFieldTT_cancellation]
  rw [he]
  simp

/-- The integral inverse exposes the metric correction produced by the inconsistent sign. -/
theorem quadraticAppendix_radial_correction (c : ℝ) :
    radialPolynomialCorrection (C (-18 * c ^ (2 : ℕ) / Real.pi)) = C (-48 * c ^ (2 : ℕ)) * X ^ (2 : ℕ) := by
  rw [radialPolynomialCorrection_constant]
  congr 2
  field_simp
  ring

/-- Positive survivor: the correct constant-core source produces no first-order metric term. -/
theorem quadraticCoreField_radial_correction :
    radialPolynomialCorrection (C (0 : ℝ)) = 0 := by
  rw [radialPolynomialCorrection_constant]
  simp

/-- The appendix's extra quadratic term changes scalar curvature by a fixed exact amount. -/
theorem quadraticAppendix_radial_curvature_shift (c β t : ℝ) :
    radialRicciScalar
        (radialCorrectedMetric (quadraticCoreMetric c) (C (-18 * c ^ (2 : ℕ) / Real.pi)) β) (Real.exp t) =
      -12 * c - 576 * β * c ^ (2 : ℕ) := by
  rw [quadraticCoreMetric_correction_ricci]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
