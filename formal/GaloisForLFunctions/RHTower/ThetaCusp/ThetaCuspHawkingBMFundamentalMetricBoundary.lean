import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMetricSource

/-!
# Boundary coefficient of the actual fundamental scalar metric

The existing KI scalar reconstruction differentiates the physical master. Its
normalized angular metric therefore retains a nonzero boundary coefficient even
though the master vanishes. This module derives the exact coefficient, identifies
its physical radius branch, and classifies zero limits of an actual tensor component.

The result does not impose a gravitational boundary condition or retire the causal
route. Physical response admission must establish the required metric boundary data.
-/

open Complex Set Filter Topology
namespace RHTower.D4BMFundamentalMetricBoundary
open D4BMFundamentalMaster
noncomputable section

/-- Normalized scalar angular coefficient of the original KI reconstruction,
using the actual fundamental master and its actual first derivative. -/
def angularCoefficient (omega q z : ℂ) : ℂ :=
  2 * (d4KIScalarGaugeInvariantOrbitOfBMMaster (boundaryFactor z) z⁻¹ omega q
    ⟨master omega z, deriv (master omega) z, 0⟩).angularTrace

/-- The boundary factor is the square root fixed by the principal complex power. -/
theorem boundaryFactor_sq (z : ℂ) : boundaryFactor z ^ (2 : ℕ) = 1 - z := by
  simp [boundaryFactor, one_div]

/-- Exact finite boundary expression, derived from the existing metric orbit. -/
theorem angularCoefficient_eq (omega q z : ℂ) (hz : z ∈ Complex.slitPlane)
    (h1 : 1 - z ∈ Complex.slitPlane) :
    angularCoefficient omega q z = D4BMPhysicalMaster.factor omega z *
      ((q / 2 - Complex.I * omega) * (1 - z) - z) := by
  have hsq := boundaryFactor_sq z
  have hz0 := Complex.slitPlane_ne_zero hz
  have h10 := Complex.slitPlane_ne_zero h1
  rw [angularCoefficient, (master_hasDerivAt omega z hz h1).deriv]
  change 2 * (-(d4KIScalarMasslessTopologicalX _ _ _ _ _ +
    d4KIScalarMasslessTopologicalY _ _ _ _) / 4) = _
  dsimp [d4KIScalarMasslessTopologicalX, d4KIScalarMasslessTopologicalY,
    first, master, rate, d4BMIngoingHorizonExponent]
  rw [hsq]
  calc
    _ = D4BMPhysicalMaster.factor omega z * boundaryFactor z ^ (2 : ℕ) *
        (q / 2 + 2 * z * (-Complex.I * omega / 2 * z⁻¹ - 1/2*(1-z)⁻¹)) := by ring
    _ = _ := by
      rw [hsq]
      field_simp
      ring

/-- On the positive physical radius, the fixed boundary branch is exactly inverse radius. -/
theorem boundaryFactor_radius (r : ℝ) (hr : 0 < r) :
    boundaryFactor (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)) = (r : ℂ)⁻¹ := by
  have ha : ((r : ℂ)⁻¹).arg = 0 := by
    rw [← Complex.ofReal_inv]
    exact Complex.arg_ofReal_of_nonneg (inv_nonneg.mpr hr.le)
  simpa [boundaryFactor, one_div] using
    (Complex.pow_cpow_nat_inv (x := (r : ℂ)⁻¹) (n := 2) (by norm_num)
      (by rw [ha]; exact neg_lt_zero.mpr (by positivity)) (by rw [ha]; positivity))

/-- The boundary observable is the literal scalar orbit trace at physical radius. -/
theorem angularCoefficient_radius (omega q : ℂ) (r : ℝ) (hr : 0 < r) :
    angularCoefficient omega q (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)) =
      2 * (d4KIScalarGaugeInvariantOrbitOfBMMaster (r : ℂ)⁻¹
        (1 - (r : ℂ)⁻¹ ^ (2 : ℕ))⁻¹ omega q
        ⟨master omega (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)),
          deriv (master omega) (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)), 0⟩).angularTrace := by
  simp only [angularCoefficient, boundaryFactor_radius r hr]

/-- Exact normalization of an actual diagonal angular metric component. Both vector
amplitudes and all other tensor components remain in the original reconstruction. -/
theorem metric_angular_normalized (omega q aS aV : ℂ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ)
    (x : Fin 4 → ℝ) (hr : 0 < x 1) :
    (x 1 : ℂ)⁻¹ ^ (2 : ℕ) * D4BMMetricReconstruction.covariantMetric omega q
      (fun b => D4BMFundamentalMetric.primitives omega aS aV S V b x) 2 2 =
    aS * angularCoefficient omega q (D4BMMetricReconstruction.bmCoordinate x) *
      D4BMFundamentalMetric.horizonScale (D4BMMetricReconstruction.angularPoint x) *
      S (D4BMMetricReconstruction.angularPoint x) *
      Complex.exp (-Complex.I * omega * (x 0 : ℂ)) := by
  have hr0 : (x 1 : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold angularCoefficient D4BMMetricReconstruction.bmCoordinate
  rw [boundaryFactor_radius (x 1) hr]
  simp [D4BMMetricReconstruction.covariantMetric,
    D4BMMetricReconstruction.covariantMetricFromOrbits,
    D4BMFundamentalMetric.primitives, D4BMMetricReconstruction.primitiveFields,
    D4BMFundamentalMetric.horizonFields, deriv_const_mul_field,
    d4KIScalarGaugeInvariantOrbitOfBMMaster, d4KIScalarMasslessTopologicalX,
    d4KIScalarMasslessTopologicalY]
  unfold D4BMMetricReconstruction.bmCoordinate
  field_simp

private theorem real_domain (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (x : ℂ) ∈ Complex.slitPlane ∧ 1 - (x : ℂ) ∈ Complex.slitPlane := by
  constructor
  · simp only [Complex.mem_slitPlane_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact Or.inl hx.1
  · simp only [Complex.mem_slitPlane_iff, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    exact Or.inl (sub_pos.mpr hx.2)

/-- The reconstructed normalized scalar angular coefficient has limit minus one,
although the master itself has limit zero. -/
theorem angularCoefficient_limit (omega q : ℂ) :
    Tendsto (fun x : ℝ => angularCoefficient omega q (x : ℂ))
      (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 (-1)) := by
  have he : (fun x : ℝ => angularCoefficient omega q (x : ℂ)) =ᶠ[𝓝[Ioo (0 : ℝ) 1] 1]
      (fun x : ℝ => D4BMPhysicalMaster.factor omega (x : ℂ) *
        ((q / 2 - Complex.I * omega) * (1 - (x : ℂ)) - (x : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact angularCoefficient_eq omega q (x : ℂ) (real_domain x hx).1 (real_domain x hx).2
  have hc : ContinuousAt (fun x : ℝ => D4BMPhysicalMaster.factor omega (x : ℂ)) 1 :=
    ((D4BMPhysicalMaster.factor_contDiffAt omega 1
      (by simp [Complex.mem_slitPlane_iff]) 0).continuousAt).comp (f := fun x : ℝ => (x : ℂ))
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ)))
  have hp : ContinuousAt (fun x : ℝ => (q / 2 - Complex.I * omega) *
      (1 - (x : ℂ)) - (x : ℂ)) 1 := by fun_prop
  have ht := (hc.mul hp).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioo (0 : ℝ) 1))
  simpa [D4BMPhysicalMaster.factor] using ht.congr' he.symm

/-- A zero master boundary value does not imply a zero reconstructed angular limit. -/
theorem angularCoefficient_not_zero_limit (omega q : ℂ) :
    ¬ Tendsto (fun x : ℝ => angularCoefficient omega q (x : ℂ))
      (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  letI := right_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
  intro h
  have he := tendsto_nhds_unique (angularCoefficient_limit omega q) h
  norm_num at he

private theorem radius_coordinate_limit :
    Tendsto (fun r : ℝ => 1 - r⁻¹ ^ (2 : ℕ)) atTop (𝓝[Ioo (0 : ℝ) 1] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).pow 2)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hr0 := lt_trans zero_lt_one hr
    have hi := inv_pos.mpr hr0
    have hil : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
    constructor <;> nlinarith [sq_pos_of_pos hi]

/-- The orbit coefficient has the same nonzero limit at physical spatial infinity. -/
theorem angularCoefficient_radius_limit (omega q : ℂ) :
    Tendsto (fun r : ℝ => angularCoefficient omega q (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)))
      atTop (𝓝 (-1)) := by
  have h := (angularCoefficient_limit omega q).comp radius_coordinate_limit
  change Tendsto (fun r : ℝ => angularCoefficient omega q ((1 - r⁻¹ ^ (2 : ℕ) : ℝ) : ℂ))
    atTop (𝓝 (-1)) at h
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_inv] using h

/-- An actual static-coordinate ray with fixed time and angular coordinates. -/
def staticRay (tau : ℝ) (u : Fin 2 → ℝ) (r : ℝ) : Fin 4 → ℝ := ![tau, r, u 0, u 1]

private theorem staticRay_angular (tau : ℝ) (u : Fin 2 → ℝ) (r : ℝ) :
    D4BMMetricReconstruction.angularPoint (staticRay tau u r) = u := by
  ext i
  fin_cases i <;> simp [D4BMMetricReconstruction.angularPoint, staticRay]

/-- The actual normalized angular metric component retains its full nonzero leading
coefficient, including scalar amplitude, horizon metric, harmonic and time phase. -/
theorem metric_angular_limit (omega q aS aV : ℂ) (tau : ℝ) (u : Fin 2 → ℝ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ) :
    Tendsto (fun r : ℝ => (r : ℂ)⁻¹ ^ (2 : ℕ) *
      D4BMFundamentalMetric.perturbation omega q aS aV S V (staticRay tau u r) 2 2)
      atTop (𝓝 (-aS * D4BMFundamentalMetric.horizonScale u * S u *
        Complex.exp (-Complex.I * omega * (tau : ℂ)))) := by
  have he : (fun r : ℝ => (r : ℂ)⁻¹ ^ (2 : ℕ) *
      D4BMFundamentalMetric.perturbation omega q aS aV S V (staticRay tau u r) 2 2) =ᶠ[atTop]
      (fun r : ℝ => aS * angularCoefficient omega q (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)) *
        D4BMFundamentalMetric.horizonScale u * S u *
        Complex.exp (-Complex.I * omega * (tau : ℂ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have h := metric_angular_normalized omega q aS aV S V
      (staticRay tau u r) (by simpa [staticRay] using hr)
    rw [staticRay_angular] at h
    simpa [D4BMFundamentalMetric.perturbation, D4BMMetricReconstruction.bmCoordinate,
      staticRay] using h
  have ht := (((angularCoefficient_radius_limit omega q).const_mul aS).mul_const
    (D4BMFundamentalMetric.horizonScale u)).mul_const (S u) |>.mul_const
      (Complex.exp (-Complex.I * omega * (tau : ℂ)))
  simpa using ht.congr' he.symm

/-- Exact vanishing classification of this boundary metric component on the physical
upper half-plane. No choice of frequency or vector amplitude removes a live scalar leg. -/
theorem metric_angular_zero_limit_iff (omega q aS aV : ℂ) (tau : ℝ) (u : Fin 2 → ℝ)
    (hy : 0 < u 1) (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ) :
    Tendsto (fun r : ℝ => (r : ℂ)⁻¹ ^ (2 : ℕ) *
      D4BMFundamentalMetric.perturbation omega q aS aV S V (staticRay tau u r) 2 2)
      atTop (𝓝 0) ↔ aS = 0 ∨ S u = 0 := by
  have hs : D4BMFundamentalMetric.horizonScale u ≠ 0 := by
    have hy0 : (u 1 : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    exact pow_ne_zero _ (inv_ne_zero hy0)
  have ht := metric_angular_limit omega q aS aV tau u S V
  constructor
  · intro h
    have he := tendsto_nhds_unique ht h
    simpa [mul_eq_zero, hs, Complex.exp_ne_zero] using he
  · intro h
    rcases h with h | h
    · simpa [h] using ht
    · simpa [h] using ht

end
end RHTower.D4BMFundamentalMetricBoundary
