import GaloisForLFunctions.HTGeometry.IncubationTubeTransport

/-!
# The spherical tube over a carrier patch has codimension volume

A patch of the unit sphere of a carrier subspace, thickened inside the ambient sphere by a radius
`r`, has normalized surface measure at least a constant times `r^d`, where `d` is the codimension of
the carrier.  The constant depends only on the patch.

The proof is a cone comparison.  Normalization is two-Lipschitz away from the origin, so a vector
whose carrier part points into the patch and whose transverse part is shorter than `r/8` normalizes
into the `r`-thickening.  Those vectors form a product set -- a carrier annulus times a transverse
ball -- whose volume is the carrier factor times `(r/8)^d` times the unit transverse ball.  Dividing
by the volume of the unit ball turns the cone volume into surface measure.
-/

open MeasureTheory Metric Set WithLp
open scoped Pointwise ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Normalization is two-Lipschitz -/

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Normalization is two-Lipschitz away from the origin.**  Two nonzero vectors have normalized
difference at most twice their distance divided by the length of the first. -/
theorem norm_normalize_sub_normalize_le {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖ ≤ 2 * ‖a - b‖ / ‖a‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hsplit : ‖a‖⁻¹ • a - ‖b‖⁻¹ • b = ‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b := by
    rw [smul_sub, sub_smul]
    abel
  have hfirst : ‖‖a‖⁻¹ • (a - b)‖ = ‖a - b‖ / ‖a‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    field_simp
  have hgap : |‖a‖⁻¹ - ‖b‖⁻¹| ≤ ‖a - b‖ / (‖a‖ * ‖b‖) := by
    have hval : ‖a‖⁻¹ - ‖b‖⁻¹ = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by
      field_simp
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖a‖ * ‖b‖)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc |‖b‖ - ‖a‖| = |‖a‖ - ‖b‖| := abs_sub_comm _ _
      _ ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have hsecond : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ ≤ ‖a - b‖ / ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |‖a‖⁻¹ - ‖b‖⁻¹| * ‖b‖ ≤ (‖a - b‖ / (‖a‖ * ‖b‖)) * ‖b‖ :=
          mul_le_mul_of_nonneg_right hgap (norm_nonneg b)
      _ = ‖a - b‖ / ‖a‖ := by field_simp
  calc ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖ = ‖‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b‖ := by rw [hsplit]
    _ ≤ ‖‖a‖⁻¹ • (a - b)‖ + ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ / ‖a‖ + ‖a - b‖ / ‖a‖ := by rw [hfirst]; linarith [hsecond]
    _ = 2 * ‖a - b‖ / ‖a‖ := by ring

end Normalize

/-! ## The carrier patch and its tube -/

section Patch

variable {f d : ℕ}

/-- The ambient coefficient space, split into a carrier and its transverse complement. -/
abbrev PatchSpace (f d : ℕ) : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin f) × EuclideanSpace ℝ (Fin d))

/-- The carrier patch, embedded in the ambient space at zero transverse part. -/
def embedPatch (PU : Set (EuclideanSpace ℝ (Fin f))) : Set (PatchSpace f d) :=
  (fun u => (toLp 2 (u, (0 : EuclideanSpace ℝ (Fin d))) : PatchSpace f d)) '' PU

/-- The carrier cone annulus: vectors of the carrier whose direction lies in the patch and whose
length lies between one half and three quarters. -/
def patchAnnulus (PU : Set (EuclideanSpace ℝ (Fin f))) : Set (EuclideanSpace ℝ (Fin f)) :=
  {u | 1 / 2 < ‖u‖ ∧ ‖u‖ < 3 / 4 ∧ ‖u‖⁻¹ • u ∈ PU}

/-- The tube over the carrier patch: the carrier cone annulus thickened transversally by `ρ`. -/
def patchTube (PU : Set (EuclideanSpace ℝ (Fin f))) (ρ : ℝ) : Set (PatchSpace f d) :=
  (ofLp : PatchSpace f d → _) ⁻¹'
    (patchAnnulus PU ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ)

/-- The `r`-thickening of the embedded patch inside the ambient unit sphere. -/
def patchThickening (PU : Set (EuclideanSpace ℝ (Fin f))) (r : ℝ) :
    Set (sphere (0 : PatchSpace f d) 1) :=
  {ω | Metric.infDist (ω : PatchSpace f d) (embedPatch (d := d) PU) ≤ r}

theorem measurableSet_patchThickening (PU : Set (EuclideanSpace ℝ (Fin f))) (r : ℝ) :
    MeasurableSet (patchThickening (d := d) PU r) := by
  have hcont : Continuous fun ω : sphere (0 : PatchSpace f d) 1 =>
      Metric.infDist (ω : PatchSpace f d) (embedPatch (d := d) PU) :=
    (Metric.continuous_infDist_pt _).comp continuous_subtype_val
  exact measurableSet_le hcont.measurable measurable_const

theorem measurableSet_patchAnnulus {PU : Set (EuclideanSpace ℝ (Fin f))}
    (hPU : MeasurableSet PU) : MeasurableSet (patchAnnulus PU) := by
  have hnorm : Measurable fun u : EuclideanSpace ℝ (Fin f) => ‖u‖ := measurable_norm
  have hnormalize : Measurable fun u : EuclideanSpace ℝ (Fin f) => ‖u‖⁻¹ • u :=
    (hnorm.inv).smul measurable_id
  refine MeasurableSet.inter (measurableSet_lt measurable_const hnorm) ?_
  exact MeasurableSet.inter (measurableSet_lt hnorm measurable_const) (hnormalize hPU)

/-! ## The tube volume -/

theorem volume_patchTube {PU : Set (EuclideanSpace ℝ (Fin f))} (hPU : MeasurableSet PU)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (patchTube (d := d) PU ρ)
      = volume (patchAnnulus PU) *
        (ENNReal.ofReal (ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
  have hmeas : MeasurableSet
      (patchAnnulus PU ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ) :=
    (measurableSet_patchAnnulus hPU).prod measurableSet_closedBall
  rw [patchTube, (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin f))
      (EuclideanSpace ℝ (Fin d))).measure_preimage hmeas.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_closedBall _ 0 hρ]
  congr 2
  simp

/-! ## The tube lies in the cone over the thickening -/

theorem patchTube_subset_cone (PU : Set (EuclideanSpace ℝ (Fin f)))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    patchTube (d := d) PU (r / 8)
      ⊆ Set.Ioo (0 : ℝ) 1 • (Subtype.val '' patchThickening (d := d) PU r) := by
  rintro x ⟨hu, hv⟩
  obtain ⟨hlow, hhigh, hdir⟩ := hu
  set u : EuclideanSpace ℝ (Fin f) := (ofLp x).1 with hudef
  set v : EuclideanSpace ℝ (Fin d) := (ofLp x).2 with hvdef
  have hvnorm : ‖v‖ ≤ r / 8 := by
    have := mem_closedBall_zero_iff.mp hv
    exact this
  have hsq : ‖x‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 x
  have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
  have hunn : 0 ≤ ‖u‖ := norm_nonneg u
  have hvnn : 0 ≤ ‖v‖ := norm_nonneg v
  have hxlow : 1 / 2 < ‖x‖ := by nlinarith [hsq, hlow, hxnn, hvnn]
  have hxhigh : ‖x‖ < 1 := by
    have hv8 : ‖v‖ ≤ 1 / 8 := by linarith [hvnorm, hr1]
    nlinarith [hsq, hhigh, hxnn, hunn, hvnn, hv8]
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxlow
    linarith
  -- the carrier point of the patch nearest to `x`
  have hune : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  set y : PatchSpace f d := toLp 2 (u, (0 : EuclideanSpace ℝ (Fin d))) with hydef
  have hyfst : y.fst = u := rfl
  have hysnd : y.snd = (0 : EuclideanSpace ℝ (Fin d)) := rfl
  have hynorm : ‖y‖ = ‖u‖ := by
    have hy2 : ‖y‖ ^ 2 = ‖u‖ ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin d))‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 y
    rw [norm_zero] at hy2
    nlinarith [hy2, norm_nonneg y, hunn]
  have hyne : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hynorm
    rw [← hynorm] at hlow
    linarith
  have hdiff : x - y = toLp 2 ((0 : EuclideanSpace ℝ (Fin f)), v) := by
    have hx : x = toLp 2 (u, v) := rfl
    rw [hx, hydef, ← WithLp.toLp_sub]
    congr 1
    simp
  have hdiffnorm : ‖x - y‖ = ‖v‖ := by
    have h2 : ‖x - y‖ ^ 2 = ‖(0 : EuclideanSpace ℝ (Fin f))‖ ^ 2 + ‖v‖ ^ 2 := by
      rw [hdiff]
      exact WithLp.prod_norm_sq_eq_of_L2 _
    rw [norm_zero] at h2
    nlinarith [h2, norm_nonneg (x - y), hvnn]
  -- the normalized carrier point lies in the embedded patch
  have hmemPatch : ‖y‖⁻¹ • y ∈ embedPatch (d := d) PU := by
    refine ⟨‖u‖⁻¹ • u, hdir, ?_⟩
    show toLp 2 (‖u‖⁻¹ • u, (0 : EuclideanSpace ℝ (Fin d))) = ‖y‖⁻¹ • y
    rw [hynorm, hydef, ← WithLp.toLp_smul]
    congr 1
    simp
    rfl
  -- the normalized vector is within `r` of the patch
  have hclose : Metric.infDist (‖x‖⁻¹ • x) (embedPatch (d := d) PU) ≤ r := by
    refine le_trans (Metric.infDist_le_dist_of_mem hmemPatch) ?_
    rw [dist_eq_norm]
    calc ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ :=
          norm_normalize_sub_normalize_le hxne hyne
      _ = 2 * ‖v‖ / ‖x‖ := by rw [hdiffnorm]
      _ ≤ r := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖x‖)]
          nlinarith [hvnorm, hxlow, hr0.le]
  have hunit : ‖x‖⁻¹ • x ∈ sphere (0 : PatchSpace f d) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg hxnn]
    field_simp
  refine ⟨‖x‖, ⟨by linarith, hxhigh⟩, ‖x‖⁻¹ • x, ⟨⟨‖x‖⁻¹ • x, hunit⟩, hclose, rfl⟩, ?_⟩
  show ‖x‖ • (‖x‖⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ (by linarith : ‖x‖ ≠ 0), one_smul]

/-! ## The codimension volume of the thickening -/

/-- **`(9)`: the spherical tube over a carrier patch has codimension volume.**  The surface measure
of the `r`-thickening of a carrier patch is at least the carrier factor times `(r/8)^d` times the
unit transverse ball, where `d` is the codimension. -/
theorem toSphere_patchThickening_ge {PU : Set (EuclideanSpace ℝ (Fin f))}
    (hPUmeas : MeasurableSet PU) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (Module.finrank ℝ (PatchSpace f d) : ℝ≥0∞) *
        (volume (patchAnnulus PU) *
          (ENNReal.ofReal ((r / 8) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)))
      ≤ (volume : Measure (PatchSpace f d)).toSphere (patchThickening (d := d) PU r) := by
  rw [Measure.toSphere_apply' _ (measurableSet_patchThickening (d := d) PU r)]
  refine mul_le_mul_right ?_ _
  rw [← volume_patchTube (d := d) hPUmeas (by positivity : (0:ℝ) ≤ r / 8)]
  exact measure_mono (patchTube_subset_cone (d := d) PU hr0 hr1)

end Patch

end

end GaloisForLFunctions.HTGeometry
