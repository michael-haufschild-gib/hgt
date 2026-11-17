import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSurfaceAnalyticity
import GaloisForLFunctions.HilbertMetric.Geometry.CompactSupportEmbedding

/-!
# The actual north surface is a rotated support parametrization

A fixed half-turn changes the standard stereographic normal into the
north-chart normal. Uniqueness of contact with the support planes then
identifies the actual compactified surface with the rotated Bonnet surface.
Thus its radius matrix is the actual geometric radius matrix in that chart.
-/

open Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.NorthSupportRotation
open StereographicFrame BonnetSurface BonnetSupport SchwartzRadius
open CompactifiedSupportSphere SchwartzSurfaceAnalyticity
noncomputable section

private def halfTurnLinear : Space →ₗ[ℝ] Space where
  toFun v := !₂[v 0, -v 1, -v 2]
  map_add' v w := by ext i; fin_cases i <;> simp [PiLp.add_apply, add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp [PiLp.smul_apply]

private theorem halfTurn_inner (v w : Space) :
    inner ℝ (halfTurnLinear v) (halfTurnLinear w) = inner ℝ v w := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [halfTurnLinear]

private theorem halfTurn_norm (v : Space) : ‖halfTurnLinear v‖ = ‖v‖ := by
  have h := halfTurn_inner v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h, norm_nonneg (halfTurnLinear v), norm_nonneg v]

/-- The orientation-preserving half-turn about the first coordinate axis. -/
def halfTurn : Space →L[ℝ] Space :=
  halfTurnLinear.mkContinuous 1 (fun v => by rw [one_mul, halfTurn_norm])

theorem halfTurn_apply (v : Space) : halfTurn v = !₂[v 0, -v 1, -v 2] := rfl

theorem halfTurn_involutive (v : Space) : halfTurn (halfTurn v) = v := by
  ext i
  fin_cases i <;> simp [halfTurn_apply]

theorem halfTurn_inner_move (v w : Space) : inner ℝ (halfTurn v) w = inner ℝ v (halfTurn w) := by
  have h := halfTurn_inner v (halfTurn w)
  change inner ℝ (halfTurn v) (halfTurn (halfTurn w)) = inner ℝ v (halfTurn w) at h
  rwa [halfTurn_involutive] at h

/-- The half-turn exactly relates the two explicit unit-normal formulas. -/
theorem halfTurn_normal (p : ℝ × ℝ) :
    halfTurn (normal p) = Bottcher.stereoInvExtended (Complex.mk p.1 p.2) := by
  ext i
  fin_cases i <;> simp [halfTurn_apply, normal, Bottcher.stereo, Bottcher.stereoInvExtended]
  <;> ring

/-- The north scalar support function written on the real coordinate plane. -/
def northSupportPlane (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  SchwartzInversion.northSupport (complexPotential f) ε (Complex.mk p.1 p.2)

theorem northSupportPlane_smooth (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    ContDiff ℝ ∞ (northSupportPlane f ε) :=
  (SchwartzInversion.northSupport_contDiff _ _).comp Complex.equivRealProdCLM.symm.contDiff

/-- The actual north surface, including its pole, is the rotated support envelope. -/
theorem north_eq_halfTurn_surface (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    SmoothSupportCompactification.north f (positiveScale f) (Complex.mk p.1 p.2) =
      halfTurn (surface (northSupportPlane f (positiveScale f)) p) := by
  let Y := SmoothSupportCompactification.north f (positiveScale f)
  have hb (q : ℝ × ℝ) : inner ℝ (halfTurn (Y (Complex.mk p.1 p.2))) (normal q) ≤
      northSupportPlane f (positiveScale f) q := by
    rw [halfTurn_inner_move, halfTurn_normal]
    have h := CompactSupportEmbedding.support_inequality f
      (northChart (Complex.mk q.1 q.2)) (northChart (Complex.mk p.1 p.2))
    simp only [sphereMap_northChart] at h
    change inner ℝ (Y (Complex.mk p.1 p.2)) (Bottcher.stereoInvExtended (Complex.mk q.1 q.2)) ≤
      inner ℝ (Y (Complex.mk q.1 q.2)) (Bottcher.stereoInvExtended (Complex.mk q.1 q.2)) at h
    exact h.trans_eq (north_support_height f (positiveScale f) _)
  have ht : inner ℝ (halfTurn (Y (Complex.mk p.1 p.2))) (normal p) =
      northSupportPlane f (positiveScale f) p := by
    rw [halfTurn_inner_move, halfTurn_normal]
    exact north_support_height f (positiveScale f) _
  have he := BonnetEnvelope.contact_point_unique (northSupportPlane_smooth f (positiveScale f))
    p (halfTurn (Y (Complex.mk p.1 p.2))) hb ht
  have hh := congrArg halfTurn he
  rwa [halfTurn_involutive] at hh

/-- The actual north differential is the half-turn of the Bonnet radius differential. -/
theorem north_fderiv_eq_halfTurn_surface (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ =>
      SmoothSupportCompactification.north f (positiveScale f) (Complex.mk q.1 q.2)) p =
      halfTurn.comp (fderiv ℝ (surface (northSupportPlane f (positiveScale f))) p) := by
  have he : (fun q : ℝ × ℝ =>
      SmoothSupportCompactification.north f (positiveScale f) (Complex.mk q.1 q.2)) =
      fun q => halfTurn (surface (northSupportPlane f (positiveScale f)) q) :=
    funext (north_eq_halfTurn_surface f)
  rw [he]
  exact (halfTurn.hasFDerivAt.comp p
    (((surface_smooth (northSupportPlane_smooth f (positiveScale f))).differentiable
      (by simp) p).hasFDerivAt)).fderiv

private theorem south_fderiv_injective (f : SchwartzMap (ℝ × ℝ) ℝ) (z : ℂ) :
    Function.Injective (fderiv ℝ (SmoothSupportCompactification.south f (positiveScale f)) z) := by
  have hd := ((surface_smooth (support_smooth (f.smooth ⊤) (positiveScale f))).differentiable
    (by simp) (z.re, z.im)).hasFDerivAt
  have hc := hd.comp z Complex.equivRealProdCLM.hasFDerivAt
  change HasFDerivAt (SmoothSupportCompactification.south f (positiveScale f)) _ z at hc
  rw [hc.fderiv]
  exact (schwartz_surface_fderiv_injective f (z.re, z.im)).comp Complex.equivRealProdCLM.injective

/-- The actual north chart is regular at every point, including the flat pole. -/
theorem north_fderiv_injective (f : SchwartzMap (ℝ × ℝ) ℝ) (z : ℂ) :
    Function.Injective (fderiv ℝ (SmoothSupportCompactification.north f (positiveScale f)) z) := by
  by_cases hz : z = 0
  · subst z
    exact NorthSupportFrame.north_fderiv_injective f _
  · let A : ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)).restrictScalars ℝ
    have hi : HasFDerivAt (fun w : ℂ => w⁻¹) A z :=
      (hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ
    have hs := ((SmoothSupportCompactification.south_smooth f (positiveScale f)).differentiable
      (by simp) z⁻¹).hasFDerivAt
    have hc := hs.comp z hi
    have he : SmoothSupportCompactification.north f (positiveScale f) =ᶠ[𝓝 z]
        (fun w => SmoothSupportCompactification.south f (positiveScale f) w⁻¹) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact (SmoothSupportCompactification.chart_overlap f (positiveScale f) hw).symm
    have hn := he.hasFDerivAt_iff.mpr hc
    rw [hn.fderiv]
    apply (south_fderiv_injective f z⁻¹).comp
    intro v w hvw
    change v * (-(z ^ 2)⁻¹) = w * (-(z ^ 2)⁻¹) at hvw
    exact mul_right_cancel₀ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz))) hvw

/-- The real-coordinate north chart has an injective actual differential everywhere. -/
theorem north_plane_fderiv_injective (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun q : ℝ × ℝ =>
      SmoothSupportCompactification.north f (positiveScale f) (Complex.mk q.1 q.2)) p) := by
  have hd := ((SmoothSupportCompactification.north_smooth f (positiveScale f)).differentiable
    (by simp) (Complex.mk p.1 p.2)).hasFDerivAt
  have hc := hd.comp p Complex.equivRealProdCLM.symm.hasFDerivAt
  change HasFDerivAt (fun q : ℝ × ℝ =>
    SmoothSupportCompactification.north f (positiveScale f) (Complex.mk q.1 q.2)) _ p at hc
  rw [hc.fderiv]
  exact (north_fderiv_injective f _).comp Complex.equivRealProdCLM.symm.injective

#print axioms north_fderiv_injective
#print axioms north_plane_fderiv_injective
#print axioms halfTurn_normal
#print axioms north_eq_halfTurn_surface
#print axioms north_fderiv_eq_halfTurn_surface
end
end GaloisForLFunctions.HilbertMetric.Geometry.NorthSupportRotation
