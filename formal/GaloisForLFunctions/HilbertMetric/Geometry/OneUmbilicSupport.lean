import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzBonnetCharts
import GaloisForLFunctions.HilbertMetric.Geometry.SupportBodyContact

/-!
# A single scalar Gauss differential on the explicit support sphere

Umbilicity is expressed by the actual Fréchet derivatives of the unit
normal and the surface chart. The nonscalar finite radius matrix excludes
every finite point; flat compactification gives the round differential at
the north pole.
-/

open scoped ContDiff
open Set Topology
namespace GaloisForLFunctions.HilbertMetric.Geometry.OneUmbilicSupport
open Bottcher BonnetSupport BonnetSurface StereographicFrame
open SchwartzBonnetCharts CompactifiedSupportSphere
noncomputable section

/-- The coordinate-free scalar Gauss condition in the finite chart. -/
def finiteScalarGauss (p : ℝ × ℝ) : Prop :=
  ∃ κ : ℝ, fderiv ℝ normal p = κ • fderiv ℝ (surface south) p

/-- The actual radius determinant is positive at every finite point. -/
theorem finite_radius_determinant_pos (p : ℝ × ℝ) :
    0 < radiusXX south p * radiusYY south p - radiusXY south p ^ 2 := by
  let a := radiusXX south p
  let b := radiusXY south p
  let c := radiusYY south p
  have ha := south_radius_positive p 1 0
  change ((1 : ℝ) ^ 2 + 0 ^ 2) / 2 ≤ a * 1 ^ 2 + 2 * b * 1 * 0 + c * 0 ^ 2 at ha
  norm_num at ha
  have hap : 0 < a := by linarith only [ha]
  have hq := south_radius_positive p b (-a)
  change (b ^ 2 + (-a) ^ 2) / 2 ≤ a * b ^ 2 + 2 * b * b * (-a) + c * (-a) ^ 2 at hq
  have he : a * b ^ 2 + 2 * b * b * (-a) + c * (-a) ^ 2 = a * (a * c - b ^ 2) := by ring
  rw [he] at hq
  have hs : 0 < (-a) ^ 2 := sq_pos_of_ne_zero (neg_ne_zero.mpr hap.ne')
  have hp : 0 < a * (a * c - b ^ 2) := by nlinarith only [hq, hs, sq_nonneg b]
  change 0 < a * c - b ^ 2
  by_contra h
  exact hp.not_ge (mul_nonpos_of_nonneg_of_nonpos hap.le (le_of_not_gt h))

/-- The corresponding condition in the actual chart centered at the missing pole. -/
def northScalarGauss : Prop :=
  ∃ κ : ℝ, fderiv ℝ stereoInvExtended 0 =
    κ • fderiv ℝ (SmoothSupportCompactification.north SeparableHessian.dampedSeedSchwartz amplitude) 0

/-- Actual normal and surface differentials are never proportional at a finite point. -/
theorem not_finiteScalarGauss (p : ℝ × ℝ) : ¬ finiteScalarGauss p := by
  rintro ⟨κ, hκ⟩
  have hn := (normal_smooth.differentiable (by simp) p).hasFDerivAt
  have hnx := (hn.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  have hny := (hn.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
  change deriv (fun t => normal (t, p.2)) p.1 = fderiv ℝ normal p (1, 0) at hnx
  change deriv (fun t => normal (p.1, t)) p.2 = fderiv ℝ normal p (0, 1) at hny
  have hx := congrArg (fun L : (ℝ × ℝ) →L[ℝ] Space => L (1, 0)) hκ
  have hy := congrArg (fun L : (ℝ × ℝ) →L[ℝ] Space => L (0, 1)) hκ
  change fderiv ℝ normal p (1, 0) = κ • fderiv ℝ (surface south) p (1, 0) at hx
  change fderiv ℝ normal p (0, 1) = κ • fderiv ℝ (surface south) p (0, 1) at hy
  rw [← hnx, surface_fderiv_apply south_smooth] at hx
  rw [← hny, surface_fderiv_apply south_smooth] at hy
  simp only [one_smul, zero_smul, add_zero, zero_add] at hx hy
  obtain ⟨he, hz, _⟩ := (gauss_derivative_scalar_iff south_smooth p).mp ⟨κ, hx, hy⟩
  exact south_radius_not_scalar p ⟨he, hz⟩

/-- The north-pole Gauss differential is exactly the surface differential. -/
theorem northScalarGauss_true : northScalarGauss := by
  refine ⟨1, ?_⟩
  rw [one_smul, SmoothSupportCompactification.north_fderiv_round]

/-- The scalar Gauss condition uses a regular chart at every normal parameter. -/
def scalarGaussAt (v : Sphere) : Prop :=
  if (v : Ambient) = northPole then northScalarGauss
  else finiteScalarGauss ((stereoFiniteChart v).re, (stereoFiniteChart v).im)

/-- The explicit compactified surface has precisely one scalar Gauss differential. -/
theorem scalarGaussAt_iff (v : Sphere) : scalarGaussAt v ↔ (v : Ambient) = northPole := by
  by_cases h : (v : Ambient) = northPole
  · simp only [scalarGaussAt, h, iff_true]
    exact northScalarGauss_true
  · simp only [scalarGaussAt, h, iff_false]
    exact not_finiteScalarGauss _

/-- The unique parameter is the actual north pole of the unit sphere. -/
theorem existsUnique_scalarGauss : ∃! v : Sphere, scalarGaussAt v := by
  refine ⟨northChart 0, (scalarGaussAt_iff _).mpr ?_, ?_⟩
  · simp [northChart]
  · intro v hv
    apply Subtype.ext
    simpa [northChart] using (scalarGaussAt_iff v).mp hv

/-- The explicit global surface, parametrized by its actual unit normals. -/
def explicitSurface : Sphere → Ambient :=
  sphereMap SeparableHessian.dampedSeedSchwartz amplitude

/-- The scalar Gauss condition for an arbitrary sphere parametrization, using its actual charts. -/
def scalarGaussOf (X : Sphere → Ambient) (v : Sphere) : Prop :=
  if (v : Ambient) = northPole then
    ∃ κ : ℝ, fderiv ℝ stereoInvExtended 0 = κ • fderiv ℝ (fun z => X (northChart z)) 0
  else
    let p := ((stereoFiniteChart v).re, (stereoFiniteChart v).im)
    ∃ κ : ℝ, fderiv ℝ normal p =
      κ • fderiv ℝ (fun q : ℝ × ℝ => X (southChart (Complex.mk q.1 q.2))) p

theorem explicit_south_chart :
    (fun q : ℝ × ℝ => explicitSurface (southChart (Complex.mk q.1 q.2))) = surface south := by
  funext q
  rw [explicitSurface, sphereMap_southChart]
  rfl

theorem explicit_north_chart :
    (fun z : ℂ => explicitSurface (northChart z)) =
      SmoothSupportCompactification.north SeparableHessian.dampedSeedSchwartz amplitude := by
  funext z
  exact sphereMap_northChart _ _ z

/-- The scalar-differential calculation concerns the actual global surface map. -/
theorem scalarGaussOf_explicit_iff (v : Sphere) :
    scalarGaussOf explicitSurface v ↔ scalarGaussAt v := by
  unfold scalarGaussOf scalarGaussAt
  rw [explicit_south_chart, explicit_north_chart]
  rfl

/-- The explicit parametrization is a closed embedding of the actual unit sphere. -/
theorem explicitSurface_isClosedEmbedding : Topology.IsClosedEmbedding explicitSurface :=
  CompactSupportEmbedding.sphereMap_isClosedEmbedding SeparableHessian.dampedSeedSchwartz

/-- Both actual coordinate maps are smooth, and their differentials are injective wherever used. -/
theorem explicitSurface_regular_charts :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => explicitSurface (southChart (Complex.mk q.1 q.2))) ∧
    (∀ p, Function.Injective (fderiv ℝ
      (fun q : ℝ × ℝ => explicitSurface (southChart (Complex.mk q.1 q.2))) p)) ∧
    ContDiff ℝ ∞ (fun z : ℂ => explicitSurface (northChart z)) ∧
    Function.Injective (fderiv ℝ (fun z : ℂ => explicitSurface (northChart z)) 0) := by
  rw [explicit_south_chart, explicit_north_chart]
  exact ⟨surface_smooth south_smooth,
    fun p => schwartz_surface_fderiv_injective SeparableHessian.dampedSeedSchwartz p,
    SmoothSupportCompactification.north_smooth _ _, NorthSupportFrame.north_fderiv_injective _ _⟩

/-- Exactly one point of the actual embedded surface has scalar Gauss differential. -/
theorem existsUnique_actual_scalarGauss : ∃! v : Sphere, scalarGaussOf explicitSurface v := by
  obtain ⟨v, hv, hu⟩ := existsUnique_scalarGauss
  exact ⟨v, (scalarGaussOf_explicit_iff v).mpr hv,
    fun w hw => hu w ((scalarGaussOf_explicit_iff w).mp hw)⟩

/-- The prescribed normals are perpendicular to the actual surface differentials in both charts. -/
theorem explicitSurface_normal_charts :
    (∀ p w : ℝ × ℝ, inner ℝ (normal p)
      (fderiv ℝ (fun q : ℝ × ℝ => explicitSurface (southChart (Complex.mk q.1 q.2))) p w) = 0) ∧
    (∀ z : ℂ, inner ℝ northPole
      (fderiv ℝ (fun q : ℂ => explicitSurface (northChart q)) 0 z) = 0) := by
  rw [explicit_south_chart, explicit_north_chart]
  constructor
  · intro p w
    rw [surface_fderiv_apply south_smooth]
    obtain ⟨hx, hy⟩ := surface_normal south_smooth p
    simp only [inner_add_right, inner_smul_right, hx, hy, mul_zero, add_zero]
  · intro z
    rw [NorthSupportFrame.north_fderiv_apply]
    simp [northPole, PiLp.inner_apply, Fin.sum_univ_three]

/-- The unique umbilic is an actual ambient point, not only a unique chart parameter. -/
theorem actual_scalarGauss_point_iff (x : Ambient) :
    (∃ v : Sphere, explicitSurface v = x ∧ scalarGaussOf explicitSurface v) ↔ x = northPole := by
  constructor
  · rintro ⟨v, hv, hs⟩
    have hn : (v : Ambient) = northPole :=
      (scalarGaussAt_iff v).mp ((scalarGaussOf_explicit_iff v).mp hs)
    have he : v = northChart 0 := by apply Subtype.ext; simpa [northChart] using hn
    rw [he] at hv
    have h0 : explicitSurface (northChart 0) = northPole := by
      rw [explicitSurface, sphereMap_northChart, SmoothSupportCompactification.north_zero]
    exact hv.symm.trans h0
  · rintro rfl
    refine ⟨northChart 0, ?_, ?_⟩
    · rw [explicitSurface, sphereMap_northChart, SmoothSupportCompactification.north_zero]
    · apply (scalarGaussOf_explicit_iff _).mpr
      apply (scalarGaussAt_iff _).mpr
      simp [northChart]

/-- A concrete compact strictly convex body whose smooth embedded boundary has exactly one umbilic. -/
theorem one_umbilic_strictlyConvex_surface :
    IsCompact (SchwartzSupportBody.body SeparableHessian.dampedSeedSchwartz) ∧
    (interior (SchwartzSupportBody.body SeparableHessian.dampedSeedSchwartz)).Nonempty ∧
    StrictConvex ℝ (SchwartzSupportBody.body SeparableHessian.dampedSeedSchwartz) ∧
    Set.range explicitSurface = frontier (SchwartzSupportBody.body SeparableHessian.dampedSeedSchwartz) ∧
    Topology.IsClosedEmbedding explicitSurface ∧
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => explicitSurface (southChart (Complex.mk q.1 q.2))) ∧
    (∀ p, Function.Injective (fderiv ℝ
      (fun q : ℝ × ℝ => explicitSurface (southChart (Complex.mk q.1 q.2))) p)) ∧
    ContDiff ℝ ∞ (fun z : ℂ => explicitSurface (northChart z)) ∧
    Function.Injective (fderiv ℝ (fun z : ℂ => explicitSurface (northChart z)) 0) ∧
    (∃! v : Sphere, scalarGaussOf explicitSurface v) := by
  obtain ⟨hs, hi, hn, hni⟩ := explicitSurface_regular_charts
  refine ⟨SchwartzSupportBody.body_compact _, SchwartzSupportBody.body_interior_nonempty _,
    SupportBodyContact.body_strictConvex _, ?_, explicitSurface_isClosedEmbedding,
    hs, hi, hn, hni, existsUnique_actual_scalarGauss⟩
  exact (SupportBodyContact.frontier_body_eq_range SeparableHessian.dampedSeedSchwartz).symm

#print axioms explicitSurface_normal_charts
#print axioms actual_scalarGauss_point_iff
#print axioms one_umbilic_strictlyConvex_surface
#print axioms explicitSurface_isClosedEmbedding
#print axioms explicitSurface_regular_charts
#print axioms existsUnique_actual_scalarGauss
#print axioms finite_radius_determinant_pos
#print axioms not_finiteScalarGauss
#print axioms northScalarGauss_true
#print axioms scalarGaussAt_iff
#print axioms existsUnique_scalarGauss
end
end GaloisForLFunctions.HilbertMetric.Geometry.OneUmbilicSupport
