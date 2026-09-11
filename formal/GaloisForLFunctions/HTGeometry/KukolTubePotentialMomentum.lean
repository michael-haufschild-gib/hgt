import GaloisForLFunctions.HTGeometry.KukolTubePotentialMinimum

/-!
# Exact orbit-potential derivatives and canonical momentum zero

Application of Kukol, *Extended Future Tube Conjecture for Unipotent Subgroups*,
arXiv:2609.10214.

The coordinate momentum equation from Sections 2 and 5 is equivalent to the
unique minimum of the native reciprocal-margin potential on every real linear subgroup.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Set
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orbit margin as a scalar quadratic with its intrinsic drift. -/
theorem kukolTubeMargin_quadratic (v : KukolLightCone E) (r s : ℝ) (z u : E) :
    kukolTubeMargin v r s z u = Real.exp s+
      2*inner ℝ (kukolOrbitDrift r v.1 v.2.2 z) u-kukolOrbitCoefficient r v.1*‖u‖^2 := by
  unfold kukolTubeMargin
  rw [kukolQuadratic_imaginaryAction,kukolQuadratic_strictState]
  simp [kukolStrictState,kukolOrbitDrift,kukolOrbitCoefficient,inner_sub_left,inner_smul_left]

/-- The exact differential of each margin, on the entire parameter space. -/
theorem hasFDerivAt_kukolTubeMargin (v : KukolLightCone E) (r s : ℝ) (z u : E) :
    HasFDerivAt (kukolTubeMargin v r s z)
      ((2 : ℝ) • innerSL ℝ (kukolOrbitDrift r v.1 v.2.2 z-kukolOrbitCoefficient r v.1 • u)) u := by
  have h := (((innerSL ℝ (kukolOrbitDrift r v.1 v.2.2 z)).hasFDerivAt.const_mul 2).const_add
    (Real.exp s)).sub ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_mul
      (kukolOrbitCoefficient r v.1))
  convert! h using 1
  · funext w
    exact kukolTubeMargin_quadratic v r s z w
  · ext w
    simp
    ring

/-- A component of the gradient, expressed by the transformed orbit drift. -/
def kukolTubeForceComponent (v : KukolLightCone E) (r s : ℝ) (z u : E) : E :=
  (1/(kukolTubeMargin v r s z u)^2) •
    (kukolOrbitCoefficient r v.1 • u-kukolOrbitDrift r v.1 v.2.2 z)

/-- Differentiation of the reciprocal margin on its natural positive domain. -/
theorem hasFDerivAt_kukolTubeReciprocal (v : KukolLightCone E) (r s : ℝ) (z : E)
    (u : {u : E | 0 < kukolTubeMargin v r s z u}) :
    HasFDerivAt (fun w => 1/kukolTubeMargin v r s z w)
      ((2 : ℝ) • innerSL ℝ (kukolTubeForceComponent v r s z u)) u.val := by
  have h := (hasDerivAt_inv u.property.ne').comp_hasFDerivAt u.val
    (hasFDerivAt_kukolTubeMargin v r s z u)
  have hmap : (-((kukolTubeMargin v r s z u)^2)⁻¹) •
      ((2 : ℝ) • innerSL ℝ (kukolOrbitDrift r v.1 v.2.2 z-kukolOrbitCoefficient r v.1 • u.val)) =
      (2 : ℝ) • innerSL ℝ (kukolTubeForceComponent v r s z u) := by
    ext w
    simp [kukolTubeForceComponent]
    ring
  rw [hmap] at h
  simpa only [Function.comp_def,one_div] using h

variable [Fintype ι]

/-- The total force; twice this vector represents the differential of the native potential. -/
def kukolTubeForce (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (u : E) : E :=
  ∑ i,kukolTubeForceComponent (v i) (r i) (s i) (z i) u

/-- The exact Fréchet derivative of the simultaneous orbit potential. -/
theorem hasFDerivAt_kukolTubePotential (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (u : kukolTubeDomain v r s z) :
    HasFDerivAt (kukolTubePotential v r s z) ((2 : ℝ) • innerSL ℝ (kukolTubeForce v r s z u)) u.val := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hasFDerivAt_kukolTubeReciprocal (v i) (r i) (s i) (z i) ⟨u.val,u.property i⟩)
  convert! h using 1
  simp only [kukolTubeForce,map_sum,Finset.smul_sum]

/-- A global supporting-plane inequality obtained from convexity along the full connecting segment. -/
theorem kukolTubePotential_support (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (anchor : ι) (u w : kukolTubeDomain v r s z) :
    kukolTubePotential v r s z u+2*inner ℝ (kukolTubeForce v r s z u) (w.val-u.val) ≤
      kukolTubePotential v r s z w := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap u.val w.val
  have hc := (strictConvexOn_kukolTubePotential v r s z anchor).convexOn.comp_affineMap g
  have hzero : (0 : ℝ) ∈ g ⁻¹' kukolTubeDomain v r s z := by simpa only [g,Set.mem_preimage,AffineMap.lineMap_apply_zero] using u.property
  have hone : (1 : ℝ) ∈ g ⁻¹' kukolTubeDomain v r s z := by simpa only [g,Set.mem_preimage,AffineMap.lineMap_apply_one] using w.property
  have hd : HasFDerivAt (kukolTubePotential v r s z)
      ((2 : ℝ) • innerSL ℝ (kukolTubeForce v r s z u)) (g 0) := by
    simpa [g] using hasFDerivAt_kukolTubePotential v r s z u
  have hline := hd.comp_hasDerivAt 0 (AffineMap.hasDerivAt_lineMap (a := u.val) (b := w.val) (x := (0 : ℝ)))
  have h := hc.le_slope_of_hasDerivAt hzero hone zero_lt_one hline
  simp only [slope,Function.comp_def,g,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,
    sub_zero,inv_one,vsub_eq_sub,smul_apply,innerSL_apply_apply,
    smul_eq_mul] at h
  linarith

variable [FiniteDimensional ℝ E]

/-- The canonical minimizer has zero momentum along every permitted subgroup direction. -/
theorem kukolTubeMinimizer_force_orthogonal (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι) :
    kukolTubeForce v r s z (kukolTubeMinimizer W v r s z anchor) ∈ Wᗮ := by
  let u := kukolTubeMinimizer W v r s z anchor
  have hu := kukolTubeMinimizer_spec W v r s z anchor
  let uW : W := ⟨u,hu.1.2⟩
  have hmin : IsMinOn (fun w : W => kukolTubePotential v r s z w)
      (Subtype.val ⁻¹' kukolTubeDomain v r s z) uW := by
    intro w hw
    exact hu.2 ⟨hw,w.property⟩
  have hopen : IsOpen (Subtype.val ⁻¹' kukolTubeDomain v r s z : Set W) :=
    (isOpen_kukolTubeDomain v r s z).preimage continuous_subtype_val
  have hl := hmin.isLocalMin (hopen.mem_nhds hu.1.1)
  have hd := (hasFDerivAt_kukolTubePotential v r s z ⟨u,hu.1.1⟩).comp uW
    W.subtypeL.hasFDerivAt
  have he := hl.hasFDerivAt_eq_zero hd
  apply (W.mem_orthogonal' _).mpr
  intro w hw
  have hew := congrArg (fun f : W →L[ℝ] ℝ => f ⟨w,hw⟩) he
  change 2*inner ℝ (kukolTubeForce v r s z u) w=0 at hew
  change inner ℝ (kukolTubeForce v r s z u) w=0
  linarith

/-- The explicit subgroup momentum equation characterizes the canonical representative exactly. -/
theorem kukolTubeMinimizer_momentum_iff (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι) (u : E) :
    u=kukolTubeMinimizer W v r s z anchor ↔
      u ∈ kukolConstrainedTubeDomain W v r s z ∧ kukolTubeForce v r s z u ∈ Wᗮ := by
  constructor
  · rintro rfl
    exact ⟨(kukolTubeMinimizer_spec W v r s z anchor).1,
      kukolTubeMinimizer_force_orthogonal W v r s z anchor⟩
  · rintro ⟨hu,hforce⟩
    apply (kukolTubeMinimizer_eq_iff W v r s z anchor u).mpr
    refine ⟨hu,?_⟩
    intro w hw
    change kukolTubePotential v r s z u ≤ kukolTubePotential v r s z w
    have h := kukolTubePotential_support v r s z anchor ⟨u,hu.1⟩ ⟨w,hw.1⟩
    have ho := (W.mem_orthogonal' _).mp hforce (w-u) (W.sub_mem hw.2 hu.2)
    simpa only [ho,mul_zero,add_zero] using h

/-- On the full imaginary group, the force vanishes at precisely one admissible point. -/
theorem kukolTubeForce_zero_iff (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (anchor : ι) (u : kukolTubeDomain v r s z) :
    kukolTubeForce v r s z u=0 ↔ u.val=kukolTubeMinimizer ⊤ v r s z anchor := by
  simpa [kukolConstrainedTubeDomain,u.property,Submodule.top_orthogonal_eq_bot] using
      (kukolTubeMinimizer_momentum_iff ⊤ v r s z anchor u.val).symm

end GaloisForLFunctions.HTGeometry
