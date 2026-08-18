import GaloisForLFunctions.HTGeometry.MacbeathQuotientMap

/-!
# The developing map is a covering map

The kernel of `macbeathHom` acts on the developed space by left multiplication on the sheet index,
and the developing map is exactly the quotient by that action: two points have the same image if and
only if they are in the same orbit, and every point has a neighbourhood — its own sheet — whose
translates are pairwise disjoint.  So the developing map is a **quotient covering map**, hence a
covering map.

* `devKerMulAction` : the action of `ker macbeathHom`.
* `devMap_eq_iff_mem_orbit` : **the fibres are the orbits.**
* `isQuotientCoveringMap_devMap`, `isCoveringMap_devMap` : **the developing map is a covering
  map.**
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise Topology

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The kernel of `macbeathHom` acts on the developed space. -/
instance devKerMulAction (V : Set X) :
    MulAction ((macbeathHom (G := G) V).ker) (DevSpace (G := G) V) where
  smul h y := devSmul V (h : MacbeathGroup (G := G) V) y
  one_smul y := devSmul_one V y
  mul_smul _ _ y := devSmul_mul V _ _ y

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem devKer_smul_mk (V : Set X) (h : (macbeathHom (G := G) V).ker)
    (p : DevSheet (G := G) V) :
    (h • Quot.mk (DevRel (G := G) V) p : DevSpace (G := G) V)
      = Quot.mk _ (⟨(h : MacbeathGroup (G := G) V) * p.1, p.2⟩ : DevSheet (G := G) V) := rfl

instance devKerContinuousConstSMul (V : Set X) :
    ContinuousConstSMul ((macbeathHom (G := G) V).ker) (DevSpace (G := G) V) where
  continuous_const_smul h := continuous_devSmul V (h : MacbeathGroup (G := G) V)

omit [ContinuousConstSMul G X] in
/-- **The fibres of the developing map are the orbits of the kernel.** -/
theorem devMap_eq_iff_mem_orbit {V : Set X} (hVne : V.Nonempty)
    {y₁ y₂ : DevSpace (G := G) V} :
    devMap V y₁ = devMap V y₂ ↔ y₁ ∈ MulAction.orbit ((macbeathHom (G := G) V).ker) y₂ := by
  constructor
  · intro h
    obtain ⟨p, rfl⟩ := Quot.exists_rep y₁
    obtain ⟨q, rfl⟩ := Quot.exists_rep y₂
    rw [devMap_mk, devMap_mk] at h
    set γ : G := (macbeathHom V q.1)⁻¹ * macbeathHom V p.1 with hγdef
    have hxx : ((p.2 : X)) = γ⁻¹ • ((q.2 : X)) := by
      rw [hγdef, mul_inv_rev, inv_inv, mul_smul, ← h, inv_smul_smul]
    have hmem : γ ∈ meetSet (G := G) V := by
      refine ⟨(q.2 : X), ?_, q.2.2⟩
      have : γ • ((p.2 : X)) ∈ γ • V := smul_mem_smul_set p.2.2
      rwa [hxx, smul_inv_smul] at this
    have hstep : (Quot.mk (DevRel (G := G) V) q : DevSpace (G := G) V)
        = Quot.mk _ (⟨q.1 * macbeathOf V ⟨γ, hmem⟩, p.2⟩ : DevSheet (G := G) V) := by
      rw [devSpace_mk_eq_iff hVne]
      exact ⟨γ, hmem, hxx, rfl⟩
    have hker : p.1 * (q.1 * macbeathOf V ⟨γ, hmem⟩)⁻¹ ∈ (macbeathHom (G := G) V).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, macbeathHom_of]
      have hcancel : macbeathHom V q.1 * γ = macbeathHom V p.1 := by
        rw [hγdef, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [hcancel, mul_inv_cancel]
    refine ⟨⟨_, hker⟩, ?_⟩
    rw [hstep]
    show devSmul V (p.1 * (q.1 * macbeathOf V ⟨γ, hmem⟩)⁻¹)
        (Quot.mk _ (⟨q.1 * macbeathOf V ⟨γ, hmem⟩, p.2⟩ : DevSheet (G := G) V)) = Quot.mk _ p
    rw [devSmul_mk]
    refine congrArg (Quot.mk _) (Sigma.ext ?_ (by simp))
    show p.1 * (q.1 * macbeathOf V ⟨γ, hmem⟩)⁻¹ * (q.1 * macbeathOf V ⟨γ, hmem⟩) = p.1
    group
  · rintro ⟨h, rfl⟩
    obtain ⟨p, rfl⟩ := Quot.exists_rep y₂
    show devMap V (devSmul V (h : MacbeathGroup (G := G) V) (Quot.mk _ p))
      = devMap V (Quot.mk _ p)
    rw [devSmul_mk, devMap_mk, devMap_mk, map_mul, MonoidHom.mem_ker.1 h.2, one_mul]

/-- **The developing map is a quotient covering map** for the kernel of `macbeathHom`. -/
theorem isQuotientCoveringMap_devMap [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    IsQuotientCoveringMap (devMap (G := G) V) ((macbeathHom (G := G) V).ker) where
  __ := isQuotientMap_devMap hVopen hVne hcover
  __ := devKerContinuousConstSMul V
  apply_eq_iff_mem_orbit := devMap_eq_iff_mem_orbit hVne
  disjoint := by
    intro e
    obtain ⟨p, rfl⟩ := Quot.exists_rep e
    refine ⟨sheetImage (G := G) V p.1 V,
      (isOpen_sheetImage hVne hVopen p.1 hVopen).mem_nhds ⟨p.2, p.2.2, rfl⟩, ?_⟩
    rintro h ⟨z, ⟨w, hwU, rfl⟩, hz2⟩
    obtain ⟨y₁, -, rfl⟩ := hwU
    obtain ⟨y₂, -, hy₂⟩ := hz2
    rw [devKer_smul_mk] at hy₂
    have hφ : macbeathHom V ((h : MacbeathGroup (G := G) V) * p.1) = macbeathHom V p.1 := by
      rw [map_mul, MonoidHom.mem_ker.1 h.2, one_mul]
    obtain ⟨heq, -⟩ := devSpace_mk_eq_mk_of_macbeathHom_eq hVne hφ hy₂
    refine Subtype.ext ?_
    have : (h : MacbeathGroup (G := G) V) * p.1 = 1 * p.1 := by rw [heq, one_mul]
    exact mul_right_cancel this

/-- **The developing map is a covering map.** -/
theorem isCoveringMap_devMap [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    IsCoveringMap (devMap (G := G) V) :=
  IsQuotientCoveringMap.isCoveringMap (isQuotientCoveringMap_devMap hVopen hVne hcover)

end GaloisForLFunctions.HTGeometry
