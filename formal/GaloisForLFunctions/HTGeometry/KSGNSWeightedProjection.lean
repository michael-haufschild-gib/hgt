import GaloisForLFunctions.HTGeometry.KSGNSConstruction

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A B : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Inverse positive square root of the KSGNS order unit `Φ(1)`. -/
def ksgnsOrderUnitInvSqrt (phi : A →CP B) (hunit : IsUnit (phi 1)) : B :=
  let hpos : 0 ≤ phi 1 := map_nonneg phi (by
    simpa using star_mul_self_nonneg (1 : A))
  let hsunit : IsUnit (CFC.sqrt (phi 1)) :=
    (CFC.isUnit_sqrt_iff (phi 1) hpos).2 hunit
  ↑(hsunit.unit⁻¹)

theorem ksgnsOrderUnitInvSqrt_mul_sqrt (phi : A →CP B)
    (hunit : IsUnit (phi 1)) :
    ksgnsOrderUnitInvSqrt phi hunit * CFC.sqrt (phi 1) = 1 := by
  let hpos : 0 ≤ phi 1 := map_nonneg phi (by
    simpa using star_mul_self_nonneg (1 : A))
  let hsunit : IsUnit (CFC.sqrt (phi 1)) :=
    (CFC.isUnit_sqrt_iff (phi 1) hpos).2 hunit
  simpa only [ksgnsOrderUnitInvSqrt, hpos, hsunit, hsunit.unit_spec] using
    Units.inv_mul hsunit.unit

theorem sqrt_mul_ksgnsOrderUnitInvSqrt (phi : A →CP B)
    (hunit : IsUnit (phi 1)) :
    CFC.sqrt (phi 1) * ksgnsOrderUnitInvSqrt phi hunit = 1 := by
  let hpos : 0 ≤ phi 1 := map_nonneg phi (by
    simpa using star_mul_self_nonneg (1 : A))
  let hsunit : IsUnit (CFC.sqrt (phi 1)) :=
    (CFC.isUnit_sqrt_iff (phi 1) hpos).2 hunit
  simpa only [ksgnsOrderUnitInvSqrt, hpos, hsunit, hsunit.unit_spec] using
    Units.mul_inv hsunit.unit

theorem star_ksgnsOrderUnitInvSqrt (phi : A →CP B)
    (hunit : IsUnit (phi 1)) :
    star (ksgnsOrderUnitInvSqrt phi hunit) =
      ksgnsOrderUnitInvSqrt phi hunit := by
  let r := ksgnsOrderUnitInvSqrt phi hunit
  let s := CFC.sqrt (phi 1)
  have hsnonneg : 0 ≤ s := CFC.sqrt_nonneg _
  obtain ⟨c, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hsnonneg
  have hsstar : star s = s := by
    rw [hc, star_mul, star_star]
  have hrs : r * s = 1 := ksgnsOrderUnitInvSqrt_mul_sqrt phi hunit
  have hsr : s * r = 1 := sqrt_mul_ksgnsOrderUnitInvSqrt phi hunit
  have hstarsr : star r * s = 1 := by
    have h := congrArg star hsr
    rw [star_mul, star_one, hsstar] at h
    exact h
  calc
    star r = star r * 1 := by rw [mul_one]
    _ = star r * (s * r) := by rw [hsr]
    _ = (star r * s) * r := by rw [mul_assoc]
    _ = r := by rw [hstarsr, one_mul]

theorem ksgnsOrderUnitInvSqrt_sq (phi : A →CP B)
    (hunit : IsUnit (phi 1)) :
    ksgnsOrderUnitInvSqrt phi hunit * ksgnsOrderUnitInvSqrt phi hunit =
      ksgnsOrderUnitInv phi hunit := by
  let r := ksgnsOrderUnitInvSqrt phi hunit
  let s := CFC.sqrt (phi 1)
  let h := phi 1
  let g := ksgnsOrderUnitInv phi hunit
  have hpos : 0 ≤ h := map_nonneg phi (by
    simpa using star_mul_self_nonneg (1 : A))
  have hsquare : s * s = h := by
    simpa only [pow_two] using CFC.sq_sqrt h hpos
  have hrs : r * s = 1 := ksgnsOrderUnitInvSqrt_mul_sqrt phi hunit
  have hhg : h * g = 1 := mul_ksgnsOrderUnitInv phi hunit
  have hrrh : (r * r) * h = 1 := by
    rw [← hsquare]
    calc
      (r * r) * (s * s) = r * (r * s) * s := by simp only [mul_assoc]
      _ = r * 1 * s := by rw [hrs]
      _ = r * s := by rw [mul_one]
      _ = 1 := hrs
  calc
    r * r = (r * r) * 1 := by rw [mul_one]
    _ = (r * r) * (h * g) := by rw [hhg]
    _ = ((r * r) * h) * g := by noncomm_ring
    _ = g := by rw [hrrh, one_mul]

/-- Normalized cyclic vector `η = ξ Φ(1)⁻¹ᐟ²`. -/
def ksgnsWeightedUnitVector (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    KSGNS phi :=
  MulOpposite.op (ksgnsOrderUnitInvSqrt phi hunit) • ksgnsCyclic phi

theorem ksgnsWeightedUnitVector_inner_self (phi : A →CP B)
    (hunit : IsUnit (phi 1)) :
    (ksgnsRightInnerModuleData phi).inner
        (ksgnsWeightedUnitVector phi hunit)
        (ksgnsWeightedUnitVector phi hunit) = 1 := by
  let M := ksgnsRightInnerModuleData phi
  let r := ksgnsOrderUnitInvSqrt phi hunit
  let s := CFC.sqrt (phi 1)
  let h := phi 1
  have hpos : 0 ≤ h := map_nonneg phi (by
    simpa using star_mul_self_nonneg (1 : A))
  have hsquare : s * s = h := by
    simpa only [pow_two] using CFC.sq_sqrt h hpos
  have hrs : r * s = 1 := ksgnsOrderUnitInvSqrt_mul_sqrt phi hunit
  have hsr : s * r = 1 := sqrt_mul_ksgnsOrderUnitInvSqrt phi hunit
  have hrstar : star r = r := star_ksgnsOrderUnitInvSqrt phi hunit
  change M.inner (M.rmul (ksgnsCyclic phi) r)
      (M.rmul (ksgnsCyclic phi) r) = 1
  rw [M.inner_rmul_right, M.inner_rmul_left,
    ksgnsRight_inner_cyclic_cyclic, hrstar]
  change r * h * r = 1
  rw [← hsquare]
  calc
    r * (s * s) * r = (r * s) * (s * r) := by simp only [mul_assoc]
    _ = 1 := by rw [hrs, hsr, one_mul]

/-- Rank-one module operator `θ_{v,v} : z ↦ v ⟨v,z⟩`. -/
noncomputable def ksgnsRankOneSelf (phi : A →CP B) (v : KSGNS phi) :
    KSGNS phi →L[ℂ] KSGNS phi :=
  (ksgnsCoefficientToVector phi v).comp (ksgnsCompletedInnerSLM phi v)

@[simp]
theorem ksgnsRankOneSelf_apply (phi : A →CP B) (v z : KSGNS phi) :
    ksgnsRankOneSelf phi v z =
      MulOpposite.op ((ksgnsRightInnerModuleData phi).inner v z) • v := rfl

/-- Weighted cyclic-line projection is exactly `θ_{η,η}`. -/
theorem ksgnsWeightedProjection_eq_rankOne_unitVector (phi : A →CP B)
    (hunit : IsUnit (phi 1)) :
    ksgnsWeightedProjection phi hunit =
      ksgnsRankOneSelf phi (ksgnsWeightedUnitVector phi hunit) := by
  ext z
  let M := ksgnsRightInnerModuleData phi
  let r := ksgnsOrderUnitInvSqrt phi hunit
  let g := ksgnsOrderUnitInv phi hunit
  let c := M.inner (ksgnsCyclic phi) z
  have hrstar : star r = r := star_ksgnsOrderUnitInvSqrt phi hunit
  have hrr : r * r = g := ksgnsOrderUnitInvSqrt_sq phi hunit
  rw [ksgnsWeightedProjection_apply, ksgnsRankOneSelf_apply]
  change M.rmul (ksgnsCyclic phi) (g * c) =
    M.rmul (M.rmul (ksgnsCyclic phi) r)
      (M.inner (M.rmul (ksgnsCyclic phi) r) z)
  rw [M.inner_rmul_left, hrstar, M.rmul_mul]
  congr 1
  rw [← mul_assoc, hrr]

/-! ## Dense-core range of a continuous projection complement -/

section ContinuousProjection

variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [AddCommGroup C] [Module ℂ C]

/-- Continuous complement `1-P` of a continuous linear projection. -/
def continuousProjectionComplement (P : E →L[ℂ] E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - P

@[simp]
theorem continuousProjectionComplement_apply (P : E →L[ℂ] E) (x : E) :
    continuousProjectionComplement P x = x - P x := rfl

/-- The complement of an idempotent projection, with codomain restricted to its kernel. -/
def continuousProjectionKernelMap (P : E →L[ℂ] E)
    (hP : ∀ x, P (P x) = P x) :
    E →L[ℂ] LinearMap.ker P.toLinearMap :=
  (continuousProjectionComplement P).codRestrict
    (LinearMap.ker P.toLinearMap) (by
      intro x
      change P (x - P x) = 0
      rw [map_sub, hP, sub_self])

theorem continuousProjectionKernelMap_surjective (P : E →L[ℂ] E)
    (hP : ∀ x, P (P x) = P x) :
    Function.Surjective (continuousProjectionKernelMap P hP) := by
  intro x
  refine ⟨(x : E), Subtype.ext ?_⟩
  change (x : E) - P x = x
  rw [show P x = 0 from x.property, sub_zero]

/-- Applying a continuous projection complement to a dense algebraic core fills exactly the
closed kernel of the projection. -/
theorem topologicalClosure_range_projectionComplement_comp_eq_ker
    (P : E →L[ℂ] E) (hP : ∀ x, P (P x) = P x)
    (J : C →ₗ[ℂ] E) (hJ : DenseRange J) :
    (LinearMap.range
        ((continuousProjectionComplement P).toLinearMap.comp J)).topologicalClosure =
      LinearMap.ker P.toLinearMap := by
  let K : Submodule ℂ E := LinearMap.ker P.toLinearMap
  let PK : E →L[ℂ] K := continuousProjectionKernelMap P hP
  let S₀ : C →ₗ[ℂ] K := PK.toLinearMap.comp J
  have hS₀ : DenseRange S₀ :=
    (continuousProjectionKernelMap_surjective P hP).denseRange.comp hJ PK.continuous
  have htop : (LinearMap.range S₀).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hS₀
  have hmap := (LinearMap.range S₀).topologicalClosure_map K.subtypeL
  have hrange_map_le :
      (LinearMap.range S₀).map K.subtype ≤
        LinearMap.range ((continuousProjectionComplement P).toLinearMap.comp J) := by
    rintro y ⟨z, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  have hK_le : K ≤
      (LinearMap.range
        ((continuousProjectionComplement P).toLinearMap.comp J)).topologicalClosure := by
    intro x hx
    have hxmap : x ∈ (⊤ : Submodule ℂ K).map K.subtype :=
      ⟨⟨x, hx⟩, Submodule.mem_top, rfl⟩
    rw [← htop] at hxmap
    have hxclosure : x ∈
        ((LinearMap.range S₀).map K.subtype).topologicalClosure := hmap hxmap
    exact Submodule.topologicalClosure_mono hrange_map_le hxclosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨c, rfl⟩
      change P (J c - P (J c)) = 0
      rw [map_sub, hP, sub_self]
    · exact P.isClosed_ker
  · exact hK_le

end ContinuousProjection

/-! ## Exact centered-complement span -/

theorem ksgnsWeightedProjection_op_smul (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (b : B) (z : KSGNS phi) :
    ksgnsWeightedProjection phi hunit (MulOpposite.op b • z) =
      MulOpposite.op b • ksgnsWeightedProjection phi hunit z := by
  let M := ksgnsRightInnerModuleData phi
  let g := ksgnsOrderUnitInv phi hunit
  let c := M.inner (ksgnsCyclic phi) z
  rw [ksgnsWeightedProjection_apply, ksgnsWeightedProjection_apply]
  change M.rmul (ksgnsCyclic phi)
      (g * M.inner (ksgnsCyclic phi) (M.rmul z b)) =
    M.rmul (M.rmul (ksgnsCyclic phi) (g * c)) b
  rw [M.inner_rmul_right, M.rmul_mul]
  congr 1
  dsimp [c]
  simp only [mul_assoc]

/-- Complex span of all right-coefficient multiples of weighted centered KSGNS vectors. -/
def ksgnsWeightedCenteredSpan (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    Submodule ℂ (KSGNS phi) :=
  Submodule.span ℂ {z | ∃ (a : A) (b : B),
    z = MulOpposite.op b • ksgnsWeightedCentered phi hunit a}

/-- On a cyclic generator, `1-P` is exactly the coefficient multiple of the weighted centered
vector. -/
theorem continuousProjectionComplement_weightedProjection_cyclicGenerator
    (phi : A →CP B) (hunit : IsUnit (phi 1)) (a : A) (b : B) :
    continuousProjectionComplement (ksgnsWeightedProjection phi hunit)
        (MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi)) =
      MulOpposite.op b • ksgnsWeightedCentered phi hunit a := by
  rw [continuousProjectionComplement_apply, ksgnsWeightedProjection_op_smul,
    ← smul_sub, ksgnsWeightedCentered_eq_one_sub_projection]

theorem range_projectionComplement_cyclicSpan_eq_weightedCenteredSpan
    (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    LinearMap.range
        ((continuousProjectionComplement (ksgnsWeightedProjection phi hunit)).toLinearMap.comp
          (ksgnsCyclicSpan phi).subtype) =
      ksgnsWeightedCenteredSpan phi hunit := by
  apply le_antisymm
  · rintro z ⟨u, rfl⟩
    change continuousProjectionComplement (ksgnsWeightedProjection phi hunit) (u : KSGNS phi) ∈
      ksgnsWeightedCenteredSpan phi hunit
    exact Submodule.span_induction (p := fun u _ =>
        continuousProjectionComplement (ksgnsWeightedProjection phi hunit) u ∈
          ksgnsWeightedCenteredSpan phi hunit)
      (by
        rintro u _
        rcases ‹u ∈ {z | ∃ (a : A) (b : B),
          z = MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi)}› with
          ⟨a, b, rfl⟩
        rw [continuousProjectionComplement_weightedProjection_cyclicGenerator]
        exact Submodule.subset_span ⟨a, b, rfl⟩)
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      (fun q x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ q hx)
      u.property
  · unfold ksgnsWeightedCenteredSpan
    rw [Submodule.span_le]
    rintro z ⟨a, b, rfl⟩
    let u : ksgnsCyclicSpan phi :=
      ⟨MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi),
        Submodule.subset_span ⟨a, b, rfl⟩⟩
    refine ⟨u, ?_⟩
    exact continuousProjectionComplement_weightedProjection_cyclicGenerator
      phi hunit a b

/-- Equation (3): the closed centered span is exactly `(1-P)E`, represented intrinsically as
the closed kernel of the orthogonal projection `P`. -/
theorem ksgnsWeightedCenteredSpan_topologicalClosure_eq_projectionKer
    (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    (ksgnsWeightedCenteredSpan phi hunit).topologicalClosure =
      LinearMap.ker (ksgnsWeightedProjection phi hunit).toLinearMap := by
  rw [← range_projectionComplement_cyclicSpan_eq_weightedCenteredSpan]
  apply topologicalClosure_range_projectionComplement_comp_eq_ker
  · exact ksgnsWeightedProjection_idempotent phi hunit
  · have hrange : Set.range (ksgnsCyclicSpan phi).subtype =
        (ksgnsCyclicSpan phi : Set (KSGNS phi)) := Subtype.range_coe
    rw [DenseRange, hrange]
    exact dense_ksgnsCyclicSpan phi

end GaloisForLFunctions.HTGeometry
