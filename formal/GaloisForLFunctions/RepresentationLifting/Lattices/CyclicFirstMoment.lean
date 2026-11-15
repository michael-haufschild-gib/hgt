import GaloisForLFunctions.RepresentationLifting.CyclicMovingCoinvariants

/-!
# First moments in the integral cyclic moving lattice

Send each regular basis vector at `g` to `g` in the additive form of the group.
Translation by `s` changes this moment by augmentation times `s`. Consequently
the moment vanishes on cyclic differences of augmentation-zero vectors.

For a finite cyclic group, this is the complete obstruction: the restricted
difference image is exactly the first-moment kernel, and its quotient is
canonically the additive group `G`. This makes the integral comparison of
Auel–Shaikh, Lemma 1.3 (https://arxiv.org/abs/2611.13468), explicit in regular
coordinates. A difference of two distinct regular basis vectors has nonzero
moment and therefore cannot belong to the restricted difference image.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (G : Type) [CommGroup G]

/-- The group-valued first moment of an integral regular vector. -/
def cyclicFirstMoment : CyclicRegular ℤ G →ₗ[ℤ] Additive G :=
  (MonoidAlgebra.basis G ℤ).constr ℤ (fun g => Additive.ofMul g)

/-- A regular basis vector has first moment equal to its group label. -/
theorem cyclicFirstMoment_single (g : G) :
    cyclicFirstMoment G (MonoidAlgebra.single g 1) = Additive.ofMul g := by
  change ((MonoidAlgebra.basis G ℤ).constr ℤ (fun h => Additive.ofMul h))
    ((MonoidAlgebra.basis G ℤ) g) = _
  rw [Module.Basis.constr_basis]

variable [Fintype G]

/-- Translation changes the first moment by augmentation times the translating element. -/
theorem cyclicFirstMoment_translate (g : G) (v : CyclicRegular ℤ G) :
    cyclicFirstMoment G (Representation.leftRegular ℤ G g v) =
      cyclicFirstMoment G v + cyclicAugmentation ℤ G v • Additive.ofMul g := by
  have hmap : (cyclicFirstMoment G).comp (Representation.leftRegular ℤ G g) =
      cyclicFirstMoment G + (cyclicAugmentation ℤ G).smulRight (Additive.ofMul g) := by
    apply (MonoidAlgebra.basis G ℤ).ext
    intro h
    simp only [MonoidAlgebra.basis_apply, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smulRight_apply]
    rw [show Representation.leftRegular ℤ G g (MonoidAlgebra.single h 1) =
        MonoidAlgebra.single (g * h) 1 from
      Representation.ofMulAction_single (k := ℤ) (G := G) (H := G) g h 1]
    rw [cyclicFirstMoment_single G (g * h), cyclicFirstMoment_single G h,
      cyclicAugmentation_single ℤ G h 1, one_smul]
    change Additive.ofMul g + Additive.ofMul h = Additive.ofMul h + Additive.ofMul g
    exact add_comm _ _
  exact LinearMap.congr_fun hmap v

variable [IsCyclic G]

/-- The first moment of a cyclic difference records the augmentation of its preimage. -/
theorem cyclicFirstMoment_delta (v : CyclicRegular ℤ G) :
    cyclicFirstMoment G (cyclicRegularDelta ℤ G v) =
      cyclicAugmentation ℤ G v • Additive.ofMul (cyclicRegularGenerator G) := by
  change cyclicFirstMoment G
    (Representation.leftRegular ℤ G (cyclicRegularGenerator G) v - v) = _
  rw [map_sub, cyclicFirstMoment_translate]
  abel

/-- First moment restricted to the norm-zero integral lattice. -/
def cyclicMovingFirstMoment : CyclicIntegralMoving G →ₗ[ℤ] Additive G :=
  (cyclicFirstMoment G).comp (CyclicIntegralMoving G).subtype

/-- The restricted difference image has zero first moment. -/
theorem cyclicMovingFirstMoment_delta (v : CyclicIntegralMoving G) :
    cyclicMovingFirstMoment G (cyclicMovingDelta G v) = 0 := by
  have hv : cyclicAugmentation ℤ G (v : CyclicRegular ℤ G) = 0 :=
    (cyclicRegularNorm_eq_zero_iff G v).mp v.property
  change cyclicFirstMoment G (cyclicRegularDelta ℤ G (v : CyclicRegular ℤ G)) = 0
  rw [cyclicFirstMoment_delta, hv, zero_smul]

/-- The augmentation-zero difference of two regular basis vectors. -/
def cyclicRootVector (a b : G) : CyclicIntegralMoving G :=
  ⟨MonoidAlgebra.single a 1 - MonoidAlgebra.single b 1, by
    change cyclicRegularNorm ℤ G _ = 0
    rw [cyclicRegularNorm_eq_zero_iff, map_sub,
      cyclicAugmentation_single, cyclicAugmentation_single, sub_self]⟩

omit [IsCyclic G] in
/-- The moment of a root is the difference of its two labels. -/
theorem cyclicMovingFirstMoment_root (a b : G) :
    cyclicMovingFirstMoment G (cyclicRootVector G a b) = Additive.ofMul a - Additive.ofMul b := by
  simp only [cyclicMovingFirstMoment, LinearMap.comp_apply, Submodule.subtype_apply,
    cyclicRootVector, map_sub, cyclicFirstMoment_single G a, cyclicFirstMoment_single G b]

/-- Only the zero root lies in the restricted difference image. -/
theorem cyclicRootVector_mem_range_iff (a b : G) :
    cyclicRootVector G a b ∈ LinearMap.range (cyclicMovingDelta G) ↔ a = b := by
  constructor
  · rintro ⟨v, hv⟩
    have hm := cyclicMovingFirstMoment_delta G v
    rw [hv, cyclicMovingFirstMoment_root] at hm
    have he : Additive.ofMul a = Additive.ofMul b := sub_eq_zero.mp hm
    exact congrArg Additive.toMul he
  · rintro rfl
    refine ⟨0, ?_⟩
    apply Subtype.ext
    simp [cyclicRootVector]

/-- The chosen generator has order equal to the group cardinality. -/
theorem cyclicRegularGenerator_order :
    orderOf (cyclicRegularGenerator G) = Fintype.card G := by
  have htop : Subgroup.zpowers (cyclicRegularGenerator G) = ⊤ := by
    apply top_unique
    intro g _
    exact cyclicRegularGenerator_generates G g
  simpa only [Nat.card_eq_fintype_card] using orderOf_eq_card_of_zpowers_eq_top htop

/-- The difference moment vanishes exactly when the preimage augmentation is divisible by the group order. -/
theorem cyclicFirstMoment_delta_zero_iff (v : CyclicRegular ℤ G) :
    cyclicFirstMoment G (cyclicRegularDelta ℤ G v) = 0 ↔
      (Fintype.card G : ℤ) ∣ cyclicAugmentation ℤ G v := by
  rw [cyclicFirstMoment_delta]
  change (cyclicRegularGenerator G) ^ (cyclicAugmentation ℤ G v) = 1 ↔ _
  rw [← orderOf_dvd_iff_zpow_eq_one, cyclicRegularGenerator_order]

/-- The first moment is the complete obstruction to being a difference of a moving vector. -/
theorem cyclicMovingDelta_range_eq_firstMoment_ker :
    LinearMap.range (cyclicMovingDelta G) = (cyclicMovingFirstMoment G).ker := by
  ext v
  change v ∈ LinearMap.range (cyclicMovingDelta G) ↔ cyclicMovingFirstMoment G v = 0
  constructor
  · rintro ⟨w, rfl⟩
    exact cyclicMovingFirstMoment_delta G w
  · intro hv
    have hvnorm : (v : CyclicRegular ℤ G) ∈ LinearMap.range (cyclicRegularDelta ℤ G) := by
      rw [cyclicRegular_delta_norm_exact]
      exact v.property
    obtain ⟨x, hx⟩ := hvnorm
    have hm : cyclicFirstMoment G (cyclicRegularDelta ℤ G x) = 0 := by
      rw [hx]
      exact hv
    have hdiv := (cyclicFirstMoment_delta_zero_iff G x).mp hm
    have hglue := (mem_cyclicIntegralGluingSubmodule_iff G x).mpr hdiv
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hglue
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change cyclicRegularDelta ℤ G w = (v : CyclicRegular ℤ G)
    rw [← hx, ← hsum, map_add, hu, zero_add]

omit [IsCyclic G] in
/-- Every group label occurs as the first moment of a moving vector. -/
theorem cyclicMovingFirstMoment_surjective : Function.Surjective (cyclicMovingFirstMoment G) := by
  intro g
  refine ⟨cyclicRootVector G g.toMul 1, ?_⟩
  rw [cyclicMovingFirstMoment_root]
  change g - 0 = g
  exact sub_zero g

/-- The moving coinvariant group is identified with `G` by its first moment. -/
def cyclicMovingMomentEquiv : CyclicMovingCoinvariants G ≃ₗ[ℤ] Additive G :=
  (Submodule.quotEquivOfEq _ _ (cyclicMovingDelta_range_eq_firstMoment_ker G)).trans
    ((cyclicMovingFirstMoment G).quotKerEquivOfSurjective (cyclicMovingFirstMoment_surjective G))

/-- The quotient class of a root is explicitly its difference of labels. -/
theorem cyclicMovingMomentEquiv_root (a b : G) :
    cyclicMovingMomentEquiv G ((LinearMap.range (cyclicMovingDelta G)).mkQ (cyclicRootVector G a b)) =
      Additive.ofMul a - Additive.ofMul b := by
  change cyclicMovingFirstMoment G (cyclicRootVector G a b) = _
  exact cyclicMovingFirstMoment_root G a b

#print axioms cyclicMovingDelta_range_eq_firstMoment_ker
#print axioms cyclicMovingMomentEquiv
#print axioms cyclicFirstMoment_delta
#print axioms cyclicRootVector_mem_range_iff

end GaloisForLFunctions.RepresentationLifting
