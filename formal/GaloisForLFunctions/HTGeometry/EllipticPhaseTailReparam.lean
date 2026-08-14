import GaloisForLFunctions.HTGeometry.EllipticRotationTail

/-!
# The phase tail of an elliptic protocol on the reparametrised carrier

The phase field of a compact parabolic signature is the elliptic functions of the phase together
with the jets of the reparametrisation.  A deck translation of a given depth fixes the elliptic
functions of that depth and fixes every jet, hence fixes the whole phase field of that depth.

An element lying in the phase field of every depth is therefore invariant under every deck
translation of every depth, so it lies in the Maurer–Cartan velocity field; conversely every jet
lies in every phase field.  The phase tail is exactly the velocity field, and with the rotation it
is the power current field of the signature.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- The phase field: the elliptic functions of a phase together with the reparametrisation jets. -/
noncomputable def baseAdjoinJets (S : IntermediateField ℂ MeromorphicPlane) :
    IntermediateField ℂ (ReparamField MeromorphicPlane) :=
  IntermediateField.adjoin ℂ
    ((algebraMap MeromorphicPlane (ReparamField MeromorphicPlane)) '' (S : Set MeromorphicPlane)
      ∪ Set.range (ReparamField.jet : ℕ → ReparamField MeromorphicPlane))

theorem jet_mem_baseAdjoinJets (S : IntermediateField ℂ MeromorphicPlane) (i : ℕ) :
    (ReparamField.jet i : ReparamField MeromorphicPlane) ∈ baseAdjoinJets S :=
  IntermediateField.subset_adjoin ℂ _ (Or.inr ⟨i, rfl⟩)

/-- The velocity field lies in every phase field. -/
theorem velocityField_le_baseAdjoinJets (S : IntermediateField ℂ MeromorphicPlane) :
    velocityField ≤ baseAdjoinJets S := by
  rw [velocityField_eq_adjoin_range_jet]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro y ⟨i, rfl⟩
  exact jet_mem_baseAdjoinJets S i

/-- The elements of the reparametrisation fixed by one deck translation. -/
noncomputable def translationFixedField (t : ℂ) :
    IntermediateField ℂ (ReparamField MeromorphicPlane) where
  carrier := {x : ReparamField MeromorphicPlane |
    ReparamField.fieldEquiv (planeTranslateEquiv t) x = x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    show ReparamField.fieldEquiv (planeTranslateEquiv t) (x + y) = x + y
    rw [map_add, hx, hy]
  mul_mem' := by
    intro x y hx hy
    show ReparamField.fieldEquiv (planeTranslateEquiv t) (x * y) = x * y
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    show ReparamField.fieldEquiv (planeTranslateEquiv t) x⁻¹ = x⁻¹
    rw [map_inv₀, hx]
  algebraMap_mem' := by
    intro c
    show ReparamField.fieldEquiv (planeTranslateEquiv t)
      (algebraMap ℂ (ReparamField MeromorphicPlane) c) = _
    have htower : algebraMap ℂ (ReparamField MeromorphicPlane) c
        = algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (constPlane c) := by
      rw [IsScalarTower.algebraMap_apply ℂ MeromorphicPlane (ReparamField MeromorphicPlane)]
      rfl
    rw [htower, ReparamField.fieldEquiv_base, planeTranslateEquiv_apply,
      planeTranslate_constPlane]

theorem mem_translationFixedField_iff (t : ℂ) {x : ReparamField MeromorphicPlane} :
    x ∈ translationFixedField t
      ↔ ReparamField.fieldEquiv (planeTranslateEquiv t) x = x := Iff.rfl

/-- **A deck translation of a phase fixes the whole phase field.** -/
theorem baseAdjoinJets_le_translationFixedField {S : IntermediateField ℂ MeromorphicPlane}
    {t : ℂ} (hS : ∀ a ∈ S, planeTranslate t a = a) :
    baseAdjoinJets S ≤ translationFixedField t := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro y (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
  · show ReparamField.fieldEquiv (planeTranslateEquiv t)
      (algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) a) = _
    rw [ReparamField.fieldEquiv_base, planeTranslateEquiv_apply, hS a ha]
  · exact ReparamField.fieldEquiv_jet (planeTranslateEquiv t) i

/-- **The phase tail of an elliptic protocol is the velocity field.**  An element lying in the
phase field of every depth is invariant under every deck translation of every depth, hence lies in
the Maurer–Cartan velocity field; and the velocity field lies in every phase field. -/
theorem iInter_baseAdjoinJets_eq_velocityField (Λ : PeriodPair) (M : ℕ → ℂ)
    (hM : ∀ k, M k ≠ 0) (hMinf : Tendsto (fun k => ‖M k‖) atTop atTop)
    (S : ℕ → IntermediateField ℂ MeromorphicPlane)
    (hS : ∀ k : ℕ, ∀ t : ℂ, M k * t ∈ Λ.lattice → ∀ a ∈ S k, planeTranslate t a = a) :
    {x : ReparamField MeromorphicPlane | ∀ k : ℕ, x ∈ baseAdjoinJets (S k)}
      = (velocityField : Set (ReparamField MeromorphicPlane)) := by
  ext x
  constructor
  · intro hx
    rw [← deckInvariantField_eq_velocityField Λ M hM hMinf]
    intro k t ht
    exact baseAdjoinJets_le_translationFixedField (hS k t ht) (hx k)
  · intro hx k
    exact velocityField_le_baseAdjoinJets (S k) hx

/-- **The phase tail of a compact parabolic signature.**  With the rotation of exact order `n`, the
phase tail of a degree-expanding elliptic protocol is the power current field `C⟨(u′)ⁿ⟩`. -/
theorem iInter_baseAdjoinJets_rotation_eq_differentialAdjoin_jetPow (Λ : PeriodPair) (M : ℕ → ℂ)
    (hM : ∀ k, M k ≠ 0) (hMinf : Tendsto (fun k => ‖M k‖) atTop atTop)
    (S : ℕ → IntermediateField ℂ MeromorphicPlane)
    (hS : ∀ k : ℕ, ∀ t : ℂ, M k * t ∈ Λ.lattice → ∀ a ∈ S k, planeTranslate t a = a)
    {ζ : ℂˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n) :
    {x : ReparamField MeromorphicPlane |
        (∀ k : ℕ, x ∈ baseAdjoinJets (S k)) ∧ rotationEquiv (Units.ne_zero ζ) x = x}
      = (differentialAdjoin ℂ ({(ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n} : Set _)
          : Set _) := by
  have hbase := iInter_baseAdjoinJets_eq_velocityField Λ M hM hMinf S hS
  ext x
  constructor
  · rintro ⟨hxt, hxρ⟩
    have hxV : x ∈ velocityField := by
      have : x ∈ {y : ReparamField MeromorphicPlane | ∀ k : ℕ, y ∈ baseAdjoinJets (S k)} := hxt
      rwa [hbase] at this
    exact mem_differentialAdjoin_jetPow_of_rotation_invariant hn hord hxV hxρ
  · intro hx
    have hpow : ((ζ : ℂˣ) : ℂ) ^ n = 1 := by
      have h1 := pow_orderOf_eq_one ζ
      rw [hord] at h1
      calc ((ζ : ℂˣ) : ℂ) ^ n = ((ζ ^ n : ℂˣ) : ℂ) := (Units.val_pow_eq_pow_val ζ n).symm
        _ = ((1 : ℂˣ) : ℂ) := by rw [h1]
        _ = 1 := Units.val_one
    have hxV : x ∈ velocityField := differentialAdjoin_jetPow_le_velocityField n hx
    refine ⟨?_, rotation_fixes_jetPow (Units.ne_zero ζ) hpow hx⟩
    have hmem : x ∈ {y : ReparamField MeromorphicPlane | ∀ k : ℕ, y ∈ baseAdjoinJets (S k)} := by
      rw [hbase]
      exact hxV
    exact hmem

end GaloisForLFunctions.HTGeometry
