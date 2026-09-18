import GaloisForLFunctions.RHTower.MaassRationalHeckeIntegralCoverL2Scaling

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The determinant-one rational conjugate is multiplicatively equivalent to its
GL source; the inverse is obtained from the proved surjectivity of `toGL`. -/
noncomputable def rationalConjugateSL2ToGLEquiv (N : ℕ) (g : GL (Fin 2) ℚ) :
    rationalConjugateSL2Group N g ≃* rationalConjugateGroup N g := by
  let f : rationalConjugateSL2Group N g →* rationalConjugateGroup N g :=
    { toFun := fun x => ⟨Matrix.SpecialLinearGroup.toGL x.val, x.property⟩
      map_one' := by
        apply Subtype.ext
        exact map_one Matrix.SpecialLinearGroup.toGL
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul Matrix.SpecialLinearGroup.toGL x.val y.val }
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxeq⟩ :=
      show y.val ∈ (rationalConjugateSL2Group N g).map Matrix.SpecialLinearGroup.toGL from
        (rationalConjugateSL2Group_map_toGL N g).symm ▸ y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxeq⟩
  let inv : rationalConjugateGroup N g → rationalConjugateSL2Group N g :=
    fun y => Classical.choose (hsurj y)
  have hinv : ∀ y, f (inv y) = y := fun y => Classical.choose_spec (hsurj y)
  exact
    { toFun := f
      invFun := inv
      left_inv := by
        intro x
        apply Subtype.ext
        apply Matrix.SpecialLinearGroup.toGL_injective
        exact congrArg Subtype.val (hinv (f x))
      right_inv := hinv
      map_mul' := f.map_mul }

/-- Under the restricted `toGL` equivalence, the principal intersection is
exactly the GL relative-intersection subgroup. -/
theorem rationalConjugateSL2_principalIntersection_map_eq (N : ℕ) (g : GL (Fin 2) ℚ) :
    Subgroup.map (rationalConjugateSL2ToGLEquiv N g).toMonoidHom
      ((realImage (CongruenceSubgroup.Gamma (N + 1))).subgroupOf
        (rationalConjugateSL2Group N g)) =
      (principalCongruenceGL N).subgroupOf (rationalConjugateGroup N g) := by
  let e := rationalConjugateSL2ToGLEquiv N g
  let Psl := realImage (CongruenceSubgroup.Gamma (N + 1))
  let Rsl := rationalConjugateSL2Group N g
  let Pgl := principalCongruenceGL N
  let Rgl := rationalConjugateGroup N g
  have hP : Pgl.comap Matrix.SpecialLinearGroup.toGL = Psl :=
    principalCongruenceGL_comap_sl2ToGL N
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    change y.val ∈ Pgl
    rw [← hxy]
    have hxP : x.val ∈ Psl := hx
    rw [← hP] at hxP
    exact hxP
  · intro hy
    obtain ⟨x, hx⟩ := e.surjective y
    refine ⟨x, ?_, hx⟩
    change x.val ∈ Psl
    rw [← hP]
    change (e x).val ∈ Pgl
    rw [hx]
    exact hy

private theorem finiteIndex_of_map_eq_under_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (S : Subgroup G) (T : Subgroup H) (hST : S.map e.toMonoidHom = T)
    [T.FiniteIndex] : S.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  let q : G ⧸ S ≃ H ⧸ T := Quotient.congr e.toEquiv (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    have hmem (x : G) : x ∈ S ↔ e x ∈ T := by
      rw [← hST]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hey⟩
        exact e.injective hey.symm ▸ hy
    change a⁻¹ * b ∈ S ↔ (e a)⁻¹ * e b ∈ T
    rw [← e.map_inv, ← e.map_mul]
    exact hmem (a⁻¹ * b))
  exact Finite.of_equiv _ q.symm

/-- The principal determinant-one subgroup has finite relative index in every
rational conjugate determinant-one source. -/
theorem principalSL2_isFiniteRelIndex_rationalConjugateSL2
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    (realImage (CongruenceSubgroup.Gamma (N + 1))).IsFiniteRelIndex
      (rationalConjugateSL2Group N g) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  let Psl := realImage (CongruenceSubgroup.Gamma (N + 1))
  let Rsl := rationalConjugateSL2Group N g
  let Pgl := principalCongruenceGL N
  let Rgl := rationalConjugateGroup N g
  letI : Pgl.IsFiniteRelIndex Rgl :=
    ⟨(rationalConjugateGroup_commensurable N g).2⟩
  exact finiteIndex_of_map_eq_under_mulEquiv
    (rationalConjugateSL2ToGLEquiv N g) (Psl.subgroupOf Rsl) (Pgl.subgroupOf Rgl)
    (rationalConjugateSL2_principalIntersection_map_eq N g)

/-- The integral common cover has finite relative index in the determinant-one
rational-conjugate source. -/
theorem realImage_rationalHeckeIntegralIntersection_isFiniteRelIndex_conjugate
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    (realImage (rationalHeckeIntegralIntersection N g)).IsFiniteRelIndex
      (rationalConjugateSL2Group N g) := by
  rw [realImage_rationalHeckeIntegralIntersection]
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  let P := realImage (CongruenceSubgroup.Gamma (N + 1))
  let R := rationalConjugateSL2Group N g
  have hsub : (P ⊓ R).subgroupOf R = P.subgroupOf R := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, x.property⟩
  rw [hsub]
  exact (Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
    (principalSL2_isFiniteRelIndex_rationalConjugateSL2 N g))

/-- The rational-conjugate determinant-one source is discrete, because its
integral common cover is discrete and finite-index. -/
theorem rationalConjugateSL2Group_discreteTopology (N : ℕ) (g : GL (Fin 2) ℚ) :
    DiscreteTopology (rationalConjugateSL2Group N g) := by
  let K := realImage (rationalHeckeIntegralIntersection N g)
  let R := rationalConjugateSL2Group N g
  letI : K.IsFiniteRelIndex R :=
    realImage_rationalHeckeIntegralIntersection_isFiniteRelIndex_conjugate N g
  have hKR : K ≤ R := by
    change realImage (rationalHeckeIntegralIntersection N g) ≤ rationalConjugateSL2Group N g
    rw [realImage_rationalHeckeIntegralIntersection]
    exact inf_le_right
  exact (Subgroup.discreteTopology_iff_of_isFiniteRelIndex hKR).mp inferInstance

instance rationalConjugateSL2Group_discreteTopology_instance (N : ℕ) (g : GL (Fin 2) ℚ) :
    DiscreteTopology (rationalConjugateSL2Group N g) :=
  rationalConjugateSL2Group_discreteTopology N g

end

end GaloisForLFunctions.RHTower
