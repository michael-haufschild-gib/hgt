import GaloisForLFunctions.RHTower.IntegralSubgroupFiniteCoverDecomposition

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

/-- A finite union of right translates of a `Γ` fundamental set, indexed by
right cosets of `K` in `Γ`. The inverse representatives produce the left
factorization required for the `K` action. -/
def integralFiniteCoverFundamentalSet (K Γ : Subgroup SL2Z) : Set SL2R :=
  ⋃ q : Γ ⧸ K.subgroupOf Γ,
    MulOpposite.op (integralSL2ToReal q.out.val) • integralSubgroupFundamentalSet Γ

/-- The finite-cover selector is measurable. -/
theorem integralFiniteCoverFundamentalSet_measurable (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] :
    MeasurableSet (integralFiniteCoverFundamentalSet K Γ) := by
  letI : Fintype (Γ ⧸ K.subgroupOf Γ) := Fintype.ofFinite _
  apply MeasurableSet.iUnion
  intro q
  exact (integralSubgroupFundamentalSet_measurable Γ).const_smul _

/-- The finite union is a fundamental selector for the smaller subgroup. -/
theorem integralFiniteCoverFundamentalSet_unique (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) (x : SL2R) :
    ∃! k : (realImage K).op, k • x ∈ integralFiniteCoverFundamentalSet K Γ := by
  obtain ⟨γ, hγ, hγuniq⟩ := integralSubgroupFundamentalSet_unique Γ x
  have hγmem : γ.val.unop ∈ realImage Γ := γ.property
  rcases hγmem with ⟨a, ha, haeq⟩
  let A : Γ := ⟨a, ha⟩
  have hγeq : γ.val.unop = integralSL2ToReal A.val := by
    exact haeq.symm
  obtain ⟨k, q, hA⟩ := subgroup_exists_left_coset_decomposition K Γ hKΓ A
  let kR : (realImage K).op := ⟨MulOpposite.op (integralSL2ToReal k.val), by
    change integralSL2ToReal k.val ∈ realImage K
    exact ⟨k.val, k.property, rfl⟩⟩
  refine ⟨kR, ?_, ?_⟩
  · refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    refine Set.mem_smul_set.mpr ⟨γ • x, hγ, ?_⟩
    have hAreal : integralSL2ToReal A.val =
        integralSL2ToReal k.val * (integralSL2ToReal q.out.val)⁻¹ := by
      have h := congrArg (fun B : Γ => integralSL2ToReal B.val) hA
      change integralSL2ToReal A.val =
        integralSL2ToReal (k.val * q.out.val⁻¹) at h
      simpa only [map_mul, map_inv] using h
    change (γ • x) * integralSL2ToReal q.out.val = x * integralSL2ToReal k.val
    change (x * γ.val.unop) * integralSL2ToReal q.out.val =
      x * integralSL2ToReal k.val
    rw [hγeq, hAreal]
    group
  · intro k' hk'
    rcases Set.mem_iUnion.mp hk' with ⟨q', hq'⟩
    rcases Set.mem_smul_set.mp hq' with ⟨y, hy, hEq⟩
    have hk'mem : k'.val.unop ∈ realImage K := k'.property
    rcases hk'mem with ⟨b, hb, hbeq⟩
    let B : K := ⟨b, hb⟩
    let δ : (realImage Γ).op :=
      ⟨MulOpposite.op (integralSL2ToReal B.val *
        (integralSL2ToReal q'.out.val)⁻¹), by
        change integralSL2ToReal B.val *
          (integralSL2ToReal q'.out.val)⁻¹ ∈ realImage Γ
        refine ⟨(Subgroup.inclusion hKΓ B) * q'.out⁻¹, ?_, ?_⟩
        · exact ((Subgroup.inclusion hKΓ B) * q'.out⁻¹).property
        · have hqinv : integralSL2ToReal (q'.out⁻¹).val =
              (integralSL2ToReal q'.out.val)⁻¹ := by
            change integralSL2ToReal (q'.out.val⁻¹) =
              (integralSL2ToReal q'.out.val)⁻¹
            exact map_inv _ _
          calc
            integralSL2ToReal (((Subgroup.inclusion hKΓ B) * q'.out⁻¹).val) =
                integralSL2ToReal (Subgroup.inclusion hKΓ B).val *
                  integralSL2ToReal (q'.out⁻¹).val := by
              change integralSL2ToReal
                ((Subgroup.inclusion hKΓ B).val * (q'.out⁻¹).val) = _
              exact map_mul integralSL2ToReal _ _
            _ = integralSL2ToReal B.val *
                  (integralSL2ToReal q'.out.val)⁻¹ := by
              rw [hqinv]
              rfl⟩
    have hδ : δ • x = y := by
      change y * integralSL2ToReal q'.out.val = x * k'.val.unop at hEq
      change x * (integralSL2ToReal B.val *
        (integralSL2ToReal q'.out.val)⁻¹) = y
      calc
        x * (integralSL2ToReal B.val *
            (integralSL2ToReal q'.out.val)⁻¹) =
            (x * integralSL2ToReal B.val) *
              (integralSL2ToReal q'.out.val)⁻¹ := by group
        _ = (y * integralSL2ToReal q'.out.val) *
              (integralSL2ToReal q'.out.val)⁻¹ := by rw [hbeq, ← hEq]
        _ = y := by group
    have hδmem : δ • x ∈ integralSubgroupFundamentalSet Γ := hδ ▸ hy
    have hδeq : δ = γ := hγuniq δ hδmem
    have hδreal : integralSL2ToReal B.val *
        (integralSL2ToReal q'.out.val)⁻¹ = γ.val.unop := by
      exact congrArg (fun z : (realImage Γ).op => z.val.unop) hδeq
    have hAreal : integralSL2ToReal A.val =
        integralSL2ToReal k.val * (integralSL2ToReal q.out.val)⁻¹ := by
      have h := congrArg (fun C : Γ => integralSL2ToReal C.val) hA
      change integralSL2ToReal A.val =
        integralSL2ToReal (k.val * q.out.val⁻¹) at h
      simpa only [map_mul, map_inv] using h
    have hRealEq : integralSL2ToReal B.val *
        (integralSL2ToReal q'.out.val)⁻¹ =
          integralSL2ToReal k.val * (integralSL2ToReal q.out.val)⁻¹ := by
      calc
        integralSL2ToReal B.val * (integralSL2ToReal q'.out.val)⁻¹ =
            γ.val.unop := hδreal
        _ = integralSL2ToReal A.val := hγeq
        _ = integralSL2ToReal k.val * (integralSL2ToReal q.out.val)⁻¹ := hAreal
    have hdecomp : Subgroup.inclusion hKΓ B * q'.out⁻¹ =
        Subgroup.inclusion hKΓ k * q.out⁻¹ := by
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
      change integralSL2ToReal
          ((Subgroup.inclusion hKΓ B * q'.out⁻¹).val) =
        integralSL2ToReal ((Subgroup.inclusion hKΓ k * q.out⁻¹).val)
      have hq'inv : integralSL2ToReal (q'.out⁻¹).val =
          (integralSL2ToReal q'.out.val)⁻¹ := by
        change integralSL2ToReal (q'.out.val⁻¹) = _
        exact map_inv _ _
      have hqinv : integralSL2ToReal (q.out⁻¹).val =
          (integralSL2ToReal q.out.val)⁻¹ := by
        change integralSL2ToReal (q.out.val⁻¹) = _
        exact map_inv _ _
      calc
        integralSL2ToReal ((Subgroup.inclusion hKΓ B * q'.out⁻¹).val) =
            integralSL2ToReal (Subgroup.inclusion hKΓ B).val *
              integralSL2ToReal (q'.out⁻¹).val := by
          change integralSL2ToReal
            ((Subgroup.inclusion hKΓ B).val * (q'.out⁻¹).val) = _
          exact map_mul integralSL2ToReal _ _
        _ = integralSL2ToReal B.val *
            (integralSL2ToReal q'.out.val)⁻¹ := by
          rw [hq'inv]
          rfl
        _ = integralSL2ToReal k.val *
            (integralSL2ToReal q.out.val)⁻¹ := hRealEq
        _ = integralSL2ToReal (Subgroup.inclusion hKΓ k).val *
            integralSL2ToReal (q.out⁻¹).val := by
          rw [hqinv]
          rfl
        _ = integralSL2ToReal ((Subgroup.inclusion hKΓ k * q.out⁻¹).val) := by
          change _ = integralSL2ToReal
            ((Subgroup.inclusion hKΓ k).val * (q.out⁻¹).val)
          exact (map_mul integralSL2ToReal _ _).symm
    have hqq : q' = q :=
      subgroup_rightCoset_eq_of_left_decomposition K Γ hKΓ B k q' q hdecomp
    subst q'
    have hBk : B = k := by
      apply Subgroup.inclusion_injective hKΓ
      exact mul_right_cancel hdecomp
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change k'.val.unop = integralSL2ToReal k.val
    calc
      k'.val.unop = integralSL2ToReal B.val := hbeq.symm
      _ = integralSL2ToReal k.val := congrArg (fun C : K => integralSL2ToReal C.val) hBk

/-- The finite selector is a Haar fundamental domain for the common cover. -/
theorem integralFiniteCoverFundamentalSet_isFundamentalDomain (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    IsFundamentalDomain (realImage K).op
      (integralFiniteCoverFundamentalSet K Γ) realSL2Haar :=
  IsFundamentalDomain.mk'
    (integralFiniteCoverFundamentalSet_measurable K Γ).nullMeasurableSet
    (integralFiniteCoverFundamentalSet_unique K Γ hKΓ)

end

end GaloisForLFunctions.RHTower
