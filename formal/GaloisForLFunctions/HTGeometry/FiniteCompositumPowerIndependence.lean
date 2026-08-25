import GaloisForLFunctions.HTGeometry.CyclotomicRelativePowerBasis

/-!
# Bounded power independence after a finite coefficient extension

If `F` and `k` are finite subfields of a common characteristic-zero field, adjoining `k` to `F`
can reduce the degree of an integral element by at most `[k : ℚ]`.  Consequently, the first
`D + 1` powers stay linearly independent whenever the original degree is larger than
`[k : ℚ] * D`.
-/

open scoped IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem mem_adjoin_singleton_of_isScalarTower
    {F A E : Type*} [Field F] [Field A] [Field E]
    [Algebra F A] [Algebra A E] [Algebra F E] [IsScalarTower F A E]
    (x z : E) (hz : z ∈ IntermediateField.adjoin F {x}) :
    z ∈ IntermediateField.adjoin A {x} := by
  apply IntermediateField.adjoin_induction F
    (p := fun y _ => y ∈ IntermediateField.adjoin A {x})
    (x := z) _ _ _ _ _ hz
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact IntermediateField.subset_adjoin A _ (Set.mem_singleton x)
  · intro r
    simpa only [IsScalarTower.algebraMap_apply F A E] using
      (IntermediateField.adjoin A {x}).algebraMap_mem (algebraMap F A r)
  · intro y w hy hw hy' hw'
    exact (IntermediateField.adjoin A {x}).add_mem hy' hw'
  · intro y hy hy'
    exact (IntermediateField.adjoin A {x}).inv_mem hy'
  · intro y w hy hw hy' hw'
    exact (IntermediateField.adjoin A {x}).mul_mem hy' hw'

/-- Adjoining a finite rational coefficient field can lower a minimal-polynomial degree by at
most the degree of that coefficient field. -/
theorem minpoly_natDegree_compositum_lower_bound
    (k F : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] [FiniteDimensional ℚ F]
    (x : ℂ) (hxQ : IsIntegral ℚ x) :
    (minpoly F x).natDegree ≤
      Module.finrank ℚ k * (minpoly ↥(k ⊔ F) x).natDegree := by
  let A : IntermediateField ℚ ℂ := k ⊔ F
  change (minpoly F x).natDegree ≤
    Module.finrank ℚ k * (minpoly A x).natDegree
  let inc : F →ₐ[ℚ] A := IntermediateField.inclusion
    (show F ≤ k ⊔ F from le_sup_right)
  letI : Algebra F A := inc.toAlgebra
  letI : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F A ℂ := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ A := inferInstance
  letI : Module.Finite F A := Module.Finite.of_restrictScalars_finite ℚ F A
  have hrelative : Module.finrank F A ≤ Module.finrank ℚ k := by
    have htower := Module.finrank_mul_finrank ℚ F A
    have hsup := IntermediateField.finrank_sup_le k F
    change Module.finrank ℚ F * Module.finrank F A = Module.finrank ℚ A at htower
    change Module.finrank ℚ A ≤ Module.finrank ℚ k * Module.finrank ℚ F at hsup
    rw [← htower] at hsup
    rw [Nat.mul_comm (Module.finrank ℚ k) (Module.finrank ℚ F)] at hsup
    exact Nat.le_of_mul_le_mul_left hsup Module.finrank_pos
  let L : IntermediateField F ℂ := IntermediateField.adjoin F {x}
  let B : IntermediateField A ℂ := IntermediateField.adjoin A {x}
  have hxF : IsIntegral F x := hxQ.tower_top
  have hxA : IsIntegral A x := hxQ.tower_top
  letI : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional hxF
  letI : FiniteDimensional A B := IntermediateField.adjoin.finiteDimensional hxA
  let incFB : F →+* B := (algebraMap A B).comp inc.toRingHom
  letI : Algebra F B := incFB.toAlgebra
  letI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite F B := Module.Finite.trans A B
  have hLmem : ∀ z : ℂ, z ∈ L → z ∈ B := fun z hz =>
    mem_adjoin_singleton_of_isScalarTower x z hz
  let toB : L →ₐ[F] B :=
    { toFun := fun z => Subtype.mk z.1 (hLmem z.1 z.2)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hfin : Module.finrank F L ≤ Module.finrank F B :=
    LinearMap.finrank_le_finrank_of_injective (f := toB.toLinearMap) toB.injective
  have htowerB := Module.finrank_mul_finrank F A B
  rw [← IntermediateField.adjoin.finrank hxF,
    ← IntermediateField.adjoin.finrank hxA]
  exact hfin.trans <| by
    rw [← htowerB]
    exact Nat.mul_le_mul_right (Module.finrank A B) hrelative

/-- A bounded initial power packet survives adjoining a finite rational coefficient field. -/
theorem linearIndependent_powers_over_finite_compositum
    (k F : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] [FiniteDimensional ℚ F]
    (x : ℂ) (hxQ : IsIntegral ℚ x) (D : ℕ)
    (hlarge : Module.finrank ℚ k * D < (minpoly F x).natDegree) :
    LinearIndependent ↥(k ⊔ F) (fun e : Fin (D + 1) => x ^ (e : ℕ)) := by
  let A : IntermediateField ℚ ℂ := k ⊔ F
  change LinearIndependent A (fun e : Fin (D + 1) => x ^ (e : ℕ))
  have hdegreeBound := minpoly_natDegree_compositum_lower_bound k F x hxQ
  have hDdegree : D + 1 ≤ (minpoly A x).natDegree := by
    by_contra hnot
    have hleD : (minpoly A x).natDegree ≤ D :=
      Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot)
    have hbad : (minpoly F x).natDegree ≤ Module.finrank ℚ k * D :=
      hdegreeBound.trans (Nat.mul_le_mul_left _ hleD)
    exact (Nat.not_lt_of_ge hbad) hlarge
  have hpowers := linearIndependent_pow (K := A) x
  exact hpowers.comp (Fin.castLE hDdegree) (Fin.castLE_injective hDdegree)

end

end GaloisForLFunctions.HTGeometry
