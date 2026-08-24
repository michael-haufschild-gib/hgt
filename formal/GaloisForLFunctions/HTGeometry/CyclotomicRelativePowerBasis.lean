import GaloisForLFunctions.HTGeometry.PrimeCyclotomicTensorBasis

/-!
# Direct relative cyclotomic power bases

The field obtained by adjoining one fresh coprime-order root directly inside `ℂ` has the expected
relative degree over the preceding cyclotomic compositum.  This direct formulation avoids nested
ambient-field transports in tensor-basis arguments.
-/

open scoped IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def cyclotomicRelativeAdjoin {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (u : ι → ℂ) :
    IntermediateField (cyclotomicAdjoin s u) ℂ :=
  IntermediateField.adjoin (cyclotomicAdjoin s u) {u a}

theorem mem_cyclotomicRelativeAdjoin_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (u : ι → ℂ) (z : ℂ) :
    z ∈ cyclotomicRelativeAdjoin s a u ↔
      z ∈ cyclotomicAdjoin (insert a s) u := by
  constructor
  · intro hz
    apply IntermediateField.adjoin_induction (cyclotomicAdjoin s u)
      (p := fun x _ => x ∈ cyclotomicAdjoin (insert a s) u)
      (x := z) _ _ _ _ _ hz
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact IntermediateField.subset_adjoin ℚ _
        ⟨a, Finset.mem_insert_self a s, rfl⟩
    · intro r
      exact cyclotomicAdjoin_le_insert s a u r.property
    · intro x y hx hy hx' hy'
      exact (cyclotomicAdjoin (insert a s) u).add_mem hx' hy'
    · intro x hx hx'
      exact (cyclotomicAdjoin (insert a s) u).inv_mem hx'
    · intro x y hx hy hx' hy'
      exact (cyclotomicAdjoin (insert a s) u).mul_mem hx' hy'
  · intro hz
    apply IntermediateField.adjoin_induction ℚ
      (p := fun x _ => x ∈ cyclotomicRelativeAdjoin s a u)
      (x := z) _ _ _ _ _ hz
    · rintro x ⟨i, hi, rfl⟩
      by_cases hia : i = a
      · subst i
        exact IntermediateField.subset_adjoin (cyclotomicAdjoin s u) _
          (Set.mem_singleton (u a))
      · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
        exact (cyclotomicRelativeAdjoin s a u).algebraMap_mem
          ⟨u i, IntermediateField.subset_adjoin ℚ _ ⟨i, his, rfl⟩⟩
    · intro r
      exact (cyclotomicRelativeAdjoin s a u).algebraMap_mem
        (algebraMap ℚ (cyclotomicAdjoin s u) r)
    · intro x y hx hy hx' hy'
      exact (cyclotomicRelativeAdjoin s a u).add_mem hx' hy'
    · intro x hx hx'
      exact (cyclotomicRelativeAdjoin s a u).inv_mem hx'
    · intro x y hx hy hx' hy'
      exact (cyclotomicRelativeAdjoin s a u).mul_mem hx' hy'

noncomputable def cyclotomicInsertEquivRelative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (u : ι → ℂ) :
    cyclotomicAdjoin (insert a s) u ≃ₐ[ℚ] cyclotomicRelativeAdjoin s a u where
  toFun z := ⟨z.1, (mem_cyclotomicRelativeAdjoin_iff s a u z.1).mpr z.2⟩
  invFun z := ⟨z.1, (mem_cyclotomicRelativeAdjoin_iff s a u z.1).mp z.2⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  map_add' x y := by ext; rfl
  map_mul' x y := by ext; rfl
  commutes' r := by ext; rfl

theorem cyclotomicRelativeAdjoin_finrank {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j)) :
    Module.finrank (cyclotomicAdjoin s u) (cyclotomicRelativeAdjoin s a u) =
      Nat.totient (q a) := by
  let Kprev := cyclotomicAdjoin s u
  let Lrel := cyclotomicRelativeAdjoin s a u
  let Kall := cyclotomicAdjoin (insert a s) u
  letI : FiniteDimensional ℚ Kprev :=
    cyclotomicAdjoin_finiteDimensional s q u
      (fun i hi => hq i (Finset.mem_insert_of_mem hi))
      (fun i hi => hu i (Finset.mem_insert_of_mem hi))
  letI : FiniteDimensional ℚ Kall :=
    cyclotomicAdjoin_finiteDimensional (insert a s) q u hq hu
  letI : FiniteDimensional ℚ Lrel :=
    FiniteDimensional.of_surjective
      (cyclotomicInsertEquivRelative s a u).toLinearEquiv.toLinearMap
      (cyclotomicInsertEquivRelative s a u).surjective
  have hprev : Module.finrank ℚ Kprev = ∏ i ∈ s, Nat.totient (q i) :=
    cyclotomicAdjoin_finrank_eq s q u
      (fun i hi => hq i (Finset.mem_insert_of_mem hi))
      (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj) hij)
  have hall : Module.finrank ℚ Lrel =
      (∏ i ∈ s, Nat.totient (q i)) * Nat.totient (q a) := by
    rw [← (cyclotomicInsertEquivRelative s a u).toLinearEquiv.finrank_eq]
    rw [cyclotomicAdjoin_finrank_eq (insert a s) q u hq hu hcop,
      Finset.prod_insert ha]
    ac_rfl
  have htower := Module.finrank_mul_finrank ℚ Kprev Lrel
  rw [hprev, hall] at htower
  have hpos : 0 < ∏ i ∈ s, Nat.totient (q i) := by
    apply Finset.prod_pos
    intro i hi
    exact Nat.totient_pos.mpr (hq i (Finset.mem_insert_of_mem hi))
  exact Nat.eq_of_mul_eq_mul_left hpos htower

theorem cyclotomicFreshRoot_minpoly_natDegree_complex
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j)) :
    (minpoly (cyclotomicAdjoin s u) (u a)).natDegree = Nat.totient (q a) := by
  have huaIntQ : IsIntegral ℚ (u a) := isAlgebraic_iff_isIntegral.mp
    (primitiveRoot_isAlgebraic (hq a (Finset.mem_insert_self a s))
      (hu a (Finset.mem_insert_self a s)))
  have huaInt : IsIntegral (cyclotomicAdjoin s u) (u a) := huaIntQ.tower_top
  rw [← IntermediateField.adjoin.finrank huaInt]
  exact cyclotomicRelativeAdjoin_finrank s a ha q u hq hu hcop

theorem linearIndependent_cyclotomicFreshRoot_powers_complex
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j)) :
    LinearIndependent (cyclotomicAdjoin s u)
      (fun e : Fin (Nat.totient (q a)) => u a ^ (e : ℕ)) := by
  have hli := linearIndependent_pow (K := cyclotomicAdjoin s u) (u a)
  rw [cyclotomicFreshRoot_minpoly_natDegree_complex s a ha q u hq hu hcop] at hli
  exact hli

end

end GaloisForLFunctions.HTGeometry
