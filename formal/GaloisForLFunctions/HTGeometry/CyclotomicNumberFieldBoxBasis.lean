import GaloisForLFunctions.HTGeometry.FiniteCompositumPowerIndependence

/-!
# Bounded cyclotomic boxes over number-field coefficients

For every finite rational coefficient field, sufficiently high pairwise-coprime cyclotomic
orders preserve each prescribed bounded exponent box.  The proof adds roots one at a time and
uses the finite-compositum degree bound, so no global linear-disjointness or ramification theorem
is needed.
-/

open scoped IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev BoundedCyclotomicBox {ι : Type*} (s : Finset ι) (D : ℕ) :=
  ∀ _i : {i // i ∈ s}, Fin (D + 1)

noncomputable def boundedCyclotomicBoxMonomial {ι : Type*}
    (s : Finset ι) (D : ℕ) (u : ι → ℂ) (e : BoundedCyclotomicBox s D) : ℂ :=
  ∏ i, u i.1 ^ (e i : ℕ)

theorem boundedCyclotomicBoxMonomial_mem {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ℕ) (u : ι → ℂ) (e : BoundedCyclotomicBox s D) :
    boundedCyclotomicBoxMonomial s D u e ∈ cyclotomicAdjoin s u := by
  apply (cyclotomicAdjoin s u).prod_mem
  intro i hi
  apply (cyclotomicAdjoin s u).toSubalgebra.pow_mem
  exact IntermediateField.subset_adjoin ℚ _ ⟨i.1, i.2, rfl⟩

private theorem linearIndependent_boundedCyclotomicFreshRoot_over_numberField
    {ι : Type*} [DecidableEq ι]
    (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    (r : Finset ι) (a : ι) (ha : a ∉ r) (D : ℕ)
    (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a r, 0 < q i)
    (hu : ∀ i ∈ insert a r, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a r, ∀ j ∈ insert a r,
      i ≠ j → Nat.Coprime (q i) (q j))
    (hlarge : Module.finrank ℚ k * D < Nat.totient (q a)) :
    LinearIndependent ↥(k ⊔ cyclotomicAdjoin r u)
      (fun e : Fin (D + 1) => u a ^ (e : ℕ)) := by
  let F : IntermediateField ℚ ℂ := cyclotomicAdjoin r u
  have hqF : ∀ i ∈ r, 0 < q i := fun i hi =>
    hq i (Finset.mem_insert_of_mem hi)
  have huF : ∀ i ∈ r, IsPrimitiveRoot (u i) (q i) := fun i hi =>
    hu i (Finset.mem_insert_of_mem hi)
  letI : FiniteDimensional ℚ F :=
    cyclotomicAdjoin_finiteDimensional r q u hqF huF
  have huaQ : IsIntegral ℚ (u a) := isAlgebraic_iff_isIntegral.mp
    (primitiveRoot_isAlgebraic (hq a (Finset.mem_insert_self a r))
      (hu a (Finset.mem_insert_self a r)))
  have hdeg : (minpoly F (u a)).natDegree = Nat.totient (q a) :=
    cyclotomicFreshRoot_minpoly_natDegree_complex r a ha q u hq hu hcop
  apply linearIndependent_powers_over_finite_compositum k F (u a) huaQ D
  rw [hdeg]
  exact hlarge

private theorem linearIndependent_mul_of_intermediateField
    (R K : IntermediateField ℚ ℂ) (hRK : R ≤ K)
    {I J : Type*} (v : I → ℂ) (hvMem : ∀ i, v i ∈ K)
    (hv : LinearIndependent R v) (w : J → ℂ) (hw : LinearIndependent K w) :
    LinearIndependent R (fun z : I × J => v z.1 * w z.2) := by
  let incRK : R →ₐ[ℚ] K := IntermediateField.inclusion hRK
  letI : Algebra R K := incRK.toAlgebra
  letI : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let vK : I → K := fun i => ⟨v i, hvMem i⟩
  have hvK : LinearIndependent R vK := by
    let val : K →ₗ[R] ℂ :=
      { toFun := fun z => z.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    apply LinearIndependent.of_comp val
    exact hv
  have hprod := linearIndependent_smul hvK hw
  change LinearIndependent R
    (fun z : I × J => algebraMap K ℂ (vK z.1) * w z.2) at hprod
  have hfun : (fun z : I × J => algebraMap K ℂ (vK z.1) * w z.2) =
      (fun z : I × J => v z.1 * w z.2) := by
    funext z
    rfl
  rw [hfun] at hprod
  exact hprod

private theorem linearIndependent_boundedCyclotomicBox_insert_of_intermediateField
    (R K : IntermediateField ℚ ℂ) (hRK : R ≤ K)
    {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (ha : a ∉ s) (D : ℕ) (u : ι → ℂ)
    (hOldMem : ∀ e : BoundedCyclotomicBox s D,
      boundedCyclotomicBoxMonomial s D u e ∈ K)
    (hOld : LinearIndependent R (boundedCyclotomicBoxMonomial s D u))
    (hFresh : LinearIndependent K (fun e : Fin (D + 1) => u a ^ (e : ℕ))) :
    LinearIndependent R (boundedCyclotomicBoxMonomial (insert a s) D u) := by
  have hProd := linearIndependent_mul_of_intermediateField R K hRK
    (boundedCyclotomicBoxMonomial s D u) hOldMem hOld
    (fun e : Fin (D + 1) => u a ^ (e : ℕ)) hFresh
  let split : BoundedCyclotomicBox (insert a s) D →
      BoundedCyclotomicBox s D × Fin (D + 1) := fun e =>
    (fun i => e ⟨i.1, Finset.mem_insert_of_mem i.2⟩,
      e ⟨a, Finset.mem_insert_self a s⟩)
  have hsplit : Function.Injective split := by
    intro e f hef
    funext i
    by_cases hia : i.1 = a
    · have hiEq : i = ⟨a, Finset.mem_insert_self a s⟩ := Subtype.ext hia
      subst i
      exact congrArg Prod.snd hef
    · have his : i.1 ∈ s := (Finset.mem_insert.mp i.2).resolve_left hia
      let is : {i // i ∈ s} := ⟨i.1, his⟩
      have hfun := congrArg Prod.fst hef
      have hi := congrFun hfun is
      simpa [split, is] using hi
  have hcomp := hProd.comp split hsplit
  change LinearIndependent R
    ((fun z : BoundedCyclotomicBox s D × Fin (D + 1) =>
      boundedCyclotomicBoxMonomial s D u z.1 *
        u a ^ (z.2 : ℕ)) ∘ split) at hcomp
  have hfamily (e : BoundedCyclotomicBox (insert a s) D) :
      boundedCyclotomicBoxMonomial s D u (split e).1 *
        u a ^ ((split e).2 : ℕ) =
        boundedCyclotomicBoxMonomial (insert a s) D u e := by
    let g : {i // i ∈ insert a s} → ℂ := fun i => u i.1 ^ (e i : ℕ)
    change (∏ i : {i // i ∈ s}, u i.1 ^
        (e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ : ℕ)) *
        u a ^ (e ⟨a, Finset.mem_insert_self a s⟩ : ℕ) = ∏ i, g i
    calc
      (∏ i : {i // i ∈ s}, u i.1 ^
          (e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ : ℕ)) *
          u a ^ (e ⟨a, Finset.mem_insert_self a s⟩ : ℕ) =
          u a ^ (e ⟨a, Finset.mem_insert_self a s⟩ : ℕ) *
            ∏ i : {i // i ∈ s}, u i.1 ^
              (e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ : ℕ) := by ac_rfl
      _ = ∏ o : Option {i // i ∈ s},
          g ((Finset.subtypeInsertEquivOption ha).symm o) := by
            rw [Fintype.prod_option]
            simp [g, Finset.subtypeInsertEquivOption]
      _ = ∏ i, g i :=
        (Finset.subtypeInsertEquivOption ha).symm.prod_comp g
  have hfun :
      ((fun z : BoundedCyclotomicBox s D × Fin (D + 1) =>
        boundedCyclotomicBoxMonomial s D u z.1 *
          u a ^ (z.2 : ℕ)) ∘ split) =
        boundedCyclotomicBoxMonomial (insert a s) D u := by
    funext e
    exact hfamily e
  rw [hfun] at hcomp
  exact hcomp

private theorem cyclotomicAdjoin_le_union_left
    {ι : Type*} [DecidableEq ι] (p s : Finset ι) (u : ι → ℂ) :
    cyclotomicAdjoin p u ≤ cyclotomicAdjoin (p ∪ s) u := by
  dsimp [cyclotomicAdjoin]
  apply IntermediateField.adjoin.mono ℚ _ _
  rintro z ⟨i, hi, rfl⟩
  exact ⟨i, Finset.mem_union_left s hi, rfl⟩

private theorem cyclotomicAdjoin_le_union_right
    {ι : Type*} [DecidableEq ι] (p s : Finset ι) (u : ι → ℂ) :
    cyclotomicAdjoin s u ≤ cyclotomicAdjoin (p ∪ s) u := by
  dsimp [cyclotomicAdjoin]
  apply IntermediateField.adjoin.mono ℚ _ _
  rintro z ⟨i, hi, rfl⟩
  exact ⟨i, Finset.mem_union_right p hi, rfl⟩

private theorem linearIndependent_boundedCyclotomicBox_insert_over_composita
    {ι : Type*} [DecidableEq ι]
    (k : IntermediateField ℚ ℂ)
    (p : Finset ι) (a : ι) (s : Finset ι) (ha : a ∉ s)
    (D : ℕ) (u : ι → ℂ)
    (hOld0 : LinearIndependent ↥(k ⊔ cyclotomicAdjoin p u)
      (boundedCyclotomicBoxMonomial s D u))
    (hFresh : LinearIndependent ↥(k ⊔ cyclotomicAdjoin (p ∪ s) u)
      (fun e : Fin (D + 1) => u a ^ (e : ℕ))) :
    LinearIndependent ↥(k ⊔ cyclotomicAdjoin p u)
      (boundedCyclotomicBoxMonomial (insert a s) D u) := by
  let A0 : IntermediateField ℚ ℂ := k ⊔ cyclotomicAdjoin p u
  let A : IntermediateField ℚ ℂ := k ⊔ cyclotomicAdjoin (p ∪ s) u
  have hA0A : A0 ≤ A := sup_le_sup le_rfl
    (cyclotomicAdjoin_le_union_left p s u)
  have hOldMem : ∀ e : BoundedCyclotomicBox s D,
      boundedCyclotomicBoxMonomial s D u e ∈ A := fun e =>
    (show cyclotomicAdjoin (p ∪ s) u ≤ A from le_sup_right)
      (cyclotomicAdjoin_le_union_right p s u
        (boundedCyclotomicBoxMonomial_mem s D u e))
  exact linearIndependent_boundedCyclotomicBox_insert_of_intermediateField
    A0 A hA0A a s ha D u hOldMem hOld0 hFresh

private theorem linearIndependent_boundedCyclotomicBox_insert_over_numberField
    {ι : Type*} [DecidableEq ι]
    (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    (p : Finset ι) (a : ι) (s : Finset ι) (ha : a ∉ s)
    (hdisj : Disjoint p (insert a s)) (D : ℕ)
    (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ p ∪ insert a s, 0 < q i)
    (hu : ∀ i ∈ p ∪ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ p ∪ insert a s, ∀ j ∈ p ∪ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j))
    (hlarge : ∀ i ∈ insert a s, Module.finrank ℚ k * D < Nat.totient (q i))
    (hOld0 : LinearIndependent ↥(k ⊔ cyclotomicAdjoin p u)
      (boundedCyclotomicBoxMonomial s D u)) :
    LinearIndependent ↥(k ⊔ cyclotomicAdjoin p u)
      (boundedCyclotomicBoxMonomial (insert a s) D u) := by
  have hall : insert a (p ∪ s) = p ∪ insert a s := by
    ext i
    simp
  have haPS : a ∉ p ∪ s := by
    rw [Finset.mem_union]
    intro h
    rcases h with hap | has
    · exact Finset.disjoint_left.mp hdisj hap (Finset.mem_insert_self a s)
    · exact ha has
  have hqAll : ∀ i ∈ insert a (p ∪ s), 0 < q i := by
    intro i hi
    exact hq i (by rwa [hall] at hi)
  have huAll : ∀ i ∈ insert a (p ∪ s), IsPrimitiveRoot (u i) (q i) := by
    intro i hi
    exact hu i (by rwa [hall] at hi)
  have hcopAll : ∀ i ∈ insert a (p ∪ s), ∀ j ∈ insert a (p ∪ s),
      i ≠ j → Nat.Coprime (q i) (q j) := by
    intro i hi j hj hij
    exact hcop i (by rwa [hall] at hi) j (by rwa [hall] at hj) hij
  have hFresh : LinearIndependent ↥(k ⊔ cyclotomicAdjoin (p ∪ s) u)
      (fun e : Fin (D + 1) => u a ^ (e : ℕ)) := by
    exact linearIndependent_boundedCyclotomicFreshRoot_over_numberField
      k (p ∪ s) a haPS D q u hqAll huAll hcopAll
        (hlarge a (Finset.mem_insert_self a s))
  exact linearIndependent_boundedCyclotomicBox_insert_over_composita
    k p a s ha D u hOld0 hFresh

theorem linearIndependent_boundedCyclotomicBox_over_numberField
    {ι : Type*} [DecidableEq ι]
    (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    (p t : Finset ι) (hdisj : Disjoint p t) (D : ℕ)
    (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ p ∪ t, 0 < q i)
    (hu : ∀ i ∈ p ∪ t, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ p ∪ t, ∀ j ∈ p ∪ t,
      i ≠ j → Nat.Coprime (q i) (q j))
    (hlarge : ∀ i ∈ t, Module.finrank ℚ k * D < Nat.totient (q i)) :
    LinearIndependent ↥(k ⊔ cyclotomicAdjoin p u)
      (boundedCyclotomicBoxMonomial t D u) := by
  induction t using Finset.induction_on with
  | empty =>
      rw [linearIndependent_unique_iff]
      simp [boundedCyclotomicBoxMonomial]
  | @insert a s ha ih =>
      have hsub : p ∪ s ⊆ p ∪ insert a s :=
        sup_le_sup le_rfl (Finset.subset_insert a s)
      apply linearIndependent_boundedCyclotomicBox_insert_over_numberField
        k p a s ha hdisj D q u hq hu hcop hlarge
      exact ih
        (hdisj.mono_right (Finset.subset_insert a s))
        (fun i hi => hq i (hsub hi))
        (fun i hi => hu i (hsub hi))
        (fun i hi j hj hij => hcop i (hsub hi) j (hsub hj) hij)
        (fun i hi => hlarge i (Finset.mem_insert_of_mem hi))

end
end GaloisForLFunctions.HTGeometry
