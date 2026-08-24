import GaloisForLFunctions.HTGeometry.CyclotomicRelativePowerBasis

/-!
# Finite cyclotomic tensor boxes

For pairwise coprime primitive-root orders, products of the standard individual power packets form
a linearly independent rational tensor box.  The proof adds one root at a time using the direct
relative power basis.
-/

open scoped IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev CyclotomicBox {ι : Type*} (s : Finset ι) (q : ι → ℕ) :=
  ∀ i : {i // i ∈ s}, Fin (Nat.totient (q i.1))

noncomputable def cyclotomicBoxMonomial {ι : Type*}
    (s : Finset ι) (q : ι → ℕ) (u : ι → ℂ) (e : CyclotomicBox s q) : ℂ :=
  ∏ i, u i.1 ^ (e i : ℕ)

theorem cyclotomicBoxMonomial_mem {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → ℕ) (u : ι → ℂ) (e : CyclotomicBox s q) :
    cyclotomicBoxMonomial s q u e ∈ cyclotomicAdjoin s u := by
  apply (cyclotomicAdjoin s u).prod_mem
  intro i hi
  apply (cyclotomicAdjoin s u).toSubalgebra.pow_mem
  exact IntermediateField.subset_adjoin ℚ _ ⟨i.1, i.2, rfl⟩

private theorem linearIndependent_smul_complexSubfield
    {K : IntermediateField ℚ ℂ} {α β : Type*}
    {v : α → K} {w : β → ℂ}
    (hv : LinearIndependent ℚ v) (hw : LinearIndependent K w) :
    LinearIndependent ℚ (fun p : α × β => v p.1 • w p.2) :=
  linearIndependent_smul hv hw

private theorem linearIndependent_cyclotomicBox_insert
    {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι) (ha : a ∉ s)
    (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j))
    (hOld0 : LinearIndependent ℚ (cyclotomicBoxMonomial s q u)) :
    LinearIndependent ℚ (cyclotomicBoxMonomial (insert a s) q u) := by
  let old : CyclotomicBox s q → cyclotomicAdjoin s u := fun e =>
    ⟨cyclotomicBoxMonomial s q u e, cyclotomicBoxMonomial_mem s q u e⟩
  have hOld : LinearIndependent ℚ old := by
    apply LinearIndependent.of_comp
      (cyclotomicAdjoin s u).toSubalgebra.toSubmodule.subtype
    change LinearIndependent ℚ (cyclotomicBoxMonomial s q u)
    exact hOld0
  have hFresh : LinearIndependent (cyclotomicAdjoin s u)
      (fun e : Fin (Nat.totient (q a)) => u a ^ (e : ℕ)) :=
    linearIndependent_cyclotomicFreshRoot_powers_complex s a ha q u hq hu hcop
  have hProd := linearIndependent_smul_complexSubfield
    (K := cyclotomicAdjoin s u) hOld hFresh
  let split : CyclotomicBox (insert a s) q →
      CyclotomicBox s q × Fin (Nat.totient (q a)) := fun e =>
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
  change LinearIndependent ℚ
    ((fun p : CyclotomicBox s q × Fin (Nat.totient (q a)) =>
      old p.1 • (u a ^ (p.2 : ℕ) : ℂ)) ∘ split) at hcomp
  have hfamily (e : CyclotomicBox (insert a s) q) :
      old (split e).1 • (u a ^ ((split e).2 : ℕ) : ℂ) =
        cyclotomicBoxMonomial (insert a s) q u e := by
    let g : {i // i ∈ insert a s} → ℂ := fun i => u i.1 ^ (e i : ℕ)
    change (∏ i : {i // i ∈ s}, u i.1 ^ (e ⟨i.1,
        Finset.mem_insert_of_mem i.2⟩ : ℕ)) *
        u a ^ (e ⟨a, Finset.mem_insert_self a s⟩ : ℕ) = ∏ i, g i
    calc
      (∏ i : {i // i ∈ s}, u i.1 ^ (e ⟨i.1,
          Finset.mem_insert_of_mem i.2⟩ : ℕ)) *
          u a ^ (e ⟨a, Finset.mem_insert_self a s⟩ : ℕ) =
          u a ^ (e ⟨a, Finset.mem_insert_self a s⟩ : ℕ) *
            ∏ i : {i // i ∈ s}, u i.1 ^ (e ⟨i.1,
              Finset.mem_insert_of_mem i.2⟩ : ℕ) := by ac_rfl
      _ = ∏ o : Option {i // i ∈ s},
          g ((Finset.subtypeInsertEquivOption ha).symm o) := by
            rw [Fintype.prod_option]
            simp [g, Finset.subtypeInsertEquivOption]
      _ = ∏ i, g i :=
        (Finset.subtypeInsertEquivOption ha).symm.prod_comp g
  have hfun :
      ((fun p : CyclotomicBox s q × Fin (Nat.totient (q a)) =>
        old p.1 • (u a ^ (p.2 : ℕ) : ℂ)) ∘ split) =
        cyclotomicBoxMonomial (insert a s) q u := by
    funext e
    exact hfamily e
  rw [hfun] at hcomp
  exact hcomp

theorem linearIndependent_cyclotomicBox {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ s, 0 < q i)
    (hu : ∀ i ∈ s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (q i) (q j)) :
    LinearIndependent ℚ (cyclotomicBoxMonomial s q u) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [linearIndependent_unique_iff]
      simp [cyclotomicBoxMonomial]
  | @insert a s ha ih =>
      apply linearIndependent_cyclotomicBox_insert a s ha q u hq hu hcop
      exact ih
        (fun i hi => hq i (Finset.mem_insert_of_mem hi))
        (fun i hi => hu i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij)

end

end GaloisForLFunctions.HTGeometry
