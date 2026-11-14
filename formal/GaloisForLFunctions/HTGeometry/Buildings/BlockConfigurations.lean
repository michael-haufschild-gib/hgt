import GaloisForLFunctions.HTGeometry.ConstHomologyMono

/-!
# Finite configurations in flag blocks

The nonempty finite subsets of a vertex set form the face poset of its
full simplex. Products of these posets model blocks of lines. Inserting
one chosen vertex per block contracts every nonempty product; an empty
product of allowed configurations has zero chains instead.

Thus every intersection obtained by restricting the permitted vertices
in each block is empty or homologically contractible. This is the good
cover mechanism of Ash--Gunnells, arXiv:2611.03303, Lemma 3.1.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial

universe u

variable {ι α : Type u}

/-- A nonempty simplex whose vertices lie in a specified set. -/
abbrev finiteVertexConfiguration (S : Set α) :=
  {s : Finset α // s.Nonempty ∧ (↑s : Set α) ⊆ S}

/-- One nonempty simplex in every block. -/
def blockConfigurations (S : ι → Set α) := ∀ i, finiteVertexConfiguration (S i)

instance (S : ι → Set α) : PartialOrder (blockConfigurations S) :=
  inferInstanceAs (PartialOrder (∀ i, finiteVertexConfiguration (S i)))

/-- A block configuration exists exactly when every block has an allowed vertex. -/
theorem blockConfigurations_nonempty_iff (S : ι → Set α) :
    Nonempty (blockConfigurations S) ↔ ∀ i, (S i).Nonempty := by
  classical
  constructor
  · rintro ⟨s⟩ i
    obtain ⟨a, ha⟩ := (s i).property.1
    exact ⟨a, (s i).property.2 ha⟩
  · intro h
    choose a ha using h
    exact ⟨fun i => ⟨{a i}, ⟨a i, Finset.mem_singleton_self _⟩,
      fun x hx => (Finset.mem_singleton.mp hx) ▸ ha i⟩⟩

/-- The point configuration chosen in each block. -/
noncomputable def blockPoint (S : ι → Set α) (a : ∀ i, S i) : blockConfigurations S := by
  classical
  exact fun i => ⟨{(a i).val}, ⟨(a i).val, Finset.mem_singleton_self _⟩,
    fun x hx => (Finset.mem_singleton.mp hx) ▸ (a i).property⟩

/-- Inserting the chosen vertex gives a common upper bound with the point configuration. -/
noncomputable def blockInsert (S : ι → Set α) (a : ∀ i, S i) :
    blockConfigurations S →o blockConfigurations S := by
  classical
  refine
    { toFun := fun s i => ⟨insert (a i).val (s i).val,
        ⟨(a i).val, Finset.mem_insert_self _ _⟩, ?_⟩
      monotone' := ?_ }
  · intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact hx ▸ (a i).property
    · exact (s i).property.2 hx
  · intro s t h i x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact Finset.mem_insert.mpr (Or.inl hx)
    · exact Finset.mem_insert.mpr (Or.inr (h i hx))

theorem le_blockInsert (S : ι → Set α) (a : ∀ i, S i) (s : blockConfigurations S) :
    s ≤ blockInsert S a s := by
  classical
  intro i x hx
  exact Finset.mem_insert.mpr (Or.inr hx)

theorem blockPoint_le_blockInsert (S : ι → Set α) (a : ∀ i, S i)
    (s : blockConfigurations S) : blockPoint S a ≤ blockInsert S a s := by
  classical
  intro i x hx
  exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hx))

/-- Inserting a vertex also gives an explicit zigzag between any two configurations. -/
theorem isConnected_blockConfigurations (S : ι → Set α)
    [Nonempty (blockConfigurations S)] : SSet.IsConnected (nerve (blockConfigurations S)) := by
  classical
  have hS := (blockConfigurations_nonempty_iff S).mp inferInstance
  choose a ha using hS
  let v : ∀ i, S i := fun i => ⟨a i, ha i⟩
  haveI : SSet.IsPreconnected (nerve (blockConfigurations S)) :=
    isPreconnected_nerve_of_zigzag (P := blockConfigurations S) (fun s t =>
      Relation.ReflTransGen.head (Or.inl (le_blockInsert S v s))
        (.head (Or.inr (blockPoint_le_blockInsert S v s))
          (.head (Or.inl (blockPoint_le_blockInsert S v t))
            (.single (Or.inr (le_blockInsert S v t))))))
  exact ⟨⟨ComposableArrows.mk₀ (blockPoint S v)⟩⟩

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- With one allowed vertex in each block, the identity is homologically constant. -/
theorem blockConfigurations_homology_contracts (S : ι → Set α) (a : ∀ i, S i)
    (R : C) (n : ℕ) :
    SSet.homologyMap (SSet.const (X := nerve (blockConfigurations S))
      (Y := nerve (blockConfigurations S)) (ComposableArrows.mk₀ (blockPoint S a))) R n = 𝟙 _ :=
  homologyMap_const_eq_id_of_conical (blockPoint S a) (blockInsert S a)
    (le_blockInsert S a) (blockPoint_le_blockInsert S a) R n

/-- Every restricted block configuration space has vanishing positive homology,
including empty intersections. -/
theorem isZero_blockConfigurations_homology (S : ι → Set α) (R : C) (n : ℕ) :
    Limits.IsZero ((nerve (blockConfigurations S)).homology R (n + 1)) := by
  classical
  rcases isEmpty_or_nonempty (blockConfigurations S) with h | h
  · haveI : SSet.HasDimensionLT (nerve (blockConfigurations S)) 0 :=
      hasDimensionLT_nerve_of_chain_bound (P := blockConfigurations S) 0
        (fun m f _ => (h.false (f 0)).elim)
    exact isZero_homology_of_hasDimensionLT _ 0 R (n + 1) (Nat.zero_le _)
  · have hS := (blockConfigurations_nonempty_iff S).mp h
    choose a ha using hS
    exact isZero_homology_of_conical (blockPoint S (fun i => ⟨a i, ha i⟩))
      (blockInsert S (fun i => ⟨a i, ha i⟩)) (le_blockInsert S _)
      (blockPoint_le_blockInsert S _) R (n + 1) (Nat.le_add_left 1 n)

end GaloisForLFunctions.HTGeometry
