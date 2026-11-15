import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentSystem

/-!
# Augmented rank and finite compression of moment equations

Adding the affine constants to the coefficient rows preserves rank exactly
for a consistent system; otherwise rank increases by one. A normalized
contradiction certificate supplies the missing vertical direction.

A basis selected from the augmented rows gives finitely many original
equations generating the identical ideal. Thus a family of coefficient rank
`r`, even an infinite family, is consistent exactly when every subsystem of
at most `r + 1` equations is consistent. The ambient bound is `|ι| + 1`.
These statements hold over every field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem
open MvPolynomial Module Classical
variable {α β ι : Type*} (K : Type*) [Field K]

/-- Finite combinations of rows with their affine constants appended. -/
def augmentedMap (a : α → ι → K) (b : α → K) : (α →₀ K) →ₗ[K] ((ι → K) × K) :=
  (rowMap K a).prod (valueMap K b)

theorem augmentedMap_eq_linearCombination (a : α → ι → K) (b : α → K) :
    augmentedMap K a b = Finsupp.linearCombination K (fun j => (a j, b j)) := by
  apply LinearMap.ext
  intro c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single j r => simp [augmentedMap, rowMap, valueMap]

theorem range_augmentedMap (a : α → ι → K) (b : α → K) :
    (augmentedMap K a b).range = Submodule.span K (Set.range (fun j => (a j, b j))) := by
  rw [augmentedMap_eq_linearCombination, Finsupp.range_linearCombination]

/-- In a consistent system, the augmented row space is the graph of its level functional. -/
theorem finrank_augmentedMap_of_compatible (a : α → ι → K) (b : α → K)
    (h : Compatible K a b) :
    finrank K (augmentedMap K a b).range = finrank K (rowMap K a).range := by
  let g := (rowMap K a).range.subtype.prod (level K a b h)
  have he : augmentedMap K a b = g.comp (rowMap K a).rangeRestrict := by
    apply LinearMap.ext
    intro c
    exact Prod.ext rfl (level_rowMap K a b h c).symm
  have hg : Function.Injective g := by
    intro u v huv
    exact Subtype.ext (congrArg Prod.fst huv)
  rw [he, LinearMap.range_comp, LinearMap.range_rangeRestrict, Submodule.map_top]
  exact LinearMap.finrank_range_of_inj hg

/-- Include the product of the coefficient row space with the scalar axis. -/
def rowProductEmbedding (a : α → ι → K) : ((rowMap K a).range × K) →ₗ[K] ((ι → K) × K) :=
  ((rowMap K a).range.subtype.comp (LinearMap.fst K _ _)).prod (LinearMap.snd K _ _)

theorem rowProductEmbedding_injective (a : α → ι → K) :
    Function.Injective (rowProductEmbedding K a) := by
  intro u v h
  change (u.1.1, u.2) = (v.1.1, v.2) at h
  exact Prod.ext (Subtype.ext (congrArg (fun p : (ι → K) × K => p.1) h))
    (congrArg (fun p : (ι → K) × K => p.2) h)

/-- A contradiction certificate lets the scalar coordinate vary independently of the row. -/
theorem range_augmentedMap_of_not_compatible (a : α → ι → K) (b : α → K)
    (h : ¬ Compatible K a b) :
    (augmentedMap K a b).range = (rowProductEmbedding K a).range := by
  obtain ⟨c, ha, hb⟩ := (not_compatible_iff_certificate K a b).mp h
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    exact ⟨((rowMap K a).rangeRestrict d, valueMap K b d), rfl⟩
  · rintro _ ⟨⟨v, t⟩, rfl⟩
    obtain ⟨d, hd⟩ := v.2
    refine ⟨d + (t - valueMap K b d) • c, ?_⟩
    apply Prod.ext
    · change rowMap K a (d + (t - valueMap K b d) • c) = v.1
      rw [map_add, map_smul, ha, smul_zero, add_zero, hd]
    · change valueMap K b (d + (t - valueMap K b d) • c) = t
      rw [map_add, map_smul, hb, smul_eq_mul, mul_one, add_sub_cancel]

variable [Fintype ι]

/-- Appending constants raises row rank by exactly one precisely in the inconsistent case. -/
theorem finrank_augmentedMap (a : α → ι → K) (b : α → K) :
    finrank K (augmentedMap K a b).range =
      finrank K (rowMap K a).range + if Compatible K a b then 0 else 1 := by
  classical
  by_cases h : Compatible K a b
  · rw [if_pos h, add_zero, finrank_augmentedMap_of_compatible K a b h]
  · rw [if_neg h, range_augmentedMap_of_not_compatible K a b h,
      LinearMap.finrank_range_of_inj (rowProductEmbedding_injective K a),
      Module.finrank_prod, Module.finrank_self]

/-- Equality of ordinary and augmented row ranks characterizes consistency. -/
theorem compatible_iff_finrank_augmentedMap (a : α → ι → K) (b : α → K) :
    Compatible K a b ↔ finrank K (augmentedMap K a b).range = finrank K (rowMap K a).range := by
  classical
  rw [finrank_augmentedMap]
  by_cases h : Compatible K a b <;> simp [h]

/-- Spanning augmented equations gives ideal containment for the actual affine generators. -/
theorem ideal_le_of_augmented_range_le (a : α → ι → K) (b : α → K)
    (a' : β → ι → K) (b' : β → K)
    (h : (augmentedMap K a b).range ≤ (augmentedMap K a' b').range) :
    ideal K a b ≤ ideal K a' b' := by
  rw [ideal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have hm : (a j, b j) ∈ (augmentedMap K a b).range := by
    refine ⟨Finsupp.single j 1, ?_⟩
    simp [augmentedMap, rowMap, valueMap]
  obtain ⟨c, hc⟩ := h hm
  have ha : rowMap K a' c = a j := congrArg Prod.fst hc
  have hb : valueMap K b' c = b j := congrArg Prod.snd hc
  change momentLinearForm K (a j) - C (b j) ∈ ideal K a' b'
  simpa only [ha, hb] using equation_linearCombination_mem K a' b' c

theorem ideal_eq_of_augmented_range_eq (a : α → ι → K) (b : α → K)
    (a' : β → ι → K) (b' : β → K)
    (h : (augmentedMap K a b).range = (augmentedMap K a' b').range) :
    ideal K a b = ideal K a' b' :=
  le_antisymm (ideal_le_of_augmented_range_le K a b a' b' h.le)
    (ideal_le_of_augmented_range_le K a' b' a b h.ge)

/-- A basis chosen among augmented rows gives original equations generating the same ideal. -/
theorem exists_subsystem_of_augmented_rank (a : α → ι → K) (b : α → K) :
    ∃ f : Fin (finrank K (augmentedMap K a b).range) → α,
      ideal K (a ∘ f) (b ∘ f) = ideal K a b := by
  classical
  obtain ⟨g, hg, hs, _⟩ := Submodule.exists_fun_fin_finrank_span_eq K
    (Set.range (fun j => (a j, b j)))
  choose f hf using hg
  have he : (fun j => (a j, b j)) ∘ f = g := funext hf
  have hi : ideal K (a ∘ f) (b ∘ f) = ideal K a b := by
    apply ideal_eq_of_augmented_range_eq
    rw [range_augmentedMap, range_augmentedMap]
    change Submodule.span K (Set.range ((fun j => (a j, b j)) ∘ f)) = _
    rw [he, hs]
  rw [range_augmentedMap]
  exact ⟨f, hi⟩

/-- At most one more equation than coefficient rank suffices to generate the entire ideal. -/
theorem exists_subsystem_of_row_rank (a : α → ι → K) (b : α → K) :
    ∃ n ≤ finrank K (rowMap K a).range + 1, ∃ f : Fin n → α,
      ideal K (a ∘ f) (b ∘ f) = ideal K a b := by
  classical
  obtain ⟨f, hf⟩ := exists_subsystem_of_augmented_rank K a b
  refine ⟨finrank K (augmentedMap K a b).range, ?_, f, hf⟩
  rw [finrank_augmentedMap]
  split_ifs <;> omega

/-- Every inconsistent family contains an inconsistent subsystem of size at most `r + 1`. -/
theorem not_compatible_iff_small_subsystem (a : α → ι → K) (b : α → K) :
    ¬ Compatible K a b ↔
      ∃ n ≤ finrank K (rowMap K a).range + 1, ∃ f : Fin n → α,
        ¬ Compatible K (a ∘ f) (b ∘ f) := by
  constructor
  · intro h
    obtain ⟨n, hn, f, hf⟩ := exists_subsystem_of_row_rank K a b
    refine ⟨n, hn, f, ?_⟩
    rw [← ideal_eq_top_iff, hf, ideal_eq_top_iff]
    exact h
  · rintro ⟨n, _, f, hf⟩ h
    obtain ⟨x, hx⟩ := (compatible_iff_exists_point K a b).mp h
    apply hf
    exact (compatible_iff_exists_point K (a ∘ f) (b ∘ f)).mpr ⟨x, fun j => hx (f j)⟩

/-- Solvability of all subsystems up to rank plus one is equivalent to global solvability. -/
theorem compatible_iff_all_small_subsystems (a : α → ι → K) (b : α → K) :
    Compatible K a b ↔ ∀ n ≤ finrank K (rowMap K a).range + 1,
      ∀ f : Fin n → α, Compatible K (a ∘ f) (b ∘ f) := by
  constructor
  · intro h n _ f
    obtain ⟨x, hx⟩ := (compatible_iff_exists_point K a b).mp h
    exact (compatible_iff_exists_point K (a ∘ f) (b ∘ f)).mpr ⟨x, fun j => hx (f j)⟩
  · intro h
    by_contra hn
    obtain ⟨n, hn, f, hf⟩ := (not_compatible_iff_small_subsystem K a b).mp hn
    exact hf (h n hn f)

/-- The ambient affine Helly bound holds over arbitrary fields, including for infinite families. -/
theorem compatible_iff_all_subsystems_card (a : α → ι → K) (b : α → K) :
    Compatible K a b ↔ ∀ n ≤ Fintype.card ι + 1,
      ∀ f : Fin n → α, Compatible K (a ∘ f) (b ∘ f) := by
  constructor
  · intro h n _ f
    obtain ⟨x, hx⟩ := (compatible_iff_exists_point K a b).mp h
    exact (compatible_iff_exists_point K (a ∘ f) (b ∘ f)).mpr ⟨x, fun j => hx (f j)⟩
  · intro h
    apply (compatible_iff_all_small_subsystems K a b).mpr
    intro n hn f
    have hr := (rowMap K a).range.finrank_le
    rw [Module.finrank_pi] at hr
    exact h n (hn.trans (Nat.add_le_add_right hr 1)) f

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.finrank_augmentedMap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.exists_subsystem_of_row_rank
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.not_compatible_iff_small_subsystem
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.compatible_iff_all_subsystems_card
