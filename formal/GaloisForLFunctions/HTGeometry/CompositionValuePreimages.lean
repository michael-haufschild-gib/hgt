import Mathlib

/-!
# Value preimages of a composition

Every point where the inner function attains an `a`-point of the outer function is an `a`-point of
the composition.  Distinct `a`-points of the outer function give disjoint preimage sets, so the
`a`-points of the composition are at least as numerous as the sum over the outer function's
`a`-points.

This is the counting mechanism behind composition growth: an outer function with many `a`-points
forces the composition to take the value `a` at least as often as the inner function takes each of
them, and the second main theorem guarantees that some value has many preimages.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A point sent by the inner function to an `a`-point of the outer function is an `a`-point of the
composition. -/
theorem comp_sub_eq_zero_of_eq {f g : ℂ → ℂ} {a b z : ℂ}
    (hfb : f b = a) (hgz : g z = b) : f (g z) - a = 0 := by
  rw [hgz, hfb, sub_self]

/-- The preimages of distinct values are disjoint. -/
theorem disjoint_preimage_of_ne {g : ℂ → ℂ} {K : Set ℂ} {b₁ b₂ : ℂ} (hb : b₁ ≠ b₂) :
    Disjoint {z ∈ K | g z = b₁} {z ∈ K | g z = b₂} := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  exact hb (hz₁.2 ▸ hz₂.2 ▸ rfl)

/-- **The composition has at least as many `a`-points as the inner function has preimages of the
outer function's `a`-points.** -/
theorem card_preimage_sum_le_card_comp {f g : ℂ → ℂ} {a : ℂ} {p : ℕ} (b : Fin p → ℂ)
    (hinj : Function.Injective b) (hfb : ∀ i, f (b i) = a) {K : Set ℂ}
    (hfin : ∀ i, {z ∈ K | g z = b i}.Finite) (hfinc : {z ∈ K | f (g z) - a = 0}.Finite) :
    ∑ i, (hfin i).toFinset.card ≤ hfinc.toFinset.card := by
  classical
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin p)), ∀ j ∈ (Finset.univ : Finset (Fin p)),
      i ≠ j → Disjoint (hfin i).toFinset (hfin j).toFinset := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    have h₁ : g z = b i := ((hfin i).mem_toFinset.mp hz₁).2
    have h₂ : g z = b j := ((hfin j).mem_toFinset.mp hz₂).2
    exact hij (hinj (h₁ ▸ h₂ ▸ rfl))
  have hsub : (Finset.univ.biUnion fun i => (hfin i).toFinset) ⊆ hfinc.toFinset := by
    intro z hz
    obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hz
    have hmem := (hfin i).mem_toFinset.mp hzi
    refine hfinc.mem_toFinset.mpr ⟨hmem.1, ?_⟩
    exact comp_sub_eq_zero_of_eq (hfb i) hmem.2
  calc ∑ i, (hfin i).toFinset.card
      = (Finset.univ.biUnion fun i => (hfin i).toFinset).card := (Finset.card_biUnion hdisj).symm
    _ ≤ hfinc.toFinset.card := Finset.card_le_card hsub

/-- **The composition attains `a` at least as often as the inner function attains one preimage.**
The special case of a single `a`-point, in the form the growth argument uses. -/
theorem card_preimage_le_card_comp {f g : ℂ → ℂ} {a b : ℂ} (hfb : f b = a) {K : Set ℂ}
    (hfin : {z ∈ K | g z = b}.Finite) (hfinc : {z ∈ K | f (g z) - a = 0}.Finite) :
    hfin.toFinset.card ≤ hfinc.toFinset.card := by
  classical
  refine Finset.card_le_card ?_
  intro z hz
  have hmem := hfin.mem_toFinset.mp hz
  exact hfinc.mem_toFinset.mpr ⟨hmem.1, comp_sub_eq_zero_of_eq hfb hmem.2⟩

/-! ## Multiplicities

Set-level counting loses the multiplicities that `logCounting` weighs.  They are recovered by
composing the two local factorizations: an `a`-point of order `k` for the outer function and a
`b`-point of order `l` for the inner one produce an `a`-point of order `k·l` for the composition. -/

/-- **The composed factorization.**  If `g - b` factors with a zero of order `l` at `z₀` and `f - a`
factors with a zero of order `k` at `b`, then `f ∘ g - a` factors with a zero of order `l·k` at
`z₀`. -/
theorem comp_factor_of_factors {f g h H : ℂ → ℂ} {a b z₀ : ℂ} {k l : ℕ} {U V : Set ℂ}
    (hg : ∀ z ∈ U, g z - b = (z - z₀) ^ l * h z)
    (hf : ∀ w ∈ V, f w - a = (w - b) ^ k * H w)
    (hmaps : ∀ z ∈ U, g z ∈ V) :
    ∀ z ∈ U, f (g z) - a = (z - z₀) ^ (l * k) * (h z ^ k * H (g z)) := by
  intro z hz
  have hgz := hg z hz
  have hfz := hf (g z) (hmaps z hz)
  rw [hfz, hgz, mul_pow, ← pow_mul]
  ring

/-- **The multiplicity of the composition dominates that of the inner function.**  With `k ≥ 1` the
composed factorization exhibits a zero of order at least `l`. -/
theorem comp_factor_of_factors_le {f g h H : ℂ → ℂ} {a b z₀ : ℂ} {k l : ℕ} {U V : Set ℂ}
    (hk : 1 ≤ k)
    (hg : ∀ z ∈ U, g z - b = (z - z₀) ^ l * h z)
    (hf : ∀ w ∈ V, f w - a = (w - b) ^ k * H w)
    (hmaps : ∀ z ∈ U, g z ∈ V) :
    ∃ e : ℕ, l ≤ e ∧ ∃ G : ℂ → ℂ, ∀ z ∈ U, f (g z) - a = (z - z₀) ^ e * G z := by
  refine ⟨l * k, ?_, fun z => h z ^ k * H (g z), comp_factor_of_factors hg hf hmaps⟩
  calc l = l * 1 := (mul_one l).symm
    _ ≤ l * k := Nat.mul_le_mul_left l hk

/-- **The composed factorization over a whole zero set.**  If `g - b` carries all its zeros in the
product `∏ (· - ζ)^{l ζ}` with zero-free cofactor `h`, and `f - a` has a zero of order `k` at `b`,
then `f ∘ g - a` carries the same zeros with every multiplicity multiplied by `k`.

This is the form `RHTower.sum_multiplicity_le_of_factor` consumes, so the composition's zero count
is directly comparable with the inner function's. -/
theorem comp_prod_factor_of_factors {f g h H : ℂ → ℂ} {a b : ℂ} {k : ℕ}
    {T : Finset ℂ} {l : ℂ → ℕ} {U V : Set ℂ}
    (hg : ∀ z ∈ U, g z - b = (∏ ζ ∈ T, (z - ζ) ^ (l ζ)) * h z)
    (hf : ∀ w ∈ V, f w - a = (w - b) ^ k * H w)
    (hmaps : ∀ z ∈ U, g z ∈ V) :
    ∀ z ∈ U, f (g z) - a
      = (∏ ζ ∈ T, (z - ζ) ^ (l ζ * k)) * (h z ^ k * H (g z)) := by
  intro z hz
  have hprod : (∏ ζ ∈ T, (z - ζ) ^ (l ζ)) ^ k = ∏ ζ ∈ T, (z - ζ) ^ (l ζ * k) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl ?_
    intro ζ _
    rw [← pow_mul]
  rw [hf (g z) (hmaps z hz), hg z hz, mul_pow, hprod]
  ring

/-- **The composition's zero count dominates the inner function's.**  Multiplying every multiplicity
by `k ≥ 1` can only increase the total. -/
theorem sum_multiplicity_le_comp {T : Finset ℂ} {l : ℂ → ℕ} {k : ℕ} (hk : 1 ≤ k) :
    ∑ ζ ∈ T, l ζ ≤ ∑ ζ ∈ T, l ζ * k := by
  refine Finset.sum_le_sum ?_
  intro ζ _
  calc l ζ = l ζ * 1 := (mul_one _).symm
    _ ≤ l ζ * k := Nat.mul_le_mul_left _ hk

/-! ## Several values at once

Keeping the zero sets of the different `b_i` as a nested product avoids any disjointness bookkeeping
in the identity itself; disjointness is needed only if one wants to flatten the nested product into a
single one, and it follows from `disjoint_preimage_of_ne`. -/

/-- **The composed factorization over several `a`-points.**  If `f - a` carries zeros of orders
`k i` at the points `b i`, and each `g - b i` carries its zeros in a product with zero-free cofactor,
then `f ∘ g - a` carries all of those zeros, with every multiplicity scaled by the corresponding
`k i`. -/
theorem comp_biUnion_factor {f g : ℂ → ℂ} {a : ℂ} {p : ℕ} (b : Fin p → ℂ)
    {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ} {k : Fin p → ℕ}
    {hh : Fin p → ℂ → ℂ} {H : ℂ → ℂ} {U V : Set ℂ}
    (hg : ∀ i : Fin p, ∀ z ∈ U, g z - b i = (∏ ζ ∈ T i, (z - ζ) ^ (l i ζ)) * hh i z)
    (hf : ∀ w ∈ V, f w - a = (∏ i, (w - b i) ^ (k i)) * H w)
    (hmaps : ∀ z ∈ U, g z ∈ V) :
    ∀ z ∈ U, f (g z) - a
      = (∏ i, ∏ ζ ∈ T i, (z - ζ) ^ (l i ζ * k i))
        * ((∏ i, hh i z ^ (k i)) * H (g z)) := by
  intro z hz
  have hterm : ∀ i : Fin p, (g z - b i) ^ (k i)
      = (∏ ζ ∈ T i, (z - ζ) ^ (l i ζ * k i)) * hh i z ^ (k i) := by
    intro i
    rw [hg i z hz, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro ζ _
    rw [← pow_mul]
  rw [hf (g z) (hmaps z hz)]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib]
  ring

/-- **The composition's total zero count dominates the inner function's.** -/
theorem sum_sum_multiplicity_le_comp {p : ℕ} {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ}
    {k : Fin p → ℕ} (hk : ∀ i : Fin p, 1 ≤ k i) :
    ∑ i, ∑ ζ ∈ T i, l i ζ ≤ ∑ i, ∑ ζ ∈ T i, l i ζ * k i := by
  refine Finset.sum_le_sum ?_
  intro i _
  refine Finset.sum_le_sum ?_
  intro ζ _
  calc l i ζ = l i ζ * 1 := (mul_one _).symm
    _ ≤ l i ζ * k i := Nat.mul_le_mul_left _ (hk i)

/-- The zero sets of distinct values are disjoint, so the nested product may be flattened. -/
theorem disjoint_zeroSets_of_ne {g : ℂ → ℂ} {p : ℕ} {b : Fin p → ℂ} (hinj : Function.Injective b)
    {T : Fin p → Finset ℂ} (hmem : ∀ i : Fin p, ∀ ζ ∈ T i, g ζ = b i) :
    ∀ i j : Fin p, i ≠ j → Disjoint (T i) (T j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro ζ hζi hζj
  exact hij (hinj ((hmem i ζ hζi) ▸ (hmem j ζ hζj) ▸ rfl))

/-! ## Flattening to a single product

`RHTower.sum_multiplicity_le_of_factor` wants one product over one `Finset`.  Disjointness of the
zero sets turns the nested product into that shape, with the multiplicity at each point read off from
the unique block containing it. -/

/-- The merged multiplicity function. -/
noncomputable def mergedMultiplicity {p : ℕ} (T : Fin p → Finset ℂ) (l : Fin p → ℂ → ℕ)
    (k : Fin p → ℕ) (ζ : ℂ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin p => ζ ∈ T i), l i ζ * k i

open scoped Classical in
/-- On a block, the merged multiplicity is that block's own. -/
theorem mergedMultiplicity_eq {p : ℕ} {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ} {k : Fin p → ℕ}
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (T i) (T j))
    {i₀ : Fin p} {ζ : ℂ} (hζ : ζ ∈ T i₀) :
    mergedMultiplicity T l k ζ = l i₀ ζ * k i₀ := by
  have hfilter : Finset.univ.filter (fun i : Fin p => ζ ∈ T i) = {i₀} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hζ⟩
    · intro i hi
      have hiT : ζ ∈ T i := (Finset.mem_filter.mp hi).2
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj i i₀ hne)) hiT hζ
  rw [mergedMultiplicity, hfilter, Finset.sum_singleton]

open scoped Classical in
/-- **The composed factorization, flattened.**  A single product over the union of the zero sets. -/
theorem comp_flat_factor {f g : ℂ → ℂ} {a : ℂ} {p : ℕ} (b : Fin p → ℂ)
    {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ} {k : Fin p → ℕ}
    {hh : Fin p → ℂ → ℂ} {H : ℂ → ℂ} {U V : Set ℂ}
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (T i) (T j))
    (hg : ∀ i : Fin p, ∀ z ∈ U, g z - b i = (∏ ζ ∈ T i, (z - ζ) ^ (l i ζ)) * hh i z)
    (hf : ∀ w ∈ V, f w - a = (∏ i, (w - b i) ^ (k i)) * H w)
    (hmaps : ∀ z ∈ U, g z ∈ V) :
    ∀ z ∈ U, f (g z) - a
      = (∏ ζ ∈ Finset.univ.biUnion T, (z - ζ) ^ (mergedMultiplicity T l k ζ))
        * ((∏ i, hh i z ^ (k i)) * H (g z)) := by
  intro z hz
  have hpd : ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint T :=
    fun i _ j _ hij => hdisj i j hij
  have hflat : (∏ ζ ∈ Finset.univ.biUnion T, (z - ζ) ^ (mergedMultiplicity T l k ζ))
      = ∏ i, ∏ ζ ∈ T i, (z - ζ) ^ (l i ζ * k i) := by
    rw [Finset.prod_biUnion hpd]
    refine Finset.prod_congr rfl ?_
    intro i _
    refine Finset.prod_congr rfl ?_
    intro ζ hζ
    rw [mergedMultiplicity_eq hdisj hζ]
  rw [hflat]
  exact comp_biUnion_factor b hg hf hmaps z hz

open scoped Classical in
/-- The merged count is the total of the block counts. -/
theorem sum_mergedMultiplicity {p : ℕ} {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ} {k : Fin p → ℕ}
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (T i) (T j)) :
    ∑ ζ ∈ Finset.univ.biUnion T, mergedMultiplicity T l k ζ
      = ∑ i, ∑ ζ ∈ T i, l i ζ * k i := by
  have hpd : ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint T :=
    fun i _ j _ hij => hdisj i j hij
  rw [Finset.sum_biUnion hpd]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro ζ hζ
  exact mergedMultiplicity_eq hdisj hζ

open scoped Classical in
/-- **The merged count, restricted to a sub-disc.**  The Jensen count of
`RHTower.sum_multiplicity_le_of_factor` is taken over the zeros inside a smaller radius, so the
merged multiplicity has to be summed over a filtered index set. -/
theorem sum_filter_mergedMultiplicity {p : ℕ} {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ}
    {k : Fin p → ℕ} (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (T i) (T j)) (P : ℂ → Prop)
    [DecidablePred P] :
    ∑ ζ ∈ (Finset.univ.biUnion T).filter P, mergedMultiplicity T l k ζ
      = ∑ i, ∑ ζ ∈ (T i).filter P, l i ζ * k i := by
  have hfilterdisj : ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
      (fun i => (T i).filter P) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro ζ hζi hζj
    exact (Finset.disjoint_left.mp (hdisj i j hij))
      (Finset.mem_filter.mp hζi).1 (Finset.mem_filter.mp hζj).1
  rw [Finset.filter_biUnion, Finset.sum_biUnion hfilterdisj]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro ζ hζ
  exact mergedMultiplicity_eq hdisj (Finset.mem_filter.mp hζ).1

/-- **The restricted count comparison.**  Each block contributes at least its own count. -/
theorem sum_filter_le_sum_filter_mergedMultiplicity {p : ℕ} {T : Fin p → Finset ℂ}
    {l : Fin p → ℂ → ℕ} {k : Fin p → ℕ} (hk : ∀ i : Fin p, 1 ≤ k i) (P : ℂ → Prop)
    [DecidablePred P] :
    ∑ i, ∑ ζ ∈ (T i).filter P, l i ζ ≤ ∑ i, ∑ ζ ∈ (T i).filter P, l i ζ * k i := by
  refine Finset.sum_le_sum ?_
  intro i _
  refine Finset.sum_le_sum ?_
  intro ζ _
  calc l i ζ = l i ζ * 1 := (mul_one _).symm
    _ ≤ l i ζ * k i := Nat.mul_le_mul_left _ (hk i)

end GaloisForLFunctions.HTGeometry
