import Mathlib

/-!
# Coordinate corank along a directed system of finite coordinate sets

For a subspace `V` of `P →₀ ℚ` and a finite set `T` of coordinates, the corank of `V` along `T` is
the dimension of the image of the coordinate subspace `ℚ^T` in the quotient by `V`.  These coranks
are finite, bounded by `|T|`, and monotone in `T`; the quotient is finite dimensional exactly when
they are bounded, and in that case they stabilize at the dimension of the quotient.

The point is the dichotomy: every finite coordinate slice has finite corank, so an infinite corank
of the limit is invisible to every slice individually and is detected only by the growth of the
sequence.

* `coordSpace`, `coordCorank` — the coordinate subspace and its corank.
* `coordCorank_le_card`, `coordCorank_mono` — every slice is finite, and coranks grow.
* `coordCorank_add_finrank_inf` — `corank + rank(V ∩ ℚ^T) = |T|`.
* `finiteDimensional_quotient_iff_bddAbove_coordCorank` — the dichotomy.
* `exists_coordCorank_stabilizes` — in the bounded case the coranks stabilize at the quotient
  dimension.
* `coordCorank_bot`, `not_bddAbove_coordCorank_bot` — the witness: over an infinite index type the
  zero subspace has every slice corank `|T|`, hence unbounded coranks and an infinite-dimensional
  quotient.
-/

namespace GaloisForLFunctions.HTGeometry

open Submodule

variable {P : Type*}

/-! ### The coordinate subspaces -/

/-- The subspace of `P →₀ ℚ` of vectors supported on a finite set of coordinates. -/
noncomputable def coordSpace (T : Finset P) : Submodule ℚ (P →₀ ℚ) :=
  Finsupp.supported ℚ ℚ (T : Set P)

theorem mem_coordSpace {T : Finset P} {f : P →₀ ℚ} :
    f ∈ coordSpace T ↔ (f.support : Set P) ⊆ (T : Set P) :=
  Finsupp.mem_supported ℚ f

theorem self_mem_coordSpace (f : P →₀ ℚ) : f ∈ coordSpace f.support :=
  mem_coordSpace.mpr (by simp)

instance instFiniteDimensionalCoordSpace (T : Finset P) :
    FiniteDimensional ℚ (coordSpace (P := P) T) := by
  have e := Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) (T : Set P)
  exact Module.Finite.equiv e.symm

theorem finrank_coordSpace (T : Finset P) :
    Module.finrank ℚ (coordSpace (P := P) T) = T.card := by
  rw [coordSpace]
  have e := Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) (T : Set P)
  rw [e.finrank_eq, Module.finrank_finsupp_self]
  simp

theorem coordSpace_mono {T T' : Finset P} (h : T ⊆ T') :
    coordSpace (P := P) T ≤ coordSpace (P := P) T' :=
  Finsupp.supported_mono (by exact_mod_cast h)

theorem iSup_coordSpace : ⨆ T : Finset P, coordSpace (P := P) T = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  exact Submodule.mem_iSup_of_mem f.support (self_mem_coordSpace f)

/-! ### The corank along a coordinate slice -/

/-- The corank of `V` along the coordinates `T`: the dimension of the image of the coordinate
subspace `ℚ^T` in the quotient by `V`. -/
noncomputable def coordCorank (V : Submodule ℚ (P →₀ ℚ)) (T : Finset P) : ℕ :=
  Module.finrank ℚ (Submodule.map V.mkQ (coordSpace T))

instance instFiniteDimensionalCoordImage (V : Submodule ℚ (P →₀ ℚ)) (T : Finset P) :
    FiniteDimensional ℚ (Submodule.map V.mkQ (coordSpace (P := P) T)) :=
  Module.Finite.map _ _

/-- **Every finite coordinate slice has finite corank**, bounded by the number of coordinates. -/
theorem coordCorank_le_card (V : Submodule ℚ (P →₀ ℚ)) (T : Finset P) :
    coordCorank V T ≤ T.card := by
  have h := Submodule.finrank_map_le V.mkQ (coordSpace (P := P) T)
  rw [finrank_coordSpace] at h
  exact h

/-- **The coranks are monotone along the directed system of coordinate slices.** -/
theorem coordCorank_mono (V : Submodule ℚ (P →₀ ℚ)) {T T' : Finset P} (h : T ⊆ T') :
    coordCorank V T ≤ coordCorank V T' :=
  Submodule.finrank_mono (Submodule.map_mono (coordSpace_mono h))

/-- **The corank identity of the card:** the corank along `T` plus the rank of the part of `V`
supported on `T` is the number of coordinates. -/
theorem coordCorank_add_finrank_inf (V : Submodule ℚ (P →₀ ℚ)) (T : Finset P) :
    coordCorank V T + Module.finrank ℚ (V ⊓ coordSpace (P := P) T : Submodule ℚ (P →₀ ℚ))
      = T.card := by
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (V.mkQ.domRestrict (coordSpace (P := P) T))
  have hrange : LinearMap.range (V.mkQ.domRestrict (coordSpace (P := P) T))
      = Submodule.map V.mkQ (coordSpace (P := P) T) := by
    rw [LinearMap.range_domRestrict]
  have hcomap : V.comap (coordSpace (P := P) T).subtype
      = (V ⊓ coordSpace (P := P) T).comap (coordSpace (P := P) T).subtype := by
    ext x
    simp [Submodule.mem_comap]
  have hker : Module.finrank ℚ (LinearMap.ker (V.mkQ.domRestrict (coordSpace (P := P) T)))
      = Module.finrank ℚ (V ⊓ coordSpace (P := P) T : Submodule ℚ (P →₀ ℚ)) := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ, hcomap]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  rw [hrange] at hrank
  rw [coordCorank, ← hker, hrank, finrank_coordSpace]

/-! ### The dichotomy -/

theorem iSup_map_mkQ_coordSpace (V : Submodule ℚ (P →₀ ℚ)) :
    ⨆ T : Finset P, Submodule.map V.mkQ (coordSpace (P := P) T) = ⊤ := by
  rw [← Submodule.map_iSup, iSup_coordSpace, Submodule.map_top, Submodule.range_mkQ]

/-- If the quotient is finite dimensional, every corank is bounded by its dimension. -/
theorem coordCorank_le_finrank_quotient (V : Submodule ℚ (P →₀ ℚ))
    [FiniteDimensional ℚ ((P →₀ ℚ) ⧸ V)] (T : Finset P) :
    coordCorank V T ≤ Module.finrank ℚ ((P →₀ ℚ) ⧸ V) :=
  Submodule.finrank_le _

/-- **A coordinate slice realizing the supremum already spans the quotient.** -/
theorem exists_map_eq_top_of_bddAbove (V : Submodule ℚ (P →₀ ℚ))
    (hb : BddAbove (Set.range (coordCorank V))) :
    ∃ T₀ : Finset P, Submodule.map V.mkQ (coordSpace (P := P) T₀) = ⊤ ∧
      coordCorank V T₀ = sSup (Set.range (coordCorank V)) := by
  classical
  have hne : (Set.range (coordCorank V)).Nonempty := ⟨coordCorank V ∅, ⟨∅, rfl⟩⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset P, coordCorank V T₀ = sSup (Set.range (coordCorank V)) := by
    have hmem := Nat.sSup_mem hne hb
    obtain ⟨T₀, hT₀⟩ := hmem
    exact ⟨T₀, hT₀⟩
  have hmax : ∀ T : Finset P, coordCorank V T ≤ coordCorank V T₀ := by
    intro T
    rw [hT₀]
    exact le_csSup hb ⟨T, rfl⟩
  have hle : ∀ T : Finset P,
      Submodule.map V.mkQ (coordSpace (P := P) T)
        ≤ Submodule.map V.mkQ (coordSpace (P := P) T₀) := by
    intro T
    have h₁ : Submodule.map V.mkQ (coordSpace (P := P) T₀)
        ≤ Submodule.map V.mkQ (coordSpace (P := P) (T ∪ T₀)) :=
      Submodule.map_mono (coordSpace_mono Finset.subset_union_right)
    have h₂ : Submodule.map V.mkQ (coordSpace (P := P) T)
        ≤ Submodule.map V.mkQ (coordSpace (P := P) (T ∪ T₀)) :=
      Submodule.map_mono (coordSpace_mono Finset.subset_union_left)
    have heq : Submodule.map V.mkQ (coordSpace (P := P) T₀)
        = Submodule.map V.mkQ (coordSpace (P := P) (T ∪ T₀)) :=
      Submodule.eq_of_le_of_finrank_le h₁ (hmax (T ∪ T₀))
    rw [heq]
    exact h₂
  refine ⟨T₀, eq_top_iff.mpr ?_, hT₀⟩
  rw [← iSup_map_mkQ_coordSpace V]
  exact iSup_le hle

/-- **The dichotomy.**  The quotient is finite dimensional exactly when the coordinate coranks are
bounded; every individual slice is always finite. -/
theorem finiteDimensional_quotient_iff_bddAbove_coordCorank (V : Submodule ℚ (P →₀ ℚ)) :
    FiniteDimensional ℚ ((P →₀ ℚ) ⧸ V) ↔ BddAbove (Set.range (coordCorank V)) := by
  constructor
  · intro h
    exact ⟨Module.finrank ℚ ((P →₀ ℚ) ⧸ V), by
      rintro n ⟨T, rfl⟩
      exact coordCorank_le_finrank_quotient V T⟩
  · intro hb
    obtain ⟨T₀, hT₀, -⟩ := exists_map_eq_top_of_bddAbove V hb
    have : FiniteDimensional ℚ (Submodule.map V.mkQ (coordSpace (P := P) T₀)) := inferInstance
    rw [hT₀] at this
    exact Module.Finite.equiv (Submodule.topEquiv (R := ℚ) (M := (P →₀ ℚ) ⧸ V))

/-- **Stabilization.**  When the coranks are bounded they are eventually equal to the dimension of
the quotient. -/
theorem exists_coordCorank_stabilizes (V : Submodule ℚ (P →₀ ℚ))
    (hb : BddAbove (Set.range (coordCorank V))) :
    ∃ T₀ : Finset P, ∀ T : Finset P, T₀ ⊆ T →
      coordCorank V T = coordCorank V T₀ := by
  obtain ⟨T₀, hT₀, -⟩ := exists_map_eq_top_of_bddAbove V hb
  refine ⟨T₀, fun T hT => ?_⟩
  have hle : Submodule.map V.mkQ (coordSpace (P := P) T₀)
      ≤ Submodule.map V.mkQ (coordSpace (P := P) T) :=
    Submodule.map_mono (coordSpace_mono hT)
  rw [hT₀] at hle
  have htop : Submodule.map V.mkQ (coordSpace (P := P) T) = ⊤ := eq_top_iff.mpr hle
  rw [coordCorank, coordCorank, htop, hT₀]

/-- **The corank of the limit is the supremum of the slice coranks**, when that supremum is
finite.  For an uncountable index type this is the correct form of the identity: a directed system
of finite-dimensional subspaces indexed by an uncountable set can have a union of dimension
strictly larger than the supremum of the dimensions, so only the finite case is an equality of
dimensions and the general case is the finite/infinite dichotomy above. -/
theorem finrank_quotient_eq_sSup_coordCorank (V : Submodule ℚ (P →₀ ℚ))
    [FiniteDimensional ℚ ((P →₀ ℚ) ⧸ V)] :
    Module.finrank ℚ ((P →₀ ℚ) ⧸ V) = sSup (Set.range (coordCorank V)) := by
  have hb : BddAbove (Set.range (coordCorank V)) :=
    (finiteDimensional_quotient_iff_bddAbove_coordCorank V).mp inferInstance
  obtain ⟨T₀, htop, hsup⟩ := exists_map_eq_top_of_bddAbove V hb
  rw [← hsup, coordCorank, htop]
  exact (Submodule.topEquiv (R := ℚ) (M := (P →₀ ℚ) ⧸ V)).finrank_eq.symm

/-- **Stabilization at the dimension of the limit.** -/
theorem coordCorank_eq_finrank_quotient_of_subset (V : Submodule ℚ (P →₀ ℚ))
    [FiniteDimensional ℚ ((P →₀ ℚ) ⧸ V)] :
    ∃ T₀ : Finset P, ∀ T : Finset P, T₀ ⊆ T →
      coordCorank V T = Module.finrank ℚ ((P →₀ ℚ) ⧸ V) := by
  have hb : BddAbove (Set.range (coordCorank V)) :=
    (finiteDimensional_quotient_iff_bddAbove_coordCorank V).mp inferInstance
  obtain ⟨T₀, htop, -⟩ := exists_map_eq_top_of_bddAbove V hb
  refine ⟨T₀, fun T hT => ?_⟩
  have hle : Submodule.map V.mkQ (coordSpace (P := P) T₀)
      ≤ Submodule.map V.mkQ (coordSpace (P := P) T) :=
    Submodule.map_mono (coordSpace_mono hT)
  rw [htop] at hle
  have hTtop : Submodule.map V.mkQ (coordSpace (P := P) T) = ⊤ := eq_top_iff.mpr hle
  rw [coordCorank, hTtop]
  exact (Submodule.topEquiv (R := ℚ) (M := (P →₀ ℚ) ⧸ V)).finrank_eq

/-! ### The witness: the zero subspace over an infinite index type -/

theorem coordCorank_bot (T : Finset P) : coordCorank (⊥ : Submodule ℚ (P →₀ ℚ)) T = T.card := by
  have hker : LinearMap.ker (⊥ : Submodule ℚ (P →₀ ℚ)).mkQ = ⊥ := by
    rw [Submodule.ker_mkQ]
  have hinj : Function.Injective (⊥ : Submodule ℚ (P →₀ ℚ)).mkQ :=
    LinearMap.ker_eq_bot.mp hker
  rw [coordCorank, ← (Submodule.equivMapOfInjective _ hinj (coordSpace (P := P) T)).finrank_eq,
    finrank_coordSpace]

/-- **The non-reconstruction witness.**  Over an infinite index type the coranks of the zero
subspace are unbounded, although every individual slice has corank `|T| < ∞`. -/
theorem not_bddAbove_coordCorank_bot [Infinite P] :
    ¬ BddAbove (Set.range (coordCorank (⊥ : Submodule ℚ (P →₀ ℚ)))) := by
  intro hb
  obtain ⟨B, hB⟩ := hb
  obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq P (B + 1)
  have := hB ⟨T, rfl⟩
  rw [coordCorank_bot, hT] at this
  omega

/-- **The limit is not seen by the slices.**  Over an infinite index type the quotient by the zero
subspace is infinite dimensional while every coordinate slice has finite corank. -/
theorem not_finiteDimensional_quotient_bot [Infinite P] :
    ¬ FiniteDimensional ℚ ((P →₀ ℚ) ⧸ (⊥ : Submodule ℚ (P →₀ ℚ))) := by
  rw [finiteDimensional_quotient_iff_bddAbove_coordCorank]
  exact not_bddAbove_coordCorank_bot

/-- **The slices do not reconstruct the limit.**  Over an infinite index type there is a subspace
whose every coordinate slice has finite corank while the quotient is infinite dimensional: no
finite slice can pose, let alone detect, the jump. -/
theorem exists_slicewise_finite_limit_infinite [Infinite P] :
    ∃ V : Submodule ℚ (P →₀ ℚ),
      (∀ T : Finset P, coordCorank V T = T.card) ∧
        ¬ FiniteDimensional ℚ ((P →₀ ℚ) ⧸ V) :=
  ⟨⊥, coordCorank_bot, not_finiteDimensional_quotient_bot⟩

end GaloisForLFunctions.HTGeometry
