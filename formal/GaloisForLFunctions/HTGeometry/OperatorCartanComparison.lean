import GaloisForLFunctions.HTGeometry.OperatorConductorLength
import GaloisForLFunctions.HTGeometry.CartanPrefixNormalizedLimit

/-!
# The Cartan prefix comparison with an explicit constant

The prefix invariants of a moving lattice, computed intrinsically against the integral lattice
`R^ι`, and computed in the ambient row space against the saturated base lattice, differ by at most
twice the length of the conductor of the embedding matrix — that is, by twice the total order of
its elementary divisors.

The two halves are already available: the row map transports prefix invariants exactly, and
changing the base lattice from the row lattice to its saturation costs at most twice their relative
dimension.  What the conductor computation adds is the value of that relative dimension, and what
the normalized limit adds is that a bound independent of the moving lattice survives division by
`n`: the intrinsic and ambient normalized Cartan vectors coincide.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Bot

variable {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The prefix invariant attached to the zero cut vanishes. -/
theorem relIndexSup_bot {κ : Type*} [Nonempty κ] (L M : Submodule K V) :
    relIndexSup (fun _ : κ => (⊥ : Submodule K V)) L M = 0 := by
  have hfun : (fun _ : κ => relIndex (L ⊓ ⊥) (M ⊓ ⊥)) = fun _ : κ => (0 : ℤ) := by
    funext _
    rw [inf_bot_eq, inf_bot_eq, relIndex, sub_self]
  rw [relIndexSup, hfun, Set.range_const, csSup_singleton]

/-- The relative index inside a cut never exceeds the relative index of the pair, so a family of
cuts has a bounded family of relative indices. -/
theorem bddAbove_relIndex_inf {κ : Type*} (L M : Submodule K V)
    [FiniteDimensional K (M.map L.mkQ)] (cut : κ → Submodule K V) :
    BddAbove (Set.range fun i => relIndex (L ⊓ cut i) (M ⊓ cut i)) := by
  refine ⟨(quotDim L M : ℤ), ?_⟩
  rintro _ ⟨i, rfl⟩
  show relIndex (L ⊓ cut i) (M ⊓ cut i) ≤ (quotDim L M : ℤ)
  have h1 : quotDim (L ⊓ cut i) (M ⊓ cut i) ≤ quotDim L M := quotDim_inf_le L M (cut i)
  have h2 : (0 : ℤ) ≤ (quotDim (M ⊓ cut i) (L ⊓ cut i) : ℤ) := Int.natCast_nonneg _
  rw [relIndex]
  omega

/-- Enlarging the base subspace preserves finiteness of the relative dimension. -/
theorem finiteDimensional_map_mkQ_of_le {L₁ L₂ M : Submodule K V} (h : L₁ ≤ L₂)
    [FiniteDimensional K (M.map L₁.mkQ)] : FiniteDimensional K (M.map L₂.mkQ) := by
  have hle : L₁ ≤ Submodule.comap (LinearMap.id (R := K) (M := V)) L₂ := h
  have hmaps : ∀ x ∈ M.map L₁.mkQ, Submodule.mapQ L₁ L₂ LinearMap.id hle x ∈ M.map L₂.mkQ := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hm, Submodule.mapQ_apply L₁ L₂ LinearMap.id (h := hle) m⟩
  refine FiniteDimensional.of_surjective
    ((Submodule.mapQ L₁ L₂ LinearMap.id hle).restrict hmaps) ?_
  rintro ⟨_, m, hm, rfl⟩
  refine ⟨⟨L₁.mkQ m, ⟨m, hm, rfl⟩⟩, ?_⟩
  exact Subtype.ext (Submodule.mapQ_apply L₁ L₂ LinearMap.id (h := hle) m)

end Bot

namespace DiffOp

open scoped Differential

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The Cartan prefix comparison.**  The intrinsic prefix invariant of a moving lattice and the
ambient prefix invariant of its image differ by at most twice the relative dimension of the row
lattice inside its saturation — a constant depending on neither the moving lattice nor the cuts. -/
theorem relIndexSup_intrinsic_ambient_bound (P : ι → ι → DiffOp K) (hP : RowIndep P)
    {κ : Type*} [Nonempty κ] (cut : κ → Submodule K (ι → PseudoDiffOp K))
    (M : Submodule K (ι → PseudoDiffOp K))
    (hfin₁ : ∀ i, FiniteDimensional K
      ((M.map (rowMapK P) ⊓ (cut i).map (rowMapK P)).map
        ((((rowLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))).mkQ))
    (hfin₂ : ∀ i, FiniteDimensional K
      (((((satLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))).map
        ((M.map (rowMapK P) ⊓ (cut i).map (rowMapK P))).mkQ))
    (hbdd₁ : BddAbove (Set.range fun i =>
      relIndex (((rowLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))
        (M.map (rowMapK P) ⊓ (cut i).map (rowMapK P))))
    (hbdd₂ : BddAbove (Set.range fun i =>
      relIndex (((satLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))
        (M.map (rowMapK P) ⊓ (cut i).map (rowMapK P)))) :
    0 ≤ relIndexSup cut ((integralLattice ι).restrictScalars K) M
          - relIndexSup (fun i => (cut i).map (rowMapK P))
              ((satLattice P).restrictScalars K) (M.map (rowMapK P)) ∧
      relIndexSup cut ((integralLattice ι).restrictScalars K) M
          - relIndexSup (fun i => (cut i).map (rowMapK P))
              ((satLattice P).restrictScalars K) (M.map (rowMapK P))
        ≤ 2 * (quotDim ((rowLattice P).restrictScalars K)
            ((satLattice P).restrictScalars K) : ℤ) := by
  obtain ⟨hlow, hupp⟩ := relIndexSup_row_sat_comparison P (fun i => (cut i).map (rowMapK P))
    (M.map (rowMapK P)) hfin₁ hfin₂ hbdd₁ hbdd₂
  have htrans : relIndexSup (fun i => (cut i).map (rowMapK P))
      ((rowLattice P).restrictScalars K) (M.map (rowMapK P))
      = relIndexSup cut ((integralLattice ι).restrictScalars K) M := by
    have hmap := relIndexSup_rowMapK P hP cut M
    rwa [map_restrictScalars_rowMapK] at hmap
  rw [htrans] at hlow hupp
  exact ⟨hlow, hupp⟩

/-- The constant of the prefix comparison is twice the total order of the elementary divisors of
the matrix. -/
theorem exists_degree_sum_relIndexSup_comparison (P : ι → ι → DiffOp K) (hP : RowIndep P)
    {κ : Type*} [Nonempty κ] (cut : κ → Submodule K (ι → PseudoDiffOp K))
    (M : Submodule K (ι → PseudoDiffOp K))
    (hfin₁ : ∀ i, FiniteDimensional K
      ((M.map (rowMapK P) ⊓ (cut i).map (rowMapK P)).map
        ((((rowLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))).mkQ))
    (hfin₂ : ∀ i, FiniteDimensional K
      (((((satLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))).map
        ((M.map (rowMapK P) ⊓ (cut i).map (rowMapK P))).mkQ))
    (hbdd₁ : BddAbove (Set.range fun i =>
      relIndex (((rowLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))
        (M.map (rowMapK P) ⊓ (cut i).map (rowMapK P))))
    (hbdd₂ : BddAbove (Set.range fun i =>
      relIndex (((satLattice P).restrictScalars K) ⊓ (cut i).map (rowMapK P))
        (M.map (rowMapK P) ⊓ (cut i).map (rowMapK P)))) :
    ∃ d : ι → DiffOp K, (∀ i, d i ≠ 0) ∧
      0 ≤ relIndexSup cut ((integralLattice ι).restrictScalars K) M
            - relIndexSup (fun i => (cut i).map (rowMapK P))
                ((satLattice P).restrictScalars K) (M.map (rowMapK P)) ∧
        relIndexSup cut ((integralLattice ι).restrictScalars K) M
            - relIndexSup (fun i => (cut i).map (rowMapK P))
                ((satLattice P).restrictScalars K) (M.map (rowMapK P))
          ≤ 2 * ((∑ i, degree (d i) : ℕ) : ℤ) := by
  obtain ⟨d, hd, hcond⟩ := exists_degree_sum_eq_quotDim_conductor P hP
  obtain ⟨hlow, hupp⟩ :=
    relIndexSup_intrinsic_ambient_bound P hP cut M hfin₁ hfin₂ hbdd₁ hbdd₂
  rw [hcond] at hupp
  exact ⟨d, hd, hlow, hupp⟩

omit [DecidableEq ι] in
/-- **The normalized Cartan vectors agree.**  If the intrinsic normalized Cartan vector of a
sequence of moving lattices converges, so does the ambient one, to the same limit: the fixed
conductor offset disappears after division by `n`. -/
theorem tendsto_normalized_ambient_cartan {s : ℕ} (P : ι → ι → DiffOp K) (hP : RowIndep P)
    {κ : Type*} [Nonempty κ] (cut : ℕ → κ → Submodule K (ι → PseudoDiffOp K))
    (hcut0 : cut 0 = fun _ => ⊥) (A : ℕ → Submodule K (ι → PseudoDiffOp K))
    (hfin₁ : ∀ n k, ∀ i, FiniteDimensional K
      (((A n).map (rowMapK P) ⊓ (cut k i).map (rowMapK P)).map
        ((((rowLattice P).restrictScalars K) ⊓ (cut k i).map (rowMapK P))).mkQ))
    (hfin₂ : ∀ n k, ∀ i, FiniteDimensional K
      (((((satLattice P).restrictScalars K) ⊓ (cut k i).map (rowMapK P))).map
        (((A n).map (rowMapK P) ⊓ (cut k i).map (rowMapK P))).mkQ))
    (hbdd₁ : ∀ n k, BddAbove (Set.range fun i =>
      relIndex (((rowLattice P).restrictScalars K) ⊓ (cut k i).map (rowMapK P))
        ((A n).map (rowMapK P) ⊓ (cut k i).map (rowMapK P))))
    (hbdd₂ : ∀ n k, BddAbove (Set.range fun i =>
      relIndex (((satLattice P).restrictScalars K) ⊓ (cut k i).map (rowMapK P))
        ((A n).map (rowMapK P) ⊓ (cut k i).map (rowMapK P))))
    {L : Fin s → ℝ}
    (hlim : Tendsto (fun (n : ℕ) (i : Fin s) =>
      ((relIndexSup (cut ((i : ℕ) + 1)) ((integralLattice ι).restrictScalars K) (A n) : ℝ)
        - (relIndexSup (cut (i : ℕ)) ((integralLattice ι).restrictScalars K) (A n) : ℝ)) / n)
      atTop (nhds L)) :
    Tendsto (fun (n : ℕ) (i : Fin s) =>
      ((relIndexSup (fun j => (cut ((i : ℕ) + 1) j).map (rowMapK P))
            ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)) : ℝ)
        - (relIndexSup (fun j => (cut (i : ℕ) j).map (rowMapK P))
            ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)) : ℝ)) / n)
      atTop (nhds L) := by
  refine tendsto_normalized_increments_of_prefix_bound
    (fun n k => relIndexSup (cut k) ((integralLattice ι).restrictScalars K) (A n))
    (fun n k => relIndexSup (fun j => (cut k j).map (rowMapK P))
      ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)))
    (2 * (quotDim ((rowLattice P).restrictScalars K) ((satLattice P).restrictScalars K) : ℝ))
    (fun n => ?_) (fun n => ?_) (fun n k => ?_) hlim
  · rw [hcut0]
    exact relIndexSup_bot _ _
  · have hbot : (fun j : κ => ((cut 0 j).map (rowMapK P))) = fun _ : κ => (⊥ : Submodule K _) := by
      rw [hcut0]
      funext j
      exact Submodule.map_bot _
    rw [hbot]
    exact relIndexSup_bot _ _
  · obtain ⟨hlow, hupp⟩ := relIndexSup_intrinsic_ambient_bound P hP (cut k) (A n)
      (hfin₁ n k) (hfin₂ n k) (hbdd₁ n k) (hbdd₂ n k)
    have hcast : (relIndexSup (cut k) ((integralLattice ι).restrictScalars K) (A n) : ℝ)
        - (relIndexSup (fun j => (cut k j).map (rowMapK P))
            ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)) : ℝ)
        = ((relIndexSup (cut k) ((integralLattice ι).restrictScalars K) (A n)
            - relIndexSup (fun j => (cut k j).map (rowMapK P))
              ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hcast, abs_of_nonneg (by exact_mod_cast hlow)]
    exact_mod_cast hupp

omit [DecidableEq ι] in
/-- **The Cartan prefix comparison for commensurable lattices.**  When the moving lattice is
commensurable with the base lattices the finiteness and boundedness side conditions are automatic,
and the comparison holds with the same constant. -/
theorem relIndexSup_intrinsic_ambient_bound_of_commensurable (P : ι → ι → DiffOp K)
    (hP : RowIndep P) {κ : Type*} [Nonempty κ] (cut : κ → Submodule K (ι → PseudoDiffOp K))
    (M : Submodule K (ι → PseudoDiffOp K))
    [FiniteDimensional K ((M.map (rowMapK P)).map (((rowLattice P).restrictScalars K)).mkQ)]
    [FiniteDimensional K (((satLattice P).restrictScalars K).map ((M.map (rowMapK P))).mkQ)] :
    0 ≤ relIndexSup cut ((integralLattice ι).restrictScalars K) M
          - relIndexSup (fun i => (cut i).map (rowMapK P))
              ((satLattice P).restrictScalars K) (M.map (rowMapK P)) ∧
      relIndexSup cut ((integralLattice ι).restrictScalars K) M
          - relIndexSup (fun i => (cut i).map (rowMapK P))
              ((satLattice P).restrictScalars K) (M.map (rowMapK P))
        ≤ 2 * (quotDim ((rowLattice P).restrictScalars K)
            ((satLattice P).restrictScalars K) : ℤ) := by
  haveI : FiniteDimensional K
      ((M.map (rowMapK P)).map (((satLattice P).restrictScalars K)).mkQ) :=
    finiteDimensional_map_mkQ_of_le (M := M.map (rowMapK P))
      (show ((rowLattice P).restrictScalars K) ≤ ((satLattice P).restrictScalars K) from
        fun x hx => rowLattice_le_satLattice P hx)
  exact relIndexSup_intrinsic_ambient_bound P hP cut M
    (fun i => finiteDimensional_inf_map _ _ ((cut i).map (rowMapK P)))
    (fun i => finiteDimensional_inf_map _ _ ((cut i).map (rowMapK P)))
    (bddAbove_relIndex_inf _ _ _) (bddAbove_relIndex_inf _ _ _)

omit [DecidableEq ι] in
/-- **The normalized Cartan vectors agree, for commensurable moving lattices.**  This is `(13)`
under the hypothesis that each moving lattice is commensurable with the base lattices — which is
what makes its prefix invariants finite in the first place. -/
theorem tendsto_normalized_ambient_cartan_of_commensurable {s : ℕ} (P : ι → ι → DiffOp K)
    (hP : RowIndep P) {κ : Type*} [Nonempty κ] (cut : ℕ → κ → Submodule K (ι → PseudoDiffOp K))
    (hcut0 : cut 0 = fun _ => ⊥) (A : ℕ → Submodule K (ι → PseudoDiffOp K))
    (hfd₁ : ∀ n, FiniteDimensional K
      (((A n).map (rowMapK P)).map (((rowLattice P).restrictScalars K)).mkQ))
    (hfd₂ : ∀ n, FiniteDimensional K
      (((satLattice P).restrictScalars K).map (((A n).map (rowMapK P))).mkQ))
    {L : Fin s → ℝ}
    (hlim : Tendsto (fun (n : ℕ) (i : Fin s) =>
      ((relIndexSup (cut ((i : ℕ) + 1)) ((integralLattice ι).restrictScalars K) (A n) : ℝ)
        - (relIndexSup (cut (i : ℕ)) ((integralLattice ι).restrictScalars K) (A n) : ℝ)) / n)
      atTop (nhds L)) :
    Tendsto (fun (n : ℕ) (i : Fin s) =>
      ((relIndexSup (fun j => (cut ((i : ℕ) + 1) j).map (rowMapK P))
            ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)) : ℝ)
        - (relIndexSup (fun j => (cut (i : ℕ) j).map (rowMapK P))
            ((satLattice P).restrictScalars K) ((A n).map (rowMapK P)) : ℝ)) / n)
      atTop (nhds L) := by
  refine tendsto_normalized_ambient_cartan P hP cut hcut0 A (fun n k i => ?_) (fun n k i => ?_)
    (fun n k => ?_) (fun n k => ?_) hlim
  · haveI := hfd₁ n
    exact finiteDimensional_inf_map _ _ ((cut k i).map (rowMapK P))
  · haveI := hfd₂ n
    exact finiteDimensional_inf_map _ _ ((cut k i).map (rowMapK P))
  · haveI := hfd₁ n
    exact bddAbove_relIndex_inf _ _ _
  · haveI := hfd₁ n
    haveI : FiniteDimensional K
        (((A n).map (rowMapK P)).map (((satLattice P).restrictScalars K)).mkQ) :=
      finiteDimensional_map_mkQ_of_le (M := (A n).map (rowMapK P))
        (show ((rowLattice P).restrictScalars K) ≤ ((satLattice P).restrictScalars K) from
          fun x hx => rowLattice_le_satLattice P hx)
    exact bddAbove_relIndex_inf _ _ _

end DiffOp

end

end GaloisForLFunctions.HTGeometry
