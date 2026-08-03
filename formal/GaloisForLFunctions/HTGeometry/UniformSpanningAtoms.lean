import GaloisForLFunctions.HTGeometry.CompactUniformFiniteProbe

/-!
# One finite atom family spanning over a whole compact patch

A continuous family of column systems which spans the target at every point of a compact patch
already spans there with finitely many columns, chosen once and for all.

Spanning with a fixed finite family is an open condition -- that is the corpus's local finite probe,
whose neighbourhood comes from a determinant -- and compactness turns the local families into one
finite family by taking their union.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- The control attached to finitely many columns: real coefficients against the columns. -/
def columnControl {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {N : ℕ} (c : Fin N → Y) :
    (Fin N → ℝ) →L[ℝ] Y :=
  ∑ l, (ContinuousLinearMap.proj l).smulRight (c l)

@[simp]
theorem columnControl_apply {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {N : ℕ}
    (c : Fin N → Y) (v : Fin N → ℝ) : columnControl c v = ∑ l, v l • c l := by
  rw [columnControl, sum_apply]
  rfl

theorem surjective_columnControl_iff {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {N : ℕ}
    (c : Fin N → Y) :
    Function.Surjective (columnControl c) ↔ Submodule.span ℝ (Set.range c) = ⊤ := by
  constructor
  · intro hsurj
    refine top_unique fun y _ => ?_
    obtain ⟨v, hv⟩ := hsurj y
    rw [← hv, columnControl_apply]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · intro hspan y
    have hy : y ∈ Submodule.span ℝ (Set.range c) := by
      rw [hspan]
      trivial
    rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hy
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, by rw [columnControl_apply]; exact hv⟩

theorem continuous_columnControl {H Y : Type*} [TopologicalSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {N : ℕ} (col : Fin N → H → Y)
    (hcol : ∀ l, Continuous (col l)) :
    Continuous fun h => columnControl fun l => col l h := by
  rw [continuous_clm_apply]
  intro v
  simp only [columnControl_apply]
  exact continuous_finsetSum _ fun l _ => (hcol l).const_smul _

/-- **A spanning column system spans with finitely many of its columns.** -/
theorem exists_finite_spanning_subfamily {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] {f : ℕ → Y} (hf : Submodule.span ℝ (Set.range f) = ⊤) :
    ∃ (N : ℕ) (a : Fin N → ℕ), Submodule.span ℝ (Set.range fun l => f (a l)) = ⊤ := by
  classical
  obtain ⟨T, hT⟩ : (⊤ : Submodule ℝ Y).FG := Module.finite_def.mp inferInstance
  have hmem : ∀ y ∈ T, ∃ t : Finset Y, ↑t ⊆ Set.range f ∧ y ∈ Submodule.span ℝ (↑t : Set Y) := by
    intro y _
    refine Submodule.mem_span_finite_of_mem_span ?_
    rw [hf]
    trivial
  choose t ht hmemt using hmem
  let S : Finset Y := T.attach.biUnion fun y => t y.1 y.2
  have hSsub : ↑S ⊆ Set.range f := by
    intro y hy
    simp only [S, Finset.coe_biUnion, Set.mem_iUnion] at hy
    obtain ⟨z, -, hz⟩ := hy
    exact ht z.1 z.2 hz
  have hSspan : Submodule.span ℝ (↑S : Set Y) = ⊤ := by
    refine top_unique ?_
    rw [← hT]
    refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_mono ?_ (hmemt y hy)
    intro v hv
    simp only [S, Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, hv⟩
  have hchoose : ∀ y : S, ∃ n : ℕ, f n = (y : Y) := fun y => hSsub y.2
  choose g hg using hchoose
  refine ⟨S.card, fun l => g (S.equivFin.symm l), ?_⟩
  refine top_unique ?_
  rw [← hSspan]
  refine Submodule.span_le.mpr fun y hy => ?_
  refine Submodule.subset_span ?_
  refine ⟨S.equivFin ⟨y, hy⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hg ⟨y, hy⟩

/-- **One finite atom family spans over the whole compact patch.** -/
theorem exists_uniform_spanning_atoms {H Y : Type*} [TopologicalSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (col : ℕ → H → Y) (hcol : ∀ n, Continuous (col n))
    {K : Set H} (hK : IsCompact K)
    (hspan : ∀ h ∈ K, Submodule.span ℝ (Set.range fun n => col n h) = ⊤) :
    ∃ (N : ℕ) (a : Fin N → ℕ), Function.Injective a ∧ ∀ h ∈ K,
      Submodule.span ℝ (Set.range fun l => col (a l) h) = ⊤ := by
  classical
  have hlocal : ∀ h : K, ∃ U : Set H, ∃ (N : ℕ) (a : Fin N → ℕ),
      IsOpen U ∧ h.1 ∈ U ∧ ∀ h' ∈ U,
        Submodule.span ℝ (Set.range fun l => col (a l) h') = ⊤ := by
    intro h
    obtain ⟨N, a, hNa⟩ := exists_finite_spanning_subfamily (hspan h.1 h.2)
    have hcont : Continuous fun h' => columnControl fun l => col (a l) h' :=
      continuous_columnControl (fun l h' => col (a l) h') fun l => hcol (a l)
    obtain ⟨U, V, hUopen, hhU, -, hVU⟩ :=
      exists_local_finiteProbe_of_continuous_surjectiveControl
        (fun h' => columnControl fun l => col (a l) h') hcont h.1
        ((surjective_columnControl_iff _).mpr hNa)
    refine ⟨U, N, a, hUopen, hhU, fun h' hh' => ?_⟩
    refine (surjective_columnControl_iff _).mp fun y => ?_
    obtain ⟨v, hv⟩ := hVU h' hh' y
    exact ⟨v.1, hv⟩
  choose U N a hUopen hhU hUspan using hlocal
  obtain ⟨s, hscover⟩ := hK.elim_finite_subcover (fun h : K => U h) (fun h => hUopen h) (by
    intro h hh
    exact Set.mem_iUnion.mpr ⟨⟨h, hh⟩, hhU ⟨h, hh⟩⟩)
  let A : Finset ℕ := s.biUnion fun j => Finset.image (a j) Finset.univ
  refine ⟨A.card, fun l => (A.equivFin.symm l : ℕ), ?_, fun h hh => ?_⟩
  · intro l₁ l₂ hl
    exact A.equivFin.symm.injective (Subtype.ext hl)
  obtain ⟨j, hjs, hjU⟩ := Set.mem_iUnion.mp (hscover hh) |>.imp fun j hj => by
    simpa using hj
  refine top_unique ?_
  rw [← hUspan j h hjU]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨l, rfl⟩
  refine Submodule.subset_span ?_
  have hmem : a j l ∈ A := by
    refine Finset.mem_biUnion.mpr ⟨j, hjs, ?_⟩
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  refine ⟨A.equivFin ⟨a j l, hmem⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]

end

end GaloisForLFunctions.HTGeometry
