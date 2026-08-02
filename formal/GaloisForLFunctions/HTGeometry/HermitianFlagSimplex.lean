import GaloisForLFunctions.HTGeometry.HermitianDegenerationFlag
import GaloisForLFunctions.HTGeometry.BuildingSpanningCover

/-!
# The degeneration flag is a simplex of the building

The degeneration flag of a Hermitian direction is a chain of subspaces, and the members that are
neither zero nor everything are vertices of the building of the space.  So every direction gives a
simplex of the building, of dimension two less than the number of distinct eigenvalues:

* distinct eigenvalues throughout give a **chamber** — a complete flag, with one subspace of every
  intermediate dimension;
* repeated eigenvalues give a **face** of a chamber, one dimension lower for each coincidence.

The nondegenerate simplices of the order complex of the building are exactly its strict chains, so
both statements are literally simplices of the building's nerve.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite Module Module.End

universe u

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}

/-! ## Members of the flag are vertices of the building -/

theorem eigenSum_ne_bot (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {i : Fin n}
    (hi : c < hT.eigenvalues hn i) : eigenSum T c ≠ ⊥ := by
  intro hcon
  exact absurd hi (not_lt.2 ((eigenSum_eq_bot_iff hT hn c).1 hcon i))

theorem eigenSum_ne_top (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {i : Fin n}
    (hi : hT.eigenvalues hn i ≤ c) : eigenSum T c ≠ ⊤ := by
  intro hcon
  exact absurd hi (not_le.2 ((eigenSum_eq_top_iff hT hn c).1 hcon i))

/-- **A threshold strictly between two eigenvalues gives a vertex of the building.** -/
theorem eigenSum_mem_properPart (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ}
    {i j : Fin n} (hi : c < hT.eigenvalues hn i) (hj : hT.eigenvalues hn j ≤ c) :
    ⊥ < eigenSum T c ∧ eigenSum T c < ⊤ :=
  ⟨lt_of_le_of_ne bot_le (Ne.symm (eigenSum_ne_bot hT hn hi)),
    lt_of_le_of_ne le_top (eigenSum_ne_top hT hn hj)⟩

/-- **Crossing an eigenvalue strictly enlarges the flag.** -/
theorem eigenSum_lt_eigenSum_of_mem_range (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {μ ν : ℝ}
    (hνμ : ν < μ) {i : Fin n} (hi : hT.eigenvalues hn i = μ) :
    eigenSum T μ < eigenSum T ν :=
  eigenSum_lt_eigenSum hT hn (le_of_lt hνμ) (hi ▸ hνμ) (le_of_eq hi)

/-! ## Distinct eigenvalues give a chamber -/

theorem strictAnti_eigenvalues (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (hinj : Function.Injective (hT.eigenvalues hn)) : StrictAnti (hT.eigenvalues hn) :=
  (hT.eigenvalues_antitone hn).strictAnti_of_injective hinj

/-- **With distinct eigenvalues the flag member at an eigenvalue has exactly that many dimensions
above it.** -/
theorem finrank_eigenSum_eigenvalues (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (hinj : Function.Injective (hT.eigenvalues hn)) (i : Fin n) :
    finrank ℂ (eigenSum T (hT.eigenvalues hn i)) = (i : ℕ) := by
  classical
  rw [finrank_eigenSum hT hn]
  have hfilter : (Finset.univ.filter fun j : Fin n => hT.eigenvalues hn i < hT.eigenvalues hn j)
      = Finset.univ.filter fun j : Fin n => j < i := by
    refine Finset.filter_congr fun j _ => ?_
    exact ⟨fun h => (StrictAnti.lt_iff_gt (strictAnti_eigenvalues hT hn hinj)).1 h,
      fun h => (strictAnti_eigenvalues hT hn hinj) h⟩
  rw [hfilter, show (Finset.univ.filter fun j : Fin n => j < i) = Finset.Iio i from by
    ext j; simp]
  simp

/-- **Distinct eigenvalues give a chamber.**  The degeneration flag of a Hermitian direction with
`N` distinct eigenvalues is a complete flag: a strictly increasing chain of proper nonzero
subspaces with one of every intermediate dimension, that is, a chamber of the building. -/
theorem exists_chamber_of_injective_eigenvalues {m : ℕ} (hT : T.IsSymmetric)
    (hn : finrank ℂ E = m + 2) (hinj : Function.Injective (hT.eigenvalues hn)) :
    ∃ f : Fin (m + 1) → properPart (Submodule ℂ E), StrictMono f ∧
      (∀ j, ∃ c : ℝ, (f j : Submodule ℂ E) = eigenSum T c) ∧
      ∀ j, finrank ℂ ((f j : Submodule ℂ E)) = (j : ℕ) + 1 := by
  have hdim : ∀ j : Fin (m + 1),
      finrank ℂ (eigenSum T (hT.eigenvalues hn j.succ)) = (j : ℕ) + 1 := by
    intro j
    rw [finrank_eigenSum_eigenvalues hT hn hinj j.succ]
    simp [Fin.val_succ]
  have hmem : ∀ j : Fin (m + 1),
      ⊥ < eigenSum T (hT.eigenvalues hn j.succ) ∧ eigenSum T (hT.eigenvalues hn j.succ) < ⊤ := by
    intro j
    constructor
    · refine lt_of_le_of_ne bot_le (Ne.symm ?_)
      intro hcon
      have := hdim j
      rw [hcon] at this
      simp at this
    · refine lt_of_le_of_ne le_top ?_
      intro hcon
      have := hdim j
      rw [hcon, finrank_top, hn] at this
      omega
  refine ⟨fun j => ⟨eigenSum T (hT.eigenvalues hn j.succ), hmem j⟩, ?_, fun j => ⟨_, rfl⟩, hdim⟩
  intro j j' hjj'
  refine Subtype.mk_lt_mk.2 (Submodule.lt_of_le_of_finrank_lt_finrank ?_ ?_)
  · exact eigenSum_antitone T ((hT.eigenvalues_antitone hn) (Fin.succ_le_succ_iff.2 (le_of_lt hjj')))
  · rw [hdim j, hdim j']
    exact Nat.succ_lt_succ hjj'

/-! ## The general flag: a face of a chamber -/

open scoped Classical in
/-- **The degeneration flag of any Hermitian direction is a simplex of the building.**  Its
dimension is two less than the number of distinct eigenvalues, so repeated eigenvalues give a
proper face of a chamber. -/
theorem exists_flag_simplex {m : ℕ} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (hk : (Finset.image (hT.eigenvalues hn) Finset.univ).card = m + 2) :
    ∃ f : Fin (m + 1) → properPart (Submodule ℂ E), StrictMono f ∧
      ∀ j, ∃ c : ℝ, (f j : Submodule ℂ E) = eigenSum T c := by
  set S : Finset ℝ := Finset.image (hT.eigenvalues hn) Finset.univ with hS
  have hne : S.Nonempty := Finset.card_pos.1 (by rw [hk]; omega)
  set M : ℝ := S.max' hne with hM
  have hMmem : M ∈ S := S.max'_mem hne
  obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.1 hMmem
  have hcard : (S.erase M).card = m + 1 := by
    rw [Finset.card_erase_of_mem hMmem, hk]
    omega
  set e := (S.erase M).orderIsoOfFin hcard with he
  have hmemS : ∀ j : Fin (m + 1), (e j : ℝ) ∈ S.erase M := fun j => (e j).2
  have hval : ∀ j : Fin (m + 1), ∃ i : Fin n, hT.eigenvalues hn i = (e j : ℝ) := by
    intro j
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase (hmemS j))
    exact ⟨i, hi⟩
  have hlt : ∀ j : Fin (m + 1), (e j : ℝ) < M := by
    intro j
    refine lt_of_le_of_ne (S.le_max' _ (Finset.mem_of_mem_erase (hmemS j))) ?_
    exact Finset.ne_of_mem_erase (hmemS j)
  have hmem : ∀ j : Fin (m + 1),
      ⊥ < eigenSum T ((e (Fin.rev j) : ℝ)) ∧ eigenSum T ((e (Fin.rev j) : ℝ)) < ⊤ := by
    intro j
    obtain ⟨i, hi⟩ := hval (Fin.rev j)
    exact eigenSum_mem_properPart hT hn (i := i₀) (j := i) (by rw [hi₀]; exact hlt (Fin.rev j))
      (le_of_eq hi)
  refine ⟨fun j => ⟨eigenSum T ((e (Fin.rev j) : ℝ)), hmem j⟩, ?_, fun j => ⟨_, rfl⟩⟩
  intro j j' hjj'
  obtain ⟨i, hi⟩ := hval (Fin.rev j)
  refine Subtype.mk_lt_mk.2 (eigenSum_lt_eigenSum_of_mem_range hT hn ?_ hi)
  exact_mod_cast (e.lt_iff_lt.2 (Fin.rev_lt_rev.2 hjj') : (e (Fin.rev j') : ℝ) < (e (Fin.rev j) : ℝ))

/-! ## The flag as a nondegenerate simplex of the building's order complex -/

/-- **The chamber of a direction with distinct eigenvalues, as a nondegenerate simplex** of the
order complex of the building, in the top dimension `N - 2`. -/
theorem exists_nonDegenerate_chamber {m : ℕ} (hT : T.IsSymmetric) (hn : finrank ℂ E = m + 2)
    (hinj : Function.Injective (hT.eigenvalues hn)) :
    ∃ s : (nerve (properPart (Submodule ℂ E))) _⦋m⦌,
      s ∈ (nerve (properPart (Submodule ℂ E))).nonDegenerate m := by
  obtain ⟨f, hf, -, -⟩ := exists_chamber_of_injective_eigenvalues hT hn hinj
  exact ⟨(Monotone.functor hf.monotone : (nerve (properPart (Submodule ℂ E))) _⦋m⦌),
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 hf⟩

open scoped Classical in
/-- **The flag of any direction, as a nondegenerate simplex** of the order complex of the building,
in dimension two less than the number of distinct eigenvalues. -/
theorem exists_nonDegenerate_flag {m : ℕ} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (hk : (Finset.image (hT.eigenvalues hn) Finset.univ).card = m + 2) :
    ∃ s : (nerve (properPart (Submodule ℂ E))) _⦋m⦌,
      s ∈ (nerve (properPart (Submodule ℂ E))).nonDegenerate m := by
  obtain ⟨f, hf, -⟩ := exists_flag_simplex hT hn hk
  exact ⟨(Monotone.functor hf.monotone : (nerve (properPart (Submodule ℂ E))) _⦋m⦌),
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 hf⟩

end GaloisForLFunctions.HTGeometry
