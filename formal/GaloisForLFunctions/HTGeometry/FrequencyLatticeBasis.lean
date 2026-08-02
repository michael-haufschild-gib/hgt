import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-!
# The integer basis of a finite frequency group

The integer combinations of a finite family of real frequencies form a finitely generated
torsion-free group, hence a free group of finite rank.  A basis of that group is a rationally
independent family through which the original frequencies factor by an integer matrix, and the
basis itself is recovered from the frequencies by another integer matrix.  The two matrices
compose to the identity.

The basis is also a rational basis of the rational span of the frequencies, so the rank of the
frequency group is the rational coordinate rank used to define temporal dimension.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d]

/-- The group of integer combinations of a finite family of real frequencies. -/
def frequencyLattice (omega : d → ℝ) : Submodule ℤ ℝ := Submodule.span ℤ (Set.range omega)

instance instFiniteFrequencyLattice (omega : d → ℝ) :
    Module.Finite ℤ (frequencyLattice omega) :=
  Module.Finite.span_of_finite ℤ (Set.finite_range omega)

instance instFreeFrequencyLattice (omega : d → ℝ) :
    Module.Free ℤ (frequencyLattice omega) :=
  Module.free_of_finite_type_torsion_free'

omit [Fintype d] in
theorem mem_frequencyLattice (omega : d → ℝ) (i : d) : omega i ∈ frequencyLattice omega :=
  Submodule.subset_span ⟨i, rfl⟩

theorem coe_sum_zsmul {k : Type*} [Fintype k] {p : Submodule ℤ ℝ} (c : k → ℤ) (v : k → p) :
    ((∑ j, c j • v j : p) : ℝ) = ∑ j, (c j : ℝ) * ((v j : p) : ℝ) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun j _ => by rw [SetLike.val_smul, zsmul_eq_mul]

/-- **Integer basis of a frequency group.**  Every finite real frequency family is an integer
combination of a rationally independent family which is itself an integer combination of the
original one; the two integer matrices compose to the identity, and the second family is a
rational basis of the rational span of the first. -/
theorem exists_frequency_integer_basis (omega : d → ℝ) :
    ∃ (k : ℕ) (gamma : Fin k → ℝ) (M : d → Fin k → ℤ) (A : Fin k → d → ℤ),
      RationallyIndependentFrequency gamma ∧
      LinearIndependent ℚ gamma ∧
      Submodule.span ℚ (Set.range gamma) = Submodule.span ℚ (Set.range omega) ∧
      (∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) ∧
      (∀ j j', (∑ i, A j i * M i j') = if j = j' then 1 else 0) ∧
      k = Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) := by
  classical
  set Λ : Submodule ℤ ℝ := frequencyLattice omega with hΛ
  set ι := Module.Free.ChooseBasisIndex ℤ Λ with hι
  set b : Module.Basis (Fin (Fintype.card ι)) ℤ Λ :=
    (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFin ι) with hb
  set k := Fintype.card ι with hk
  set gamma : Fin k → ℝ := fun j => ((b j : Λ) : ℝ) with hgamma
  -- integer independence of the basis, read in the real line
  have hindepZ : ∀ n : Fin k → ℤ, (∑ j, (n j : ℝ) * gamma j) = 0 → n = 0 := by
    intro n hn
    have hsum : ((∑ j, n j • b j : Λ) : ℝ) = 0 := by
      rw [coe_sum_zsmul]
      exact hn
    have hzero : (∑ j, n j • b j : Λ) = 0 := Subtype.ext hsum
    have := Fintype.linearIndependent_iff.mp b.linearIndependent n hzero
    funext j
    exact this j
  -- the frequencies are integer combinations of the basis
  have hmem : ∀ i, omega i ∈ Λ := fun i => mem_frequencyLattice omega i
  set M : d → Fin k → ℤ := fun i j => b.repr ⟨omega i, hmem i⟩ j with hM
  have hMspec : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j := by
    intro i
    have hrepr := b.sum_repr ⟨omega i, hmem i⟩
    have := congrArg (fun z : Λ => (z : ℝ)) hrepr
    rw [coe_sum_zsmul] at this
    exact this.symm
  -- the basis is an integer combination of the frequencies
  have hbmem : ∀ j : Fin k, ((b j : Λ) : ℝ) ∈ Submodule.span ℤ (Set.range omega) := fun j =>
    (b j).2
  choose A hA using fun j : Fin k =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hbmem j)
  have hAspec : ∀ j j' : Fin k, (∑ i, A j i * M i j') = if j = j' then 1 else 0 := by
    intro j
    have hexpand : ∀ j' : Fin k,
        (∑ i, ((A j i : ℝ) * omega i))
          = ∑ j'', ((∑ i, A j i * M i j'' : ℤ) : ℝ) * gamma j'' := by
      intro j'
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
        rw [hMspec i, Finset.mul_sum]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j'' _ => ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hgoal : (∑ j'', ((∑ i, A j i * M i j'' : ℤ) : ℝ) * gamma j'')
        = ∑ j'', ((if j = j'' then (1 : ℤ) else 0 : ℤ) : ℝ) * gamma j'' := by
      rw [← hexpand j]
      have hAj := hA j
      have hleft : (∑ i, ((A j i : ℝ) * omega i)) = gamma j := by
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
          rw [← zsmul_eq_mul]]
        exact hAj
      rw [hleft]
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]
        push_cast
        ring
      · intro j'' _ hj''
        rw [if_neg (Ne.symm hj'')]
        push_cast
        ring
      · intro hcon
        exact absurd (Finset.mem_univ j) hcon
    intro j'
    have hdiff : (∑ j'', (((∑ i, A j i * M i j'') - (if j = j'' then (1 : ℤ) else 0) : ℤ) : ℝ)
        * gamma j'') = 0 := by
      have hsplit : ∀ j'' : Fin k,
          (((∑ i, A j i * M i j'') - (if j = j'' then (1 : ℤ) else 0) : ℤ) : ℝ) * gamma j''
            = ((∑ i, A j i * M i j'' : ℤ) : ℝ) * gamma j''
              - ((if j = j'' then (1 : ℤ) else 0 : ℤ) : ℝ) * gamma j'' := by
        intro j''
        push_cast
        ring
      rw [Finset.sum_congr rfl fun j'' (_ : j'' ∈ Finset.univ) => hsplit j'',
        Finset.sum_sub_distrib, hgoal, sub_self]
    have := hindepZ _ hdiff
    have hj' := congrFun this j'
    simpa using sub_eq_zero.mp (by simpa using hj')
  -- rational independence and rational span
  have hindepQ : LinearIndependent ℚ gamma := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hsum : (∑ j, (g j : ℝ) * gamma j) = 0 := by
      rw [← hg]
      exact Finset.sum_congr rfl fun j _ => by rw [zsmul_eq_mul]
    exact congrFun (hindepZ g hsum) j
  have hspan : Submodule.span ℚ (Set.range gamma) = Submodule.span ℚ (Set.range omega) := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      have hAj := hA j
      have hval : gamma j = ∑ i, (A j i : ℝ) * omega i := by
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
          rw [← zsmul_eq_mul]]
        exact (hA j).symm
      rw [hval]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ ((A j i : ℚ)) (Submodule.subset_span ⟨i, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hMspec i]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact Submodule.smul_mem _ ((M i j : ℚ)) (Submodule.subset_span ⟨j, rfl⟩)
  have hrank : k = Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) := by
    have hbasis : Module.Basis (Fin k) ℚ (Submodule.span ℚ (Set.range gamma)) :=
      Module.Basis.span hindepQ
    rw [← hspan, Module.finrank_eq_card_basis hbasis, Fintype.card_fin]
  exact ⟨k, gamma, M, A, fun n hn => hindepZ n hn, hindepQ, hspan, hMspec, hAspec, hrank⟩

end

end GaloisForLFunctions.HTGeometry
