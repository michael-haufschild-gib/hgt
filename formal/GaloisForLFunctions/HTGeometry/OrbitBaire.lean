import GaloisForLFunctions.HTGeometry.OrbitDensity

/-!
# The orbit lemma in one variable

The sources with a nonsingular evaluation matrix for a given finite family of distinct jet monomials
form an open dense subset of the compact box of sources, and there are only countably many such
families.  Baire's theorem therefore produces one source family that is good for all of them at once,
and a family of distinct jet monomials with a nonsingular evaluation matrix is linearly independent.

Hence: for finitely many nonzero frequencies and finitely many members with pairwise distinct
translation classes on each source, there are entire sources whose whole orbit family satisfies no
algebraic differential equation with complex coefficients.
-/

open Filter Topology MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A neighbourhood of a source family contains every family agreeing on a long enough
prefix.** -/
theorem exists_prefix_subset_nhds (C₀ : Fin L → sourceBox) {O : Set (Fin L → sourceBox)}
    (hO : O ∈ nhds C₀) :
    ∃ N₀ : ℕ, ∀ C : Fin L → sourceBox,
      (∀ (j : Fin L) (k : ℕ), k < N₀ → C j k = C₀ j k) → C ∈ O := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hO
  obtain ⟨I, -, U, hU, hUsub⟩ := hO
  have hUj : ∀ j : Fin L, ∃ (S : Set ℕ) (V : ∀ k : ℕ,
      Set (Metric.closedBall (0 : ℂ) (((k.factorial : ℝ))⁻¹))),
      S.Finite ∧ (∀ k, V k ∈ nhds (C₀ j k)) ∧ S.pi V ⊆ U j := by
    intro j
    have hj := hU j
    rw [nhds_pi, Filter.mem_pi] at hj
    obtain ⟨S, hSfin, V, hV, hVsub⟩ := hj
    exact ⟨S, V, hSfin, hV, hVsub⟩
  choose S V hSfin hV hVsub using hUj
  refine ⟨(Finset.univ.sup fun j => (hSfin j).toFinset.sup id) + 1, fun C hC => ?_⟩
  refine hUsub fun j _ => hVsub j fun k hk => ?_
  have hklt : k < (Finset.univ.sup fun j => (hSfin j).toFinset.sup id) + 1 := by
    have h1 : k ≤ (hSfin j).toFinset.sup id :=
      Finset.le_sup (f := id) ((hSfin j).mem_toFinset.mpr hk)
    have h2 : (hSfin j).toFinset.sup id ≤ Finset.univ.sup fun j => (hSfin j).toFinset.sup id :=
      Finset.le_sup (f := fun j => (hSfin j).toFinset.sup id) (Finset.mem_univ j)
    omega
  rw [hC j k hklt]
  exact mem_of_mem_nhds (hV j k)

/-- **The good sources are dense.** -/
theorem dense_orbGood (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0) (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i'))
    {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (hM : Function.Injective M) :
    Dense (orbGood lam src sh M) := by
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨C₀, hC₀⟩ := hUne
  obtain ⟨N₀, hN₀⟩ := exists_prefix_subset_nhds C₀ (hUopen.mem_nhds hC₀)
  obtain ⟨C, hCpre, hCgood⟩ :=
    exists_orbGood_agreeing lam hlam src sh hdist M hM C₀ N₀
  exact ⟨C, hN₀ C hCpre, hCgood⟩

/-- The countable set of finite jet-monomial families. -/
abbrev orbTask (ι : Type) [Fintype ι] : Type :=
  Σ p : ℕ × ℕ, (Fin p.2 → (Option (ι × Fin (p.1 + 1)) →₀ ℕ))

/-- **One source family good for every finite jet-monomial family.** -/
theorem exists_source_orbGood_all (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0) (src : ι → Fin L)
    (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i')) :
    ∃ C : Fin L → sourceBox, ∀ (n K : ℕ) (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)),
      Function.Injective M → C ∈ orbGood lam src sh M := by
  classical
  set G : orbTask ι → Set (Fin L → sourceBox) := fun τ =>
    if Function.Injective τ.2 then orbGood lam src sh τ.2 else Set.univ with hG
  have hGopen : ∀ τ, IsOpen (G τ) := by
    intro τ
    rw [hG]
    by_cases h : Function.Injective τ.2
    · simp only [if_pos h]
      exact isOpen_orbGood lam src sh τ.2
    · simp only [if_neg h]
      exact isOpen_univ
  have hGdense : ∀ τ, Dense (G τ) := by
    intro τ
    rw [hG]
    by_cases h : Function.Injective τ.2
    · simp only [if_pos h]
      exact dense_orbGood lam hlam src sh hdist τ.2 h
    · simp only [if_neg h]
      exact dense_univ
  obtain ⟨C, hC⟩ := (dense_iInter_of_isOpen hGopen hGdense).nonempty
  refine ⟨C, fun n K M hM => ?_⟩
  have hmem := Set.mem_iInter.mp hC (⟨(n, K), M⟩ : orbTask ι)
  rw [hG] at hmem
  simpa only [if_pos hM] using hmem

omit [Fintype ι] in
/-- **A source good for every finite jet-monomial family is jointly hypertranscendental.** -/
theorem jointlyHypertranscendental_of_orbGood_all (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    (C : Fin L → sourceBox)
    (hC : ∀ (n K : ℕ) (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)),
      Function.Injective M → C ∈ orbGood lam src sh M) :
    JointlyHypertranscendental (orbFun lam src sh C) := by
  classical
  rintro ⟨n, Q, hQ, hrel⟩
  set K : ℕ := Q.support.card with hK
  set M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ) :=
    fun i => ((Q.support.equivFin.symm i : Q.support) : Option (ι × Fin (n + 1)) →₀ ℕ) with hM
  have hMinj : Function.Injective M := by
    intro i i' h
    exact Q.support.equivFin.symm.injective (Subtype.ext h)
  obtain ⟨t, hdet⟩ := hC n K M hMinj
  have hgamma : (fun i => MvPolynomial.coeff (M i) Q) = 0 := by
    refine linearIndependent_of_orbEvalMatrix_det_ne_zero lam src sh C M t hdet ?_
    intro z
    have hz := hrel z
    rw [MvPolynomial.eval_eq] at hz
    rw [← hz]
    exact (Fintype.sum_equiv Q.support.equivFin.symm _ _ fun i => rfl).trans
      (Finset.sum_attach Q.support fun m =>
        MvPolynomial.coeff m Q * ∏ v ∈ m.support,
          (famJetPoint (orbFun lam src sh C) n z v) ^ m v)
  refine hQ ?_
  ext m
  by_cases hm : m ∈ Q.support
  · have hi := congrFun hgamma (Q.support.equivFin ⟨m, hm⟩)
    rw [hM] at hi
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at hi
    rw [hi, MvPolynomial.coeff_zero]
  · rw [MvPolynomial.notMem_support_iff.mp hm, MvPolynomial.coeff_zero]

/-- **The orbit lemma in one variable.**  For finitely many nonzero frequencies and finitely many
members whose translation classes are pairwise distinct on each source, there are entire sources
whose whole orbit family satisfies no algebraic differential equation with complex coefficients. -/
theorem exists_source_jointlyHypertranscendental (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0)
    (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i')) :
    ∃ C : Fin L → sourceBox, JointlyHypertranscendental (orbFun lam src sh C) := by
  obtain ⟨C, hC⟩ := exists_source_orbGood_all lam hlam src sh hdist
  exact ⟨C, jointlyHypertranscendental_of_orbGood_all lam src sh C hC⟩

end

end GaloisForLFunctions.HTGeometry
