/-
# The path shell and the numbered nearest-neighbour Pauli family

The coefficient labels of the path-local Pauli shell -- one per site and axis, nine per edge -- are
exactly the nonidentity Pauli strings of support diameter at most one on the open path: a label of
diameter at most one is supported on a single site or on a single edge.  The two parametrizations of
the nearest-neighbour shell Hamiltonian therefore agree after one relabelling of coefficients and
one renumbering of the register.

Main results:
* `pathWord`, `pathWord_isChainLabel`, `pathWord_ne_identity`, `pathWord_injective`.
* `exists_pathWord_eq` — every nearest-neighbour Pauli label is a path label.
* `pathLabelEquiv` — **the two label sets agree**.
* `reindex_pathHamiltonian` — **the two Hamiltonian families agree**.
-/
import GaloisForLFunctions.HTGeometry.PathShellDelayFloor
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

open Matrix Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The Pauli word carried by a path-shell coefficient label. -/
def pathWord : PathLabel n → (Fin (n + 2) → Option (Fin 3))
  | Sum.inl sq => onsiteWord sq.1 sq.2
  | Sum.inr eab => couplingWord eab.1 eab.2

theorem onsiteWord_isChainLabel (s : Fin (n + 2)) (q : Fin 3) :
    IsChainLabel (onsiteWord s q) := by
  intro i j hi hj
  have hie : i = s := by
    by_contra hc
    exact hi (by rw [onsiteWord, if_neg hc])
  have hje : j = s := by
    by_contra hc
    exact hj (by rw [onsiteWord, if_neg hc])
  rw [hie, hje]
  omega

theorem couplingWord_isChainLabel (e : Fin (n + 1)) (ab : Fin 3 × Fin 3) :
    IsChainLabel (couplingWord e ab) := by
  intro i j hi hj
  have hsupp : ∀ t : Fin (n + 2), couplingWord e ab t ≠ none →
      (t : ℕ) = (e : ℕ) ∨ (t : ℕ) = (e : ℕ) + 1 := by
    intro t ht
    by_cases h1 : t = e.castSucc
    · exact Or.inl (by rw [h1, Fin.val_castSucc])
    · by_cases h2 : t = e.succ
      · exact Or.inr (by rw [h2, Fin.val_succ])
      · exact absurd (by rw [couplingWord, if_neg h1, if_neg h2]) ht
  rcases hsupp i hi with h | h <;> rcases hsupp j hj with h' | h' <;> omega

theorem pathWord_isChainLabel (l : PathLabel n) : IsChainLabel (pathWord l) := by
  cases l with
  | inl sq => exact onsiteWord_isChainLabel sq.1 sq.2
  | inr eab => exact couplingWord_isChainLabel eab.1 eab.2

theorem pathWord_ne_identity (l : PathLabel n) : pathWord l ≠ pauliIdentityLabel (n + 2) := by
  cases l with
  | inl sq =>
      intro h
      have := congrFun h sq.1
      rw [pathWord, onsiteWord, if_pos rfl, pauliIdentityLabel] at this
      exact absurd this (by simp)
  | inr eab =>
      intro h
      have := congrFun h eab.1.castSucc
      rw [pathWord, couplingWord, if_pos rfl, pauliIdentityLabel] at this
      exact absurd this (by simp)


theorem onsiteWord_ne_none_iff {s : Fin (n + 2)} {q : Fin 3} {t : Fin (n + 2)} :
    onsiteWord s q t ≠ none ↔ t = s := by
  rw [onsiteWord]
  by_cases h : t = s
  · simp [h]
  · simp [h]

theorem couplingWord_ne_none_iff {e : Fin (n + 1)} {ab : Fin 3 × Fin 3} {t : Fin (n + 2)} :
    couplingWord e ab t ≠ none ↔ (t : ℕ) = (e : ℕ) ∨ (t : ℕ) = (e : ℕ) + 1 := by
  constructor
  · intro ht
    by_cases h1 : t = e.castSucc
    · exact Or.inl (by rw [h1, Fin.val_castSucc])
    · by_cases h2 : t = e.succ
      · exact Or.inr (by rw [h2, Fin.val_succ])
      · exact absurd (show couplingWord e ab t = none by
          rw [couplingWord, if_neg h1, if_neg h2]) ht
  · intro hc
    rcases hc with hc | hc
    · have h1 : t = e.castSucc := Fin.ext (by rw [hc, Fin.val_castSucc])
      rw [couplingWord, if_pos h1]
      simp
    · have h2 : t = e.succ := Fin.ext (by rw [hc, Fin.val_succ])
      have h1 : t ≠ e.castSucc := by
        intro hcon
        have hv := congrArg Fin.val hcon
        rw [Fin.val_castSucc, hc] at hv
        omega
      rw [couplingWord, if_neg h1, if_pos h2]
      simp

theorem pathWord_injective : Function.Injective (pathWord (n := n)) := by
  intro l l' h
  cases l with
  | inl sq =>
      cases l' with
      | inl sq' =>
          have hs : sq.1 = sq'.1 := by
            have h1 : onsiteWord sq.1 sq.2 sq.1 ≠ none := by
              rw [onsiteWord_ne_none_iff]
            rw [pathWord, pathWord] at h
            rw [h, onsiteWord_ne_none_iff] at h1
            exact h1
          have hq : sq.2 = sq'.2 := by
            rw [pathWord, pathWord] at h
            have := congrFun h sq.1
            rw [onsiteWord, if_pos rfl, onsiteWord, if_pos hs] at this
            exact Option.some_injective _ this
          exact congrArg Sum.inl (Prod.ext hs hq)
      | inr eab' =>
          exfalso
          rw [pathWord, pathWord] at h
          have hc : onsiteWord sq.1 sq.2 eab'.1.castSucc ≠ none := by
            rw [h, couplingWord_ne_none_iff]
            exact Or.inl (by rw [Fin.val_castSucc])
          have hs : eab'.1.castSucc = sq.1 := onsiteWord_ne_none_iff.mp hc
          have hc2 : onsiteWord sq.1 sq.2 eab'.1.succ ≠ none := by
            rw [h, couplingWord_ne_none_iff]
            exact Or.inr (by rw [Fin.val_succ])
          have hs2 : eab'.1.succ = sq.1 := onsiteWord_ne_none_iff.mp hc2
          have : (eab'.1 : ℕ) = (eab'.1 : ℕ) + 1 := by
            have h1 : (eab'.1.castSucc : ℕ) = (sq.1 : ℕ) := by rw [hs]
            have h2 : (eab'.1.succ : ℕ) = (sq.1 : ℕ) := by rw [hs2]
            rw [Fin.val_castSucc] at h1
            rw [Fin.val_succ] at h2
            omega
          omega
  | inr eab =>
      cases l' with
      | inl sq' =>
          exfalso
          rw [pathWord, pathWord] at h
          have hc : onsiteWord sq'.1 sq'.2 eab.1.castSucc ≠ none := by
            rw [← h, couplingWord_ne_none_iff]
            exact Or.inl (by rw [Fin.val_castSucc])
          have hs : eab.1.castSucc = sq'.1 := onsiteWord_ne_none_iff.mp hc
          have hc2 : onsiteWord sq'.1 sq'.2 eab.1.succ ≠ none := by
            rw [← h, couplingWord_ne_none_iff]
            exact Or.inr (by rw [Fin.val_succ])
          have hs2 : eab.1.succ = sq'.1 := onsiteWord_ne_none_iff.mp hc2
          have h1 : (eab.1.castSucc : ℕ) = (sq'.1 : ℕ) := by rw [hs]
          have h2 : (eab.1.succ : ℕ) = (sq'.1 : ℕ) := by rw [hs2]
          rw [Fin.val_castSucc] at h1
          rw [Fin.val_succ] at h2
          omega
      | inr eab' =>
          rw [pathWord, pathWord] at h
          have he : eab.1 = eab'.1 := by
            have hA : couplingWord eab'.1 eab'.2 eab.1.castSucc ≠ none := by
              rw [← h, couplingWord_ne_none_iff]
              exact Or.inl (by rw [Fin.val_castSucc])
            have hB : couplingWord eab.1 eab.2 eab'.1.castSucc ≠ none := by
              rw [h, couplingWord_ne_none_iff]
              exact Or.inl (by rw [Fin.val_castSucc])
            rw [couplingWord_ne_none_iff, Fin.val_castSucc] at hA
            rw [couplingWord_ne_none_iff, Fin.val_castSucc] at hB
            exact Fin.ext (by omega)
          have hab : eab.2 = eab'.2 := by
            have h1 := congrFun h eab.1.castSucc
            have h2 := congrFun h eab.1.succ
            rw [couplingWord, if_pos rfl, couplingWord, if_pos (by rw [he])] at h1
            have hne : eab.1.succ ≠ eab.1.castSucc := by
              intro hc
              have := congrArg Fin.val hc
              rw [Fin.val_succ, Fin.val_castSucc] at this
              omega
            have hne' : eab.1.succ ≠ eab'.1.castSucc := by rw [← he]; exact hne
            rw [couplingWord, if_neg hne, if_pos rfl, couplingWord,
              if_neg hne', if_pos (by rw [he])] at h2
            exact Prod.ext (Option.some_injective _ h1) (Option.some_injective _ h2)
          exact congrArg Sum.inr (Prod.ext he hab)


/-- **Every nearest-neighbour Pauli label is a path-shell label.**  A nonidentity label of support
diameter at most one is supported either on one site or on one edge of the open path. -/
theorem exists_pathWord_eq {P : Fin (n + 2) → Option (Fin 3)}
    (hP : IsChainLabel P) (hne : P ≠ pauliIdentityLabel (n + 2)) :
    ∃ l : PathLabel n, pathWord l = P := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin (n + 2)),
    S = Finset.univ.filter (fun i => P i ≠ none) := ⟨_, rfl⟩
  have hmemS : ∀ t : Fin (n + 2), t ∈ S ↔ P t ≠ none := by
    intro t
    rw [hSdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ t, h⟩⟩
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    refine hne (funext fun t => ?_)
    by_contra hcon
    exact absurd (hmemS t |>.mpr hcon) (by rw [hempty]; exact Finset.notMem_empty t)
  obtain ⟨m, hmdef⟩ : ∃ m, m = S.min' hSne := ⟨_, rfl⟩
  have hmS : m ∈ S := by rw [hmdef]; exact S.min'_mem hSne
  have hmP : P m ≠ none := (hmemS m).mp hmS
  obtain ⟨a, ha⟩ : ∃ a, P m = some a := Option.ne_none_iff_exists'.mp hmP
  have hrange : ∀ t : Fin (n + 2), t ∈ S → (t : ℕ) = (m : ℕ) ∨ (t : ℕ) = (m : ℕ) + 1 := by
    intro t ht
    have hlow : (m : ℕ) ≤ (t : ℕ) := by
      have := S.min'_le t ht
      rw [← hmdef] at this
      exact this
    have hhigh : (t : ℕ) ≤ (m : ℕ) + 1 := hP t m ((hmemS t).mp ht) hmP
    omega
  by_cases hcase : ∃ i ∈ S, (i : ℕ) = (m : ℕ) + 1
  · obtain ⟨i₀, hi₀S, hi₀⟩ := hcase
    have hmlt : (m : ℕ) < n + 1 := by
      have := i₀.isLt
      omega
    obtain ⟨e, hedef⟩ : ∃ e : Fin (n + 1), e = ⟨(m : ℕ), hmlt⟩ := ⟨_, rfl⟩
    have hcast : e.castSucc = m := by
      refine Fin.ext ?_
      rw [Fin.val_castSucc, hedef]
    have hsucc : e.succ = i₀ := by
      refine Fin.ext ?_
      rw [Fin.val_succ, hedef, hi₀]
    have hi₀P : P i₀ ≠ none := (hmemS i₀).mp hi₀S
    obtain ⟨b, hb⟩ : ∃ b, P i₀ = some b := Option.ne_none_iff_exists'.mp hi₀P
    refine ⟨Sum.inr (e, (a, b)), ?_⟩
    show couplingWord e (a, b) = P
    funext t
    by_cases h1 : t = e.castSucc
    · rw [couplingWord, if_pos h1, h1, hcast, ha]
    · by_cases h2 : t = e.succ
      · rw [couplingWord, if_neg h1, if_pos h2, h2, hsucc, hb]
      · rw [couplingWord, if_neg h1, if_neg h2]
        by_contra hcon
        rcases hrange t ((hmemS t).mpr (fun hc => hcon hc.symm)) with hr | hr
        · exact h1 (Fin.ext (by rw [Fin.val_castSucc, hedef, hr]))
        · exact h2 (Fin.ext (by rw [Fin.val_succ, hedef, hr]))
  · refine ⟨Sum.inl (m, a), ?_⟩
    show onsiteWord m a = P
    funext t
    by_cases h1 : t = m
    · rw [onsiteWord, if_pos h1, h1, ha]
    · rw [onsiteWord, if_neg h1]
      by_contra hcon
      have htS : t ∈ S := (hmemS t).mpr (fun hc => hcon hc.symm)
      rcases hrange t htS with hr | hr
      · exact h1 (Fin.ext hr)
      · exact hcase ⟨t, htS, hr⟩

/-- The path-shell labels are exactly the nearest-neighbour Pauli labels. -/
def pathLabelEquiv (n : ℕ) : PathLabel n ≃ ChainLabel (n + 2) := by
  classical
  refine Equiv.ofBijective (fun l => ⟨pathWord l, pathWord_isChainLabel l, pathWord_ne_identity l⟩)
    ⟨fun l l' h => pathWord_injective (congrArg Subtype.val h), fun Q => ?_⟩
  obtain ⟨l, hl⟩ := exists_pathWord_eq Q.2.1 Q.2.2
  exact ⟨l, Subtype.ext hl⟩

theorem pathLabelEquiv_val (l : PathLabel n) : (pathLabelEquiv n l).1 = pathWord l := rfl


/-- The path-local Hamiltonian is the coefficient combination of the path Pauli words. -/
theorem pathHamiltonian_eq_sum (u : PathShell n) :
    pathHamiltonian u
      = ∑ l : PathLabel n, ((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) := by
  rw [Fintype.sum_sum_type, pathHamiltonian]
  have h1 : onsitePart u = ∑ a : Fin (n + 2) × Fin 3,
      ((u (Sum.inl a) : ℝ) : ℂ) • finitePauliMatrix (pathWord (Sum.inl a)) := rfl
  have h2 : ∑ e : Fin (n + 1), edgePart u e
      = ∑ b : Fin (n + 1) × (Fin 3 × Fin 3),
        ((u (Sum.inr b) : ℝ) : ℂ) • finitePauliMatrix (pathWord (Sum.inr b)) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun e _ => rfl
  rw [h1, h2]

/-- The coefficient relabelling from the numbered chain family to the path shell. -/
def pathCoeffEquiv (n : ℕ) : Fin (Fintype.card (ChainLabel (n + 2))) ≃ PathLabel n :=
  (Fintype.equivFin (ChainLabel (n + 2))).symm.trans (pathLabelEquiv n).symm

/-- **The path-local Hamiltonian is the numbered nearest-neighbour shell Hamiltonian.** -/
theorem reindex_pathHamiltonian (u : PathShell n) :
    Matrix.reindex (qubitConfigFin (n + 2)) (qubitConfigFin (n + 2)) (pathHamiltonian u)
      = spectralEnsembleMatrix (chainPauliFin (n + 2)) (fun a => u (pathCoeffEquiv n a)) := by
  classical
  rw [pathHamiltonian_eq_sum, spectralEnsembleMatrix]
  have hterm : ∀ a : Fin (Fintype.card (ChainLabel (n + 2))),
      ((u (pathCoeffEquiv n a) : ℝ) : ℂ) • chainPauliFin (n + 2) a
        = Matrix.reindex (qubitConfigFin (n + 2)) (qubitConfigFin (n + 2))
          (((u (pathCoeffEquiv n a) : ℝ) : ℂ) •
            finitePauliMatrix (pathWord (pathCoeffEquiv n a))) := by
    intro a
    have hlabel : ((Fintype.equivFin (ChainLabel (n + 2))).symm a).1
        = pathWord (pathCoeffEquiv n a) := by
      rw [pathCoeffEquiv]
      show ((Fintype.equivFin (ChainLabel (n + 2))).symm a).1
        = pathWord ((pathLabelEquiv n).symm ((Fintype.equivFin (ChainLabel (n + 2))).symm a))
      rw [← pathLabelEquiv_val, Equiv.apply_symm_apply]
    ext x y
    rw [chainPauliFin, hlabel]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  have hswap : ∑ a : Fin (Fintype.card (ChainLabel (n + 2))),
      Matrix.reindex (qubitConfigFin (n + 2)) (qubitConfigFin (n + 2))
        (((u (pathCoeffEquiv n a) : ℝ) : ℂ) • finitePauliMatrix (pathWord (pathCoeffEquiv n a)))
      = Matrix.reindex (qubitConfigFin (n + 2)) (qubitConfigFin (n + 2))
        (∑ a : Fin (Fintype.card (ChainLabel (n + 2))),
          ((u (pathCoeffEquiv n a) : ℝ) : ℂ) •
            finitePauliMatrix (pathWord (pathCoeffEquiv n a))) := by
    ext x y
    rw [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
    rfl
  rw [hswap]
  congr 1
  exact (Equiv.sum_comp (pathCoeffEquiv n)
    (fun l : PathLabel n => ((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l))).symm

end GaloisForLFunctions.HTGeometry

end
