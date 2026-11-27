import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ScalarCechGrading

/-! A mixed Čech complex with acyclic columns outside one singleton
has the cohomology of that singleton column. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits GlobalTheory.WH

namespace HTGeometry.FinsetCechDatum

/-- With zero coefficient on the empty index, ordinary Čech acyclicity
gives primitives in the total cochain module. -/
theorem exists_primitive_of_acyclic_linearComplex {R T : Type} [Field R]
    [LinearOrder T] [Fintype T] (D : FinsetCechDatum.{0} T) [∀ s, Module R (D.obj s)]
    (hD : ∀ {s t : Finset T} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    (h₀ : Subsingleton (D.obj ∅)) (h : (D.linearComplex (R := R) hD).Acyclic)
    (x : D.Cochain) (hx : D.d x = 0) : ∃ y, D.d y = x := by
  let C := D.linearComplex (R := R) hD
  have hd (n : ℕ) (z : D.degreeSubmodule (R := R) n) :
      (C.d n (n + 1) z).1 = D.d z.1 := by
    change (CochainComplex.of.d (fun j : ℕ => ModuleCat.of R (D.degreeSubmodule (R := R) j))
      _ n (n + 1) z).1 = _
    rw [CochainComplex.of_d]
    rfl
  refine D.exists_primitive_of_augmented_exact (K := R) ?_ ?_ x hx
  · intro z hz _
    funext s
    by_cases hs : s = ∅
    · subst s
      exact h₀.elim _ _
    · exact hz s (Finset.nonempty_iff_ne_empty.mpr hs)
  · intro n z hz hclosed
    let v : D.degreeSubmodule (R := R) n := ⟨z, hz⟩
    have hker : C.d n (n + 1) v = 0 := Subtype.ext ((hd n v).trans hclosed)
    cases n with
    | zero =>
      let S := C.sc' 0 0 1
      have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
        ((C.exactAt_iff' 0 0 1 (by simp) (by simp)).mp (h 0))
      obtain ⟨w, hw⟩ := (he v).mp hker
      change C.d 0 0 w = v at hw
      have hz : C.d 0 0 = 0 := C.shape 0 0 (by simp)
      have hw' : (0 : C.X 0) = v := (congrArg (fun f : C.X 0 ⟶ C.X 0 => f w) hz).symm.trans hw
      exact ⟨0, fun _ _ => rfl, D.d_zero.trans (congrArg Subtype.val hw')⟩
    | succ n =>
      let S := C.sc' n (n + 1) (n + 2)
      have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
        ((C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp (h (n + 1)))
      obtain ⟨w, hw⟩ := (he v).mp hker
      exact ⟨w.1, w.2, (hd n w).symm.trans (congrArg Subtype.val hw)⟩

section Supports

variable {R I J : Type} [Field R] [LinearOrder I] [LinearOrder J] [Fintype J]
  (D : FinsetCechDatum.{0} (I ⊕ₗ J)) [∀ s, Module R (D.obj s)]
  (hD : ∀ {s t : Finset (I ⊕ₗ J)} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)

/-- The upper support consisting of columns with an index other than the
distinguished singleton. -/
def offSingletonSupport (k : J) : Set (Finset J) :=
  {s | ∃ j ∈ s, j ≠ k}

omit [LinearOrder J] [Fintype J] in
theorem offSingletonSupport_upper (k : J) : IsUpperSet (offSingletonSupport k) :=
  fun _ _ h ⟨a, ha, hne⟩ => ⟨a, h ha, hne⟩

omit [LinearOrder J] [Fintype J] in
theorem offSingletonSupport_le (k : J) : offSingletonSupport k ⊆ nonemptyIntersections J :=
  fun _ ⟨j, hj, _⟩ => ⟨j, hj⟩

abbrev mixedSupport (I J : Type) [LinearOrder I] [LinearOrder J] :=
  joinedSupport (nonemptyIntersections I) (nonemptyIntersections J)

abbrev offSingletonMixedSupport (I : Type) [LinearOrder I] (k : J) :=
  joinedSupport (nonemptyIntersections I) (offSingletonSupport k)

omit [LinearOrder J] [Fintype J] in
theorem offSingletonMixedSupport_upper (k : J) :
    IsUpperSet (offSingletonMixedSupport I k) := by
  intro s t h hs
  exact ⟨hs.1.mono (lft_monotone h), offSingletonSupport_upper k (rgt_monotone h) hs.2⟩

theorem offSingletonMixedSupport_upper_in_mixed (k : J) ⦃s t : Finset (I ⊕ₗ J)⦄
    (hs : s ∈ offSingletonMixedSupport I k) (_ : t ∈ mixedSupport I J) (h : s ⊆ t) :
    t ∈ offSingletonMixedSupport I k :=
  offSingletonMixedSupport_upper k h hs

/-- Discarding the acyclic upper support leaves the same cohomology. -/
theorem nonempty_homology_equiv_singleton_column (k : J)
    (hC : ∀ T ∈ offSingletonSupport k,
      let P := offSingletonMixedSupport I k
      let hP := (offSingletonMixedSupport_upper (I := I) k).ordConnected
      let E := (D.truncate (R := R) P hP).leftSlice T
      ∀ x : E.Cochain, E.d x = 0 → ∃ y, E.d y = x) (n : ℕ) :
    let P := offSingletonMixedSupport I k
    let Q := mixedSupport I J
    let hP := (offSingletonMixedSupport_upper (I := I) k).ordConnected
    let hQ := joinedSupport_ordConnected (nonemptyIntersections_ordConnected I)
      (nonemptyIntersections_ordConnected J)
    let hS := supportDiff_ordConnected hQ (offSingletonMixedSupport_upper_in_mixed k)
    Nonempty (((D.truncate (R := R) Q hQ).linearComplex (D.truncate_linear (R := R) Q hQ hD)).homology n ≃ₗ[R]
      ((D.truncate (R := R) (Q \ P) hS).linearComplex
        (D.truncate_linear (R := R) (Q \ P) hS hD)).homology n) := by
  let P := offSingletonMixedSupport I k
  let Q := mixedSupport I J
  let hP := (offSingletonMixedSupport_upper (I := I) k).ordConnected
  let hQ := joinedSupport_ordConnected (nonemptyIntersections_ordConnected I)
    (nonemptyIntersections_ordConnected J)
  have hle : P ⊆ Q := fun _ h => ⟨h.1, offSingletonSupport_le k h.2⟩
  have hup : ∀ ⦃s t⦄, s ∈ P → t ∈ Q → s ⊆ t → t ∈ P := offSingletonMixedSupport_upper_in_mixed k
  let A := D.truncate (R := R) P hP
  have hac : (A.linearComplex (D.truncate_linear (R := R) P hP hD)).Acyclic := by
    have hEmpty : (∅ : Finset (I ⊕ₗ J)) ∉ P := by
      intro h
      have hl := h.1
      rw [← uni_empty_empty, lft_uni] at hl
      exact Finset.not_nonempty_empty hl
    refine A.acyclic_linearComplex_of_total_exact (D.truncate_linear (R := R) P hP hD)
      (D.subsingleton_truncate_obj P hP ∅ hEmpty) (A.exists_primitive_of_leftSlices ?_)
    intro T x hx
    by_cases hT : T ∈ offSingletonSupport k
    · exact hC T hT x hx
    · refine ⟨0, (A.leftSlice T).d_zero.trans (funext fun s => ?_)⟩
      have hnot : uni s T ∉ P := fun hs => hT (by simpa only [P, offSingletonMixedSupport,
        joinedSupport, rgt_uni] using hs.2)
      exact (D.subsingleton_truncate_obj P hP (uni s T) hnot).elim _ _
  obtain ⟨S, hS, h₁, h₂, h₃⟩ := D.shortExact_truncate (R := R) hP hQ hle hup hD
  have hA : S.X₁.Acyclic := h₁.symm ▸ hac
  have hz (i : ℕ) : IsZero (S.X₁.homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hA i)
  let g := HomologicalComplex.homologyMap S.g n
  letI : Mono g := (hS.homology_exact₂ n).mono_g ((hz n).eq_zero_of_src _)
  letI : Epi g := (hS.homology_exact₃ n (n + 1) (by simp)).epi_f ((hz (n + 1)).eq_zero_of_tgt _)
  letI : IsIso g := isIso_of_mono_of_epi g
  exact ⟨(HomologicalComplex.homologyMapIso (eqToIso h₂.symm) n ≪≫ asIso g ≪≫
    HomologicalComplex.homologyMapIso (eqToIso h₃) n).toLinearEquiv⟩

end Supports

end HTGeometry.FinsetCechDatum
