import GaloisForLFunctions.HTGeometry.DegenerationIteration
import GaloisForLFunctions.HTGeometry.FamilyGenericSaturation
import GaloisForLFunctions.HTGeometry.FamilyFibreRescaled
import GaloisForLFunctions.HTGeometry.HomogIdealList
import GaloisForLFunctions.HTGeometry.QuotientRegularSequence
import GaloisForLFunctions.HTGeometry.InitialIdealDegeneration

/-!
# A Gröbner degeneration transports a whole regular sequence

```text
exists_generic_degeneration_bound  ** one point of the base line bounds every partial fibre **
isRegularOn_of_isRegular           reading a regular sequence back as regularity of each stage
finrank_quotDegreePart_top         a unit ideal has empty quotient in every degree
exists_isRegular_of_degeneration_homogeneous
                                   ** the transported regular sequence, again of linear forms **
exists_isRegular_of_degeneration   the same, forgetting homogeneity
```

The induction carries two things at once: the invariant that the two partial quotients have the same
Hilbert function in every degree, and the regularity of the deformed form at the current stage.  The
step is `forall_mem_of_hilbert_le`, whose fibre hypothesis is supplied by the flat family through
`exists_generic_degeneration_bound`; the invariant is restored by `hilbert_eq_of_forall_mem` in the
degrees at and above the degree of the form, and by `degreePart_sup_span_of_lt` below it.

The deformation is a single rescaling of the variables, chosen once for the whole sequence: the
fibre of the family over the chosen point is the rescaled ideal, so the form that ends up regular on
the original ideal is the *pullback* of the form regular on the degeneration.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {N : ℕ} {K : Type u} [Field K]

/-- **One point of the base line bounds every partial fibre at once.** -/
theorem exists_generic_degeneration_bound [Infinite K] (w : Fin N → ℤ)
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : IsHomogIdeal I)
    (ls : List (MvPolynomial (Fin N) K)) (hls : ∀ l ∈ ls, ∃ d, l.IsHomogeneous d) :
    ∃ (lam : K) (hlam : lam ≠ 0), ∀ i ≤ ls.length, ∀ e : ℕ,
      finrank K (quotDegreePart ((Ideal.map
            (weightScaleEquiv w hlam : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K) I
          ⊔ Ideal.ofList (ls.take i)).restrictScalars K) e)
        ≤ finrank K (quotDegreePart ((initialIdeal w I
          ⊔ Ideal.ofList (ls.take i)).restrictScalars K) e) := by
  classical
  set A : Fin (ls.length + 1) → Ideal (Polynomial (MvPolynomial (Fin N) K)) :=
    fun j => familyIdeal w I ⊔ Ideal.ofList (((ls.take (j : ℕ)).map Polynomial.C)) with hAdef
  have hAgr : ∀ j, IsXGradedIdeal (A j) := fun j =>
    isXGraded_sup_ofList_C (isXGraded_familyIdeal w hI) _
      (fun l hl => hls l (List.mem_of_mem_take hl))
  obtain ⟨lam, hlam0, hle⟩ := exists_generic_fibre_le A hAgr
  refine ⟨lam, hlam0, fun i hi e => ?_⟩
  have hfib := hle ⟨i, by omega⟩ e
  have hL : Ideal.map (famEval (MvPolynomial.C lam)) (A ⟨i, by omega⟩)
      = Ideal.map (weightScaleEquiv w hlam0 :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K) I
        ⊔ Ideal.ofList (ls.take i) := by
    rw [hAdef, Ideal.map_sup, map_famEval_familyIdeal w hlam0, map_famEval_ofList_C]
  have hR : Ideal.map (famEval (MvPolynomial.C (0 : K))) (A ⟨i, by omega⟩)
      = initialIdeal w I ⊔ Ideal.ofList (ls.take i) := by
    rw [hAdef, Ideal.map_sup, map_famEval_ofList_C, map_zero, map_famEval_zero_familyIdeal]
  rw [hL, hR] at hfib
  exact hfib

/-- Reading a regular sequence back as regularity of each stage. -/
theorem isRegularOn_of_isRegular {R : Type u} [CommRing R] (I : Ideal R) (rs : List R)
    (h : RingTheory.Sequence.IsRegular (R ⧸ I) rs) (i : ℕ) (hi : i < rs.length) :
    IsRegularOn (I ⊔ Ideal.ofList (rs.take i)) rs[i] := by
  have h1 := h.1.regular_mod_prev i hi
  rw [isSMulRegular_congr (quotSMulTopIdealEquiv I (Ideal.ofList (rs.take i)))] at h1
  exact (isSMulRegular_quotient_iff _ _).mp h1

/-- A unit ideal has empty quotient in every degree. -/
theorem finrank_quotDegreePart_top (e : ℕ)
    [FiniteDimensional K (homogeneousSubmodule (Fin N) K e)] :
    finrank K (quotDegreePart ((⊤ : Ideal (MvPolynomial (Fin N) K)).restrictScalars K) e) = 0 := by
  have hsub : Subsingleton (quotDegreePart
      ((⊤ : Ideal (MvPolynomial (Fin N) K)).restrictScalars K) e) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact trivial
  exact finrank_zero_of_subsingleton

/-- A proper ideal leaves a nonzero constant class in degree zero. -/
theorem finrank_quotDegreePart_zero_ne_zero {a : Ideal (MvPolynomial (Fin N) K)} (ha : a ≠ ⊤) :
    finrank K (quotDegreePart (a.restrictScalars K) 0) ≠ 0 := by
  intro h0
  have hfd : FiniteDimensional K (quotDegreePart (a.restrictScalars K) 0) := by
    infer_instance
  have hsub : Subsingleton (quotDegreePart (a.restrictScalars K) 0) :=
    Module.finrank_zero_iff.mp h0
  have hone : (1 : MvPolynomial (Fin N) K) ∈ homogeneousSubmodule (Fin N) K 0 :=
    MvPolynomial.isHomogeneous_one _ _
  have hmem : (⟨1, hone⟩ : homogeneousSubmodule (Fin N) K 0) ∈ degreePart (a.restrictScalars K) 0 := by
    have := Subsingleton.elim (Submodule.Quotient.mk (p := degreePart (a.restrictScalars K) 0)
      ⟨1, hone⟩) 0
    rwa [Submodule.Quotient.mk_eq_zero] at this
  exact ha (Ideal.eq_top_iff_one a |>.mpr hmem)

/-- **The degeneration transports a whole regular sequence.**  A regular sequence of linear forms on
the monomial degeneration deforms, by a single rescaling of the variables, to a regular sequence of
linear forms on the ideal itself. -/
theorem exists_isRegular_of_degeneration_homogeneous [Infinite K] (w : Fin N → ℤ)
    {I J : Ideal (MvPolynomial (Fin N) K)} (hI : IsHomogIdeal I) (hJ : IsHomogIdeal J)
    {S : Submodule K (MvPolynomial (Fin N) K)} (hS : IsGradedSubmodule S)
    (hIS : IsCompl (I.restrictScalars K) S) (hJS : IsCompl (J.restrictScalars K) S)
    (hJinit : J ≤ initialIdeal w I)
    (ls : List (MvPolynomial (Fin N) K)) (hls : ∀ l ∈ ls, l.IsHomogeneous 1)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin N) K ⧸ J) ls) :
    ∃ ls' : List (MvPolynomial (Fin N) K), ls'.length = ls.length ∧
      (∀ l ∈ ls', l.IsHomogeneous 1) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin N) K ⧸ I) ls' := by
  classical
  obtain ⟨lam, hlam, hbound⟩ :=
    exists_generic_degeneration_bound w hI ls (fun l hl => ⟨1, hls l hl⟩)
  set ψ : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K :=
    (weightScaleEquiv w hlam : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K) with hψ
  set f : MvPolynomial (Fin N) K → MvPolynomial (Fin N) K :=
    fun x => familyWeightScale w lam⁻¹ x with hfdef
  have hhom' : ∀ l ∈ ls.map f, l.IsHomogeneous 1 := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    exact isHomogeneous_familyWeightScale w (inv_ne_zero hlam) (hls x hx)
  have hmapls : ∀ i, ((ls.map f).take i).map (fun x => ψ x) = ls.take i := by
    intro i
    rw [← List.map_take, List.map_map]
    refine Eq.trans (List.map_congr_left ?_) (List.map_id _)
    intro a _
    exact (weightScaleEquiv w hlam).apply_symm_apply a
  have hmapI : ∀ i, Ideal.map ψ (I ⊔ Ideal.ofList ((ls.map f).take i))
      = Ideal.map ψ I ⊔ Ideal.ofList (ls.take i) := by
    intro i
    rw [Ideal.map_sup, map_ofList, hmapls i]
  have hsemi : ∀ i, i ≤ ls.length → ∀ e,
      finrank K (quotDegreePart ((I ⊔ Ideal.ofList ((ls.map f).take i)).restrictScalars K) e)
        ≤ finrank K (quotDegreePart ((J ⊔ Ideal.ofList (ls.take i)).restrictScalars K) e) := by
    intro i hi e
    have h1 : finrank K
        (quotDegreePart ((I ⊔ Ideal.ofList ((ls.map f).take i)).restrictScalars K) e)
        = finrank K (quotDegreePart
          ((Ideal.map ψ I ⊔ Ideal.ofList (ls.take i)).restrictScalars K) e) := by
      rw [← hmapI i, hψ]
      exact (finrank_quotDegreePart_map_weightScaleEquiv w hlam _ e).symm
    rw [h1]
    refine le_trans (hbound i hi e) ?_
    exact finrank_quotDegreePart_le_of_le
      (fun x hx => (sup_le_sup_right hJinit (Ideal.ofList (ls.take i))) hx) e
  have hIhom : ∀ i, IsHomogIdeal (I ⊔ Ideal.ofList ((ls.map f).take i)) := fun i =>
    isHomogIdeal_ofList_sup hI _ (fun l hl => ⟨1, hhom' l (List.mem_of_mem_take hl)⟩)
  have hJhom : ∀ i, IsHomogIdeal (J ⊔ Ideal.ofList (ls.take i)) := fun i =>
    isHomogIdeal_ofList_sup hJ _ (fun l hl => ⟨1, hls l (List.mem_of_mem_take hl)⟩)
  have hstepI : ∀ (i : ℕ) (hi : i < ls.length),
      (I ⊔ Ideal.ofList ((ls.map f).take i)) ⊔ Ideal.span {f ls[i]}
        = I ⊔ Ideal.ofList ((ls.map f).take (i + 1)) := by
    intro i hi
    rw [ofList_map_take_succ f ls i hi, ← sup_assoc]
  have hstepJ : ∀ (i : ℕ) (hi : i < ls.length),
      (J ⊔ Ideal.ofList (ls.take i)) ⊔ Ideal.span {ls[i]}
        = J ⊔ Ideal.ofList (ls.take (i + 1)) := by
    intro i hi
    rw [ofList_take_succ ls i hi, ← sup_assoc]
  have hregJ : ∀ (i : ℕ) (hi : i < ls.length), ∀ g : MvPolynomial (Fin N) K,
      ls[i] * g ∈ J ⊔ Ideal.ofList (ls.take i) → g ∈ J ⊔ Ideal.ofList (ls.take i) := fun i hi =>
    forall_mem_of_isRegularOn (isRegularOn_of_isRegular J ls hreg i hi)
  have hhomf : ∀ (i : ℕ) (hi : i < ls.length), (f ls[i]).IsHomogeneous 1 := fun i hi =>
    isHomogeneous_familyWeightScale w (inv_ne_zero hlam) (hls _ (List.getElem_mem hi))
  have hsemi' : ∀ (i : ℕ) (hi : i < ls.length), ∀ e,
      finrank K (quotDegreePart
          (((I ⊔ Ideal.ofList ((ls.map f).take i)) ⊔ Ideal.span {f ls[i]}).restrictScalars K)
          (1 + e))
        ≤ finrank K (quotDegreePart
          (((J ⊔ Ideal.ofList (ls.take i)) ⊔ Ideal.span {ls[i]}).restrictScalars K) (1 + e)) := by
    intro i hi e
    rw [hstepI i hi, hstepJ i hi]
    exact hsemi (i + 1) hi (1 + e)
  -- the invariant
  have hkey : ∀ i, i ≤ ls.length → ∀ e,
      finrank K (quotDegreePart ((I ⊔ Ideal.ofList ((ls.map f).take i)).restrictScalars K) e)
        = finrank K (quotDegreePart ((J ⊔ Ideal.ofList (ls.take i)).restrictScalars K) e) := by
    intro i
    induction i with
    | zero =>
      intro _ e
      rw [List.take_zero, List.take_zero, ofList_nil, sup_bot_eq, sup_bot_eq]
      exact finrank_quotDegreePart_eq_of_finrank_degreePart_eq e
        (finrank_degreePart_eq (isGradedSubmodule_of_isHomogIdeal hI)
          (isGradedSubmodule_of_isHomogIdeal hJ) hS hIS hJS e)
    | succ i ih =>
      intro hi
      have hi' : i < ls.length := by omega
      have hInv := ih (by omega)
      have hl : (ls[i]).IsHomogeneous 1 := hls _ (List.getElem_mem hi')
      have hregI := forall_mem_of_hilbert_le (hIhom i) (hJhom i) hInv hl (hhomf i hi')
        (hregJ i hi') (hsemi' i hi')
      have hnext := hilbert_eq_of_forall_mem (hIhom i) (hJhom i) hInv hl (hhomf i hi')
        (hregJ i hi') hregI
      intro e
      cases e with
      | zero =>
        have h0I : degreePart ((I ⊔ Ideal.ofList ((ls.map f).take (i + 1))).restrictScalars K) 0
            = degreePart ((I ⊔ Ideal.ofList ((ls.map f).take i)).restrictScalars K) 0 := by
          rw [← hstepI i hi']
          exact degreePart_sup_span_of_lt (hIhom i) (hhomf i hi') (by omega)
        have h0J : degreePart ((J ⊔ Ideal.ofList (ls.take (i + 1))).restrictScalars K) 0
            = degreePart ((J ⊔ Ideal.ofList (ls.take i)).restrictScalars K) 0 := by
          rw [← hstepJ i hi']
          exact degreePart_sup_span_of_lt (hJhom i) hl (by omega)
        rw [(Submodule.quotEquivOfEq _ _ h0I).finrank_eq,
          (Submodule.quotEquivOfEq _ _ h0J).finrank_eq]
        exact hInv 0
      | succ e =>
        have hn := hnext e
        rw [hstepI i hi', hstepJ i hi'] at hn
        rw [show e + 1 = 1 + e from by omega]
        exact hn
  refine ⟨ls.map f, List.length_map _, hhom', ?_⟩
  refine Extra.isRegular_quotient_of_isRegularOn I (ls.map f) ?_ ?_
  · intro i hi
    have hi' : i < ls.length := by rwa [List.length_map] at hi
    have hl : (ls[i]).IsHomogeneous 1 := hls _ (List.getElem_mem hi')
    have hregI := forall_mem_of_hilbert_le (hIhom i) (hJhom i) (hkey i (by omega)) hl
      (hhomf i hi') (hregJ i hi') (hsemi' i hi')
    rw [List.getElem_map]
    exact isRegularOn_of_forall_mem hregI
  · intro htop
    have hJne : J ⊔ Ideal.ofList ls ≠ ⊤ := by
      intro h
      exact hreg.2 ((Extra.smul_top_eq_top_iff J (Ideal.ofList ls)).mpr h)
    have h0 := hkey ls.length le_rfl 0
    have hlm : (ls.map f).take ls.length = ls.map f := by simp
    rw [hlm, List.take_length, htop, finrank_quotDegreePart_top] at h0
    exact finrank_quotDegreePart_zero_ne_zero hJne h0.symm

/-- **The degeneration transports a whole regular sequence**, without recording homogeneity. -/
theorem exists_isRegular_of_degeneration [Infinite K] (w : Fin N → ℤ)
    {I J : Ideal (MvPolynomial (Fin N) K)} (hI : IsHomogIdeal I) (hJ : IsHomogIdeal J)
    {S : Submodule K (MvPolynomial (Fin N) K)} (hS : IsGradedSubmodule S)
    (hIS : IsCompl (I.restrictScalars K) S) (hJS : IsCompl (J.restrictScalars K) S)
    (hJinit : J ≤ initialIdeal w I)
    (ls : List (MvPolynomial (Fin N) K)) (hls : ∀ l ∈ ls, l.IsHomogeneous 1)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin N) K ⧸ J) ls) :
    ∃ ls' : List (MvPolynomial (Fin N) K), ls'.length = ls.length ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin N) K ⧸ I) ls' := by
  obtain ⟨ls', h1, -, h3⟩ :=
    exists_isRegular_of_degeneration_homogeneous w hI hJ hS hIS hJS hJinit ls hls hreg
  exact ⟨ls', h1, h3⟩

end GaloisForLFunctions.HTGeometry
