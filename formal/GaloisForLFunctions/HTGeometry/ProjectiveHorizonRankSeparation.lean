import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetDeterminant

/-!
# Rank separation of horizon fields

The determinant of the square jet array indexed by a covector span `t` is invariant under the
observer group `G_t`, because the rows indexed by `t` transform by the `t`-block of the inverse,
which is unimodular and has no entries outside `t`.

A transvection whose column lies outside `t` replaces one row of that array by itself minus a
multiple of a row labelled outside `t`, and the replaced array is still nondegenerate.  So the jet
determinant is moved, and adding a direction to a span always shrinks its horizon field.  With the
reduction already available, the horizon-field assignment is injective.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The jet determinant of a covector span. -/
def jetDet (t : Finset n) : HomogeneousJetField n K :=
  (jetArray t fun m => (m : n)).det

omit [Fintype n] in
theorem jetDet_ne_zero (t : Finset n) : jetDet (K := K) t ≠ 0 :=
  jetArray_det_ne_zero t Subtype.coe_injective

/-! ## Invariance under the observer group -/

/-- On a jet indexed by `t`, an observer of `t` acts through its `t`-block. -/
theorem linearJetAction_freeCoordinate_of_mem {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) (m : ↥t) (l : ℕ) :
    g • freeCoordinate K (n × ℕ) ((m : n), l) =
      ∑ q : ↥t, algebraMap K (HomogeneousJetField n K)
        (blockRestrict t (g⁻¹ : SpecialLinearGroup n K) m q) *
          freeCoordinate K (n × ℕ) ((q : n), l) := by
  have hginv : (g⁻¹ : SpecialLinearGroup n K) ∈
      chartSubsetStabilizer (K := K) (↑t : Set n) := inv_mem hg
  have hvanish : ∀ q ∈ (Finset.univ : Finset n), q ∉ t →
      algebraMap K (HomogeneousJetField n K)
          (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) (m : n) q) *
        freeCoordinate K (n × ℕ) (q, l) = 0 := by
    intro q _ hq
    rw [coe_apply_eq_zero_of_mem_chartSubsetStabilizer hginv m.2 hq, map_zero, zero_mul]
  rw [linearJetAction_freeCoordinate]
  calc ∑ q : n, algebraMap K (HomogeneousJetField n K)
        (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) (m : n) q) *
          freeCoordinate K (n × ℕ) (q, l)
      = ∑ q ∈ t, algebraMap K (HomogeneousJetField n K)
          (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) (m : n) q) *
            freeCoordinate K (n × ℕ) (q, l) :=
        (Finset.sum_subset (Finset.subset_univ t) hvanish).symm
    _ = _ := (Finset.sum_coe_sort t _).symm

/-- **Invariance of the jet determinant.**  The jet determinant of `t` is fixed by every observer
of `t`. -/
theorem jetDet_invariant {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) :
    g • jetDet (K := K) t = jetDet t := by
  have hginv : (g⁻¹ : SpecialLinearGroup n K) ∈
      chartSubsetStabilizer (K := K) (↑t : Set n) := inv_mem hg
  have hmap : (jetArray (K := K) t fun m => (m : n)).map
        ((linearJetFieldEquiv g : HomogeneousJetField n K →+* HomogeneousJetField n K)) =
      ((blockRestrict t (g⁻¹ : SpecialLinearGroup n K)).map
        (algebraMap K (HomogeneousJetField n K))) * (jetArray t fun m => (m : n)) := by
    ext m c
    rw [Matrix.map_apply, jetArray, Matrix.of_apply, Matrix.mul_apply]
    show linearJetFieldEquiv g (freeCoordinate K (n × ℕ) ((m : n), jetOrder t c)) = _
    rw [← linearJetAction_apply, linearJetAction_freeCoordinate_of_mem hg m (jetOrder t c)]
    exact Finset.sum_congr rfl fun q _ => rfl
  have hdetB : ((blockRestrict t (g⁻¹ : SpecialLinearGroup n K)).map
      (algebraMap K (HomogeneousJetField n K))).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_blockRestrict hginv, map_one]
  have hF : g • (jetArray (K := K) t fun m => (m : n)).det =
      ((linearJetFieldEquiv g : HomogeneousJetField n K →+* HomogeneousJetField n K))
        (jetArray (K := K) t fun m => (m : n)).det := rfl
  rw [jetDet, hF, RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_mul, hdetB,
    one_mul]

/-! ## Motion under an outside transvection -/

omit [Fintype n] in
/-- Replacing one row label of the jet array by a label outside `t` keeps it nondegenerate. -/
theorem jetArray_update_det_ne_zero {t : Finset n} {i : n} (hi : i ∉ t) (m₀ : ↥t) :
    (jetArray (K := K) t (Function.update (fun m => (m : n)) m₀ i)).det ≠ 0 := by
  refine jetArray_det_ne_zero t ?_
  intro a b hab
  by_cases ha : a = m₀ <;> by_cases hb : b = m₀
  · rw [ha, hb]
  · rw [ha, Function.update_self, Function.update_of_ne hb] at hab
    exact absurd (hab ▸ b.2) hi
  · rw [hb, Function.update_self, Function.update_of_ne ha] at hab
    exact absurd (hab ▸ a.2) hi
  · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
    exact Subtype.ext hab

/-- **Motion of the jet determinant.**  A transvection with a row inside `t` and column outside `t`
moves the jet determinant of `t`. -/
theorem jetDet_not_invariant {t : Finset n} {i : n} (hi : i ∉ t) (m₀ : ↥t)
    (hm₀ : (m₀ : n) ≠ i) :
    (transvectionSL (m₀ : n) i hm₀ (1 : K)) • jetDet (K := K) t ≠ jetDet t := by
  set g : SpecialLinearGroup n K := transvectionSL (m₀ : n) i hm₀ 1 with hgdef
  set A : Matrix ↥t ↥t (HomogeneousJetField n K) := jetArray t (fun m => (m : n)) with hAdef
  set A' : Matrix ↥t ↥t (HomogeneousJetField n K) :=
    jetArray t (Function.update (fun m => (m : n)) m₀ i) with hA'def
  have hrow : ∀ (m : ↥t) (c : ↥t),
      g • freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) =
        if m = m₀ then
          freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) -
            freeCoordinate K (n × ℕ) (i, jetOrder t c)
        else freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) := by
    intro m c
    rw [linearJetAction_freeCoordinate, hgdef, transvectionSL_inv]
    have hentry : ∀ q : n, ((transvectionSL (m₀ : n) i hm₀ (-1 : K) :
        SpecialLinearGroup n K) : Matrix n n K) (m : n) q =
        (1 : Matrix n n K) (m : n) q +
          (if m = m₀ then (if i = q then -1 else 0) else 0) := by
      intro q
      show Matrix.transvection (m₀ : n) i (-1 : K) (m : n) q = _
      by_cases hmm : m = m₀
      · rw [hmm]
        rw [transvection_row_self]
        by_cases hq : i = q <;> simp [hq]
      · have hne : (m₀ : n) ≠ (m : n) := fun hcon => hmm (Subtype.ext hcon.symm)
        rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply,
          if_neg (fun h => hne h.1), add_zero]
        simp [hmm]
    rw [Finset.sum_congr rfl fun q _ => by rw [hentry q, map_add, add_mul]]
    rw [Finset.sum_add_distrib]
    have hfirst : ∑ q : n, algebraMap K (HomogeneousJetField n K) ((1 : Matrix n n K) (m : n) q) *
        freeCoordinate K (n × ℕ) (q, jetOrder t c) =
        freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) := by
      rw [Finset.sum_eq_single (m : n)]
      · rw [Matrix.one_apply_eq, map_one, one_mul]
      · intro q _ hq
        rw [Matrix.one_apply_ne (Ne.symm hq), map_zero, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ (m : n)) hcon
    rw [hfirst]
    by_cases hmm : m = m₀
    · rw [if_pos hmm]
      have hsecond : ∑ q : n, algebraMap K (HomogeneousJetField n K)
          (if m = m₀ then (if i = q then (-1 : K) else 0) else 0) *
            freeCoordinate K (n × ℕ) (q, jetOrder t c) =
          -freeCoordinate K (n × ℕ) (i, jetOrder t c) := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos hmm, if_pos rfl, map_neg, map_one, neg_one_mul]
        · intro q _ hq
          rw [if_pos hmm, if_neg (Ne.symm hq), map_zero, zero_mul]
        · intro hcon
          exact absurd (Finset.mem_univ i) hcon
      rw [hsecond, sub_eq_add_neg]
    · rw [if_neg hmm]
      have hsecond : ∑ q : n, algebraMap K (HomogeneousJetField n K)
          (if m = m₀ then (if i = q then (-1 : K) else 0) else 0) *
            freeCoordinate K (n × ℕ) (q, jetOrder t c) = 0 := by
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [if_neg hmm, map_zero, zero_mul]
      rw [hsecond, add_zero]
  have hA_apply : ∀ m c : ↥t, A m c = freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) :=
    fun _ _ => rfl
  have hA'_apply : ∀ m c : ↥t, A' m c =
      freeCoordinate K (n × ℕ)
        (Function.update (fun m : ↥t => (m : n)) m₀ i m, jetOrder t c) := fun _ _ => rfl
  have hmap : A.map ((linearJetFieldEquiv g :
        HomogeneousJetField n K →+* HomogeneousJetField n K)) =
      Matrix.updateRow A m₀ (A m₀ - A' m₀) := by
    ext m c
    rw [Matrix.map_apply, hA_apply]
    have hshift : ((linearJetFieldEquiv g :
        HomogeneousJetField n K →+* HomogeneousJetField n K))
          (freeCoordinate K (n × ℕ) ((m : n), jetOrder t c)) =
        g • freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) := rfl
    rw [hshift, hrow m c]
    by_cases hmm : m = m₀
    · subst hmm
      rw [if_pos rfl, Matrix.updateRow_self, Pi.sub_apply, hA_apply, hA'_apply,
        Function.update_self]
    · rw [if_neg hmm, Matrix.updateRow_ne hmm, hA_apply]
  intro hcon
  have hArow : Matrix.updateRow A m₀ (A' m₀) = A' := by
    ext m c
    by_cases hmm : m = m₀
    · subst hmm
      rw [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hmm, hA_apply, hA'_apply, Function.update_of_ne hmm]
  have hstep : (Matrix.updateRow A m₀ (A m₀ - A' m₀)).det = A.det - A'.det := by
    rw [sub_eq_add_neg, ← neg_one_smul (HomogeneousJetField n K) (A' m₀),
      Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hArow,
      neg_one_mul, ← sub_eq_add_neg]
  have hdet : A.det - A'.det = A.det := by
    calc A.det - A'.det = (Matrix.updateRow A m₀ (A m₀ - A' m₀)).det := hstep.symm
      _ = (A.map ((linearJetFieldEquiv g :
            HomogeneousJetField n K →+* HomogeneousJetField n K))).det := by rw [hmap]
      _ = g • A.det := by
            rw [show g • A.det =
              ((linearJetFieldEquiv g : HomogeneousJetField n K →+* HomogeneousJetField n K))
                A.det from rfl, RingHom.map_det, RingHom.mapMatrix_apply]
      _ = A.det := hcon
  exact jetArray_update_det_ne_zero hi m₀ (sub_eq_self.1 hdet)

/-! ## One-step strictness and injectivity -/

/-- **One-step strictness.**  Adding a direction to a covector span strictly shrinks its horizon
field. -/
theorem horizonField_insert_ne [Nontrivial n] {t : Finset n} {i : n} (hi : i ∉ t) :
    horizonField (K := K) (insert i (↑t : Set n)) ≠ horizonField (K := K) (↑t : Set n) := by
  intro hcon
  rcases t.eq_empty_or_nonempty with rfl | ⟨m₀, hm₀⟩
  · obtain ⟨j, hj⟩ := exists_ne i
    have hmem : freeCoordinate K (n × ℕ) (j, 0) ∈
        horizonField (K := K) (↑(∅ : Finset n) : Set n) := by
      rw [mem_horizonField_iff]
      rintro g ⟨k, hk, -⟩
      simp only [Finset.coe_empty, Set.mem_empty_iff_false] at hk
    rw [← hcon] at hmem
    refine freeCoordinate_notMem_horizonField_of_ne (K := K) hj 0 ?_
    simpa using hmem
  · have hm₀i : ((⟨m₀, hm₀⟩ : ↥t) : n) ≠ i := fun h => hi (h ▸ hm₀)
    have hinv : jetDet (K := K) t ∈ horizonField (K := K) (↑t : Set n) := by
      rw [mem_horizonField_iff']
      intro g hg
      exact jetDet_invariant hg
    rw [← hcon] at hinv
    have hgmem : transvectionSL ((⟨m₀, hm₀⟩ : ↥t) : n) i hm₀i (1 : K) ∈
        chartSubsetStabilizer (K := K) (insert i (↑t : Set n)) :=
      transvectionSL_mem_chartSubsetStabilizer (Set.mem_insert i _) hm₀i (1 : K)
    exact jetDet_not_invariant hi ⟨m₀, hm₀⟩ hm₀i
      ((mem_horizonField_iff'.1 hinv) _ hgmem)

/-- **Injectivity of the horizon-field assignment.**  Distinct covector spans have distinct horizon
fields, so `S ↦ mathcal I_S` embeds the span lattice into the lattice of differential subfields. -/
theorem horizonField_injective [Nontrivial n] :
    Function.Injective (horizonField (n := n) (K := K)) := by
  classical
  refine horizonField_injective_of_ne_insert ?_
  intro s i hi
  have hs : (↑(s.toFinset) : Set n) = s := Set.coe_toFinset s
  have hi' : i ∉ s.toFinset := by simpa using hi
  have hstrict := horizonField_insert_ne (K := K) hi'
  rwa [hs] at hstrict

end

end GaloisForLFunctions.HTGeometry
