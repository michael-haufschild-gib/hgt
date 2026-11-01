import GaloisForLFunctions.HeckeKreinToeplitz.Index.RadicalQuotientIsometries

/-!
# Common nonpositive lines modulo a finite radical

A negative direction survives removal of the radical. The complete signed
model of its Hilbert complement supplies a common nonpositive eigenvector,
whose lift is invariant modulo the original radical.
-/

noncomputable section
set_option autoImplicit false
open Complex

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E]

/-- A closed invariant subspace with a negative direction has a common
nonpositive line in its nondegenerate quotient by the radical. -/
theorem exists_common_nonpositive_line_mod_radical
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hc : ∀ i j v, T i (T j v) = T j (T i v))
    (W : Submodule ℂ (H × E)) (hW : IsClosed (W : Set (H × E)))
    (hi : IsBiInvariant T W) (hn : ∃ v ∈ W, (pairing v v).re < 0) :
    ∃ (s : H × E) (a : ι → ℂ), s ∈ W ∧ s ∉ restrictedRadical W ∧
      (pairing s s).re ≤ 0 ∧ ∀ i, a i ≠ 0 ∧ T i s - a i • s ∈ restrictedRadical W := by
  let S := radicalComplement W
  have hS : IsClosed (S : Set (H × E)) := isClosed_radicalComplement W hW
  letI : CompleteSpace (positiveKernel S) := (isClosed_positiveKernel S hS).completeSpace_coe
  obtain ⟨n, d, hd, e, he⟩ := exists_closed_signed_splitting S hS
    (restrictedRadical_radicalComplement W)
  let A : ι → S ≃L[ℂ] S := fun i => radicalQuotientEquiv W (T i) (hT i)
    (fun v hv => (hi i v hv).1) (fun v hv => (hi i v hv).2)
  have hA (i : ι) (u v : S) : pairing (A i u : H × E) (A i v : H × E) =
      pairing (u : H × E) (v : H × E) :=
    radicalQuotientEquiv_pairing W (T i) (hT i)
      (fun v hv => (hi i v hv).1) (fun v hv => (hi i v hv).2) u v
  have hAc (i j : ι) (v : S) : A i (A j v) = A j (A i v) :=
    radicalQuotientEquiv_commute W T hT hi hc i j v
  let C := fun i => (e.symm.trans (A i)).trans e
  have hC : ∀ i v w, pairing (C i v) (C i w) = pairing v w := by
    intro i v w
    change pairing (e (A i (e.symm v))) (e (A i (e.symm w))) = _
    rw [he, hA]
    simpa only [e.apply_symm_apply] using (he (e.symm v) (e.symm w)).symm
  have hCc : ∀ i j v, C i (C j v) = C j (C i v) := by
    intro i j v
    change e (A i (e.symm (e (A j (e.symm v))))) =
      e (A j (e.symm (e (A i (e.symm v)))))
    rw [e.symm_apply_apply, e.symm_apply_apply, hAc]
  obtain ⟨v, hvW, hvq⟩ := hn
  let v₀ : S := ⟨radicalRetraction W v, radicalRetraction_mem W hvW⟩
  have hv₀q : (pairing (e v₀) (e v₀)).re < 0 := by
    rw [he]
    change (pairing (radicalRetraction W v) (radicalRetraction W v)).re < 0
    rw [pairing_radicalRetraction W hvW hvW]
    exact hvq
  have hv₀ : e v₀ ≠ 0 := by
    intro hz
    have hzero : pairing (e v₀) (e v₀) = 0 := by simp [hz, pairing]
    rw [hzero, Complex.zero_re] at hv₀q
    exact (lt_irrefl 0) hv₀q
  have hsnd : (e v₀).2 ≠ 0 := fun h => hv₀ (eq_zero_of_nonpositive_snd_eq_zero hv₀q.le h)
  letI : Nontrivial (FiniteSignature.NegativeSpace d hd) := ⟨⟨(e v₀).2, 0, hsnd⟩⟩
  obtain ⟨w, a, hw, hwq, hwe⟩ := exists_common_nonpositive_eigenvector C hC hCc
  let s : S := e.symm w
  have hsne : (s : H × E) ≠ 0 := by
    intro hz
    have hs0 : s = 0 := Subtype.ext hz
    have he0 : e s = 0 := by rw [hs0, map_zero]
    exact hw (by simpa only [s, e.apply_symm_apply] using he0)
  have hsq : (pairing (s : H × E) (s : H × E)).re ≤ 0 := by
    have h := he s s
    change pairing (e (e.symm w)) (e (e.symm w)) = _ at h
    rw [e.apply_symm_apply] at h
    rw [← h]
    exact hwq
  refine ⟨s, a, s.property.1, ?_, hsq, ?_⟩
  · intro hsR
    exact hsne (eq_zero_of_mem_positiveOrthogonal (restrictedRadical W) hsR s.property.2)
  · intro i
    have heig : A i s = a i • s := by
      apply e.injective
      rw [map_smul]
      change C i w = a i • e (e.symm w)
      rw [e.apply_symm_apply]
      exact (hwe i).2
    have heig' : radicalRetraction W (T i (s : H × E)) = a i • (s : H × E) :=
      congrArg Subtype.val heig
    refine ⟨(hwe i).1, ?_⟩
    rw [← heig']
    exact sub_radicalRetraction_mem W _

#print axioms exists_common_nonpositive_line_mod_radical

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
