import GaloisForLFunctions.HeckeKreinToeplitz.Index.CommonEigenlineModuloRadical

/-!
# Invariant nonpositive subspaces with nonnegative complements

Nonpositive subspaces have bounded finite dimension. A maximal invariant
one has nonnegative signed orthogonal complement: otherwise a common line
in the radical quotient would enlarge it.
-/

noncomputable section
set_option autoImplicit false
open Complex Module
open scoped ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Every vector in the subspace has a nonpositive square. -/
def IsNonpositiveSubspace (U : Submodule ℂ (H × E)) : Prop :=
  ∀ v ∈ U, (pairing v v).re ≤ 0

theorem nonpositive_snd_injective (U : Submodule ℂ (H × E))
    (hU : IsNonpositiveSubspace U) :
    Function.Injective ((LinearMap.snd ℂ H E).comp U.subtype) := by
  intro u v huv
  have hs : ((u - v : U) : H × E).2 = 0 := sub_eq_zero.mpr huv
  have hz := eq_zero_of_nonpositive_snd_eq_zero (hU (u - v) (u - v).property) hs
  exact sub_eq_zero.mp (Subtype.ext hz)

theorem finiteDimensional_of_nonpositive [FiniteDimensional ℂ E]
    (U : Submodule ℂ (H × E)) (hU : IsNonpositiveSubspace U) : FiniteDimensional ℂ U :=
  Module.Finite.of_injective ((LinearMap.snd ℂ H E).comp U.subtype)
    (nonpositive_snd_injective U hU)

theorem finrank_nonpositive_le [FiniteDimensional ℂ E]
    (U : Submodule ℂ (H × E)) (hU : IsNonpositiveSubspace U) : finrank ℂ U ≤ finrank ℂ E := by
  letI := finiteDimensional_of_nonpositive U hU
  exact LinearMap.finrank_le_finrank_of_injective (nonpositive_snd_injective U hU)

/-- Bounded dimensions give a maximal invariant nonpositive subspace. -/
theorem exists_maximal_dimension_invariant_nonpositive [FiniteDimensional ℂ E] {ι : Type*}
    (T : ι → (H × E) ≃L[ℂ] (H × E)) :
    ∃ U : Submodule ℂ (H × E), IsBiInvariant T U ∧ IsNonpositiveSubspace U ∧
      ∀ V : Submodule ℂ (H × E), IsBiInvariant T V → IsNonpositiveSubspace V →
        finrank ℂ V ≤ finrank ℂ U := by
  classical
  let P (n : ℕ) := ∃ U : Submodule ℂ (H × E),
    IsBiInvariant T U ∧ IsNonpositiveSubspace U ∧ finrank ℂ U = n
  have h0 : P 0 := by
    refine ⟨⊥, ?_, ?_, finrank_bot ℂ (H × E)⟩
    · intro i v hv
      have hz := (Submodule.mem_bot ℂ).mp hv
      subst v
      simp only [map_zero, Submodule.zero_mem, and_self]
    · intro v hv
      have hz := (Submodule.mem_bot ℂ).mp hv
      subst v
      simp [pairing]
  obtain ⟨U, hiU, hnU, hdU⟩ := Nat.findGreatest_spec (Nat.zero_le (finrank ℂ E)) h0
  refine ⟨U, hiU, hnU, ?_⟩
  intro V hiV hnV
  rw [hdU]
  exact Nat.le_findGreatest (finrank_nonpositive_le V hnV) ⟨V, hiV, hnV, rfl⟩

/-- A common line modulo an invariant space enlarges it invariantly in both directions. -/
theorem isBiInvariant_sup_span_of_modulo {ι : Type*}
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (U : Submodule ℂ (H × E)) (hi : IsBiInvariant T U)
    (s : H × E) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (he : ∀ i, T i s - a i • s ∈ U) : IsBiInvariant T (U ⊔ ℂ ∙ s) := by
  let V := U ⊔ ℂ ∙ s
  have hs : s ∈ V := (le_sup_right : ℂ ∙ s ≤ V) (Submodule.mem_span_singleton_self s)
  have hf (i : ι) : T i s ∈ V := by
    have hm := V.add_mem ((le_sup_left : U ≤ V) (he i)) (V.smul_mem (a i) hs)
    simpa only [sub_add_cancel] using hm
  have hb (i : ι) : (T i).symm s ∈ V := by
    have hr : (T i).symm (T i s - a i • s) ∈ U := (hi i _ (he i)).2
    have heq : a i • (T i).symm s = s - (T i).symm (T i s - a i • s) := by
      rw [map_sub, map_smul, (T i).symm_apply_apply, sub_sub_cancel]
    have hm : a i • (T i).symm s ∈ V := by
      rw [heq]
      exact V.sub_mem hs ((le_sup_left : U ≤ V) hr)
    have h := V.smul_mem (a i)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ (ha i), one_smul] using h
  intro i v hv
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  constructor
  · rw [map_add, map_smul]
    exact V.add_mem ((le_sup_left : U ≤ V) (hi i u hu).1) (V.smul_mem c (hf i))
  · rw [map_add, map_smul]
    exact V.add_mem ((le_sup_left : U ≤ V) (hi i u hu).2) (V.smul_mem c (hb i))

/-- Adjoining an orthogonal nonpositive vector preserves nonpositivity. -/
theorem isNonpositiveSubspace_sup_span (U : Submodule ℂ (H × E))
    (hU : IsNonpositiveSubspace U) {s : H × E}
    (ho : s ∈ signedOrthogonal U) (hs : (pairing s s).re ≤ 0) :
    IsNonpositiveSubspace (U ⊔ ℂ ∙ s) := by
  intro v hv
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have horth (u : U) : pairing s (U.subtype u) = 0 := by
    change pairing s (u : H × E) = 0
    rw [← pairing_conj_symm, (mem_signedOrthogonal U s).mp ho u u.property, map_zero]
  have h := pairing_adjoinVector_self U.subtype s horth ⟨u, hu⟩ c
  change pairing (u + c • s) (u + c • s) = _ at h
  rw [h, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact add_nonpos (hU u hu) (mul_nonpos_of_nonneg_of_nonpos (normSq_nonneg c) hs)

/-- Commuting finite-index isometries admit a finite invariant nonpositive
subspace whose signed orthogonal complement is nonnegative. -/
theorem exists_invariant_nonpositive_with_nonnegative_complement
    [CompleteSpace H] [CompleteSpace E] [FiniteDimensional ℂ E] {ι : Type*}
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hc : ∀ i j v, T i (T j v) = T j (T i v)) :
    ∃ U : Submodule ℂ (H × E), IsBiInvariant T U ∧ IsNonpositiveSubspace U ∧
      finrank ℂ U ≤ finrank ℂ E ∧
      ∀ v ∈ signedOrthogonal U, 0 ≤ (pairing v v).re := by
  classical
  obtain ⟨U, hiU, hnU, hmax⟩ := exists_maximal_dimension_invariant_nonpositive T
  letI := finiteDimensional_of_nonpositive U hnU
  have hU : IsClosed (U : Set (H × E)) := U.closed_of_finiteDimensional
  refine ⟨U, hiU, hnU, finrank_nonpositive_le U hnU, ?_⟩
  intro v hv
  by_contra hvn
  have hvneg : (pairing v v).re < 0 := lt_of_not_ge hvn
  obtain ⟨s, a, hsW, hsR, hsq, he⟩ := exists_common_nonpositive_line_mod_radical
    T hT hc (signedOrthogonal U) (isClosed_signedOrthogonal U)
    (isBiInvariant_signedOrthogonal T hT U hiU) ⟨v, hv, hvneg⟩
  have hRU : restrictedRadical (signedOrthogonal U) ≤ U := by
    rw [restrictedRadical_signedOrthogonal U hU]
    exact inf_le_right
  have hsU : s ∉ U := by
    intro hs
    apply hsR
    rw [restrictedRadical_signedOrthogonal U hU]
    exact ⟨hsW, hs⟩
  let V := U ⊔ ℂ ∙ s
  have hiV : IsBiInvariant T V := isBiInvariant_sup_span_of_modulo T U hiU s a
    (fun i => (he i).1) (fun i => hRU (he i).2)
  have hnV : IsNonpositiveSubspace V := isNonpositiveSubspace_sup_span U hnU hsW hsq
  letI := finiteDimensional_of_nonpositive V hnV
  have hlt : U < V := by
    apply lt_of_le_of_ne le_sup_left
    intro h
    apply hsU
    rw [h]
    exact (le_sup_right : ℂ ∙ s ≤ V) (Submodule.mem_span_singleton_self s)
  exact (not_lt_of_ge (hmax V hiV hnV)) (Submodule.finrank_lt_finrank_of_lt hlt)

#print axioms exists_invariant_nonpositive_with_nonnegative_complement

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
