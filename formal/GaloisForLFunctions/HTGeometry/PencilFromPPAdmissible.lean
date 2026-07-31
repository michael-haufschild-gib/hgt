import GaloisForLFunctions.HTGeometry.PencilSRRealization
import GaloisForLFunctions.HTGeometry.PPMatrixRankFormula

/-!
# A periodic pencil realizes its complex entirely in the same dimension

An admissible facet-evaluation configuration of `PPMatrixRankFormula` is exactly a periodic-pencil
separation: the facet form `U B` becomes the additive phase `L_B z = 2πi ∑ᵢ U B i · zᵢ`, the
integrality condition off the facet says `exp (L_B (a v)) = 1`, and the `ℚ`-independence of
`{1} ∪ {M B v : v ∈ B}` says exactly that the steps inside the facet are integrally independent
modulo those periods.

Feeding this into `PencilSeparation.entireSRRealization` turns every periodic-pencil separation in
dimension `d` into an entire `d`-variable Stanley–Reisner realization, so the intrinsic realization
dimension never exceeds the periodic-pencil dimension.

* `facetForm` — the phase of a facet form;
* `pencilOfPPAdmissible` — the pencil separation of an admissible configuration;
* `entireSRRealization_of_ppAdmissible`, `srRealizableDim_of_ppAdmissible` — the realization;
* `htDim_le_ppDim` — the comparison of the two dimensions.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Classical

noncomputable section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-! ### The phase of a facet form -/

/-- The additive phase attached to a facet form. -/
def facetForm {d : ℕ} (c : Fin d → ℂ) : (Fin d → ℂ) →ₗ[ℂ] ℂ where
  toFun z := 2 * Real.pi * Complex.I * ∑ i, c i * z i
  map_add' x y := by
    show 2 * Real.pi * Complex.I * ∑ i, c i * (x i + y i) = _
    have h : ∑ i, c i * (x i + y i) = (∑ i, c i * x i) + ∑ i, c i * y i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h]
    ring
  map_smul' r x := by
    show 2 * Real.pi * Complex.I * ∑ i, c i * (r * x i) = _
    have h : ∑ i, c i * (r * x i) = r * ∑ i, c i * x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h]
    show _ = r * (2 * Real.pi * Complex.I * ∑ i, c i * x i)
    ring

@[simp] theorem facetForm_apply {d : ℕ} (c : Fin d → ℂ) (z : Fin d → ℂ) :
    facetForm c z = 2 * Real.pi * Complex.I * ∑ i, c i * z i := rfl

theorem differentiable_facetForm {d : ℕ} (c : Fin d → ℂ) :
    Differentiable ℂ fun z : Fin d → ℂ => facetForm c z := by
  show Differentiable ℂ fun z : Fin d → ℂ => 2 * Real.pi * Complex.I * ∑ i, c i * z i
  exact (Differentiable.fun_sum fun i _ => (differentiable_apply i).const_mul _).const_mul _

theorem surjective_facetForm {d : ℕ} {c : Fin d → ℂ} (hc : c ≠ 0) :
    Function.Surjective fun z : Fin d → ℂ => facetForm c z := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    exact hc (funext fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  intro w
  set z₀ : Fin d → ℂ := Pi.single i₀ (w / (2 * Real.pi * Complex.I * c i₀)) with hz₀
  refine ⟨z₀, ?_⟩
  have hsum : ∑ i, c i * z₀ i
      = c i₀ * (w / (2 * Real.pi * Complex.I * c i₀)) := by
    rw [hz₀]
    rw [Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ i₀) hcon
  show facetForm c z₀ = w
  rw [facetForm_apply, hsum]
  field_simp

/-! ### The pencil separation of an admissible configuration -/

/-- The facet family of a facet system, as a finite set of finite sets. -/
def facetFinset (faces : A → Finset V) : Finset (Finset V) := Finset.univ.image faces

omit [Fintype V] [DecidableEq A] in
theorem mem_facetFinset {faces : A → Finset V} {F : Finset V} :
    F ∈ facetFinset faces ↔ ∃ B, faces B = F := by
  simp [facetFinset]

/-- A representing index of a facet. -/
def facetIndex (faces : A → Finset V) (F : Finset V) [Nonempty A] : A :=
  if h : ∃ B, faces B = F then h.choose else Classical.arbitrary A

omit [Fintype V] [DecidableEq A] in
theorem faces_facetIndex {faces : A → Finset V} [Nonempty A] {F : Finset V}
    (hF : F ∈ facetFinset faces) : faces (facetIndex faces F) = F := by
  have h : ∃ B, faces B = F := mem_facetFinset.mp hF
  rw [facetIndex, dif_pos h]
  exact h.choose_spec

/-- **The pencil separation of an admissible configuration.** -/
def pencilOfPPAdmissible {d : ℕ} [Nonempty A] (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty) (a : V → Fin d → ℂ) (U : A → Fin d → ℂ)
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    PencilSeparation (facetFinset faces) (Fin d → ℂ) where
  ω := a
  phase := fun F => (facetForm (U (facetIndex faces F))).toAddMonoidHom
  phase_surjective := by
    intro F hF
    obtain ⟨hint, hli⟩ := hadm (facetIndex faces F)
    obtain ⟨v₀, hv₀⟩ := hne (facetIndex faces F)
    have hUne : U (facetIndex faces F) ≠ 0 := by
      intro h0
      have hz := hli.ne_zero (some ⟨v₀, hv₀⟩)
      refine hz ?_
      show (∑ i, U (facetIndex faces F) i * a v₀ i) = 0
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [show U (facetIndex faces F) i = 0 from congrFun h0 i, zero_mul]
    exact surjective_facetForm hUne
  outside := by
    intro F hF v hv
    obtain ⟨hint, _⟩ := hadm (facetIndex faces F)
    have hvF : v ∉ faces (facetIndex faces F) := by rw [faces_facetIndex hF]; exact hv
    obtain ⟨n, hn⟩ := hint v hvF
    show Complex.exp (facetForm (U (facetIndex faces F)) (a v)) = 1
    rw [facetForm_apply]
    have hval : (∑ i, U (facetIndex faces F) i * a v i) = (n : ℂ) := hn
    rw [hval]
    exact Complex.exp_eq_one_iff.mpr ⟨n, by ring⟩
  inside := by
    intro F hF g hg v hv
    obtain ⟨_, hli⟩ := hadm (facetIndex faces F)
    set B := facetIndex faces F with hB
    have hFB : faces B = F := faces_facetIndex hF
    have hphase : ∀ w : V, (facetForm (U B) (a w))
        = 2 * Real.pi * Complex.I * (∑ i, U B i * a w i) := fun w => rfl
    have hexp : Complex.exp (2 * Real.pi * Complex.I *
        ∑ w ∈ F, (g w : ℂ) * (∑ i, U B i * a w i)) = 1 := by
      have hrw : (∑ w ∈ F, (g w : ℂ) * (facetForm (U B)) (a w))
          = 2 * Real.pi * Complex.I * ∑ w ∈ F, (g w : ℂ) * (∑ i, U B i * a w i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hphase w]
        ring
      rw [← hrw]
      exact hg
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
    have hksum : (∑ w ∈ F, (g w : ℂ) * (∑ i, U B i * a w i)) = (k : ℂ) := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      field_simp at hk ⊢
      linear_combination hk
    set c : Option (faces B) → ℚ := fun i => i.elim (-(k : ℚ)) fun w => (g (w : V) : ℚ) with hc
    have hzero : ∑ i, c i • (fun i : Option (faces B) =>
        i.elim (1 : ℂ) fun w => (fun B v => ∑ j, U B j * a v j) B (w : V)) i = 0 := by
      rw [Fintype.sum_option]
      have h1 : c none • (1 : ℂ) = -(k : ℂ) := by
        rw [hc]
        show ((-(k : ℚ)) : ℚ) • (1 : ℂ) = _
        rw [Rat.smul_def, mul_one]
        push_cast
        ring
      have h2 : ∑ w : faces B, c (some w) •
          ((fun B v => ∑ j, U B j * a v j) B (w : V))
          = ∑ w ∈ F, (g w : ℂ) * (∑ j, U B j * a w j) := by
        rw [← hFB]
        rw [← Finset.sum_coe_sort (faces B)]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hc]
        show ((g (w : V) : ℚ)) • (∑ j, U B j * a (w : V) j) = _
        rw [Rat.smul_def]
        push_cast
        ring
      show c none • (1 : ℂ)
        + ∑ w : faces B, c (some w) • (∑ j, U B j * a (w : V) j) = 0
      rw [h1, h2, hksum]
      ring
    have hcz := Fintype.linearIndependent_iff.mp hli c hzero
    have hgv := hcz (some ⟨v, by rw [hFB]; exact hv⟩)
    rw [hc] at hgv
    have hgv' : ((g v : ℤ) : ℚ) = 0 := hgv
    exact_mod_cast hgv'

/-! ### The realization and the dimension comparison -/

omit [Fintype V] [DecidableEq A] in
/-- **An admissible configuration realizes its complex entirely in the same dimension.** -/
theorem entireSRRealization_of_ppAdmissible {d : ℕ} [Nonempty A] (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty)
    (hanti : FacetAntichain (↑(facetFinset faces) : Set (Finset V)))
    (a : V → Fin d → ℂ) (hindep : LinearIndependent ℚ a) (U : A → Fin d → ℂ)
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    Nonempty (EntireSRRealization d (facetFinset faces)) :=
  ⟨(pencilOfPPAdmissible faces hne a U hadm).entireSRRealization hindep
    (fun _ _ => differentiable_facetForm _) hanti⟩

/-- Realizability of a complex in a prescribed number of variables. -/
def SRRealizableDim (facets : Finset (Finset V)) (d : ℕ) : Prop :=
  Nonempty (EntireSRRealization d facets)

/-- The intrinsic realization dimension. -/
def srDim (facets : Finset (Finset V)) : ℕ := sInf {d | SRRealizableDim facets d}

omit [Fintype V] [DecidableEq A] in
/-- **The intrinsic realization dimension is at most any periodic-pencil dimension.** -/
theorem srDim_le_of_ppAdmissible {d : ℕ} [Nonempty A] (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty)
    (hanti : FacetAntichain (↑(facetFinset faces) : Set (Finset V)))
    (a : V → Fin d → ℂ) (hindep : LinearIndependent ℚ a) (U : A → Fin d → ℂ)
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    srDim (facetFinset faces) ≤ d :=
  Nat.sInf_le (entireSRRealization_of_ppAdmissible faces hne hanti a hindep U hadm)

omit [Fintype V] [DecidableEq A] in
/-- **`htDim ≤ ppDim`.**  Whenever the periodic-pencil dimension is attained, the intrinsic
realization dimension does not exceed it. -/
theorem srDim_le_ppDim [Nonempty A] (faces : A → Finset V) (hne : ∀ B, (faces B).Nonempty)
    (hanti : FacetAntichain (↑(facetFinset faces) : Set (Finset V)))
    (hattained : {d | ∃ (a : V → Fin d → ℂ), LinearIndependent ℚ a ∧
      ∃ (U : A → Fin d → ℂ), PPAdmissible faces (fun B v => ∑ i, U B i * a v i)}.Nonempty) :
    srDim (facetFinset faces) ≤ ppDim faces := by
  obtain ⟨a, hindep, U, hadm⟩ := Nat.sInf_mem hattained
  exact srDim_le_of_ppAdmissible faces hne hanti a hindep U hadm

end

end GaloisForLFunctions.HTGeometry
