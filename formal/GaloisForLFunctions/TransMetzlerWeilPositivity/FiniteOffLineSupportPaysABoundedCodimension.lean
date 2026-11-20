import GaloisForLFunctions.TransMetzlerWeilPositivity.ZeroSideStratum
import GaloisForLFunctions.HTGeometry.NativeObserverUniversalDescentInertiaLaw
import GaloisForLFunctions.RHTower.SeamPolarizationWeld

/-!
# Finite off-line support pays a bounded codimension

If `ζ` has finitely many zeros off the critical line, the complete Weil form on every atomic
family `Σ y_i atomDilate φ (c/N) (u - log(i + 1))` is nonnegative on a coefficient subspace of
`ℝ^N` of codimension at most `#rightZeros`, uniformly in the overlap `c`, the horizon `N` and the
profile `φ`.

The atomic Weil Gram is the complexification of the real Weil pairing. A real negative-definite
subspace keeps its dimension and its negativity under complexification, so the real negative index
is at most the Hermitian negative index, which the Krein index of `zetaKernel` bounds by
`#rightZeros`. The orthogonal complement of a maximal real negative-definite subspace then carries
a nonnegative form.
-/

noncomputable section

open Matrix Zeta23

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticCastelnuovoSeveri (cx realTests rightZeros)
open ArithmeticIndexDescent (complexWeilMixed complexWeilMixed_eq_weilGram
  hermQuad_complexWeilMixed_ofReal realWeilForm realWeilForm_symm realTestSynthesisMap)
open ArithmeticLorentzianGeometry (atom contDiff_atom hasCompactSupport_atom finAtomicTest)
open HTGeometry (hermNegIndex hermQuad IsPosDefOn finrank_le_posIndex hermQuad_neg
  BilinearNegativeOn bilinearNegativeIndex bilinearNegativeDimensions_bddAbove
  exists_negativeCarrier_finrank_eq_index)
open RenormalizedArithmeticPotentialTheory (atomDilate_facts)
open SpacingScaleHarmonicAnalysis (atomDilate weilQuad)

/-! ### 1. Real negative subspaces of a complexified real matrix -/

/-- A real subspace on which a real matrix is negative definite has dimension at most the
Hermitian negative index of the complexified matrix: its complex span is negative definite because
the Hermitian form of a real matrix splits over real and imaginary parts. -/
theorem finrank_le_hermNegIndex_of_real_negative {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (W : Submodule ℝ (Fin N → ℝ))
    (hW : ∀ y ∈ W, y ≠ 0 → hermQuad (B.map fun r : ℝ => (r : ℂ)) (fun i => (y i : ℂ)) < 0) :
    Module.finrank ℝ W ≤ hermNegIndex (B.map fun r : ℝ => (r : ℂ)) := by
  let b := Module.finBasis ℝ W
  let v : Fin (Module.finrank ℝ W) → (Fin N → ℂ) := fun k i => (((b k : W) : Fin N → ℝ) i : ℂ)
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hre : ∑ k, (g k).re • b k = 0 := by
      ext i
      have hi := congrArg (fun z : Fin N → ℂ => (z i).re) hg
      simpa [v, Finset.sum_apply, Complex.re_sum] using hi
    have him : ∑ k, (g k).im • b k = 0 := by
      ext i
      have hi := congrArg (fun z : Fin N → ℂ => (z i).im) hg
      simpa [v, Finset.sum_apply, Complex.im_sum] using hi
    have h1 := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun k => (g k).re) hre k
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun k => (g k).im) him k
    exact Complex.ext (by simpa using h1) (by simpa using h2)
  have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = Module.finrank ℝ W := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hparts : ∀ z ∈ Submodule.span ℂ (Set.range v),
      (fun i => (z i).re) ∈ W ∧ (fun i => (z i).im) ∈ W := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        have h1 : (fun i => (v k i).re) = ((b k : W) : Fin N → ℝ) := by
          funext i; simp [v]
        have h2 : (fun i => (v k i).im) = 0 := by
          funext i; simp [v]
        rw [h1, h2]
        exact ⟨(b k).2, W.zero_mem⟩
    | zero =>
        have h0 : (fun i => ((0 : Fin N → ℂ) i).re) = 0 := by funext i; simp
        have h0' : (fun i => ((0 : Fin N → ℂ) i).im) = 0 := by funext i; simp
        rw [h0, h0']
        exact ⟨W.zero_mem, W.zero_mem⟩
    | add x y _ _ hx hy =>
        have h1 : (fun i => ((x + y) i).re) = (fun i => (x i).re) + fun i => (y i).re := by
          funext i; simp
        have h2 : (fun i => ((x + y) i).im) = (fun i => (x i).im) + fun i => (y i).im := by
          funext i; simp
        rw [h1, h2]
        exact ⟨W.add_mem hx.1 hy.1, W.add_mem hx.2 hy.2⟩
    | smul a x _ hx =>
        have h1 : (fun i => ((a • x) i).re) =
            a.re • (fun i => (x i).re) - a.im • fun i => (x i).im := by
          funext i; simp [Complex.mul_re]
        have h2 : (fun i => ((a • x) i).im) =
            a.re • (fun i => (x i).im) + a.im • fun i => (x i).re := by
          funext i; simp [Complex.mul_im]
        rw [h1, h2]
        exact ⟨W.sub_mem (W.smul_mem _ hx.1) (W.smul_mem _ hx.2),
          W.add_mem (W.smul_mem _ hx.2) (W.smul_mem _ hx.1)⟩
  have hle : ∀ y ∈ W, hermQuad (B.map fun r : ℝ => (r : ℂ)) (fun i => (y i : ℂ)) ≤ 0 := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · have h0 : (fun i => (((0 : Fin N → ℝ) i : ℝ) : ℂ)) = 0 := by funext i; simp
      rw [h0]
      exact (RHTower.hermQuad_zero' _).le
    · exact (hW y hy hy0).le
  have hneg : IsPosDefOn (-(B.map fun r : ℝ => (r : ℂ))) (Submodule.span ℂ (Set.range v)) := by
    intro z hz hz0
    obtain ⟨hre, him⟩ := hparts z hz
    have hsplit := RHTower.hermQuad_map_ofReal_eq_add B z
    rw [hermQuad_neg, hsplit]
    have hcases : (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      apply hz0
      funext i
      exact Complex.ext (congrFun hboth.1 i) (congrFun hboth.2 i)
    have h1 := hle _ hre
    have h2 := hle _ him
    rcases hcases with h | h
    · have := hW _ hre h
      linarith only [this, h2]
    · have := hW _ him h
      linarith only [this, h1]
  rw [← hdim]
  exact finrank_le_posIndex hneg

/-! ### 2. The complement of a maximal negative subspace -/

/-- A symmetric real bilinear form on a finite-dimensional space is nonnegative on a subspace of
codimension at most its negative index: the orthogonal complement of a maximal negative-definite
subspace. -/
theorem exists_nonneg_subspace_codim_le_bilinearNegativeIndex {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (Q : LinearMap.BilinForm ℝ V) (hQ : Q.IsSymm) :
    ∃ U : Submodule ℝ V, Module.finrank ℝ V ≤ Module.finrank ℝ U + bilinearNegativeIndex Q ∧
      ∀ u ∈ U, 0 ≤ Q u u := by
  obtain ⟨W, hW, hdim⟩ := exists_negativeCarrier_finrank_eq_index Q
  refine ⟨Q.orthogonal W, ?_, ?_⟩
  · have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hQ.isRefl W
    omega
  · intro u hu
    have hortho : ∀ a ∈ W, Q a u = 0 := fun a ha =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp hu a ha
    by_contra hneg
    push Not at hneg
    have huW : u ∉ W := fun huW => by
      have := hortho u huW
      linarith only [this, hneg]
    have hspan : ∀ y ∈ Submodule.span ℝ {u}, y ≠ 0 → Q y y < 0 := by
      intro y hy hy0
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have ht : t ≠ 0 := by rintro rfl; simp at hy0
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      nlinarith only [sq_pos_of_ne_zero ht, hneg]
    have hcross : ∀ a ∈ W, ∀ c ∈ Submodule.span ℝ {u}, Q a c = 0 := by
      intro a ha c hc
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hc
      rw [map_smul, smul_eq_mul, hortho a ha, mul_zero]
    have hnegsup : ∀ y ∈ (W ⊔ Submodule.span ℝ ({u} : Set V) : Submodule ℝ V), y ≠ 0 → Q y y < 0 :=
      RHTower.negDef_sup hQ hW hspan hcross
    have hlt : W < W ⊔ Submodule.span ℝ {u} := by
      refine lt_of_le_of_ne le_sup_left fun h => huW ?_
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
    have hfin := Submodule.finrank_lt_finrank_of_lt hlt
    have hle : Module.finrank ℝ ↥(W ⊔ Submodule.span ℝ {u}) ≤ bilinearNegativeIndex Q :=
      le_csSup (bilinearNegativeDimensions_bddAbove Q) ⟨_, hnegsup, rfl⟩
    omega

/-! ### 3. Bounded codimension under finite off-line support -/

/-- **Finite off-line support pays a bounded codimension.** If `(rightZeros zetaZeroConfig)` is
finite then, for every admissible profile, every overlap `c > 0` and every horizon `N ≥ 1`, the
complete Weil form `weilQuad` of the atomic family is nonnegative on a subspace of `ℝ^N` whose
codimension is at most `#rightZeros`. -/
theorem exists_weilQuad_nonneg_subspace_of_finiteOffLine
    (hfin : (rightZeros zetaZeroConfig).Finite)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    ∃ V : Submodule ℝ (Fin N → ℝ),
      N ≤ Module.finrank ℝ V + (rightZeros zetaZeroConfig).ncard ∧
        ∀ y ∈ V, 0 ≤ weilQuad (finAtomicTest (atomDilate φ (c / N)) N y) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw
  let f : Fin N → realTests := fun i =>
    ⟨atom (atomDilate φ (c / N)) (i.1 + 1), contDiff_atom hg (i.1 + 1),
      hasCompactSupport_atom hgsupp (i.1 + 1)⟩
  have hgram : complexWeilMixed f f = atomicShiftWeilGram φ (c / N) N := by
    rw [complexWeilMixed_eq_weilGram]
    unfold atomicShiftWeilGram
    congr 1
    funext i u
    simp only [f, atom, cx, ArithmeticCastelnuovoSeveri.translate]
    push_cast
    rfl
  let Q : LinearMap.BilinForm ℝ (Fin N → ℝ) :=
    realWeilForm.compl₁₂ (realTestSynthesisMap f) (realTestSynthesisMap f)
  have hQ : Q.IsSymm := ⟨fun x y => realWeilForm_symm _ _⟩
  have hQq : ∀ y, Q y y = hermQuad (complexWeilMixed f f) (fun i => (y i : ℂ)) :=
    fun y => (hermQuad_complexWeilMixed_ofReal f y).symm
  have hQw : ∀ y, Q y y = weilQuad (finAtomicTest (atomDilate φ (c / N)) N y) := fun y => by
    rw [hQq, hgram, hermQuad_atomicShiftWeilGram_eq_weilQuad hφ hsupp hw]
  obtain ⟨W, hW, hdim⟩ := exists_negativeCarrier_finrank_eq_index Q
  have hidx : bilinearNegativeIndex Q ≤ (rightZeros zetaZeroConfig).ncard := by
    rw [← hdim]
    let B : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => realWeilForm (f i) (f j)
    have h1 := finrank_le_hermNegIndex_of_real_negative B W (fun y hy hy0 => by
        have h := hW y hy hy0
        rw [hQq] at h
        exact h)
    have h2 : hermNegIndex (B.map fun r : ℝ => (r : ℂ)) =
        hermNegIndex (atomicShiftWeilGram φ (c / N) N) := by
      rw [← hgram]
      rfl
    rw [h2] at h1
    exact h1.trans (hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine hfin hφ hsupp hc hN)
  obtain ⟨U, hU, hUnn⟩ := exists_nonneg_subspace_codim_le_bilinearNegativeIndex Q hQ
  refine ⟨U, ?_, fun y hy => by rw [← hQw]; exact hUnn y hy⟩
  rw [Module.finrank_fin_fun] at hU
  omega

#print axioms finrank_le_hermNegIndex_of_real_negative
#print axioms exists_nonneg_subspace_codim_le_bilinearNegativeIndex
#print axioms exists_weilQuad_nonneg_subspace_of_finiteOffLine

end GaloisForLFunctions.TransMetzlerWeilPositivity
