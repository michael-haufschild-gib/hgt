import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTensorHomotopy
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.TensorProduct.Finite

/-! Over a field, the total cohomology dimension is the convolution of the
cohomology dimensions of the two factors. -/

noncomputable section

open CategoryTheory TensorProduct Finset.Nat Finset.HasAntidiagonal

namespace GlobalTheory.CechDR.FiniteGradedComplex

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

private theorem orthogonal_ranges (G : FiniteGradedComplex K V) (e : Module.End K V)
    (hee : ∀ x, e (e x) = e x) (hπ : ∀ p x, e (G.π p x) = G.π p (e x)) (p q : ℕ) :
    (e ∘ₗ G.π p) * (e ∘ₗ G.π q) = if p = q then e ∘ₗ G.π p else 0 := by
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    apply LinearMap.ext
    intro x
    change e (G.π p (e (G.π p x))) = e (G.π p x)
    rw [← hπ p (G.π p x), hee, G.idem]
  · rw [if_neg hpq]
    apply LinearMap.ext
    intro x
    change e (G.π p (e (G.π q x))) = 0
    rw [← hπ p (G.π q x), hee, G.orth _ _ _ hpq, map_zero]

private theorem subsingleton_range_zero (G : FiniteGradedComplex K V) (e : Module.End K V) :
    Subsingleton (LinearMap.range (e ∘ₗ G.π 0)) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  obtain ⟨_, x, rfl⟩ := x
  obtain ⟨_, y, rfl⟩ := y
  exact congrArg e ((G.zero x).trans (G.zero y).symm)

/-- The degree-zero terms vanish in the shifted grading, so total degree
`n + 2` corresponds to the usual antidiagonal in cohomological degree `n`. -/
theorem finrank_homology_tensor (G : FiniteGradedComplex K V) (H : FiniteGradedComplex K W)
    (hG : ∀ p, Module.Finite K (G.degreeShort p).homology)
    (hH : ∀ q, Module.Finite K (H.degreeShort q).homology) (n : ℕ) :
    Module.Finite K ((G.tensorComplex H).degreeShort (n + 1)).homology ∧
      Module.finrank K ((G.tensorComplex H).degreeShort (n + 1)).homology =
        ∑ x ∈ antidiagonal n, Module.finrank K (G.degreeShort x.1).homology *
          Module.finrank K (H.degreeShort x.2).homology := by
  obtain ⟨e, h, hde, hed, hee, hc, hh, hπ⟩ := G.exists_idempotent_contraction
  obtain ⟨e', h', hde', hed', hee', hc', hh', hπ'⟩ := H.exists_idempotent_contraction
  let T := G.tensorComplex H
  let E := TensorProduct.map e e'
  let J := G.tensorChainHomotopy e h h'
  obtain ⟨hDE, hED, hJ⟩ :=
    G.tensor_contraction H e h e' h' hde hed hc hh hπ hde' hed' hc'
  have hEE (z : V ⊗[K] W) : E (E z) = E z := by
    have hE : E ∘ₗ E = E := by
      refine TensorProduct.ext' fun a b => ?_
      simp only [E, LinearMap.comp_apply, TensorProduct.map_tmul, hee, hee']
    exact LinearMap.congr_fun hE z
  have hEπ (p : ℕ) (z : V ⊗[K] W) : E (T.π p z) = T.π p (E z) :=
    LinearMap.congr_fun (G.tensorProjection_map H e e' hπ hπ' p) z
  obtain ⟨R⟩ := T.nonempty_homology_equiv_termRange E J hDE hED hEE hJ
    (G.tensorChainHomotopy_degree H e h h' hh hh' hπ) hEπ (n + 1)
  let f (p : ℕ) := e ∘ₗ G.π p
  let g (q : ℕ) := e' ∘ₗ H.π q
  let S := antidiagonal (n + 2)
  obtain ⟨I, Q, hIQ, hQI⟩ := exists_retraction_tensor_ranges
    (f := f) (g := g) (orthogonal_ranges G e hee hπ) (orthogonal_ranges H e' hee' hπ') S
  have hP (z : V ⊗[K] W) : E (T.π (n + 2) z) = I (Q z) := by
    rw [hIQ]
    change E (G.tensorProjection H (n + 2) z) = _
    simp only [E, f, g, S, tensorProjection, LinearMap.sum_apply, map_sum, TensorProduct.map_map]
  have hRange : LinearMap.range I = LinearMap.range (E ∘ₗ T.π (n + 2)) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨I w, (hP (I w)).trans (congrArg I (hQI w))⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Q w, (hP w).symm⟩
  let B := R.trans ((LinearEquiv.ofEq _ _ hRange).symm.trans
    (LinearEquiv.ofLeftInverse hQI).symm)
  have A₁ (p : ℕ) := G.nonempty_homology_equiv_termRange e h hde hed hee hc hh hπ p
  have A₂ (p : ℕ) := H.nonempty_homology_equiv_termRange e' h' hde' hed' hee' hc' hh' hπ' p
  letI : Subsingleton (LinearMap.range (f 0)) := subsingleton_range_zero G e
  letI : Subsingleton (LinearMap.range (g 0)) := subsingleton_range_zero H e'
  letI (p : ℕ) : Module.Finite K (LinearMap.range (f p)) := by
    cases p with
    | zero => infer_instance
    | succ p =>
      letI := hG p
      exact Module.Finite.equiv (A₁ p).some
  letI (p : ℕ) : Module.Finite K (LinearMap.range (g p)) := by
    cases p with
    | zero => infer_instance
    | succ p =>
      letI := hH p
      exact Module.Finite.equiv (A₂ p).some
  refine ⟨Module.Finite.equiv B.symm, ?_⟩
  calc
    _ = ∑ x ∈ S, Module.finrank K (LinearMap.range (f x.1)) *
        Module.finrank K (LinearMap.range (g x.2)) := by
      rw [B.finrank_eq, Module.finrank_pi_fintype, ← Finset.sum_coe_sort S]
      exact Finset.sum_congr rfl fun x _ => Module.finrank_tensorProduct
    _ = _ := by
      rw [show S = antidiagonal (n + 2) from rfl, antidiagonal_succ_succ',
        Finset.sum_cons, Finset.sum_cons, Finset.sum_map,
        Module.finrank_zero_of_subsingleton (M := LinearMap.range (f 0)),
        Module.finrank_zero_of_subsingleton (M := LinearMap.range (g 0)), zero_mul,
        mul_zero, zero_add, zero_add]
      exact Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·)
        (A₁ x.1).some.finrank_eq.symm (A₂ x.2).some.finrank_eq.symm

end GlobalTheory.CechDR.FiniteGradedComplex
