import GaloisForLFunctions.HeckeKreinToeplitz.Index.MaximalInvariantNonpositiveSubspace
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FinitePairingFunctionSpaces
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletedFrameRepresentation
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Translation-stable positive constraints characterize finite negative index

A common invariant nonpositive space in the completed column representation
has nonnegative orthogonal complement. Pairing against this finite space
supplies translation-stable constraints, simultaneously for all finite Gram
restrictions. Dimension counting proves the converse.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Module
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {k : G → ℂ}

/-- Finite negative index supplies a finite translation-invariant function
space whose annihilator is positive for every finite Gram form. -/
theorem exists_translation_stable_positive_constraints {r : ℕ}
    (hk : IsHermKernel k) (hi : negIndex k ≤ r) :
    ∃ Φ : Submodule ℂ (G → ℂ), FiniteDimensional ℂ Φ ∧ finrank ℂ Φ ≤ r ∧
      (∀ h : G, ∀ f ∈ Φ, (fun g => f (h * g)) ∈ Φ) ∧
      ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
        (∀ f ∈ Φ, ∑ i, c i * f (x i) = 0) → 0 ≤ hermQuad (gram k x) c := by
  classical
  obtain ⟨m, hm, e, he, hp⟩ := exists_maximal_negative_column_frame hk hi
  let H := NegativeFrame.Hilbert hk e he hp
  let T : G → (H × EuclideanSpace ℂ (Fin m)) ≃L[ℂ]
      (H × EuclideanSpace ℂ (Fin m)) := NegativeFrame.action hk e he hp
  let E : kernelColumnSpan k →ₗ[ℂ] (H × EuclideanSpace ℂ (Fin m)) :=
    NegativeFrame.embedding hk e he hp
  let z : G → H × EuclideanSpace ℂ (Fin m) := fun g => E (kernelColumnPoint k g)
  have hT : ∀ g v w, FiniteNegative.pairing (T g v) (T g w) = FiniteNegative.pairing v w :=
    NegativeFrame.action_pairing hk e he hp
  have hmul (a b : G) (v : H × EuclideanSpace ℂ (Fin m)) : T (a * b) v = T a (T b v) :=
    NegativeFrame.action_mul hk e he hp a b v
  have hcomm (a b : G) (v : H × EuclideanSpace ℂ (Fin m)) : T a (T b v) = T b (T a v) := by
    rw [← hmul, ← hmul, mul_comm a b]
  obtain ⟨U, hiU, hnU, hdU, hpU⟩ :=
    FiniteNegative.exists_invariant_nonpositive_with_nonnegative_complement T hT hcomm
  letI := FiniteNegative.finiteDimensional_of_nonpositive U hnU
  obtain ⟨Φ, hfin, hdΦ, hΦ⟩ := FiniteNegative.exists_finite_pairing_function_space U z
  have hdim : finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by simp
  rw [hdim] at hdU
  refine ⟨Φ, hfin, hdΦ.trans (hdU.trans hm), ?_, ?_⟩
  · intro h f hf
    obtain ⟨u, rfl⟩ := (hΦ f).mp hf
    apply (hΦ _).mpr
    refine ⟨⟨(T h).symm u, (hiU h u u.property).2⟩, ?_⟩
    funext g
    have hz : z (h * g) = T h (z g) := by
      exact (NegativeFrame.action_point hk e he hp h g).symm
    rw [hz]
    have hh := hT h ((T h).symm u) (z g)
    rw [(T h).apply_symm_apply] at hh
    exact hh
  · intro n x c hc
    let v : kernelColumnSpan k := ∑ i, c i • kernelColumnPoint k (x i)
    have ho : E v ∈ FiniteNegative.signedOrthogonal U := by
      apply (FiniteNegative.mem_signedOrthogonal U _).mpr
      intro u hu
      have hfu : (fun g => FiniteNegative.pairing u (z g)) ∈ Φ :=
        (hΦ _).mpr ⟨⟨u, hu⟩, rfl⟩
      have hmass := hc _ hfu
      change FiniteNegative.pairingLinear u (E v) = 0
      simpa only [v, map_sum, map_smul, smul_eq_mul] using hmass
    have h := hpU (E v) ho
    change 0 ≤ (FiniteNegative.pairing (NegativeFrame.embedding hk e he hp v)
      (NegativeFrame.embedding hk e he hp v)).re at h
    rw [NegativeFrame.embedding_pairing, kernelColumnPoint_sum_self_re hk] at h
    exact h

/-- Positivity on the annihilator of a finite function space bounds negative index. -/
theorem negIndex_le_of_finite_positive_constraints {r : ℕ}
    (Φ : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ Φ] (hd : finrank ℂ Φ ≤ r)
    (hpos : ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      (∀ f ∈ Φ, ∑ i, c i * f (x i) = 0) → 0 ≤ hermQuad (gram k x) c) :
    negIndex k ≤ r := by
  classical
  let b := Module.finBasis ℂ Φ
  apply negIndex_le_iff.mpr
  intro n x
  let L : (G → ℂ) →ₗ[ℂ] ((Fin n → ℂ) →ₗ[ℂ] ℂ) :=
    { toFun f := Fintype.linearCombination ℂ (fun i => f (x i))
      map_add' f g := by
        ext c
        simp only [Fintype.linearCombination_apply, Pi.add_apply, mul_add,
          smul_eq_mul, Finset.sum_add_distrib, LinearMap.add_apply]
      map_smul' a f := by
        ext c
        simp only [Fintype.linearCombination_apply, Pi.smul_apply, smul_eq_mul,
          LinearMap.smul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
    (gram k x) (fun i => L (b i)) (fun c hc => hpos n x c (by
      intro f hf
      let f₀ : Φ := ⟨f, hf⟩
      have hz : L f c = 0 := by
        have heq : f = ∑ i, b.repr f₀ i • (b i : G → ℂ) := by
          have he := congrArg Φ.subtype (b.sum_repr f₀)
          simpa only [map_sum, map_smul] using he.symm
        rw [heq, map_sum]
        simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hc,
          smul_zero, Finset.sum_const_zero]
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk,
        Fintype.linearCombination_apply, smul_eq_mul] using hz))
  have hb : Fintype.card (Fin (finrank ℂ Φ)) = finrank ℂ Φ := Fintype.card_fin _
  rw [hb] at h
  exact_mod_cast h.trans hd

/-- Finite negative index is equivalent to positivity after imposing finitely
many constraints whose span is translation invariant. -/
theorem negIndex_le_iff_translation_stable_positive_constraints (hk : IsHermKernel k) (r : ℕ) :
    negIndex k ≤ r ↔
      ∃ Φ : Submodule ℂ (G → ℂ), FiniteDimensional ℂ Φ ∧ finrank ℂ Φ ≤ r ∧
        (∀ h : G, ∀ f ∈ Φ, (fun g => f (h * g)) ∈ Φ) ∧
        ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
          (∀ f ∈ Φ, ∑ i, c i * f (x i) = 0) → 0 ≤ hermQuad (gram k x) c := by
  constructor
  · exact exists_translation_stable_positive_constraints hk
  · rintro ⟨Φ, hfin, hd, _, hp⟩
    letI := hfin
    exact negIndex_le_of_finite_positive_constraints Φ hd hp

#print axioms exists_translation_stable_positive_constraints
#print axioms negIndex_le_iff_translation_stable_positive_constraints

end GaloisForLFunctions.HeckeKreinToeplitz
