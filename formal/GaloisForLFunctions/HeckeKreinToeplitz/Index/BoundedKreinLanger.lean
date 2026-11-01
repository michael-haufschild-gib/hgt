import GaloisForLFunctions.HeckeKreinToeplitz.Index.SignedTorusCorrections
import GaloisForLFunctions.HTGeometry.FiniteNegativeSupport
import GaloisForLFunctions.HTGeometry.FiniteNegativeAtomCount

/-!
# Bounded converse Krein–Langer theorem on free lattices

Every bounded finite-index Hermitian kernel on a countable free abelian group
is positive definite minus a positive combination of distinct unitary characters.
The smallest number of such characters is the negative index. Boundedness is necessary
and sufficient for an index-sized unitary decomposition on the finite stratum.
-/

open Complex Finset MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

/-- Subtracting a finite family of unitary characters costs at most one
negative square per character. -/
theorem negIndex_sub_unitary_characters_le {G J : Type*} [Group G] [Fintype J]
    {p : G → ℂ} (hp : IsPosDefKernel p) (χ : J → G →* ℂ)
    (hχ : ∀ j, IsUnitaryChar (χ j)) (a : J → ℝ) :
    negIndex (fun g => p g - ∑ j, (a j : ℂ) * χ j g) ≤ Fintype.card J := by
  have hpair (j : J) (g : G) : pairKernel (χ j) ((-a j / 2 : ℝ) : ℂ) g =
      -((a j : ℂ) * χ j g) := by
    rw [pairKernel, reflectChar_eq_of_unitary (hχ j), Complex.conj_ofReal]
    push_cast
    ring
  simpa only [hpair, sum_neg_distrib, sub_eq_add_neg] using
    negIndex_add_sum_pairKernel_le hp χ (fun j => ((-a j / 2 : ℝ) : ℂ))

/-- The negative spectral part of a bounded finite-index kernel consists of
at most its index many positive atoms. -/
theorem exists_torus_spectral_atoms_of_bounded_finite_index
    {I : Type*} [Countable I] {k : Multiplicative (I →₀ ℤ) → ℂ}
    (hk : IsHermKernel k) {m : ℕ} (hm : negIndex k = m)
    (hbounded : ∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) :
    ∃ (P : FiniteMeasure (UnitAddTorus I)) (s : Finset (UnitAddTorus I)) (a : s → ℝ),
      s.card ≤ m ∧ (∀ j, 0 < a j) ∧
      ∀ g, k g = torusFourierKernel (P : Measure (UnitAddTorus I)) g -
        ∑ j : s, (a j : ℂ) * torusLatticeCharacter (j : UnitAddTorus I) g := by
  classical
  obtain ⟨P, N, hmut, hrepr, q, hrepair⟩ :=
    exists_signed_torus_measure_with_repaired_L2 hk hm hbounded
  have hq (i : Fin m) (θ : UnitAddTorus I) : ‖q i θ‖ ≤ ∑ j, ‖q j‖ :=
    ((q i).norm_coe_le_norm θ).trans
      (single_le_sum (fun j _ => norm_nonneg (q j)) (mem_univ i))
  have hfin := finite_negative_support_of_bounded_corrections
    (P : Measure (UnitAddTorus I)) (N : Measure (UnitAddTorus I)) hmut
    (fun i θ => q i θ) hq hrepair
  obtain ⟨s, hw, hN⟩ := exists_positive_dirac_sum_of_finite_support
    (N : Measure (UnitAddTorus I)) hfin
  have hcard_le : s.card ≤ m := finite_negative_atom_count_le
    (P : Measure (UnitAddTorus I)) (N : Measure (UnitAddTorus I)) hmut s hw hN
    (fun i θ => q i θ) hrepair
  let a : s → ℝ := fun j => (N : Measure (UnitAddTorus I)).real {(j : UnitAddTorus I)}
  refine ⟨P, s, a, hcard_le, fun j => hw j j.2, fun g => ?_⟩
  rw [hrepr]
  congr 1
  change (∫ θ, torusCharacter g.toAdd θ ∂(N : Measure (UnitAddTorus I))) = _
  conv_lhs => rw [hN]
  rw [integral_finsetWeightedDirac_general s _ (fun θ hθ => (hw θ hθ).le)
    (fun θ : UnitAddTorus I => θ) (fun θ => torusCharacter g.toAdd θ), ← sum_coe_sort]
  apply sum_congr rfl fun j _ => ?_
  change a j • torusCharacter g.toAdd (j : UnitAddTorus I) =
    (a j : ℂ) * torusCharacter g.toAdd (j : UnitAddTorus I)
  exact Complex.real_smul

/-- A bounded finite-index kernel on a countable free lattice is positive
definite minus exactly its index many distinct unitary characters, each with
positive weight. -/
theorem bounded_free_lattice_krein_langer
    {I : Type*} [Countable I] {k : Multiplicative (I →₀ ℤ) → ℂ}
    (hk : IsHermKernel k) {m : ℕ} (hm : negIndex k = m)
    (hbounded : ∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) :
    ∃ (p : Multiplicative (I →₀ ℤ) → ℂ)
      (χ : Fin m → Multiplicative (I →₀ ℤ) →* ℂ) (a : Fin m → ℝ),
      IsPosDefKernel p ∧ Function.Injective χ ∧ (∀ j, IsUnitaryChar (χ j)) ∧
      (∀ j, 0 < a j) ∧ ∀ g, k g = p g - ∑ j, (a j : ℂ) * χ j g := by
  classical
  obtain ⟨P, s, a, hcard_le, ha, hdecomp⟩ :=
    exists_torus_spectral_atoms_of_bounded_finite_index hk hm hbounded
  let p : Multiplicative (I →₀ ℤ) → ℂ := torusFourierKernel (P : Measure (UnitAddTorus I))
  let χ : s → Multiplicative (I →₀ ℤ) →* ℂ :=
    fun j => torusLatticeCharacter (I := I) (j : UnitAddTorus I)
  have hp : IsPosDefKernel p := isPosDefKernel_torusFourierKernel (P : Measure (UnitAddTorus I))
  have hχ : ∀ j : s, IsUnitaryChar (χ j) :=
    fun j => torusLatticeCharacter_unitary (I := I) (j : UnitAddTorus I)
  have hcard_ge : m ≤ s.card := by
    have hi : negIndex (fun g => p g - ∑ j : s, (a j : ℂ) * χ j g) ≤ Fintype.card s :=
      negIndex_sub_unitary_characters_le hp χ hχ a
    have he : (fun g => p g - ∑ j : s, (a j : ℂ) * χ j g) = k :=
      (funext hdecomp).symm
    rw [he, hm, Fintype.card_coe] at hi
    exact_mod_cast hi
  have hcard : Fintype.card s = m := by
    simpa only [Fintype.card_coe] using le_antisymm hcard_le hcard_ge
  let e : Fin m ≃ s := (finCongr hcard.symm).trans (Fintype.equivFin s).symm
  refine ⟨p, χ ∘ e, a ∘ e, hp, ?_, fun j => hχ (e j), fun j => ha (e j), fun g => ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact torusLatticeCharacter_injective (I := I) hij
  · rw [hdecomp]
    exact congrArg (fun z : ℂ => p g - z)
      (e.sum_comp (fun j : s => (a j : ℂ) * χ j g)).symm

/-- For a bounded Hermitian free-lattice kernel, finite negative index is
equivalent to a finite positive unitary-character subtraction. -/
theorem bounded_free_lattice_finite_index_iff
    {I : Type*} [Countable I] {k : Multiplicative (I →₀ ℤ) → ℂ}
    (hk : IsHermKernel k) (hbounded : ∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) :
    negIndex k ≠ ⊤ ↔ ∃ (n : ℕ) (p : Multiplicative (I →₀ ℤ) → ℂ)
      (χ : Fin n → Multiplicative (I →₀ ℤ) →* ℂ) (a : Fin n → ℝ),
      IsPosDefKernel p ∧ Function.Injective χ ∧ (∀ j, IsUnitaryChar (χ j)) ∧
      (∀ j, 0 < a j) ∧ ∀ g, k g = p g - ∑ j, (a j : ℂ) * χ j g := by
  constructor
  · intro hfin
    have hm : ∃ m : ℕ, negIndex k = m := by
      cases he : negIndex k using ENat.recTopCoe with
      | top => exact False.elim (hfin he)
      | coe m => exact ⟨m, rfl⟩
    obtain ⟨m, hm⟩ := hm
    obtain ⟨p, χ, a, hp, hχinj, hχ, ha, hrep⟩ := bounded_free_lattice_krein_langer hk hm hbounded
    exact ⟨m, p, χ, a, hp, hχinj, hχ, ha, hrep⟩
  · rintro ⟨n, p, χ, a, hp, _, hχ, _, hrep⟩
    have hle := negIndex_sub_unitary_characters_le hp χ hχ a
    rw [← show k = fun g => p g - ∑ j, (a j : ℂ) * χ j g from funext hrep] at hle
    exact ne_top_of_le_ne_top (by simp) hle

/-- Every unitary-character decomposition has at least as many terms as
the negative index; the bounded free-lattice theorem attains this minimum. -/
theorem negative_index_le_unitary_decomposition_size
    {G : Type*} [Group G] {k p : G → ℂ} {m n : ℕ}
    (hm : negIndex k = m) (hp : IsPosDefKernel p)
    (χ : Fin n → G →* ℂ) (hχ : ∀ j, IsUnitaryChar (χ j)) (a : Fin n → ℝ)
    (hrep : ∀ g, k g = p g - ∑ j, (a j : ℂ) * χ j g) : m ≤ n := by
  have hle := negIndex_sub_unitary_characters_le hp χ hχ a
  rw [← show k = fun g => p g - ∑ j, (a j : ℂ) * χ j g from funext hrep, hm] at hle
  rw [Fintype.card_fin] at hle
  exact_mod_cast hle

/-- Within finite-index free-lattice kernels, boundedness is exactly the
existence of an index-sized unitary decomposition. -/
theorem finite_index_bounded_iff_unitary_decomposition
    {I : Type*} [Countable I] {k : Multiplicative (I →₀ ℤ) → ℂ}
    (hk : IsHermKernel k) {m : ℕ} (hm : negIndex k = m) :
    (∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) ↔
      ∃ (p : Multiplicative (I →₀ ℤ) → ℂ)
        (χ : Fin m → Multiplicative (I →₀ ℤ) →* ℂ) (a : Fin m → ℝ),
        IsPosDefKernel p ∧ Function.Injective χ ∧ (∀ j, IsUnitaryChar (χ j)) ∧
        (∀ j, 0 < a j) ∧ ∀ g, k g = p g - ∑ j, (a j : ℂ) * χ j g := by
  refine ⟨bounded_free_lattice_krein_langer hk hm, ?_⟩
  rintro ⟨p, χ, a, hp, _, hχ, _, hrep⟩
  refine ⟨(p 1).re + ∑ j, ‖(a j : ℂ)‖, fun g => ?_⟩
  rw [hrep]
  apply (norm_sub_le _ _).trans
  apply add_le_add (hp.norm_le g)
  calc
    ‖∑ j, (a j : ℂ) * χ j g‖ ≤ ∑ j, ‖(a j : ℂ) * χ j g‖ := norm_sum_le _ _
    _ = ∑ j, ‖(a j : ℂ)‖ := by
      apply sum_congr rfl fun j _ => ?_
      rw [norm_mul, hχ j g, mul_one]

end

#print axioms exists_torus_spectral_atoms_of_bounded_finite_index
#print axioms bounded_free_lattice_krein_langer
#print axioms bounded_free_lattice_finite_index_iff
#print axioms negative_index_le_unitary_decomposition_size
#print axioms finite_index_bounded_iff_unitary_decomposition

end GaloisForLFunctions.HeckeKreinToeplitz
