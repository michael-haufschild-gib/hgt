import GaloisForLFunctions.RepresentationLifting.Lattices.PrimitivePadicBilinearReduction
import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature
import Mathlib.Tactic.FunProp

/-!
# Finite congruence obstructions for p-adic projective equations

A bilinear system has a nonzero p-adic solution in both projective blocks
exactly when every finite subsystem has normalized solutions modulo every
prime power. Compactness of normalized integral coordinates supplies a
simultaneous limit; no compatibility of the finite solutions is assumed.
This completes the prime-power obstruction mechanism behind the projective
normalization in Yang, arXiv:2611.21188, Lemma 1.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.PrimitiveReduction
open GaloisForLFunctions.RHTower
variable (p : ℕ) [Fact p.Prime]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ]

private theorem pairing_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (A : ι → κ → R) (u : ι → R) (v : κ → R) :
    φ (pairing A u v) = pairing (fun i j => φ (A i j)) (fun i => φ (u i)) (fun j => φ (v j)) := by
  simp only [pairing, map_sum, map_mul]

/-- A finite prime-power solution with a coordinate equal to one in each block. -/
def FiniteCongruenceSolution (A : τ → ι → κ → ℤ_[p]) (S : Finset τ) (n : ℕ) : Prop :=
  ∃ u : ι → ZMod (p ^ n), ∃ v : κ → ZMod (p ^ n),
    (∃ i, u i = 1) ∧ (∃ j, v j = 1) ∧
      ∀ t ∈ S, pairing (fun i j => PadicInt.toZModPow n (A t i j)) u v = 0

private theorem normalized_residue_lift {δ : Type*} (n : ℕ)
    (u : δ → ZMod (p ^ n)) (hu : ∃ i, u i = 1) :
    ∃ v : δ → ℤ_[p], (∃ i, v i = 1) ∧ ∀ i, PadicInt.toZModPow n (v i) = u i := by
  classical
  obtain ⟨j, hj⟩ := hu
  refine ⟨fun i => if i = j then 1 else fieldOnePadicIntResidueRep p n (u i),
    ⟨j, if_pos rfl⟩, ?_⟩
  intro i
  dsimp only
  by_cases h : i = j
  · subst i
    rw [if_pos rfl, map_one, hj]
  · rw [if_neg h, fieldOnePadicIntResidueRep_spec]

private def normalizedLattice : Set ((ι → ℤ_[p]) × (κ → ℤ_[p])) :=
  {z | (∃ i, z.1 i = 1) ∧ ∃ j, z.2 j = 1}

private theorem normalizedLattice_compact :
    IsCompact (normalizedLattice p (ι := ι) (κ := κ)) := by
  apply IsClosed.isCompact
  have h₁ : IsClosed {z : (ι → ℤ_[p]) × (κ → ℤ_[p]) | ∃ i, z.1 i = 1} := by
    simp only [Set.setOf_exists]
    exact isClosed_iUnion_of_finite (fun i => isClosed_eq ((continuous_apply i).comp continuous_fst) continuous_const)
  have h₂ : IsClosed {z : (ι → ℤ_[p]) × (κ → ℤ_[p]) | ∃ j, z.2 j = 1} := by
    simp only [Set.setOf_exists]
    exact isClosed_iUnion_of_finite (fun j => isClosed_eq ((continuous_apply j).comp continuous_snd) continuous_const)
  exact h₁.inter h₂

private def congruenceLocus (A : τ → ι → κ → ℤ_[p]) (k : ℕ × τ) :
    Set ((ι → ℤ_[p]) × (κ → ℤ_[p])) :=
  {z | PadicInt.toZModPow k.1 (pairing (A k.2) z.1 z.2) = 0}

private theorem congruenceLocus_closed (A : τ → ι → κ → ℤ_[p]) (k : ℕ × τ) :
    IsClosed (congruenceLocus p A k) := by
  apply isClosed_eq _ continuous_const
  apply (fieldOnePadicInt_toZModPow_continuous p k.1).comp
  unfold pairing
  fun_prop

private theorem lower_congruence {x : ℤ_[p]} {n m : ℕ} (hnm : n ≤ m)
    (hm : PadicInt.toZModPow m x = 0) : PadicInt.toZModPow n x = 0 := by
  have h := congrArg (fun φ : ℤ_[p] →+* ZMod (p ^ n) => φ x)
    (PadicInt.zmod_cast_comp_toZModPow n m hnm)
  simpa only [RingHom.comp_apply, hm, map_zero] using h.symm

/-- Compactness upgrades arbitrary finite congruence witnesses to one normalized integral solution. -/
theorem integral_solution_iff_finite_congruences (A : τ → ι → κ → ℤ_[p]) :
    (∃ u : ι → ℤ_[p], ∃ v : κ → ℤ_[p],
      (∃ i, u i = 1) ∧ (∃ j, v j = 1) ∧ ∀ t, pairing (A t) u v = 0) ↔
      ∀ S : Finset τ, ∀ n : ℕ, FiniteCongruenceSolution p A S n := by
  classical
  constructor
  · rintro ⟨u, v, ⟨i, hi⟩, ⟨j, hj⟩, h⟩ S n
    refine ⟨fun i => PadicInt.toZModPow n (u i), fun j => PadicInt.toZModPow n (v j),
      ⟨i, by dsimp only; rw [hi, map_one]⟩, ⟨j, by dsimp only; rw [hj, map_one]⟩, ?_⟩
    intro t _
    rw [← pairing_map, h, map_zero]
  · intro h
    have hfinite (U : Finset (ℕ × τ)) :
        (normalizedLattice p ∩ ⋂ k ∈ U, congruenceLocus p A k).Nonempty := by
      let m := ∑ k ∈ U, k.1
      obtain ⟨u, v, hu, hv, huv⟩ := h (U.image Prod.snd) m
      obtain ⟨u', hu', he⟩ := normalized_residue_lift p m u hu
      obtain ⟨v', hv', hf⟩ := normalized_residue_lift p m v hv
      refine ⟨(u', v'), ⟨hu', hv'⟩, ?_⟩
      simp only [Set.mem_iInter]
      intro k hk
      change PadicInt.toZModPow k.1 (pairing (A k.2) u' v') = 0
      apply lower_congruence p (show k.1 ≤ m from
        Finset.single_le_sum (fun k _ => Nat.zero_le k.1) hk)
      rw [pairing_map]
      simp only [he, hf]
      exact huv k.2 (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    obtain ⟨z, hz, hc⟩ := (normalizedLattice_compact p).inter_iInter_nonempty
      (congruenceLocus p A) (congruenceLocus_closed p A) hfinite
    refine ⟨z.1, z.2, hz.1, hz.2, ?_⟩
    intro t
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [map_zero]
    exact Set.mem_iInter.mp hc (n, t)

/-- Primitive normalization turns the compact congruence criterion into an exact projective criterion. -/
theorem projective_solution_iff_finite_congruences (A : τ → ι → κ → ℤ_[p]) :
    (∃ x : ι → ℚ_[p], ∃ y : κ → ℚ_[p],
      x ≠ 0 ∧ y ≠ 0 ∧ ∀ t, pairing (fun i j => (A t i j : ℚ_[p])) x y = 0) ↔
      ∀ S : Finset τ, ∀ n : ℕ, FiniteCongruenceSolution p A S n := by
  rw [← integral_solution_iff_finite_congruences]
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    obtain ⟨c, _, u, hu, i, hi⟩ := exists_primitive_model p x hx
    obtain ⟨d, _, v, hv, j, hj⟩ := exists_primitive_model p y hy
    refine ⟨u, v, ⟨i, hi⟩, ⟨j, hj⟩, ?_⟩
    intro t
    apply PadicInt.ext
    change ((pairing (A t) u v : ℤ_[p]) : ℚ_[p]) = 0
    simp only [pairing, PadicInt.coe_sum, PadicInt.coe_mul, hu, hv]
    change pairing (fun i j => (A t i j : ℚ_[p])) (fun i => c * x i) (fun j => d * y j) = 0
    rw [pairing_scale, hxy, mul_zero]
  · rintro ⟨u, v, ⟨i, hi⟩, ⟨j, hj⟩, h⟩
    refine ⟨fun i => (u i : ℚ_[p]), fun j => (v j : ℚ_[p]), ?_, ?_, ?_⟩
    · intro hz
      have he := congrFun hz i
      rw [hi] at he
      exact one_ne_zero he
    · intro hz
      have he := congrFun hz j
      rw [hj] at he
      exact one_ne_zero he
    · intro t
      have he := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (h t)
      simpa only [pairing, PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_zero] using he

/-- Every failure of p-adic projective solvability has a finite congruence certificate. -/
theorem no_projective_solution_iff_finite_obstruction (A : τ → ι → κ → ℤ_[p]) :
    (¬ ∃ x : ι → ℚ_[p], ∃ y : κ → ℚ_[p],
      x ≠ 0 ∧ y ≠ 0 ∧ ∀ t, pairing (fun i j => (A t i j : ℚ_[p])) x y = 0) ↔
      ∃ S : Finset τ, ∃ n : ℕ, ¬ FiniteCongruenceSolution p A S n := by
  rw [projective_solution_iff_finite_congruences]
  push Not
  rfl

#print axioms integral_solution_iff_finite_congruences
#print axioms projective_solution_iff_finite_congruences
#print axioms no_projective_solution_iff_finite_obstruction
end GaloisForLFunctions.RepresentationLifting.PrimitiveReduction
