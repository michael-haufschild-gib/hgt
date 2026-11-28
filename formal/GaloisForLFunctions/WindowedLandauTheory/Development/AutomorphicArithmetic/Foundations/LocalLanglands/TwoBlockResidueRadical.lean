import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.OppositeRadicalAveraging
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSplitCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction

/-! The upper-right two-block radical is the group attached to a
coordinate projection and its complement. Vanishing of its fixed
space forces the Harish–Chandra restriction to have degree zero. -/

noncomputable section

open Matrix Representation GlobalTheory.OppRad
open scoped Classical

namespace GlobalTheory.GLq

/-- Projection onto the specified coordinate summands. -/
def coordinateProjection (R : Type*) [Ring R] {n : ℕ} (s : Fin n → Prop) [DecidablePred s] :
    Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if s i then 1 else 0

theorem one_sub_coordinateProjection {R : Type*} [Ring R] {n : ℕ}
    (s : Fin n → Prop) [DecidablePred s] :
    1 - coordinateProjection R s = coordinateProjection R (fun i => ¬ s i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : s i <;> simp [coordinateProjection, Matrix.sub_apply, hi]
  · simp [coordinateProjection, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply, hij]

/-- Projection onto the first `a` coordinates. -/
def blockProjection (R : Type*) [Ring R] (a n : ℕ) : Matrix (Fin n) (Fin n) R :=
  coordinateProjection R fun i => i.val < a

theorem blockProjection_idempotent (R : Type*) [Ring R] (a n : ℕ) :
    blockProjection R a n * blockProjection R a n = blockProjection R a n := by
  rw [blockProjection, coordinateProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem mapMatrix_blockProjection {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a n : ℕ) :
    f.mapMatrix (blockProjection R a n) = blockProjection S a n := by
  ext i j
  simp [blockProjection, coordinateProjection, Matrix.diagonal_apply, apply_ite f]

theorem mem_coordinateRadical_iff {R : Type} [Ring R] {n : ℕ}
    (s : Fin n → Prop) [DecidablePred s] (u : GL (Fin n) R) :
    u ∈ U (coordinateProjection R s) (1 - coordinateProjection R s) ↔
      ∀ i j : Fin n, ¬ (s i ∧ ¬ s j) → u.val i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [mem_U, one_sub_coordinateProjection]
  constructor
  · rintro ⟨hl, hr⟩ i j hij
    by_cases hi : s i
    · have hj : ¬ ¬ s j := fun hh => hij ⟨hi, hh⟩
      have he := congrFun (congrFun hr i) j
      rw [coordinateProjection, Matrix.mul_diagonal, if_neg hj, mul_zero, Matrix.sub_apply, eq_comm, sub_eq_zero] at he
      exact he
    · have he := congrFun (congrFun hl i) j
      rw [coordinateProjection, Matrix.diagonal_mul, if_neg hi, zero_mul, Matrix.sub_apply, eq_comm, sub_eq_zero] at he
      exact he
  · intro h
    constructor
    · ext i j
      rw [coordinateProjection, Matrix.diagonal_mul]
      by_cases hi : s i
      · rw [if_pos hi, one_mul]
      · rw [if_neg hi, zero_mul, Matrix.sub_apply, h i j (fun h => hi h.1), sub_self]
    · ext i j
      rw [coordinateProjection, Matrix.mul_diagonal]
      by_cases hj : ¬ s j
      · rw [if_pos hj, mul_one]
      · rw [if_neg hj, mul_zero, Matrix.sub_apply, h i j (fun h => hj h.2), sub_self]

theorem mem_blockRadical_iff {R : Type} [Ring R] {a n : ℕ} (u : GL (Fin n) R) :
    u ∈ U (blockProjection R a n) (1 - blockProjection R a n) ↔
      ∀ i j : Fin n, ¬ (i.val < a ∧ a ≤ j.val) → u.val i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  simpa only [blockProjection, not_lt] using mem_coordinateRadical_iff (fun i => i.val < a) u

variable {p a b : ℕ} [Fact p.Prime]

private theorem exists_leviKernel_of_mem_blockRadical (u : Gn p (a + b))
    (hu : u ∈ U (blockProjection (ZMod p) a (a + b)) (1 - blockProjection (ZMod p) a (a + b))) :
    ∃ x : (twoBlockLevi (g := p) (a := a) (b := b)).ker, x.val.val = u := by
  have h := (mem_blockRadical_iff u).mp hu
  let x : twoBlockParabolic p a b := ⟨u, fun i j hj hi => by
    rw [h i j (fun h => (not_lt_of_ge hi) h.1)]
    exact Matrix.one_apply_ne (by rintro rfl; omega)⟩
  have ht : tl a u.val = 1 := by
    ext i j
    rw [tl_apply_add, h _ _ (fun h => (j.isLt.not_ge) h.2)]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  have hb : br a b u.val = 1 := by
    ext i j
    rw [br_apply_add, h _ _ (fun h => (not_lt_of_ge (Nat.le_add_right a i.val)) h.1)]
    simp [Matrix.one_apply, Fin.natAdd_inj]
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker, twoBlockLevi_val]
  change (toG (tl a u.val), toG (br a b u.val)) = 1
  rw [ht, hb]
  have hOne {d : ℕ} : toG (1 : Mt p d) = 1 := by
    apply Units.ext
    rw [toG, dif_pos isUnit_one, IsUnit.unit_spec]
    rfl
  rw [hOne, hOne]
  rfl

theorem restriction_degree_zero_of_no_blockRadical_fixed
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Gn p (a + b)) V)
    (hτ : ∀ v : V, (∀ u ∈ U (blockProjection (ZMod p) a (a + b))
      (1 - blockProjection (ZMod p) a (a + b)), τ u v = v) → v = 0) :
    res a b τ.character 1 1 = 0 := by
  let P := twoBlockParabolic p a b
  let π : P →* Gn p a × Gn p b := twoBlockLevi
  let N := π.ker
  letI : Fintype N := Fintype.ofFinite _
  let σ : Representation ℂ N V := τ.comp (P.subtype.comp N.subtype)
  have hsum : ∑ u : N, σ u = 0 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    apply hτ
    intro u hu
    obtain ⟨x, rfl⟩ := exists_leviKernel_of_mem_blockRadical u hu
    change σ x (∑ u : N, σ u v) = _
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun y => ?_
    change σ x (σ y v) = σ (x * y) v
    rw [map_mul, Module.End.mul_apply]
  have hf : (∑ x : P, if π x = 1 then τ.character x.val else 0) =
      ∑ u : N, σ.character u := by
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x : P => x ∈ N), τ.character x.val := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun x _ => if_congr MonoidHom.mem_ker.symm rfl rfl
      _ = _ := Finset.sum_subtype _ (fun x : P =>
        (Finset.mem_filter).trans (and_iff_right (Finset.mem_univ x))) (fun x : P => τ.character x.val)
  rw [res_eq_sum_diagonal_fibre]
  change ((p : ℂ) ^ (a * b))⁻¹ * (∑ x : P, if π x = 1 then τ.character x.val else 0) = 0
  rw [hf]
  change ((p : ℂ) ^ (a * b))⁻¹ * ∑ u : N, LinearMap.trace ℂ V (σ u) = 0
  rw [← map_sum, hsum, map_zero, mul_zero]

end GlobalTheory.GLq

#print axioms GlobalTheory.GLq.restriction_degree_zero_of_no_blockRadical_fixed
