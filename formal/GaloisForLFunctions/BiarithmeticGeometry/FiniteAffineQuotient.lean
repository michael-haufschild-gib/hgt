import GaloisForLFunctions.BiarithmeticGeometry.HorizonAffineActions
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!
# The faithful finite quotient of the absorbing affine action

The origin and first cell determine an affine operator completely. Its finite image has
one zero state and a triangular array of nonzero states, including one saturated slope
at each surviving origin. This gives an exact polynomial-size quotient without periodicity.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

theorem horizonCell_eq_zero_iff (N j : ℕ) : horizonCell N j = 0 ↔ N < j := by
  constructor
  · intro h
    by_contra hj
    have he := congrFun h ⟨j, by omega⟩
    simp [horizonCell] at he
  · exact horizonCell_eq_zero N j

/-- Two absorbed cells agree exactly when their indices agree or both have escaped. -/
theorem horizonCell_eq_iff (N i j : ℕ) :
    horizonCell N i = horizonCell N j ↔ i = j ∨ (N < i ∧ N < j) := by
  constructor
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      constructor
      · by_contra hi
        have he := congrFun h ⟨i, by omega⟩
        simp [horizonCell, hij] at he
      · by_contra hj
        have he := congrFun h ⟨j, by omega⟩
        simp [horizonCell, Ne.symm hij] at he
  · rintro (rfl | ⟨hi, hj⟩)
    · rfl
    · rw [horizonCell_eq_zero N i hi, horizonCell_eq_zero N j hj]

/-- The whole positive affine action vanishes exactly when its origin has escaped. -/
theorem horizonAffine_eq_zero_iff (N : ℕ) (a : ℕ+) (b : ℕ) :
    horizonAffine N a b = 0 ↔ N < b := by
  constructor
  · intro h
    have he := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N =>
      L (horizonCell N 0)) h
    simpa only [horizonAffine_cell_nat, mul_zero, zero_add,
      LinearMap.zero_apply, horizonCell_eq_zero_iff] using he
  · intro hb
    apply LinearMap.ext
    intro v
    change (∑ j : Fin (N + 1), v j • horizonCell N (a * j.val + b)) = 0
    apply Finset.sum_eq_zero
    intro j _
    rw [horizonCell_eq_zero N (a * j.val + b) (by omega), smul_zero]

/-- Complete equality classification for absorbing-horizon affine operators. -/
theorem horizonAffine_eq_iff (N : ℕ) (a c : ℕ+) (b d : ℕ) :
    horizonAffine N a b = horizonAffine N c d ↔
      (N < b ∧ N < d) ∨
        (b = d ∧ (a = c ∨ (N < (a : ℕ) + b ∧ N < (c : ℕ) + d))) := by
  constructor
  · intro h
    have h0 := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N =>
      L (horizonCell N 0)) h
    have h1 := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N =>
      L (horizonCell N 1)) h
    simp only [horizonAffine_cell_nat, mul_zero, zero_add] at h0
    simp only [horizonAffine_cell_nat, mul_one] at h1
    rcases (horizonCell_eq_iff N b d).mp h0 with hbd | hbd
    · right
      refine ⟨hbd, ?_⟩
      rcases (horizonCell_eq_iff N _ _).mp h1 with hac | hout
      · left
        apply Subtype.ext
        change (a : ℕ) = (c : ℕ)
        omega
      · exact Or.inr hout
    · exact Or.inl hbd
  · rintro (⟨hb, hd⟩ | ⟨hbd, hac⟩)
    · rw [(horizonAffine_eq_zero_iff N a b).mpr hb,
        (horizonAffine_eq_zero_iff N c d).mpr hd]
    · subst d
      rcases hac with rfl | ⟨ha, hc⟩
      · rfl
      · apply LinearMap.ext
        intro v
        change (∑ j : Fin (N + 1), v j • horizonCell N (a * j.val + b)) =
          ∑ j : Fin (N + 1), v j • horizonCell N (c * j.val + b)
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val = 0
        · simp only [hj, mul_zero]
        · have hj1 : 1 ≤ j.val := by omega
          have haj : (a : ℕ) ≤ (a : ℕ) * j.val := by
            simpa only [mul_one] using Nat.mul_le_mul_left (a : ℕ) hj1
          have hcj : (c : ℕ) ≤ (c : ℕ) * j.val := by
            simpa only [mul_one] using Nat.mul_le_mul_left (c : ℕ) hj1
          rw [horizonCell_eq_zero N _ (by omega), horizonCell_eq_zero N _ (by omega)]

/-- Images of the origin and first cell determine every operator in the affine image. -/
theorem horizonAffine_eq_iff_origin_first (N : ℕ) (a c : ℕ+) (b d : ℕ) :
    horizonAffine N a b = horizonAffine N c d ↔
      horizonAffine N a b (horizonCell N 0) = horizonAffine N c d (horizonCell N 0) ∧
      horizonAffine N a b (horizonCell N 1) = horizonAffine N c d (horizonCell N 1) := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    simp only [horizonAffine_cell_nat, mul_zero, zero_add] at h0
    simp only [horizonAffine_cell_nat, mul_one] at h1
    apply (horizonAffine_eq_iff N a c b d).mpr
    rcases (horizonCell_eq_iff N b d).mp h0 with hbd | hout
    · right
      refine ⟨hbd, ?_⟩
      rcases (horizonCell_eq_iff N _ _).mp h1 with hac | hout
      · left
        apply Subtype.ext
        change (a : ℕ) = (c : ℕ)
        omega
      · exact Or.inr hout
    · exact Or.inl hout

/-- One zero state, and a surviving origin with a clipped positive slope. -/
abbrev HorizonAffineCode (N : ℕ) := Option (Σ b : Fin (N + 1), Fin (N + 1 - b.val))

def horizonCodeAction (N : ℕ) : HorizonAffineCode N → (HorizonSpace N →ₗ[ℝ] HorizonSpace N)
  | none => 0
  | some ⟨b, a⟩ => horizonAffine N ⟨a.val + 1, Nat.succ_pos _⟩ b.val

/-- Distinct finite codes represent distinct affine operators. -/
theorem horizonCodeAction_injective (N : ℕ) : Function.Injective (horizonCodeAction N) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      rcases y with ⟨b, a⟩
      have hz := (horizonAffine_eq_zero_iff N ⟨a.val + 1, Nat.succ_pos _⟩ b.val).mp h.symm
      have hb := b.isLt
      omega
  | some x =>
    cases y with
    | none =>
      rcases x with ⟨b, a⟩
      have hz := (horizonAffine_eq_zero_iff N ⟨a.val + 1, Nat.succ_pos _⟩ b.val).mp h
      have hb := b.isLt
      omega
    | some y =>
      rcases x with ⟨b, a⟩
      rcases y with ⟨d, c⟩
      rcases (horizonAffine_eq_iff N ⟨a.val + 1, Nat.succ_pos _⟩
        ⟨c.val + 1, Nat.succ_pos _⟩ b.val d.val).mp h with hout | ⟨hbd, hs⟩
      · have hb := b.isLt; omega
      · have hbd' : b = d := Fin.ext hbd
        subst d
        have hac : a = c := by
          apply Fin.ext
          rcases hs with hs | hs
          · have he := congrArg (fun z : ℕ+ => (z : ℕ)) hs
            dsimp at he
            omega
          · have ha := a.isLt
            have hc := c.isLt
            dsimp at hs
            omega
        subst c
        rfl

/-- Every positive affine operator has one of the finite canonical codes. -/
theorem exists_horizonAffineCode (N : ℕ) (a : ℕ+) (b : ℕ) :
    ∃ c : HorizonAffineCode N, horizonCodeAction N c = horizonAffine N a b := by
  by_cases hb : b ≤ N
  · let k : ℕ := min ((a : ℕ) - 1) (N - b)
    have hk : k < N + 1 - b := by
      have := min_le_right ((a : ℕ) - 1) (N - b)
      dsimp [k]
      omega
    refine ⟨some ⟨⟨b, by omega⟩, ⟨k, hk⟩⟩, ?_⟩
    change horizonAffine N ⟨k + 1, Nat.succ_pos _⟩ b = horizonAffine N a b
    apply (horizonAffine_eq_iff N _ _ _ _).mpr
    right
    refine ⟨rfl, ?_⟩
    by_cases ha : (a : ℕ) + b ≤ N
    · left
      apply Subtype.ext
      change k + 1 = (a : ℕ)
      dsimp [k]
      rw [min_eq_left (by omega)]
      have := a.pos
      omega
    · right
      have hmin : k = N - b := min_eq_right (by omega)
      dsimp
      rw [hmin]
      omega
  · exact ⟨none, ((horizonAffine_eq_zero_iff N a b).mpr (by omega)).symm⟩

/-- The finite code image is exactly the full positive affine image. -/
theorem range_horizonCodeAction (N : ℕ) :
    Set.range (horizonCodeAction N) =
      Set.range (fun ab : ℕ+ × ℕ => horizonAffine N ab.1 ab.2) := by
  ext L
  constructor
  · rintro ⟨c, rfl⟩
    cases c with
    | none => exact ⟨(1, N + 1), (horizonAffine_eq_zero_iff N 1 (N + 1)).mpr (by omega)⟩
    | some c =>
      rcases c with ⟨b, a⟩
      exact ⟨(⟨a.val + 1, Nat.succ_pos _⟩, b.val), rfl⟩
  · rintro ⟨⟨a,b⟩, rfl⟩
    exact exists_horizonAffineCode N a b

theorem card_horizonAffineCode_sum (N : ℕ) :
    Fintype.card (HorizonAffineCode N) =
      1 + ∑ b : Fin (N + 1), (N + 1 - b.val) := by
  simp only [HorizonAffineCode, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin]
  omega

private theorem sum_fin_tsub_mul_two (n : ℕ) :
    2 * (∑ i : Fin n, (n - i.val)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
    nlinarith only [ih]

/-- The faithful finite code space has triangular, hence polynomial, size. -/
theorem card_horizonAffineCode (N : ℕ) :
    Fintype.card (HorizonAffineCode N) = 1 + (N + 1) * (N + 2) / 2 := by
  rw [card_horizonAffineCode_sum]
  have h : 2 * (∑ i : Fin (N + 1), (N + 1 - i.val)) = (N + 1) * (N + 2) := by
    simpa only [Nat.add_assoc] using sum_fin_tsub_mul_two (N + 1)
  omega

/-- The codes identify the entire operator image, with no full-period completion. -/
def horizonAffineImageEquiv (N : ℕ) :
    HorizonAffineCode N ≃ Set.range (fun ab : ℕ+ × ℕ => horizonAffine N ab.1 ab.2) :=
  Equiv.ofBijective
    (fun c => ⟨horizonCodeAction N c, by
      rw [← range_horizonCodeAction]
      exact ⟨c, rfl⟩⟩)
    ⟨fun x y h => horizonCodeAction_injective N (congrArg Subtype.val h), by
      intro L
      obtain ⟨⟨a, b⟩, hab⟩ := L.property
      obtain ⟨c, hc⟩ := exists_horizonAffineCode N a b
      exact ⟨c, Subtype.ext (hc.trans hab)⟩⟩

/-- Exact number of distinct positive affine operators at the given horizon. -/
theorem card_horizonAffine_image (N : ℕ) :
    Nat.card (Set.range (fun ab : ℕ+ × ℕ => horizonAffine N ab.1 ab.2)) =
      1 + (N + 1) * (N + 2) / 2 := by
  rw [← Nat.card_congr (horizonAffineImageEquiv N), Nat.card_eq_fintype_card,
    card_horizonAffineCode]

/-- Canonical affine states are closed under exact composition. -/
theorem horizonCodeAction_comp (N : ℕ) (x y : HorizonAffineCode N) :
    ∃ z : HorizonAffineCode N,
      horizonCodeAction N z = (horizonCodeAction N x).comp (horizonCodeAction N y) := by
  cases x with
  | none => exact ⟨none, by simp [horizonCodeAction]⟩
  | some x =>
    cases y with
    | none => exact ⟨none, by simp [horizonCodeAction]⟩
    | some y =>
      rcases x with ⟨b, a⟩
      rcases y with ⟨d, c⟩
      dsimp [horizonCodeAction]
      rw [horizonAffine_comp]
      exact exists_horizonAffineCode N _ _

end GaloisForLFunctions.BiarithmeticGeometry
