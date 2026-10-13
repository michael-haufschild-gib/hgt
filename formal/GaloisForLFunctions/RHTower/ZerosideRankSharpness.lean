import Zeta23.Assembly

/-!
# Sharpness of the rank–trace counting inequality

Alpöge–Furman's counting step (`Zeta23.Assembly.zeroside_rank_core`): if `Â = P + Q` with `P ⪰ 0`,
`rank P ≤ r`, `Q` Hermitian with at most `b` positive eigenvalues, `tr P ≤ N_on` and `N_on + 2b ≤ N`, then

`4 tr Â − 2N − ‖Â‖_F² ≤ r`.

This inequality is attained for every `r` and `b` (`zeroside_rank_core_sharp`): take `P` the identity on
`r` coordinates (simple zeros on the line, mutually orthogonal) and `Q = 2·`identity on `b` further
coordinates (off-line pairs whose two vectors coincide).  Then `tr Â = N = r + 2b`,
`‖Â‖_F² = r + 4b`, and the left side is exactly `r = rank P`.

Consequently, with only `tr Â ≈ N` and `‖Â‖_F² ≈ cN` as inputs, the critical-line proportion `2 − c`
cannot be improved: the configuration with a proportion `2 − c` of orthogonal simple zeros and a
proportion `c − 1` of zeros in coalesced off-line pairs meets every hypothesis
(`critical_line_bound_optimal`).  Its spectrum lies on `{0, 1, 2}`, so every spectral moment
satisfies `S₃ − 3S₂ + 2S₁ = 0` (`extremal_third_moment`), the same relation as the sine-kernel moments
at bandwidth one.
-/

open Matrix RHLinalg
open scoped ComplexOrder

noncomputable section

namespace RHTower

/-- The diagonal of the on-line part: `1` on the first `r` coordinates. -/
def sharpOnDiag (r b : ℕ) : Fin r ⊕ Fin b → ℂ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- The diagonal of the off-line part: `2` on the last `b` coordinates. -/
def sharpOffDiag (r b : ℕ) : Fin r ⊕ Fin b → ℂ := Sum.elim (fun _ => 0) (fun _ => 2)

theorem rtrace_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    rtrace (diagonal d) = ∑ i, (d i).re := by
  unfold rtrace; rw [trace_diagonal]; simp

theorem frobSq_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    frobSq (diagonal d) = ∑ i, ‖d i‖ ^ 2 := by
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [diagonal_apply_ne _ (Ne.symm hji)]; simp)
    (by simp)]
  rw [diagonal_apply_eq]

/-- The nonzero coordinates of the on-line part are exactly the first `r`. -/
def sharpOnEquiv (r b : ℕ) : {i // sharpOnDiag r b i ≠ 0} ≃ Fin r where
  toFun := fun x => match x with
    | ⟨Sum.inl a, _⟩ => a
    | ⟨Sum.inr _, h⟩ => (h rfl).elim
  invFun := fun a => ⟨Sum.inl a, by simp [sharpOnDiag]⟩
  left_inv := by
    rintro ⟨(a | a), h⟩
    · rfl
    · exact (h rfl).elim
  right_inv := fun _ => rfl

theorem rank_sharpOn (r b : ℕ) : (diagonal (sharpOnDiag r b)).rank = r := by
  rw [rank_diagonal, Fintype.card_congr (sharpOnEquiv r b), Fintype.card_fin]

/-- **The counting inequality is attained.** -/
theorem zeroside_rank_core_sharp (r b : ℕ) :
    ∃ (P Q : Matrix (Fin r ⊕ Fin b) (Fin r ⊕ Fin b) ℂ) (hQ : Q.IsHermitian),
      P.PosSemidef ∧ P.rank = r ∧ posIndex hQ ≤ b ∧ rtrace P = r ∧
      rtrace (P + Q) = r + 2 * b ∧ frobSq (P + Q) = r + 4 * b ∧
      4 * rtrace (P + Q) - 2 * ((r : ℝ) + 2 * b) - frobSq (P + Q) = r := by
  have hsa : IsSelfAdjoint (sharpOffDiag r b) := by
    funext i; cases i <;> simp [sharpOffDiag]
  have hQ := isHermitian_diagonal_of_self_adjoint _ hsa
  have hsum : diagonal (sharpOnDiag r b) + diagonal (sharpOffDiag r b)
      = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => 2)) := by
    rw [diagonal_add]; congr 1; funext i; cases i <;> simp [sharpOnDiag, sharpOffDiag]
  have htrP : rtrace (diagonal (sharpOnDiag r b)) = r := by
    rw [rtrace_diagonal, Fintype.sum_sum_type]; simp [sharpOnDiag]
  have htrA : rtrace (diagonal (sharpOnDiag r b) + diagonal (sharpOffDiag r b)) = r + 2 * b := by
    rw [hsum, rtrace_diagonal, Fintype.sum_sum_type]; simp; ring
  have hfrA : frobSq (diagonal (sharpOnDiag r b) + diagonal (sharpOffDiag r b)) = r + 4 * b := by
    rw [hsum, frobSq_diagonal, Fintype.sum_sum_type]; simp; norm_num; ring
  have hrankQ : (diagonal (sharpOffDiag r b)).rank ≤ b := by
    rw [rank_diagonal]
    have hf : ∀ x : {i // sharpOffDiag r b i ≠ 0}, x.1.isRight = true := by
      rintro ⟨(a | a), h⟩
      · exact (h (by simp [sharpOffDiag])).elim
      · rfl
    calc Fintype.card {i // sharpOffDiag r b i ≠ 0}
        ≤ Fintype.card {i : Fin r ⊕ Fin b // i.isRight} :=
          Fintype.card_le_of_injective (fun x => ⟨x.1, hf x⟩)
            (fun x y h => Subtype.ext (congrArg Subtype.val h :))
      _ = b := by
          rw [Fintype.card_subtype]
          rw [show (Finset.univ.filter fun i : Fin r ⊕ Fin b => i.isRight = true)
              = Finset.univ.map Function.Embedding.inr by
            ext i; cases i <;> simp]
          simp
  refine ⟨diagonal (sharpOnDiag r b), diagonal (sharpOffDiag r b), hQ, ?_, rank_sharpOn r b,
    (Zeta23.Assembly.posIndex_le_rank hQ).trans hrankQ, htrP, htrA, hfrA, ?_⟩
  · rw [posSemidef_diagonal_iff]; intro i; cases i <;> simp [sharpOnDiag]
  · rw [htrA, hfrA]; ring

/-- **The critical-line bound `2 − c` is optimal for its inputs.**  For every `r, b` (not both zero)
there is a configuration with `N = r + 2b`, `tr Â = N`, `‖Â‖_F² = cN` with `c = (r + 4b)/(r + 2b)`,
meeting every hypothesis of the counting step, whose on-line rank is exactly `(2 − c) N`. -/
theorem critical_line_bound_optimal (r b : ℕ) (h : 0 < r + 2 * b) :
    ∃ (P Q : Matrix (Fin r ⊕ Fin b) (Fin r ⊕ Fin b) ℂ) (hQ : Q.IsHermitian),
      P.PosSemidef ∧ posIndex hQ ≤ b ∧ rtrace P ≤ r ∧ (r : ℝ) + 2 * b ≤ r + 2 * b ∧
      rtrace (P + Q) = r + 2 * b ∧
      (P.rank : ℝ) = (2 - frobSq (P + Q) / (r + 2 * b)) * (r + 2 * b) := by
  obtain ⟨P, Q, hQ, hP, hrank, hpos, htrP, htrA, hfrA, -⟩ := zeroside_rank_core_sharp r b
  have hN : (0 : ℝ) < r + 2 * b := by exact_mod_cast h
  refine ⟨P, Q, hQ, hP, hpos, htrP.le, le_rfl, htrA, ?_⟩
  rw [hrank, hfrA]
  field_simp
  ring

/-- The extremal spectrum lies on `{0, 1, 2}`: `x³ − 3x² + 2x` vanishes there, so the third spectral
moment is determined by the first two, `S₃ = 3S₂ − 2S₁`. -/
theorem extremal_third_moment (r b : ℕ) :
    (r : ℝ) * 1 ^ 3 + b * 2 ^ 3 = 3 * ((r : ℝ) * 1 ^ 2 + b * 2 ^ 2) - 2 * ((r : ℝ) * 1 + b * 2) := by
  ring

end RHTower
