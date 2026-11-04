import GaloisForLFunctions.KodairaParshinAbc.DegreeZeroClassesHaveVanishingTateHeight
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.JacobiHurwitzTorsionInflationAndShortCycleHeights

/-!
# Jacobi–Hurwitz heights of degree zero

A torsion-weighted Jacobi–Hurwitz theta packet `P` on a real vector space has a log-height
`h_P = Σ wᵢ log ϑᵢ` at bounded distance from the homogeneous quadratic form
`q_P(x) = Σ wᵢ π Jᵢ(x)² / tᵢ` (`SelectivePositivityAndThresholdLaws.abs_jacobiHurwitzHeight_sub_quad_le`).
The two height principles for classes on a curve therefore apply to these packets:

* **negative degree** — if `h_P` is bounded above, then `q_P = 0`, so every channel functional
  `Jᵢ` vanishes (`jacobiHurwitz_J_eq_zero_of_bounded_above`);
* **degree zero** — if `|h_P - c h_Q| ≤ ε h_Q + B_ε` for every `ε > 0`, then the quadratic parts
  are proportional, `q_P = c q_Q` (`jacobiHurwitzQuad_eq_smul_of_degree_zero`).
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.KodairaParshinAbc

open SelectivePositivityAndThresholdLaws

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {m m' : ℕ}

theorem jacobiHurwitzQuad_two_nsmul (P : JacobiHurwitzTorsionPacket E m) (x : E) :
    jacobiHurwitzQuad P (2 • x) = 4 * jacobiHurwitzQuad P x := by
  rw [two_nsmul, ← two_smul ℝ x, jacobiHurwitzQuad_smul]
  norm_num

/-- **Negative degree for theta packets**: a Jacobi–Hurwitz height bounded above has vanishing
quadratic part. -/
theorem jacobiHurwitzQuad_eq_zero_of_bounded_above (P : JacobiHurwitzTorsionPacket E m) {B : ℝ}
    (hB : ∀ x, jacobiHurwitzHeight P x ≤ B) (x : E) : jacobiHurwitzQuad P x = 0 := by
  refine le_antisymm ?_ (jacobiHurwitzQuad_nonneg P x)
  refine nonpos_of_two_nsmul_of_bounded_above (q := jacobiHurwitzQuad P)
    (jacobiHurwitzQuad_two_nsmul P) (B := B + jacobiHurwitzErrorBound P) (fun y => ?_) x
  have h := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P y)).1
  linarith [hB y]

/-- A Jacobi–Hurwitz height bounded above has all channel functionals equal to zero. -/
theorem jacobiHurwitz_J_eq_zero_of_bounded_above (P : JacobiHurwitzTorsionPacket E m) {B : ℝ}
    (hB : ∀ x, jacobiHurwitzHeight P x ≤ B) (i : Fin m) (x : E) : P.J i x = 0 := by
  have h0 := jacobiHurwitzQuad_eq_zero_of_bounded_above P hB x
  unfold jacobiHurwitzQuad at h0
  have hterm := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (P.hw j).le
    (div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) (P.ht j).le))).mp h0 i (mem_univ i)
  have hw := P.hw i
  have ht := P.ht i
  have hsq : (P.J i x) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h hw.ne'
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact (mul_eq_zero.mp h).resolve_left Real.pi_pos.ne'
      · exact absurd h ht.ne'
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq

/-- **Degree zero for theta packets**: if `|h_P - c h_Q| ≤ ε h_Q + B_ε` for every `ε > 0`, the
quadratic parts satisfy `q_P = c q_Q`. -/
theorem jacobiHurwitzQuad_eq_smul_of_degree_zero (P : JacobiHurwitzTorsionPacket E m)
    (Q : JacobiHurwitzTorsionPacket E m') (c : ℝ)
    (hcor : ∀ ε > 0, ∃ B, ∀ x,
      |jacobiHurwitzHeight P x - c * jacobiHurwitzHeight Q x| ≤ ε * jacobiHurwitzHeight Q x + B)
    (x : E) : jacobiHurwitzQuad P x = c * jacobiHurwitzQuad Q x := by
  have h := eq_zero_of_two_nsmul_of_degree_zero
    (q := fun y => jacobiHurwitzQuad P y - c * jacobiHurwitzQuad Q y)
    (qM := jacobiHurwitzQuad Q)
    (fun y => by simp only [jacobiHurwitzQuad_two_nsmul]; ring) (jacobiHurwitzQuad_two_nsmul Q)
    (fun ε hε => by
      obtain ⟨B, hB⟩ := hcor ε hε
      refine ⟨B + jacobiHurwitzErrorBound P + |c| * jacobiHurwitzErrorBound Q +
        ε * jacobiHurwitzErrorBound Q, fun y => ?_⟩
      have hP := abs_jacobiHurwitzHeight_sub_quad_le P y
      have hQ := abs_jacobiHurwitzHeight_sub_quad_le Q y
      have hQ' := (abs_le.mp hQ).1
      have hcQ : |c * (jacobiHurwitzHeight Q y - jacobiHurwitzQuad Q y)| ≤
          |c| * jacobiHurwitzErrorBound Q := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hQ (abs_nonneg c)
      calc |jacobiHurwitzQuad P y - c * jacobiHurwitzQuad Q y|
          = |(jacobiHurwitzHeight P y - c * jacobiHurwitzHeight Q y) -
              (jacobiHurwitzHeight P y - jacobiHurwitzQuad P y) +
              c * (jacobiHurwitzHeight Q y - jacobiHurwitzQuad Q y)| := by ring_nf
        _ ≤ |jacobiHurwitzHeight P y - c * jacobiHurwitzHeight Q y| +
              |jacobiHurwitzHeight P y - jacobiHurwitzQuad P y| +
              |c * (jacobiHurwitzHeight Q y - jacobiHurwitzQuad Q y)| :=
            (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ (ε * jacobiHurwitzHeight Q y + B) + jacobiHurwitzErrorBound P +
              |c| * jacobiHurwitzErrorBound Q := by linarith [hB y]
        _ ≤ ε * jacobiHurwitzQuad Q y + (B + jacobiHurwitzErrorBound P +
              |c| * jacobiHurwitzErrorBound Q + ε * jacobiHurwitzErrorBound Q) := by
            have hle : jacobiHurwitzHeight Q y ≤ jacobiHurwitzQuad Q y + jacobiHurwitzErrorBound Q :=
              by linarith [(abs_le.mp hQ).2]
            nlinarith [mul_le_mul_of_nonneg_left hle hε.le]) x
  linarith

end GaloisForLFunctions.KodairaParshinAbc
