import GaloisForLFunctions.HTGeometry.DiagonalCommutatorWidth
import GaloisForLFunctions.QuantumAlg.Util.Complex

/-!
# Comparing an arc with its chord below a full winding

Two phases separated by at most `2π - η` have their separation controlled by their chord, with the
constant `(2π - η)/(2 sin(η/2))`.  The mechanism is the secant bound for the concave sine: on
`[0, π - η/2]` the sine lies above the chord from the origin, and `sin(π - η/2) = sin(η/2)`.

The constant blows up as `η → 0`, which is exactly the regime where a candidate logarithm approaches
a complete winding and collision-induced nonphysical branches become possible.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The exact chord between two phases. -/
theorem norm_expI_sub_eq (x y : ℝ) :
    ‖Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp (-(y : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((x - y) / 2)| := by
  have hsq := normSq_expI_sub (-x) (-y)
  have hcos : Real.cos (-x - -y) = Real.cos (x - y) := by
    rw [show (-x - -y : ℝ) = -(x - y) from by ring, Real.cos_neg]
  have hcast : ∀ r : ℝ, ((-r : ℝ) : ℂ) = -(r : ℂ) := fun r => by push_cast; ring
  rw [hcast, hcast, hcos] at hsq
  have hdouble : Real.cos (x - y) = 1 - 2 * Real.sin ((x - y) / 2) ^ 2 := by
    have h := Real.cos_two_mul ((x - y) / 2)
    rw [show 2 * ((x - y) / 2) = x - y from by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq ((x - y) / 2), h]
  rw [hdouble] at hsq
  have hnn : (0 : ℝ) ≤ ‖Complex.exp (-(x : ℂ) * Complex.I)
      - Complex.exp (-(y : ℂ) * Complex.I)‖ := norm_nonneg _
  have habs : (0 : ℝ) ≤ 2 * |Real.sin ((x - y) / 2)| := by positivity
  nlinarith [hsq, hnn, habs, sq_abs (Real.sin ((x - y) / 2))]

/-- **The secant comparison.**  Below a full winding, the separation is controlled by the sine of the
half-separation, with the constant of the endpoint. -/
theorem mul_sin_le_of_le_sub {η d : ℝ} (hη0 : 0 < η) (hηlt : η < 2 * Real.pi)
    (hd0 : 0 ≤ d) (hd : d ≤ 2 * Real.pi - η) :
    d * Real.sin (η / 2) ≤ (2 * Real.pi - η) * Real.sin (d / 2) := by
  set A : ℝ := Real.pi - η / 2 with hA
  have hApos : 0 < A := by
    rw [hA]
    linarith
  have hApi : A ≤ Real.pi := by
    rw [hA]
    linarith
  have hx0 : (0 : ℝ) ≤ d / 2 := by linarith
  have hxA : d / 2 ≤ A := by
    rw [hA]
    linarith
  have hsec := QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le hApos hApi hx0 hxA
  have hsinA : Real.sin A = Real.sin (η / 2) := by
    rw [hA]
    exact Real.sin_pi_sub _
  rw [hsinA] at hsec
  have hwidth : (0 : ℝ) < 2 * Real.pi - η := by linarith
  have hAval : 2 * A = 2 * Real.pi - η := by
    rw [hA]
    ring
  have hmul := mul_le_mul_of_nonneg_left hsec (le_of_lt hwidth)
  calc d * Real.sin (η / 2)
      = (2 * Real.pi - η) * (Real.sin (η / 2) / A * (d / 2)) := by
        rw [← hAval]
        field_simp
    _ ≤ (2 * Real.pi - η) * Real.sin (d / 2) := hmul

/-- **Theorem C.1's eigenvalue comparison.**  A separation below a full winding is at most a fixed
multiple of the chord. -/
theorem abs_sub_le_chord {η : ℝ} (hη0 : 0 < η) (hηlt : η < 2 * Real.pi) {a b : ℝ}
    (hd : |a - b| ≤ 2 * Real.pi - η) :
    |a - b| ≤ ((2 * Real.pi - η) / (2 * Real.sin (η / 2)))
      * ‖Complex.exp (-(a : ℂ) * Complex.I) - Complex.exp (-(b : ℂ) * Complex.I)‖ := by
  have hsin : 0 < Real.sin (η / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith
  have hmain := mul_sin_le_of_le_sub hη0 hηlt (abs_nonneg (a - b)) hd
  rw [norm_expI_sub_eq]
  have hchord : |a - b| * Real.sin (η / 2)
      ≤ (2 * Real.pi - η) * |Real.sin ((a - b) / 2)| := by
    refine le_trans hmain ?_
    have hle : Real.sin (|a - b| / 2) ≤ |Real.sin ((a - b) / 2)| := by
      rcases abs_cases (a - b) with ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [heq]
        exact le_abs_self _
      · rw [heq]
        rw [show (-(a - b) : ℝ) / 2 = -((a - b) / 2) from by ring, Real.sin_neg]
        rw [← abs_neg]
        exact le_abs_self _
    have hwidth : (0 : ℝ) < 2 * Real.pi - η := by linarith
    exact mul_le_mul_of_nonneg_left hle (le_of_lt hwidth)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hchord, hsin]

/-! ## The entrywise commutator comparison -/

section Entrywise

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator of a matrix with a diagonal, in the other order. -/
theorem commutator_diagonal_apply' (d : n → ℂ) (X : Matrix n n ℂ) (i j : n) :
    (X * Matrix.diagonal d - Matrix.diagonal d * X) i j = (d j - d i) * X i j := by
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- **Theorem C.1's commutator comparison.**  An entrywise comparison of two diagonal families
transfers to their commutator energies. -/
theorem hsSqRe_commutator_comparison (d e : n → ℂ) (X : Matrix n n ℂ) {C : ℝ}
    (hcomp : ∀ i j : n, ‖d j - d i‖ ≤ C * ‖e j - e i‖) :
    hsSqRe (X * Matrix.diagonal d - Matrix.diagonal d * X)
      ≤ C ^ 2 * hsSqRe (X * Matrix.diagonal e - Matrix.diagonal e * X) := by
  rw [hsSqRe_eq_sum, hsSqRe_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [commutator_diagonal_apply', commutator_diagonal_apply', norm_mul, norm_mul, mul_pow,
    mul_pow]
  have hab := hcomp b a
  have hnn : (0 : ℝ) ≤ ‖d a - d b‖ := norm_nonneg _
  have hnn' : (0 : ℝ) ≤ ‖e a - e b‖ := norm_nonneg _
  have hsq : ‖d a - d b‖ ^ 2 ≤ C ^ 2 * ‖e a - e b‖ ^ 2 := by
    nlinarith [hab, hnn, hnn']
  calc ‖d a - d b‖ ^ 2 * ‖X b a‖ ^ 2
      ≤ (C ^ 2 * ‖e a - e b‖ ^ 2) * ‖X b a‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = C ^ 2 * (‖e a - e b‖ ^ 2 * ‖X b a‖ ^ 2) := by ring

omit [DecidableEq n] in
/-- **Left multiplication is bounded by the operator norm.**  Each column is moved by at most the
operator bound, so the total Hilbert--Schmidt energy is. -/
theorem hsSqRe_mul_left_le (E A : Matrix n n ℂ) {c : ℝ}
    (hE : ∀ v : n → ℂ, ∑ l, ‖(E *ᵥ v) l‖ ^ 2 ≤ c ^ 2 * ∑ l, ‖v l‖ ^ 2) :
    hsSqRe (E * A) ≤ c ^ 2 * hsSqRe A := by
  rw [hsSqRe_eq_sum, hsSqRe_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have hcol : ∀ b : n, (E * A) b a = (E *ᵥ fun k => A k a) b := by
    intro b
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun b _ => by rw [hcol b]]
  exact hE _

end Entrywise


end GaloisForLFunctions.HTGeometry
