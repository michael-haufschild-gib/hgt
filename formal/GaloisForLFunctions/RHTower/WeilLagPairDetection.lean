import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Sharp detection scale for reflected Weil-lag pole pairs

For a pair at `ρ = 1/2 ± a + iγ`, put `X = γ² + 1/4 - a²` and
`A = Im s - γ`. The real-coordinate pair response below is the real part
of the two weighted resolvents multiplied by the positive factor
`X² + 4a²γ²`.

For `σ > |a|`, all-frequency nonnegativity is equivalent to
`4a⁴γ² ≤ X²(σ²-a²)`. The negative-frequency set is an explicit quadratic
sublevel set. In physical coordinates, a negative value with `σ > a > 0`
requires `(σ-a)γ² < 2a³`.

Shallow off-line quartets at arbitrary large heights satisfy positivity for
`σ ≥ 13/25`, with arbitrary multiplicity. These are algebraic model spectra,
not asserted zeta zeros; they test the information supplied by the damping
sign alone. No density theorem or prime-side estimate is assumed or proved.
-/

namespace RHTower.LagPairDetection

noncomputable section

def response (X a γ σ A : ℝ) : ℝ :=
  (X * (σ - a) + 2 * a * γ * A) / ((σ - a) ^ 2 + A ^ 2) +
  (X * (σ + a) - 2 * a * γ * A) / ((σ + a) ^ 2 + A ^ 2)

def quadratic (X a γ σ A : ℝ) : ℝ :=
  X * (σ ^ 2 - a ^ 2 + A ^ 2) + 4 * a ^ 2 * γ * A

theorem denominator_pos {a σ A : ℝ} (ha : |a| < σ) :
    0 < ((σ - a) ^ 2 + A ^ 2) * ((σ + a) ^ 2 + A ^ 2) := by
  obtain ⟨hl, hr⟩ := abs_lt.mp ha
  apply mul_pos <;> nlinarith [sq_nonneg A, sq_pos_of_pos (show 0 < σ - a by linarith),
    sq_pos_of_pos (show 0 < σ + a by linarith)]

theorem response_mul_den {X a γ σ A : ℝ} (ha : |a| < σ) :
    response X a γ σ A *
      (((σ - a) ^ 2 + A ^ 2) * ((σ + a) ^ 2 + A ^ 2)) =
        2 * σ * quadratic X a γ σ A := by
  obtain ⟨hl, hr⟩ := abs_lt.mp ha
  have h1 : (σ - a) ^ 2 + A ^ 2 ≠ 0 := by
    have := sq_pos_of_pos (show 0 < σ - a by linarith)
    nlinarith [sq_nonneg A]
  have h2 : (σ + a) ^ 2 + A ^ 2 ≠ 0 := by
    have := sq_pos_of_pos (show 0 < σ + a by linarith)
    nlinarith [sq_nonneg A]
  unfold response quadratic
  field_simp [h1, h2]
  ring

theorem square_identity (X a γ σ A : ℝ) :
    X * quadratic X a γ σ A =
      (X * A + 2 * a ^ 2 * γ) ^ 2 +
        X ^ 2 * (σ ^ 2 - a ^ 2) - 4 * a ^ 4 * γ ^ 2 := by
  unfold quadratic
  ring

theorem response_nonneg_iff {X a γ σ A : ℝ} (hX : 0 < X) (ha : |a| < σ) :
    0 ≤ response X a γ σ A ↔
      4 * a ^ 4 * γ ^ 2 ≤ (X * A + 2 * a ^ 2 * γ) ^ 2 +
        X ^ 2 * (σ ^ 2 - a ^ 2) := by
  have hσ : 0 < 2 * σ := by linarith [abs_nonneg a]
  rw [← mul_nonneg_iff_of_pos_right (denominator_pos ha), response_mul_den ha,
    mul_nonneg_iff_of_pos_left hσ, ← mul_nonneg_iff_of_pos_left hX,
    square_identity]
  constructor <;> intro h <;> linarith

/-- Exact negative-frequency region, not only a sufficient positivity test. -/
theorem response_neg_iff {X a γ σ A : ℝ} (hX : 0 < X) (ha : |a| < σ) :
    response X a γ σ A < 0 ↔
      (X * A + 2 * a ^ 2 * γ) ^ 2 <
        4 * a ^ 4 * γ ^ 2 - X ^ 2 * (σ ^ 2 - a ^ 2) := by
  have h := response_nonneg_iff (γ := γ) (A := A) hX ha
  constructor <;> intro hh
  · by_contra hn
    have hp : 0 ≤ response X a γ σ A := h.mpr (by linarith)
    linarith
  · by_contra hn
    have hp := h.mp (show 0 ≤ response X a γ σ A by linarith)
    linarith

/-- The all-frequency threshold is necessary and sufficient. -/
theorem all_nonneg_iff {X a γ σ : ℝ} (hX : 0 < X) (ha : |a| < σ) :
    (∀ A : ℝ, 0 ≤ response X a γ σ A) ↔
      4 * a ^ 4 * γ ^ 2 ≤ X ^ 2 * (σ ^ 2 - a ^ 2) := by
  constructor
  · intro h
    have hstar := (response_nonneg_iff hX ha).mp (h (-2 * a ^ 2 * γ / X))
    have he : X * (-2 * a ^ 2 * γ / X) + 2 * a ^ 2 * γ = 0 := by
      field_simp [hX.ne']
      ring
    rw [he, zero_pow (by decide), zero_add] at hstar
    exact hstar
  · intro h A
    exact (response_nonneg_iff hX ha).mpr (by nlinarith [sq_nonneg (X * A + 2 * a ^ 2 * γ)])

/-- A synthetic shallow off-line pair, at depth 1/10 and arbitrary large height,
passes the damping gate.
This is a model of the pair geometry, not a claim that these points are zeta zeros. -/
theorem offLine_model_nonneg {γ σ : ℝ} (hγ : 25 ≤ γ ^ 2)
    (hσ : 13 / 25 ≤ σ) (A : ℝ) :
    0 ≤ response (γ ^ 2 + 6 / 25) (1 / 10) γ σ A := by
  apply (all_nonneg_iff (by nlinarith : (0 : ℝ) < γ ^ 2 + 6 / 25)
    (show |(1 / 10 : ℝ)| < σ by norm_num; linarith)).mpr ?_ A
  have hs : (13 / 25 : ℝ) ^ 2 ≤ σ ^ 2 := by nlinarith
  have hX : γ ^ 2 ≤ (γ ^ 2 + 6 / 25) ^ 2 := by
    nlinarith [sq_nonneg (γ ^ 2 - 1)]
  have hp := mul_le_mul_of_nonneg_left
    (show (13 / 25 : ℝ) ^ 2 - (1 / 10) ^ 2 ≤ σ ^ 2 - (1 / 10) ^ 2 by linarith)
    (sq_nonneg (γ ^ 2 + 6 / 25))
  norm_num at hp ⊢
  nlinarith

theorem response_neg_height (X a γ σ A : ℝ) :
    response X a (-γ) σ A = response X a γ σ (-A) := by
  unfold response
  congr 1 <;> congr 1 <;> ring

/-- The conjugation-completed quartet also passes. Arbitrary replication preserves the sign;
positivity at fixed damping therefore does not restrict its off-line proportion. -/
theorem offLine_quartet_nonneg (m : ℕ) {γ σ t : ℝ}
    (hγ : 25 ≤ γ ^ 2) (hσ : 13 / 25 ≤ σ) :
    0 ≤ (m : ℝ) *
      (response (γ ^ 2 + 6 / 25) (1 / 10) γ σ (t - γ) +
        response (γ ^ 2 + 6 / 25) (1 / 10) (-γ) σ (t + γ)) := by
  rw [response_neg_height]
  exact mul_nonneg (Nat.cast_nonneg m)
    (add_nonneg (offLine_model_nonneg hγ hσ _) (offLine_model_nonneg hγ hσ _))

/-- The exact witness exposed by failure of the sharp threshold. -/
theorem response_at_witness_neg {X a γ σ : ℝ} (hX : 0 < X) (ha : |a| < σ)
    (hgap : X ^ 2 * (σ ^ 2 - a ^ 2) < 4 * a ^ 4 * γ ^ 2) :
    response X a γ σ (-2 * a ^ 2 * γ / X) < 0 := by
  rw [response_neg_iff hX ha]
  have he : X * (-2 * a ^ 2 * γ / X) + 2 * a ^ 2 * γ = 0 := by
    field_simp [hX.ne']
    ring
  rw [he, zero_pow (by decide)]
  linarith

/-- In physical lag coordinates, detecting a pair from the right of its pole requires
radial resolution finer than `2 a^3 / γ^2`. This is an exact inequality, not asymptotic
or numerical evidence. It concerns this pair detector, not every possible aggregate test. -/
theorem radial_resolution_of_neg {a γ σ A : ℝ}
    (ha : 0 < a) (haHalf : a < 1 / 2) (hγ : 0 < γ ^ 2) (hσ : a < σ)
    (hneg : response (γ ^ 2 + 1 / 4 - a ^ 2) a γ σ A < 0) :
    (σ - a) * γ ^ 2 < 2 * a ^ 3 := by
  let X := γ ^ 2 + 1 / 4 - a ^ 2
  have hXa : γ ^ 2 ≤ X := by dsimp [X]; nlinarith
  have hX : 0 < X := lt_of_lt_of_le hγ hXa
  have hσabs : |a| < σ := by rw [abs_of_pos ha]; exact hσ
  have hn := (response_neg_iff hX hσabs).mp hneg
  have hgap : X ^ 2 * (σ ^ 2 - a ^ 2) < 4 * a ^ 4 * γ ^ 2 := by
    nlinarith [sq_nonneg (X * A + 2 * a ^ 2 * γ)]
  have hD : 0 < σ ^ 2 - a ^ 2 := by nlinarith
  have hX2 : γ ^ 2 * γ ^ 2 ≤ X ^ 2 := by nlinarith
  have hcmp := mul_le_mul_of_nonneg_right hX2 hD.le
  have hmid : γ ^ 2 * (σ ^ 2 - a ^ 2) < 4 * a ^ 4 := by
    by_contra hn
    have hp := mul_nonneg hγ.le
      (show 0 ≤ γ ^ 2 * (σ ^ 2 - a ^ 2) - 4 * a ^ 4 by linarith)
    nlinarith
  have hsmall : 2 * a * (σ - a) ≤ σ ^ 2 - a ^ 2 := by
    nlinarith [sq_nonneg (σ - a)]
  have hsmallg := mul_le_mul_of_nonneg_left hsmall hγ.le
  by_contra hn
  have hp := mul_nonneg ha.le
    (show 0 ≤ (σ - a) * γ ^ 2 - 2 * a ^ 3 by linarith)
  nlinarith

end

end RHTower.LagPairDetection
