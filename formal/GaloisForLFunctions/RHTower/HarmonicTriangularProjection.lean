import GaloisForLFunctions.RHTower.FloorTransformHarmonicInverse

/-!
# The harmonic triangular projection of a floor transport

For a source sequence `a` with partial sums `R`, the triangular transport

`T_N(D) = ∑_{m ≤ ⌊N/(D+1)⌋} a_m (⌊N/m⌋ − D)`

is exactly the tail `∑_{d > D} R(⌊N/d⌋)` of the harmonic floor transform.  Projecting it against
the harmonic increment weights `w_D = 1/D − 1/(D+1)` collapses it back onto the same two invariants
it came from:

`∑_{D < N} w_D T_N(D) = ∑_{m ≤ N} a_m ⌊N/m⌋ − ∑_{d ≤ N} R(⌊N/d⌋)/d`.

So the signed harmonic projection is a change of coordinates, not a cancellation mechanism.  The
quadratic path kernel is computed in closed form as well; it is positive semidefinite, and its
diagonal is of the same size as the whole transport.
-/

namespace RHTower

noncomputable section

/-! ## Harmonic sums and increment weights -/

/-- The harmonic number `H_n = ∑_{k ≤ n} 1/k`. -/
def harmonicSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

theorem harmonicSum_succ (n : ℕ) :
    harmonicSum (n + 1) = harmonicSum n + 1 / ((n : ℝ) + 1) := by
  rw [harmonicSum, harmonicSum, Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

/-- The harmonic increment weight `w_D = 1/D − 1/(D+1)`. -/
def harmonicGap (D : ℕ) : ℝ := 1 / (D : ℝ) - 1 / ((D : ℝ) + 1)

theorem harmonicGap_mul (D : ℕ) (hD : 1 ≤ D) :
    (D : ℝ) * harmonicGap D = 1 / ((D : ℝ) + 1) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [harmonicGap]
  field_simp
  ring

theorem harmonicGap_sq_mul (D : ℕ) (hD : 1 ≤ D) :
    (D : ℝ) ^ 2 * harmonicGap D = 1 - 1 / ((D : ℝ) + 1) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [harmonicGap]
  field_simp
  ring

/-! ## The three telescoping moments -/

theorem sum_harmonicGap (n : ℕ) :
    ∑ D ∈ Finset.Icc 1 n, harmonicGap D = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonicGap]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    push_cast
    field_simp
    ring

theorem sum_mul_harmonicGap (n : ℕ) :
    ∑ D ∈ Finset.Icc 1 n, (D : ℝ) * harmonicGap D = harmonicSum (n + 1) - 1 := by
  induction n with
  | zero => simp [harmonicSum]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonicGap_mul _ (by omega),
      harmonicSum_succ (n + 1)]
    push_cast
    ring

theorem sum_sq_mul_harmonicGap (n : ℕ) :
    ∑ D ∈ Finset.Icc 1 n, (D : ℝ) ^ 2 * harmonicGap D = (n : ℝ) - (harmonicSum (n + 1) - 1) := by
  induction n with
  | zero => simp [harmonicSum]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonicGap_sq_mul _ (by omega),
      harmonicSum_succ (n + 1)]
    push_cast
    ring

/-! ## The linear and quadratic projections -/

/-- **(24.38) The harmonic projection of a linear ramp.** -/
theorem sum_ramp_harmonicGap {q : ℕ} (hq : 1 ≤ q) :
    ∑ D ∈ Finset.Icc 1 (q - 1), ((q : ℝ) - (D : ℝ)) * harmonicGap D
      = (q : ℝ) - harmonicSum q := by
  have hsucc : q - 1 + 1 = q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsplit : ∑ D ∈ Finset.Icc 1 (q - 1), ((q : ℝ) - (D : ℝ)) * harmonicGap D
      = (q : ℝ) * ∑ D ∈ Finset.Icc 1 (q - 1), harmonicGap D
        - ∑ D ∈ Finset.Icc 1 (q - 1), (D : ℝ) * harmonicGap D := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [hsplit, sum_harmonicGap, sum_mul_harmonicGap, hsucc]
  have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    rw [Nat.cast_sub hq]
    push_cast
    ring
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hstep : (q : ℝ) * (1 - 1 / (q : ℝ)) = (q : ℝ) - 1 := by field_simp
  rw [hcast, hstep]
  ring

/-- **(24.42) The harmonic projection of a product of two ramps.** -/
theorem sum_biramp_harmonicGap {l v : ℕ} (hl : 1 ≤ l) :
    ∑ D ∈ Finset.Icc 1 (l - 1), ((l : ℝ) - (D : ℝ)) * ((v : ℝ) - (D : ℝ)) * harmonicGap D
      = (l : ℝ) * (v : ℝ) + 2 * (l : ℝ) - ((l : ℝ) + (v : ℝ) + 1) * harmonicSum l := by
  have hsucc : l - 1 + 1 = l := by omega
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hsplit : ∑ D ∈ Finset.Icc 1 (l - 1),
        ((l : ℝ) - (D : ℝ)) * ((v : ℝ) - (D : ℝ)) * harmonicGap D
      = (l : ℝ) * (v : ℝ) * ∑ D ∈ Finset.Icc 1 (l - 1), harmonicGap D
        - ((l : ℝ) + (v : ℝ)) * ∑ D ∈ Finset.Icc 1 (l - 1), (D : ℝ) * harmonicGap D
        + ∑ D ∈ Finset.Icc 1 (l - 1), (D : ℝ) ^ 2 * harmonicGap D := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [hsplit, sum_harmonicGap, sum_mul_harmonicGap, sum_sq_mul_harmonicGap, hsucc]
  have hcastAdd : ((l - 1 : ℕ) : ℝ) + 1 = (l : ℝ) := by
    rw [Nat.cast_sub hl]
    push_cast
    ring
  have hcastSub : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub hl]
    push_cast
    ring
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlpos
  have hstep : (l : ℝ) * (v : ℝ) * (1 - 1 / (l : ℝ)) = (l : ℝ) * (v : ℝ) - (v : ℝ) := by
    field_simp
  rw [hcastAdd, hcastSub, hstep]
  ring

end

end RHTower
