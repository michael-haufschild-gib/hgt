import GaloisForLFunctions.RHTower.HarmonicPrimitiveLadder
import GaloisForLFunctions.RHTower.HarmonicTriangularProjection

/-!
# The harmonic primitive against the mass adjoint cell quotient

With the harmonic increment `w_n = 1/n − 1/(n+1)`, the harmonic primitive `J_N = ∑_{n ≤ N} R(n) w_n`
and the adjoint cell quotient `A_n = (K_n − K_{n+1})/w_n`, finite Abel summation turns the mass cell
current into

`S_N = J_N A_N − J_0 A_1 + ∑_{n < N} J_n (A_n − A_{n+1})`,

which replaces the unbounded remainder by the primitive before any norm is taken.  Subtracting the
limit of the primitive costs only the fixed boundary term `−2γ A_1`, because the constant part
telescopes exactly.

The primitive itself has an exact closed form: for the partial sums of any source `a`,

`J_N = ∑_{n ≤ N} a(n)/n − R(N)/(N+1)`,

which for `a = Λ − 1` is the Mertens combination `∑ Λ(n)/n − H_N − R(N)/(N+1)`.
-/

namespace RHTower

noncomputable section

/-! ## The three objects -/

/-- **(24.61)** The harmonic primitive of a source remainder. -/
def harmonicPrimitive (R : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, R n * harmonicGap n

/-- **(24.62)** The adjoint cell quotient of a receiver. -/
def adjointCellQuotient (K : ℕ → ℝ) (n : ℕ) : ℝ := (K n - K (n + 1)) / harmonicGap n

/-- The finite mass cell current. -/
def massCellCurrent (R K : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, R n * (K n - K (n + 1))

@[simp]
theorem harmonicPrimitive_zero (R : ℕ → ℝ) : harmonicPrimitive R 0 = 0 := by
  rw [harmonicPrimitive]
  simp

theorem harmonicGap_pos {n : ℕ} (hn : 1 ≤ n) : 0 < harmonicGap n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  rw [harmonicGap, sub_pos]
  exact one_div_lt_one_div_of_lt hnpos (by linarith)

theorem harmonicGap_ne_zero {n : ℕ} (hn : 1 ≤ n) : harmonicGap n ≠ 0 :=
  ne_of_gt (harmonicGap_pos hn)

theorem harmonicPrimitive_diff (R : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    harmonicPrimitive R n - harmonicPrimitive R (n - 1) = harmonicGap n * R n := by
  have hstep : n - 1 + 1 = n := by omega
  have hsplit : harmonicPrimitive R n = harmonicPrimitive R (n - 1) + R n * harmonicGap n := by
    rw [harmonicPrimitive, harmonicPrimitive, ← hstep, Finset.sum_Icc_succ_top (by omega)]
    rw [hstep]
  rw [hsplit]
  ring

/-! ## The exact Abel identity -/

/-- **(24.63) The exact harmonic-primitive form of the mass cell current.** -/
theorem massCellCurrent_abel (R K : ℕ → ℝ) (M : ℕ) :
    massCellCurrent R K (M + 1)
      = harmonicPrimitive R (M + 1) * adjointCellQuotient K (M + 1)
        - harmonicPrimitive R 0 * adjointCellQuotient K 1
        + ∑ n ∈ Finset.Icc 1 M, harmonicPrimitive R n *
            (adjointCellQuotient K n - adjointCellQuotient K (n + 1)) := by
  have hterm : ∀ n ∈ Finset.Icc 1 (M + 1),
      R n * (K n - K (n + 1))
        = (harmonicPrimitive R n - harmonicPrimitive R (n - 1)) * adjointCellQuotient K n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [harmonicPrimitive_diff R hn.1, adjointCellQuotient]
    field_simp [harmonicGap_ne_zero hn.1]
  rw [massCellCurrent, Finset.sum_congr rfl hterm, sum_telescope_abel]

/-- The adjoint quotient telescopes on the interior. -/
theorem sum_adjointCellQuotient_telescope (K : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (adjointCellQuotient K n - adjointCellQuotient K (n + 1))
      = adjointCellQuotient K 1 - adjointCellQuotient K (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- **(24.65) The centred harmonic-primitive form.**  Subtracting the limit of the primitive costs
only the fixed boundary term. -/
theorem massCellCurrent_centered (R K : ℕ → ℝ) (gam : ℝ) (M : ℕ) :
    massCellCurrent R K (M + 1)
      = -(2 * gam) * adjointCellQuotient K 1
        + (harmonicPrimitive R (M + 1) + 2 * gam) * adjointCellQuotient K (M + 1)
        + ∑ n ∈ Finset.Icc 1 M, (harmonicPrimitive R n + 2 * gam) *
            (adjointCellQuotient K n - adjointCellQuotient K (n + 1)) := by
  have habel := massCellCurrent_abel R K M
  have hsplit : ∑ n ∈ Finset.Icc 1 M, (harmonicPrimitive R n + 2 * gam) *
        (adjointCellQuotient K n - adjointCellQuotient K (n + 1))
      = (∑ n ∈ Finset.Icc 1 M, harmonicPrimitive R n *
          (adjointCellQuotient K n - adjointCellQuotient K (n + 1)))
        + 2 * gam * ∑ n ∈ Finset.Icc 1 M,
          (adjointCellQuotient K n - adjointCellQuotient K (n + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hsplit, sum_adjointCellQuotient_telescope, habel, harmonicPrimitive_zero]
  ring

/-! ## The closed form of the primitive -/

/-- **(24.64) The exact primitive identity.**  The harmonic primitive of the partial sums of a
source is the logarithmic source mean minus the endpoint quotient. -/
theorem harmonicPrimitive_sourcePartialSum (a : ℕ → ℝ) (N : ℕ) :
    harmonicPrimitive (sourcePartialSum a) N
      = (∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) - sourcePartialSum a N / ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    rw [harmonicPrimitive, sourcePartialSum]
    simp
  | succ N ih =>
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hstep : sourcePartialSum a (N + 1) = sourcePartialSum a N + a (N + 1) := by
      rw [sourcePartialSum, sourcePartialSum, Finset.sum_Icc_succ_top (by omega)]
    have hgap : harmonicGap (N + 1) = 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) := by
      rw [harmonicGap]
      push_cast
      ring_nf
    rw [harmonicPrimitive, Finset.sum_Icc_succ_top (by omega), ← harmonicPrimitive, ih,
      Finset.sum_Icc_succ_top (by omega), hgap, hstep]
    push_cast
    field_simp
    ring

end

end RHTower
