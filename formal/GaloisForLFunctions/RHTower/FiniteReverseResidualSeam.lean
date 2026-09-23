import GaloisForLFunctions.RHTower.FiniteTwoLevelMomentCarrier

/-!
# Integer-rank seam in a reverse residual moment carrier

The canonical reverse residual head changes its number of positive atoms
when the effective rank crosses an integer. At the crossing, the two
neighboring formulas give the same padded vector, not merely the same
first two moments. This is the algebraic seam needed to glue the residual
carrier continuously while sweeping a distinguished atom.
-/

namespace RHTower

noncomputable section

/-- Common large atom in a reverse head with `n-1` large atoms. -/
def reverseResidualLarge (A B : ℝ) (n : ℕ) : ℝ :=
  (A + twoLevelDeviation A B n) / n

/-- Exceptional small atom in a reverse head with `n-1` large atoms. -/
def reverseResidualSmall (A B : ℝ) (n : ℕ) : ℝ :=
  (A - ((n : ℝ) - 1) * twoLevelDeviation A B n) / n

/-- At integer residual rank `k`, the `k`-atom branch has `k` equal atoms
`A/k`; the `(k+1)`-atom branch has the same `k` atoms and one zero. -/
theorem reverseResidual_integerRank_seam
    {A : ℝ} {k : ℕ} (hA : 0 < A) (hk : 2 ≤ k) :
    twoLevelDeviation A (A ^ (2 : ℕ) / k) k = 0 ∧
    twoLevelDeviation A (A ^ (2 : ℕ) / k) (k + 1) = A / k ∧
    reverseResidualLarge A (A ^ (2 : ℕ) / k) k = A / k ∧
    reverseResidualSmall A (A ^ (2 : ℕ) / k) k = A / k ∧
    reverseResidualLarge A (A ^ (2 : ℕ) / k) (k + 1) = A / k ∧
    reverseResidualSmall A (A ^ (2 : ℕ) / k) (k + 1) = 0 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0' : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hk1cast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hnum : (k : ℝ) * (A ^ (2 : ℕ) / k) - A ^ (2 : ℕ) = 0 := by
    field_simp [hk0']
    ring
  have hd0 : twoLevelDeviation A (A ^ (2 : ℕ) / k) k = 0 := by
    unfold twoLevelDeviation
    rw [hnum, zero_div, Real.sqrt_zero]
  have hrad :
      ((((k + 1 : ℕ) : ℝ) * (A ^ (2 : ℕ) / k) - A ^ (2 : ℕ)) /
        (((k + 1 : ℕ) : ℝ) - 1)) = (A / k) ^ (2 : ℕ) := by
    rw [hk1cast]
    field_simp [hk0']
    ring
  have hd1 : twoLevelDeviation A (A ^ (2 : ℕ) / k) (k + 1) = A / k := by
    unfold twoLevelDeviation
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hA hk0)]
  refine ⟨hd0, hd1, ?_, ?_, ?_, ?_⟩
  · unfold reverseResidualLarge
    rw [hd0]
    ring
  · unfold reverseResidualSmall
    rw [hd0]
    ring
  · unfold reverseResidualLarge
    rw [hd1, hk1cast]
    field_simp [hk0']
  · unfold reverseResidualSmall
    rw [hd1, hk1cast]
    field_simp [hk0']
    ring

/-- The reverse-head Hankel defect is at most `4/(27k)` of the squared
second moment. The sharp cubic factor is
`4a³ - 27b(a-b)² = (3b-a)²(4a-3b)`. -/
theorem reverseResidual_hankelGap_le_four_over_twentySeven
    {a b F k : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a)
    (hba : b ≤ a) (hF : F = k * a ^ (2 : ℕ) + b ^ (2 : ℕ)) :
    27 * k * (k * a * b * (a - b) ^ (2 : ℕ)) ≤
      4 * F ^ (2 : ℕ) := by
  have hfactor :
      0 ≤ (3 * b - a) ^ (2 : ℕ) * (4 * a - 3 * b) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hid :
      4 * a ^ (3 : ℕ) - 27 * b * (a - b) ^ (2 : ℕ) =
        (3 * b - a) ^ (2 : ℕ) * (4 * a - 3 * b) := by
    ring
  have hlocal : 27 * b * (a - b) ^ (2 : ℕ) ≤ 4 * a ^ (3 : ℕ) := by
    linarith
  have hscale : 0 ≤ k ^ (2 : ℕ) * a := mul_nonneg (sq_nonneg _) ha
  have hscaled := mul_le_mul_of_nonneg_right hlocal hscale
  have hFge : k * a ^ (2 : ℕ) ≤ F := by
    rw [hF]
    exact le_add_of_nonneg_right (sq_nonneg b)
  have hFsq : (k * a ^ (2 : ℕ)) ^ (2 : ℕ) ≤ F ^ (2 : ℕ) := by
    apply (sq_le_sq₀ (mul_nonneg hk (sq_nonneg a)) ?_).mpr hFge
    rw [hF]
    exact add_nonneg (mul_nonneg hk (sq_nonneg a)) (sq_nonneg b)
  calc
    27 * k * (k * a * b * (a - b) ^ (2 : ℕ)) =
        (27 * b * (a - b) ^ (2 : ℕ)) * (k ^ (2 : ℕ) * a) := by ring
    _ ≤ (4 * a ^ (3 : ℕ)) * (k ^ (2 : ℕ) * a) := hscaled
    _ = 4 * (k * a ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ ≤ 4 * F ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hFsq (by norm_num)

/-- For a reverse head of at least ten atoms, a `247/243` strengthening
of the source Hankel inequality suffices for the sixth-moment lower bracket. -/
theorem reverseResidual_lowerBracket_of_strongHankel
    {E F G a b k : ℝ} (hk : 9 ≤ k) (hE : 0 < E)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : k * a + b = E)
    (hsecond : k * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F)
    (hstrong : 247 * F ^ (2 : ℕ) ≤ 243 * E * G) :
    k * a ^ (3 : ℕ) + b ^ (3 : ℕ) ≤ G := by
  let D := k * a * b * (a - b) ^ (2 : ℕ)
  have hk0 : 0 ≤ k := by linarith
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  have hbound : 27 * k * D ≤ 4 * F ^ (2 : ℕ) := by
    simpa only [D] using
      reverseResidual_hankelGap_le_four_over_twentySeven hk0 ha hba hsecond.symm
  have hcount : 9 * (27 * D) ≤ k * (27 * D) :=
    mul_le_mul_of_nonneg_right hk (by positivity)
  have hDsharp : 243 * D ≤ 4 * F ^ (2 : ℕ) := by
    nlinarith [hbound, hcount]
  have hidentity :
      E * (k * a ^ (3 : ℕ) + b ^ (3 : ℕ)) - F ^ (2 : ℕ) = D := by
    rw [← hfirst, ← hsecond]
    dsimp [D]
    ring
  have hcompare : E * (k * a ^ (3 : ℕ) + b ^ (3 : ℕ)) ≤ E * G := by
    nlinarith [hDsharp, hstrong, hidentity]
  by_contra hnot
  have hlt : G < k * a ^ (3 : ℕ) + b ^ (3 : ℕ) := lt_of_not_ge hnot
  have hpositive : 0 < E * (k * a ^ (3 : ℕ) + b ^ (3 : ℕ) - G) :=
    mul_pos hE (sub_pos.mpr hlt)
  nlinarith

end

end RHTower
