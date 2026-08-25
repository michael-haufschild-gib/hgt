import GaloisForLFunctions.HTGeometry.IndexedDiagonalApproximation
import GaloisForLFunctions.RHTower.ApproximationNumberUnitary
import GaloisForLFunctions.RHTower.WeakSchattenResidue

/-!
# Weak Schatten membership for enumerated indexed diagonals

A critical power bound on an arbitrarily enumerated diagonal symbol gives weak Schatten membership.
The proof truncates the first `n` coordinates, uses the exact rank bound of that truncation, and
controls the omitted multiplier by taking the positive `P`-th root of its power bound.
-/

namespace RHTower

open HTGeometry

noncomputable section

/-- Weak Schatten membership is invariant under unitary transport. -/
theorem MemWeakSchattenClass.unitaryPush
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {P : ℝ} {T : H →L[ℂ] H} (hT : MemWeakSchattenClass P T)
    (u : H ≃ₗᵢ[ℂ] K) : MemWeakSchattenClass P (RHTower.unitaryPush u T) := by
  obtain ⟨C, hC, hbound⟩ := hT
  exact ⟨C, hC, fun n => by rw [approxNumber_unitaryPush]; exact hbound n⟩

/-- Logarithmic Schatten residues are invariant under unitary transport. -/
theorem HasSchattenLogResidue.unitaryPush
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {P R : ℝ} {T : H →L[ℂ] H} (hT : HasSchattenLogResidue P T R)
    (u : H ≃ₗᵢ[ℂ] K) : HasSchattenLogResidue P (RHTower.unitaryPush u T) R := by
  simpa [HasSchattenLogResidue, schattenPowerPartialSum, approxNumber_unitaryPush] using hT

/-- An enumerated `P`-power decay bound on a bounded diagonal symbol places its diagonal operator
in weak Schatten class `S_{P,∞}`. -/
theorem memWeakSchattenClass_ellTwoDiagonal_of_reindex_pow_le
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ)
    {lam : κ → ℂ} {M : ℝ} (hM : ∀ i, ‖lam i‖ ≤ M)
    {P : ℕ} (hP : 0 < P) {C : ℝ} (hC0 : 0 ≤ C)
    (hdecay : ∀ n : ℕ, ‖lam (e n)‖ ^ P ≤ C / ((n : ℝ) + 1)) :
    MemWeakSchattenClass (P : ℝ) (ellTwoDiagonal lam hM) := by
  refine ⟨C, hC0, fun n => ?_⟩
  let b : ℝ := C / ((n : ℝ) + 1)
  have hb0 : 0 ≤ b := div_nonneg hC0 (by positivity)
  let r : ℝ := b ^ ((P : ℝ)⁻¹)
  have hPℝ : 0 < (P : ℝ) := by exact_mod_cast hP
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0 _
  let F := ellTwoDiagonal (equivTruncMultiplier e lam n)
    (norm_equivTruncMultiplier_le e hM n)
  let tail : κ → ℂ := fun i => if n ≤ e.symm i then lam i else 0
  have htail : ∀ i, ‖tail i‖ ≤ r := by
    intro i
    dsimp [tail]
    split_ifs with hi
    · have hpow := hdecay (e.symm i)
      rw [e.apply_symm_apply] at hpow
      have hquot : C / (((e.symm i : ℕ) : ℝ) + 1) ≤ b := by
        dsimp [b]
        gcongr
      have hpowb : ‖lam i‖ ^ P ≤ b := hpow.trans hquot
      have hpowb' : ‖lam i‖ ^ (P : ℝ) ≤ b := by
        rwa [Real.rpow_natCast]
      have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg (lam i)) (P : ℝ))
        hpowb' (le_of_lt (inv_pos.mpr hPℝ))
      dsimp [r]
      rw [← Real.rpow_mul (norm_nonneg (lam i)),
        mul_inv_cancel₀ (ne_of_gt hPℝ), Real.rpow_one] at hroot
      exact hroot
    · simpa using hr0
  have hsub : ellTwoDiagonal lam hM - F = ellTwoDiagonal tail htail := by
    ext f i
    change lam i * f i - equivTruncMultiplier e lam n i * f i = tail i * f i
    dsimp [tail, equivTruncMultiplier]
    by_cases hi : e.symm i < n
    · simp [hi, Nat.not_le.mpr hi]
    · simp [hi, Nat.le_of_not_gt hi]
  have ha : approxNumber (ellTwoDiagonal lam hM) n ≤ r := by
    calc
      approxNumber (ellTwoDiagonal lam hM) n ≤ ‖ellTwoDiagonal lam hM - F‖ :=
        approxNumber_le _ _ _ (hasRankLE_ellTwoDiagonal_equivTrunc e lam hM n)
      _ = ‖ellTwoDiagonal tail htail‖ := by rw [hsub]
      _ ≤ r := norm_ellTwoDiagonal_le tail htail hr0
  calc
    approxNumber (ellTwoDiagonal lam hM) n ^ (P : ℝ) ≤ r ^ (P : ℝ) :=
      Real.rpow_le_rpow (approxNumber_nonneg _ _) ha (by positivity)
    _ = b := by
      dsimp [r]
      rw [← Real.rpow_mul hb0, inv_mul_cancel₀ (ne_of_gt hPℝ), Real.rpow_one]
    _ = C / ((n : ℝ) + 1) := rfl

end

end RHTower
