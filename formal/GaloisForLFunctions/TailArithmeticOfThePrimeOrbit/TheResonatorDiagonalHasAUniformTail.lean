import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheDivisorBoundControlsResonatorEnergy

/-!
# Uniform removal of the coefficient cutoff

The full coefficient energy and its complementary tail are controlled by
the same divisor majorant. Balancing the square-norm perturbation at the
square root of the tail's power gives a uniform diagonal error.
-/

noncomputable section
open Real Finset Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

private theorem abs_tsum_norm_sq_sub_le_split {f g : ℕ → ℂ}
    (hf : Summable (fun k => ‖f k‖ ^ 2)) (hg : Summable (fun k => ‖g k‖ ^ 2))
    (hfg : Summable (fun k => ‖f k - g k‖ ^ 2)) {δ : ℝ} (hδ : 0 < δ) :
    |(∑' k : ℕ, ‖f k‖ ^ 2) - ∑' k : ℕ, ‖g k‖ ^ 2| ≤
      δ * (∑' k : ℕ, ‖g k‖ ^ 2) + (1 + δ⁻¹) * ∑' k : ℕ, ‖f k - g k‖ ^ 2 := by
  have hb := (hg.mul_left δ).add (hfg.mul_left (1 + δ⁻¹))
  have heq : (∑' k : ℕ, δ * ‖g k‖ ^ 2 + (1 + δ⁻¹) * ‖f k - g k‖ ^ 2) =
      δ * (∑' k : ℕ, ‖g k‖ ^ 2) + (1 + δ⁻¹) * ∑' k : ℕ, ‖f k - g k‖ ^ 2 := by
    rw [(hg.mul_left δ).tsum_add (hfg.mul_left (1 + δ⁻¹)), tsum_mul_left, tsum_mul_left]
  have hu := Summable.tsum_le_tsum
    (fun k => (abs_le.mp (abs_norm_sq_sub_le_split (f k) (g k) hδ)).2) (hf.sub hg) hb
  have hl := Summable.tsum_le_tsum (fun k => show ‖g k‖ ^ 2 - ‖f k‖ ^ 2 ≤
      δ * ‖g k‖ ^ 2 + (1 + δ⁻¹) * ‖f k - g k‖ ^ 2 from by
        have h := (abs_le.mp (abs_norm_sq_sub_le_split (f k) (g k) hδ)).1
        linarith only [h]) (hg.sub hf) hb
  rw [hf.tsum_sub hg, heq] at hu
  rw [hg.tsum_sub hf, heq] at hl
  exact abs_le.mpr ⟨by linarith only [hl], hu⟩

/-- The diagonal discrepancy is bounded by a full energy and a complementary tail. -/
theorem abs_resonator_diagonal_sub_trunc_le_split {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0)
    (r : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    |(∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2) -
      ∑' k : ℕ, ‖truncResonatorCoeff A r σ N k‖ ^ 2| ≤
        Sieve.divisorBoundConst ε * (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
          (δ * (∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)) +
            (1 + δ⁻¹) * ((N : ℝ) ^ (1 + ε - 2 * σ) / (2 * σ - ε - 1))) := by
  have hf : Summable (fun k : ℕ => ‖resonatorCoeff A r σ k‖ ^ 2) := by
    simpa only [resonatorCoeff, and_true] using
      (summable_resonator_slice_sq_and_bound hε hεσ hA r (fun _ => True)).1
  have hg : Summable (fun k : ℕ => ‖truncResonatorCoeff A r σ N k‖ ^ 2) :=
    (summable_resonator_slice_sq_and_bound hε hεσ hA r (fun n => n ≤ N)).1
  have htail : Summable (fun k : ℕ =>
      ‖truncResonatorCoeff A r σ N k - resonatorCoeff A r σ k‖ ^ 2) := by
    simpa only [norm_sub_rev, resonatorCoeff_sub_trunc] using
      (summable_resonator_slice_sq_and_bound hε hεσ hA r (fun n => N < n)).1
  have h := abs_tsum_norm_sq_sub_le_split hg hf htail hδ
  rw [abs_sub_comm] at h
  simp_rw [norm_sub_rev] at h
  apply h.trans
  calc
    _ ≤ δ * (Sieve.divisorBoundConst ε *
        (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) * ∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)) +
      (1 + δ⁻¹) * (Sieve.divisorBoundConst ε *
        (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
          ((N : ℝ) ^ (1 + ε - 2 * σ) / (2 * σ - ε - 1))) :=
      add_le_add (mul_le_mul_of_nonneg_left (tsum_norm_resonatorCoeff_sq_le hε hεσ hA r) hδ.le)
        (mul_le_mul_of_nonneg_left
          (tsum_norm_resonatorCoeff_sub_trunc_sq_le hε hεσ hA r hN) (by positivity))
    _ = _ := by ring

/-- A square-root balance gives the uniform power rate for the diagonal itself. -/
theorem abs_resonator_diagonal_sub_trunc_le_power {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0)
    (r : ℕ → ℂ) {M : ℕ} (hM : ∀ m ∈ A, m ≤ M) {N : ℕ} (hN : 1 ≤ N) :
    |(∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2) -
      ∑' k : ℕ, ‖truncResonatorCoeff A r σ N k‖ ^ 2| ≤
        (Sieve.divisorBoundConst ε *
          ((∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)) + 2 / (2 * σ - ε - 1)) *
            ((M : ℝ) ^ ε * (N : ℝ) ^ ((1 + ε - 2 * σ) / 2))) *
              ∑ m ∈ A, ‖r m‖ ^ 2 := by
  let δ := (N : ℝ) ^ ((1 + ε - 2 * σ) / 2)
  have hNR : (1 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN0 _
  have hδ1 : δ ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
      (by norm_num : (0 : ℝ) < 1) hNR
      (by linarith only [hεσ] : (1 + ε - 2 * σ) / 2 ≤ 0)
  have hδsq : (N : ℝ) ^ (1 + ε - 2 * σ) = δ ^ 2 := by
    dsimp [δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    norm_num <;> ring
  have hden : 0 < 2 * σ - ε - 1 := by linarith only [hεσ]
  have htail : (1 + δ⁻¹) * ((N : ℝ) ^ (1 + ε - 2 * σ) / (2 * σ - ε - 1)) ≤
      δ * (2 / (2 * σ - ε - 1)) := by
    rw [hδsq]
    calc
      _ = δ * ((δ + 1) / (2 * σ - ε - 1)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith only [hδ1]) hden.le) hδ.le
  have hP : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hC : 0 ≤ (∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)) + 2 / (2 * σ - ε - 1) := by
    positivity
  have hw := sum_resonator_weighted_energy_le hε.le hM r
  apply (abs_resonator_diagonal_sub_trunc_le_split hε hεσ hA r hN hδ).trans
  calc
    _ ≤ Sieve.divisorBoundConst ε * (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
        (δ * ((∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)) + 2 / (2 * σ - ε - 1))) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Sieve.divisorBoundConst_pos hε).le (by positivity))
      nlinarith only [htail]
    _ ≤ Sieve.divisorBoundConst ε * ((M : ℝ) ^ ε * ∑ m ∈ A, ‖r m‖ ^ 2) *
        (δ * ((∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)) + 2 / (2 * σ - ε - 1))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw (Sieve.divisorBoundConst_pos hε).le) (mul_nonneg hδ.le hC)
    _ = _ := by ring

#print axioms abs_resonator_diagonal_sub_trunc_le_power

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
