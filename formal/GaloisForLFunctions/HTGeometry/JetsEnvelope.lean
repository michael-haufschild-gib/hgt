import GaloisForLFunctions.HTGeometry.JetCoeffEnvelope

/-!
# All jet slots are envelope-dominated by one constant

Taking the maximum of the per-jet constants over the finitely many derivative slots, and enlarging
the constant once more so that the variable slot's single nonzero coefficient is covered, gives one
pair `(B, K)` dominating every slot of `formalJetsOver`:

`‖[X^n] (jets i)‖ ≤ K (n+1)^B · facEnv r 𝔞 n`   for every slot `i`.

This is the exact hypothesis of the truncated-remainder bound.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- **One envelope for all jet slots.** -/
theorem exists_jets_envelope (hyp : FactorialSlope a α Λ Cc c) (m : ℕ) :
    ∃ (B : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ (i : Fin (m + 2)) (n : ℕ),
      ‖PowerSeries.coeff n (formalJetsOver m (PowerSeries.mk a) i)‖
        ≤ K * ((n : ℝ) + 1) ^ B * facEnv α.re (slopeRatio α Λ) n := by
  classical
  have h𝔞 : 0 < slopeRatio α Λ := slopeRatio_pos hyp.lam_ne
  choose Bj Kj hKj hbound using fun j : Fin (m + 1) => exists_jet_coeff_envelope hyp (j : ℕ)
  set B : ℕ := Finset.univ.sup Bj with hB
  have hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  set K₀ : ℝ := Finset.univ.sup' hne Kj with hK₀
  set K : ℝ := max K₀ (1 / (2 ^ B * slopeRatio α Λ)) with hK
  have hK₀nn : 0 ≤ K₀ := le_trans (hKj 0) (Finset.le_sup' Kj (Finset.mem_univ 0))
  have hKnn : 0 ≤ K := le_trans hK₀nn (le_max_left _ _)
  refine ⟨B, K, hKnn, ?_⟩
  intro i n
  have hfacpos : 0 < facEnv α.re (slopeRatio α Λ) n := facEnv_pos (r := α.re) h𝔞 n
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  refine Fin.cases ?_ ?_ i
  · -- the variable slot
    rcases eq_or_ne n 1 with hn | hn
    · subst hn
      rw [formalJetsOver_zero, PowerSeries.coeff_X, if_pos rfl, norm_one]
      have hfac1 : facEnv α.re (slopeRatio α Λ) 1 = slopeRatio α Λ := by
        rw [facEnv]
        norm_num
      rw [hfac1]
      have hKle : 1 / (2 ^ B * slopeRatio α Λ) ≤ K := le_max_right _ _
      have hpos : (0 : ℝ) < 2 ^ B * slopeRatio α Λ := by positivity
      rw [div_le_iff₀ hpos] at hKle
      have hcast : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
      rw [hcast]
      linarith
    · rw [formalJetsOver_zero, PowerSeries.coeff_X, if_neg hn, norm_zero]
      positivity
  · -- the derivative slots
    intro j
    rw [formalJetsOver_succ]
    refine le_trans (hbound j n) ?_
    have hBj : Bj j ≤ B := Finset.le_sup (Finset.mem_univ j)
    have hKj' : Kj j ≤ K := le_trans (Finset.le_sup' Kj (Finset.mem_univ j)) (le_max_left _ _)
    have hpow : ((n : ℝ) + 1) ^ Bj j ≤ ((n : ℝ) + 1) ^ B := pow_le_pow_right₀ hbase hBj
    have hstep : Kj j * ((n : ℝ) + 1) ^ Bj j ≤ K * ((n : ℝ) + 1) ^ B := by
      have h1 : Kj j * ((n : ℝ) + 1) ^ Bj j ≤ Kj j * ((n : ℝ) + 1) ^ B :=
        mul_le_mul_of_nonneg_left hpow (hKj j)
      have h2 : Kj j * ((n : ℝ) + 1) ^ B ≤ K * ((n : ℝ) + 1) ^ B :=
        mul_le_mul_of_nonneg_right hKj' (by positivity)
      linarith
    exact mul_le_mul_of_nonneg_right hstep (le_of_lt hfacpos)

end

end GaloisForLFunctions.HTGeometry
