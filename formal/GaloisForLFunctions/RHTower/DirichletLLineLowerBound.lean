import GaloisForLFunctions.RHTower.DirichletLStripBounds

/-!
# A uniform lower bound on a vertical line

Far to the right the Dirichlet series is dominated by its first term.  Splitting off `n = 1` and
comparing the rest with `2^{2-σ} ∑ n^{-2}` shows that beyond an explicit abscissa the L-function
has modulus at least `1/2`, **uniformly in the imaginary part**.

Uniformity is the point: this is the value at the centre of the Borel–Carathéodory disc, which
travels up the vertical line, so a bound valid only along the real ray would be useless.  No
numerical estimate is involved — the tail is compared to itself at exponent `2`.
-/

open Complex
open scoped LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Uniform lower bound on a vertical line.**  Beyond an explicit abscissa the L-function has
modulus at least `1/2` on the whole line. -/
theorem exists_line_lower_bound (χ : DirichletCharacter ℂ N) :
    ∃ σ₀ : ℝ, 2 ≤ σ₀ ∧
      ∀ s : ℂ, σ₀ ≤ s.re → (1 : ℝ) / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  classical
  have hSsum : Summable fun n : ℕ => (((n : ℝ)) ^ (2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  set S : ℝ := ∑' n : ℕ, (((n : ℝ)) ^ (2 : ℝ))⁻¹ with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun n => by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max 2 (2 + Real.log (2 * (S + 1)) / Real.log 2), le_max_left _ _, fun s hs => ?_⟩
  have hσ2 : (2 : ℝ) ≤ s.re := le_trans (le_max_left _ _) hs
  have hσbig : 2 + Real.log (2 * (S + 1)) / Real.log 2 ≤ s.re := le_trans (le_max_right _ _) hs
  have hs1 : (1 : ℝ) < s.re := by linarith
  -- split off the first term
  set T : ℕ → ℂ := fun n => LSeries.term (↗χ) s n - (if n = 1 then (1 : ℂ) else 0) with hT
  have hmaj : ∀ n : ℕ, ‖T n‖ ≤ (2 : ℝ) ^ (2 - s.re) * (((n : ℝ)) ^ (2 : ℝ))⁻¹ := by
    intro n
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 - s.re) := Real.rpow_pos_of_pos (by norm_num) _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [hT, LSeries.term_zero]
    rcases eq_or_ne n 1 with rfl | hn1
    · have hT1 : T 1 = 0 := by
        rw [hT]
        simp
      rw [hT1, norm_zero]
      positivity
    · have hn2 : 2 ≤ n := by omega
      have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hTn : T n = LSeries.term (↗χ) s n := by rw [hT]; simp [hn1]
      rw [hTn, LSeries.term_of_ne_zero hn0, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0)]
      have hchi : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := norm_dirichletCharacter_le_one χ _
      have hsplit : ((n : ℝ)) ^ s.re = ((n : ℝ)) ^ (2 : ℝ) * ((n : ℝ)) ^ (s.re - 2) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      have hpowbig : (2 : ℝ) ^ (s.re - 2) ≤ ((n : ℝ)) ^ (s.re - 2) :=
        Real.rpow_le_rpow (by norm_num) hn2R (by linarith)
      have h2p : (0 : ℝ) < (2 : ℝ) ^ (s.re - 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hnp : (0 : ℝ) < ((n : ℝ)) ^ (2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      have hinv : (2 : ℝ) ^ (2 - s.re) = ((2 : ℝ) ^ (s.re - 2))⁻¹ := by
        rw [← Real.rpow_neg (by norm_num)]
        congr 1
        ring
      have hnσ : (0 : ℝ) < ((n : ℝ)) ^ s.re := Real.rpow_pos_of_pos hnpos _
      have hnp2 : (0 : ℝ) < ((n : ℝ)) ^ (s.re - 2) := Real.rpow_pos_of_pos hnpos _
      have step1 : ‖χ ((n : ℕ) : ZMod N)‖ / ((n : ℝ)) ^ s.re ≤ 1 / ((n : ℝ)) ^ s.re := by
        rw [div_le_div_iff₀ hnσ hnσ]
        nlinarith [hchi, hnσ]
      have step2 : 1 / ((n : ℝ)) ^ s.re
          = (((n : ℝ)) ^ (2 : ℝ))⁻¹ * (((n : ℝ)) ^ (s.re - 2))⁻¹ := by
        rw [hsplit]
        field_simp
      have step3 : (((n : ℝ)) ^ (s.re - 2))⁻¹ ≤ ((2 : ℝ) ^ (s.re - 2))⁻¹ :=
        (inv_le_inv₀ hnp2 h2p).mpr hpowbig
      calc ‖χ ((n : ℕ) : ZMod N)‖ / ((n : ℝ)) ^ s.re
          ≤ 1 / ((n : ℝ)) ^ s.re := step1
        _ = (((n : ℝ)) ^ (2 : ℝ))⁻¹ * (((n : ℝ)) ^ (s.re - 2))⁻¹ := step2
        _ ≤ (((n : ℝ)) ^ (2 : ℝ))⁻¹ * ((2 : ℝ) ^ (s.re - 2))⁻¹ :=
            mul_le_mul_of_nonneg_left step3 (by positivity)
        _ = (2 : ℝ) ^ (2 - s.re) * (((n : ℝ)) ^ (2 : ℝ))⁻¹ := by rw [hinv]; ring
  have hTsummable : Summable fun n : ℕ => ‖T n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmaj ?_
    exact hSsum.mul_left _
  have hTsum : Summable T := Summable.of_norm hTsummable
  have hδsummable : Summable fun n : ℕ => (if n = 1 then (1 : ℂ) else 0) := by
    refine summable_of_ne_finset_zero (s := ({1} : Finset ℕ)) ?_
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  have hLsummable : Summable fun n : ℕ => LSeries.term (↗χ) s n := by
    have : (fun n : ℕ => LSeries.term (↗χ) s n) = fun n => T n + (if n = 1 then (1 : ℂ) else 0) := by
      funext n; rw [hT]; ring
    rw [this]
    exact hTsum.add hδsummable
  have hsplit : ∑' n : ℕ, T n = DirichletCharacter.LFunction χ s - 1 := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1, LSeries, hT]
    rw [Summable.tsum_sub hLsummable hδsummable, tsum_ite_eq]
  -- the tail is small
  have htail : ‖DirichletCharacter.LFunction χ s - 1‖ ≤ (2 : ℝ) ^ (2 - s.re) * S := by
    rw [← hsplit]
    refine le_trans (norm_tsum_le_tsum_norm hTsummable) ?_
    have hle := Summable.tsum_le_tsum hmaj hTsummable (hSsum.mul_left _)
    rwa [tsum_mul_left] at hle
  have hsmall : (2 : ℝ) ^ (2 - s.re) * S ≤ 1 / 2 := by
    have hexp : (2 : ℝ) ^ (2 - s.re) ≤ 1 / (2 * (S + 1)) := by
      have hpos : (0 : ℝ) < 2 * (S + 1) := by linarith
      rw [show (2 : ℝ) ^ (2 - s.re) = Real.exp ((2 - s.re) * Real.log 2) by
        rw [Real.rpow_def_of_pos (by norm_num)]; ring]
      rw [le_div_iff₀ hpos, ← Real.exp_log hpos]
      rw [← Real.exp_add]
      refine Real.exp_le_one_iff.mpr ?_
      have hsub : Real.log (2 * (S + 1)) / Real.log 2 ≤ s.re - 2 := by linarith
      rw [div_le_iff₀ hlog2] at hsub
      nlinarith [hsub, hlog2]
    have hSp : (0 : ℝ) < 2 * (S + 1) := by linarith
    calc (2 : ℝ) ^ (2 - s.re) * S ≤ 1 / (2 * (S + 1)) * S :=
          mul_le_mul_of_nonneg_right hexp hSnn
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hSp (by norm_num)]
          nlinarith
  have hone : (1 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖
      + ‖DirichletCharacter.LFunction χ s - 1‖ := by
    have h := norm_sub_le (DirichletCharacter.LFunction χ s)
      (DirichletCharacter.LFunction χ s - 1)
    have h3 : DirichletCharacter.LFunction χ s - (DirichletCharacter.LFunction χ s - 1)
        = 1 := by ring
    rw [h3, norm_one] at h
    exact h
  linarith [hone, htail, hsmall]

end RHTower
