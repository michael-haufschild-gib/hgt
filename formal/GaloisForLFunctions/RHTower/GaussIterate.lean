import GaloisForLFunctions.RHTower.GaussIteratedAmplitude

/-!
# The iterated principal action

Iterating the one-step estimate `r` times gives

`‖G^r(e_n) - (p |d_n|²)^r e_n a_(δ_n)^r‖ → 0`.

The induction closes because two quantities stay bounded along it: the operator `G` itself, whose
norm multiplies the accumulated error at each step, and the step scalar `p |d_n|²`, whose `r`-th
power multiplies the new error.  The two decay constants of the one-step estimate are supplied at
every stage by the iterated amplitude, whose partition never refines.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

theorem norm_gaussStepScalar_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ) :
    ‖((p : ℝ) : ℂ) * (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)‖
      ≤ (p : ℝ) * (gaussSampleValueBound hm k p * gaussSampleValueBound hm k p) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have hd := norm_gaussSampleValue_le hm k p n
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos,
    RCLike.norm_conj]
  refine mul_le_mul_of_nonneg_left ?_ hppos.le
  exact mul_le_mul hd hd (norm_nonneg _) (gaussSampleValueBound_nonneg hm k p)

/-- **The iterated principal action.**  `G^r` acts on the twisted constant function as the `r`-th
power of the step scalar times the `r`-th power of the moving amplitude, up to a vanishing `L²`
error. -/
theorem tendsto_gaussIterate {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) (r : ℕ) :
    Tendsto (fun n : ℕ =>
      ‖(gaussQuasiInnerG hm k p ^ r) (fourierMulBlock (ι n) (fourierLp 2 0)) -
        ((((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (ι n)) * gaussSampleValue k p (ι n))) ^ r) •
          fourierMulBlock (ι n)
            ((gaussMovingAmplitudeBlock hp
              ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r)
                (fourierLp 2 0))‖)
      atTop (nhds 0) := by
  induction r with
  | zero =>
      have hz : ∀ n : ℕ,
          ‖(gaussQuasiInnerG hm k p ^ (0 : ℕ)) (fourierMulBlock (ι n) (fourierLp 2 0)) -
            ((((p : ℝ) : ℂ) *
                (starRingEnd ℂ (gaussSampleValue k p (ι n)) *
                  gaussSampleValue k p (ι n))) ^ (0 : ℕ)) •
              fourierMulBlock (ι n)
                ((gaussMovingAmplitudeBlock hp
                  ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ (0 : ℕ))
                    (fourierLp 2 0))‖ = 0 := by
        intro n
        have h1 : (gaussQuasiInnerG hm k p ^ (0 : ℕ)) (fourierMulBlock (ι n) (fourierLp 2 0))
            = fourierMulBlock (ι n) (fourierLp 2 0) := by
          rw [pow_zero]
          rfl
        have h2 : (gaussMovingAmplitudeBlock hp
              ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ (0 : ℕ)) (fourierLp 2 0)
            = (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
          rw [pow_zero]
          rfl
        rw [h1, h2, pow_zero, one_smul, sub_self, norm_zero]
      exact (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop)).congr fun n => (hz n).symm
  | succ r ih =>
      have hM := gaussSampleValueBound_nonneg hm k p
      have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
      -- the two decay constants of the one-step estimate at this stage
      have h1 : ∀ (n : ℕ) (j : ℤ),
          ‖fourierCoeff ((gaussPrimeScaleBlock hp
              ((gaussMovingAmplitudeBlock hp
                ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r)
                  (fourierLp 2 0)) : AddCircle (1 : ℝ) → ℂ)) j‖
            ≤ 4 * (p : ℝ) ^ (r + 1) / (1 + (j.natAbs : ℝ)) := by
        intro n j
        have hb := norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow hp
          (Int.fract_nonneg (gaussSamplePhase m p (ι n)))
          (Int.fract_lt_one (gaussSamplePhase m p (ι n))) r j
        rwa [coe_fract_eq] at hb
      have h2 : ∀ (n : ℕ) (j : ℤ),
          ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
              (gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
                (gaussPrimeScaleBlock hp
                  ((gaussMovingAmplitudeBlock hp
                    ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r)
                      (fourierLp 2 0)))) : AddCircle (1 : ℝ) → ℂ)) j‖
            ≤ 4 * (p : ℝ) ^ (r + 1) / (1 + (j.natAbs : ℝ)) := by
        intro n j
        have hb := norm_fourierCoeff_gaussIntermediate_amplitudePow hp
          (Int.fract_nonneg (gaussSamplePhase m p (ι n)))
          (Int.fract_lt_one (gaussSamplePhase m p (ι n))) r j
        rwa [coe_fract_eq] at hb
      have hstep := tendsto_gaussOneStep_family hm k p hp hι
        (fun n : ℕ => (gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r) (fourierLp 2 0))
        h1 h2
      have hdom : Tendsto (fun n : ℕ =>
          ‖gaussQuasiInnerG hm k p‖ *
              ‖(gaussQuasiInnerG hm k p ^ r) (fourierMulBlock (ι n) (fourierLp 2 0)) -
                ((((p : ℝ) : ℂ) *
                    (starRingEnd ℂ (gaussSampleValue k p (ι n)) *
                      gaussSampleValue k p (ι n))) ^ r) •
                  fourierMulBlock (ι n)
                    ((gaussMovingAmplitudeBlock hp
                      ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r)
                        (fourierLp 2 0))‖ +
            ((p : ℝ) * (gaussSampleValueBound hm k p * gaussSampleValueBound hm k p)) ^ r *
              ‖gaussQuasiInnerG hm k p (fourierMulBlock (ι n)
                  ((gaussMovingAmplitudeBlock hp
                    ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r)
                      (fourierLp 2 0))) -
                (((p : ℝ) : ℂ) *
                    (starRingEnd ℂ (gaussSampleValue k p (ι n)) *
                      gaussSampleValue k p (ι n))) •
                  fourierMulBlock (ι n)
                    (gaussMovingAmplitudeBlock hp
                      ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
                        ((gaussMovingAmplitudeBlock hp
                          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ r)
                            (fourierLp 2 0)))‖) atTop (nhds 0) := by
        have hsum := (ih.const_mul ‖gaussQuasiInnerG hm k p‖).add
          (hstep.const_mul
            (((p : ℝ) * (gaussSampleValueBound hm k p * gaussSampleValueBound hm k p)) ^ r))
        simpa using hsum
      refine squeeze_zero_norm' ?_ hdom
      filter_upwards with n
      set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
        with hδ
      set σ : ℂ := ((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p (ι n)) * gaussSampleValue k p (ι n)) with hσ
      set g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
        (gaussMovingAmplitudeBlock hp δ ^ r) (fourierLp 2 0) with hg
      set X : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
        (gaussQuasiInnerG hm k p ^ r) (fourierMulBlock (ι n) (fourierLp 2 0)) with hX
      set Y : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
        (σ ^ r) • fourierMulBlock (ι n) g with hY
      have hGX : (gaussQuasiInnerG hm k p ^ (r + 1)) (fourierMulBlock (ι n) (fourierLp 2 0))
          = gaussQuasiInnerG hm k p X := by
        rw [hX, pow_succ']
        rfl
      have hAg : (gaussMovingAmplitudeBlock hp δ ^ (r + 1)) (fourierLp 2 0)
          = gaussMovingAmplitudeBlock hp δ g := by
        rw [hg, pow_succ']
        rfl
      have hsplit :
          (gaussQuasiInnerG hm k p ^ (r + 1)) (fourierMulBlock (ι n) (fourierLp 2 0)) -
              (σ ^ (r + 1)) •
                fourierMulBlock (ι n)
                  ((gaussMovingAmplitudeBlock hp δ ^ (r + 1)) (fourierLp 2 0))
            = gaussQuasiInnerG hm k p (X - Y) +
              (σ ^ r) • (gaussQuasiInnerG hm k p (fourierMulBlock (ι n) g) -
                σ • fourierMulBlock (ι n) (gaussMovingAmplitudeBlock hp δ g)) := by
        rw [hGX, hAg, hY, map_sub, map_smul, smul_sub, smul_smul, ← pow_succ]
        abel
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hsplit]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((gaussQuasiInnerG hm k p).le_opNorm _) ?_
      rw [norm_smul, norm_pow]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gaussStepScalar_le hm k p (ι n)) r

end

end RHTower
