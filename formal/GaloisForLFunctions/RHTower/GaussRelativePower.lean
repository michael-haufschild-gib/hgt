import GaloisForLFunctions.RHTower.GaussRelativeIterate
import GaloisForLFunctions.RHTower.GaussIterateInner

/-!
# The relative form of equation (11) at every `m`

The telescope of `HTGeometry/OperatorPowerTelescope` writes the deviation of `R^m` from its model
on the constant vector as a sum of one-step deviations evaluated on the iterates of `R`, weighted
by powers of the *model*.  Pairing against the constant vector and moving the model powers onto
the left slot — they are self-adjoint — turns each summand into exactly the quantity the previous
module proves to vanish.

Since `⟪e_n, G^m e_n⟫ = σ_n^m ⟪1, R_n^m 1⟫` with the step scalar outside, the resulting `o(1)` is
the *relative* form of equation (11).
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-- Powers of the moving amplitude are self-adjoint. -/
theorem gaussMovingAmplitudeBlock_pow_inner {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) (t : ℕ)
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ f ((gaussMovingAmplitudeBlock hp δ ^ t) g) : ℂ)
      = inner ℂ ((gaussMovingAmplitudeBlock hp δ ^ t) f) g := by
  induction t generalizing f g with
  | zero => simp
  | succ t ih =>
      have h1 : ((gaussMovingAmplitudeBlock hp δ ^ (t + 1)) g)
          = (gaussMovingAmplitudeBlock hp δ ^ t) (gaussMovingAmplitudeBlock hp δ g) := by
        rw [pow_succ]
        rfl
      have h2 : ((gaussMovingAmplitudeBlock hp δ ^ (t + 1)) f)
          = gaussMovingAmplitudeBlock hp δ ((gaussMovingAmplitudeBlock hp δ ^ t) f) := by
        rw [pow_succ']
        rfl
      rw [h1, h2, ih f (gaussMovingAmplitudeBlock hp δ g),
        gaussMovingAmplitudeBlock_inner hp δ]

/-- **The telescope of the deviation, paired against the constant vector.** -/
theorem inner_gaussPrincipalStep_pow_sub_eq (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ) (r : ℕ) :
    (inner ℂ (fourierLp 2 (0 : ℤ))
        ((gaussPrincipalStepBlock hm k p hp n ^ r) (fourierLp 2 (0 : ℤ))) : ℂ) -
      inner ℂ (fourierLp 2 (0 : ℤ))
        ((gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) ^ r)
          (fourierLp 2 (0 : ℤ)))
      = ∑ i ∈ Finset.range r,
        inner ℂ ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) ^ (r - 1 - i))
          (fourierLp 2 (0 : ℤ)))
          (gaussPrincipalStepBlock hm k p hp n
              ((gaussPrincipalStepBlock hm k p hp n ^ i) (fourierLp 2 (0 : ℤ))) -
            gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
              ((gaussPrincipalStepBlock hm k p hp n ^ i) (fourierLp 2 (0 : ℤ)))) := by
  set X := gaussPrincipalStepBlock hm k p hp n with hX
  set Y := gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) with hY
  have htel := GaloisForLFunctions.HTGeometry.operator_pow_sub_eq_sum X Y r
    (fourierLp 2 (0 : ℤ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
  rw [← inner_sub_right, htel, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hY, gaussMovingAmplitudeBlock_pow_inner hp]
  rfl

/-! ## Equation (11), relative form -/

set_option maxHeartbeats 1000000 in
/-- **The `m`-fold principal step agrees with its model on the constant vector**, with no step
scalar in front. -/
theorem tendsto_inner_gaussPrincipalStep_pow_sub_amplitude (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) :
    Tendsto (fun I : ℕ =>
      ‖(inner ℂ (fourierLp 2 (0 : ℤ))
          ((gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (I : ℤ) ^ m)
            (fourierLp 2 (0 : ℤ))) : ℂ) -
        ((gaussAmplitudeSegment (p : ℝ) m
          (Int.fract (gaussSamplePhase m p (I : ℤ))) : ℝ) : ℂ)‖) atTop (nhds 0) := by
  have hm : 1 ≤ m := le_trans one_le_two hm2
  have hval : ∀ I : ℕ, (inner ℂ (fourierLp 2 (0 : ℤ))
      ((gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ m)
        (fourierLp 2 (0 : ℤ))) : ℂ)
      = ((gaussAmplitudeSegment (p : ℝ) m
        (Int.fract (gaussSamplePhase m p (I : ℤ))) : ℝ) : ℂ) := by
    intro I
    have hs0 : (0 : ℝ) ≤ Int.fract (gaussSamplePhase m p (I : ℤ)) := Int.fract_nonneg _
    have hs1 : Int.fract (gaussSamplePhase m p (I : ℤ)) < 1 := Int.fract_lt_one _
    have hδ : ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ))
        = ((Int.fract (gaussSamplePhase m p (I : ℤ)) : ℝ) : AddCircle (1 : ℝ)) :=
      (coe_fract_eq _).symm
    rw [hδ, inner_fourierLp_eq_fourierCoeff, fourierCoeff_gaussAmplitudeIterate_zero hp hs0 hs1 m]
  have hterm : ∀ i ∈ Finset.range m, Tendsto (fun I : ℕ =>
      ‖(inner ℂ ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ (m - 1 - i))
          (fourierLp 2 (0 : ℤ)))
        (gaussPrincipalStepBlock hm k p hp (I : ℤ)
            ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ i) (fourierLp 2 (0 : ℤ))) -
          gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ))
            ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ i) (fourierLp 2 (0 : ℤ)))) : ℂ)‖)
      atTop (nhds 0) := by
    intro i hi
    exact tendsto_norm_inner_gaussPrincipalStep_sub_iterate_zero hm2 k p hp i (m - 1 - i)
      (Finset.mem_range.mp hi)
  have hsum : Tendsto (fun I : ℕ => ∑ i ∈ Finset.range m,
      ‖(inner ℂ ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) ^ (m - 1 - i))
          (fourierLp 2 (0 : ℤ)))
        (gaussPrincipalStepBlock hm k p hp (I : ℤ)
            ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ i) (fourierLp 2 (0 : ℤ))) -
          gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ))
            ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ i) (fourierLp 2 (0 : ℤ)))) : ℂ)‖)
      atTop (nhds 0) := by
    have h0 := tendsto_finsetSum (Finset.range m) hterm
    simpa using h0
  refine squeeze_zero (fun I => norm_nonneg _) (fun I => ?_) hsum
  rw [← hval I, inner_gaussPrincipalStep_pow_sub_eq hm k p hp (I : ℤ) m]
  exact norm_sum_le _ _

/-- The diagonal of `G^r` is the step scalar times the diagonal of the principal step. -/
theorem inner_gaussQuasiInnerG_pow_eq (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0) (r : ℕ) :
    (inner ℂ (fourierLp 2 n) ((gaussQuasiInnerG hm k p ^ r) (fourierLp 2 n)) : ℂ)
      = ((((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) ^ r) *
        inner ℂ (fourierLp 2 (0 : ℤ))
          ((gaussPrincipalStepBlock hm k p hp n ^ r) (fourierLp 2 (0 : ℤ))) := by
  rw [← fourierMulBlock_fourierLp_zero n,
    gaussQuasiInnerG_pow_fourierMulBlock hm k p hp hn, inner_smul_right, fourierMulBlock_inner]

/-- **Equation (11), relative form, at every `m ≥ 2`.**  The deviation of `⟪e_n, G^m e_n⟫` from
`(p |d_n|²)^m A_m(δ_n)` is the main term times a factor that vanishes. -/
theorem tendsto_norm_inner_gaussQuasiInnerG_pow_sub_amplitude_div (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) :
    Tendsto (fun I : ℕ =>
      ‖(inner ℂ (fourierLp 2 ((I : ℤ)))
          ((gaussQuasiInnerG (le_trans one_le_two hm2) k p ^ m) (fourierLp 2 ((I : ℤ)))) : ℂ) -
        ((((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (I : ℤ)) *
              gaussSampleValue k p (I : ℤ))) ^ m) *
          ((gaussAmplitudeSegment (p : ℝ) m
            (Int.fract (gaussSamplePhase m p (I : ℤ))) : ℝ) : ℂ)‖ /
        ‖(((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (I : ℤ)) *
              gaussSampleValue k p (I : ℤ))) ^ m‖) atTop (nhds 0) := by
  have hm : 1 ≤ m := le_trans one_le_two hm2
  refine (tendsto_inner_gaussPrincipalStep_pow_sub_amplitude hm2 k p hp).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with I hI
  have hn : ((I : ℤ)) ≠ 0 := by
    have : 0 < I := hI
    omega
  set σ : ℂ := ((p : ℝ) : ℂ) *
    (starRingEnd ℂ (gaussSampleValue k p (I : ℤ)) * gaussSampleValue k p (I : ℤ)) with hσ
  have hσne : σ ≠ 0 := by
    have hd : gaussSampleValue k p (I : ℤ) ≠ 0 := gaussSampleValue_ne_zero hm k p hn
    have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
    have hpne : ((p : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hppos
    have hcd : starRingEnd ℂ (gaussSampleValue k p (I : ℤ)) ≠ 0 := by simpa using hd
    rw [hσ]
    exact mul_ne_zero hpne (mul_ne_zero hcd hd)
  rw [inner_gaussQuasiInnerG_pow_eq hm k p hp hn m, ← hσ, ← mul_sub, norm_mul]
  have hne : ‖σ ^ m‖ ≠ 0 := norm_ne_zero_iff.mpr (pow_ne_zero m hσne)
  rw [mul_comm, mul_div_assoc, div_self hne, mul_one]

end

end RHTower
