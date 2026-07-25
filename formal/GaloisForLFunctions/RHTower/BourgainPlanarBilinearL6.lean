/-
# Factorized planar bilinear `L⁶` estimate

The local model in Bourgain's equation (2.7) contains two independent
parabola sums, each in its own pair of periodic variables.  Fubini
factorization reduces the four-variable product moment to the product of two
two-torus sixth moments.  The arithmetic parabola estimate then gives the
required subpower loss.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaTwoTorusL6

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sixth moment of one discrete parabola sum. -/
def bourgainParabolaL6Moment
    (H : ℕ) (a : Fin H → ℂ) : ℝ :=
  Real.circleAverage
    (fun v =>
      Real.circleAverage
        (fun u => ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
        0 1)
    0 1

/-- Product sixth moment of two independent discrete parabola sums. -/
def bourgainIndependentPlanarBilinearMoment
    (H₁ H₂ : ℕ) (a : Fin H₁ → ℂ) (b : Fin H₂ → ℂ) : ℝ :=
  Real.circleAverage
    (fun v₂ =>
      Real.circleAverage
        (fun u₂ =>
          Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
                    ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
                0 1)
            0 1)
        0 1)
    0 1

/-- Exact Fubini factorization of the independent four-torus moment. -/
theorem bourgainIndependentPlanarBilinearMoment_eq_mul
    (H₁ H₂ : ℕ) (a : Fin H₁ → ℂ) (b : Fin H₂ → ℂ) :
    bourgainIndependentPlanarBilinearMoment H₁ H₂ a b =
      bourgainParabolaL6Moment H₁ a *
        bourgainParabolaL6Moment H₂ b := by
  unfold bourgainIndependentPlanarBilinearMoment
    bourgainParabolaL6Moment
  have hinner (u₂ v₂ v₁ : ℂ) :
      Real.circleAverage
          (fun u₁ =>
            ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
              ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
          0 1 =
        ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
          Real.circleAverage
            (fun u₁ =>
              ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
            0 1 := by
    rw [show
      (fun u₁ =>
        ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
          ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ)) =
      (fun u₁ =>
        ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
          ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ)) by
        funext u₁
        ring]
    simpa [smul_eq_mul] using
      (Real.circleAverage_fun_smul
        (a := ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
        (f := fun u₁ =>
          ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
        (c := 0) (R := 1))
  have hfirst (u₂ v₂ : ℂ) :
      Real.circleAverage
          (fun v₁ =>
            Real.circleAverage
              (fun u₁ =>
                ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
                  ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
              0 1)
          0 1 =
        ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
          Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
                0 1)
            0 1 := by
    rw [show
      (fun v₁ =>
        Real.circleAverage
          (fun u₁ =>
            ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
              ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
          0 1) =
      (fun v₁ =>
        ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
          Real.circleAverage
            (fun u₁ =>
              ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
            0 1) by
        funext v₁
        exact hinner u₂ v₂ v₁]
    simpa [smul_eq_mul] using
      (Real.circleAverage_fun_smul
        (a := ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
        (f := fun v₁ =>
          Real.circleAverage
            (fun u₁ =>
              ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
            0 1)
        (c := 0) (R := 1))
  have hsecond (v₂ : ℂ) :
      Real.circleAverage
          (fun u₂ =>
            ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
              Real.circleAverage
                (fun v₁ =>
                  Real.circleAverage
                    (fun u₁ =>
                      ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
                    0 1)
                0 1)
          0 1 =
        Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
                0 1)
            0 1 *
          Real.circleAverage
            (fun u₂ =>
              ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
            0 1 := by
    rw [show
      (fun u₂ =>
        ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
          Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
                0 1)
            0 1) =
      (fun u₂ =>
        Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
                0 1)
            0 1 *
          ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ)) by
        funext u₂
        ring]
    simpa [smul_eq_mul] using
      (Real.circleAverage_fun_smul
        (a := Real.circleAverage
          (fun v₁ =>
            Real.circleAverage
              (fun u₁ =>
                ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
              0 1)
          0 1)
        (f := fun u₂ =>
          ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
        (c := 0) (R := 1))
  rw [show
    (fun v₂ =>
      Real.circleAverage
        (fun u₂ =>
          Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
                    ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
                0 1)
            0 1)
        0 1) =
    (fun v₂ =>
      Real.circleAverage
          (fun v₁ =>
            Real.circleAverage
              (fun u₁ =>
                ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
              0 1)
          0 1 *
        Real.circleAverage
          (fun u₂ =>
            ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
          0 1) by
      funext v₂
      rw [show
        (fun u₂ =>
          Real.circleAverage
            (fun v₁ =>
              Real.circleAverage
                (fun u₁ =>
                  ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ) *
                    ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
                0 1)
            0 1) =
        (fun u₂ =>
          ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ) *
            Real.circleAverage
              (fun v₁ =>
                Real.circleAverage
                  (fun u₁ =>
                    ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
                  0 1)
              0 1) by
          funext u₂
          exact hfirst u₂ v₂]
      exact hsecond v₂]
  simpa [smul_eq_mul] using
    (Real.circleAverage_fun_smul
      (a := Real.circleAverage
        (fun v₁ =>
          Real.circleAverage
            (fun u₁ =>
              ‖bourgainParabolaTwoTorusSum H₁ a u₁ v₁‖ ^ (6 : ℕ))
            0 1)
        0 1)
      (f := fun v₂ =>
        Real.circleAverage
          (fun u₂ =>
            ‖bourgainParabolaTwoTorusSum H₂ b u₂ v₂‖ ^ (6 : ℕ))
          0 1)
      (c := 0) (R := 1))

theorem bourgainParabolaL6Moment_nonneg
    (H : ℕ) (a : Fin H → ℂ) :
    0 ≤ bourgainParabolaL6Moment H a := by
  unfold bourgainParabolaL6Moment
  rw [circleAverage_circleAverage_parabola_norm_pow_six]
  positivity

/-- Uniform subpower estimate for the factorized bilinear local model. -/
theorem bourgainIndependentPlanarBilinearMoment_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a b : Fin H → ℂ),
        bourgainIndependentPlanarBilinearMoment H H a b ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨C₀, hC₀, hsingle⟩ :=
    circleAverage_circleAverage_parabola_norm_pow_six_subpower hhalf
  refine ⟨C₀ ^ (2 : ℕ), by positivity, ?_⟩
  intro H a b
  rw [bourgainIndependentPlanarBilinearMoment_eq_mul]
  have ha := hsingle H a
  have hb := hsingle H b
  calc
    bourgainParabolaL6Moment H a * bourgainParabolaL6Moment H b ≤
        (C₀ * (H : ℝ) ^ (ε / 2) *
          (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) *
        (C₀ * (H : ℝ) ^ (ε / 2) *
          (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
      exact mul_le_mul ha hb
        (bourgainParabolaL6Moment_nonneg H b) (by positivity)
    _ = C₀ ^ (2 : ℕ) * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      by_cases hH : H = 0
      · subst H
        simp
      · have hHpos : 0 < (H : ℝ) := by positivity
        have hpow :
            (H : ℝ) ^ (ε / 2) * (H : ℝ) ^ (ε / 2) =
              (H : ℝ) ^ ε := by
          rw [← Real.rpow_add hHpos]
          congr 1
          ring
        rw [show
          C₀ * (H : ℝ) ^ (ε / 2) *
                (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (C₀ * (H : ℝ) ^ (ε / 2) *
                (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) =
            C₀ ^ (2 : ℕ) *
              ((H : ℝ) ^ (ε / 2) * (H : ℝ) ^ (ε / 2)) *
              (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ) by ring,
          hpow]

end

end RHTower
