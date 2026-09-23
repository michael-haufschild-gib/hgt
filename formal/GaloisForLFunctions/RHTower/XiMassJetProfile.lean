import GaloisForLFunctions.RHTower.XiMassJetRecursion

/-!
# Every height derivative of the mass profile is a height-ring state

The mass profile is the state `(0, 2aτ·Z/R)` at exponent one, because `2aτ/Z = 2aτ·Z/R`.  Iterating
the jet recursion therefore produces, for every `k`, an explicit quadruple of polynomials whose
state is the `k`-th height derivative of the profile:

`∂_w^k ( 2aτ·K₁(aZ)/Z ) = ( P_A^{(k)} + Q_A^{(k)}Z )/R^{k+1} · K₀(aZ)
                         + ( P_B^{(k)} + Q_B^{(k)}Z )/R^{k+1} · K₁(aZ)` .

Nothing asymptotic enters: the quadruple is produced by a fixed polynomial recursion, and the
identity holds exactly on the whole region `Re(τ² + w²) > 0`.  A caustic-null jet operator
`4a⁴ − ∂_w²` is a fixed combination of two such derivatives, so its iterates are read off the same
recursion.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The coefficient quadruple of the `k`-th height derivative of the mass profile. -/
def xiJetData (a : ℝ) (τ : ℂ) :
    ℕ → Polynomial ℂ × Polynomial ℂ × Polynomial ℂ × Polynomial ℂ
  | 0 => (0, 0, 0, Polynomial.C (2 * (a : ℂ) * τ))
  | k + 1 =>
      match xiJetData a τ k with
      | (PA, QA, PB, QB) =>
          (xiJetStepPA a τ PA QB (k + 1), xiJetStepQA a τ QA PB (k + 1),
           xiJetStepPB a τ QA PB (k + 1), xiJetStepQB a τ PA QB (k + 1))

theorem xiJetData_zero (a : ℝ) (τ : ℂ) :
    xiJetData a τ 0 = (0, 0, 0, Polynomial.C (2 * (a : ℂ) * τ)) := rfl

theorem xiJetData_succ (a : ℝ) (τ : ℂ) (k : ℕ) :
    xiJetData a τ (k + 1)
      = (xiJetStepPA a τ (xiJetData a τ k).1 (xiJetData a τ k).2.2.2 (k + 1),
         xiJetStepQA a τ (xiJetData a τ k).2.1 (xiJetData a τ k).2.2.1 (k + 1),
         xiJetStepPB a τ (xiJetData a τ k).2.1 (xiJetData a τ k).2.2.1 (k + 1),
         xiJetStepQB a τ (xiJetData a τ k).1 (xiJetData a τ k).2.2.2 (k + 1)) := by
  rw [xiJetData]

/-- The `k`-th height derivative of the mass profile, as a height-ring state. -/
def xiJetProfile (a : ℝ) (τ : ℂ) (k : ℕ) : ℂ → ℂ :=
  xiMassBesselState a τ
    (xiHeightCoeff τ (xiJetData a τ k).1 (xiJetData a τ k).2.1 (k + 1))
    (xiHeightCoeff τ (xiJetData a τ k).2.2.1 (xiJetData a τ k).2.2.2 (k + 1))

/-- **The recursion differentiates the profile.** -/
theorem hasDerivAt_xiJetProfile {a : ℝ} {τ w : ℂ} (ha : 0 < a) (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (k : ℕ) :
    HasDerivAt (xiJetProfile a τ k) (xiJetProfile a τ (k + 1) w) w := by
  have hstep := hasDerivAt_xiJetState (a := a) (τ := τ) (w := w) ha hw
    (xiJetData a τ k).1 (xiJetData a τ k).2.1 (xiJetData a τ k).2.2.1 (xiJetData a τ k).2.2.2
    (k + 1)
  have hval : xiJetProfile a τ (k + 1) w
      = xiMassBesselState a τ
        (xiHeightCoeff τ
          (xiJetStepPA a τ (xiJetData a τ k).1 (xiJetData a τ k).2.2.2 (k + 1))
          (xiJetStepQA a τ (xiJetData a τ k).2.1 (xiJetData a τ k).2.2.1 (k + 1)) (k + 1 + 1))
        (xiHeightCoeff τ
          (xiJetStepPB a τ (xiJetData a τ k).2.1 (xiJetData a τ k).2.2.1 (k + 1))
          (xiJetStepQB a τ (xiJetData a τ k).1 (xiJetData a τ k).2.2.2 (k + 1)) (k + 1 + 1)) w := by
    rw [xiJetProfile, xiJetData_succ]
  rw [hval, xiJetProfile]
  exact hstep

/-- **The base of the recursion is the mass profile.** -/
theorem xiJetProfile_zero {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re) :
    xiJetProfile a τ 0 w = xiMassBesselHeightSide a τ w := by
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hZ2 : xiMassHeightRadius τ w ^ (2 : ℕ) = τ ^ (2 : ℕ) + w ^ (2 : ℕ) := xiMassHeightRadius_sq hw
  rw [xiJetProfile, xiJetData_zero, xiMassBesselState, xiHeightCoeff, xiHeightCoeff,
    xiMassBesselHeightSide, xiMassHeightK1, ← xiMassHeightRadius, ← hZ2]
  simp only [Polynomial.eval_zero, Polynomial.eval_C, zero_add, zero_mul, pow_one]
  field_simp
  ring

end

end RHTower
