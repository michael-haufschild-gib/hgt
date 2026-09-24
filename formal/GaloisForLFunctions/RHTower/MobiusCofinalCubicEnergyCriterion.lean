import GaloisForLFunctions.RHTower.MobiusReciprocalGammaHankelBridge
import GaloisForLFunctions.RHTower.MobiusMertensFiniteSectionEnergy

/-!
# Cofinal cubic Route L source criterion

A cutoff ceiling for the literal signed cubic energy at a cofinal family of
positive shifts implies RH. The ceiling may depend on the shift. The proof
uses the closed two-order reciprocal transfer, finite Gamma--Hankel identity,
and cofinal finite-section receiver. No endpoint shift of zero is requested.
-/

namespace RHTower

private theorem gamma_bounded_of_cubic (δ : ℝ) (hδ : 0 < δ)
    (h : ∃ C : ℝ, ∀ N : ℕ, finiteGeneralReciprocalEnergy (3 + δ) δ N ≤ C) :
    MobiusGammaHankelEnergyUniformlyBounded (1 + δ) := by
  obtain ⟨C, hC⟩ := h
  let A : ℝ :=
    (4 * ((2 * (1 + δ) - δ) / (2 * (1 + δ) - 1 - δ))) *
      (4 * ((2 * ((1 + δ) + 1) - δ) / (2 * ((1 + δ) + 1) - 1 - δ)))
  have hnum1 : 0 < 2 * (1 + δ) - δ := by linarith
  have hden1 : 0 < 2 * (1 + δ) - 1 - δ := by linarith
  have hnum2 : 0 < 2 * ((1 + δ) + 1) - δ := by linarith
  have hden2 : 0 < 2 * ((1 + δ) + 1) - 1 - δ := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hG : 0 ≤ Real.Gamma (1 + δ) :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + δ)).le
  refine ⟨Real.Gamma (1 + δ) * (A * C), ?_⟩
  intro N
  have ht : finiteGeneralReciprocalEnergy (1 + δ) δ N ≤
      A * finiteGeneralReciprocalEnergy (3 + δ) δ N := by
    simpa only [A, show (1 + δ) + 2 = 3 + δ by ring] using
      finiteGeneralReciprocalEnergy_le_two_orders (1 + δ) δ hden1 N
  calc
    finiteMobiusGammaHankelEnergy N (1 + δ) =
        Real.Gamma (1 + δ) * finiteGeneralReciprocalEnergy (1 + δ) δ N :=
      finiteMobiusGammaHankelEnergy_eq_gamma_mul_generalReciprocalEnergy δ N
    _ ≤ Real.Gamma (1 + δ) *
        (A * finiteGeneralReciprocalEnergy (3 + δ) δ N) :=
      mul_le_mul_of_nonneg_left ht hG
    _ ≤ Real.Gamma (1 + δ) * (A * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hC N) hA) hG

/-- For each distance to the critical line, one positive-shift cubic source
energy has a finite ceiling along all natural cutoffs. -/
def RouteLCofinalCubicEnergyBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 2 * ε ∧
    ∃ C : ℝ, ∀ N : ℕ, finiteGeneralReciprocalEnergy (3 + δ) δ N ≤ C

/-- A cofinal family of literal cubic signed bounds excludes all off-line zeros. -/
theorem riemannHypothesis_of_routeLCofinalCubicEnergyBounded
    (h : RouteLCofinalCubicEnergyBounded) : RiemannHypothesis := by
  apply mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_iff_riemannHypothesis.mp
  intro ε hε
  obtain ⟨δ, hδ, hδlt, hbound⟩ := h ε hε
  let σ : ℝ := (1 + δ) / 2
  have hσhalf : 1 / 2 < σ := by dsimp [σ]; linarith
  have hσupper : σ < 1 / 2 + ε := by dsimp [σ]; linarith
  refine ⟨σ, hσhalf, hσupper, ?_⟩
  have hσ : 2 * σ = 1 + δ := by dsimp [σ]; ring
  rw [hσ]
  exact (mobiusGammaHankelEnergyUniformlyBounded_iff_offDiagonalUpperBounded
    (by linarith : 1 < 1 + δ)).mp (gamma_bounded_of_cubic δ hδ hbound)

/-- Explicit countable cubic source target at shifts `2/(k+2)`. -/
def RouteLCanonicalCubicEnergyBounded : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ N : ℕ,
    finiteGeneralReciprocalEnergy
      (3 + 2 / ((k + 2 : ℕ) : ℝ))
      (2 / ((k + 2 : ℕ) : ℝ)) N ≤ C

/-- The explicit countable cubic target suffices for RH. -/
theorem riemannHypothesis_of_routeLCanonicalCubicEnergyBounded
    (h : RouteLCanonicalCubicEnergyBounded) : RiemannHypothesis := by
  apply riemannHypothesis_of_routeLCofinalCubicEnergyBounded
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hden : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hprod : 1 < ε * (k : ℝ) := by
    have := (div_lt_iff₀ hε).mp hk
    simpa only [one_div, mul_comm] using this
  have hprod2 : 1 < ε * (((k + 2 : ℕ) : ℝ)) := by
    push_cast
    nlinarith
  have hsmall : 1 / (((k + 2 : ℕ) : ℝ)) < ε :=
    (div_lt_iff₀ hden).2 (by simpa only [mul_comm] using hprod2)
  let δ : ℝ := 2 / (((k + 2 : ℕ) : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδlt : δ < 2 * ε := by
    have heq : δ = 2 * (1 / (((k + 2 : ℕ) : ℝ))) := by dsimp [δ]; ring
    rw [heq]
    linarith
  exact ⟨δ, hδ, hδlt, h k⟩

/-- One finite cubic ceiling need only recur at arbitrarily large cutoffs on each
member of a cofinal family of positive shifts. -/
def RouteLCofinalCubicEnergyFrequentlyBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 2 * ε ∧
    ∃ C : ℝ, ∃ᶠ N : ℕ in Filter.atTop,
      finiteGeneralReciprocalEnergy (3 + δ) δ N ≤ C

/-- Bounded cubic returns already imply RH through the Fatou subsequence receiver. -/
theorem riemannHypothesis_of_routeLCofinalCubicEnergyFrequentlyBounded
    (h : RouteLCofinalCubicEnergyFrequentlyBounded) : RiemannHypothesis := by
  apply mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_iff_riemannHypothesis.mp
  intro ε hε
  obtain ⟨δ, hδ, hδlt, C, hfreq⟩ := h ε hε
  let σ : ℝ := (1 + δ) / 2
  let A : ℝ :=
    (4 * ((2 * (1 + δ) - δ) / (2 * (1 + δ) - 1 - δ))) *
      (4 * ((2 * ((1 + δ) + 1) - δ) / (2 * ((1 + δ) + 1) - 1 - δ)))
  have hden1 : 0 < 2 * (1 + δ) - 1 - δ := by linarith
  have hnum1 : 0 < 2 * (1 + δ) - δ := by linarith
  have hden2 : 0 < 2 * ((1 + δ) + 1) - 1 - δ := by linarith
  have hnum2 : 0 < 2 * ((1 + δ) + 1) - δ := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hG : 0 ≤ Real.Gamma (1 + δ) :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + δ)).le
  have hσhalf : 1 / 2 < σ := by dsimp [σ]; linarith
  have hσupper : σ < 1 / 2 + ε := by dsimp [σ]; linarith
  refine ⟨σ, Real.Gamma (1 + δ) * (A * C), hσhalf, hσupper, ?_⟩
  have hσ : 2 * σ = 1 + δ := by dsimp [σ]; ring
  rw [hσ]
  exact hfreq.mono (fun N hN => by
    have ht : finiteGeneralReciprocalEnergy (1 + δ) δ N ≤
        A * finiteGeneralReciprocalEnergy (3 + δ) δ N := by
      simpa only [A, show (1 + δ) + 2 = 3 + δ by ring] using
        finiteGeneralReciprocalEnergy_le_two_orders (1 + δ) δ hden1 N
    have hE : finiteMobiusGammaHankelEnergy N (1 + δ) ≤
        Real.Gamma (1 + δ) * (A * C) := by
      calc
        finiteMobiusGammaHankelEnergy N (1 + δ) =
            Real.Gamma (1 + δ) * finiteGeneralReciprocalEnergy (1 + δ) δ N :=
          finiteMobiusGammaHankelEnergy_eq_gamma_mul_generalReciprocalEnergy δ N
        _ ≤ Real.Gamma (1 + δ) *
            (A * finiteGeneralReciprocalEnergy (3 + δ) δ N) :=
          mul_le_mul_of_nonneg_left ht hG
        _ ≤ Real.Gamma (1 + δ) * (A * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN hA) hG
    rw [finiteMobiusGammaHankelOffDiagonalCovariance]
    exact (sub_le_self _
      (finiteMobiusGammaHankelDiagonalEnergy_nonneg N
        (by linarith : 0 < 1 + δ))).trans hE)

end RHTower
