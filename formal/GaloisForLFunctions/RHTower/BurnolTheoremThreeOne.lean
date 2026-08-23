import GaloisForLFunctions.RHTower.BurnolMinimalityAperture
import GaloisForLFunctions.RHTower.BurnolCoPoissonNotComplete
import GaloisForLFunctions.RHTower.BurnolCompletenessUnit

/-!
# Burnol's Theorem 3.1

The evaluator system `Y^a_{ρ,k}` attached to the nontrivial zeros of `ζ` is

* **complete** in `L_a` exactly for `a ≥ 1`,
* **minimal** in `L_a` exactly for `a ≤ 1`.

Everything is phrased in the jet language in which the corpus states the whole `Y`-theory:
"`v` is orthogonal to `Y^a_{ρ,k}` for all `k < m_ρ`" is "`ζ` divides the continued Mellin transform
of `v` at `ρ`", and "`v` is not orthogonal to `Y^a_{ρ,k}`" is "the transform has order exactly `k`
at `ρ`".  With that dictionary the four statements below are literally Burnol's Theorem 3.1.

## Main results

* `IsExtendedSonineDatum`, `AnnihilatesEvaluators`
* `burnol_evaluators_complete_of_one_le`
* `burnol_evaluators_not_complete_of_lt_one`
* `burnol_evaluators_minimal_of_le_one`
* `burnol_evaluators_not_minimal_of_one_lt`
* `burnol_theorem_three_one`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- `v` is a vector of `L_a` with aperture constants `c` (cosine side) and `d` (physical side). -/
def IsExtendedSonineDatum (a : ℝ) (v : SoninL2) (c d : ℂ) : Prop :=
  v ∈ evenSubspace ∧ v ∈ centralSoninExtendedCarrier a ∧
    (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) ∧
    (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)

/-- `v` is orthogonal to every evaluator attached to every nontrivial zero. -/
def AnnihilatesEvaluators (a : ℝ) (v : SoninL2) (c d : ℂ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    meromorphicOrderAt riemannZeta ρ
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ

/-- `v` is orthogonal to every evaluator outside the finite exceptional set `R`. -/
def AnnihilatesEvaluatorsOff (a : ℝ) (R : Finset ℂ) (v : SoninL2) (c d : ℂ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
    meromorphicOrderAt riemannZeta ρ
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ

/-- **Complete for `a ≥ 1`.** -/
theorem burnol_evaluators_complete_of_one_le {a : ℝ} (ha : 1 ≤ a) {v : SoninL2} {c d : ℂ}
    (hdat : IsExtendedSonineDatum a v c d) (hann : AnnihilatesEvaluators a v c d) : v = 0 :=
  eq_zero_of_zeta_dvd_extendedMellin_one_le ha hdat.1 hdat.2.2.1 hdat.2.2.2 hann

/-- **Not complete for `a < 1`.** -/
theorem burnol_evaluators_not_complete_of_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ (v : SoninL2) (c d : ℂ), IsExtendedSonineDatum a v c d ∧
      AnnihilatesEvaluators a v c d ∧ v ≠ 0 := by
  obtain ⟨v, c, d, hne, hev, hmem, hc, hd, hann⟩ :=
    exists_nonzero_zeta_dvd_of_aperture_lt_one ha ha1
  exact ⟨v, c, d, ⟨hev, hmem, hc, hd⟩, hann, hne⟩

/-- **Minimal for `a ≤ 1`.**  For every nontrivial zero `ρ` and every jet index `k` below its
multiplicity there is a vector of `L_a` orthogonal to all the other evaluators and *not* orthogonal
to `Y^a_{ρ,k}`. -/
theorem burnol_evaluators_minimal_of_le_one {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {k : ℕ}
    (hk : (k : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    ∃ (v : SoninL2) (c d : ℂ), IsExtendedSonineDatum a v c d ∧
      (∀ ρ' : ℂ, 0 < ρ'.re → ρ'.re < 1 → ρ' ≠ ρ →
        meromorphicOrderAt riemannZeta ρ'
          ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ') ∧
      meromorphicOrderAt (extendedMellinContinuation a c d v) ρ = ((k : ℤ) : WithTop ℤ) := by
  obtain ⟨v, c, d, hev, hmem, hc, hd, hother, hself⟩ :=
    exists_minimality_witness_aperture ha ha1 h0 h1 hk
  exact ⟨v, c, d, ⟨hev, hmem, hc, hd⟩, hother, hself⟩

/-- **Not minimal for `a > 1`.**  The system stays complete after omitting arbitrarily finitely
many evaluators, so no member is outside the closed span of the others. -/
theorem burnol_evaluators_not_minimal_of_one_lt {a : ℝ} (ha : 1 < a) {R : Finset ℂ}
    (hR : ∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) {v : SoninL2} {c d : ℂ}
    (hdat : IsExtendedSonineDatum a v c d) (hann : AnnihilatesEvaluatorsOff a R v c d) :
    v = 0 :=
  eq_zero_of_zeta_dvd_off_finite ha hdat.1 hdat.2.1 hdat.2.2.1 hdat.2.2.2 hR hann

/-- **Burnol's Theorem 3.1.**  The aperture threshold of the evaluator system is exactly `1`:
complete for `a ≥ 1` and not for `a < 1`; minimal for `a ≤ 1` and not for `a > 1`. -/
theorem burnol_theorem_three_one :
    (∀ a : ℝ, 1 ≤ a → ∀ (v : SoninL2) (c d : ℂ), IsExtendedSonineDatum a v c d →
        AnnihilatesEvaluators a v c d → v = 0) ∧
    (∀ a : ℝ, 0 < a → a < 1 → ∃ (v : SoninL2) (c d : ℂ), IsExtendedSonineDatum a v c d ∧
        AnnihilatesEvaluators a v c d ∧ v ≠ 0) ∧
    (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → ∀ k : ℕ,
        (k : ℕ∞) < analyticOrderAt riemannZeta ρ →
        ∃ (v : SoninL2) (c d : ℂ), IsExtendedSonineDatum a v c d ∧
          (∀ ρ' : ℂ, 0 < ρ'.re → ρ'.re < 1 → ρ' ≠ ρ →
            meromorphicOrderAt riemannZeta ρ'
              ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ') ∧
          meromorphicOrderAt (extendedMellinContinuation a c d v) ρ = ((k : ℤ) : WithTop ℤ)) ∧
    (∀ a : ℝ, 1 < a → ∀ R : Finset ℂ, (∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) →
        ∀ (v : SoninL2) (c d : ℂ), IsExtendedSonineDatum a v c d →
        AnnihilatesEvaluatorsOff a R v c d → v = 0) :=
  ⟨fun _ ha _ _ _ hdat hann => burnol_evaluators_complete_of_one_le ha hdat hann,
   fun _ ha ha1 => burnol_evaluators_not_complete_of_lt_one ha ha1,
   fun _ ha ha1 _ h0 h1 _ hk => burnol_evaluators_minimal_of_le_one ha ha1 h0 h1 hk,
   fun _ ha _ hR _ _ _ hdat hann => burnol_evaluators_not_minimal_of_one_lt ha hR hdat hann⟩

end

end RHTower
