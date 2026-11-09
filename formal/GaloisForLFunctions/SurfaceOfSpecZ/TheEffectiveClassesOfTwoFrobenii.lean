import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimeNumberTheoremInEveryWindow

/-!
# The effective classes of two Frobenii

`TwoFrobeniiSuffice` bounds the traces on the planes `⟨Γ_1, Γ_d⟩`, `d = pᵃqᵇ`, whose lags
`a log p + b log q` are discrete, and needs an attained top. The effective classes `Γ_m + Γ_n` with
`m, n` both in the monoid `⟨p, q⟩` have the defect `2c_B(0) + 2c_B(log m − log n)` (Hecke invariance),
and their lags fill the dense group `ℤ log p + ℤ log q`. A one-sided bound there extends by
continuity to every lag, so no attainment is needed:

* `riemannHypothesis_iff_bddBelow_twoFrobeniiLags`: RH iff `c_B(log m − log n) ≥ −K` for all
  `m, n ∈ ⟨p, q⟩`;
* `riemannHypothesis_iff_twoFrobeniiEffectiveCounts`: RH iff every effective class `Γ_m + Γ_n`,
  `m, n ∈ ⟨p, q⟩`, carries an `ℕ`-count along its ray with Tate limit `2c_B(0) + 2c_B(log m − log n)`.

The count door of the prime planes (`TheEffectiveClassesOfThePrimePlanes`) needs every prime; here
two suffice, one-sided.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri CountingHolography

variable {p q : ℕ}

/-- A lower bound on a dense set of lags is a lower bound at every lag. -/
theorem bddBelow_orbitCorr_of_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ, -K ≤ zetaScalingDatum.orbitCorr splineCycle
      (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ))) (t : ℝ) :
    -K ≤ zetaScalingDatum.orbitCorr splineCycle t := by
  have hcont := continuous_zetaOrbitCorr' splineCycle
  have hclosed : IsClosed {t : ℝ | -K ≤ zetaScalingDatum.orbitCorr splineCycle t} :=
    isClosed_le continuous_const hcont
  have hsub : ((AddSubgroup.closure {Real.log p, Real.log q} : AddSubgroup ℝ) : Set ℝ) ⊆
      {t : ℝ | -K ≤ zetaScalingDatum.orbitCorr splineCycle t} := by
    intro t ht
    obtain ⟨a, b, a', b', rfl⟩ := exists_lag_of_mem_closure hp hq ht
    exact hK a b a' b'
  have huniv := ((RHTower.dense_addSubgroup_log_primes hp hq hpq).mono hsub).closure_eq
  rw [hclosed.closure_eq] at huniv
  have : t ∈ {t : ℝ | -K ≤ zetaScalingDatum.orbitCorr splineCycle t} := by rw [huniv]; trivial
  exact this

/-- **One side on the lags of two Frobenii is RH.** -/
theorem riemannHypothesis_iff_bddBelow_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ a b a' b' : ℕ, -K ≤ zetaScalingDatum.orbitCorr splineCycle
      (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ)) := by
  constructor
  · intro hRH
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun a b a' b' => ?_⟩
    have h := (riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH)
      (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ))
    rw [ScalingDatum.HasseWeilAt] at h
    exact (abs_le.mp h).1
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_iff_bddBelow_primeDegrees'.mpr
      ⟨K, fun r _ => bddBelow_orbitCorr_of_twoFrobeniiLags hp hq hpq hK _⟩

/-- **The count door at the effective classes of two Frobenii.** -/
theorem riemannHypothesis_iff_twoFrobeniiEffectiveCounts (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ a b a' b' : ℕ, ∃ K : ℕ → ℕ,
      Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2) atTop
        (𝓝 (2 * zetaScalingDatum.orbitCorr splineCycle 0 + 2 * zetaScalingDatum.orbitCorr
          splineCycle (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ)))) := by
  constructor
  · intro hRH a b a' b'
    have h := (riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH)
      (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ))
    rw [ScalingDatum.HasseWeilAt] at h
    have hnn : 0 ≤ 2 * zetaScalingDatum.orbitCorr splineCycle 0 + 2 * zetaScalingDatum.orbitCorr
        splineCycle (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ)) := by
      linarith [(abs_le.mp h).1]
    exact ⟨fun m => ⌊(m : ℝ) ^ 2 * _⌋₊, tendsto_floor_div_sq hnn⟩
  · intro h
    refine (riemannHypothesis_iff_bddBelow_twoFrobeniiLags hp hq hpq).mpr
      ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun a b a' b' => ?_⟩
    obtain ⟨K, hK⟩ := h a b a' b'
    have hnn := ge_of_tendsto' hK fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
