import GaloisForLFunctions.RHTower.SummableWeightedHeadFixedWaterCeiling
import GaloisForLFunctions.RHTower.CountableWeightedFirstReturn
import GaloisForLFunctions.RHTower.BlaschkeLocalizedEarlyReturnClock

/-!
# Universal spectral-depth law for countable recurrence

For every normalized nonnegative summable pure-point spectrum, the same
finite-head water entropy controls both sides of recurrence:

* it gives a deterministic deadline by which every phase packet returns;
* it gives a measure bound on packets returning before any proposed
  earlier deadline.

No finite-dimensional ambient space is assumed. The truncation depth,
water level, and tail mass are selected at the requested accuracy.
-/

open MeasureTheory

noncomputable section

namespace RHTower

/--
Spectral-depth entropy of the first `M` weights at water level `lam`.
Only weights visible above the inverse water level contribute.
-/
def countableSpectralDepthEntropy
    (p : ℕ → ℝ) (M : ℕ) (lam : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i : Fin M, Real.log (max 1 (lam * p i))

/--
Full-packet return defect obtained by resolving a head to defect `eta`
and discarding the remaining tail adversarially.
-/
def countableSpectralDepthDefect
    (p : ℕ → ℝ) (M : ℕ) (eta : ℝ) : ℝ :=
  summableWeightedHeadMass p M * eta +
    2 * ∑' j, p (M + j)

/--
Coordinate-resolution overhead in the constructive recurrence deadline.
-/
def countableSpectralDepthResolutionCost (M : ℕ) : ℝ :=
  (M - 1 : ℕ) * Real.log projectivePhaseResolutionConstant

/--
Every normalized countable pure-point spectrum has a deterministic
actual-first-return deadline controlled by its spectral-depth entropy.
-/
theorem exists_countableSpectralDepthFirstReturnDeadline
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    (pivot : Fin M)
    {eta lam : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hlam : 0 < lam)
    (hwater :
      projectiveWaterMass
          (normalizedWeightedHeadWeight p M) pivot
          (summableWeightedHeadMass p M * lam) ≤ eta) :
    ∃ T : ℕ,
      (∀ x : ℕ → UnitAddCircle,
        countableTorusWeightedFirstCoherenceTime p x
            (countableSpectralDepthDefect p M eta) ≤ T) ∧
      Real.log (T : ℝ) ≤
        countableSpectralDepthEntropy p M lam +
          countableSpectralDepthResolutionCost M := by
  obtain ⟨T, hreturn, hlog⟩ :=
    exists_countableWeightedCoherenceDeadline_headFixedWaterCeiling
      p hp hsum htotal M hM hmass pivot
      heta0 heta1 hlam hwater
  refine ⟨T, ?_, ?_⟩
  · intro x
    obtain ⟨n, hn0, hnT, hnreturn⟩ :=
      hreturn (fun k => torusRealFrequency (x k))
    have hn :
        CountableTorusWeightedCoherenceAt p x
          (countableSpectralDepthDefect p M eta) n := by
      refine ⟨hn0, ?_⟩
      simpa only [countableSpectralDepthDefect,
        exp_torusRealFrequency_eq_fourier_zsmul] using hnreturn
    exact
      (countableTorusWeightedFirstCoherenceTime_le_of
        p x (countableSpectralDepthDefect p M eta) hn).trans
        (by exact_mod_cast hnT)
  · simpa only [countableSpectralDepthEntropy,
      countableSpectralDepthResolutionCost] using hlog

/--
For every finite-head dominated phase ensemble, the probability of an
early return to the same full-packet defect is exponentially suppressed
by the same spectral-depth entropy that gives the constructive ceiling.
-/
theorem measureReal_countableSpectralDepthEarlyReturn_le
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M N : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    {eta lam : ℝ}
    (hdefect :
      countableSpectralDepthDefect p M eta /
          summableWeightedHeadMass p M ≤ 1)
    (hwater : 1 ≤ summableWeightedHeadMass p M * lam)
    (nu : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure nu]
    (B : NNReal)
    (hhead :
      Measure.map (countableTorusHead M) nu ≤ B • volume) :
    nu.real
        (countableTorusWeightedCoherenceHitUnion p N
          (countableSpectralDepthDefect p M eta)) ≤
      (B : ℝ) * ((N : ℝ) * ((M : ℝ) * Real.exp (
        (Real.pi / 4) *
            (lam * countableSpectralDepthDefect p M eta) -
          countableSpectralDepthEntropy p M lam +
          (1 / 2 : ℝ) *
            Real.log (summableWeightedHeadMass p M * lam)))) := by
  simpa only [countableSpectralDepthEntropy] using
    measureReal_countableTorusWeightedCoherenceHitUnion_originalHeadEntropy_le
      p hp hsum htotal M N hmass hdefect hwater nu B hhead

/--
Product Haar specialization: for every normalized countable spectrum,
the exact same entropy governs the early-return probability and the
deterministic actual-first-return ceiling.
-/
theorem countableSpectralDepthFirstReturnSandwich_productHaar
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    (pivot : Fin M)
    {eta lam : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hlam : 0 < lam)
    (hwaterFeasible :
      projectiveWaterMass
          (normalizedWeightedHeadWeight p M) pivot
          (summableWeightedHeadMass p M * lam) ≤ eta)
    (hdefect :
      countableSpectralDepthDefect p M eta /
          summableWeightedHeadMass p M ≤ 1)
    (hwaterUnit : 1 ≤ summableWeightedHeadMass p M * lam) :
    ∃ T : ℕ,
      (∀ x : ℕ → UnitAddCircle,
        countableTorusWeightedFirstCoherenceTime p x
            (countableSpectralDepthDefect p M eta) ≤ T) ∧
      Real.log (T : ℝ) ≤
        countableSpectralDepthEntropy p M lam +
          countableSpectralDepthResolutionCost M ∧
      ∀ N : ℕ,
        (Measure.infinitePi (fun _ : ℕ =>
            (volume : Measure UnitAddCircle))).real
            (countableTorusWeightedCoherenceHitUnion p N
              (countableSpectralDepthDefect p M eta)) ≤
          (N : ℝ) * ((M : ℝ) * Real.exp (
            (Real.pi / 4) *
                (lam * countableSpectralDepthDefect p M eta) -
              countableSpectralDepthEntropy p M lam +
              (1 / 2 : ℝ) *
                Real.log
                  (summableWeightedHeadMass p M * lam))) := by
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨T, hfirst, hlog⟩ :=
    exists_countableSpectralDepthFirstReturnDeadline
      p hp hsum htotal M hM hmass pivot
      heta0 heta1 hlam hwaterFeasible
  refine ⟨T, hfirst, hlog, ?_⟩
  intro N
  have hhead :
      Measure.map (countableTorusHead M)
          (Measure.infinitePi (fun _ : ℕ =>
            (volume : Measure UnitAddCircle))) ≤
        (1 : NNReal) • volume := by
    simpa only [one_smul] using
      (map_countableTorusHead_infinitePi_volume M).le
  simpa only [NNReal.coe_one, one_mul] using
    measureReal_countableSpectralDepthEarlyReturn_le
      p hp hsum htotal M N hmass hdefect hwaterUnit
      (Measure.infinitePi (fun _ : ℕ =>
        (volume : Measure UnitAddCircle)))
      (1 : NNReal) hhead

end RHTower
