import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedApertureFiniteSupport
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCanonicalGroundHeadConvergence

/-!
# Source-faithful all-prime matched convergence on canonical CCM heads

For a fixed physical aperture, mass-matched prime--polar cells have a uniform finite support:
the cutoff depends only on the aperture, not on the chosen head.  Consequently their literal
all-prime signed sum is one finite, norm-continuous block.  Applying this to the canonical finite
Gamma--Slepian heads upgrades their known form-norm convergence to convergence of the intact
prime-minus-matched-polar source.  No Fourier-moment, smooth-core, positivity, or RH premise
enters.  This closes convergence only; lower control of the resulting finite signed block remains
the RH-bearing obstacle.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Fixed-endpoint outgoing matched polar mass varies continuously with the literal aperture
head. -/
theorem continuous_ccmActualHeadOutgoingPolarSymmetricCell_on_aperture
    (a : SuzukiPositiveAperture) (s rho : ℝ) :
    Continuous (fun f : suzukiApertureHilbert a =>
      ccmActualHeadOutgoingPolarSymmetricCell s rho f.1) := by
  unfold ccmActualHeadOutgoingPolarSymmetricCell
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : suzukiApertureHilbert a × ℝ =>
    Real.exp (p.2 / 2) * ccmActualHeadTranslationDefect p.2 p.1.1)
  apply (Real.continuous_exp.comp
    (continuous_snd.div_const 2)).mul
    (continuous_ccmActualHeadTranslationDefect_joint.comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)))

/-- A fixed aperture has one common tail cutoff for the literal matched prime--polar cells of
every admissible head.  This is stronger than pointwise summability: it keeps the all-prime
source finite before taking any head limit. -/
theorem exists_uniform_ccmActualHeadMatchedPrimePolarCell_support
    (a : SuzukiPositiveAperture) :
    ∃ N : ℕ, ∀ (f : suzukiApertureHilbert a) (n : ℕ), N ≤ n →
      criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f.1 -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1 = 0 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htail : ∀ᶠ n : ℕ in atTop,
      2 * a.1 + 1 < Real.log n ∧ 1 ≤ n := by
    filter_upwards [hlog.eventually_gt_atTop (2 * a.1 + 1),
      eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hlogn hn
    exact ⟨hlogn, hn⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  refine ⟨N, fun f n hn' => ?_⟩
  exact ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_log_gt
    a f (hN n hn').2 (hN n hn').1

/-- One literal matched prime--polar cell is norm-continuous on the exact aperture space. -/
theorem continuous_ccmActualHeadMatchedPrimePolarCellDifference_on_aperture
    (a : SuzukiPositiveAperture) (n : ℕ) :
    Continuous (fun f : suzukiApertureHilbert a =>
      criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f.1 -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1) := by
  apply (continuous_const.mul
    (continuous_ccmActualHeadTranslationDefect_joint.comp
      (continuous_const.prodMk continuous_subtype_val))).sub
    (continuous_ccmActualHeadOutgoingPolarSymmetricCell_on_aperture a (Real.log n)
      (ccmActualHeadMatchedPrimePolarRadius n))

/-- At fixed aperture, each uniform matched finite block is norm-continuous. -/
theorem continuous_ccmActualHeadMatchedPrimePolarFiniteBlock_on_aperture
    (a : SuzukiPositiveAperture) (F : Finset ℕ) :
    Continuous (fun f : suzukiApertureHilbert a =>
      ccmActualHeadMatchedPrimePolarFiniteBlock F f.1) := by
  unfold ccmActualHeadMatchedPrimePolarFiniteBlock
  apply continuous_finsetSum F
  intro n hn
  exact continuous_ccmActualHeadMatchedPrimePolarCellDifference_on_aperture a n

/-- The literal all-prime matched source equals a finite block with a cutoff independent of the
head once the aperture is fixed. -/
theorem exists_tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_uniform_finiteBlock
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∃ N : ℕ,
      (∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n) f.1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1)) =
        ccmActualHeadMatchedPrimePolarFiniteBlock (Finset.range N) f.1 := by
  obtain ⟨N, hN⟩ := exists_uniform_ccmActualHeadMatchedPrimePolarCell_support a
  refine ⟨N, ?_⟩
  rw [tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact hN f n hn

/-- Norm convergence of aperture heads transports the full literal all-prime matched source.
The proof reduces both sides to one common finite block before passing to the limit. -/
theorem tendsto_tsum_ccmActualHeadMatchedPrimePolarCellDifference_of_tendsto
    (a : SuzukiPositiveAperture) {g : ℕ → suzukiApertureHilbert a}
    {f : suzukiApertureHilbert a} (hg : Tendsto g atTop (nhds f)) :
    Tendsto (fun k : ℕ =>
      ∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n) (g k).1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) (g k).1))
      atTop
      (nhds (∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n) f.1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1))) := by
  obtain ⟨N, hN⟩ := exists_uniform_ccmActualHeadMatchedPrimePolarCell_support a
  have hsum : ∀ x : suzukiApertureHilbert a,
      (∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n) x.1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) x.1)) =
        ccmActualHeadMatchedPrimePolarFiniteBlock (Finset.range N) x.1 := by
    intro x
    rw [tsum_eq_sum (s := Finset.range N)]
    · rfl
    · intro n hn
      rw [Finset.mem_range, not_lt] at hn
      exact hN x n hn
  rw [show (fun k : ℕ =>
      ∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n) (g k).1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) (g k).1)) =
        fun k => ccmActualHeadMatchedPrimePolarFiniteBlock (Finset.range N) (g k).1 by
      funext k
      exact hsum (g k)]
  rw [hsum f]
  exact (continuous_ccmActualHeadMatchedPrimePolarFiniteBlock_on_aperture
    a (Finset.range N)).tendsto f |>.comp hg

/-- Canonical finite Gamma--Slepian heads converge for the literal all-prime matched
prime-minus-polar source.  Cancellation is retained cellwise and the limiting head is the true
restricted-Weil ground state. -/
theorem tendsto_tsum_ccmActualHeadMatchedPrimePolarCellDifference_canonicalGroundHead
    (a : SuzukiPositiveAperture) :
    Tendsto (fun k : ℕ =>
      ∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n)
                (ccmArchimedeanFormToAperture a
                  (ccmRestrictedWeilCanonicalGroundHead a k)).1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n)
              (ccmArchimedeanFormToAperture a
                (ccmRestrictedWeilCanonicalGroundHead a k)).1))
      atTop
      (nhds (∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n)
                (ccmRestrictedWeilCanonicalGroundEigenstate a).1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n)
              (ccmRestrictedWeilCanonicalGroundEigenstate a).1))) := by
  apply tendsto_tsum_ccmActualHeadMatchedPrimePolarCellDifference_of_tendsto a
  have hhead := tendsto_ccmRestrictedWeilCanonicalGroundHead a
  have hphysical := (ccmArchimedeanFormToAperture a).continuous.continuousAt.tendsto.comp hhead
  rw [ccmRestrictedWeilCanonicalGroundFormLift_embedding] at hphysical
  exact hphysical

end RHTower
