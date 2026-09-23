import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport
import GaloisForLFunctions.RHTower.SuzukiCriticalWallFieldSquareRootWeld
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw
import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceDivisorTomography

/-!
# Gamma-sewn Julia rectangular divisor transgression

The singular environment coordinate of the canonical Gamma-sewn Julia lift recovers the
observer-free Suzuki critical wall amplitude at the boundary.  Its symmetric square is therefore
the exact von Mangoldt weight on every prime-power cell.  Extending by zero away from prime
powers and taking a finite sharp rectangular scalarization recovers the entire prime source.

Adding the canonical polar and Gamma terms gives the exact Xi-Weil observable.  On logarithmic
samples, the resulting coefficient tail is precisely the prime--Gamma Dirichlet coefficient
whose meromorphic continuation detects every off-critical Xi zero and its multiplicity.

All limits are pointwise or finite-sum limits.  No positivity hypothesis, zero hypothesis,
estimate, or numerical computation is used.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Squared critical Julia environment coordinate, extended by zero away from prime powers. -/
def gammaSewnMobiusJuliaCriticalHardCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  if hpow : IsPrimePow n then
    gammaSewnMobiusJuliaHardHalfWeightTransport x (-1 / 2)
      (Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩) ^ (2 : ℕ)
  else 0

/-- At critical damping, the Julia boundary amplitude is exactly the observer-free Suzuki wall
amplitude. -/
theorem xiGammaEulerBoundaryRealAmplitude_neg_half_eq_suzukiCriticalEntryWallBareAmplitude
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerBoundaryRealAmplitude (-1 / 2) pe =
      suzukiCriticalEntryWallBareAmplitude pe.1 pe.2 := by
  unfold xiGammaEulerBoundaryRealAmplitude
    suzukiCriticalEntryWallBareAmplitude
  dsimp only
  congr 1
  ring_nf

/-- Critical Julia environment coordinate recovers the exact von Mangoldt weight on every
integer cell. -/
theorem tendsto_gammaSewnMobiusJuliaCriticalHardCoefficient_nhdsGT_zero
    (n : ℕ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaCriticalHardCoefficient x n)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (ArithmeticFunction.vonMangoldt n / Real.sqrt n)) := by
  by_cases hpow : IsPrimePow n
  · let pe : Nat.Primes × ℕ := Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hn :
        xiGammaEulerValuationNat pe = n := by
      have hx := congrArg Subtype.val
        (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
      simpa [pe, xiGammaEulerValuationNat] using hx
    have hlim :=
      (tendsto_gammaSewnMobiusJuliaHardHalfWeightTransport_nhdsGT_zero
        (-1 / 2) pe).pow 2
    rw [xiGammaEulerBoundaryRealAmplitude_neg_half_eq_suzukiCriticalEntryWallBareAmplitude,
      sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt, hn] at hlim
    simpa only [gammaSewnMobiusJuliaCriticalHardCoefficient, hpow, pe, dite_true] using hlim
  · have hvm : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
    simp only [gammaSewnMobiusJuliaCriticalHardCoefficient, hpow, hvm, zero_div]
    exact tendsto_const_nhds

/-- Finite rectangular scalarization of the critical Julia environment channel. -/
def gammaSewnMobiusJuliaCriticalPrimeAutocorrelation
    (x L a : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a))),
    gammaSewnMobiusJuliaCriticalHardCoefficient x n *
      rectangularTwoEdgeAutocorrelation L a (Real.log n)

/-- Critical Julia environment channel converges to the entire finite rectangular prime source,
not merely to isolated prime-power weights. -/
theorem tendsto_gammaSewnMobiusJuliaCriticalPrimeAutocorrelation_nhdsGT_zero
    (L a : ℝ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaCriticalPrimeAutocorrelation x L a)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (rectangularPrimeAutocorrelationSum L a)) := by
  unfold gammaSewnMobiusJuliaCriticalPrimeAutocorrelation
    rectangularPrimeAutocorrelationSum
  apply tendsto_finsetSum
  intro n _hn
  exact
    (tendsto_gammaSewnMobiusJuliaCriticalHardCoefficient_nhdsGT_zero n).mul_const
      (rectangularTwoEdgeAutocorrelation L a (Real.log n))

/-- Completed source scalar obtained from the Julia environment channel. -/
def gammaSewnMobiusJuliaCriticalCompletedSource
    (x L a : ℝ) : ℝ :=
  -2 * gammaSewnMobiusJuliaCriticalPrimeAutocorrelation x L a +
    2 * rectangularEvenPolarFeature L a ^ (2 : ℕ) +
      rectangularGammaPolarCorrection L a

/-- **Julia-to-Xi transgression law.**  After canonical polar and Gamma completion, the singular
Julia environment channel converges to the exact sharp Xi-Weil observable. -/
theorem tendsto_gammaSewnMobiusJuliaCriticalCompletedSource_nhdsGT_zero
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaCriticalCompletedSource x L a)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a)).re) := by
  have hprime :=
    tendsto_gammaSewnMobiusJuliaCriticalPrimeAutocorrelation_nhdsGT_zero L a
  have hcompleted :=
    (hprime.const_mul (-2)).add
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℝ =>
            2 * rectangularEvenPolarFeature L a ^ (2 : ℕ) +
              rectangularGammaPolarCorrection L a)
          (nhdsWithin (0 : ℝ) (Ioi 0))
          (nhds
            (2 * rectangularEvenPolarFeature L a ^ (2 : ℕ) +
              rectangularGammaPolarCorrection L a)))
  have hsource := congrArg Complex.re
    (xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection hL ha)
  simp only [Complex.ofReal_re] at hsource
  rw [rectangularPrimePolarSourceCoefficient] at hsource
  rw [hsource]
  simpa only [gammaSewnMobiusJuliaCriticalCompletedSource, add_assoc] using hcompleted

/-- Julia-recovered completed coefficient sequence after deleting a finite prefix. -/
def gammaSewnMobiusJuliaCriticalCompletedTailCoefficient
    (x L : ℝ) (N n : ℕ) : ℝ :=
  if N ≤ n then
    gammaSewnMobiusJuliaCriticalCompletedSource x L (Real.log n / 2)
  else 0

/-- Every coefficient of the Julia-recovered tail converges to the source Dirichlet coefficient
whose continuation detects every off-critical Xi zero and its multiplicity. -/
theorem tendsto_gammaSewnMobiusJuliaCriticalCompletedTailCoefficient_nhdsGT_zero
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (n : ℕ) :
    Tendsto
      (fun x : ℝ =>
        gammaSewnMobiusJuliaCriticalCompletedTailCoefficient x L N n)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (xiRectangularPrimeGammaTailCoefficient L N n)) := by
  by_cases hn : N ≤ n
  · have hlimit :=
      tendsto_gammaSewnMobiusJuliaCriticalCompletedSource_nhdsGT_zero
        hL (hN n hn).2
    rw [xiRectangularPrimeGammaTailCoefficient, if_pos hn,
      xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
        hL (hN n hn).2]
    simpa only [gammaSewnMobiusJuliaCriticalCompletedTailCoefficient,
      if_pos hn, xiRectangularWeilLogCoefficient] using hlimit
  · simp only [gammaSewnMobiusJuliaCriticalCompletedTailCoefficient,
      xiRectangularPrimeGammaTailCoefficient, if_neg hn]
    exact tendsto_const_nhds

/-- **Arithmetic Julia divisor-completeness law.**  At every fixed positive window width and
every admissible tail, the singular Julia completion converges coefficientwise to a Dirichlet
source whose continuation is meromorphic on `Re s > 1`, whose poles are exactly all shifted
right-Xi zeros, whose normalized residues are their exact multiplicities, and whose holomorphy
there is equivalent to RH. -/
theorem gammaSewnMobiusJuliaCriticalCompletedTail_divisorComplete
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ n : ℕ,
      Tendsto
        (fun x : ℝ =>
          gammaSewnMobiusJuliaCriticalCompletedTailCoefficient x L N n)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (xiRectangularPrimeGammaTailCoefficient L N n))) ∧
    MeromorphicOn (xiRectangularPrimeGammaTailContinuation L N)
      {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re →
      (meromorphicOrderAt (xiRectangularPrimeGammaTailContinuation L N) s =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s)) ∧
    (∀ q : XiRightZeroCopy,
      meromorphicTrailingCoeffAt
          (xiRectangularPrimeGammaTailContinuation L N)
          (xiRightShiftedPole q) /
          (2 * xiRectangularRightCoefficient L q) =
        (xiRightMultiplicity q : ℂ)) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ (xiRectangularPrimeGammaTailContinuation L N) s) := by
  refine ⟨fun n =>
      tendsto_gammaSewnMobiusJuliaCriticalCompletedTailCoefficient_nhdsGT_zero
        hL.le hN n,
    meromorphicOn_xiRectangularPrimeGammaTailContinuation_rightOne hN,
    ?_, normalizedPrimeGammaTailResidue_eq_xiRightMultiplicity hL hN,
    riemannHypothesis_iff_primeGammaTailContinuation_analytic_rightOne hL hN⟩
  intro s hs
  exact
    meromorphicOrderAt_xiRectangularPrimeGammaTailContinuation_eq_neg_one_iff
      hL hN hs

end

end RHTower
