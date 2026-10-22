import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalScalarReaderPacketBlowup
import GaloisForLFunctions.RHTower.IndexedDiagonalWeakSchatten
import GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimePrimitiveRecovery

/-!
# Möbius prime-normal half-density weak-Schatten boundary

The literal physical half-density cannot enter the existing adaptive `ℓ¹` codiagonal off the
critical line.  Its canonical diagonal realization nevertheless lies unconditionally in weak
Schatten class `S_{2,∞}`.  This constructs the weak-`ℓ²` boundary carrier demanded by the domain
no-go without assuming neutrality.

The boundary is sharp: the same diagonal is Hilbert--Schmidt exactly when the individual theta
Green boundary flux vanishes, and global Hilbert--Schmidt admission is equivalent to RH.  Thus a
future compensated codiagonal may legally use the weak endpoint, but it cannot silently strengthen
that endpoint to ordinary Hilbert-space admission without already proving the desired theorem.
-/

open Complex
open scoped ENNReal NNReal BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HTGeometry

/-- Complex diagonal symbol of the literal physical Möbius prime-normal half-density. -/
def thetaMobiusPrimeNormalHalfDensityDiagonalSymbol
    (q : XiZeroCopy) (p : Nat.Primes) : ℂ :=
  thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q

theorem norm_thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_le_one
    (q : XiZeroCopy) (p : Nat.Primes) :
    ‖thetaMobiusPrimeNormalHalfDensityDiagonalSymbol q p‖ ≤ 1 := by
  simpa [thetaMobiusPrimeNormalHalfDensityDiagonalSymbol, Real.norm_eq_abs] using
    abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_one p q

/-- Bounded diagonal realization of the literal physical half-density on prime `ℓ²`. -/
def thetaMobiusPrimeNormalHalfDensityDiagonal
    (q : XiZeroCopy) : IndexedEllTwo Nat.Primes →L[ℂ] IndexedEllTwo Nat.Primes :=
  ellTwoDiagonal (thetaMobiusPrimeNormalHalfDensityDiagonalSymbol q)
    (norm_thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_le_one q)

/-- The physical channel gap never exceeds the universal critical `p⁻¹ᐟ²` amplitude. -/
theorem abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_universal
    (p : Nat.Primes) (q : XiZeroCopy) :
    |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| ≤
      routeNGammaSewnUniversalCriticalChannelAmplitude p := by
  let t := primeDepthBVWoldXiCenteredRate q.1
  let u := routeNGammaSewnUniversalCriticalChannelAmplitude p
  let v := routeNGammaSewnTwistedCriticalChannelAmplitude t p
  have hv0 : 0 < v := by
    dsimp [v, routeNGammaSewnTwistedCriticalChannelAmplitude]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hvu : v ≤ u := by
    dsimp [v, u, t]
    exact routeNGammaSewnTwistedCriticalChannelAmplitude_le_universal _ _
  have hgap : 0 ≤ u - v := sub_nonneg.mpr hvu
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap]
  change |if 0 ≤ t then u - v else -(u - v)| ≤ u
  split_ifs
  · rw [abs_of_nonneg hgap]
    exact sub_le_self _ hv0.le
  · rw [abs_neg, abs_of_nonneg hgap]
    exact sub_le_self _ hv0.le

/-- Ordered coefficients obey the exact square-decay estimate required at the weak `S₂` wall. -/
theorem thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_nthPrime_sq_le
    (q : XiZeroCopy) (n : ℕ) :
    ‖thetaMobiusPrimeNormalHalfDensityDiagonalSymbol q (nthPrimeEquiv n)‖ ^ 2 ≤
      1 / ((n : ℝ) + 1) := by
  let p : Nat.Primes := nthPrimeEquiv n
  have hamp := abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_universal p q
  have hindexNat : n + 1 ≤ (p : ℕ) := by
    change n + 1 ≤ (nthPrimeSubtype n : ℕ)
    exact le_trans (by omega) (nthPrimeSubtype_index_add_two_le n)
  have hindex : (n : ℝ) + 1 ≤ (p : ℝ) := by
    exact_mod_cast hindexNat
  calc
    ‖thetaMobiusPrimeNormalHalfDensityDiagonalSymbol q (nthPrimeEquiv n)‖ ^ 2 =
        |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| ^ 2 := by
      simp [thetaMobiusPrimeNormalHalfDensityDiagonalSymbol, p, Real.norm_eq_abs]
    _ ≤ routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2 := by
      gcongr
    _ = routeNGammaSewnUniversalCriticalChannelMass p :=
      routeNGammaSewnUniversalCriticalChannelAmplitude_sq p
    _ = 1 / (p : ℝ) := by
      rw [routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]
      simp
    _ ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hindex

/-- Unconditional weak-`S₂` admission of the physical half-density boundary operator. -/
theorem thetaMobiusPrimeNormalHalfDensityDiagonal_memWeakSchattenClass_two
    (q : XiZeroCopy) :
    MemWeakSchattenClass 2 (thetaMobiusPrimeNormalHalfDensityDiagonal q) := by
  exact memWeakSchattenClass_ellTwoDiagonal_of_reindex_pow_le nthPrimeEquiv
    (norm_thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_le_one q)
    (by norm_num : 0 < (2 : ℕ)) (by norm_num : 0 ≤ (1 : ℝ))
    (thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_nthPrime_sq_le q)

/-- Square summability of the literal physical half-density is exactly same-copy neutrality. -/
theorem summable_sq_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [show (fun p : Nat.Primes =>
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2) =
      fun p : Nat.Primes => thetaMobiusPrimeNormalProfilePositiveGauge p q *
        thetaMobiusPrimeNormalReflectionProfile p q ^ 2 by
    funext p
    exact thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq p q]
  rw [← thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_mobiusPrimeNormalProfileEnergy]
  exact thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero q

/-- Sharp endpoint wall: the weak-`S₂` boundary operator improves to Hilbert--Schmidt exactly on a
neutral theta divisor copy. -/
theorem thetaMobiusPrimeNormalHalfDensityDiagonal_isHilbertSchmidt_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    ContinuousLinearMap.IsHilbertSchmidt
        (thetaMobiusPrimeNormalHalfDensityDiagonal q) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [thetaMobiusPrimeNormalHalfDensityDiagonal,
    isHilbertSchmidt_ellTwoDiagonal_iff]
  rw [← summable_sq_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_iff_boundaryFlux_zero q]
  apply summable_congr
  intro p
  simp [thetaMobiusPrimeNormalHalfDensityDiagonalSymbol, Real.norm_eq_abs, sq_abs]

/-- Global ordinary Hilbert--Schmidt admission of the physical boundary diagonals. -/
def EveryThetaMobiusPrimeNormalHalfDensityDiagonalHilbertSchmidt : Prop :=
  ∀ q : XiZeroCopy,
    ContinuousLinearMap.IsHilbertSchmidt
      (thetaMobiusPrimeNormalHalfDensityDiagonal q)

/-- Global Hilbert--Schmidt admission of the literal physical boundary is exactly RH. -/
theorem everyThetaMobiusPrimeNormalHalfDensityDiagonalHilbertSchmidt_iff_riemannHypothesis :
    EveryThetaMobiusPrimeNormalHalfDensityDiagonalHilbertSchmidt ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    thetaMobiusPrimeNormalHalfDensityDiagonal_isHilbertSchmidt_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
