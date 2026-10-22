import GaloisForLFunctions.RHTower.PrimeHarmonicLogLower
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture

/-!
# Suzuki aperture forces superpolynomial reflected-sewing cost

Suzuki's compact interval `[-a,a]` exposes prime powers with logarithmic location at most
`2a`.  At integer prime cutoff `X`, the corresponding exact aperture is therefore

`a_X = (1 / 2) log (X + 1)`.

The finite Euler-product domination of the harmonic sum gives the unconditional lower bound

`log (X + 1) ≤ primeWoldBoundaryVolumeBelow (X + 1)⁻¹`.

Combining this source-specific cutoff law with the reflected Hellinger--Rees fracture proves
that every exact bounded linear sewing of the reflected valuation sectors has norm larger than
every fixed power of the Suzuki aperture.  Thus no polynomially conditioned exact sewing can
implement that source reflection.

This is a quantitative no-go only for the reflected-valuation sewing architecture appearing in
the modular-superselection theorem.  It does not exclude singular or relation-valued sewing, a
source-selected pre-fusion channel, or Suzuki's surviving two-angle meromorphic Livšic route.
-/

open Filter Asymptotics
open GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Integer prime cutoff `X` expressed in Suzuki's physical half-log aperture. -/
def suzukiPrimeCutoffAperture (X : ℕ) : ℝ :=
  Real.log ((X : ℝ) + 1) / 2

/-- The finite Euler product gives a sharp source-coordinate comparison: reciprocal Wold
volume dominates the logarithmic prime cutoff. -/
theorem log_natCast_add_one_le_primeWoldBoundaryVolumeBelow_succ_inv (X : ℕ) :
    Real.log ((X : ℝ) + 1) ≤
      (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ := by
  have hharm :
      Real.log ((X : ℝ) + 1) ≤
        ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ := by
    have h1 : Real.log ((X : ℝ) + 1) ≤ ((harmonic X : ℚ) : ℝ) := by
      have h := log_add_one_le_harmonic X
      have hcast : ((X : ℝ) + 1) = (((X + 1 : ℕ)) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      exact_mod_cast h
    have h2 :
        ((harmonic X : ℚ) : ℝ) =
          ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    linarith [h1, h2.le, h2.ge]
  calc
    Real.log ((X : ℝ) + 1) ≤
        ∑ m ∈ Finset.Icc 1 X, ((m : ℝ))⁻¹ := hharm
    _ ≤ ∏ p ∈ Nat.primesBelow (X + 1),
        (1 - ((p : ℝ))⁻¹)⁻¹ :=
      harmonic_sum_le_prod_primesBelow X
    _ = (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ := by
      rw [primeWoldBoundaryVolumeBelow_eq, Finset.prod_inv_distrib]

/-- Suzuki's half-log aperture is nonnegative at every integer cutoff. -/
theorem suzukiPrimeCutoffAperture_nonneg (X : ℕ) :
    0 ≤ suzukiPrimeCutoffAperture X := by
  rw [suzukiPrimeCutoffAperture]
  have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  exact div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)

/-- The Suzuki aperture is bounded by the reciprocal Wold boundary volume at the matching
prime cutoff. -/
theorem suzukiPrimeCutoffAperture_le_woldScale_succ (X : ℕ) :
    suzukiPrimeCutoffAperture X ≤
      (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ := by
  have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hlog_nonneg : 0 ≤ Real.log ((X : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hhalf :
      Real.log ((X : ℝ) + 1) / 2 ≤ Real.log ((X : ℝ) + 1) := by
    linarith
  exact hhalf.trans
    (log_natCast_add_one_le_primeWoldBoundaryVolumeBelow_succ_inv X)

/-- Every fixed aperture power is asymptotically bounded by the corresponding reciprocal-Wold
power. -/
theorem suzukiPrimeCutoffAperture_pow_isBigO_woldScale_succ_pow (K : ℕ) :
    (fun X => suzukiPrimeCutoffAperture X ^ K) =O[atTop]
      (fun X => (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ ^ K) := by
  apply IsBigO.of_bound 1
  filter_upwards [] with X
  have ha : 0 ≤ suzukiPrimeCutoffAperture X :=
    suzukiPrimeCutoffAperture_nonneg X
  have hb : 0 ≤ (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ :=
    inv_nonneg.mpr (primeWoldBoundaryVolumeBelow_pos (X + 1)).le
  have hpow :
      suzukiPrimeCutoffAperture X ^ K ≤
        (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ ^ K :=
    pow_le_pow_left₀ ha (suzukiPrimeCutoffAperture_le_woldScale_succ X) K
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha K),
    abs_of_nonneg (pow_nonneg hb K), one_mul] using hpow

/-- **Suzuki aperture--Rees conditioning no-go.** Every exact bounded linear sewing of the
positive and reflected prime-valuation Hellinger sectors has norm beyond every fixed power of
the physical Suzuki aperture. -/
theorem reflectedHellingerSewingOperatorNorm_beyondEverySuzukiAperturePower
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N => R N (primeValuationSquaredHellingerBelow c N)) =
        primeValuationSquaredHellingerBelow (-c))
    (K : ℕ) :
    (fun X => suzukiPrimeCutoffAperture X ^ K) =o[atTop]
      (fun X => ‖R (X + 1)‖) := by
  have hrees :
      (fun X => (primeWoldBoundaryVolumeBelow (X + 1))⁻¹ ^ K) =o[atTop]
        (fun X => ‖R (X + 1)‖) :=
    (reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder
      hc hcHalf R hsew K).comp_tendsto
        (Filter.tendsto_add_atTop_nat 1)
  exact
    (suzukiPrimeCutoffAperture_pow_isBigO_woldScale_succ_pow K).trans_isLittleO hrees

/-- Consequently, an exact reflected sewing family cannot have operator norm bounded by any
fixed power of the matching Suzuki aperture. -/
theorem reflectedHellingerSewingOperatorNorm_not_isBigO_suzukiAperturePower
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N => R N (primeValuationSquaredHellingerBelow c N)) =
        primeValuationSquaredHellingerBelow (-c))
    (K : ℕ) :
    ¬ (fun X => ‖R (X + 1)‖) =O[atTop]
      (fun X => suzukiPrimeCutoffAperture X ^ K) := by
  intro hpoly
  have hself :
      (fun X => suzukiPrimeCutoffAperture X ^ K) =o[atTop]
        (fun X => suzukiPrimeCutoffAperture X ^ K) :=
    (reflectedHellingerSewingOperatorNorm_beyondEverySuzukiAperturePower
      hc hcHalf R hsew K).trans_isBigO hpoly
  apply (isLittleO_irrefl ?_) hself
  exact Filter.Eventually.frequently <|
    (eventually_ge_atTop (1 : ℕ)).mono fun X hX =>
      pow_ne_zero K (by
        rw [suzukiPrimeCutoffAperture]
        exact div_ne_zero
          (Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by
            norm_num
            omega))
          (by norm_num))

end

end RHTower
