import GaloisForLFunctions.RHTower.HedenmalmThetaEndpointSourceDomainNoGo
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume

/-!
# Moving-horizon boundary energy of the theta aperture doublet

Canonical source-Hilbert landing fails because prime endpoints escape to the horizons
`x = ± log(p) / 2`.  Sampling the actual even/odd source doublet at its moving horizon recovers an
exact prime-harmonic boundary channel plus a positive, rapidly decaying theta residual.  Thus the
same `1/p` baseline found in the spectral marked-character receiver already exists on the physical
source side; it is not an artificially imposed prime weight.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

noncomputable section

namespace HedenmalmThetaSource

open HedenmalmContinuousAperture

/-- Even aperture endpoint at the left moving horizon. -/
theorem thetaApertureEvenEndpoint_leftHorizon (L : ℝ) :
    centeredApertureEvenEndpoint thetaSource L (-L / 2) =
      Real.exp (-L / 2) * (thetaSource.k 0 + thetaSource.k L) := by
  rw [centeredApertureEvenEndpoint,
    show -L / 2 + L / 2 = 0 by ring,
    show -L / 2 - L / 2 = -L by ring,
    thetaSource_even]

/-- Odd aperture endpoint at the left moving horizon. -/
theorem thetaApertureOddEndpoint_leftHorizon (L : ℝ) :
    centeredApertureOddEndpoint thetaSource L (-L / 2) =
      Real.exp (-L / 2) * (thetaSource.k 0 - thetaSource.k L) := by
  rw [centeredApertureOddEndpoint,
    show -L / 2 + L / 2 = 0 by ring,
    show -L / 2 - L / 2 = -L by ring,
    thetaSource_even]

/-- **Moving-horizon Pythagoras law.** The physical endpoint doublet has one universal boundary
atom `k(0)` and one decaying theta-tail atom `k(L)`. -/
theorem thetaApertureEndpoint_leftHorizon_energy (L : ℝ) :
    centeredApertureEvenEndpoint thetaSource L (-L / 2) ^ 2 +
        centeredApertureOddEndpoint thetaSource L (-L / 2) ^ 2 =
      2 * Real.exp (-L) * (thetaSource.k 0 ^ 2 + thetaSource.k L ^ 2) := by
  rw [thetaApertureEvenEndpoint_leftHorizon,
    thetaApertureOddEndpoint_leftHorizon, mul_pow, mul_pow]
  have hexp : Real.exp (-L / 2) ^ 2 = Real.exp (-L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- At prime aperture, moving-horizon energy has the exact `1/p` scale. -/
theorem primeThetaApertureEndpoint_leftHorizon_energy (p : Nat.Primes) :
    centeredApertureEvenEndpoint thetaSource (Real.log (p.1 : ℕ))
          (-Real.log (p.1 : ℕ) / 2) ^ 2 +
        centeredApertureOddEndpoint thetaSource (Real.log (p.1 : ℕ))
          (-Real.log (p.1 : ℕ) / 2) ^ 2 =
      2 / (p.1 : ℝ) *
        (thetaSource.k 0 ^ 2 + thetaSource.k (Real.log (p.1 : ℕ)) ^ 2) := by
  rw [thetaApertureEndpoint_leftHorizon_energy]
  have hp0 : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.pos
  rw [Real.exp_neg, Real.exp_log hp0]
  ring

/-- One physical moving-horizon prime channel. -/
def thetaMovingHorizonPrimeTerm (p : ℕ) : ℝ :=
  centeredApertureEvenEndpoint thetaSource (Real.log p) (-Real.log p / 2) ^ 2 +
    centeredApertureOddEndpoint thetaSource (Real.log p) (-Real.log p / 2) ^ 2

theorem thetaMovingHorizonPrimeTerm_eq {p : ℕ} (hp : p.Prime) :
    thetaMovingHorizonPrimeTerm p =
      2 / (p : ℝ) * (thetaSource.k 0 ^ 2 + thetaSource.k (Real.log p) ^ 2) := by
  let P : Nat.Primes := ⟨p, hp⟩
  simpa only [thetaMovingHorizonPrimeTerm, P] using
    primeThetaApertureEndpoint_leftHorizon_energy P

/-- Finite physical moving-horizon energy on the canonical prime exhaustion. -/
def thetaMovingHorizonCutoffEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow N, thetaMovingHorizonPrimeTerm p

/-- Positive theta-tail correction to universal prime-harmonic boundary mass. -/
def thetaMovingHorizonResidualEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow N,
    2 / (p : ℝ) * thetaSource.k (Real.log p) ^ 2

theorem thetaMovingHorizonResidualEnergy_nonneg (N : ℕ) :
    0 ≤ thetaMovingHorizonResidualEnergy N := by
  rw [thetaMovingHorizonResidualEnergy]
  apply Finset.sum_nonneg
  intro p hp
  have hpprime := Nat.prime_of_mem_primesBelow hp
  positivity

/-- **Exact physical boundary decomposition.** Source-side horizon energy equals the universal
prime-harmonic channel plus a nonnegative theta residual. -/
theorem thetaMovingHorizonCutoffEnergy_eq (N : ℕ) :
    thetaMovingHorizonCutoffEnergy N =
      2 * thetaSource.k 0 ^ 2 * GaloisForLFunctions.primeReciprocalPartialSum N +
        thetaMovingHorizonResidualEnergy N := by
  rw [thetaMovingHorizonCutoffEnergy, GaloisForLFunctions.primeReciprocalPartialSum,
    thetaMovingHorizonResidualEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [thetaMovingHorizonPrimeTerm_eq (Nat.prime_of_mem_primesBelow hp)]
  ring

theorem thetaMovingHorizonCutoffEnergy_ge_primeMass (N : ℕ) :
    2 * thetaSource.k 0 ^ 2 * GaloisForLFunctions.primeReciprocalPartialSum N ≤
      thetaMovingHorizonCutoffEnergy N := by
  rw [thetaMovingHorizonCutoffEnergy_eq]
  exact le_add_of_nonneg_right (thetaMovingHorizonResidualEnergy_nonneg N)

/-- Physical moving-horizon energy diverges.  The divergence is forced by its exact universal
`k(0)^2/p` boundary component, not by the negligible translated theta tails. -/
theorem tendsto_thetaMovingHorizonCutoffEnergy_atTop :
    Tendsto thetaMovingHorizonCutoffEnergy atTop atTop := by
  have hk0 : 0 < 2 * thetaSource.k 0 ^ 2 := by
    have := thetaSource.pos_k 0
    positivity
  have hbase : Tendsto
      (fun N => 2 * thetaSource.k 0 ^ 2 *
        GaloisForLFunctions.primeReciprocalPartialSum N) atTop atTop :=
    GaloisForLFunctions.tendsto_primeReciprocalPartialSum_atTop.const_mul_atTop hk0
  refine tendsto_atTop_mono' atTop ?_ hbase
  exact Eventually.of_forall thetaMovingHorizonCutoffEnergy_ge_primeMass

/-- The translated theta tail is cubic-summable after the prime-normal horizon scaling. -/
theorem thetaMovingHorizonResidualTerm_le (p : Nat.Primes) :
    2 / (p.1 : ℝ) * thetaSource.k (Real.log (p.1 : ℕ)) ^ 2 ≤
      2 * thetaCuspDerivativeExpConstant 0 ^ 2 * ((p.1 : ℝ) ^ 3)⁻¹ := by
  have hp0 : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.pos
  have hlog0 : 0 ≤ Real.log (p.1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have htheta := abs_thetaCuspFullSource_le (Real.log (p.1 : ℕ))
  rw [abs_of_pos (thetaCuspFullSource_pos _), abs_of_nonneg hlog0,
    Real.exp_neg, Real.exp_log hp0] at htheta
  have hk : thetaSource.k (Real.log (p.1 : ℕ)) ≤
      thetaCuspDerivativeExpConstant 0 / (p.1 : ℝ) := by
    simpa only [thetaSource_k, div_eq_mul_inv] using htheta
  have hsquare : thetaSource.k (Real.log (p.1 : ℕ)) ^ 2 ≤
      (thetaCuspDerivativeExpConstant 0 / (p.1 : ℝ)) ^ 2 :=
    (sq_le_sq₀ (thetaSource.pos_k _).le
      (div_nonneg (thetaCuspDerivativeExpConstant_nonneg 0) hp0.le)).2 hk
  calc
    2 / (p.1 : ℝ) * thetaSource.k (Real.log (p.1 : ℕ)) ^ 2
        ≤ 2 / (p.1 : ℝ) *
            (thetaCuspDerivativeExpConstant 0 / (p.1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 2 * thetaCuspDerivativeExpConstant 0 ^ 2 * ((p.1 : ℝ) ^ 3)⁻¹ := by
      field_simp [hp0.ne']

/-- **Universal-atom rigidity.** The entire moving-horizon theta residual is summable.  Hence all
non-Hilbert source mass is carried by the single common boundary atom `k(0)/sqrt p`; quotienting
that atom would remove precisely the channel capable of detecting radial spectral displacement. -/
theorem summable_thetaMovingHorizonResidual :
    Summable (fun p : Nat.Primes =>
      2 / (p.1 : ℝ) * thetaSource.k (Real.log (p.1 : ℕ)) ^ 2) := by
  have hmajor : Summable (fun p : Nat.Primes =>
      2 * thetaCuspDerivativeExpConstant 0 ^ 2 * ((p.1 : ℝ) ^ 3)⁻¹) :=
    ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ))).comp_injective
      Subtype.val_injective).mul_left (2 * thetaCuspDerivativeExpConstant 0 ^ 2)
  exact Summable.of_nonneg_of_le
    (fun p => by positivity) thetaMovingHorizonResidualTerm_le hmajor

end HedenmalmThetaSource

end

end RHTower
