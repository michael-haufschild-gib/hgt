import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesComplexHalfPlaneCurrent
import GaloisForLFunctions.RHTower.Deninger.DeningerCriticalFloquetVonMangoldtWall

/-!
# Gamma-sewn Stokes current, Deninger time, and the singular corona

The complex Euler current produced by the Gamma-sewn Stokes connection admits an exact local-time
interpretation.  A compactly supported Deninger time test lifts to a finite Kummer vector by
sampling it on the positive prime-power axes.  Pairing the complex Euler current with this lift is
exactly the finite Euler--Laplace sampling of the same test.  On the positive half-plane the
physical sewn dual, after Stokes transport and Kummer phase, therefore has the identical local-time
response.  At zero Laplace parameter the prime response welds to the independently constructed
Deninger prime distribution, and adjoining the archimedean distribution gives the complete local
trace distribution.

The scalar constant-one direction is different.  Seeing value one on the first `N` powers of even
one prime forces zeroth height seminorm at least `N`.  Hence no uniformly bounded family of rapid
Kummer tests can approach the constant-one corona through exact finite interpolation.  The wall at
`Re(s) = 1` is therefore not loss of the Euler current or of its compact local trace: it is a
quantitatively singular unitization problem.

No Xi zero, analytic continuation of zeta, positivity premise, or RH-equivalent hypothesis enters
these statements.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions FourierTransform

noncomputable section

namespace RHTower

/-! ## Exact prime-power time coordinate -/

/-- The Euler coefficient is the Laplace weight at the corresponding Deninger orbit time. -/
theorem primePowerFluxTerm_eq_deningerTimeLaplace
    (s : ℂ) (pk : Nat.Primes × ℕ) :
    primePowerFluxTerm s pk =
      (Real.log (pk.1 : ℕ) : ℂ) *
        Complex.exp (-s *
          (deningerPrimePowerTime
            (deningerEulerPrimePowerIndex pk) : ℂ)) := by
  have hp0 : (((pk.1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast pk.1.2.ne_zero
  rw [primePowerFluxTerm, deningerPrimePowerTime_euler]
  rw [Complex.cpow_def_of_ne_zero hp0]
  rw [← Complex.natCast_log]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ## Compact time tests as rapid Kummer vectors -/

/-- Prime/exponent atoms whose Deninger time lies in a fixed compact set. -/
noncomputable def gammaSewnMobiusApertureStokesTimeActiveFinset
    (K : Compacts ℝ) : Finset (Nat.Primes × ℕ) :=
  (deningerPrimeActiveFinset K).preimage
    deningerEulerPrimePowerIndex
    (Set.injOn_of_injective deningerEulerPrimePowerIndex_injective)

@[simp]
theorem mem_gammaSewnMobiusApertureStokesTimeActiveFinset
    (K : Compacts ℝ) (pk : Nat.Primes × ℕ) :
    pk ∈ gammaSewnMobiusApertureStokesTimeActiveFinset K ↔
      deningerPrimePowerTime
          (deningerEulerPrimePowerIndex pk) ∈ (K : Set ℝ) := by
  simp [gammaSewnMobiusApertureStokesTimeActiveFinset]

/-- A fixed-support Deninger time test sampled on positive prime-power Kummer axes. -/
noncomputable def gammaSewnMobiusApertureStokesCompactTimeLift
    (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) : DeningerHeightKothe :=
  ∑ pk ∈ gammaSewnMobiusApertureStokesTimeActiveFinset K,
    (φ (deningerPrimePowerTime (deningerEulerPrimePowerIndex pk)) : ℂ) •
      deningerKotheDelta deningerHeightKotheData
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk)

/-- The compact time lift recovers the time-test value on every prime-power axis, including the
zero values outside the compact support. -/
theorem gammaSewnMobiusApertureStokesCompactTimeLift_primePowerAxis
    (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ))
    (pk : Nat.Primes × ℕ) :
    ((gammaSewnMobiusApertureStokesCompactTimeLift K φ :
        DeningerHeightKothe) : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk) =
      (φ (deningerPrimePowerTime
        (deningerEulerPrimePowerIndex pk)) : ℂ) := by
  classical
  by_cases hpk :
      pk ∈ gammaSewnMobiusApertureStokesTimeActiveFinset K
  · rw [gammaSewnMobiusApertureStokesCompactTimeLift,
      Submodule.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single pk]
    · simp
    · intro q hq hne
      have haxis :
          gammaSewnMobiusApertureStokesPrimePowerAxis pk ≠
            gammaSewnMobiusApertureStokesPrimePowerAxis q := by
        intro h
        exact hne
          (gammaSewnMobiusApertureStokesPrimePowerAxis_injective h.symm)
      change
        (φ (deningerPrimePowerTime
          (deningerEulerPrimePowerIndex q)) : ℂ) *
          (Pi.single
            (gammaSewnMobiusApertureStokesPrimePowerAxis q) (1 : ℂ) :
              DeningerPrimeLattice → ℂ)
              (gammaSewnMobiusApertureStokesPrimePowerAxis pk) = 0
      rw [Pi.single_eq_of_ne haxis, mul_zero]
    · exact fun h => (h hpk).elim
  · have htime :
        deningerPrimePowerTime
            (deningerEulerPrimePowerIndex pk) ∉ (K : Set ℝ) := by
      simpa using hpk
    have hzero :
        φ (deningerPrimePowerTime
          (deningerEulerPrimePowerIndex pk)) = 0 :=
      φ.zero_on_compl htime
    rw [gammaSewnMobiusApertureStokesCompactTimeLift,
      Submodule.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_zero]
    · simp [hzero]
    · intro q hq
      have hne :
          gammaSewnMobiusApertureStokesPrimePowerAxis pk ≠
            gammaSewnMobiusApertureStokesPrimePowerAxis q := by
        exact fun h => hpk
          ((gammaSewnMobiusApertureStokesPrimePowerAxis_injective h).symm ▸ hq)
      simp [deningerKotheDelta_coe, Pi.single_eq_of_ne hne]

/-! ## Exact Euler--Laplace pushforward -/

/-- Finite Euler--Laplace sampling of a fixed compact time stage. -/
def gammaSewnMobiusApertureStokesCompactTimePairing
    (s : ℂ) (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) : ℂ :=
  ∑ pk ∈ gammaSewnMobiusApertureStokesTimeActiveFinset K,
    (Real.log (pk.1 : ℕ) : ℂ) *
      Complex.exp (-s *
        (deningerPrimePowerTime
          (deningerEulerPrimePowerIndex pk) : ℂ)) *
      (φ (deningerPrimePowerTime
        (deningerEulerPrimePowerIndex pk)) : ℂ)

/-- **Kummer-to-time pushforward.**  The complex Euler current on a compact time lift is exactly
the finite Euler--Laplace response, for every complex parameter. -/
theorem gammaSewnMobiusApertureStokesComplexEulerDualPairing_compactTimeLift
    (s : ℂ) (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) :
    gammaSewnMobiusApertureStokesComplexEulerDualPairing s
        (gammaSewnMobiusApertureStokesCompactTimeLift K φ) =
      gammaSewnMobiusApertureStokesCompactTimePairing s K φ := by
  rw [gammaSewnMobiusApertureStokesComplexEulerDualPairing,
    gammaSewnMobiusApertureStokesCompactTimePairing]
  rw [tsum_eq_sum
    (s := gammaSewnMobiusApertureStokesTimeActiveFinset K)]
  · apply Finset.sum_congr rfl
    intro pk hpk
    rw [gammaSewnMobiusApertureStokesCompactTimeLift_primePowerAxis,
      primePowerFluxTerm_eq_deningerTimeLaplace]
  · intro pk hpk
    have htime :
        deningerPrimePowerTime
            (deningerEulerPrimePowerIndex pk) ∉ (K : Set ℝ) := by
      simpa using hpk
    have hzero :
        φ (deningerPrimePowerTime
          (deningerEulerPrimePowerIndex pk)) = 0 :=
      φ.zero_on_compl htime
    rw [gammaSewnMobiusApertureStokesCompactTimeLift_primePowerAxis,
      hzero]
    simp

/-- **Physical sewn-to-time law.**  Positive-chamber Stokes transport followed by vertical Kummer
phase has exactly the compact Euler--Laplace response. -/
theorem gammaSewnMobiusApertureStokesDualFeaturePairing_phase_positiveChamber_compactTimeLift
    {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ)
    (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) :
    gammaSewnMobiusApertureStokesDualFeaturePairing sigma
        (gammaSewnMobiusApertureStokesPositiveChamberOperator sigma hsigma
          (gammaSewnMobiusApertureStokesKummerPhaseOperator t
            (gammaSewnMobiusApertureStokesCompactTimeLift K φ))) =
      gammaSewnMobiusApertureStokesCompactTimePairing
        ((sigma : ℂ) + (t : ℂ) * Complex.I) K φ := by
  rw [
    gammaSewnMobiusApertureStokesDualFeaturePairing_phase_positiveChamber_eq_complexEuler,
    gammaSewnMobiusApertureStokesComplexEulerDualPairing_compactTimeLift]

/-! ## Weld to the independently constructed Deninger distribution -/

/-- At zero Laplace parameter, the finite time response is exactly Deninger's locally finite
von-Mangoldt distribution. -/
theorem deningerPrimeLefschetzDistribution_eq_gammaSewnCompactTimePairing_zero
    (K : Compacts ℝ)
    (K_sub : (K : Set ℝ) ⊆ (deningerTimeDomain : Set ℝ))
    (φ : 𝓓_{K}(ℝ, ℝ)) :
    deningerPrimeLefschetzDistribution
        (TestFunction.ofSupportedIn K_sub φ) =
      gammaSewnMobiusApertureStokesCompactTimePairing 0 K φ := by
  rw [deningerPrimeLefschetzDistribution_apply]
  rw [← tsum_prime_iterate_eq_deningerPrimePower_vonMangoldt
    (fun t : ℝ =>
      ((TestFunction.ofSupportedIn K_sub φ) t : ℂ))]
  rw [gammaSewnMobiusApertureStokesCompactTimePairing]
  rw [tsum_eq_sum
    (s := gammaSewnMobiusApertureStokesTimeActiveFinset K)]
  · apply Finset.sum_congr rfl
    intro pk hpk
    rw [← deningerPrimePowerTime_euler pk]
    simp
  · intro pk hpk
    have htime :
        deningerPrimePowerTime
            (deningerEulerPrimePowerIndex pk) ∉ (K : Set ℝ) := by
      simpa using hpk
    have hzero :
        φ (deningerPrimePowerTime
          (deningerEulerPrimePowerIndex pk)) = 0 :=
      φ.zero_on_compl htime
    have hzero' :
        φ ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ)) = 0 := by
      rw [← deningerPrimePowerTime_euler pk]
      exact hzero
    simp [hzero']

/-- The zero-parameter Gamma-sewn current plus the archimedean local term is the complete
prime--archimedean Deninger Lefschetz distribution on every fixed compact-support stage. -/
theorem deningerPrimeArchimedeanLefschetzDistribution_eq_gammaSewnCompletedCompactTime
    (K : Compacts ℝ)
    (K_sub : (K : Set ℝ) ⊆ (deningerTimeDomain : Set ℝ))
    (φ : 𝓓_{K}(ℝ, ℝ)) :
    deningerPrimeArchimedeanLefschetzDistribution
        (TestFunction.ofSupportedIn K_sub φ) =
      gammaSewnMobiusApertureStokesComplexEulerDualPairing 0
          (gammaSewnMobiusApertureStokesCompactTimeLift K φ) +
        deningerArchimedeanLefschetzDistribution
          (TestFunction.ofSupportedIn K_sub φ) := by
  rw [deningerPrimeArchimedeanLefschetzDistribution]
  change
    deningerPrimeLefschetzDistribution
          (TestFunction.ofSupportedIn K_sub φ) +
        deningerArchimedeanLefschetzDistribution
          (TestFunction.ofSupportedIn K_sub φ) = _
  rw [deningerPrimeLefschetzDistribution_eq_gammaSewnCompactTimePairing_zero,
    ← gammaSewnMobiusApertureStokesComplexEulerDualPairing_compactTimeLift]

/-! ## Quantitative singular-corona obstruction -/

/-- Positive powers on the prime-two ray, used to audit the constant-one corona direction. -/
def gammaSewnMobiusApertureStokesCoronaAxis (e : ℕ) :
    DeningerPrimeLattice :=
  gammaSewnMobiusApertureStokesPrimePowerAxis
    (⟨2, Nat.prime_two⟩, e)

theorem gammaSewnMobiusApertureStokesCoronaAxis_injective :
    Function.Injective gammaSewnMobiusApertureStokesCoronaAxis := by
  intro e f h
  have hp := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  exact congrArg Prod.snd hp

/-- Seeing amplitude at least `c` on the first `N` corona axes costs at least `N c` in the zeroth
height seminorm. -/
theorem gammaSewnMobiusApertureStokesCorona_finiteVisibility_lowerBound
    (N : ℕ) (a : DeningerHeightKothe) (c : ℝ)
    (hcoord : ∀ e ∈ Finset.range N,
      c ≤ ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesCoronaAxis e)‖) :
    (N : ℝ) * c ≤ deningerHeightSeminorm 0 a := by
  have hfinite :
      ∑ e ∈ Finset.range N,
          ‖(a : DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesCoronaAxis e)‖ ≤
        deningerHeightSeminorm 0 a := by
    rw [deningerHeightSeminorm_zero_eq]
    have himage :
        (∑ m ∈ Finset.image
            gammaSewnMobiusApertureStokesCoronaAxis (Finset.range N),
          ‖(a : DeningerPrimeLattice → ℂ) m‖) =
        ∑ e ∈ Finset.range N,
          ‖(a : DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesCoronaAxis e)‖ :=
      Finset.sum_image
        (Set.injOn_of_injective
          gammaSewnMobiusApertureStokesCoronaAxis_injective)
    rw [← himage]
    exact (deningerHeightKothe_summable_norm a).sum_le_tsum
      (Finset.image
        gammaSewnMobiusApertureStokesCoronaAxis (Finset.range N))
      (fun _ _ => norm_nonneg _)
  calc
    (N : ℝ) * c = ∑ e ∈ Finset.range N, c := by simp
    _ ≤ ∑ e ∈ Finset.range N,
        ‖(a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesCoronaAxis e)‖ := by
      exact Finset.sum_le_sum fun e he => hcoord e he
    _ ≤ deningerHeightSeminorm 0 a := hfinite

/-- Exact visibility of the first `N` constant-one corona coordinates forces seminorm at least
`N`. -/
theorem gammaSewnMobiusApertureStokesCorona_exactVisibility_lowerBound
    (N : ℕ) (a : DeningerHeightKothe)
    (hcoord : ∀ e ∈ Finset.range N,
      (a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesCoronaAxis e) = 1) :
    (N : ℝ) ≤ deningerHeightSeminorm 0 a := by
  have h :=
    gammaSewnMobiusApertureStokesCorona_finiteVisibility_lowerBound
      N a 1 (fun e he => by rw [hcoord e he]; norm_num)
  simpa using h

/-- **Singular-corona law.**  No uniformly zeroth-seminorm-bounded family of rapid Kummer tests can
interpolate the constant-one direction on arbitrarily long initial prime-two rays. -/
theorem gammaSewnMobiusApertureStokes_no_uniformlyBounded_coronaApproximation :
    ¬ ∃ C : ℝ, ∀ N : ℕ, ∃ a : DeningerHeightKothe,
      deningerHeightSeminorm 0 a ≤ C ∧
        ∀ e ∈ Finset.range N,
          (a : DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesCoronaAxis e) = 1 := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hNC⟩ := exists_nat_gt C
  obtain ⟨a, ha, hcoord⟩ := hC N
  have hN :=
    gammaSewnMobiusApertureStokesCorona_exactVisibility_lowerBound
      N a hcoord
  linarith

end RHTower
