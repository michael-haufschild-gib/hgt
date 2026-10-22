import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyStokesRegulator
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# C*-closure blindness of the cofinal Gamma Bockstein

The signed ordinary-prime Gamma Bockstein tends to zero throughout the open
critical strip, while its absolute coefficients are summable exactly at neutral
grade. Thus its diagonal realization is always compact in the strip but is
trace-class only at the critical line. A norm-closed C*-ideal which absorbs
finite-rank ambiguity therefore cannot retain this summability wall.

The second obstruction is homological. A degree-minus-one homotopy which
contracts a cocycle forces every regulator annihilating boundaries to vanish on
that cocycle. Applied to the rational-adelic relative source, this rules out a
contraction of the retained period-one class.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- In the open critical strip, the absolute cofinal Gamma Bockstein coefficient
vanishes along the cofinite filter on ordinary primes. This is the sequence-level
content of compactness for its diagonal operator realization. -/
theorem primeGammaCofinalBocksteinMagnitude_tendsto_cofinite_zero
    {t : ℝ} (ht : |t| < 1) :
    Tendsto (primeGammaCofinalBocksteinMagnitude t)
      cofinite (𝓝 0) := by
  have hpNat : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Nat.Primes.coe_nat_injective.tendsto_cofinite
  have hpReal : Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop :=
    tendsto_natCast_atTop_atTop.comp hpNat
  have hmodel : Tendsto (fun p : Nat.Primes =>
      (p : ℝ) ^ (|t| - 1)) cofinite (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr ht)).comp hpReal
    have hexp : |t| - 1 = -(1 - |t|) := by ring
    change Tendsto (fun p : Nat.Primes =>
      (p : ℝ) ^ (-(1 - |t|))) cofinite (𝓝 0) at hpow
    simpa only [hexp] using hpow
  exact squeeze_zero
    (fun p => abs_nonneg _)
    (fun p => (primeGammaCofinalBocksteinMagnitude_bounds t p).2)
    hmodel

/-- The signed Gamma Bockstein coefficient itself vanishes along the cofinite
ordinary-prime filter throughout the open critical strip. -/
theorem primeGammaCofinalBocksteinCoefficient_tendsto_cofinite_zero
    {t : ℝ} (ht : |t| < 1) :
    Tendsto (primeGammaCofinalBocksteinCoefficient t)
      cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  change Tendsto (fun p : Nat.Primes =>
    |primeGammaCofinalBocksteinCoefficient t p|) cofinite (𝓝 0)
  exact (primeGammaCofinalBocksteinMagnitude_tendsto_cofinite_zero ht).congr'
    (Eventually.of_forall fun p => by rfl)

/-- A non-neutral cofinal Gamma Bockstein is never absolutely summable over
ordinary primes. -/
theorem not_summable_primeGammaCofinalBocksteinMagnitude
    {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (primeGammaCofinalBocksteinMagnitude t) := by
  intro hsum
  have hmass : Summable (primeGammaCofinalBocksteinSchattenMass 1 t) := by
    have heq : primeGammaCofinalBocksteinSchattenMass 1 t =
        primeGammaCofinalBocksteinMagnitude t := by
      funext p
      exact Real.rpow_one _
    rw [heq]
    exact hsum
  have hclass :=
    (summable_primeGammaCofinalBocksteinSchattenMass_iff
      (show (0 : ℝ) < 1 by norm_num)).mp hmass
  rcases hclass with hzero | horder
  · exact ht hzero
  · have habs : 0 < |t| := abs_pos.mpr ht
    norm_num at horder
    linarith

/-- Absolute summability of the cofinal Gamma Bockstein detects neutral grade
exactly. In the diagonal realization this is the trace-class wall. -/
theorem summable_primeGammaCofinalBocksteinMagnitude_iff
    {t : ℝ} :
    Summable (primeGammaCofinalBocksteinMagnitude t) ↔ t = 0 := by
  constructor
  · intro hsum
    by_contra ht
    exact not_summable_primeGammaCofinalBocksteinMagnitude ht hsum
  · rintro rfl
    have hzero : primeGammaCofinalBocksteinMagnitude 0 =
        fun _ : Nat.Primes => 0 := by
      funext p
      simp [primeGammaCofinalBocksteinMagnitude]
    rw [hzero]
    exact summable_zero

/-- A contracting homotopy on a cocycle annihilates every linear regulator
which vanishes on boundaries. -/
theorem regulator_eq_zero_of_contracts_cocycle
    {𝕜 C0 C1 C2 V : Type*}
    [Semiring 𝕜]
    [AddCommMonoid C0] [Module 𝕜 C0]
    [AddCommMonoid C1] [Module 𝕜 C1]
    [AddCommMonoid C2] [Module 𝕜 C2]
    [AddCommMonoid V] [Module 𝕜 V]
    (d0 : C0 →ₗ[𝕜] C1) (d1 : C1 →ₗ[𝕜] C2)
    (R : C1 →ₗ[𝕜] V) (h1 : C1 →ₗ[𝕜] C0) (h2 : C2 →ₗ[𝕜] C1)
    (κ : C1) (hκ : d1 κ = 0)
    (hR : R.comp d0 = 0)
    (hcontract : d0 (h1 κ) + h2 (d1 κ) = κ) :
    R κ = 0 := by
  rw [hκ, map_zero, add_zero] at hcontract
  rw [← hcontract]
  exact LinearMap.congr_fun hR (h1 κ)

/-- The period-one rational-adelic source cocycle admits no boundary primitive.
Consequently no degree-minus-one homotopy can satisfy `d h + h d = 1` on it. -/
theorem not_exists_ccmRationalAdelicPrimeRelativeCocycle_sourcePrimitive
    (p : Nat.Primes) :
    ¬ ∃ x,
      ccmRationalAdelicPrimeRelativeD0 p x =
        ccmRationalAdelicPrimeRelativeCocycle p := by
  rintro ⟨x, hx⟩
  have hzero := LinearMap.congr_fun
    (ccmRationalAdelicPrimeRelativeStokesRegulator_comp_D0 p) x
  rw [LinearMap.comp_apply, hx,
    ccmRationalAdelicPrimeRelativeStokesRegulator_cocycle] at hzero
  exact one_ne_zero hzero

end

end RHTower
