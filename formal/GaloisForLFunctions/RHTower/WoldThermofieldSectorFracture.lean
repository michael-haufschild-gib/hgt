import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture

open Filter Topology Asymptotics
open GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

theorem tendsto_primeValuationHellingerBelow_zero_of_neg
    {c : ℝ} (hc : c < 0) :
    Tendsto (primeValuationHellingerBelow c) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ :=
    (primeValuationHellingerBelow_isTheta_halfNormal_of_neg hc).isBigO.bound
  have hsqrt : Tendsto (fun N => Real.sqrt (primeWoldBoundaryVolumeBelow N))
      atTop (𝓝 0) := by
    change Tendsto (Real.sqrt ∘ primeWoldBoundaryVolumeBelow) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        tendsto_primeWoldBoundaryVolumeBelow_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N => Real.sqrt_nonneg _
  · filter_upwards [hC] with N hN
    simpa only [primeValuationHellingerBelow, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg
        (primeValuationSquaredHellingerBelow c N))] using hN
  · simpa using tendsto_const_nhds.mul hsqrt

theorem tendsto_primeValuationHellingerBelow_zero_of_pos
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    Tendsto (primeValuationHellingerBelow c) atTop (𝓝 0) := by
  have h := (primeValuationHellingerBelow_reesAllOrdersFlat_of_pos hc hcHalf) 0
  have h' : (primeValuationHellingerBelow c) =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    simpa using h
  exact (isLittleO_one_iff ℝ).mp h'

/-- Every noncritical radial thermofield overlap vanishes cofinally. -/
theorem tendsto_primeValuationHellingerBelow_zero_of_ne
    {c : ℝ} (hcHalf : c < 1 / 2) (hc0 : c ≠ 0) :
    Tendsto (primeValuationHellingerBelow c) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hc0 with hc | hc
  · exact tendsto_primeValuationHellingerBelow_zero_of_neg hc
  · exact tendsto_primeValuationHellingerBelow_zero_of_pos hc hcHalf

/-- Complete overlap-sector law: critical finite thermofield vectors have limiting overlap one;
every distinct coherent radial sector has limiting overlap zero. -/
theorem tendsto_primeValuationHellingerBelow_ite
    {c : ℝ} (hcHalf : c < 1 / 2) :
    Tendsto (primeValuationHellingerBelow c) atTop
      (𝓝 (if c = 0 then 1 else 0)) := by
  by_cases hc0 : c = 0
  · subst c
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [] with N
    simpa using (primeValuationHellingerBelow_zero N).symm
  · simpa [hc0] using tendsto_primeValuationHellingerBelow_zero_of_ne hcHalf hc0

theorem geometricHellingerAffinity_sq_primeRadial
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.geometricHellingerAffinity
        (primeRadialCriticalMass p) (primeRadialTwistedMass c p) ^ 2 =
      primeValuationSquaredHellingerFactor c p := by
  have hq0 : 0 ≤ primeRadialCriticalMass p := by
    exact inv_nonneg.mpr (by exact_mod_cast p.2.pos.le)
  have hq1 : primeRadialCriticalMass p < 1 := by
    exact (inv_lt_one₀ (by exact_mod_cast p.2.pos)).2
      (by exact_mod_cast p.2.one_lt)
  have hr0 : 0 ≤ primeRadialTwistedMass c p := by
    exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hr1 : primeRadialTwistedMass c p < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by linarith)
  have hu0 : 0 ≤ primeRadialCrossMass c p := by
    exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hsqrt :
      Real.sqrt (primeRadialCriticalMass p * primeRadialTwistedMass c p) =
        primeRadialCrossMass c p := by
    rw [← primeRadialCrossMass_sq c p, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hu0]
  have hnum : 0 ≤
      (1 - primeRadialCriticalMass p) *
        (1 - primeRadialTwistedMass c p) :=
    mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hr1.le)
  rw [GaloisForLFunctions.HTGeometry.geometricHellingerAffinity,
    primeValuationSquaredHellingerFactor, squaredHellingerAffinity,
    hsqrt, div_pow, Real.sq_sqrt hnum]

theorem geometricHellingerAffinity_primeRadial_nonneg
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    0 ≤ GaloisForLFunctions.HTGeometry.geometricHellingerAffinity
      (primeRadialCriticalMass p) (primeRadialTwistedMass c p) := by
  rw [GaloisForLFunctions.HTGeometry.geometricHellingerAffinity]
  apply div_nonneg (Real.sqrt_nonneg _)
  have hq0 : 0 ≤ primeRadialCriticalMass p := by
    exact inv_nonneg.mpr (by exact_mod_cast p.2.pos.le)
  have hr0 : 0 ≤ primeRadialTwistedMass c p := by
    exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hq1 : primeRadialCriticalMass p < 1 := by
    exact (inv_lt_one₀ (by exact_mod_cast p.2.pos)).2
      (by exact_mod_cast p.2.one_lt)
  have hr1 : primeRadialTwistedMass c p < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by linarith)
  have hsqrt : Real.sqrt
      (primeRadialCriticalMass p * primeRadialTwistedMass c p) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    nlinarith
  linarith

private def primeOfBelow {N : ℕ} (p : ↑(Nat.primesBelow N)) : Nat.Primes :=
  ⟨p.1, Nat.prime_of_mem_primesBelow p.2⟩

/-- The finite product in the Wold thermofield vector state is exactly the canonical finite-prime
Hellinger affinity. -/
theorem prod_geometricHellingerAffinity_primeRadial
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    (∏ p : ↑(Nat.primesBelow N),
      GaloisForLFunctions.HTGeometry.geometricHellingerAffinity
        (primeRadialCriticalMass (primeOfBelow p))
        (primeRadialTwistedMass c (primeOfBelow p))) =
      primeValuationHellingerBelow c N := by
  let A : ℝ := ∏ p : ↑(Nat.primesBelow N),
    GaloisForLFunctions.HTGeometry.geometricHellingerAffinity
      (primeRadialCriticalMass (primeOfBelow p))
      (primeRadialTwistedMass c (primeOfBelow p))
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    apply Finset.prod_nonneg
    intro p hp
    exact geometricHellingerAffinity_primeRadial_nonneg hcHalf (primeOfBelow p)
  have hA2 : A ^ 2 = primeValuationSquaredHellingerBelow c N := by
    dsimp only [A]
    rw [← Finset.prod_pow]
    calc
      (∏ p : ↑(Nat.primesBelow N),
          GaloisForLFunctions.HTGeometry.geometricHellingerAffinity
            (primeRadialCriticalMass (primeOfBelow p))
            (primeRadialTwistedMass c (primeOfBelow p)) ^ 2) =
          ∏ p : ↑(Nat.primesBelow N),
            primeValuationSquaredHellingerFactor c (primeOfBelow p) := by
              apply Finset.prod_congr rfl
              intro p hp
              exact geometricHellingerAffinity_sq_primeRadial hcHalf (primeOfBelow p)
      _ = ∏ p : ↑(Nat.primesBelow N),
          primeValuationSquaredHellingerFactorNat c p.1 := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [primeValuationSquaredHellingerFactorNat_of_prime c
              (Nat.prime_of_mem_primesBelow p.2)]
            congr 2
      _ = ∏ p ∈ Nat.primesBelow N,
          primeValuationSquaredHellingerFactorNat c p := by
            rw [show (Finset.univ : Finset ↑(Nat.primesBelow N)) =
              (Nat.primesBelow N).attach by ext p; simp,
              Finset.prod_attach]
      _ = primeValuationSquaredHellingerBelow c N := rfl
  rw [primeValuationHellingerBelow, ← hA2,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hA0]

/-- Critical finite-prime Wold half-density, in the literal finite occupation carrier. -/
def primeCriticalFiniteThermofieldHalfDensity (N : ℕ) :=
  HTGeometry.finiteOccupationNormalizedHalfDensity
    (fun p : ↑(Nat.primesBelow N) =>
      primeRadialCriticalMass (primeOfBelow p))
    (fun p => inv_nonneg.mpr (by exact_mod_cast (primeOfBelow p).2.pos.le))
    (fun p => (inv_lt_one₀ (by exact_mod_cast (primeOfBelow p).2.pos)).2
      (by exact_mod_cast (primeOfBelow p).2.one_lt))

/-- Coherently twisted finite-prime Wold half-density. -/
def primeTwistedFiniteThermofieldHalfDensity
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :=
  HTGeometry.finiteOccupationNormalizedHalfDensity
    (fun p : ↑(Nat.primesBelow N) =>
      primeRadialTwistedMass c (primeOfBelow p))
    (fun p => Real.rpow_nonneg (by exact_mod_cast (primeOfBelow p).2.pos.le) _)
    (fun p => Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (primeOfBelow p).2.one_lt) (by linarith))

/-- Exact finite-prime vector realization of the Hellinger overlap `(24)`. -/
theorem inner_primeFiniteThermofieldHalfDensity
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    inner ℂ (primeCriticalFiniteThermofieldHalfDensity N)
      (primeTwistedFiniteThermofieldHalfDensity hcHalf N) =
        (primeValuationHellingerBelow c N : ℂ) := by
  rw [primeCriticalFiniteThermofieldHalfDensity,
    primeTwistedFiniteThermofieldHalfDensity,
    GaloisForLFunctions.HTGeometry.inner_finiteOccupationNormalizedHalfDensity]
  exact_mod_cast prod_geometricHellingerAffinity_primeRadial hcHalf N

/-- Cofinal vector-overlap sector fracture: the critical and twisted finite thermofield vectors
have limiting overlap one exactly in the critical sector and zero in every other radial sector. -/
theorem tendsto_inner_primeFiniteThermofieldHalfDensity
    {c : ℝ} (hcHalf : c < 1 / 2) :
    Tendsto (fun N => inner ℂ (primeCriticalFiniteThermofieldHalfDensity N)
      (primeTwistedFiniteThermofieldHalfDensity hcHalf N)) atTop
      (𝓝 ((if c = 0 then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto
    (if c = 0 then (1 : ℝ) else 0)).comp
      (tendsto_primeValuationHellingerBelow_ite hcHalf)
  refine h.congr' (Filter.Eventually.of_forall fun N => ?_)
  change (primeValuationHellingerBelow c N : ℂ) =
    inner ℂ (primeCriticalFiniteThermofieldHalfDensity N)
      (primeTwistedFiniteThermofieldHalfDensity hcHalf N)
  exact (inner_primeFiniteThermofieldHalfDensity hcHalf N).symm

end

end RHTower
