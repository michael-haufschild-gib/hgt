import GaloisForLFunctions.HTGeometry.PolarizedTangentGauge
import GaloisForLFunctions.HTGeometry.PrimeOccupationPolarizedGammaPhaseSurvival
import GaloisForLFunctions.HTGeometry.PrimeValuationLevelStructure

/-!
# Cofinal completion of the prime occupation sums

The occupation vectors supported in a finite prime set are the smooth part of the occupation
monoid, and every finite set of occupation vectors is supported in all large enough prime sets.
Above level one the occupation reciprocals are absolutely summable over the whole monoid, so every
occupation power sum converges cofinally to its completed value.

The intensity is a product over the squared occupations, so its logarithm converges cofinally
directly.  The tangent-normalized polarized phase has, by the odd jet split, a logarithm which is
the series of odd occupation power sums from the third on; those are dominated uniformly in the
prime set by the level-two mass, so the whole series converges cofinally term by term.

* `GaloisForLFunctions.occupationSupported`, `GaloisForLFunctions.cofinal_occupationSupported`;
* `GaloisForLFunctions.tendsto_smoothPowerSum`;
* `GaloisForLFunctions.tendsto_smoothLogIntensity`;
* `GaloisForLFunctions.tendsto_smoothOddJetSeries`.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-! ### The smooth part of the occupation monoid -/

/-- Occupation vectors supported in a finite prime set. -/
def occupationSupported (S : Finset Nat.Primes) : Set (Nat.Primes →₀ ℕ) := {ν | ν.support ⊆ S}

/-- **Every finite set of occupation vectors is eventually smooth.** -/
theorem cofinal_occupationSupported (F : Finset (Nat.Primes →₀ ℕ)) :
    ∀ᶠ S : Finset Nat.Primes in atTop,
      (F : Set (Nat.Primes →₀ ℕ)) ⊆ occupationSupported S := by
  classical
  refine Filter.eventually_atTop.2 ⟨F.biUnion fun ν => ν.support, fun S hS ν hν => ?_⟩
  intro p hp
  exact hS (Finset.mem_biUnion.2 ⟨ν, Finset.mem_coe.1 hν, hp⟩)

/-- The reciprocal of the integer represented by an occupation vector. -/
def occupationRecip (ν : Nat.Primes →₀ ℕ) : ℂ := HTGeometry.nomeMonomial primeLinearNome ν

theorem occupationRecip_eq (ν : Nat.Primes →₀ ℕ) :
    occupationRecip ν = ((primeProduct ν : ℕ) : ℂ)⁻¹ := nomeMonomial_primeLinearNome ν

theorem norm_occupationRecip_le_one (ν : Nat.Primes →₀ ℕ) : ‖occupationRecip ν‖ ≤ 1 := by
  rw [occupationRecip_eq, norm_inv, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ ((primeProduct ν : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (primeProduct_pos ν).ne'
  rw [inv_le_one_iff₀]
  exact Or.inr h1

theorem norm_primeSquareNome_lt_one (p : Nat.Primes) : ‖primeSquareNome p‖ < 1 := by
  rw [primeSquareNome, norm_pow, norm_inv, Complex.norm_natCast]
  have hp : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have hinv : ((p : ℕ) : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hp
  have hnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ)⁻¹ := by positivity
  nlinarith [hinv, hnn]

/-- **The level-two occupation mass is finite.** -/
theorem summable_norm_occupationRecip_sq :
    Summable fun ν : Nat.Primes →₀ ℕ => ‖occupationRecip ν‖ ^ 2 := by
  have hprimes : Summable fun p : Nat.Primes => ‖primeSquareNome p‖ ^ (0 + 1) := by
    refine HTGeometry.summable_primeReciprocal_sq.congr fun p => ?_
    rw [primeSquareNome, norm_pow, norm_inv, Complex.norm_natCast]
    ring
  have h := (HTGeometry.summable_nomeMonomial_pow_iff 0 primeSquareNome
    norm_primeSquareNome_lt_one).2 hprimes
  refine h.congr fun ν => ?_
  rw [nomeMonomial_primeSquareNome, occupationRecip_eq, norm_pow]
  ring

theorem summable_norm_occupationRecip_pow {k : ℕ} (hk : 2 ≤ k) :
    Summable fun ν : Nat.Primes →₀ ℕ => ‖occupationRecip ν ^ k‖ := by
  refine summable_norm_occupationRecip_sq.of_nonneg_of_le (fun _ => norm_nonneg _) fun ν => ?_
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (norm_occupationRecip_le_one ν) hk

/-- The level-two occupation mass, the uniform bound for every higher power sum. -/
def occupationLevelTwoMass : ℝ := ∑' ν : Nat.Primes →₀ ℕ, ‖occupationRecip ν‖ ^ 2

theorem occupationLevelTwoMass_nonneg : 0 ≤ occupationLevelTwoMass :=
  tsum_nonneg fun _ => by positivity

/-! ### Cofinal convergence of the occupation power sums -/

/-- The `k`-th occupation power sum of a finite prime source. -/
def smoothPowerSum (S : Finset Nat.Primes) (k : ℕ) : ℂ :=
  ∑' ν : occupationSupported S, occupationRecip (ν : Nat.Primes →₀ ℕ) ^ k

/-- **Above level one the occupation power sums converge cofinally.** -/
theorem tendsto_smoothPowerSum {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun S : Finset Nat.Primes => smoothPowerSum S k) atTop
      (𝓝 (∑' ν : Nat.Primes →₀ ℕ, occupationRecip ν ^ k)) :=
  HTGeometry.tendsto_tsum_subtype_of_cofinal (summable_norm_occupationRecip_pow hk)
    cofinal_occupationSupported

/-- **Every occupation power sum above level one is bounded by the level-two mass.** -/
theorem norm_smoothPowerSum_le (S : Finset Nat.Primes) {k : ℕ} (hk : 2 ≤ k) :
    ‖smoothPowerSum S k‖ ≤ occupationLevelTwoMass := by
  have hsub : Summable fun ν : occupationSupported S =>
      ‖occupationRecip (ν : Nat.Primes →₀ ℕ) ^ k‖ :=
    (summable_norm_occupationRecip_pow hk).subtype _
  have hsq : Summable fun ν : Nat.Primes →₀ ℕ => ‖occupationRecip ν‖ ^ 2 :=
    summable_norm_occupationRecip_sq
  calc ‖smoothPowerSum S k‖
      ≤ ∑' ν : occupationSupported S, ‖occupationRecip (ν : Nat.Primes →₀ ℕ) ^ k‖ :=
        norm_tsum_le_tsum_norm hsub
    _ ≤ ∑' ν : occupationSupported S, ‖occupationRecip (ν : Nat.Primes →₀ ℕ)‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun ν => ?_) hsub (hsq.subtype _)
        rw [norm_pow]
        exact pow_le_pow_of_le_one (norm_nonneg _) (norm_occupationRecip_le_one _) hk
    _ ≤ occupationLevelTwoMass := by
        refine Summable.tsum_le_tsum_of_inj
          (fun ν : occupationSupported S => (ν : Nat.Primes →₀ ℕ))
          (fun x y hxy => Subtype.ext hxy) (fun _ _ => by positivity) (fun _ => le_rfl)
          (hsq.subtype _) hsq

/-! ### Cofinal convergence of the intensity -/

/-- The finite-source logarithmic intensity: the sum of the logarithms of the squared occupation
factors. -/
def smoothLogIntensity (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  ∑' ν : occupationSupported S,
    Complex.log (1 - t * occupationRecip (ν : Nat.Primes →₀ ℕ) ^ 2)

/-- **The logarithmic intensity converges cofinally.** -/
theorem tendsto_smoothLogIntensity {t : ℂ} (ht : ‖t‖ < 1) :
    Tendsto (fun S : Finset Nat.Primes => smoothLogIntensity S t) atTop
      (𝓝 (∑' ν : Nat.Primes →₀ ℕ, Complex.log (1 - t * occupationRecip ν ^ 2))) := by
  refine HTGeometry.tendsto_tsum_log_of_cofinal (a := fun ν => occupationRecip ν ^ 2) ?_ ?_ ht
    cofinal_occupationSupported
  · exact summable_norm_occupationRecip_pow (le_refl 2)
  · intro ν
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_occupationRecip_le_one ν)

/-! ### Cofinal convergence of the odd jet -/

/-- The odd jet series of the tangent-normalized polarized phase of a finite prime source. -/
def smoothOddJetSeries (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  ∑' j : ℕ, -(2 * smoothPowerSum S (2 * (j + 1) + 1) * t ^ (2 * (j + 1) + 1)
    / ((2 * (j + 1) + 1 : ℕ) : ℂ))

/-- The completed odd jet series. -/
def completedOddJetSeries (t : ℂ) : ℂ :=
  ∑' j : ℕ, -(2 * (∑' ν : Nat.Primes →₀ ℕ, occupationRecip ν ^ (2 * (j + 1) + 1))
    * t ^ (2 * (j + 1) + 1) / ((2 * (j + 1) + 1 : ℕ) : ℂ))

/-- **The odd jet series converges cofinally.**  Every coefficient converges, and the terms are
dominated uniformly in the prime set by a geometric series. -/
theorem tendsto_smoothOddJetSeries {t : ℂ} (ht : ‖t‖ < 1) :
    Tendsto (fun S : Finset Nat.Primes => smoothOddJetSeries S t) atTop
      (𝓝 (completedOddJetSeries t)) := by
  have htn : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
  set A : ℝ := occupationLevelTwoMass with hA
  have hA0 : 0 ≤ A := occupationLevelTwoMass_nonneg
  set bound : ℕ → ℝ := fun j => 2 * A * ‖t‖ ^ (2 * (j + 1) + 1) with hbound
  have hboundsummable : Summable bound := by
    have hgeo : Summable fun j : ℕ => (2 * A * ‖t‖ ^ 3) * (‖t‖ ^ 2) ^ j :=
      (summable_geometric_of_lt_one (by positivity) (by nlinarith [htn, ht] : ‖t‖ ^ 2 < 1)).mul_left _
    refine hgeo.congr fun j => ?_
    show 2 * A * ‖t‖ ^ 3 * (‖t‖ ^ 2) ^ j = 2 * A * ‖t‖ ^ (2 * (j + 1) + 1)
    have hsplit : ‖t‖ ^ (2 * (j + 1) + 1) = ‖t‖ ^ 3 * (‖t‖ ^ 2) ^ j := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hsplit]
    ring
  refine tendsto_tsum_of_dominated_convergence hboundsummable ?_ ?_
  · intro j
    have hk : 2 ≤ 2 * (j + 1) + 1 := by omega
    have hcoef := tendsto_smoothPowerSum hk
    have hconst : Tendsto (fun S : Finset Nat.Primes =>
        -(2 * smoothPowerSum S (2 * (j + 1) + 1) * t ^ (2 * (j + 1) + 1)
          / ((2 * (j + 1) + 1 : ℕ) : ℂ))) atTop
        (𝓝 (-(2 * (∑' ν : Nat.Primes →₀ ℕ, occupationRecip ν ^ (2 * (j + 1) + 1))
          * t ^ (2 * (j + 1) + 1) / ((2 * (j + 1) + 1 : ℕ) : ℂ)))) := by
      exact ((((hcoef.const_mul (2 : ℂ)).mul_const (t ^ (2 * (j + 1) + 1))).div_const
        (((2 * (j + 1) + 1 : ℕ) : ℂ))).neg)
    exact hconst
  · refine Filter.Eventually.of_forall fun S j => ?_
    have hk : 2 ≤ 2 * (j + 1) + 1 := by omega
    have hPk : ‖smoothPowerSum S (2 * (j + 1) + 1)‖ ≤ A := norm_smoothPowerSum_le S hk
    have hcast : ‖((2 * (j + 1) + 1 : ℕ) : ℂ)‖ = ((2 * (j + 1) + 1 : ℕ) : ℝ) :=
      Complex.norm_natCast _
    have hden : (1 : ℝ) ≤ ((2 * (j + 1) + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * (j + 1) + 1 := by omega
      exact_mod_cast this
    have hval : ‖-(2 * smoothPowerSum S (2 * (j + 1) + 1) * t ^ (2 * (j + 1) + 1)
          / ((2 * (j + 1) + 1 : ℕ) : ℂ))‖
        = 2 * ‖smoothPowerSum S (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1)
          / ((2 * (j + 1) + 1 : ℕ) : ℝ) := by
      simp only [norm_neg, norm_div, norm_mul, norm_pow, hcast]
      norm_num
    have hnum0 : (0 : ℝ) ≤ 2 * ‖smoothPowerSum S (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1) := by
      positivity
    rw [hval, hbound]
    calc 2 * ‖smoothPowerSum S (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1)
          / ((2 * (j + 1) + 1 : ℕ) : ℝ)
        ≤ 2 * ‖smoothPowerSum S (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1) :=
          div_le_self hnum0 hden
      _ ≤ 2 * A * ‖t‖ ^ (2 * (j + 1) + 1) := by
          have hstep : ‖smoothPowerSum S (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1)
              ≤ A * ‖t‖ ^ (2 * (j + 1) + 1) :=
            mul_le_mul_of_nonneg_right hPk (by positivity)
          nlinarith [hstep]

end

end GaloisForLFunctions
