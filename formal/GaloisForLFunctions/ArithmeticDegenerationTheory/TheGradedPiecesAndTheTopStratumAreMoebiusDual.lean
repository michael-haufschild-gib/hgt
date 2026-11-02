import GaloisForLFunctions.ArithmeticDegenerationTheory.TheConductorEnergyIsAConeSumOfTopStrata
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheMoebiusGluingOfStars

/-!
# The graded pieces and the top stratum are Möbius dual

`TheConductorEnergyIsAConeSumOfTopStrata` writes the energy of a graded piece (a normalized
Ramanujan packet) as a `θ²`-weighted sum over the dilation cone of top-stratum energies of lowered
conductors. The Möbius gluing of stars (HWV) inverts this:

`Top_{c,N}(r_e) = ⟨W_{c,N} r_e, r_e⟩ + (log N)⁻¹ Σ_{2 ≤ d ≤ N} μ(d) θ_d(e)² ⟨W_{c_d,⌊N/d⌋} R_{e/(e,d)}, R_{e/(e,d)}⟩`

(`topStratumEnergy_ramanujan_moebius_expansion`): the top-stratum (coprime) energy of a graded piece
is the Möbius-signed cone sum of the graded energies of its lowered conductors at the star
resolutions. Together with the forward expansion this is a Möbius pair over the cone:

* graded = `Σ_g θ_g² · top(lowered)`  (sign-free: the gcd stratification);
* top = `Σ_d μ(d) θ_d² · graded(lowered)`  (alternating: the Möbius gluing).

The extension data of the limiting structure (top stratum) and its graded pieces determine each other
exactly, prime by prime through the monodromy. The positivity of the graded pieces does not pass to
the top stratum, because the inversion is alternating; this is the arithmetic form of the statement
that local positivity on stars does not glue (HWV).
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory HodgeTheoryWithoutVarieties

theorem completeWeilEnergy_smul (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (s : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (s • u) = s ^ 2 * completeWeilEnergy φ c N u := by
  simp only [completeWeilEnergy, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

/-- The star pullback of a normalized packet, as a vector. -/
theorem starPull_normalizedRamanujanHorizonVector_eq {g N e : ℕ} (hg : 0 < g) (he : 0 < e) :
    starPull g N (normalizedRamanujanHorizonVector e N) =
      ((Real.sqrt (Real.log N))⁻¹ * coneFactor g e) •
        ramanujanHorizonVector (e / Nat.gcd e g) (N / g) := by
  ext a
  rw [starPull_normalizedRamanujanHorizonVector hg he a]
  rfl

/-- **The Möbius dual of the cone expansion.** The top-stratum energy of a graded piece is the
graded energy minus the Möbius-signed cone sum of the graded energies of its lowered conductors. -/
theorem topStratumEnergy_ramanujan_moebius_expansion {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ)
    {c : ℝ} (hc : 0 < c) (N : ℕ) {e : ℕ} (he : 0 < e) :
    topStratumEnergy φ c N (normalizedRamanujanHorizonVector e N) =
      completeWeilEnergy φ c N (normalizedRamanujanHorizonVector e N) +
        (Real.log N)⁻¹ * ∑ d ∈ Icc 2 N, (ArithmeticFunction.moebius d : ℝ) * coneFactor d e ^ 2 *
          completeWeilEnergy φ (starOverlap c N d) (N / d)
            (ramanujanHorizonVector (e / Nat.gcd e d) (N / d)) := by
  have hglue := completeWeilEnergy_moebius_gluing hφ hc N (normalizedRamanujanHorizonVector e N)
  have hstar : ∀ d ∈ Icc 2 N, completeWeilEnergy φ (starOverlap c N d) (N / d)
      (starPull d N (normalizedRamanujanHorizonVector e N)) =
        (Real.log N)⁻¹ * coneFactor d e ^ 2 *
          completeWeilEnergy φ (starOverlap c N d) (N / d)
            (ramanujanHorizonVector (e / Nat.gcd e d) (N / d)) := by
    intro d hd
    have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
    rw [starPull_normalizedRamanujanHorizonVector_eq hd0 he, completeWeilEnergy_smul,
      mul_pow, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  have hsum_eq : ∑ d ∈ Icc 2 N, -(ArithmeticFunction.moebius d : ℝ) *
      completeWeilEnergy φ (starOverlap c N d) (N / d) (starPull d N (normalizedRamanujanHorizonVector e N)) =
        -((Real.log N)⁻¹ * ∑ d ∈ Icc 2 N, (ArithmeticFunction.moebius d : ℝ) * coneFactor d e ^ 2 *
          completeWeilEnergy φ (starOverlap c N d) (N / d)
            (ramanujanHorizonVector (e / Nat.gcd e d) (N / d))) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun d hd => ?_
    rw [hstar d hd]
    ring
  rw [hsum_eq] at hglue
  have htop : topStratumEnergy φ c N (normalizedRamanujanHorizonVector e N) =
      ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        (if Nat.Coprime (i : ℕ) j then completeWeilMatrix φ c N i j *
          normalizedRamanujanHorizonVector e N i * normalizedRamanujanHorizonVector e N j else 0) := rfl
  rw [htop]
  linarith [hglue]

end GaloisForLFunctions.ArithmeticDegenerationTheory
