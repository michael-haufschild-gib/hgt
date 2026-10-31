import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.SmoothedDivisorJet
import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage

/-!
# Positive adjunction lag charges on source profiles

Integrating finite-source autocorrelation weights gives nonnegative
conductor weights for arbitrary translates of a compact real profile.
Their incoming divisor charge is the profile Gram of the reduced-lag
adjunction deficit. The logarithmic source mesh is included exactly,
without replacing its varying spacings by a uniform lattice.
-/

open MeasureTheory Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence ArithmeticIntersectionTheory
open RHTower.ArchimedeanAnomaly
noncomputable section


private theorem integral_sourceProfile_gram {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (S : Finset ℕ) (x θ : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∫ u, ∑ i ∈ S, ∑ j ∈ S,
      (x i * φ (u + θ i)) * (x j * φ (u + θ j)) * K i j) =
      ∑ i ∈ S, ∑ j ∈ S, x i * x j * K i j * autocorr φ (θ j - θ i) := by
  have hint (i j : ℕ) : Integrable fun u =>
      (x i * x j * K i j) * (φ (u + θ i) * φ (u + θ j)) :=
    (BiScaleUncertainty.integrable_shift_mul_shift hφ hφc (θ i) (θ j)).const_mul _
  have he : (fun u => ∑ i ∈ S, ∑ j ∈ S,
      (x i * φ (u + θ i)) * (x j * φ (u + θ j)) * K i j) =
      fun u => ∑ i ∈ S, ∑ j ∈ S,
        (x i * x j * K i j) * (φ (u + θ i) * φ (u + θ j)) := by
    funext u
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ => hint i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum S (fun j _ => hint i j)]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul, BiScaleUncertainty.integral_shift_mul_shift]

/-- Conductor compression of a source profile at arbitrary real shifts. -/
def ramanujanProfileWeight (φ : ℝ → ℝ) (S : Finset ℕ) (x θ : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ S, ∑ j ∈ S,
    x i * x j * ramanujanLagCoefficient k (Nat.dist i j) * autocorr φ (θ j - θ i)) /
      (k.totient : ℝ)

/-- The profile weight is the integral of the literal finite-source weights. -/
theorem ramanujanProfileWeight_eq_integral {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (S : Finset ℕ) (x θ : ℕ → ℝ) (k : ℕ) :
    ramanujanProfileWeight φ S x θ k =
      ∫ u, ramanujanAutocorrelationWeight S (fun i => x i * φ (u + θ i)) k := by
  have he : (fun u => ramanujanAutocorrelationWeight S (fun i => x i * φ (u + θ i)) k) =
      fun u => (1 / (k.totient : ℝ)) * ∑ i ∈ S, ∑ j ∈ S,
        (x i * φ (u + θ i)) * (x j * φ (u + θ j)) *
          ramanujanLagCoefficient k (Nat.dist i j) := by
    funext u
    rw [ramanujanAutocorrelationWeight]
    ring
  rw [he, integral_const_mul, integral_sourceProfile_gram hφ hφc, ramanujanProfileWeight]
  ring

/-- Every finite signed profile packet has nonnegative compressed conductor weights. -/
theorem ramanujanProfileWeight_nonneg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (S : Finset ℕ) (x θ : ℕ → ℝ) (k : ℕ) :
    0 ≤ ramanujanProfileWeight φ S x θ k := by
  rw [ramanujanProfileWeight_eq_integral hφ hφc]
  exact integral_nonneg fun u =>
    ramanujanAutocorrelationWeight_nonneg S (fun i => x i * φ (u + θ i)) k

private theorem totient_mul_profileWeight {k : ℕ} (hk : 0 < k)
    (φ : ℝ → ℝ) (S : Finset ℕ) (x θ : ℕ → ℝ) :
    (k.totient : ℝ) * ramanujanProfileWeight φ S x θ k =
      ∑ i ∈ S, ∑ j ∈ S, x i * x j * ramanujanLagCoefficient k (Nat.dist i j) *
        autocorr φ (θ j - θ i) := by
  have hp : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  rw [ramanujanProfileWeight]
  field_simp [hp]

private theorem lower_jet_charge {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∑ k ∈ m.divisors, vonMangoldt (m / k) * ramanujanLagCoefficient k n) =
      ramanujanLagCoefficient m n *
        (tameDifferent m - (Real.log (m / Nat.gcd m n : ℕ) + tameDifferent (m / Nat.gcd m n))) := by
  have hmm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have he := ramanujanLogDivisorJet_eq_weighted_conductors hm n
  simp only [ramanujanJetConductorWeight, add_mul, sum_add_distrib,
    ite_mul, zero_mul, sum_ite_eq', if_pos hmm] at he
  rw [ramanujanLogDivisorJet_eq_adjunction_gap hm] at he
  linear_combination -he

/-- The incoming weighted divisor charge is exactly the profile Gram of the adjunction lag kernel. -/
theorem sum_divisor_profileWeight_eq_adjunction_charge {m : ℕ} (hm : 0 < m)
    (φ : ℝ → ℝ) (S : Finset ℕ) (x θ : ℕ → ℝ) :
    (∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) *
      ramanujanProfileWeight φ S x θ k) =
      ∑ i ∈ S, ∑ j ∈ S,
        x i * x j * autocorr φ (θ j - θ i) * ramanujanLagCoefficient m (Nat.dist i j) *
          (tameDifferent m -
            (Real.log (m / Nat.gcd m (Nat.dist i j) : ℕ) +
              tameDifferent (m / Nat.gcd m (Nat.dist i j)))) := by
  calc
    _ = ∑ k ∈ m.divisors, ∑ i ∈ S, ∑ j ∈ S,
        x i * x j * autocorr φ (θ j - θ i) *
          (vonMangoldt (m / k) * ramanujanLagCoefficient k (Nat.dist i j)) := by
      apply sum_congr rfl
      intro k hk
      rw [mul_assoc, totient_mul_profileWeight (Nat.pos_of_mem_divisors hk), mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ i ∈ S, ∑ k ∈ m.divisors, ∑ j ∈ S,
        x i * x j * autocorr φ (θ j - θ i) *
          (vonMangoldt (m / k) * ramanujanLagCoefficient k (Nat.dist i j)) := by
      rw [sum_comm]
    _ = ∑ i ∈ S, ∑ j ∈ S, x i * x j * autocorr φ (θ j - θ i) *
        (∑ k ∈ m.divisors, vonMangoldt (m / k) * ramanujanLagCoefficient k (Nat.dist i j)) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [lower_jet_charge hm]
      ring

/-- The reduced-lag adjunction charge remains positive with the actual profile Gram. -/
theorem profiled_adjunction_lag_charge_nonneg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {m : ℕ} (hm : 0 < m) (S : Finset ℕ) (x θ : ℕ → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      x i * x j * autocorr φ (θ j - θ i) * ramanujanLagCoefficient m (Nat.dist i j) *
        (tameDifferent m -
          (Real.log (m / Nat.gcd m (Nat.dist i j) : ℕ) +
            tameDifferent (m / Nat.gcd m (Nat.dist i j)))) := by
  rw [← sum_divisor_profileWeight_eq_adjunction_charge hm]
  exact sum_nonneg fun k _ => mul_nonneg
    (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (ramanujanProfileWeight_nonneg hφ hφc S x θ k)

/-- The exact logarithmic source mesh preserves positivity without freezing its spacings. -/
theorem logarithmic_profile_adjunction_charge_nonneg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {m : ℕ} (hm : 0 < m) (S : Finset ℕ) (x : ℕ → ℝ) (w : ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      x i * x j * autocorr φ (Real.log j / w - Real.log i / w) *
        ramanujanLagCoefficient m (Nat.dist i j) *
        (tameDifferent m -
          (Real.log (m / Nat.gcd m (Nat.dist i j) : ℕ) +
            tameDifferent (m / Nat.gcd m (Nat.dist i j)))) :=
  profiled_adjunction_lag_charge_nonneg hφ hφc hm S x (fun i => Real.log i / w)

/-- Source profile weights preserve every nonnegative conductor-edge square. -/
theorem weightedDivisorJetEnergy_profile_nonneg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (M : ℕ) (S : Finset ℕ) (x θ f : ℕ → ℝ) :
    0 ≤ weightedDivisorJetEnergy M (ramanujanProfileWeight φ S x θ) f := by
  apply sum_nonneg
  intro m _
  apply sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg
    (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (ramanujanProfileWeight_nonneg hφ hφc S x θ k)) (sq_nonneg _)

#print axioms ramanujanProfileWeight_eq_integral
#print axioms ramanujanProfileWeight_nonneg
#print axioms sum_divisor_profileWeight_eq_adjunction_charge
#print axioms profiled_adjunction_lag_charge_nonneg
#print axioms logarithmic_profile_adjunction_charge_nonneg
#print axioms weightedDivisorJetEnergy_profile_nonneg
end
end GaloisForLFunctions.SuccessorShellArithmetic
