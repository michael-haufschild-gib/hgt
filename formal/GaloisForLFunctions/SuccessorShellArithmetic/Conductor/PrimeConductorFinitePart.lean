import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramTorsionEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# The torsion boundary of the prime conductor form

The logarithmically normalized full prime matrix has an exact finite part
on every fixed pair of Ramanujan conductors. Its mixed entry is minus the
normalized torsion intersection; its diagonal is `-2 log m`. The harmonic
Gram finite part retains the cutoff contribution that survives the
vanishing prime-row residual.
-/

open Filter Topology Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  ArithmeticEffectivityTheory ArithmeticElectrostatics ArithmeticIntersectionTheory
noncomputable section

private theorem ramanujanPoleProfile_mul_eq (m l n : ℕ) :
    ramanujanPoleProfile m n * ramanujanPoleProfile l n =
      normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ) := by
  rw [ramanujanPoleProfile_eq_mul_poleVector, ramanujanPoleProfile_eq_mul_poleVector]
  unfold poleVector
  calc
    _ = (normalizedRamanujanMode m n * normalizedRamanujanMode l n) *
        (1 / Real.sqrt (n : ℝ)) ^ 2 := by ring
    _ = _ := by rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring

private theorem tendsto_log_mul_normalizedRamanujanGram_finitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => Real.log N *
      ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then Real.log N else 0)) atTop
      (𝓝 ((if m = l then Real.eulerMascheroniConstant else 0) -
        orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))) := by
  apply (tendsto_normalizedRamanujan_harmonicGram_torsion hm hl).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [normalizedRamanujanHorizonVector_inner]
  simp_rw [ramanujanPoleProfile_mul_eq]
  field_simp

private theorem tendsto_prime_residual_pairing {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => ⟪normalizedRamanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N) -
        (Real.log N - ramanujanAdjunctionEnergy l) • normalizedRamanujanHorizonVector l N⟫)
      atTop (𝓝 0) := by
  have hnorm : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖)
      atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt
  apply squeeze_zero_norm (fun N => norm_inner_le_norm _ _)
  simpa only [mul_zero] using hnorm.mul
    (tendsto_normalizedRamanujanHorizonVector_residual_norm hl)

/-- The literal prime matrix retains the torsion finite part of every conductor pairing. -/
theorem tendsto_primeConductorPairing_finitePart {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => ⟪normalizedRamanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ -
        (if m = l then Real.log N else 0)) atTop
      (𝓝 (-orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0))) := by
  have h := ((tendsto_prime_residual_pairing hm hl).add
    (tendsto_log_mul_normalizedRamanujanGram_finitePart hm hl)).sub
      ((tendsto_normalizedRamanujanHorizonVector_gram hm hl).const_mul
        (ramanujanAdjunctionEnergy l))
  have hfun : (fun N : ℕ => (⟪normalizedRamanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N) -
        (Real.log N - ramanujanAdjunctionEnergy l) • normalizedRamanujanHorizonVector l N⟫ +
      (Real.log N * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then Real.log N else 0))) -
      ramanujanAdjunctionEnergy l *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫) =
      (fun N : ℕ => ⟪normalizedRamanujanHorizonVector m N,
        Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ -
          (if m = l then Real.log N else 0)) := by
    funext N
    rw [inner_sub_right, real_inner_smul_right]
    ring
  change Tendsto _ atTop (𝓝 _) at h
  rw [hfun] at h
  convert h using 1
  congr 1
  by_cases hml : m = l
  · subst l
    simp only [ite_true, ramanujanAdjunctionEnergy]
    ring
  · simp only [if_neg hml, mul_zero]
    ring

/-- The diagonal finite part is exactly twice the negative conductor logarithm. -/
theorem tendsto_primeConductorPairing_diagonal {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ⟪normalizedRamanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N)⟫ -
        Real.log N) atTop (𝓝 (-2 * Real.log m)) := by
  have h := tendsto_primeConductorPairing_finitePart hm hm
  simp only [ite_true] at h
  convert h using 1
  congr 1
  rw [orbitIntersection_self_eq hm, localCorrection_eq_totient_mul_tameDifferent,
    ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
  have hphi : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
  field_simp
  ring

/-- Distinct conductors retain precisely the negative torsion edge. -/
theorem tendsto_primeConductorPairing_of_ne {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hml : m ≠ l) :
    Tendsto (fun N : ℕ => ⟪normalizedRamanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫) atTop
      (𝓝 (-orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))) := by
  simpa only [if_neg hml, sub_zero] using tendsto_primeConductorPairing_finitePart hm hl

private theorem weighted_conductor_diagonal (S : Finset ℕ) (a c : ℕ → ℝ) :
    (∑ m ∈ S, ∑ l ∈ S, a m * a l * (if m = l then c m else 0)) =
      ∑ m ∈ S, a m ^ 2 * c m := by
  apply sum_congr rfl
  intro m hm
  rw [sum_eq_single_of_mem m hm]
  · simp only [ite_true]
    ring
  · intro l _ hne
    rw [if_neg hne.symm, mul_zero]

/-- Every fixed finite packet has one exact quadratic prime finite part. -/
theorem tendsto_primeConductorPacket_finitePart (S : Finset ℕ) (a : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) :
    Tendsto (fun N : ℕ =>
      ⟪∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N,
        Matrix.toEuclideanLin (fullPrimeMatrix N)
          (∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N)⟫ -
        Real.log N * ∑ m ∈ S, a m ^ 2) atTop
      (𝓝 (-(∑ m ∈ S, ∑ l ∈ S, a m * a l * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))) -
          ∑ m ∈ S, a m ^ 2 * (Real.log m + tameDifferent m))) := by
  have hpair (N : ℕ) :
      ⟪∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N,
        Matrix.toEuclideanLin (fullPrimeMatrix N)
          (∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N)⟫ =
      ∑ m ∈ S, ∑ l ∈ S, a m * a l *
        ⟪normalizedRamanujanHorizonVector m N,
          Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ := by
    simp only [map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun l _ => by ring
  have hlim := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    (tendsto_primeConductorPairing_finitePart (hS m hm) (hS l hl)).const_mul (a m * a l)
  have hfun (N : ℕ) :
      (∑ m ∈ S, ∑ l ∈ S, a m * a l *
        (⟪normalizedRamanujanHorizonVector m N,
          Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ -
            (if m = l then Real.log N else 0))) =
      ⟪∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N,
        Matrix.toEuclideanLin (fullPrimeMatrix N)
          (∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N)⟫ -
        Real.log N * ∑ m ∈ S, a m ^ 2 := by
    simp only [mul_sub, sum_sub_distrib]
    rw [← hpair, weighted_conductor_diagonal S a (fun _ => Real.log N), ← sum_mul]
    ring
  have hval :
      (∑ m ∈ S, ∑ l ∈ S, a m * a l *
        (-orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
          (if m = l then Real.log m + tameDifferent m else 0))) =
      -(∑ m ∈ S, ∑ l ∈ S, a m * a l * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))) -
          ∑ m ∈ S, a m ^ 2 * (Real.log m + tameDifferent m) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [weighted_conductor_diagonal]
    congr 1
    simp only [neg_div, mul_div_assoc, mul_neg, sum_neg_distrib]
  rw [hval] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall hfun)

#print axioms tendsto_primeConductorPairing_finitePart
#print axioms tendsto_primeConductorPairing_diagonal
#print axioms tendsto_primeConductorPairing_of_ne
#print axioms tendsto_primeConductorPacket_finitePart

end
end GaloisForLFunctions.SuccessorShellArithmetic
