import GaloisForLFunctions.HTGeometry.ReplicaCrowdingCentralLimitFloor

/-!
# The soft-light filter and the replica collision mass

Truncating a probability weighting at a multiple of its own collision scale removes only a small
part of the mass, because Chebyshev applied to the weights themselves bounds the mass sitting above
any threshold by the collision scale over that threshold.  What survives is a weighting whose
largest normalized entry is controlled by the collision scale.

A weighting with small largest entry has small replica collision mass: the multinomial amplitude of
any multiplicity vector is at most `r!` times the `r`-th power of the largest entry, and the
collision mass is bounded by the largest amplitude because the amplitudes sum to one.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## The soft-light filter -/

/-- The soft-light filter: keep exactly the levels whose weight is below the collision-scaled
threshold `4C/a`. -/
def softLightFilter (p : I → ℝ) (a C : ℝ) : I → ℝ :=
  fun j => if p j ≤ 4 * C / a then p j else 0

theorem softLightFilter_nonneg {p : I → ℝ} (hp : ∀ j, 0 ≤ p j) (a C : ℝ) (j : I) :
    0 ≤ softLightFilter p a C j := by
  rw [softLightFilter]
  split
  · exact hp j
  · exact le_rfl

theorem softLightFilter_le_threshold {p : I → ℝ} (a C : ℝ) (hthr : 0 ≤ 4 * C / a) (j : I) :
    softLightFilter p a C j ≤ 4 * C / a := by
  rw [softLightFilter]
  split
  · assumption
  · exact hthr

theorem softLightFilter_le_self {p : I → ℝ} (hp : ∀ j, 0 ≤ p j) (a C : ℝ) (j : I) :
    softLightFilter p a C j ≤ p j := by
  rw [softLightFilter]
  split
  · exact le_rfl
  · exact hp j

/-- **The soft-light filter keeps almost all the mass.**  The mass above the threshold `4C/a` is at
most `a/4` when the collision mass is at most `C`. -/
theorem softLightFilter_mass_ge {p : I → ℝ} (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    {a C : ℝ} (ha : 0 < a) (hCpos : 0 < C) (hC : ∑ j, p j ^ 2 ≤ C) :
    1 - a / 4 ≤ ∑ j, softLightFilter p a C j := by
  classical
  set t : ℝ := 4 * C / a with ht
  have htpos : 0 < t := by positivity
  set B : Finset I := Finset.univ.filter fun j => ¬ (p j ≤ t) with hB
  have hdrop : ∑ j ∈ B, p j ≤ a / 4 := by
    have hstep : ∀ j ∈ B, t * p j ≤ p j ^ 2 := by
      intro j hj
      rw [hB, Finset.mem_filter] at hj
      have hgt : t < p j := not_le.mp hj.2
      nlinarith [hp j]
    have hkey : t * ∑ j ∈ B, p j ≤ C := by
      calc t * ∑ j ∈ B, p j = ∑ j ∈ B, t * p j := by rw [Finset.mul_sum]
        _ ≤ ∑ j ∈ B, p j ^ 2 := Finset.sum_le_sum hstep
        _ ≤ ∑ j, p j ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => sq_nonneg _)
        _ ≤ C := hC
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ ha] at hkey
    nlinarith [hkey, hCpos, Finset.sum_nonneg (fun j (_ : j ∈ B) => hp j)]
  have hsplit : ∑ j, p j =
      (∑ j ∈ Finset.univ.filter fun j => p j ≤ t, p j) + ∑ j ∈ B, p j :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => p j ≤ t) p).symm
  have hfilter : ∑ j, softLightFilter p a C j =
      ∑ j ∈ Finset.univ.filter fun j => p j ≤ t, p j := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [hfilter, hsum] at *
  linarith [hsplit, hdrop]

/-! ## The replica collision mass of a flat weighting -/

theorem prod_pow_le {weight : I → ℝ} (hw : ∀ j, 0 ≤ weight j) {M : ℝ} (hM : ∀ j, weight j ≤ M)
    {p : I → ℕ} {r : ℕ} (hp : ∑ j, p j = r) :
    ∏ j, weight j ^ p j ≤ M ^ r := by
  classical
  calc ∏ j, weight j ^ p j ≤ ∏ j, M ^ p j :=
        Finset.prod_le_prod (fun j _ => pow_nonneg (hw j) _)
          fun j _ => pow_le_pow_left₀ (hw j) (hM j) _
    _ = M ^ ∑ j, p j := Finset.prod_pow_eq_pow_sum _ _ _
    _ = M ^ r := by rw [hp]

/-- The multinomial amplitude of a weighting with largest entry `M` is at most `r! M^r`. -/
theorem fidelityReplicaMultiplicityAmplitude_le {weight : I → ℝ} (hw : ∀ j, 0 ≤ weight j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, weight j ≤ M) {p : I → ℕ} {r : ℕ}
    (hp : p ∈ Finset.univ.piAntidiag r) :
    fidelityReplicaMultiplicityAmplitude weight p ≤ (Nat.factorial r : ℝ) * M ^ r := by
  classical
  have hsum : ∑ j, p j = r := by
    have h := (Finset.mem_piAntidiag.mp hp).1
    simpa using h
  have hmulti : ((Nat.multinomial Finset.univ p : ℕ) : ℝ) ≤ (Nat.factorial r : ℝ) := by
    exact_mod_cast multinomial_le_factorial hsum
  rw [fidelityReplicaMultiplicityAmplitude]
  calc ((Nat.multinomial Finset.univ p : ℕ) : ℝ) * ∏ j, weight j ^ p j
      ≤ ((Nat.multinomial Finset.univ p : ℕ) : ℝ) * M ^ r :=
        mul_le_mul_of_nonneg_left (prod_pow_le hw hM hsum) (by positivity)
    _ ≤ (Nat.factorial r : ℝ) * M ^ r := mul_le_mul_of_nonneg_right hmulti (by positivity)

/-- **Corollary C1, equation (18).**  A probability weighting whose largest entry is `M` has replica
collision mass at most `(r M)^r`. -/
theorem replicaCollisionMass_le {weight : I → ℝ} (hw : ∀ j, 0 ≤ weight j)
    (hsum : ∑ j, weight j = 1) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, weight j ≤ M) (r : ℕ) :
    ∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p ^ 2
      ≤ ((r : ℝ) * M) ^ r := by
  classical
  have hampnn : ∀ p : I → ℕ, 0 ≤ fidelityReplicaMultiplicityAmplitude weight p :=
    fun p => fidelityReplicaMultiplicityAmplitude_nonneg hw p
  have hstep : ∀ p ∈ Finset.univ.piAntidiag r,
      fidelityReplicaMultiplicityAmplitude weight p ^ 2 ≤
        ((Nat.factorial r : ℝ) * M ^ r) * fidelityReplicaMultiplicityAmplitude weight p := by
    intro p hp
    rw [sq]
    exact mul_le_mul_of_nonneg_right (fidelityReplicaMultiplicityAmplitude_le hw hM0 hM hp)
      (hampnn p)
  calc ∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p ^ 2
      ≤ ∑ p ∈ Finset.univ.piAntidiag r,
          ((Nat.factorial r : ℝ) * M ^ r) * fidelityReplicaMultiplicityAmplitude weight p :=
        Finset.sum_le_sum hstep
    _ = ((Nat.factorial r : ℝ) * M ^ r) *
          ∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p := by
        rw [Finset.mul_sum]
    _ = (Nat.factorial r : ℝ) * M ^ r := by rw [replicaAmplitude_total_mass hsum r, mul_one]
    _ ≤ ((r : ℝ) ^ r) * M ^ r := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.factorial_le_pow r
    _ = ((r : ℝ) * M) ^ r := (mul_pow _ _ _).symm

end GaloisForLFunctions.HTGeometry
