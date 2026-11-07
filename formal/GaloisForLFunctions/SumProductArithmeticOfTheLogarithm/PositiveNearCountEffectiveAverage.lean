import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.EffectiveLogarithmicHalfTurn
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountProfileModulus

/-!
# Effective finite averages and the actual count remainder

A bounded sequence with an approximate complementary shift has average error
at most half the pairing error plus its boundary cost. For the positive count
profile, the explicit logarithmic half-turn and continuity modulus give
`resolutionError Q + returnCost Q / n`, uniformly in the starting scale.

The actual weighted-count bridge transfers this estimate to the integral of
the generalized-integer count. Every resolution `Q ≥ 2` yields an explicit
remainder for its coefficient `1 / (4 log 3)` at every threshold `x > 1`.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

private theorem abs_range_sum_le {u : ℕ → ℝ} {M : ℝ}
    (hu : ∀ i, |u i| ≤ M) (n : ℕ) :
    |∑ i ∈ Finset.range n, u i| ≤ (n : ℝ) * M := by
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (s := Finset.range n) (fun i _ => (abs_le.mp (hu i)).1)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg] using h
  · have h := Finset.sum_le_sum (s := Finset.range n) (fun i _ => (abs_le.mp (hu i)).2)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

/-- Approximate complementary pairing controls a finite average by the pairing error and its boundary. -/
theorem average_error_of_complementary_shift {u : ℕ → ℝ} {M c ε : ℝ} {k n : ℕ}
    (hn : 1 ≤ n) (hu : ∀ i, |u i| ≤ M)
    (hp : ∀ i, |u i + u (i + k) - c| ≤ ε) :
    |(∑ i ∈ Finset.range n, u i) / (n : ℝ) - c / 2| ≤
      ε / 2 + (k : ℝ) * M / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∑ i ∈ Finset.range n, u i) + (∑ i ∈ Finset.range k, u (n + i)) =
      (∑ i ∈ Finset.range k, u i) + (∑ i ∈ Finset.range n, u (k + i)) := by
    rw [← Finset.sum_range_add, ← Finset.sum_range_add, Nat.add_comm n k]
  simp_rw [Nat.add_comm n, Nat.add_comm k] at he
  have hA := abs_le.mp (abs_range_sum_le (fun i => hu (i + n)) k)
  have hB := abs_le.mp (abs_range_sum_le hu k)
  have hshift : |(∑ i ∈ Finset.range n, u (i + k)) - ∑ i ∈ Finset.range n, u i| ≤
      2 * (k : ℝ) * M := by
    apply abs_le.mpr
    constructor <;> linarith only [he, hA.1, hA.2, hB.1, hB.2]
  have hpSum := abs_range_sum_le hp n
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hpSum
  have hD : |2 * (∑ i ∈ Finset.range n, u i) - (n : ℝ) * c| ≤
      (n : ℝ) * ε + 2 * (k : ℝ) * M := by
    have h1 := abs_le.mp hpSum
    have h2 := abs_le.mp hshift
    apply abs_le.mpr
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have he' : (∑ i ∈ Finset.range n, u i) / (n : ℝ) - c / 2 =
      (2 * (∑ i ∈ Finset.range n, u i) - (n : ℝ) * c) / (2 * (n : ℝ)) := by
    field_simp
  rw [he', abs_div, abs_of_pos (by positivity : 0 < 2 * (n : ℝ))]
  calc
    _ ≤ ((n : ℝ) * ε + 2 * (k : ℝ) * M) / (2 * (n : ℝ)) :=
      div_le_div_of_nonneg_right hD (by positivity)
    _ = _ := by field_simp

namespace PositiveNearCount

private theorem logarithmicProfile_half_complement (t : ℝ) :
    logarithmicProfile t + logarithmicProfile (t - Real.log 4 / 2) = 1 / 2 := by
  have he : Real.log 4 / 2 = Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  dsimp only [logarithmicProfile]
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact fourProfile_half (Real.exp_pos t)

private theorem logarithmicProfile_three_orbit {X : ℝ} (hX : 0 < X) (i : ℕ) :
    logarithmicProfile (Real.log X - (i : ℝ) * Real.log 3) = fourProfile (X / (3 : ℝ) ^ i) := by
  dsimp only [logarithmicProfile]
  rw [Real.exp_sub, Real.exp_log hX, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- A fully explicit uniform error for the actual count profile along powers of three. -/
theorem effective_profile_average {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 1 ≤ n)
    {X : ℝ} (hX : 0 < X) :
    |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
      (8 * Real.log (Q : ℝ) + 32 * Real.log 4 + 2 / 3) / (Q : ℝ) +
        (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / (4 * (n : ℝ)) := by
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨k, _, hk, ℓ, happrox⟩ := exists_effective_three_four_half_turn hQ
  let e := (k : ℝ) * Real.log 3 - (ℓ : ℝ) * Real.log 4 - Real.log 4 / 2
  let μ := (16 * Real.log (Q : ℝ) + 64 * Real.log 4 + 4 / 3) / (Q : ℝ)
  have he : |e| ≤ Real.log 4 / (Q : ℝ) := by
    have heq : e = Real.log 4 * ((k : ℝ) * threeFourRotation - ℓ - 1 / 2) := by
      dsimp only [e, threeFourRotation]
      field_simp
    rw [heq, abs_mul, abs_of_pos hp]
    have h := (mul_lt_mul_of_pos_left happrox hp).le
    simpa only [mul_one_div] using h
  have hpair (t : ℝ) :
      |logarithmicProfile t + logarithmicProfile (t - (k : ℝ) * Real.log 3) - 1 / 2| ≤ μ := by
    have hmod := logarithmicProfile_resolution_modulus hQ (t - Real.log 4 / 2) (-e)
      (by simpa only [abs_neg] using he)
    have hshift : logarithmicProfile (t - (k : ℝ) * Real.log 3) =
        logarithmicProfile ((t - Real.log 4 / 2) + (-e)) := by
      have hid : ((t - Real.log 4 / 2) + (-e)) - (ℓ : ℝ) * Real.log 4 =
          t - (k : ℝ) * Real.log 3 := by dsimp only [e]; ring
      have h := (logarithmicProfile_periodic.int_mul ℓ).sub_eq ((t - Real.log 4 / 2) + (-e))
      rwa [hid] at h
    have hc := logarithmicProfile_half_complement t
    have heq : logarithmicProfile t + logarithmicProfile (t - (k : ℝ) * Real.log 3) - 1 / 2 =
        logarithmicProfile (t - (k : ℝ) * Real.log 3) -
          logarithmicProfile (t - Real.log 4 / 2) := by linarith only [hc]
    rw [heq, hshift]
    exact hmod
  let u (i : ℕ) := logarithmicProfile (Real.log X - (i : ℝ) * Real.log 3)
  have hu (i : ℕ) : |u i| ≤ 1 / 2 := by
    change |fourProfile (Real.exp (Real.log X - (i : ℝ) * Real.log 3))| ≤ _
    rw [abs_of_nonneg (fourProfile_nonneg (Real.exp_pos _))]
    exact fourProfile_le_half (Real.exp_pos _)
  have hup (i : ℕ) : |u i + u (i + k) - 1 / 2| ≤ μ := by
    simpa only [u, Nat.cast_add, add_mul, sub_sub] using
      hpair (Real.log X - (i : ℝ) * Real.log 3)
  have hmean := average_error_of_complementary_shift hn hu hup
  have horbit (i : ℕ) : u i = fourProfile (X / (3 : ℝ) ^ i) := logarithmicProfile_three_orbit hX i
  simp only [horbit, show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] at hmean
  have hboundary : (k : ℝ) * (1 / 2) / (n : ℝ) ≤
      (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / (4 * (n : ℝ)) := by
    calc
      _ ≤ ((Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / 2) * (1 / 2) / (n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk (by norm_num)) hn0.le
      _ = _ := by ring
  calc
    _ ≤ μ / 2 + (k : ℝ) * (1 / 2) / (n : ℝ) := hmean
    _ ≤ μ / 2 + (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / (4 * (n : ℝ)) :=
      add_le_add le_rfl hboundary
    _ = _ := by dsimp only [μ]; ring


/-- The contribution from the profile's finite-resolution modulus. -/
def resolutionError (Q : ℕ) : ℝ :=
  (8 * Real.log (Q : ℝ) + 32 * Real.log 4 + 2 / 3) / (Q : ℝ)

/-- The boundary cost of the explicit complementary return. -/
def returnCost (Q : ℕ) : ℝ := (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / 4

theorem returnCost_nonneg (Q : ℕ) : 0 ≤ returnCost Q := by
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  dsimp only [returnCost]
  positivity

/-- Number of norm-three exponents retained at a positive counting threshold. -/
def threeLength (X : ℝ) : ℕ := ⌊Real.log X / Real.log 3⌋₊ + 1

theorem resolutionError_nonneg {Q : ℕ} (hQ : 2 ≤ Q) : 0 ≤ resolutionError Q := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hlog := Real.log_nonneg hQ1
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  dsimp only [resolutionError]
  positivity

/-- A logarithmic floor locates a real threshold between consecutive powers. -/
theorem pow_log_floor_bracket {b X : ℝ} (hb : 1 < b) (hX : 1 ≤ X) :
    b ^ ⌊Real.log X / Real.log b⌋₊ ≤ X ∧ X < b ^ (⌊Real.log X / Real.log b⌋₊ + 1) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hp : 0 < Real.log b := Real.log_pos hb
  have hlo := Nat.floor_le (div_nonneg (Real.log_nonneg hX) hp.le)
  have hhi := Nat.lt_floor_add_one (Real.log X / Real.log b)
  constructor
  · apply (Real.log_le_log_iff (pow_pos hb0 _) hx).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hp).mp hlo
  · apply (Real.log_lt_log_iff hx (pow_pos hb0 _)).mp
    rw [Real.log_pow]
    push_cast
    exact (div_lt_iff₀ hp).mp hhi

/-- The exact exponent count differs from its logarithmic density by at most one term. -/
theorem threeLength_ratio {X : ℝ} (hX : 1 < X) :
    0 ≤ (threeLength X : ℝ) / Real.log X - 1 / Real.log 3 ∧
      (threeLength X : ℝ) / Real.log X - 1 / Real.log 3 ≤ 1 / Real.log X := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hd : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlo := Nat.floor_le (div_pos hL hd).le
  have hhi := (Nat.lt_floor_add_one (Real.log X / Real.log 3)).le
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hL).mpr
    dsimp only [threeLength]
    convert hhi using 1 <;> push_cast <;> ring
  · have hn : (threeLength X : ℝ) ≤ Real.log X / Real.log 3 + 1 := by
      dsimp only [threeLength]
      push_cast
      linarith only [hlo]
    have hdiv := div_le_div_of_nonneg_right hn hL.le
    have he : (Real.log X / Real.log 3 + 1) / Real.log X =
        1 / Real.log 3 + 1 / Real.log X := by field_simp
    rw [he] at hdiv
    linarith only [hdiv]

/-- An explicit remainder for the actual first count deficit at every threshold at least one. -/
theorem effective_riesz_length_error {Q : ℕ} (hQ : 2 ≤ Q) {X : ℝ} (hX : 1 ≤ X) :
    |(X ^ 2 / 2 - rieszCount X) / X - (threeLength X : ℝ) / 4| ≤
      5 / 8 + (threeLength X : ℝ) * resolutionError Q + returnCost Q := by
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hn : 1 ≤ threeLength X := by dsimp only [threeLength]; omega
  have hn0 : (0 : ℝ) < threeLength X := by exact_mod_cast (show 0 < threeLength X by omega)
  have havg := effective_profile_average hQ hn hx
  let S := ∑ a ∈ Finset.range (threeLength X), fourProfile (X / (3 : ℝ) ^ a)
  have hcost : (8 * Real.log (Q : ℝ) + 32 * Real.log 4 + 2 / 3) / (Q : ℝ) +
      (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / (4 * (threeLength X : ℝ)) =
      resolutionError Q + returnCost Q / (threeLength X : ℝ) := by
    dsimp only [resolutionError, returnCost]
    ring
  rw [hcost] at havg
  have hS : |S - (threeLength X : ℝ) / 4| ≤
      (threeLength X : ℝ) * resolutionError Q + returnCost Q := by
    have he : S - (threeLength X : ℝ) / 4 =
        (threeLength X : ℝ) * (S / (threeLength X : ℝ) - 1 / 4) := by
      field_simp
    rw [he, abs_mul, abs_of_pos hn0]
    calc
      _ ≤ (threeLength X : ℝ) *
          (resolutionError Q + returnCost Q / (threeLength X : ℝ)) :=
        mul_le_mul_of_nonneg_left havg hn0.le
      _ = _ := by field_simp
  have hc := pow_log_floor_bracket (b := (3 : ℝ)) (by norm_num) hX
  have hbridge := normalized_deficit_profile_error hX ⌊Real.log X / Real.log 3⌋₊ hc.1 hc.2
  change |(X ^ 2 / 2 - rieszCount X) / X - S| ≤ 5 / 8 at hbridge
  calc
    _ = |((X ^ 2 / 2 - rieszCount X) / X - S) + (S - (threeLength X : ℝ) / 4)| := by
      congr 1
      ring
    _ ≤ |(X ^ 2 / 2 - rieszCount X) / X - S| + |S - (threeLength X : ℝ) / 4| := abs_add_le _ _
    _ ≤ 5 / 8 + ((threeLength X : ℝ) * resolutionError Q + returnCost Q) := add_le_add hbridge hS
    _ = _ := by ring

/-- A finite-parameter error bound for the actual logarithmic deficit coefficient. -/
theorem effective_riesz_coefficient_error {Q : ℕ} (hQ : 2 ≤ Q) {X : ℝ} (hX : 1 < X) :
    |(X ^ 2 / 2 - rieszCount X) / (X * Real.log X) - 1 / (4 * Real.log 3)| ≤
      resolutionError Q * (1 / Real.log 3 + 1 / Real.log X) +
        (returnCost Q + 7 / 8) / Real.log X := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hd : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hr := threeLength_ratio hX
  have hD := effective_riesz_length_error hQ hX.le
  let D := (X ^ 2 / 2 - rieszCount X) / X
  let L := Real.log X
  let n : ℝ := threeLength X
  have he : D / L - 1 / (4 * Real.log 3) =
      (D - n / 4) / L + (n / L - 1 / Real.log 3) / 4 := by field_simp; ring
  have hfirst : |(D - n / 4) / L| ≤
      (5 / 8 + n * resolutionError Q + returnCost Q) / L := by
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hD hL.le
  have hsecond : |(n / L - 1 / Real.log 3) / 4| ≤ (1 / L) / 4 := by
    rw [abs_div, abs_of_nonneg hr.1, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right hr.2 (by norm_num)
  have hratio : n / L ≤ 1 / Real.log 3 + 1 / L := by linarith only [hr.2]
  have hfinal : |D / L - 1 / (4 * Real.log 3)| ≤
      resolutionError Q * (1 / Real.log 3 + 1 / L) + (returnCost Q + 7 / 8) / L := by
    rw [he]
    calc
      _ ≤ |(D - n / 4) / L| + |(n / L - 1 / Real.log 3) / 4| := abs_add_le _ _
      _ ≤ (5 / 8 + n * resolutionError Q + returnCost Q) / L + (1 / L) / 4 :=
        add_le_add hfirst hsecond
      _ = resolutionError Q * (n / L) + (returnCost Q + 7 / 8) / L := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left hratio (resolutionError_nonneg hQ)) le_rfl
  simpa only [D, L, div_div] using hfinal

/-- The effective coefficient bound is for the integral of the actual generalized-integer count. -/
theorem effective_integral_count_coefficient_error {Q : ℕ} (hQ : 2 ≤ Q)
    {X : ℝ} (hX : 1 < X) :
    |(X ^ 2 / 2 - ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) / (X * Real.log X) -
      1 / (4 * Real.log 3)| ≤
      resolutionError Q * (1 / Real.log 3 + 1 / Real.log X) +
        (returnCost Q + 7 / 8) / Real.log X := by
  rw [← rieszCount_eq_integral_count (zero_le_one.trans hX.le)]
  exact effective_riesz_coefficient_error hQ hX

end PositiveNearCount

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
