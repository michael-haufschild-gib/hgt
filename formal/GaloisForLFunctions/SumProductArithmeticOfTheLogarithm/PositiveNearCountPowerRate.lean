import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountEffectiveAverage
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PolynomialLogarithmicReturns

/-!
# Power convergence for the positive count profile

Polynomial half-turn returns and the profile's logarithmic modulus yield
uniform orbit averages with a fixed positive power rate. The actual weighted
count bridge transfers the same exponent to a power of the logarithmic height.
All constants concern the fixed odd-primes-plus-{3,4} positive-generator system.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
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

/-- Any approximate half-turn controls the profile average by its resolution and boundary cost. -/
theorem profile_average_of_half_turn {Q n k : ℕ} (hQ : 2 ≤ Q) (hn : 1 ≤ n)
    {X : ℝ} (hX : 0 < X) {ℓ : ℤ}
    (happrox : |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / (Q : ℝ)) :
    |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
      resolutionError Q + (k : ℝ) / (2 * (n : ℝ)) := by
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
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
  calc
    _ ≤ μ / 2 + (k : ℝ) * (1 / 2) / (n : ℝ) := hmean
    _ = _ := by dsimp only [μ, resolutionError]; ring


/-- The logarithmic resolution loss is bounded by a square-root loss. -/
theorem resolutionError_le_half_power {Q : ℕ} (hQ : 2 ≤ Q) :
    resolutionError Q ≤ (16 + 32 * Real.log 4 + 2 / 3) * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ0 : (0 : ℝ) < Q := zero_lt_one.trans_le hQ1
  have hs : 1 ≤ (Q : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
  have hlog := Real.log_le_rpow_div hQ0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnum : 8 * Real.log (Q : ℝ) + 32 * Real.log 4 + 2 / 3 ≤
      (16 + 32 * Real.log 4 + 2 / 3) * (Q : ℝ) ^ (1 / 2 : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 32 * Real.log 4 + 2 / 3)
    nlinarith only [hlog, ht]
  calc
    _ ≤ ((16 + 32 * Real.log 4 + 2 / 3) * (Q : ℝ) ^ (1 / 2 : ℝ)) / Q :=
      div_le_div_of_nonneg_right hnum hQ0.le
    _ = _ := by
      have he : (Q : ℝ) ^ (1 / 2 : ℝ) / (Q : ℝ) = (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
        calc
          _ = (Q : ℝ) ^ (1 / 2 : ℝ) / (Q : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hQ0]; norm_num
      rw [mul_div_assoc, he]

/-- A polynomial return cost and the profile modulus yield a fixed positive power rate. -/
theorem exists_resolution_polynomial_rate {M : ℕ} (hM : 1 ≤ M) {A : ℝ} (hA : 0 < A) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∃ Q : ℕ, 2 ≤ Q ∧ resolutionError Q + A * (Q : ℝ) ^ M / Y ≤ K * Y ^ (-η) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM1
  let a : ℝ := 1 / (2 * M)
  let η : ℝ := 1 / (4 * M)
  let C : ℝ := 16 + 32 * Real.log 4 + 2 / 3
  have ha : 0 < a := by dsimp only [a]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηhalf : η ≤ 1 / 2 := by
    dsimp only [η]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * M) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith only [hM1]
  have hC : 0 < C := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    dsimp only [C]
    positivity
  refine ⟨η, C + A * (3 : ℝ) ^ M, hη, by linarith only [hηhalf], by positivity, ?_⟩
  intro Y hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  let u : ℝ := Y ^ a
  have hu1 : 1 ≤ u := Real.one_le_rpow hY ha.le
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  let Q : ℕ := ⌈u⌉₊ + 1
  have huQ : u ≤ (Q : ℝ) := by
    have h := Nat.le_ceil u
    dsimp only [Q]
    push_cast
    linarith only [h]
  have hQ2 : 2 ≤ Q := by
    have hc : (1 : ℝ) ≤ (⌈u⌉₊ : ℝ) := hu1.trans (Nat.le_ceil u)
    have hn : 1 ≤ ⌈u⌉₊ := by exact_mod_cast hc
    dsimp only [Q]
    omega
  have hQup : (Q : ℝ) ≤ 3 * u := by
    have h := Nat.ceil_lt_add_one hu0.le
    dsimp only [Q]
    push_cast
    linarith only [h, hu1]
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hmod : resolutionError Q ≤ C * Y ^ (-η) := by
    calc
      _ ≤ C * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := resolutionError_le_half_power hQ2
      _ ≤ C * u ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hu0 huQ (by norm_num)) hC.le
      _ = _ := by
        dsimp only [u]
        rw [← Real.rpow_mul hY0.le]
        congr 2
        dsimp only [a, η]
        ring
  have htail : A * (Q : ℝ) ^ M / Y ≤ A * (3 : ℝ) ^ M * Y ^ (-η) := by
    calc
      _ ≤ A * (3 * u) ^ M / Y := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQup M) hA.le) hY0.le
      _ = A * (3 : ℝ) ^ M * Y ^ (-(1 / 2 : ℝ)) := by
        rw [mul_pow]
        have he : a * (M : ℝ) = 1 / 2 := by dsimp only [a]; field_simp
        have hu : u ^ M / Y = Y ^ (-(1 / 2 : ℝ)) := by
          dsimp only [u]
          rw [← Real.rpow_natCast (Y ^ a) M, ← Real.rpow_mul hY0.le, he]
          calc
            _ = Y ^ (1 / 2 : ℝ) / Y ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_sub hY0]; norm_num
        rw [← mul_assoc, mul_div_assoc, hu]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hY (by linarith only [hηhalf])) (by positivity)
  refine ⟨Q, hQ2, ?_⟩
  calc
    _ ≤ C * Y ^ (-η) + A * (3 : ℝ) ^ M * Y ^ (-η) := add_le_add hmod htail
    _ = _ := by ring


/-- A profile-average estimate controls the actual integrated count with a universal boundary loss. -/
private theorem count_coefficient_of_profile_average {X ε B : ℝ} (hX : 1 < X) (hε : 0 ≤ ε)
    (havg : |(∑ a ∈ Finset.range (threeLength X), fourProfile (X / (3 : ℝ) ^ a)) /
      (threeLength X : ℝ) - 1 / 4| ≤ ε + B / (threeLength X : ℝ)) :
    |(X ^ 2 / 2 - ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) / (X * Real.log X) -
      1 / (4 * Real.log 3)| ≤ ε * (1 / Real.log 3 + 1 / Real.log X) + (B + 7 / 8) / Real.log X := by
  have hx : 0 < X := zero_lt_one.trans hX
  have hn : 1 ≤ threeLength X := by dsimp only [threeLength]; omega
  have hn0 : (0 : ℝ) < threeLength X := by exact_mod_cast (show 0 < threeLength X by omega)
  let S := ∑ a ∈ Finset.range (threeLength X), fourProfile (X / (3 : ℝ) ^ a)
  have hS : |S - (threeLength X : ℝ) / 4| ≤ (threeLength X : ℝ) * ε + B := by
    have he : S - (threeLength X : ℝ) / 4 =
        (threeLength X : ℝ) * (S / (threeLength X : ℝ) - 1 / 4) := by field_simp
    rw [he, abs_mul, abs_of_pos hn0]
    calc
      _ ≤ (threeLength X : ℝ) * (ε + B / (threeLength X : ℝ)) :=
        mul_le_mul_of_nonneg_left havg hn0.le
      _ = _ := by field_simp
  have hc := pow_log_floor_bracket (b := (3 : ℝ)) (by norm_num) hX.le
  have hbridge := normalized_deficit_profile_error hX.le ⌊Real.log X / Real.log 3⌋₊ hc.1 hc.2
  change |(X ^ 2 / 2 - rieszCount X) / X - S| ≤ 5 / 8 at hbridge
  have hD : |(X ^ 2 / 2 - rieszCount X) / X - (threeLength X : ℝ) / 4| ≤
      5 / 8 + (threeLength X : ℝ) * ε + B := by
    calc
      _ = |((X ^ 2 / 2 - rieszCount X) / X - S) + (S - (threeLength X : ℝ) / 4)| := by
        congr 1
        ring
      _ ≤ |(X ^ 2 / 2 - rieszCount X) / X - S| + |S - (threeLength X : ℝ) / 4| := abs_add_le _ _
      _ ≤ 5 / 8 + ((threeLength X : ℝ) * ε + B) := add_le_add hbridge hS
      _ = _ := by ring
  have hL : 0 < Real.log X := Real.log_pos hX
  have hr := threeLength_ratio hX
  let D := (X ^ 2 / 2 - rieszCount X) / X
  let L := Real.log X
  let n : ℝ := threeLength X
  have he : D / L - 1 / (4 * Real.log 3) =
      (D - n / 4) / L + (n / L - 1 / Real.log 3) / 4 := by field_simp; ring
  have hfirst : |(D - n / 4) / L| ≤ (5 / 8 + n * ε + B) / L := by
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hD hL.le
  have hsecond : |(n / L - 1 / Real.log 3) / 4| ≤ (1 / L) / 4 := by
    rw [abs_div, abs_of_nonneg hr.1, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right hr.2 (by norm_num)
  have hratio : n / L ≤ 1 / Real.log 3 + 1 / L := by linarith only [hr.2]
  have hfinal : |D / L - 1 / (4 * Real.log 3)| ≤
      ε * (1 / Real.log 3 + 1 / L) + (B + 7 / 8) / L := by
    rw [he]
    calc
      _ ≤ |(D - n / 4) / L| + |(n / L - 1 / Real.log 3) / 4| := abs_add_le _ _
      _ ≤ (5 / 8 + n * ε + B) / L + (1 / L) / 4 := add_le_add hfirst hsecond
      _ = ε * (n / L) + (B + 7 / 8) / L := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hratio hε) le_rfl
  rw [← rieszCount_eq_integral_count hx.le]
  simpa only [D, L, div_div] using hfinal

/-- Fixed polynomial return costs control both profile averages and the actual count coefficient. -/
theorem exists_polynomial_profile_remainders :
    ∃ M : ℕ, 2 ≤ M ∧ ∃ A : ℝ, 0 < A ∧
      (∀ Q n : ℕ, 2 ≤ Q → 1 ≤ n → ∀ X : ℝ, 0 < X →
        |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
          resolutionError Q + A * (Q : ℝ) ^ M / n) ∧
      (∀ Q : ℕ, 2 ≤ Q → ∀ X : ℝ, 1 < X →
        |(X ^ 2 / 2 - ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) / (X * Real.log X) -
          1 / (4 * Real.log 3)| ≤ resolutionError Q * (1 / Real.log 3 + 1 / Real.log X) +
          (A * (Q : ℝ) ^ M + 7 / 8) / Real.log X) := by
  obtain ⟨D, hD, A, hA, hreturn⟩ := exists_polynomial_three_four_half_turn
  have havg (Q n : ℕ) (hQ : 2 ≤ Q) (hn : 1 ≤ n) (X : ℝ) (hX : 0 < X) :
      |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
        resolutionError Q + A * (Q : ℝ) ^ (D + 1) / n := by
    obtain ⟨k, _, hk, ℓ, hclose⟩ := hreturn Q hQ
    have h := profile_average_of_half_turn hQ hn hX hclose
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcost : (k : ℝ) / (2 * (n : ℝ)) ≤ A * (Q : ℝ) ^ (D + 1) / n := by
      have hkhalf : (k : ℝ) / 2 ≤ A * (Q : ℝ) ^ (D + 1) := by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        linarith only [hk, hk0]
      simpa only [div_div, mul_comm (n : ℝ) 2] using div_le_div_of_nonneg_right hkhalf hn0.le
    exact h.trans (add_le_add le_rfl hcost)
  refine ⟨D + 1, by omega, A, hA, havg, ?_⟩
  intro Q hQ X hX
  exact count_coefficient_of_profile_average hX (resolutionError_nonneg hQ)
    (havg Q (threeLength X) hQ (by dsimp only [threeLength]; omega) X (zero_lt_one.trans hX))


/-- One positive exponent controls every starting scale and the actual integrated counting error. -/
theorem exists_profile_and_count_power_rate :
    ∃ η K L : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧ 0 < L ∧
      (∀ n : ℕ, 1 ≤ n → ∀ X : ℝ, 0 < X →
        |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
          K * (n : ℝ) ^ (-η)) ∧
      (∀ X : ℝ, Real.exp 1 ≤ X →
        |(X ^ 2 / 2 - ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) / (X * Real.log X) -
          1 / (4 * Real.log 3)| ≤ L * (Real.log X) ^ (-η)) := by
  obtain ⟨M, hM, A, hA, havg, hcount⟩ := exists_polynomial_profile_remainders
  obtain ⟨η, K, hη, hη1, hK, hbalance⟩ := exists_resolution_polynomial_rate (by omega : 1 ≤ M) hA
  have hd : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let c : ℝ := 1 / Real.log 3 + 1
  have hc1 : 1 ≤ c := by
    have hp := one_div_pos.mpr hd
    dsimp only [c]
    linarith only [hp]
  have hc : 0 < c := zero_lt_one.trans_le hc1
  refine ⟨η, K, c * K + 7 / 8, hη, hη1, hK, by positivity, ?_, ?_⟩
  · intro n hn X hX
    obtain ⟨Q, hQ, hb⟩ := hbalance n (by exact_mod_cast hn)
    exact (havg Q n hQ hn X hX).trans hb
  · intro X hX
    have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hX1 : 1 < X := he.trans_le hX
    have hY : 1 ≤ Real.log X := by
      have h := Real.log_le_log (Real.exp_pos 1) hX
      simpa only [Real.log_exp] using h
    have hY0 : 0 < Real.log X := zero_lt_one.trans_le hY
    obtain ⟨Q, hQ, hb⟩ := hbalance (Real.log X) hY
    have hR := resolutionError_nonneg hQ
    have hB : 0 ≤ A * (Q : ℝ) ^ M / Real.log X := by positivity
    have hrecip : 1 / Real.log X ≤ 1 := by
      apply (div_le_iff₀ hY0).mpr
      simpa only [one_mul] using hY
    have hfactor : 1 / Real.log 3 + 1 / Real.log X ≤ c := by
      dsimp only [c]
      linarith only [hrecip]
    have htail : (7 / 8 : ℝ) / Real.log X ≤ (7 / 8 : ℝ) * (Real.log X) ^ (-η) := by
      have hp : (Real.log X) ^ (-1 : ℝ) ≤ (Real.log X) ^ (-η) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith only [hη1])
      rw [Real.rpow_neg hY0.le, Real.rpow_one] at hp
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 7 / 8)
    calc
      _ ≤ resolutionError Q * (1 / Real.log 3 + 1 / Real.log X) +
          (A * (Q : ℝ) ^ M + 7 / 8) / Real.log X := hcount Q hQ X hX1
      _ ≤ c * (resolutionError Q + A * (Q : ℝ) ^ M / Real.log X) + (7 / 8 : ℝ) / Real.log X := by
        have h1 := mul_le_mul_of_nonneg_left hfactor hR
        have h2 := mul_le_mul_of_nonneg_right hc1 hB
        rw [add_div]
        calc
          _ ≤ resolutionError Q * c +
              (c * (A * (Q : ℝ) ^ M / Real.log X) + (7 / 8 : ℝ) / Real.log X) :=
            add_le_add h1 (add_le_add (by simpa only [one_mul] using h2) le_rfl)
          _ = _ := by ring
      _ ≤ c * (K * (Real.log X) ^ (-η)) + (7 / 8 : ℝ) * (Real.log X) ^ (-η) :=
        add_le_add (mul_le_mul_of_nonneg_left hb hc.le) htail
      _ = _ := by ring


end PositiveNearCount
end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
