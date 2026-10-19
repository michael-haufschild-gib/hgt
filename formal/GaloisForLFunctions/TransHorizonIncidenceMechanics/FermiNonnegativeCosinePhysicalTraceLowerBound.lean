import GaloisForLFunctions.HTGeometry.OddDirichletKernel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPhysicalTraceSineUpperBound

/-!
# Nonnegative cosine packets for the physical Fermi trace

Finite dyadic coefficient increments synthesize a mixed-boundary cosine profile
on every odd ray. Exact geometric continuation and pronic weight comparisons give
a complete physical trace lower bound. All coefficient entries are nonnegative.
The odd Dirichlet kernel supplies the exact finite profile mass.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open Finset GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence

private noncomputable def profileAngle (r : ℕ) : ℝ := Real.pi / (2 * (r : ℝ) + 1)
private noncomputable def cosineProfile (r k : ℕ) : ℝ :=
  Real.cos (((k : ℝ) + 1 / 2) * profileAngle r)

private theorem profile_angle_pos (r : ℕ) : 0 < profileAngle r := by
  unfold profileAngle
  positivity

private theorem profile_angle_lt_pi {r : ℕ} (hr : 0 < r) : profileAngle r < Real.pi := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := profile_angle_pos r
  have he : profileAngle r * (2 * (r : ℝ) + 1) = Real.pi := by
    dsimp [profileAngle]
    field_simp
  nlinarith

private theorem profile_end_angle (r : ℕ) :
    ((r : ℝ) + 1 / 2) * profileAngle r = Real.pi / 2 := by
  dsimp [profileAngle]
  field_simp

private theorem profile_end (r : ℕ) : cosineProfile r r = 0 := by
  rw [cosineProfile, profile_end_angle, Real.cos_pi_div_two]

private theorem profile_nonneg (r k : ℕ) (hk : k ≤ r) : 0 ≤ cosineProfile r k := by
  have hp := profile_angle_pos r
  have hkR : (k : ℝ) ≤ r := by exact_mod_cast hk
  have hu : ((k : ℝ) + 1 / 2) * profileAngle r ≤ Real.pi / 2 := by
    rw [← profile_end_angle r]
    exact mul_le_mul_of_nonneg_right (by linarith) hp.le
  have hlo : 0 ≤ ((k : ℝ) + 1 / 2) * profileAngle r := by positivity
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hu

private theorem profile_first_pos {r : ℕ} (hr : 0 < r) : 0 < cosineProfile r 0 := by
  have hp := profile_angle_pos r
  have hu := profile_angle_lt_pi hr
  apply Real.cos_pos_of_mem_Ioo
  simp only [Nat.cast_zero, zero_add]
  constructor <;> nlinarith [Real.pi_pos]

private theorem profile_recurrence (r k : ℕ) :
    cosineProfile r k + cosineProfile r (k + 2) =
      2 * Real.cos (profileAngle r) * cosineProfile r (k + 1) := by
  dsimp only [cosineProfile]
  rw [Real.cos_add_cos]
  have ha : (((k : ℝ) + 1 / 2) * profileAngle r +
      (((k + 2 : ℕ) : ℝ) + 1 / 2) * profileAngle r) / 2 =
      (((k + 1 : ℕ) : ℝ) + 1 / 2) * profileAngle r := by push_cast; ring
  have hb : (((k : ℝ) + 1 / 2) * profileAngle r -
      (((k + 2 : ℕ) : ℝ) + 1 / 2) * profileAngle r) / 2 = -profileAngle r := by
    push_cast
    ring
  rw [ha, hb, Real.cos_neg]
  ring

private theorem profile_first_recurrence (r : ℕ) :
    cosineProfile r 0 + cosineProfile r 1 =
      2 * Real.cos (profileAngle r) * cosineProfile r 0 := by
  dsimp only [cosineProfile]
  simp only [Nat.cast_zero, Nat.cast_one, zero_add]
  rw [Real.cos_add_cos]
  rw [show ((1 / 2 : ℝ) * profileAngle r + (1 + 1 / 2) * profileAngle r) / 2 =
    profileAngle r by ring]
  rw [show ((1 / 2 : ℝ) * profileAngle r - (1 + 1 / 2) * profileAngle r) / 2 =
    -((1 / 2 : ℝ) * profileAngle r) by ring, Real.cos_neg]

private theorem profile_coefficient_nonneg (r k : ℕ) (hk : k + 2 ≤ r) :
    0 ≤ 2 * cosineProfile r (k + 1) - cosineProfile r k := by
  have hrec := profile_recurrence r k
  have hx := profile_nonneg r (k + 1) (by omega)
  have hy := profile_nonneg r (k + 2) hk
  have hc := Real.cos_le_one (profileAngle r)
  nlinarith

private theorem profile_mass (r : ℕ) (hr : 0 < r) :
    (∑ k ∈ range r, (cosineProfile r k)^2) = (2 * (r : ℝ) + 1) / 4 := by
  have hs0 := Real.sin_pos_of_pos_of_lt_pi (profile_angle_pos r) (profile_angle_lt_pi hr)
  have hs := sum_cos_odd (ne_of_gt hs0) r
  have ha : 2 * (r : ℝ) * profileAngle r = Real.pi - profileAngle r := by
    dsimp [profileAngle]
    field_simp
    ring
  rw [ha, Real.sin_pi_sub] at hs
  have hc : (∑ k ∈ range r, Real.cos ((2 * (k : ℝ) + 1) * profileAngle r)) = 1 / 2 := by
    rw [hs]
    field_simp
  have ht (k : ℕ) : (cosineProfile r k)^2 =
      (1 + Real.cos ((2 * (k : ℝ) + 1) * profileAngle r)) / 2 := by
    have h := Real.cos_two_mul (((k : ℝ) + 1 / 2) * profileAngle r)
    rw [show 2 * (((k : ℝ) + 1 / 2) * profileAngle r) =
      (2 * (k : ℝ) + 1) * profileAngle r by ring] at h
    dsimp [cosineProfile]
    linarith
  simp_rw [ht]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hc]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

private theorem profile_energy (r : ℕ) :
    (∑ k ∈ range r, (cosineProfile r k - cosineProfile r (k + 1))^2) =
      (2 - 2 * Real.cos (profileAngle r)) * ∑ k ∈ range r, (cosineProfile r k)^2 := by
  let x := cosineProfile r
  let lam := 2 - 2 * Real.cos (profileAngle r)
  let f := fun k => x k * (x k - x (k + 1))
  have hterm (k : ℕ) : (x k - x (k + 1))^2 =
      f k - f (k + 1) + lam * (x (k + 1))^2 := by
    have h := profile_recurrence r k
    dsimp only [f, lam, x]
    rw [show k + 1 + 1 = k + 2 by omega]
    linear_combination -(cosineProfile r (k + 1)) * h
  have hshift : (∑ k ∈ range r, (x (k + 1))^2) =
      (∑ k ∈ range r, (x k)^2) - (x 0)^2 := by
    have h1 := Finset.sum_range_succ' (fun k => (x k)^2) r
    have h2 := Finset.sum_range_succ (fun k => (x k)^2) r
    have he : x r = 0 := profile_end r
    rw [he, zero_pow (by decide : 2 ≠ 0), add_zero] at h2
    linarith only [h1, h2]
  have hf0 : f 0 = lam * (x 0)^2 := by
    have h := profile_first_recurrence r
    dsimp [f, lam, x]
    linear_combination -(cosineProfile r 0) * h
  have hfr : f r = 0 := by dsimp [f, x]; rw [profile_end]; ring
  change (∑ k ∈ range r, (x k - x (k + 1))^2) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum, hshift, hf0, hfr]
  dsimp only [x, lam]
  ring

/-- Dyadic increments of the finite cosine profile, supported through `2^(L+1)`. -/
noncomputable def fermiDyadicCosineWeight (L d : ℕ) : ℝ :=
  (if d = 2 then 2 * cosineProfile (L + 1) 0 else 0) +
    ∑ k ∈ range L, if d = 2^(k + 2) then
      (2 : ℝ)^(k + 1) * (2 * cosineProfile (L + 1) (k + 1) - cosineProfile (L + 1) k)
    else 0

/-- Every coefficient in the finite dyadic cosine packet is nonnegative. -/
theorem fermiDyadicCosineWeight_nonneg (L d : ℕ) : 0 ≤ fermiDyadicCosineWeight L d := by
  have hx := (profile_first_pos (show 0 < L + 1 by omega)).le
  unfold fermiDyadicCosineWeight
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact mul_nonneg (by positivity) (profile_coefficient_nonneg (L + 1) k (by
        have := Finset.mem_range.mp hk
        omega))
    · rfl

private theorem cosine_sieve (L n : ℕ) :
    sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) n =
      (if 2 ∣ n then 2 * cosineProfile (L + 1) 0 else 0) +
        ∑ k ∈ range L, if 2^(k + 2) ∣ n then
          (2 : ℝ)^(k + 1) * (2 * cosineProfile (L + 1) (k + 1) - cosineProfile (L + 1) k)
        else 0 := by
  unfold sieveSeq fermiDyadicCosineWeight
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have h2 : 2 ≤ (2 : ℕ)^(L + 1) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ L + 1 by omega)
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc,
    show 1 ≤ (2 : ℕ) by decide, h2, true_and]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkL := Finset.mem_range.mp hk
  have hp : 1 ≤ (2 : ℕ)^(k + 2) := by
    have : 0 < (2 : ℕ)^(k + 2) := by positivity
    omega
  have hb : (2 : ℕ)^(k + 2) ≤ 2^(L + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simp only [hp, hb, true_and]

private theorem pow_dvd_odd_ray (a k : ℕ) {b : ℕ} (hb : Odd b) :
    (2 : ℕ)^a ∣ 2^k * b ↔ a ≤ k := by
  rw [(Nat.Coprime.pow_left a hb.coprime_two_left).dvd_mul_right,
    Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))]

private theorem prefix_difference_sum (L k : ℕ) (f : ℕ → ℝ) :
    f 0 + (∑ j ∈ range L, if j < k then f (j + 1) - f j else 0) = f (min L k) := by
  have hs : (range L).filter (fun j => j < k) = range (min L k) := by
    ext j
    simp
  rw [← Finset.sum_filter, hs, Finset.sum_range_sub]
  ring

private theorem cosine_sieve_ray (L k : ℕ) {b : ℕ} (hb : Odd b) :
    sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) (2^(k + 1) * b) =
      (2 : ℝ)^(min L k + 1) * cosineProfile (L + 1) (min L k) := by
  rw [cosine_sieve]
  have h2 : 2 ∣ 2^(k + 1) * b := by
    simpa using (pow_dvd_odd_ray 1 (k + 1) hb).2 (by omega)
  rw [if_pos h2]
  let f := fun j => (2 : ℝ)^(j + 1) * cosineProfile (L + 1) j
  have ht (j : ℕ) :
      (if 2^(j + 2) ∣ 2^(k + 1) * b then
        (2 : ℝ)^(j + 1) * (2 * cosineProfile (L + 1) (j + 1) - cosineProfile (L + 1) j)
      else 0) = if j < k then f (j + 1) - f j else 0 := by
    simp only [pow_dvd_odd_ray (j + 2) (k + 1) hb, show j + 2 ≤ k + 1 ↔ j < k by omega]
    split_ifs
    · dsimp [f]
      simp only [pow_succ]
      ring
    · rfl
  simp_rw [ht]
  have h0 : 2 * cosineProfile (L + 1) 0 = f 0 := by simp [f]
  rw [h0, prefix_difference_sum]

private theorem cosine_sieve_odd (L : ℕ) {b : ℕ} (hb : Odd b) :
    sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) b = 0 := by
  have hn (a : ℕ) (ha : 0 < a) : ¬ (2 : ℕ)^a ∣ b := by
    intro h
    have hz := (pow_dvd_odd_ray a 0 hb).1 (by simpa using h)
    omega
  rw [cosine_sieve, if_neg (by simpa using hn 1 (by decide)), zero_add]
  apply Finset.sum_eq_zero
  intro k _
  exact if_neg (hn (k + 2) (by omega))

private theorem cosine_normalized_head (L k : ℕ) {b : ℕ} (hb : Odd b) (hk : k ≤ L) :
    fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1) =
      cosineProfile (L + 1) k := by
  unfold fermiNormalizedDyadicSieve
  rw [cosine_sieve_ray L k hb, Nat.min_eq_right hk]
  field_simp

private theorem cosine_normalized_tail (L j : ℕ) {b : ℕ} (hb : Odd b) :
    fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (L + j + 1) =
      cosineProfile (L + 1) L / (2 : ℝ)^j := by
  unfold fermiNormalizedDyadicSieve
  rw [cosine_sieve_ray L (L + j) hb, Nat.min_eq_left (by omega)]
  rw [show L + j + 1 = (L + 1) + j by omega, pow_add (2 : ℝ) (L + 1) j]
  field_simp

private theorem cosine_jump_head (L k : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) (hk : k < L) :
    fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1) =
      cosineProfile (L + 1) k - cosineProfile (L + 1) (k + 1) := by
  rw [fermiNormalizedDyadicJump_eq_sub _ _ hb0,
    cosine_normalized_head L k hb (by omega), cosine_normalized_head L (k + 1) hb (by omega)]

private theorem cosine_jump_tail (L j : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (L + j + 1) =
      cosineProfile (L + 1) L / (2 : ℝ)^(j + 1) := by
  rw [fermiNormalizedDyadicJump_eq_sub _ _ hb0, cosine_normalized_tail L j hb,
    show L + j + 1 + 1 = L + (j + 1) + 1 by omega, cosine_normalized_tail L (j + 1) hb,
    pow_succ]
  field_simp
  ring

private theorem half_geometric_square_hasSum (a : ℝ) :
    HasSum (fun j : ℕ => (a / (2 : ℝ)^j)^2) ((4 / 3 : ℝ) * a^2) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (a^2)
  have hv : a^2 * (1 - (1 / 4 : ℝ))⁻¹ = (4 / 3 : ℝ) * a^2 := by norm_num; ring
  rw [hv] at h
  have heq : (fun j : ℕ => (a / (2 : ℝ)^j)^2) = fun j : ℕ => a^2 * (1 / 4 : ℝ)^j := by
    funext j
    have hp : ((2 : ℝ)^j)^2 = (4 : ℝ)^j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    simp only [div_pow, one_pow, hp]
    ring
  rw [heq]
  exact h

private theorem cosine_sieve_tail_hasSum (L : ℕ) {b : ℕ} (hb : Odd b) :
    HasSum (fun j : ℕ =>
      (fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (L + j + 1))^2)
      ((4 / 3 : ℝ) * (cosineProfile (L + 1) L)^2) := by
  have heq : (fun j : ℕ =>
      (fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (L + j + 1))^2) =
      fun j : ℕ => (cosineProfile (L + 1) L / (2 : ℝ)^j)^2 := by
    funext j
    rw [cosine_normalized_tail L j hb]
  rw [heq]
  exact half_geometric_square_hasSum _

private theorem cosine_jump_tail_hasSum (L : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    HasSum (fun j : ℕ =>
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (L + j + 1))^2)
      ((cosineProfile (L + 1) L)^2 / 3) := by
  have heq : (fun j : ℕ =>
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (L + j + 1))^2) =
      fun j : ℕ => ((cosineProfile (L + 1) L / 2) / (2 : ℝ)^j)^2 := by
    funext j
    rw [cosine_jump_tail L j hb hb0]
    simp only [pow_succ, div_div, mul_comm]
  rw [heq]
  have h := half_geometric_square_hasSum (cosineProfile (L + 1) L / 2)
  rw [show (4 / 3 : ℝ) * (cosineProfile (L + 1) L / 2)^2 =
    (cosineProfile (L + 1) L)^2 / 3 by ring] at h
  exact h

private theorem cosine_ray_squares_summable (L : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    Summable (fun k : ℕ =>
      (fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2) ∧
    Summable (fun k : ℕ =>
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2) := by
  constructor
  · apply (summable_nat_add_iff L).1
    simpa only [Nat.add_comm] using (cosine_sieve_tail_hasSum L hb).summable
  · apply (summable_nat_add_iff L).1
    simpa only [Nat.add_comm] using (cosine_jump_tail_hasSum L hb hb0).summable

private theorem cosine_homogeneous_selected_energy (L : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    (∑' k : ℕ, (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2) =
      (2 - 2 * Real.cos (profileAngle (L + 1))) * (2 * ((L + 1 : ℕ) : ℝ) + 1) / 4 -
        (2 / 3 : ℝ) * (cosineProfile (L + 1) L)^2 := by
  have hy := (cosine_ray_squares_summable L hb hb0).2
  have hs := Summable.sum_add_tsum_nat_add L hy
  have ht : (∑' j : ℕ,
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (j + L + 1))^2) =
      (cosineProfile (L + 1) L)^2 / 3 := by
    simpa only [Nat.add_comm] using (cosine_jump_tail_hasSum L hb hb0).tsum_eq
  rw [ht] at hs
  have hp : (∑ k ∈ range L,
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2) =
      ∑ k ∈ range L, (cosineProfile (L + 1) k - cosineProfile (L + 1) (k + 1))^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [cosine_jump_head L k hb hb0 (Finset.mem_range.mp hk)]
  rw [hp] at hs
  have he := profile_energy (L + 1)
  rw [Finset.sum_range_succ, profile_end, sub_zero, profile_mass _ (by omega)] at he
  linarith only [hs, he]

private noncomputable def cosineMass (L : ℕ) : ℝ := (2 * ((L + 1 : ℕ) : ℝ) + 1) / 4
private noncomputable def cosineEnergy (L : ℕ) : ℝ :=
  (2 - 2 * Real.cos (profileAngle (L + 1))) * cosineMass L

private theorem cosine_ray_weighted_summable (L : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    Summable (fun k : ℕ =>
      (fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2 *
        fermiDyadicPronicWeight (k + 1) b) ∧
    Summable (fun k : ℕ =>
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2 *
        fermiDyadicPronicWeight (k + 2) b) := by
  obtain ⟨hx, hy⟩ := cosine_ray_squares_summable L hb hb0
  constructor
  · refine Summable.of_nonneg_of_le (fun k => by unfold fermiDyadicPronicWeight; positivity)
      (fun k => ?_) (hx.mul_right (1 / (b : ℝ)^2))
    exact mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (k + 1) b hb0).2 (sq_nonneg _)
  · refine Summable.of_nonneg_of_le (fun k => by unfold fermiDyadicPronicWeight; positivity)
      (fun k => ?_) (hy.mul_right (1 / (b : ℝ)^2))
    exact mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (k + 2) b hb0).2 (sq_nonneg _)

private theorem prefix_half_weight_sum_le (n : ℕ) :
    (∑ k ∈ range n, 1 / (2 : ℝ)^(k + 1)) ≤ 1 := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2 : ℝ)
  norm_num at h
  have heq : (fun k : ℕ => 1 / (2 : ℝ)^(k + 1)) = fun k : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ)^k := by
    funext k
    simp only [pow_succ, div_pow, one_pow]
    ring
  have hh : HasSum (fun k : ℕ => 1 / (2 : ℝ)^(k + 1)) 1 := by rw [heq]; exact h
  exact (Summable.sum_le_tsum (range n) (fun k _ => by positivity) hh.summable).trans_eq hh.tsum_eq

private theorem cosine_mass_weight_loss (L : ℕ) :
    (∑ k ∈ range (L + 1), (cosineProfile (L + 1) k)^2 / (2 : ℝ)^(k + 1)) ≤ 1 := by
  apply le_trans (Finset.sum_le_sum fun k hk => ?_) (prefix_half_weight_sum_le (L + 1))
  have hx := profile_nonneg (L + 1) k (by have := Finset.mem_range.mp hk; omega)
  have hx1 : cosineProfile (L + 1) k ≤ 1 := Real.cos_le_one _
  have hsq : (cosineProfile (L + 1) k)^2 ≤ 1 := by nlinarith
  exact mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ ((2 : ℝ)^(k + 1))⁻¹)

private theorem cosine_physical_ray_lower (L : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    (cosineMass L - 1) / (b : ℝ)^2 ≤ fermiDyadicRaySieveEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) b := by
  have hp := (cosine_ray_weighted_summable L hb hb0).1
  have hprefix := Summable.sum_le_tsum (range (L + 1))
    (fun k _ => by unfold fermiDyadicPronicWeight; positivity) hp
  have ht (k : ℕ) (hk : k ∈ range (L + 1)) :
      ((cosineProfile (L + 1) k)^2 - (cosineProfile (L + 1) k)^2 / (2 : ℝ)^(k + 1)) /
          (b : ℝ)^2 ≤
      (fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2 *
        fermiDyadicPronicWeight (k + 1) b := by
    rw [cosine_normalized_head L k hb (by have := Finset.mem_range.mp hk; omega)]
    calc
      _ = (cosineProfile (L + 1) k)^2 * ((1 - 1 / (2 : ℝ)^(k + 1)) / (b : ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (fermiDyadicPronicWeight_lower_error (k + 1) b hb0) (sq_nonneg _)
  have hpart := Finset.sum_le_sum ht
  rw [← Finset.sum_div, Finset.sum_sub_distrib, profile_mass _ (by omega)] at hpart
  have hloss := cosine_mass_weight_loss L
  have hm : (cosineMass L - 1) / (b : ℝ)^2 ≤
      (cosineMass L - ∑ k ∈ range (L + 1),
        (cosineProfile (L + 1) k)^2 / (2 : ℝ)^(k + 1)) / (b : ℝ)^2 := by
    exact mul_le_mul_of_nonneg_right (by linarith)
      (inv_nonneg.mpr (sq_nonneg (b : ℝ)))
  exact hm.trans (hpart.trans hprefix)

private theorem cosine_physical_ray_upper (L : ℕ) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    fermiDyadicRaySelectedEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) b ≤ cosineEnergy L / (b : ℝ)^2 := by
  have hy := (cosine_ray_squares_summable L hb hb0).2
  have hq := (cosine_ray_weighted_summable L hb hb0).2
  have hcomp := hq.tsum_le_tsum (fun k =>
    mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (k + 2) b hb0).2 (sq_nonneg _))
    (hy.mul_right (1 / (b : ℝ)^2))
  rw [tsum_mul_right] at hcomp
  have hh : (∑' k : ℕ,
      (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) b (k + 1))^2) ≤ cosineEnergy L := by
    have he := cosine_homogeneous_selected_energy L hb hb0
    dsimp [cosineEnergy, cosineMass]
    nlinarith only [he, sq_nonneg (cosineProfile (L + 1) L)]
  calc
    _ ≤ _ := hcomp
    _ ≤ cosineEnergy L * (1 / (b : ℝ)^2) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

private theorem cosine_physical_ray_ratio (L : ℕ) (hL : 1 ≤ L) {b : ℕ} (hb : Odd b) (hb0 : 0 < b) :
    (cosineMass L - 1) * fermiDyadicRaySelectedEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) b ≤
      cosineEnergy L * fermiDyadicRaySieveEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) b := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hm : 0 ≤ cosineMass L - 1 := by dsimp [cosineMass]; push_cast; linarith
  have he : 0 ≤ cosineEnergy L := by
    unfold cosineEnergy
    apply mul_nonneg
    · linarith [Real.cos_le_one (profileAngle (L + 1))]
    · unfold cosineMass; positivity
  calc
    _ ≤ (cosineMass L - 1) * (cosineEnergy L / (b : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (cosine_physical_ray_upper L hb hb0) hm
    _ = cosineEnergy L * ((cosineMass L - 1) / (b : ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (cosine_physical_ray_lower L hb hb0) he

private theorem cosine_total_ray_decomposition (L : ℕ) :
    sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) =
      ∑' j : ℕ, fermiDyadicRaySieveEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1) ∧
    fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) =
      ∑' j : ℕ, fermiDyadicRaySelectedEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1) := by
  have hz : (∑' j : ℕ, (sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1))^2 /
      (pronicSeq (2 * j + 1) : ℝ)) = 0 := by
    have hzero (j : ℕ) : sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1) = 0 :=
      cosine_sieve_odd L (show Odd (2 * j + 1) from ⟨j, by omega⟩)
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_div, tsum_zero]
  obtain ⟨hp, hq⟩ := sieve_fermi_dyadic_pronic_summable (2^(L + 1)) (fermiDyadicCosineWeight L)
  constructor
  · rw [sieveTotalPronicEnergy_dyadic_rays, hz, zero_add]
    exact (Summable.tsum_comm
      (f := fun k j : ℕ =>
        (fermiNormalizedDyadicSieve (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1) (k + 1))^2 *
          fermiDyadicPronicWeight (k + 1) (2 * j + 1)) hp).symm
  · rw [fermiSelectedTotalPronicEnergy_dyadic_rays, hz, zero_add]
    exact (Summable.tsum_comm
      (f := fun k j : ℕ =>
        (fermiNormalizedDyadicJump (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1) (k + 1))^2 *
          fermiDyadicPronicWeight (k + 2) (2 * j + 1)) hq).symm

private theorem cosine_physical_total_ratio (L : ℕ) (hL : 1 ≤ L) :
    (cosineMass L - 1) * fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) ≤
      cosineEnergy L * sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by
  obtain ⟨hP, hQ⟩ := cosine_total_ray_decomposition L
  obtain ⟨hp, hq⟩ := sieve_fermi_dyadic_pronic_summable (2^(L + 1)) (fermiDyadicCosineWeight L)
  have hps : Summable (fun j : ℕ => fermiDyadicRaySieveEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1)) :=
    hp.prod_symm.prod
  have hqs : Summable (fun j : ℕ => fermiDyadicRaySelectedEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) (2 * j + 1)) :=
    hq.prod_symm.prod
  rw [hP, hQ, ← tsum_mul_left, ← tsum_mul_left]
  exact (hqs.mul_left (cosineMass L - 1)).tsum_le_tsum
    (fun j => cosine_physical_ray_ratio L hL (show Odd (2 * j + 1) from ⟨j, by omega⟩) (by omega))
    (hps.mul_left (cosineEnergy L))

/-- Every dyadic cosine packet has positive complete selected physical energy. -/
theorem fermiDyadicCosine_selected_pos (L : ℕ) :
    0 < fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by
  have hx := profile_first_pos (show 0 < L + 1 by omega)
  have hs1 : sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) 1 = 0 := cosine_sieve_odd L (by decide)
  have hs2 : sieveSeq (2^(L + 1)) (fermiDyadicCosineWeight L) 2 = 2 * cosineProfile (L + 1) 0 := by
    simpa using cosine_sieve_ray L 0 (b := 1) (by decide)
  have hp0 : 0 < sievePairedPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) {0} := by
    norm_num [sievePairedPronicEnergy, hs1, hs2, pronicSeq]
    positivity
  have hP : 0 < sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by
    have hpart := Summable.sum_le_tsum ({0} : Finset ℕ)
      (fun j _ => show 0 ≤ sievePairedPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) {j} by
        unfold sievePairedPronicEnergy
        exact Finset.sum_nonneg fun _ _ => by positivity)
      (sieve_fermi_pronic_summable (2^(L + 1)) (fermiDyadicCosineWeight L)).1
    exact hp0.trans_le (by simpa only [Finset.sum_singleton, sieveTotalPronicEnergy] using hpart)
  have hQ : 0 ≤ fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by
    unfold fermiSelectedTotalPronicEnergy
    apply tsum_nonneg
    intro j
    unfold fermiSelectedPronicEnergy
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hi := sieveTotalPronicEnergy_le_depth_selected (2^(L + 1)) (fermiDyadicCosineWeight L)
  dsimp only at hi
  by_contra hn
  have hz : fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) = 0 :=
    le_antisymm (le_of_not_gt hn) hQ
  rw [hz, mul_zero] at hi
  exact (not_le_of_gt hP) hi

/-- The physical inverse loss of the nonnegative cosine packet is bounded below
by its finite profile mass minus the pronic weight loss, divided by its sine gap. -/
theorem fermiDyadicCosine_physical_ratio (L : ℕ) (hL : 1 ≤ L) :
    let r : ℝ := ((L + 1 : ℕ) : ℝ)
    let S : ℝ := (2 * r + 1) / 4
    (S - 1) * fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) ≤
      (2 - 2 * Real.cos (Real.pi / (2 * r + 1))) * S *
        sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by
  exact cosine_physical_total_ratio L hL

end GaloisForLFunctions.TransHorizonIncidenceMechanics
