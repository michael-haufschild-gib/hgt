import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPronicRayWeightAndTailControl
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ArithmeticUncertaintyAndSpikeCancellation

/-!
# A sine bound for the complete physical Fermi trace

The existing path inequality controls the finite head of each dyadic ray.
Exact physical weights and the geometric tail then transfer the mixed-boundary
sine estimate to the full trace. The free cutoff and square-penalty parameter
keep lower-order costs explicit for subsequent asymptotic analysis.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open RHTower GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

private theorem ray_interval_difference (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b)
    (a n : ℕ) :
    (fermiNormalizedDyadicSieve N c b a - fermiNormalizedDyadicSieve N c b (a + n))^2 ≤
      (n : ℝ) * ∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k))^2 := by
  have h := sq_sub_le_length_mul_sum_range_addDiff_sq
    (fermiNormalizedDyadicSieve N c b) a n
  have hs : (∑ k ∈ Finset.range n,
      (fermiNormalizedDyadicSieve N c b (a + k + 1) -
        fermiNormalizedDyadicSieve N c b (a + k))^2) =
      ∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k))^2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [fermiNormalizedDyadicJump_eq_sub N c hb]
    ring
  rw [hs] at h
  nlinarith only [h]

private theorem tail_sum_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (D a n : ℕ) (ha : 1 ≤ a) (hn : a + n = D + 1) :
    (∑ k ∈ Finset.range n, f (a + k)) ≤ ∑ k ∈ Finset.range D, f (k + 1) := by
  have hd : D = (a - 1) + n := by omega
  rw [hd, Finset.sum_range_add]
  have heq : (∑ k ∈ Finset.range n, f (a - 1 + k + 1)) =
      ∑ k ∈ Finset.range n, f (a + k) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    omega
  rw [heq]
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range (a - 1), f (k + 1) :=
    Finset.sum_nonneg fun k _ => hf (k + 1)
  linarith

private theorem ray_value_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b)
    (a : ℕ) (ha : 1 ≤ a) (haD : a ≤ Nat.log 2 N + 1) :
    (fermiNormalizedDyadicSieve N c b a)^2 ≤
      2 * ((Nat.log 2 N + 1 : ℕ) + 1 : ℝ) *
        ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          (fermiNormalizedDyadicJump N c b (k + 1))^2 := by
  let D := Nat.log 2 N + 1
  let n := D + 1 - a
  have hn : a + n = D + 1 := by dsimp [n, D]; omega
  have hn0 : 0 < n := by dsimp [n, D]; omega
  have hD0 : 0 < D := by dsimp [D]; omega
  have hnD : (n : ℝ) ≤ D := by exact_mod_cast (show n ≤ D by omega)
  let E := ∑ k ∈ Finset.range D, (fermiNormalizedDyadicJump N c b (k + 1))^2
  have hE : 0 ≤ E := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsub := tail_sum_le (fun k => (fermiNormalizedDyadicJump N c b k)^2)
    (fun k => sq_nonneg _) D a n ha hn
  have hdiff := ray_interval_difference N c hb a n
  have hterm : fermiNormalizedDyadicSieve N c b (a + n) =
      fermiNormalizedDyadicJump N c b D := by
    rw [hn]
    exact (fermiNormalizedDyadicJump_depth_boundary N c hb).symm
  rw [hterm] at hdiff
  have hbd : (fermiNormalizedDyadicJump N c b D)^2 ≤ E := by
    have h := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range D) => sq_nonneg (fermiNormalizedDyadicJump N c b (k + 1)))
      (show D - 1 ∈ Finset.range D by simp only [Finset.mem_range]; omega)
    rw [show D - 1 + 1 = D by omega] at h
    exact h
  have h1 := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h2 := mul_le_mul_of_nonneg_right hnD hE
  change (fermiNormalizedDyadicSieve N c b a)^2 ≤ 2 * ((D : ℝ) + 1) * E
  nlinarith only [hdiff, h1, h2, hbd,
    sq_nonneg (fermiNormalizedDyadicSieve N c b a -
      2 * fermiNormalizedDyadicJump N c b D)]

/-- Complete physical sieve energy along the dyadic ray based at b. -/
noncomputable def fermiDyadicRaySieveEnergy (N : ℕ) (c : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑' k : ℕ, (fermiNormalizedDyadicSieve N c b (k + 1))^2 * fermiDyadicPronicWeight (k + 1) b

/-- Complete selected-jump energy along the dyadic ray based at b. -/
noncomputable def fermiDyadicRaySelectedEnergy (N : ℕ) (c : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑' k : ℕ, (fermiNormalizedDyadicJump N c b (k + 1))^2 * fermiDyadicPronicWeight (k + 2) b

private theorem weight_nonneg (k b : ℕ) : 0 ≤ fermiDyadicPronicWeight k b := by
  unfold fermiDyadicPronicWeight
  positivity

private theorem homogeneous_le_weight (k l b : ℕ) (hkl : k ≤ l) (hb : 0 < b) :
    1 / (b : ℝ)^2 ≤ (1 + 1 / (2 : ℝ)^k) * fermiDyadicPronicWeight l b := by
  have ha : (0 : ℝ) < 2^k := by positivity
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  calc
    1 / (b : ℝ)^2 = (1 + 1 / (2 : ℝ)^k) *
        ((2 : ℝ)^k / (((2 : ℝ)^k + 1) * (b : ℝ)^2)) := by
      field_simp
    _ ≤ (1 + 1 / (2 : ℝ)^k) * fermiDyadicPronicWeight k b :=
      mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds k b hb).1 (by positivity)
    _ ≤ (1 + 1 / (2 : ℝ)^k) * fermiDyadicPronicWeight l b :=
      mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_mono k l b hkl hb) (by positivity)

private theorem ray_squares_summable (N : ℕ) (c : ℕ → ℝ) (b a : ℕ) :
    Summable (fun j : ℕ => (fermiNormalizedDyadicSieve N c b (a + j))^2) := by
  have hh := (fermiNormalizedDyadicSieve_tail_hasSum N c b a).summable
  have heq : (fun j : ℕ => (fermiNormalizedDyadicSieve N c b (a + (j + (Nat.log 2 N + 1))))^2) =
      fun j : ℕ => (fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + a + j))^2 := by
    funext j
    congr 2
    omega
  apply (summable_nat_add_iff (Nat.log 2 N + 1)).mp
  rw [heq]
  exact hh

private theorem ray_jump_squares_summable (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) (a : ℕ) :
    Summable (fun j : ℕ => (fermiNormalizedDyadicJump N c b (a + j))^2) := by
  have hh := ((ray_squares_summable N c b a).mul_left (2 : ℝ)).add
    ((ray_squares_summable N c b (a + 1)).mul_left (2 : ℝ))
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hh
  rw [fermiNormalizedDyadicJump_eq_sub N c hb,
    show a + 1 + j = a + j + 1 by omega]
  nlinarith only [sq_nonneg (fermiNormalizedDyadicSieve N c b (a + j) +
    fermiNormalizedDyadicSieve N c b (a + j + 1))]

private theorem ray_weighted_summable (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) (a : ℕ) :
    Summable (fun j : ℕ => (fermiNormalizedDyadicSieve N c b (a + j))^2 *
      fermiDyadicPronicWeight (a + j) b) ∧
    Summable (fun j : ℕ => (fermiNormalizedDyadicJump N c b (a + j))^2 *
      fermiDyadicPronicWeight (a + j + 1) b) := by
  constructor
  · refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (weight_nonneg _ _)) (fun j => ?_)
      ((ray_squares_summable N c b a).mul_right (1 / (b : ℝ)^2))
    exact mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (a + j) b hb).2 (sq_nonneg _)
  · refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (weight_nonneg _ _)) (fun j => ?_)
      ((ray_jump_squares_summable N c hb a).mul_right (1 / (b : ℝ)^2))
    exact mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (a + j + 1) b hb).2 (sq_nonneg _)

private theorem finite_jump_mass_le_ray (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) (a n : ℕ) (ha : 1 ≤ a) :
    (1 / (b : ℝ)^2) * (∑ k ∈ Finset.range n,
      (fermiNormalizedDyadicJump N c b (a + k))^2) ≤
      (1 + 1 / (2 : ℝ)^(a + 1)) * fermiDyadicRaySelectedEnergy N c b := by
  let f := fun k => (fermiNormalizedDyadicJump N c b k)^2 * fermiDyadicPronicWeight (k + 1) b
  have hf : ∀ k, 0 ≤ f k := fun k => mul_nonneg (sq_nonneg _) (weight_nonneg _ _)
  have hq : Summable (fun k : ℕ => f (k + 1)) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, f] using
      (ray_weighted_summable N c hb 1).2
  have hpart := tail_sum_le f hf (a - 1 + n) a n ha (by omega)
  have hprefix := Summable.sum_le_tsum (Finset.range (a - 1 + n))
    (fun k _ => hf (k + 1)) hq
  have hsub : (∑ k ∈ Finset.range n, f (a + k)) ≤ fermiDyadicRaySelectedEnergy N c b := by
    change (∑ k ∈ Finset.range n, f (a + k)) ≤ ∑' k : ℕ, f (k + 1)
    exact hpart.trans hprefix
  calc
    (1 / (b : ℝ)^2) * (∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k))^2)
        ≤ (1 + 1 / (2 : ℝ)^(a + 1)) * (∑ k ∈ Finset.range n, f (a + k)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have h := mul_le_mul_of_nonneg_left
        (homogeneous_le_weight (a + 1) (a + k + 1) b (by omega) hb)
        (sq_nonneg (fermiNormalizedDyadicJump N c b (a + k)))
      dsimp only [f]
      nlinarith only [h]
    _ ≤ (1 + 1 / (2 : ℝ)^(a + 1)) * fermiDyadicRaySelectedEnergy N c b :=
      mul_le_mul_of_nonneg_left hsub (by positivity)

private theorem weighted_head_cell_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) (a : ℕ) (ha : 1 ≤ a) (haD : a ≤ Nat.log 2 N + 1) :
    (fermiNormalizedDyadicSieve N c b a)^2 * fermiDyadicPronicWeight a b ≤
      (5 / 2 : ℝ) * ((Nat.log 2 N + 1 : ℕ) + 1 : ℝ) * fermiDyadicRaySelectedEnergy N c b := by
  have hpoint := ray_value_bound N c hb a ha haD
  have henergy := finite_jump_mass_le_ray N c hb 1 (Nat.log 2 N + 1) (by omega)
  norm_num only [Nat.reduceAdd, Nat.add_comm 1] at henergy
  have hw := mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds a b hb).2
    (sq_nonneg (fermiNormalizedDyadicSieve N c b a))
  have h1 := mul_le_mul_of_nonneg_right hpoint (show (0 : ℝ) ≤ 1 / (b : ℝ)^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left henergy
    (show (0 : ℝ) ≤ 2 * ((Nat.log 2 N + 1 : ℕ) + 1 : ℝ) by positivity)
  nlinarith only [hw, h1, h2]

private theorem weighted_ray_tail_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) (K n : ℕ) (hK : 1 ≤ K) (hn : K + n = Nat.log 2 N + 2)
    (hn0 : 0 < n) (M : ℝ) (hM : 0 ≤ M) :
    let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
    M * lam * (∑' j : ℕ, (fermiNormalizedDyadicSieve N c b (K + j))^2 *
      fermiDyadicPronicWeight (K + j) b) ≤
      (1 + 1 / (2 : ℝ)^(K + 1)) *
        ((M + 1) + M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam) *
          fermiDyadicRaySelectedEnergy N c b := by
  dsimp only
  let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
  let G := (M + 1) + M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    linarith [Real.cos_le_one (Real.pi / (((2 * n : ℕ) : ℝ) + 1))]
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hP := (ray_weighted_summable N c hb K).1
  have hX := ray_squares_summable N c b K
  have hcmp := hP.tsum_le_tsum (fun j =>
      mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (K + j) b hb).2 (sq_nonneg _))
    (hX.mul_right (1 / (b : ℝ)^2))
  rw [tsum_mul_right] at hcmp
  have hmass := fermiNormalizedDyadicSieve_complete_ray_sine_bound N c hb K n hn hn0 M hM
  dsimp only at hmass
  have hfinite := finite_jump_mass_le_ray N c hb K n hK
  have h1 := mul_le_mul_of_nonneg_left hcmp (mul_nonneg hM hlam)
  have h2 := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 1 / (b : ℝ)^2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hfinite hG
  dsimp only [lam, G] at h1 h2 h3
  nlinarith only [h1, h2, h3]

/-- An explicit sine bound for one complete physical dyadic ray. -/
theorem fermiDyadicRay_sine_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) (K : ℕ) (hK : 1 ≤ K) (hKD : K ≤ Nat.log 2 N + 1)
    (M : ℝ) (hM : 0 ≤ M) :
    let D := Nat.log 2 N + 1
    let n := D + 1 - K
    let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
    M * lam * fermiDyadicRaySieveEnergy N c b ≤
      ((1 + 1 / (2 : ℝ)^(K + 1)) *
        ((M + 1) + M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam) +
        (5 / 2 : ℝ) * (K - 1 : ℕ) * ((D : ℝ) + 1) * M * lam) *
        fermiDyadicRaySelectedEnergy N c b := by
  dsimp only
  let D := Nat.log 2 N + 1
  let n := D + 1 - K
  let L := K - 1
  let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
  have hn : K + n = Nat.log 2 N + 2 := by dsimp [n, D]; omega
  have hn0 : 0 < n := by dsimp [n, D]; omega
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    linarith [Real.cos_le_one (Real.pi / (((2 * n : ℕ) : ℝ) + 1))]
  have hhead : (∑ j ∈ Finset.range L,
      (fermiNormalizedDyadicSieve N c b (j + 1))^2 * fermiDyadicPronicWeight (j + 1) b) ≤
      (5 / 2 : ℝ) * L * ((D : ℝ) + 1) * fermiDyadicRaySelectedEnergy N c b := by
    have hh := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range L) =>
      weighted_head_cell_bound N c hb (j + 1) (by omega)
        (by have h := Finset.mem_range.mp hj; dsimp [L] at h; omega))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm, D] using hh
  have hP : Summable (fun j : ℕ =>
      (fermiNormalizedDyadicSieve N c b (j + 1))^2 * fermiDyadicPronicWeight (j + 1) b) := by
    simpa only [Nat.add_comm 1] using (ray_weighted_summable N c hb 1).1
  have hsplit := Summable.sum_add_tsum_nat_add L hP
  have heq : (∑' j : ℕ, (fermiNormalizedDyadicSieve N c b (j + L + 1))^2 *
      fermiDyadicPronicWeight (j + L + 1) b) =
      ∑' j : ℕ, (fermiNormalizedDyadicSieve N c b (K + j))^2 * fermiDyadicPronicWeight (K + j) b := by
    apply tsum_congr
    intro j
    rw [show j + L + 1 = K + j by dsimp [L]; omega]
  rw [heq] at hsplit
  change _ + _ = fermiDyadicRaySieveEnergy N c b at hsplit
  have htail := weighted_ray_tail_bound N c hb K n hK hn hn0 M hM
  dsimp only at htail
  have hhead' := mul_le_mul_of_nonneg_left hhead (mul_nonneg hM hlam)
  dsimp only [L, D, n, lam] at hhead' htail
  rw [← hsplit]
  nlinarith only [hhead', htail]

private theorem total_energy_rays (N : ℕ) (c : ℕ → ℝ) :
    sieveTotalPronicEnergy N c =
      (∑' m : ℕ, (sieveSeq N c (2 * m + 1))^2 / (pronicSeq (2 * m + 1) : ℝ)) +
        ∑' j : ℕ, fermiDyadicRaySieveEnergy N c (2 * j + 1) ∧
    fermiSelectedTotalPronicEnergy N c =
      (∑' m : ℕ, (sieveSeq N c (2 * m + 1))^2 / (pronicSeq (2 * m + 1) : ℝ)) +
        ∑' j : ℕ, fermiDyadicRaySelectedEnergy N c (2 * j + 1) := by
  constructor
  · rw [sieveTotalPronicEnergy_dyadic_rays]
    congr 1
    exact (Summable.tsum_comm (f := fun k j : ℕ =>
      (fermiNormalizedDyadicSieve N c (2 * j + 1) (k + 1))^2 *
        fermiDyadicPronicWeight (k + 1) (2 * j + 1))
      (sieve_fermi_dyadic_pronic_summable N c).1).symm
  · rw [fermiSelectedTotalPronicEnergy_dyadic_rays]
    congr 1
    exact (Summable.tsum_comm (f := fun k j : ℕ =>
      (fermiNormalizedDyadicJump N c (2 * j + 1) (k + 1))^2 *
        fermiDyadicPronicWeight (k + 2) (2 * j + 1))
      (sieve_fermi_dyadic_pronic_summable N c).2).symm

/-- An unconditional physical trace bound with explicit head and terminal costs. -/
theorem sieveTotalPronicEnergy_scaled_sine_bound (N : ℕ) (c : ℕ → ℝ)
    (K : ℕ) (hK : 1 ≤ K) (hKD : K ≤ Nat.log 2 N + 1) (M : ℝ) (hM : 0 ≤ M) :
    let D := Nat.log 2 N + 1
    let n := D + 1 - K
    let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
    M * lam * sieveTotalPronicEnergy N c ≤
      ((1 + 1 / (2 : ℝ)^(K + 1)) *
        ((M + 1) + M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam) +
        (5 / 2 : ℝ) * (K - 1 : ℕ) * ((D : ℝ) + 1) * M * lam) *
        fermiSelectedTotalPronicEnergy N c := by
  dsimp only
  let D := Nat.log 2 N + 1
  let n := D + 1 - K
  let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
  let G := (M + 1) + M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam
  let C := (1 + 1 / (2 : ℝ)^(K + 1)) * G +
    (5 / 2 : ℝ) * (K - 1 : ℕ) * ((D : ℝ) + 1) * M * lam
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by dsimp [n, D]; omega)
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    linarith [Real.cos_le_one (Real.pi / (((2 * n : ℕ) : ℝ) + 1))]
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hC : M * lam ≤ C := by
    have hA := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ M + 1 by linarith)
      (mul_nonneg hM hlam)
    have hB := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ M * lam * (M + 1) by positivity)
    have htail : 0 ≤ (4 / 3 : ℝ) * M * lam := by positivity
    have hscale : 0 ≤ (1 / (2 : ℝ)^(K + 1)) * G := by positivity
    have hhead : 0 ≤ (5 / 2 : ℝ) * (K - 1 : ℕ) * ((D : ℝ) + 1) * M * lam := by positivity
    dsimp only [C, G] at hscale ⊢
    nlinarith only [hA, hB, htail, hscale, hhead, hM]
  have hp : Summable (fun j : ℕ => fermiDyadicRaySieveEnergy N c (2 * j + 1)) :=
    (sieve_fermi_dyadic_pronic_summable N c).1.prod_symm.prod
  have hq : Summable (fun j : ℕ => fermiDyadicRaySelectedEnergy N c (2 * j + 1)) :=
    (sieve_fermi_dyadic_pronic_summable N c).2.prod_symm.prod
  have hs := (hp.mul_left (M * lam)).tsum_le_tsum (fun j =>
      (show M * lam * fermiDyadicRaySieveEnergy N c (2 * j + 1) ≤ C * fermiDyadicRaySelectedEnergy N c (2 * j + 1) from
        fermiDyadicRay_sine_bound N c (by omega) K hK hKD M hM))
    (hq.mul_left C)
  rw [tsum_mul_left, tsum_mul_left] at hs
  let O := ∑' m : ℕ, (sieveSeq N c (2 * m + 1))^2 / (pronicSeq (2 * m + 1) : ℝ)
  have hO : 0 ≤ O := tsum_nonneg fun _ => by positivity
  have hod := mul_le_mul_of_nonneg_right hC hO
  obtain ⟨hP, hQ⟩ := total_energy_rays N c
  change sieveTotalPronicEnergy N c = O + _ at hP
  change fermiSelectedTotalPronicEnergy N c = O + _ at hQ
  change M * lam * sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c
  rw [hP, hQ]
  nlinarith only [hs, hod]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
