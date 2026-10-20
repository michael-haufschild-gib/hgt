import GaloisForLFunctions.TransHorizonIncidenceMechanics.DirichletChainDoubledPrefixAndRobinRamp
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPhysicalOptimalConstants

/-!
# The all-boundary Fermi trace: Dirichlet rays

The selected Fermi schedule reads odd boundaries and boundaries divisible by four. Adding the
boundaries `n ≡ 2 (mod 4)` gives the trace of every reciprocal-cell boundary. Along a dyadic
ray `2^k b` (`b` odd) with normalized sieve values `y_k` and normalized jumps
`x_k = y_k - y_{k+1}`, the selected trace sees `y₀` and `x_k` for `k ≥ 1` only: the step from
the odd base to its first double is unobserved and the ray is free at its bottom. The extra
boundaries observe exactly that step, so every ray becomes pinned at both ends: below by the
observed base value, above by horizon saturation, whose geometric tail costs as much as a
three-step ramp to zero.

The physical weights `w_k(b) = 4^k / ((2^k b)(2^k b + 1))` are at least `1/(2 b²)` and at
least `ρ_m / b²` with `ρ_m = 2^(m+1)/(2^(m+1)+1)` beyond level `m`. Splitting the first `m + 1`
steps into half-steps absorbs the low-level weight deficit, and the soft-prefix Dirichlet chain
bound gives, on every ray, physical sieve energy at most
`(1/λ + 1)/ρ_m` times the all-boundary energy, with `λ = 2 - 2 cos(π/(D + m + 5))` and
`D = log₂ N + 1`.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Physical energy of the boundary readings at twice odd integers, the cells omitted by the
selected schedule. -/
def fermiTwiceOddPronicEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, fermiBoundaryJump N c (4 * m + 2) ^ 2 / (pronicSeq (4 * m + 2) : ℝ)

/-- Physical energy of the trace of every reciprocal-cell boundary. -/
def fermiAllBoundaryPronicEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  fermiSelectedTotalPronicEnergy N c + fermiTwiceOddPronicEnergy N c

/-- Physical sieve energy carried by the dyadic ray over `b`, base included. -/
def fermiRaySieveEnergy (N : ℕ) (c : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑' k : ℕ, fermiNormalizedDyadicSieve N c b k ^ 2 * fermiDyadicPronicWeight k b

/-- Physical all-boundary energy carried by the dyadic ray over `b`, base included. -/
def fermiRayAllBoundaryEnergy (N : ℕ) (c : ℕ → ℝ) (b : ℕ) : ℝ :=
  fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
    ∑' k : ℕ, fermiNormalizedDyadicJump N c b k ^ 2 * fermiDyadicPronicWeight (k + 1) b

/-- The weight ratio `ρ_m = 2^(m+1)/(2^(m+1)+1)` available beyond level `m`. -/
def fermiRayWeightFloor (m : ℕ) : ℝ := (2 : ℝ) ^ (m + 1) / ((2 : ℝ) ^ (m + 1) + 1)

theorem fermiRayWeightFloor_pos (m : ℕ) : 0 < fermiRayWeightFloor m := by
  unfold fermiRayWeightFloor; positivity

theorem fermiRayWeightFloor_le_one (m : ℕ) : fermiRayWeightFloor m ≤ 1 := by
  unfold fermiRayWeightFloor
  rw [div_le_one (by positivity)]
  linarith

/-! ### Ray summability and tails -/

/-- Physical ray weights are nonnegative. -/
theorem fermiDyadicPronicWeight_nonneg (k b : ℕ) : 0 ≤ fermiDyadicPronicWeight k b := by
  unfold fermiDyadicPronicWeight; positivity

/-- The normalized sieve values are square-summable along every ray. -/
theorem fermiRay_sq_summable (N : ℕ) (c : ℕ → ℝ) (b : ℕ) :
    Summable (fun k : ℕ => fermiNormalizedDyadicSieve N c b k ^ 2) := by
  have h := (fermiNormalizedDyadicSieve_tail_hasSum N c b 0).summable
  apply (summable_nat_add_iff (Nat.log 2 N + 1)).mp
  have heq : (fun j : ℕ => fermiNormalizedDyadicSieve N c b (j + (Nat.log 2 N + 1)) ^ 2) =
      fun j : ℕ => fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + 0 + j) ^ 2 := by
    funext j
    rw [show j + (Nat.log 2 N + 1) = Nat.log 2 N + 1 + 0 + j by omega]
  rw [heq]
  exact h

/-- The normalized jumps are square-summable along every ray. -/
theorem fermiRay_jump_sq_summable (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) :
    Summable (fun k : ℕ => fermiNormalizedDyadicJump N c b k ^ 2) := by
  have hs := fermiRay_sq_summable N c b
  have hh := (hs.mul_left 2).add (((summable_nat_add_iff 1).mpr hs).mul_left 2)
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hh
  rw [fermiNormalizedDyadicJump_eq_sub N c hb]
  nlinarith [sq_nonneg (fermiNormalizedDyadicSieve N c b k +
    fermiNormalizedDyadicSieve N c b (k + 1))]

/-- Both physical ray families are summable along the ray. -/
theorem fermiRay_weighted_summable (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) :
    Summable (fun k : ℕ => fermiNormalizedDyadicSieve N c b k ^ 2 *
      fermiDyadicPronicWeight k b) ∧
    Summable (fun k : ℕ => fermiNormalizedDyadicJump N c b k ^ 2 *
      fermiDyadicPronicWeight (k + 1) b) := by
  constructor
  · refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _))
      (fun k => ?_) ((fermiRay_sq_summable N c b).mul_right (1 / (b : ℝ) ^ 2))
    exact mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds k b hb).2 (sq_nonneg _)
  · refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _))
      (fun k => ?_) ((fermiRay_jump_sq_summable N c hb).mul_right (1 / (b : ℝ) ^ 2))
    exact mul_le_mul_of_nonneg_left (fermiDyadicPronicWeight_bounds (k + 1) b hb).2 (sq_nonneg _)

/-- Beyond saturation the sieve values sum to one third of the last free square. -/
theorem fermiRay_value_tail (N : ℕ) (c : ℕ → ℝ) (b : ℕ) :
    ∑' j : ℕ, fermiNormalizedDyadicSieve N c b (j + (Nat.log 2 N + 1 + 1)) ^ 2 =
      fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1) ^ 2 / 3 := by
  have h := fermiNormalizedDyadicSieve_tail_hasSum N c b 0
  simp only [Nat.add_zero] at h
  have h2 := h.summable.tsum_eq_zero_add
  rw [h.tsum_eq] at h2
  have hshift : (∑' j : ℕ, fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + (j + 1)) ^ 2) =
      ∑' j : ℕ, fermiNormalizedDyadicSieve N c b (j + (Nat.log 2 N + 1 + 1)) ^ 2 :=
    tsum_congr fun j => by rw [show Nat.log 2 N + 1 + (j + 1) = j + (Nat.log 2 N + 1 + 1) by omega]
  simp only [Nat.add_zero] at h2
  rw [hshift] at h2
  linarith

/-- Beyond saturation the jumps sum to one third of the last free square. -/
theorem fermiRay_jump_tail (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) :
    ∑' j : ℕ, fermiNormalizedDyadicJump N c b (j + (Nat.log 2 N + 1)) ^ 2 =
      fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1) ^ 2 / 3 := by
  have h := fermiNormalizedDyadicSieve_tail_hasSum N c b 0
  simp only [Nat.add_zero] at h
  have hj (j : ℕ) : fermiNormalizedDyadicJump N c b (j + (Nat.log 2 N + 1)) ^ 2 =
      fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + j) ^ 2 / 4 := by
    rw [fermiNormalizedDyadicJump_eq_sub N c hb,
      show j + (Nat.log 2 N + 1) + 1 = Nat.log 2 N + 1 + 0 + (j + 1) by omega,
      fermiNormalizedDyadicSieve_depth_tail N c b 0 (j + 1),
      show j + (Nat.log 2 N + 1) = Nat.log 2 N + 1 + 0 + j by omega,
      fermiNormalizedDyadicSieve_depth_tail N c b 0 j]
    simp only [Nat.add_zero, pow_succ]
    field_simp
    ring
  simp_rw [hj]
  rw [tsum_div_const, h.tsum_eq]
  ring

/-! ### The Dirichlet ray inequality -/

/-- `b² w_k(b) ≥ 2^k/(2^k + 1)`. -/
theorem fermiDyadicPronicWeight_floor (k b : ℕ) (hb : 0 < b) :
    (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) ≤ (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b := by
  have h := (fermiDyadicPronicWeight_bounds k b hb).1
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left h hb2.le
  have he : (b : ℝ) ^ 2 * ((2 : ℝ) ^ k / (((2 : ℝ) ^ k + 1) * (b : ℝ) ^ 2)) =
      (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) := by
    field_simp
  linarith

/-- The weight ratio `2^k/(2^k + 1)` increases with the level. -/
theorem fermiWeightRatio_mono {k l : ℕ} (hkl : k ≤ l) :
    (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) ≤ (2 : ℝ) ^ l / ((2 : ℝ) ^ l + 1) := by
  have h : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) hkl
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The weight ratio is at least one half. -/
theorem half_le_fermiWeightRatio (k : ℕ) : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) := by
  have h : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Dirichlet ray inequality.** On every ray, for every cutoff `m ≤ D = log₂ N + 1`, the
physical sieve energy is at most `(1/λ + 1)/ρ_m` times the all-boundary energy, where
`λ = 2 - 2 cos(π/(D + m + 5))`. -/
theorem fermiRaySieveEnergy_le_allBoundary (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b)
    (m : ℕ) (hm : m ≤ Nat.log 2 N + 1) :
    fermiRaySieveEnergy N c b ≤
      (1 / (2 - 2 * Real.cos (Real.pi / (((Nat.log 2 N + 1 + m + 4 : ℕ) : ℝ) + 1))) + 1) /
        fermiRayWeightFloor m * fermiRayAllBoundaryEnergy N c b := by
  set D := Nat.log 2 N + 1 with hD
  set y : ℕ → ℝ := fun k => fermiNormalizedDyadicSieve N c b k with hy
  set lam := 2 - 2 * Real.cos (Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1)) with hlam
  have hxy (k : ℕ) : fermiNormalizedDyadicJump N c b k = y k - y (k + 1) :=
    fermiNormalizedDyadicJump_eq_sub N c hb k
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hρ := fermiRayWeightFloor_pos m
  have hρ1 := fermiRayWeightFloor_le_one m
  -- the positive Dirichlet constant
  have hlampos : 0 < lam := by
    have hx : 0 < Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1) := by positivity
    have hxπ : Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1) ≤ Real.pi := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, (Nat.cast_nonneg (D + m + 4) : (0 : ℝ) ≤ _)]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hxπ hx
    rw [Real.cos_zero] at this
    rw [hlam]; linarith
  -- the chain inequality with the bulk and ramp energy `R`
  have hchain := ray_dirichlet_robin_bound D m hm y
  set R := (1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
      (∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2) + y D ^ 2 / 3 with hR
  have hR0 : y D ^ 2 / 3 ≤ R := by
    have h1 : 0 ≤ ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    rw [hR]; nlinarith [sq_nonneg (y 0)]
  -- sieve side: `b² P ≤ Σ_{k ≤ D} y² + y_D²/3`
  obtain ⟨hPs, hQs⟩ := fermiRay_weighted_summable N c hb
  have hP : (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤
      (∑ k ∈ range (D + 1), y k ^ 2) + y D ^ 2 / 3 := by
    unfold fermiRaySieveEnergy
    rw [← tsum_mul_left]
    have hle : ∑' k : ℕ, (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b k ^ 2 *
        fermiDyadicPronicWeight k b) ≤ ∑' k : ℕ, y k ^ 2 := by
      refine Summable.tsum_le_tsum (fun k => ?_) (hPs.mul_left _) (fermiRay_sq_summable N c b)
      have hw := (fermiDyadicPronicWeight_bounds k b hb).2
      have : (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b ≤ 1 := by
        rw [← le_div_iff₀' hb2]; simpa using hw
      nlinarith [sq_nonneg (fermiNormalizedDyadicSieve N c b k)]
    have hsplit := (fermiRay_sq_summable N c b).sum_add_tsum_nat_add (D + 1)
    have htail := fermiRay_value_tail N c b
    rw [← hD] at htail
    linarith
  -- boundary side: `b² Q ≥ ρ R`
  have hQ : fermiRayWeightFloor m * R ≤ (b : ℝ) ^ 2 * fermiRayAllBoundaryEnergy N c b := by
    unfold fermiRayAllBoundaryEnergy
    set f : ℕ → ℝ := fun k => fermiNormalizedDyadicJump N c b k ^ 2 *
      fermiDyadicPronicWeight (k + 1) b with hf
    have hsplit := hQs.sum_add_tsum_nat_add D
    have hrange : (∑ k ∈ range D, f k) = (∑ k ∈ range m, f k) +
        ∑ j ∈ range (D - m), f (m + j) := by
      have h := sum_range_add f m (D - m)
      rwa [show m + (D - m) = D by omega] at h
    -- weighted lower bounds term by term
    have hbase : (1 / 2) * y 0 ^ 2 ≤
        (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) := by
      have h := (half_le_fermiWeightRatio 0).trans (fermiDyadicPronicWeight_floor 0 b hb)
      nlinarith [sq_nonneg (y 0)]
    have hlow : (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 ≤
        (b : ℝ) ^ 2 * ∑ k ∈ range m, f k := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro k _
      have h := (half_le_fermiWeightRatio (k + 1)).trans
        (fermiDyadicPronicWeight_floor (k + 1) b hb)
      rw [hf]; dsimp only
      rw [hxy k]
      nlinarith [sq_nonneg (y k - y (k + 1))]
    have hmid : fermiRayWeightFloor m * ∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2 ≤
        (b : ℝ) ^ 2 * ∑ j ∈ range (D - m), f (m + j) := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro j _
      have h := (fermiWeightRatio_mono (show m + 1 ≤ m + j + 1 by omega)).trans
        (fermiDyadicPronicWeight_floor (m + j + 1) b hb)
      rw [hf]; dsimp only
      rw [hxy (m + j)]
      unfold fermiRayWeightFloor
      nlinarith [sq_nonneg (y (m + j) - y (m + j + 1))]
    have htailQ : fermiRayWeightFloor m * (y D ^ 2 / 3) ≤
        (b : ℝ) ^ 2 * ∑' j : ℕ, f (j + D) := by
      have ht := fermiRay_jump_tail N c hb
      rw [← hD] at ht
      rw [← ht, ← tsum_mul_left, ← tsum_mul_left]
      have hsum1 : Summable (fun j => fermiRayWeightFloor m *
          fermiNormalizedDyadicJump N c b (j + D) ^ 2) :=
        (((summable_nat_add_iff D).mpr (fermiRay_jump_sq_summable N c hb))).mul_left _
      have hsum2 : Summable (fun j => (b : ℝ) ^ 2 * f (j + D)) :=
        ((summable_nat_add_iff D).mpr hQs).mul_left _
      refine Summable.tsum_le_tsum (fun j => ?_) hsum1 hsum2
      have h := (fermiWeightRatio_mono (show m + 1 ≤ j + D + 1 by omega)).trans
        (fermiDyadicPronicWeight_floor (j + D + 1) b hb)
      rw [hf]; dsimp only
      unfold fermiRayWeightFloor at *
      nlinarith [sq_nonneg (fermiNormalizedDyadicJump N c b (j + D))]
    rw [← hsplit, hrange]
    have hRexp : fermiRayWeightFloor m * R =
        fermiRayWeightFloor m * ((1 / 2) * y 0 ^ 2 +
          (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
        fermiRayWeightFloor m * ∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2 +
        fermiRayWeightFloor m * (y D ^ 2 / 3) := by
      rw [hR]; ring
    have hexp : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 *
        fermiDyadicPronicWeight 0 b + (∑ k ∈ range m, f k +
          ∑ j ∈ range (D - m), f (m + j) + ∑' i : ℕ, f (i + D))) =
        (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) +
        (b : ℝ) ^ 2 * ∑ k ∈ range m, f k + (b : ℝ) ^ 2 * ∑ j ∈ range (D - m), f (m + j) +
        (b : ℝ) ^ 2 * ∑' i : ℕ, f (i + D) := by ring
    have hhalf : fermiRayWeightFloor m * ((1 / 2) * y 0 ^ 2 +
        (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) ≤
        (1 / 2) * y 0 ^ 2 + (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := by
      have h0 : 0 ≤ (1 / 2) * y 0 ^ 2 + (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 :=
        add_nonneg (by positivity) (mul_nonneg (by norm_num) (sum_nonneg fun _ _ => sq_nonneg _))
      nlinarith
    rw [hRexp, hexp]
    linarith
  -- combine
  have hfin : (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤ (1 / lam + 1) * R := by
    have h1 : (∑ k ∈ range (D + 1), y k ^ 2) ≤ R / lam := by
      rw [le_div_iff₀ hlampos]; linarith
    have : R / lam = 1 / lam * R := by ring
    nlinarith
  have hK : 0 ≤ (1 / lam + 1) / fermiRayWeightFloor m := by positivity
  rw [← mul_le_mul_iff_of_pos_left hb2]
  calc (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤ (1 / lam + 1) * R := hfin
    _ = (1 / lam + 1) / fermiRayWeightFloor m * (fermiRayWeightFloor m * R) := by
        field_simp
    _ ≤ (1 / lam + 1) / fermiRayWeightFloor m *
        ((b : ℝ) ^ 2 * fermiRayAllBoundaryEnergy N c b) := mul_le_mul_of_nonneg_left hQ hK
    _ = _ := by ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
