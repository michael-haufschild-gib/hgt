import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasRamanujanQuasimodes

/-!
# The complete Weil form on finite Ramanujan packets

The normalized Ramanujan Gram tends to the identity. Pairing the actual Weil
norm residual with another normalized mode gives the mixed energy limit.
Finite sums therefore diagonalize the limiting form on every fixed packet,
including its conductor-one pole shift.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The literal pole-gauge profile of a finite Ramanujan packet. -/
def ramanujanPacketProfile (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ S, b m * ramanujanPoleProfile m n

/-- A finite Ramanujan packet with common logarithmic mass normalization. -/
def normalizedRamanujanPacketVector (S : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ S, b m • normalizedRamanujanHorizonVector m N

/-- Each normalized mode has norm tending to one. -/
theorem tendsto_normalizedRamanujanHorizonVector_norm {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
    (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt

/-- Vanishing norm errors pair to zero against a norm-convergent horizon family. -/
theorem tendsto_horizon_inner_zero_of_norm
    (r v : ∀ N : ℕ, EuclideanSpace ℝ (PrimeHorizonIndex N)) {L : ℝ}
    (hr : Tendsto (fun N => ‖r N‖) atTop (𝓝 0))
    (hv : Tendsto (fun N => ‖v N‖) atTop (𝓝 L)) :
    Tendsto (fun N => ⟪r N, v N⟫) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => norm_inner_le_norm (r N) (v N))
  simpa only [zero_mul] using hr.mul hv

/-- Every mixed complete-Weil entry tends to its diagonal arithmetic energy. -/
theorem tendsto_completeWeilMatrix_ramanujan_inner {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N),
        normalizedRamanujanHorizonVector l N⟫)
      atTop (𝓝 (if m = l then completeWeilAdjunctionEnergy φ c m else 0)) := by
  have herr := tendsto_horizon_inner_zero_of_norm
    (fun N => Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N)
    (fun N => normalizedRamanujanHorizonVector l N)
    (tendsto_completeWeilMatrix_ramanujan_residual_norm hφ hsupp hM hc0 hc1 hm)
    (tendsto_normalizedRamanujanHorizonVector_norm hl)
  have hmain := (tendsto_normalizedRamanujanHorizonVector_gram hm hl).const_mul
    (completeWeilAdjunctionEnergy φ c m)
  simpa only [inner_sub_left, real_inner_smul_left, sub_add_cancel, zero_add,
    mul_ite, mul_one, mul_zero] using herr.add hmain

private theorem packet_diagonal_sum (S : Finset ℕ) (b d e : ℕ → ℝ) :
    (∑ m ∈ S, ∑ l ∈ S, b m * (d l * if m = l then e m else 0)) =
      ∑ m ∈ S, b m * d m * e m := by
  classical
  apply sum_congr rfl
  intro m hm
  rw [sum_eq_single m]
  · rw [if_pos rfl]
    ring
  · intro l _ hl
    rw [if_neg (Ne.symm hl), mul_zero, mul_zero]
  · exact fun h => False.elim (h hm)

/-- The limiting Gram form of a fixed packet is the Euclidean coefficient form. -/
theorem tendsto_normalizedRamanujanPacketVector_inner
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b d : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ⟪normalizedRamanujanPacketVector S b N, normalizedRamanujanPacketVector S d N⟫)
      atTop (𝓝 (∑ m ∈ S, b m * d m)) := by
  have h := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    ((tendsto_normalizedRamanujanHorizonVector_gram (hS m hm) (hS l hl)).const_mul (d l)).const_mul (b m)
  rw [packet_diagonal_sum S b d (fun _ => 1)] at h
  simp only [mul_one] at h
  refine h.congr fun N => ?_
  simp only [normalizedRamanujanPacketVector, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro m _
  ring

/-- The normalized packet mass tends to the sum of squared coefficients. -/
theorem tendsto_normalizedRamanujanPacketVector_norm_sq
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ‖normalizedRamanujanPacketVector S b N‖ ^ 2)
      atTop (𝓝 (∑ m ∈ S, b m ^ 2)) := by
  simpa only [real_inner_self_eq_norm_sq, pow_two] using
    tendsto_normalizedRamanujanPacketVector_inner S hS b b

/-- The full Weil mixed form is asymptotically diagonal on every finite packet. -/
theorem tendsto_completeWeilMatrix_packet_inner {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b d : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanPacketVector S b N),
        normalizedRamanujanPacketVector S d N⟫)
      atTop (𝓝 (∑ m ∈ S, b m * d m * completeWeilAdjunctionEnergy φ c m)) := by
  have h := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    ((tendsto_completeWeilMatrix_ramanujan_inner hφ hsupp hM hc0 hc1
      (hS m hm) (hS l hl)).const_mul (d l)).const_mul (b m)
  rw [packet_diagonal_sum] at h
  refine h.congr fun N => ?_
  simp only [normalizedRamanujanPacketVector, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro m _
  ring

/-- Restricting the literal packet profile gives the finite vector sum. -/
theorem horizonProfileVector_ramanujanPacketProfile
    (S : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) :
    horizonProfileVector (ramanujanPacketProfile S b) N =
      ∑ m ∈ S, b m • ramanujanHorizonVector m N := by
  ext n
  have hsum : (∑ m ∈ S, b m • ramanujanHorizonVector m N) n =
      ∑ m ∈ S, b m * ramanujanPoleProfile m n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
      (∑ m ∈ S, b m • ramanujanHorizonVector m N) = _
    rw [map_sum]
    exact sum_congr rfl fun m _ => rfl
  exact hsum.symm

/-- Packet normalization is the common inverse square root of logarithmic mass. -/
theorem normalizedRamanujanPacketVector_eq_smul_profile
    (S : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) :
    normalizedRamanujanPacketVector S b N =
      (Real.sqrt (Real.log N))⁻¹ • horizonProfileVector (ramanujanPacketProfile S b) N := by
  rw [horizonProfileVector_ramanujanPacketProfile, smul_sum]
  exact sum_congr rfl fun m _ => smul_comm (b m) (Real.sqrt (Real.log N))⁻¹ _

/-- The normalized packet norm is its literal squared mass divided by the logarithm. -/
theorem normalizedRamanujanPacketVector_norm_sq_eq
    (S : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) :
    ‖normalizedRamanujanPacketVector S b N‖ ^ 2 =
      (∑ n ∈ Icc 1 N, ramanujanPacketProfile S b n ^ 2) / Real.log N := by
  rw [normalizedRamanujanPacketVector_eq_smul_profile, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N),
    horizonProfileVector_norm_sq]
  ring

/-- Every matrix form scales by the same logarithmic packet mass. -/
theorem normalizedRamanujanPacketVector_matrix_inner
    (S : Finset ℕ) (b d : ℕ → ℝ) (N : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    ⟪Matrix.toEuclideanLin A (normalizedRamanujanPacketVector S b N),
      normalizedRamanujanPacketVector S d N⟫ =
      ⟪Matrix.toEuclideanLin A (horizonProfileVector (ramanujanPacketProfile S b) N),
        horizonProfileVector (ramanujanPacketProfile S d) N⟫ / Real.log N := by
  rw [normalizedRamanujanPacketVector_eq_smul_profile,
    normalizedRamanujanPacketVector_eq_smul_profile, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  have hs : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← mul_assoc, hs]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
