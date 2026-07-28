/-
# Infinite phase-ladder moment transfer

The phase-lattice lift preserves every finite block of spectral moments.  More precisely, each
lifted moment is a triangular combination of original moments of no higher degree, with universal
coefficients supplied by the common ladder.  Hence two finite spectral laws agreeing through
degree `D` lift to genuine infinite spectral laws still agreeing through degree `D`.

This closes the local-data seam in the infinite extension: target-return factorization is not the
only invariant.  Every finite Krylov/moment record used to identify a local Hamiltonian prefix
survives unchanged.
-/
import GaloisForLFunctions.RHTower.InfinitePhaseLadderLocalHorizonLaw

open scoped BigOperators

noncomputable section

namespace RHTower.ParityForecast

theorem phaseLadderSpacingMoment_summable
    (T : ℝ) (d : ℕ) :
    Summable (fun k : ℕ =>
      phaseLadderWeight k *
        (2 * Real.pi * (k : ℝ) / T) ^ d) := by
  have hbase :
      Summable (fun k : ℕ =>
        (k : ℝ) ^ d * ((1 : ℝ) / 2) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one d (by norm_num)
  have hscaled := hbase.mul_left
    ((((1 : ℝ) / 2) * (2 * Real.pi / T) ^ d))
  apply hscaled.congr
  intro k
  unfold phaseLadderWeight
  rw [pow_succ]
  ring

theorem phaseLadderFiberMoment_summable
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (d : ℕ) (j : Fin (m + 1)) :
    Summable (fun k : ℕ =>
      weight j * phaseLadderWeight k *
        phaseLadderEnergy T energy (j, k) ^ d) := by
  rw [show (fun k : ℕ =>
      weight j * phaseLadderWeight k *
        phaseLadderEnergy T energy (j, k) ^ d) =
      fun k => ∑ a ∈ Finset.range (d + 1),
        (weight j * energy j ^ a * d.choose a) *
          (phaseLadderWeight k *
            (2 * Real.pi * (k : ℝ) / T) ^ (d - a)) by
    funext k
    unfold phaseLadderEnergy
    rw [add_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring]
  apply summable_sum
  intro a _ha
  exact (phaseLadderSpacingMoment_summable T (d - a)).mul_left
    (weight j * energy j ^ a * d.choose a)

theorem phaseLadderMoment_summable
    {m : ℕ} {T : ℝ} (hT : 0 < T)
    (energy weight : Fin (m + 1) → ℝ)
    (henergy : ∀ j, 0 ≤ energy j)
    (hweight : ∀ j, 0 ≤ weight j) (d : ℕ) :
    Summable (fun x : Fin (m + 1) × ℕ =>
      weight x.1 * phaseLadderWeight x.2 *
        phaseLadderEnergy T energy x ^ d) := by
  rw [summable_prod_of_nonneg (fun x => by
    apply mul_nonneg
    · exact mul_nonneg (hweight x.1)
        (phaseLadderWeight_nonneg x.2)
    · exact pow_nonneg (by
        unfold phaseLadderEnergy
        exact add_nonneg (henergy x.1)
          (div_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) Real.pi_pos.le)
              (Nat.cast_nonneg x.2))
            hT.le)) _)]
  · constructor
    · exact phaseLadderFiberMoment_summable T energy weight d
    · exact (hasSum_fintype _).summable

/-- The common `d`-th moment of the added phase lattice. -/
def phaseLadderSpacingMoment (T : ℝ) (d : ℕ) : ℝ :=
  ∑' k : ℕ, phaseLadderWeight k *
    (2 * Real.pi * (k : ℝ) / T) ^ d

theorem phaseLadderFiberMoment_eq
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (d : ℕ) (j : Fin (m + 1)) :
    (∑' k : ℕ, weight j * phaseLadderWeight k *
        phaseLadderEnergy T energy (j, k) ^ d) =
      ∑ a ∈ Finset.range (d + 1),
        weight j * energy j ^ a * d.choose a *
          phaseLadderSpacingMoment T (d - a) := by
  rw [show (fun k : ℕ =>
      weight j * phaseLadderWeight k *
        phaseLadderEnergy T energy (j, k) ^ d) =
      fun k => ∑ a ∈ Finset.range (d + 1),
        (weight j * energy j ^ a * d.choose a) *
          (phaseLadderWeight k *
            (2 * Real.pi * (k : ℝ) / T) ^ (d - a)) by
    funext k
    unfold phaseLadderEnergy
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring]
  rw [Summable.tsum_finsetSum (fun a _ha =>
    (phaseLadderSpacingMoment_summable T (d - a)).mul_left
      (weight j * energy j ^ a * d.choose a))]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold phaseLadderSpacingMoment
  rw [tsum_mul_left]

/-- Every lifted moment is a triangular combination of the original finite moments. -/
theorem phaseLadderMoment_decomposition
    {m : ℕ} {T : ℝ} (hT : 0 < T)
    (energy weight : Fin (m + 1) → ℝ)
    (henergy : ∀ j, 0 ≤ energy j)
    (hweight : ∀ j, 0 ≤ weight j) (d : ℕ) :
    (∑' x : Fin (m + 1) × ℕ,
        weight x.1 * phaseLadderWeight x.2 *
          phaseLadderEnergy T energy x ^ d) =
      ∑ a ∈ Finset.range (d + 1),
        (∑ j : Fin (m + 1), weight j * energy j ^ a) *
          d.choose a * phaseLadderSpacingMoment T (d - a) := by
  have hs := phaseLadderMoment_summable hT energy weight
    henergy hweight d
  rw [hs.tsum_prod, tsum_fintype]
  simp_rw [phaseLadderFiberMoment_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_mul, Finset.sum_mul]

/--
Moment equality survives the infinite lift.  Agreement of all finite moments through degree `D`
therefore gives agreement of every lifted moment through the same degree.
-/
theorem phaseLadderMoment_eq_of_base_moments_eq
    {m : ℕ} {T : ℝ} (hT : 0 < T)
    (energy : Fin (m + 1) → ℝ)
    (weight₁ weight₂ : Fin (m + 1) → ℝ)
    (henergy : ∀ j, 0 ≤ energy j)
    (hweight₁ : ∀ j, 0 ≤ weight₁ j)
    (hweight₂ : ∀ j, 0 ≤ weight₂ j)
    {D : ℕ}
    (hmoment : ∀ a ≤ D,
      (∑ j : Fin (m + 1), weight₁ j * energy j ^ a) =
        ∑ j : Fin (m + 1), weight₂ j * energy j ^ a) :
    ∀ d ≤ D,
      (∑' x : Fin (m + 1) × ℕ,
          weight₁ x.1 * phaseLadderWeight x.2 *
            phaseLadderEnergy T energy x ^ d) =
        ∑' x : Fin (m + 1) × ℕ,
          weight₂ x.1 * phaseLadderWeight x.2 *
            phaseLadderEnergy T energy x ^ d := by
  intro d hd
  rw [phaseLadderMoment_decomposition hT energy weight₁
      henergy hweight₁ d,
    phaseLadderMoment_decomposition hT energy weight₂
      henergy hweight₂ d]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hmoment a (by
    have := Finset.mem_range.mp ha
    omega)]

/--
Every pair of interpolated clocks has exactly the same lifted moments through any prescribed
degree strictly below the finite clock order.  This is the concrete moment seam used by the
universal local-horizon family.
-/
theorem infiniteAngularInterpolated_moments_eq
    {T : ℝ} (hT : 0 < T) {n D : ℕ} (hD : D < n)
    {θ φ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ d ≤ D,
      (∑' x : Fin (n + 1) × ℕ,
          interpolatedWeight n θ x.1 *
            phaseLadderWeight x.2 *
              phaseLadderEnergy T (angularEnergy T n) x ^ d) =
        ∑' x : Fin (n + 1) × ℕ,
          interpolatedWeight n φ x.1 *
            phaseLadderWeight x.2 *
              phaseLadderEnergy T (angularEnergy T n) x ^ d := by
  apply phaseLadderMoment_eq_of_base_moments_eq
    hT (angularEnergy T n)
    (interpolatedWeight n θ)
    (interpolatedWeight n φ)
    (angularEnergy_nonneg hT n)
    (interpolatedWeight_nonneg n hθ0 hθ1)
    (interpolatedWeight_nonneg n hφ0 hφ1)
  intro a ha
  calc
    (∑ j : Fin (n + 1),
        interpolatedWeight n θ j *
          angularEnergy T n j ^ a) =
      ∑ j : Fin (n + 1),
        fullWeight n j * angularEnergy T n j ^ a :=
      angular_interpolated_energyMoment_eq_full
        (lt_of_le_of_lt ha hD) θ
    _ = ∑ j : Fin (n + 1),
        interpolatedWeight n φ j *
          angularEnergy T n j ^ a :=
      (angular_interpolated_energyMoment_eq_full
        (lt_of_le_of_lt ha hD) φ).symm

/-- The last finite coordinate always has strictly positive interpolated weight, including at the
rank-dropped parity endpoint. -/
theorem interpolatedWeight_last_pos
    (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    0 < interpolatedWeight n θ (Fin.last n) := by
  rw [interpolatedWeight, parityWeight]
  have hlast : n - ((Fin.last n : Fin (n + 1)) : ℕ) = 0 := by
    simp
  rw [hlast]
  norm_num
  have hfull := fullWeight_pos n (Fin.last n)
  nlinarith

/-- Every infinite interpolated clock has an actually populated ladder of pairwise distinct energy
levels, not merely zero-weight spectator dimensions. -/
theorem infiniteInterpolated_populated_ladder
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) :
    (∀ k : ℕ,
      0 < interpolatedWeight n θ (Fin.last n) *
        phaseLadderWeight k) ∧
    Function.Injective
      (fun k : ℕ =>
        phaseLadderEnergy T (angularEnergy T n)
          (Fin.last n, k)) := by
  constructor
  · intro k
    exact mul_pos (interpolatedWeight_last_pos n hθ0)
      (phaseLadderWeight_pos k)
  · exact phaseLadderEnergy_injective_nat hT
      (angularEnergy T n) (Fin.last n)

end RHTower.ParityForecast
