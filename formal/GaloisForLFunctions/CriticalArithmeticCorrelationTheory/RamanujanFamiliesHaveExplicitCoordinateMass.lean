import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingRamanujanFamiliesHaveASquareRootHorizon
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# Ramanujan coordinate mass at an explicit horizon

The harmonic lower frame for conductors through `Q` gives half the coefficient
mass once `Q⁴≤N`. A unit vector approximated to squared error `1/4` then has
squared Ramanujan coordinate mass at least `1/18` at that same horizon.
-/

noncomputable section
open Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory

private theorem ramanujanCombination_norm_sq (Q N : ℕ) (a : ℕ → ℝ) :
    ‖∑ m ∈ Icc 1 Q, a m • ramanujanHorizonVector m N‖ ^ 2 =
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, ← sum_coe_sort (Icc 1 N)]
  apply sum_congr rfl
  intro n _
  congr 1
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
    (∑ m ∈ Icc 1 Q, a m • ramanujanHorizonVector m N) = _
  rw [map_sum]
  exact sum_congr rfl fun m _ => rfl

/-- The normalized conductor family has lower frame constant `1/2` at `N≥Q⁴`. -/
theorem half_sum_sq_le_normalizedRamanujan_synthesis_sq
    {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q ^ 4 ≤ N) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, a m ^ 2) / 2 ≤
      ‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hN : 2 ≤ N := hQ.trans ((Nat.le_self_pow (by norm_num : 4 ≠ 0) Q).trans hQN)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hpow : (Q : ℝ) ^ 4 ≤ N := by exact_mod_cast hQN
  have hlog := Real.log_le_log (pow_pos hQpos 4) hpow
  rw [Real.log_pow] at hlog
  have hsucc := Real.log_le_log hNpos (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith only)
  have hfactor : Real.log (N : ℝ) / 2 ≤
      Real.log ((N : ℝ) + 1) - 2 * Real.log Q := by
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog, hsucc]
  have hraw := (mul_le_mul_of_nonneg_right hfactor
    (sum_nonneg fun m _ => sq_nonneg (a m))).trans
      (ramanujanPoleProfile_family_squareRoot_lower hQ a N)
  rw [← ramanujanCombination_norm_sq] at hraw
  have heq : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) =
      (Real.sqrt (Real.log N))⁻¹ • (∑ m ∈ Icc 1 Q, a m • ramanujanHorizonVector m N) := by
    rw [Finset.smul_sum]
    apply sum_congr rfl
    intro m _
    rw [normalizedRamanujanHorizonVector, smul_comm]
  rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hL.le]
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hL).mpr
  nlinarith only [hraw]

/-- A nearby unit vector has definite coordinate mass at the explicit frame horizon. -/
theorem normalizedRamanujan_coordinate_mass_ge_of_explicit_approximation
    {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q ^ 4 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hx : ‖x‖ = 1) (a : ℕ → ℝ)
    (happrox : ‖x - ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 1 / 4) :
    1 / 18 ≤ ∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  let z := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  have hdist : ‖x - z‖ ≤ 1 / 2 := by
    change ‖x - z‖ ^ 2 ≤ 1 / 4 at happrox
    nlinarith only [happrox, norm_nonneg (x - z)]
  have hznorm : ‖z‖ ≤ 3 / 2 := by
    have ht := norm_add_le (z - x) x
    rw [sub_add_cancel, norm_sub_rev, hx] at ht
    linarith only [ht, hdist]
  have hac : (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 9 / 2 := by
    have h := half_sum_sq_le_normalizedRamanujan_synthesis_sq hQ hQN a
    change (∑ m ∈ Icc 1 Q, a m ^ 2) / 2 ≤ ‖z‖ ^ 2 at h
    nlinarith only [h, hznorm, norm_nonneg z]
  have hic : |⟪x, x - z⟫| ≤ ‖x‖ * ‖x - z‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x (x - z)
  have hinner : 1 / 2 ≤ ⟪x, z⟫ := by
    rw [hx, one_mul, inner_sub_right, real_inner_self_eq_norm_sq, hx] at hic
    have h := (le_abs_self (1 ^ 2 - ⟪x, z⟫)).trans hic
    nlinarith only [h, hdist]
  have hcs : ⟪x, z⟫ ^ 2 ≤ (∑ m ∈ Icc 1 Q, a m ^ 2) *
      ∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
    have heq : ⟪x, z⟫ = ∑ m ∈ Icc 1 Q, a m * ⟪x, normalizedRamanujanHorizonVector m N⟫ := by
      simp only [z, inner_sum, real_inner_smul_right]
    rw [heq]
    exact sum_mul_sq_le_sq_mul_sq (Icc 1 Q) a
      (fun m => ⟪x, normalizedRamanujanHorizonVector m N⟫)
  have hupper := mul_le_mul_of_nonneg_right hac
    (sum_nonneg (s := Icc 1 Q) fun m _ => sq_nonneg ⟪x, normalizedRamanujanHorizonVector m N⟫)
  nlinarith only [hinner, hcs, hupper]

/-- Raw finite-profile approximation gives the same coordinate certificate after
zero extension and the exact square-root logarithmic normalization. -/
theorem normalizedRamanujan_coordinate_mass_ge_of_raw_approximation
    {R Q N : ℕ} (hRQ : R ≤ Q) (hQ : 2 ≤ Q) (hQN : Q ^ 4 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hx : ‖x‖ = 1) (a : ℕ → ℝ)
    (happrox : (∑ n ∈ Icc 1 N,
      (primeHorizonExtension x n - ∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4) :
    1 / 18 ≤ ∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  have hN : 2 ≤ N := hQ.trans ((Nat.le_self_pow (by norm_num : 4 ≠ 0) Q).trans hQN)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  let b : ℕ → ℝ := fun m => if m ≤ R then a m * Real.sqrt (Real.log N) else 0
  have hcoeff (m : ℕ) (hm : m ∈ Icc 1 R) :
      b m • normalizedRamanujanHorizonVector m N = a m • ramanujanHorizonVector m N := by
    dsimp only [b]
    rw [if_pos (mem_Icc.mp hm).2, normalizedRamanujanHorizonVector, smul_smul]
    congr 1
    field_simp
  have heq : (∑ m ∈ Icc 1 R, a m • ramanujanHorizonVector m N) =
      ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N := by
    calc
      _ = ∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => (hcoeff m hm).symm
      _ = _ := sum_subset (Icc_subset_Icc le_rfl hRQ) fun m hmQ hmR => by
        have hm : ¬m ≤ R := fun h => hmR (mem_Icc.mpr ⟨(mem_Icc.mp hmQ).1, h⟩)
        simp only [b, if_neg hm, zero_smul]
  apply normalizedRamanujan_coordinate_mass_ge_of_explicit_approximation hQ hQN x hx b
  rw [← heq, EuclideanSpace.real_norm_sq_eq]
  rw [← sum_coe_sort (Icc 1 N) (fun n =>
    (primeHorizonExtension x n - ∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2)] at happrox
  convert happrox using 1
  apply sum_congr rfl
  intro n _
  have hsum : (∑ m ∈ Icc 1 R, a m • ramanujanHorizonVector m N) n =
      ∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
      (∑ m ∈ Icc 1 R, a m • ramanujanHorizonVector m N) = _
    rw [map_sum]
    exact sum_congr rfl fun m _ => rfl
  simp only [PiLp.sub_apply, hsum, primeHorizonExtension_coe]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.half_sum_sq_le_normalizedRamanujan_synthesis_sq
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.normalizedRamanujan_coordinate_mass_ge_of_explicit_approximation
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.normalizedRamanujan_coordinate_mass_ge_of_raw_approximation
