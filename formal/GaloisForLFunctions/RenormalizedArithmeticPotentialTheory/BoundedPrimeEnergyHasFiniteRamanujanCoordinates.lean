import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRenormalizedPrimeEnergyControlsTheDefect
import GaloisForLFunctions.HTGeometry.FiniteGramApproximationCertificate

/-!
# Bounded prime energy is detected by finitely many Ramanujan coordinates

The logarithmically normalized profiles have identity Gram limit. Uniform
finite-span approximation therefore gives a positive coordinate mass for every
unit vector in a fixed renormalized energy sublevel.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Normalize the actual Ramanujan vector by the common logarithmic mass scale. -/
def normalizedRamanujanHorizonVector (m N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • ramanujanHorizonVector m N

theorem ramanujanHorizonVector_inner (m l N : ℕ) :
    ⟪ramanujanHorizonVector m N, ramanujanHorizonVector l N⟫ =
      ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N,
    ramanujanPoleProfile l n * ramanujanPoleProfile m n) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile l n * ramanujanPoleProfile m n)]
  exact sum_congr rfl fun n _ => mul_comm _ _

theorem normalizedRamanujanHorizonVector_inner (m l N : ℕ) :
    ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ =
      (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) / Real.log N := by
  rw [normalizedRamanujanHorizonVector, normalizedRamanujanHorizonVector,
    real_inner_smul_left, real_inner_smul_right, ramanujanHorizonVector_inner]
  have hs : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← mul_assoc, hs]
  ring

theorem tendsto_normalizedRamanujanHorizonVector_gram {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫)
      atTop (𝓝 (if m = l then 1 else 0)) := by
  simpa only [normalizedRamanujanHorizonVector_inner] using tendsto_ramanujanPoleProfile_gram hm hl

theorem tendsto_normalizedRamanujanHorizonVector_norm_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖ ^ 2) atTop (𝓝 1) := by
  have h := tendsto_normalizedRamanujanHorizonVector_gram hm hm
  rw [if_pos rfl] at h
  simpa only [real_inner_self_eq_norm_sq] using h

/-- The normalized actual residual tends to zero in Euclidean norm. -/
theorem tendsto_normalizedRamanujanHorizonVector_residual_norm {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖)
      atTop (𝓝 0) := by
  have heq (N : ℕ) :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 /
          Real.log N := by
    simp only [normalizedRamanujanHorizonVector, map_smul]
    rw [smul_comm (Real.log N - ramanujanAdjunctionEnergy m) (Real.sqrt (Real.log N))⁻¹,
      ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N)]
    ring
  have hsq := tendsto_ramanujanHorizonVector_residual_norm_sq hm
  have hsq' : Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 0) := by simpa only [heq] using hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsq'.sqrt

/-- Every fixed finite packet has a uniform synthesis lower bound eventually. -/
theorem eventually_normalizedRamanujanHorizonVector_gram_close
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ m l : S,
      |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        if m = l then 1 else 0| ≤ 1 / (2 * ((Fintype.card S : ℝ) + 1)) := by
  have hδ : (0 : ℝ) < 1 / (2 * ((Fintype.card S : ℝ) + 1)) := by positivity
  apply Filter.eventually_all.mpr
  intro m
  apply Filter.eventually_all.mpr
  intro l
  have h := ((tendsto_normalizedRamanujanHorizonVector_gram
    (hS m m.property) (hS l l.property)).sub_const (if (m : ℕ) = (l : ℕ) then 1 else 0)).abs
  have hz : Tendsto (fun N : ℕ =>
      |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        if m = l then 1 else 0|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, Subtype.ext_iff] using h
  filter_upwards [hz.eventually (gt_mem_nhds hδ)] with N hN
  exact hN.le

/-- Actual bounded-energy unit vectors have uniformly positive mass in a fixed
finite list of Ramanujan coordinates. No limiting operator is assumed. -/
theorem exists_finite_ramanujan_coordinate_certificate (T : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → renormalizedPrimeEnergy N x ≤ T →
          1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_renormalizedPrimeEnergy_le T
    (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨S, hS, ?_⟩
  filter_upwards [happ, eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2] with N haN hgram hN x hx henergy
  obtain ⟨a, ha⟩ := haN x hx henergy
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  let b : S → ℝ := fun m => a m * Real.sqrt (Real.log N)
  have heq : (∑ m : S, b m • normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ S, a m • ramanujanHorizonVector m N := by
    rw [← sum_coe_sort S (fun m => a m • ramanujanHorizonVector m N)]
    refine sum_congr rfl fun m _ => ?_
    rw [normalizedRamanujanHorizonVector, smul_smul]
    congr 1
    dsimp only [b]
    field_simp
  have hcert := HTGeometry.coordinate_mass_ge_of_finite_approximation
    (fun m : S => normalizedRamanujanHorizonVector m N) hgram x hx b
    (by rw [heq]; exact ha)
  simpa only [sum_coe_sort S (fun m => ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2)] using hcert

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
