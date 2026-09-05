import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleZeroLanding

/-!
# Canonical real second-level shadow at a zeta zero

For a finite chronological sequence `z`, the strict Hermitian second level satisfies

```text
normSq(∑ z) = ∑ normSq(z) + 2 Re(∑_{i<j} z_i conj(z_j)).
```

The modulus-`q + 1` deletion jumps are square summable whenever `Re s > 1/2`.  If `s` is also a
zeta zero, their endpoint tends to zero, so the real part of the chronological second level has
the forced nonzero limit `-½` times the positive quadratic energy.

This removes ambiguity from the real second-level shadow without assuming convergence of the
imaginary chronological area.  No comparison between replication and dilation is asserted.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace RHTower

/-- Strict chronological Hermitian second level of the first `N` jumps. -/
def chronologicalSecondPrefix (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (∑ i ∈ Finset.range j, z i) * star (z j)

/-- Diagonal quadratic energy of the first `N` jumps. -/
def quadraticEnergyPrefix (z : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, Complex.normSq (z j)

/-- Finite Hermitian quasi-shuffle identity for chronologically indexed jumps. -/
theorem endpoint_normSq_eq_energy_add_secondPrefix (z : ℕ → ℂ) (N : ℕ) :
    Complex.normSq (∑ i ∈ Finset.range N, z i) =
      quadraticEnergyPrefix z N + 2 * (chronologicalSecondPrefix z N).re := by
  induction N with
  | zero => simp [quadraticEnergyPrefix, chronologicalSecondPrefix]
  | succ N ih =>
      rw [Finset.sum_range_succ, Complex.normSq_add, ih]
      simp only [quadraticEnergyPrefix, chronologicalSecondPrefix, Finset.sum_range_succ,
        Complex.add_re, Complex.mul_re, starRingEnd_apply]
      ring

/-- Weighted jump in the conditional modulus-`q + 1` Euler-deletion path. -/
def eulerDeletionWeightedJump (q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  eulerDeletionDirichletCoefficient q n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

/-- Every modulus-`q + 1` deletion coefficient has norm at most `q`. -/
theorem norm_eulerDeletionDirichletCoefficient_le
    {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ‖eulerDeletionDirichletCoefficient q n‖ ≤ q := by
  rw [eulerDeletionDirichletCoefficient, blockDeletionCoefficient]
  by_cases hd : q + 1 ∣ n + 1
  · simp [hd]
  · simp [hd]
    exact_mod_cast hq

/-- Deletion-jump energy is bounded by a shifted `2 Re s` power tail. -/
theorem normSq_eulerDeletionWeightedJump_le
    {q : ℕ} (hq : 0 < q) (s : ℂ) (n : ℕ) :
    Complex.normSq (eulerDeletionWeightedJump q s n) ≤
      (q : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-2 * s.re) := by
  rw [Complex.normSq_eq_norm_sq, eulerDeletionWeightedJump, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  have hc := norm_eulerDeletionDirichletCoefficient_le hq n
  have hr : 0 ≤ ((n : ℝ) + 1) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  have hsq : (((n : ℝ) + 1) ^ (-s.re)) ^ 2 =
      ((n : ℝ) + 1) ^ (-2 * s.re) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), pow_two,
      ← Real.exp_add]
    congr 1
    ring
  have hmul : ‖eulerDeletionDirichletCoefficient q n‖ * ((n : ℝ) + 1) ^ (-s.re) ≤
      (q : ℝ) * ((n : ℝ) + 1) ^ (-s.re) :=
    mul_le_mul_of_nonneg_right hc hr
  rw [← hsq]
  calc
    (‖eulerDeletionDirichletCoefficient q n‖ * ((n : ℝ) + 1) ^ (-s.re)) ^ 2 ≤
        ((q : ℝ) * ((n : ℝ) + 1) ^ (-s.re)) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hr) (by positivity)).2 hmul
    _ = (q : ℝ) ^ 2 * (((n : ℝ) + 1) ^ (-s.re)) ^ 2 := by ring

/-- Weighted deletion jumps have summable diagonal energy right of the half-line. -/
theorem summable_quadraticEnergy_eulerDeletionWeightedJump
    {q : ℕ} (hq : 0 < q) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun n => Complex.normSq (eulerDeletionWeightedJump q s n)) := by
  have hbase0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * s.re)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) 1).2 hbase0
  apply Summable.of_nonneg_of_le
    (fun n => Complex.normSq_nonneg _)
    (fun n => normSq_eulerDeletionWeightedJump_le hq s n)
  exact hbase.mul_left ((q : ℝ) ^ 2)

/-- Total diagonal energy of the weighted deletion path. -/
noncomputable def eulerDeletionQuadraticEnergy (q : ℕ) (s : ℂ) : ℝ :=
  ∑' n, Complex.normSq (eulerDeletionWeightedJump q s n)

/-- Nontrivial deletion paths have strictly positive total energy right of the half-line. -/
theorem eulerDeletionQuadraticEnergy_pos
    {q : ℕ} (hq : 0 < q) {s : ℂ} (hs : 1 / 2 < s.re) :
    0 < eulerDeletionQuadraticEnergy q s := by
  have hsum := summable_quadraticEnergy_eulerDeletionWeightedJump hq hs
  apply hsum.tsum_pos (fun n => Complex.normSq_nonneg _) 0
  have hndvd : ¬q + 1 ∣ 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  norm_num [eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient,
    blockDeletionCoefficient, hndvd]

/-- Finite diagonal energies converge to the total energy. -/
theorem tendsto_quadraticEnergyPrefix_eulerDeletion
    {q : ℕ} (hq : 0 < q) {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun N => quadraticEnergyPrefix (eulerDeletionWeightedJump q s) N)
      atTop (nhds (eulerDeletionQuadraticEnergy q s)) := by
  have hsum := summable_quadraticEnergy_eulerDeletionWeightedJump hq hs
  simpa [quadraticEnergyPrefix, eulerDeletionQuadraticEnergy] using
    hsum.hasSum.tendsto_sum_nat

/-- At a positive-half-plane zeta zero, every weighted deletion prefix tends to zero. -/
theorem tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    (q : ℕ) {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n)
      atTop (nhds 0) := by
  have hconv := eulerDeletionDirichlet_convergesAt (q := q) (s := rho) hrhoRe
  have ht := GaloisForLFunctions.RHTower.tendsto_dirichletSum hconv
  have hzero :=
    eulerDeletionDirichletSum_eq_zero_of_riemannZeta_eq_zero q hrhoRe hrho1 hzeta
  change GaloisForLFunctions.RHTower.dirichletSum
    (eulerDeletionDirichletCoefficient q) rho = 0 at hzero
  rw [hzero] at ht
  simpa [GaloisForLFunctions.RHTower.dirichletPartialSum,
    eulerDeletionWeightedJump, eulerDeletionDirichletSum] using ht

/--
At a zeta zero right of the half-line, the real chronological second level converges to the
strictly negative value `-½` times the deletion energy.
-/
theorem tendsto_re_chronologicalSecondPrefix_eulerDeletion_of_zeta_zero
    {q : ℕ} (hq : 0 < q) {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Tendsto
      (fun N => (chronologicalSecondPrefix (eulerDeletionWeightedJump q rho) N).re)
      atTop (nhds (-eulerDeletionQuadraticEnergy q rho / 2)) := by
  have hrhoRe : 0 < rho.re := by linarith
  have hend := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    q hrhoRe hrho1 hzeta
  have hnorm : Tendsto
      (fun N => Complex.normSq
        (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n))
      atTop (nhds 0) := by
    convert Complex.continuous_normSq.continuousAt.tendsto.comp hend using 1 <;>
      simp [Function.comp_def]
  have henergy := tendsto_quadraticEnergyPrefix_eulerDeletion hq hrhoHalf
  have hcombined := (hnorm.sub henergy).div_const 2
  have hformula : ∀ N,
      (chronologicalSecondPrefix (eulerDeletionWeightedJump q rho) N).re =
        (Complex.normSq
          (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n) -
            quadraticEnergyPrefix (eulerDeletionWeightedJump q rho) N) / 2 := by
    intro N
    have hid := endpoint_normSq_eq_energy_add_secondPrefix
      (eulerDeletionWeightedJump q rho) N
    linarith
  convert hcombined using 1
  · ext N
    rw [hformula]
  · ring_nf

end RHTower
