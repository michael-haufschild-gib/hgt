import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiMixedBoundaryRayStability
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Exact pronic decomposition into dyadic rays

The positive integer index is reindexed by its unique power of two and odd part.
Both physical energies retain their actual pronic weights. The selected trace
has the next-level weight, and its normalized difference starts on level one.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem two_pow_odd_unique (a c b d : ℕ)
    (h : 2 ^ a * (2 * b + 1) = 2 ^ c * (2 * d + 1)) : a = c ∧ b = d := by
  induction a generalizing c with
  | zero =>
      cases c with
      | zero =>
          simp only [pow_zero, one_mul] at h
          exact ⟨rfl, by omega⟩
      | succ c =>
          simp only [pow_zero, one_mul, pow_succ', Nat.mul_assoc] at h
          omega
  | succ a ih =>
      cases c with
      | zero =>
          simp only [pow_zero, one_mul, pow_succ', Nat.mul_assoc] at h
          omega
      | succ c =>
          have hc : 2 ^ a * (2 * b + 1) = 2 ^ c * (2 * d + 1) := by
            simp only [pow_succ', Nat.mul_assoc] at h
            omega
          obtain ⟨hac, hbd⟩ := ih c hc
          exact ⟨by omega, hbd⟩

private def oddRayIndex (p : ℕ × ℕ) : ℕ := 2 ^ p.1 * (2 * p.2 + 1) - 1

private theorem oddRayIndex_bijective : Function.Bijective oddRayIndex := by
  constructor
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    change 2 ^ a * (2 * b + 1) - 1 = 2 ^ c * (2 * d + 1) - 1 at h
    have hpa : 0 < 2 ^ a * (2 * b + 1) := by positivity
    have hpc : 0 < 2 ^ c * (2 * d + 1) := by positivity
    obtain ⟨hac, hbd⟩ := two_pow_odd_unique a c b d (by omega)
    exact Prod.ext hac hbd
  · intro m
    obtain ⟨k, u, hu, he⟩ := Nat.exists_eq_two_pow_mul_odd (n := m + 1) (by omega)
    obtain ⟨j, hj⟩ := hu
    refine ⟨(k, j), ?_⟩
    change 2 ^ k * (2 * j + 1) - 1 = m
    rw [show 2 * j + 1 = u by omega, ← he]
    omega

private def oddRayEquiv : (ℕ × ℕ) ≃ ℕ := Equiv.ofBijective oddRayIndex oddRayIndex_bijective

private theorem tsum_odd_ray (f : ℕ → ℝ) (hf : Summable f) :
    ∑' m, f m = ∑' k, ∑' j, f (2 ^ k * (2 * j + 1) - 1) := by
  have hp : Summable (fun p : ℕ × ℕ => f (oddRayIndex p)) :=
    hf.comp_injective oddRayIndex_bijective.1
  calc
    _ = ∑' p : ℕ × ℕ, f (oddRayIndex p) := (oddRayEquiv.tsum_eq f).symm
    _ = _ := hp.tsum_prod

private theorem normalized_square_weight (a x q : ℝ) (ha : a ≠ 0) :
    (x / a)^2 * (a^2 / q) = x^2 / q := by
  by_cases hq : q = 0
  · simp [hq]
  · field_simp

/-- The actual pronic weight after normalization along a dyadic ray. -/
def fermiDyadicPronicWeight (k b : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)^2 / (pronicSeq (2 ^ k * b) : ℝ)

private theorem normalized_sieve_term (N : ℕ) (c : ℕ → ℝ) (b k : ℕ) :
    (fermiNormalizedDyadicSieve N c b k)^2 * fermiDyadicPronicWeight k b =
      (sieveSeq N c (2 ^ k * b))^2 / (pronicSeq (2 ^ k * b) : ℝ) := by
  unfold fermiNormalizedDyadicSieve fermiDyadicPronicWeight
  exact normalized_square_weight _ _ _ (by positivity)

private theorem normalized_jump_term (N : ℕ) (c : ℕ → ℝ) (b k : ℕ) :
    (fermiNormalizedDyadicJump N c b k)^2 * fermiDyadicPronicWeight (k + 1) b =
      (fermiBoundaryJump N c (2 ^ (k + 1) * b))^2 /
        (pronicSeq (2 ^ (k + 1) * b) : ℝ) := by
  unfold fermiNormalizedDyadicJump fermiDyadicPronicWeight
  exact normalized_square_weight _ _ _ (by positivity)

private theorem even_ray_boundary (k j : ℕ) :
    2 * (2 ^ k * (2 * j + 1) - 1) + 2 = 2 ^ (k + 1) * (2 * j + 1) := by
  have hp : 0 < 2 ^ k * (2 * j + 1) := by positivity
  rw [pow_succ', Nat.mul_assoc]
  omega

private theorem four_ray_boundary (k j : ℕ) :
    4 * (2 ^ k * (2 * j + 1) - 1) + 4 = 2 ^ (k + 2) * (2 * j + 1) := by
  calc
    _ = 2 * (2 * (2 ^ k * (2 * j + 1) - 1) + 2) := by ring
    _ = 2 * (2 ^ (k + 1) * (2 * j + 1)) := by rw [even_ray_boundary]
    _ = _ := by rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']; ring

private theorem summable_nonnegative_pair (f g : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m) (hg : ∀ m, 0 ≤ g m)
    (hs : Summable (fun m => f m + g m)) : Summable f ∧ Summable g := by
  constructor
  · exact Summable.of_nonneg_of_le hf (fun m => by linarith [hg m]) hs
  · exact Summable.of_nonneg_of_le hg (fun m => by linarith [hf m]) hs

/-- Complete sieve energy splits exactly into its odd readings and normalized dyadic rays. -/
theorem sieveTotalPronicEnergy_dyadic_rays (N : ℕ) (c : ℕ → ℝ) :
    sieveTotalPronicEnergy N c =
      (∑' m : ℕ, (sieveSeq N c (2 * m + 1))^2 / (pronicSeq (2 * m + 1) : ℝ)) +
      ∑' k : ℕ, ∑' j : ℕ,
        (fermiNormalizedDyadicSieve N c (2 * j + 1) (k + 1))^2 *
          fermiDyadicPronicWeight (k + 1) (2 * j + 1) := by
  let f : ℕ → ℝ := fun m => (sieveSeq N c (2 * m + 1))^2 /
    (pronicSeq (2 * m + 1) : ℝ)
  let g : ℕ → ℝ := fun m => (sieveSeq N c (2 * m + 2))^2 /
    (pronicSeq (2 * m + 2) : ℝ)
  have hs : Summable (fun m => f m + g m) := by
    simpa only [sievePairedPronicEnergy, Finset.sum_singleton] using
      (sieve_fermi_pronic_summable N c).1
  obtain ⟨hf, hg⟩ := summable_nonnegative_pair f g
    (fun m => by dsimp [f]; positivity) (fun m => by dsimp [g]; positivity) hs
  calc
    _ = ∑' m, (f m + g m) := by
      simp only [sieveTotalPronicEnergy, sievePairedPronicEnergy, Finset.sum_singleton, f, g]
    _ = (∑' m, f m) + ∑' m, g m := hf.tsum_add hg
    _ = (∑' m, f m) + ∑' k, ∑' j, g (2 ^ k * (2 * j + 1) - 1) := by
      rw [tsum_odd_ray g hg]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro k
      apply tsum_congr
      intro j
      dsimp only [g]
      rw [even_ray_boundary]
      exact (normalized_sieve_term N c (2 * j + 1) (k + 1)).symm

/-- The selected trace has the same odd energy and the next-level dyadic jump weight. -/
theorem fermiSelectedTotalPronicEnergy_dyadic_rays (N : ℕ) (c : ℕ → ℝ) :
    fermiSelectedTotalPronicEnergy N c =
      (∑' m : ℕ, (sieveSeq N c (2 * m + 1))^2 / (pronicSeq (2 * m + 1) : ℝ)) +
      ∑' k : ℕ, ∑' j : ℕ,
        (fermiNormalizedDyadicJump N c (2 * j + 1) (k + 1))^2 *
          fermiDyadicPronicWeight (k + 2) (2 * j + 1) := by
  let f : ℕ → ℝ := fun m => (sieveSeq N c (2 * m + 1))^2 /
    (pronicSeq (2 * m + 1) : ℝ)
  let g : ℕ → ℝ := fun m => (fermiBoundaryJump N c (4 * m + 4))^2 /
    (pronicSeq (4 * m + 4) : ℝ)
  have hs : Summable (fun m => f m + g m) := by
    simpa only [fermiSelectedPronicEnergy, Finset.sum_singleton,
      fermiBoundaryJump_odd, neg_sq] using (sieve_fermi_pronic_summable N c).2
  obtain ⟨hf, hg⟩ := summable_nonnegative_pair f g
    (fun m => by dsimp [f]; positivity) (fun m => by dsimp [g]; positivity) hs
  calc
    _ = ∑' m, (f m + g m) := by
      simp only [fermiSelectedTotalPronicEnergy, fermiSelectedPronicEnergy,
        Finset.sum_singleton, fermiBoundaryJump_odd, neg_sq, f, g]
    _ = (∑' m, f m) + ∑' m, g m := hf.tsum_add hg
    _ = (∑' m, f m) + ∑' k, ∑' j, g (2 ^ k * (2 * j + 1) - 1) := by
      rw [tsum_odd_ray g hg]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro k
      apply tsum_congr
      intro j
      dsimp only [g]
      rw [four_ray_boundary]
      simpa only [Nat.add_assoc] using
        (normalized_jump_term N c (2 * j + 1) (k + 1)).symm

/-- Both physical ray arrays are summable before either order of summation is chosen. -/
theorem sieve_fermi_dyadic_pronic_summable (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ =>
      (fermiNormalizedDyadicSieve N c (2 * p.2 + 1) (p.1 + 1))^2 *
        fermiDyadicPronicWeight (p.1 + 1) (2 * p.2 + 1)) ∧
    Summable (fun p : ℕ × ℕ =>
      (fermiNormalizedDyadicJump N c (2 * p.2 + 1) (p.1 + 1))^2 *
        fermiDyadicPronicWeight (p.1 + 2) (2 * p.2 + 1)) := by
  constructor
  · let f : ℕ → ℝ := fun m => (sieveSeq N c (2 * m + 1))^2 /
      (pronicSeq (2 * m + 1) : ℝ)
    let g : ℕ → ℝ := fun m => (sieveSeq N c (2 * m + 2))^2 /
      (pronicSeq (2 * m + 2) : ℝ)
    have hs : Summable (fun m => f m + g m) := by
      simpa only [sievePairedPronicEnergy, Finset.sum_singleton] using
        (sieve_fermi_pronic_summable N c).1
    have hg := (summable_nonnegative_pair f g
      (fun m => by dsimp [f]; positivity) (fun m => by dsimp [g]; positivity) hs).2
    have heq : (fun p : ℕ × ℕ =>
        (fermiNormalizedDyadicSieve N c (2 * p.2 + 1) (p.1 + 1))^2 *
          fermiDyadicPronicWeight (p.1 + 1) (2 * p.2 + 1)) =
        fun p : ℕ × ℕ => g (oddRayIndex p) := by
      funext p
      dsimp only [g, oddRayIndex]
      rw [even_ray_boundary]
      exact normalized_sieve_term N c (2 * p.2 + 1) (p.1 + 1)
    rw [heq]
    exact hg.comp_injective oddRayIndex_bijective.1
  · let f : ℕ → ℝ := fun m => (sieveSeq N c (2 * m + 1))^2 /
      (pronicSeq (2 * m + 1) : ℝ)
    let g : ℕ → ℝ := fun m => (fermiBoundaryJump N c (4 * m + 4))^2 /
      (pronicSeq (4 * m + 4) : ℝ)
    have hs : Summable (fun m => f m + g m) := by
      simpa only [fermiSelectedPronicEnergy, Finset.sum_singleton,
        fermiBoundaryJump_odd, neg_sq] using (sieve_fermi_pronic_summable N c).2
    have hg := (summable_nonnegative_pair f g
      (fun m => by dsimp [f]; positivity) (fun m => by dsimp [g]; positivity) hs).2
    have heq : (fun p : ℕ × ℕ =>
        (fermiNormalizedDyadicJump N c (2 * p.2 + 1) (p.1 + 1))^2 *
          fermiDyadicPronicWeight (p.1 + 2) (2 * p.2 + 1)) =
        fun p : ℕ × ℕ => g (oddRayIndex p) := by
      funext p
      dsimp only [g, oddRayIndex]
      rw [four_ray_boundary]
      simpa only [Nat.add_assoc] using normalized_jump_term N c (2 * p.2 + 1) (p.1 + 1)
    rw [heq]
    exact hg.comp_injective oddRayIndex_bijective.1

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
