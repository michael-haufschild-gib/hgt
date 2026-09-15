import GaloisForLFunctions.RHTower.EulerDeletionMobiusGlobalLogSaving

/-!
# The first complementary block is a signed Mertens-increment field

A small initial harmonic defect does not remove the complementary arithmetic
field. Its complete first-block error retains the signed linear interaction.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionFirstTail

/-- Every omitted floor is one on the first complementary block. -/
theorem floorResidual_eq_mertens_increment {N n : ℕ} (hn : N < n) (hcap : n ≤ 2*N) :
    bdMobiusFloorResidual N n = Sieve.mertensM n - Sieve.mertensM N := by
  rw [bdMobiusFloorResidual_eq_sum_Ioc N n (by omega) hn.le]
  have hfloor (m : ℕ) (hm : m ∈ Finset.Ioc N n) : n/m = 1 := by
    obtain ⟨hNm,hmn⟩ := Finset.mem_Ioc.mp hm
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have he : (∑ m ∈ Finset.Ioc N n, ((moebius m : ℤ) : ℝ)*((n/m : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ioc N n, ((moebius m : ℤ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hfloor m hm]
    simp
  rw [he]
  rw [show Finset.Ioc N n = Finset.Ico (N+1) (n+1) by ext k; simp,
    Finset.sum_Ico_eq_sub _ (by omega)]
  rfl

/-- Exact source error on the entire first tail, including its signed scalar interaction. -/
theorem error_eq_harmonic_add_mertens_increment {N n : ℕ} (hn : N < n) (hcap : n ≤ 2*N) :
    1 - bdMobiusModularApproximant N n =
      (n : ℝ)*deningerHarmonicPartial N + Sieve.mertensM n - Sieve.mertensM N := by
  rw [one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual,
    floorResidual_eq_mertens_increment hn hcap]
  ring

/-- Literal weighted target error on N<n<=2N. -/
def firstTailErrorEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2*N), (1-bdMobiusModularApproximant N n)^2/((n : ℝ)*((n : ℝ)+1))

/-- Actual signed Mertens increments, squared only after subtraction at the cutoff. -/
def incrementEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2*N), (Sieve.mertensM n-Sieve.mertensM N)^2/((n : ℝ)*((n : ℝ)+1))

/-- The signed interaction of the increment field with the harmonic defect. -/
def incrementMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2*N), (Sieve.mertensM n-Sieve.mertensM N)/((n : ℝ)+1)

private theorem mertens_sub_eq_mobius_block {N n : ℕ} (hNn : N ≤ n) :
    Sieve.mertensM n - Sieve.mertensM N =
      ∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) := by
  have hunion : Finset.range (n + 1) =
      Finset.range (N + 1) ∪ Finset.Ioc N n := by
    ext d
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisjoint : Disjoint (Finset.range (N + 1)) (Finset.Ioc N n) := by
    simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [Sieve.mertensM, Sieve.mertensM, hunion, Finset.sum_union hdisjoint]
  ring

/-- The first-tail cross moment is an exact signed low--next-block Möbius covariance. -/
theorem incrementMoment_eq_mobius_block_covariance (N : ℕ) :
    incrementMoment N =
      ∑ d ∈ Finset.Ioc N (2 * N), ((moebius d : ℤ) : ℝ) *
        (∑ n ∈ Finset.Icc d (2 * N), 1 / ((n : ℝ) + 1)) := by
  let S := Finset.Ioc N (2 * N)
  let a : ℕ → ℝ := fun d => ((moebius d : ℤ) : ℝ)
  have htail (n : ℕ) (hn : n ∈ S) :
      (∑ d ∈ Finset.Ioc N n, a d) =
        ∑ d ∈ S, if d ≤ n then a d else 0 := by
    simp only [S, Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, S]
    omega
  have hinner (d : ℕ) (hd : d ∈ S) :
      (∑ n ∈ S, if d ≤ n then a d / ((n : ℝ) + 1) else 0) =
        a d * (∑ n ∈ Finset.Icc d (2 * N), 1 / ((n : ℝ) + 1)) := by
    simp only [S, Finset.mem_Ioc] at hd
    rw [← Finset.sum_filter]
    have hset : S.filter (fun n => d ≤ n) = Finset.Icc d (2 * N) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, S]
      omega
    rw [hset, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  unfold incrementMoment
  calc
    (∑ n ∈ Finset.Ioc N (2 * N),
      (Sieve.mertensM n - Sieve.mertensM N) / ((n : ℝ) + 1)) =
        ∑ n ∈ S, ∑ d ∈ S,
          if d ≤ n then a d / ((n : ℝ) + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mertens_sub_eq_mobius_block (by
        have := (Finset.mem_Ioc.mp hn).1
        omega), htail n hn]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    _ = ∑ d ∈ S, ∑ n ∈ S,
          if d ≤ n then a d / ((n : ℝ) + 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Ioc N (2 * N), ((moebius d : ℤ) : ℝ) *
        (∑ n ∈ Finset.Icc d (2 * N), 1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hinner d hd

/-- Complete first-tail energy, with its signed cross term retained exactly. -/
theorem firstTailErrorEnergy_eq (N : ℕ) :
    firstTailErrorEnergy N = incrementEnergy N + 2*deningerHarmonicPartial N*incrementMoment N +
      deningerHarmonicPartial N^2*(∑ n ∈ Finset.Ioc N (2*N), (n : ℝ)/((n : ℝ)+1)) := by
  unfold firstTailErrorEnergy incrementEnergy incrementMoment
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hNn,hnN⟩ := Finset.mem_Ioc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [error_eq_harmonic_add_mertens_increment hNn hnN]
  field_simp
  ring

private theorem harmonic_block_energy_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2*N), ((n : ℝ)*deningerHarmonicPartial N)^2/((n : ℝ)*((n : ℝ)+1))) ≤
      (N : ℝ)*deningerHarmonicPartial N^2 := by
  calc _ ≤ ∑ n ∈ Finset.Ioc N (2*N), deningerHarmonicPartial N^2 := by
         apply Finset.sum_le_sum
         intro n hn
         have hn0 : (0 : ℝ) < n := by
           exact_mod_cast (show 0 < n by have h := (Finset.mem_Ioc.mp hn).1; omega)
         apply (div_le_iff₀ (by positivity)).mpr
         nlinarith [mul_nonneg hn0.le (sq_nonneg (deningerHarmonicPartial N))]
       _ = _ := by simp [Nat.card_Ioc,show 2*N-N=N by omega]

/-- A first-tail upper bound retains both the harmonic defect and increment energy. -/
theorem firstTailErrorEnergy_le (N : ℕ) :
    firstTailErrorEnergy N ≤ 2*incrementEnergy N + 2*(N : ℝ)*deningerHarmonicPartial N^2 := by
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc N (2*N)) :
      (1-bdMobiusModularApproximant N n)^2/((n : ℝ)*((n : ℝ)+1)) ≤
      2*((Sieve.mertensM n-Sieve.mertensM N)^2/((n : ℝ)*((n : ℝ)+1))) +
        2*(((n : ℝ)*deningerHarmonicPartial N)^2/((n : ℝ)*((n : ℝ)+1))) := by
    obtain ⟨hNn,hnN⟩ := Finset.mem_Ioc.mp hn
    rw [error_eq_harmonic_add_mertens_increment hNn hnN]
    rw [← mul_div_assoc,← mul_div_assoc,← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg ((n : ℝ)*deningerHarmonicPartial N-(Sieve.mertensM n-Sieve.mertensM N))]
  have h := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  exact h.trans (by dsimp [incrementEnergy]; linarith [harmonic_block_energy_le N])

/-- The converse estimate exposes increment energy that the scalar initial defect cannot erase. -/
theorem incrementEnergy_le (N : ℕ) :
    incrementEnergy N ≤ 2*firstTailErrorEnergy N + 2*(N : ℝ)*deningerHarmonicPartial N^2 := by
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc N (2*N)) :
      (Sieve.mertensM n-Sieve.mertensM N)^2/((n : ℝ)*((n : ℝ)+1)) ≤
      2*((1-bdMobiusModularApproximant N n)^2/((n : ℝ)*((n : ℝ)+1))) +
        2*(((n : ℝ)*deningerHarmonicPartial N)^2/((n : ℝ)*((n : ℝ)+1))) := by
    obtain ⟨hNn,hnN⟩ := Finset.mem_Ioc.mp hn
    rw [error_eq_harmonic_add_mertens_increment hNn hnN]
    rw [← mul_div_assoc,← mul_div_assoc,← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (2*(n : ℝ)*deningerHarmonicPartial N+(Sieve.mertensM n-Sieve.mertensM N))]
  have h := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  exact h.trans (by dsimp [firstTailErrorEnergy]; linarith [harmonic_block_energy_le N])

/-- This finite first tail is part of the genuine full complementary tail. -/
theorem firstTailErrorEnergy_le_complementaryTail (N : ℕ) :
    firstTailErrorEnergy N ≤ bdMobiusComplementaryTailErrorEnergy N N := by
  have hprefix : bdMobiusPrefixErrorEnergy N (2*N) =
      bdMobiusPrefixErrorEnergy N N + firstTailErrorEnergy N := by
    unfold bdMobiusPrefixErrorEnergy firstTailErrorEnergy
    rw [show Finset.Icc 1 (2*N) = Finset.Icc 1 N ∪ Finset.Ioc N (2*N) by ext k; simp; omega,
      Finset.sum_union (by simp only [Finset.disjoint_left,Finset.mem_Icc,Finset.mem_Ioc]; omega)]
  have hfull := bdMobiusFullErrorEnergy_eq_prefix_add_tail N N
  have hdouble := bdMobiusFullErrorEnergy_eq_prefix_add_tail N (2*N)
  rw [hprefix] at hdouble
  have hnonneg : 0 ≤ bdMobiusComplementaryTailErrorEnergy N (2*N) := tsum_nonneg (fun _ => by positivity)
  linarith

/-- An unconditional lower obstruction inside the full complementary tail. -/
theorem incrementEnergy_le_full_tail (N : ℕ) :
    incrementEnergy N ≤ 2*bdMobiusComplementaryTailErrorEnergy N N +
      2*(N : ℝ)*deningerHarmonicPartial N^2 := by
  linarith [incrementEnergy_le N,firstTailErrorEnergy_le_complementaryTail N]

/-- The full actual error controls the complete first-block Mertens-increment energy. -/
theorem incrementEnergy_le_six_fullErrorEnergy (N : ℕ) :
    incrementEnergy N ≤ 6*bdMobiusFullErrorEnergy N := by
  have hfull := bdMobiusFullErrorEnergy_eq_prefix_add_tail N N
  have hprefix := bdMobiusPrefixErrorEnergy_nonneg N N
  have hscalar := half_nat_mul_deningerHarmonicPartial_sq_le_bdMobiusFullErrorEnergy N
  nlinarith [incrementEnergy_le_full_tail N]

end RHTower.DeletionFirstTail
end
