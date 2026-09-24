import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence

/-!
# A universal gcd-square form bound

The Selberg gcd-power diagonalization and a multiples reindexing bound the
complete gcd-square Gram form by `N` times the squared harmonic sum. This is
the arithmetic input for bounding complete-period residue-source variance;
no cancellation of coefficients is assumed.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace RHTower.Sieve

/-- The positive harmonic sum on `[1,N]`. -/
def harmonicSqBound (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)

private theorem harmonicSqBound_nonneg (N : ℕ) :
    0 ≤ harmonicSqBound N := by
  unfold harmonicSqBound
  exact Finset.sum_nonneg (fun n hn => by positivity)

private theorem divisor_harmonic_le (N d : ℕ) (hd : 0 < d) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), 1 / (m : ℝ)) ≤
      harmonicSqBound N / (d : ℝ) := by
  rw [RHTower.sum_Icc_filter_dvd_reindex d N hd (fun m => 1 / (m : ℝ))]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrewrite :
      (∑ m ∈ Finset.Icc 1 (N / d), 1 / ((d * m : ℕ) : ℝ)) =
        (∑ m ∈ Finset.Icc 1 (N / d), 1 / (m : ℝ)) / (d : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    push_cast
    field_simp [ne_of_gt hdR, ne_of_gt hmR]
  rw [hrewrite]
  have hsubset : Finset.Icc 1 (N / d) ⊆ Finset.Icc 1 N := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
      (Finset.mem_Icc.mp hm).2.trans (Nat.div_le_self N d)⟩
  have hsum :
      (∑ m ∈ Finset.Icc 1 (N / d), 1 / (m : ℝ)) ≤ harmonicSqBound N := by
    unfold harmonicSqBound
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m hm hnot => by positivity)
  exact div_le_div_of_nonneg_right hsum hdR.le

private theorem divisor_harmonic_nonneg (N d : ℕ) :
    0 ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), 1 / (m : ℝ) := by
  exact Finset.sum_nonneg (fun m hm => by positivity)

private theorem gcd_kernel_le_sq {d : ℕ} (hd : 0 < d) :
    gcdPowKernel 2 d ≤ (d : ℝ) ^ (2 : ℝ) := by
  rw [← sum_gcdPowKernel_divisors (2 : ℝ) hd]
  exact Finset.single_le_sum
    (fun e he => gcdPowKernel_nonneg (by norm_num : (0 : ℝ) ≤ 2) e)
    (Nat.mem_divisors_self d hd.ne')

private theorem divisor_union_eq_Icc (N : ℕ) :
    (Finset.Icc 1 N).biUnion Nat.divisors = Finset.Icc 1 N := by
  ext d
  constructor
  · intro hd
    obtain ⟨m, hm, hdm⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hdvd, hm0⟩ := Nat.mem_divisors.mp hdm
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Finset.mem_Icc.mp hm).1
    exact Finset.mem_Icc.mpr ⟨hd0,
      (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hdvd).trans (Finset.mem_Icc.mp hm).2⟩
  · intro hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    exact Finset.mem_biUnion.mpr
      ⟨d, hd, Nat.mem_divisors.mpr ⟨dvd_rfl, hdpos.ne'⟩⟩

/-- Universal bound for the normalized gcd-square double sum. -/
theorem gcd_square_double_sum_le_harmonic (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        (Nat.gcd p.1 p.2 : ℝ) ^ (2 : ℝ) / ((p.1 : ℝ) * p.2)) ≤
      (N : ℝ) * harmonicSqBound N ^ (2 : ℕ) := by
  let S := Finset.Icc 1 N
  have hS : ∀ m ∈ S, 0 < m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hdiag := sum_gcd_rpow_div_eq_kernel_diagonal S hS (fun _ => (1 : ℝ)) (2 : ℝ)
  have hdiag' :
      (∑ p ∈ S ×ˢ S,
        (Nat.gcd p.1 p.2 : ℝ) ^ (2 : ℝ) / ((p.1 : ℝ) * p.2)) =
      ∑ d ∈ S.biUnion Nat.divisors, gcdPowKernel 2 d *
        (∑ m ∈ S.filter (fun m => d ∣ m), 1 / (m : ℝ)) ^ 2 := by
    simpa only [one_mul] using hdiag
  rw [hdiag', divisor_union_eq_Icc]
  have hterm (d : ℕ) (hd : d ∈ S) :
      gcdPowKernel 2 d *
        (∑ m ∈ S.filter (fun m => d ∣ m), 1 / (m : ℝ)) ^ 2 ≤
      harmonicSqBound N ^ (2 : ℕ) := by
    have hd0 : 0 < d := hS d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hinner := divisor_harmonic_le N d hd0
    have hinner0 := divisor_harmonic_nonneg N d
    have hH0 := harmonicSqBound_nonneg N
    have hsq := pow_le_pow_left₀ hinner0 hinner 2
    have hker := gcd_kernel_le_sq hd0
    have hker0 := gcdPowKernel_nonneg (by norm_num : (0 : ℝ) ≤ 2) d
    calc
      _ ≤ (d : ℝ) ^ (2 : ℝ) * (harmonicSqBound N / d) ^ (2 : ℕ) :=
        mul_le_mul hker hsq (sq_nonneg _) (by positivity)
      _ = harmonicSqBound N ^ (2 : ℕ) := by
        rw [Real.rpow_two]
        field_simp [ne_of_gt hdR]
  calc
    _ ≤ ∑ d ∈ S, harmonicSqBound N ^ (2 : ℕ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) * harmonicSqBound N ^ (2 : ℕ) := by
      simp [S]

end RHTower.Sieve
