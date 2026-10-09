import GaloisForLFunctions.RHTower.RiemannUniformMomentCancellation
import GaloisForLFunctions.RHTower.WeilLogShiftSuperpolynomialGramCost

/-!
# Exponential cost of full-cutoff finite Gram certificates

A cluster occupying a fixed fraction of the cutoff cancels a linearly growing
number of logarithmic moments. Uniform derivative budgets make its sensitivity
geometrically small. The actual normalized Gram certificates pay the reciprocal.
-/

open scoped BigOperators

namespace RHTower

theorem exists_pairedLogKernel_geometric_cluster_envelope :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r n : ℕ),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ (n : ℝ) →
      ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ y : ℝ,
        |∑ i, c i * pairedLogKernel y (n + (i : ℕ))| ≤
          B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2 * (2 : ℝ) ^ r)⁻¹ := by
  obtain ⟨E, L, hE, hL, hcancel⟩ := exists_riemannAutocorr_uniform_moment_cancellation_envelope
  refine ⟨4 * E, L, by positivity, hL, ?_⟩
  intro r n hwidth
  let R : ℝ := (r + 1 : ℕ)
  let H : ℝ := R / (n : ℝ)
  have hR1 : 1 ≤ R := by dsimp [R]; exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hR : 0 < R := by linarith
  have hLR : R ≤ L * R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hR.le
  have hnrreal : R ≤ (n : ℝ) := by change 4 * L * R ≤ (n : ℝ) at hwidth; nlinarith
  have hn : 0 < (n : ℝ) := lt_of_lt_of_le hR hnrreal
  have hnr : r + 1 ≤ n := by dsimp [R] at hnrreal; exact_mod_cast hnrreal
  have hH0 : 0 ≤ H := (div_pos hR hn).le
  have hH1 : H ≤ 1 := (div_le_one hn).mpr hnrreal
  have hquarter : L * H ≤ (1 : ℝ) / 4 := by
    have hq : L * R / (n : ℝ) ≤ (1 : ℝ) / 4 := (div_le_iff₀ hn).mpr (by
      change 4 * L * R ≤ (n : ℝ) at hwidth
      nlinarith)
    simpa only [H, mul_div_assoc] using hq
  have hM : ((r + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r + 1) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := r + 1))
  have hgeom : ((r + 2 : ℕ) : ℝ) * L ^ r * H ^ (r + 1) ≤ 2 * ((2 : ℝ) ^ r)⁻¹ := by
    calc
      ((r + 2 : ℕ) : ℝ) * L ^ r * H ^ (r + 1) =
          ((r + 2 : ℕ) : ℝ) * (L * H) ^ r * H := by rw [mul_pow, pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (r + 1) * ((1 : ℝ) / 4) ^ r * 1 := by gcongr
      _ = 2 * ((2 : ℝ) ^ r)⁻¹ := by
        rw [pow_succ, div_pow, one_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        field_simp
  obtain ⟨c, hc, hbound⟩ := pairedLogKernel_cluster_envelope_of_moment_bound r
    (E := E * L ^ r) (by positivity) (hcancel r) n hnr
  refine ⟨c, hc, ?_⟩
  intro y
  calc
    |∑ i, c i * pairedLogKernel y (n + (i : ℕ))| ≤
        (2 * (E * L ^ r) * ((r + 2 : ℕ) : ℝ)) * Real.exp (2 * |y|) *
          ((n : ℝ) ^ 2)⁻¹ * H ^ (r + 1) := hbound y
    _ = (2 * E * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹) *
        (((r + 2 : ℕ) : ℝ) * L ^ r * H ^ (r + 1)) := by ring
    _ ≤ (2 * E * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹) *
        (2 * ((2 : ℝ) ^ r)⁻¹) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (4 * E) * Real.exp (2 * |y|) * ((n : ℝ) ^ 2 * (2 : ℝ) ^ r)⁻¹ := by
      rw [mul_inv_rev]
      ring

theorem exists_finiteWeilGram_geometric_cluster_cost_bound :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (s : Finset ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate s tests → ∀ (r k : ℕ),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∀ i : Fin (r + 2), k + (i : ℕ) ∈ s) →
      2 * (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) <
        ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_pairedLogKernel_geometric_cluster_envelope
  refine ⟨B, L, hB, hL, ?_⟩
  intro s tests hcert r k hwidth hmem
  exact finiteWeilGram_cluster_cost_of_paired_bound r s tests hcert k hmem hB
    (by positivity) (hbound r (k + 2) hwidth)

/-- A fixed fraction of the cutoff supplies a linearly growing cancellation
order, forcing an exponential staircase lower bound. -/
theorem exists_finiteWeilGram_cutoff_exponential_cost_bound :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∀ tests : Finset FiniteWeilGramTest,
      FiniteWeilGramNormCertificate (Finset.range N) tests →
      (2 : ℝ) ^ (N / K) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_geometric_cluster_cost_bound
  obtain ⟨K, hKreal⟩ := exists_nat_gt (4 * L + 1)
  have hK2 : 2 ≤ K := by
    have h : (2 : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast h
  have hK : 0 < K := by omega
  refine ⟨B, hB, K, hK2, ?_⟩
  intro N hN tests hcert
  let q : ℕ := N / K
  let r : ℕ := q - 2
  let k : ℕ := N - q
  have hq2 : 2 ≤ q := (Nat.le_div_iff_mul_le hK).mpr hN
  have hqN : q ≤ N := Nat.div_le_self N K
  have hrq : r + 2 = q := by dsimp [r]; omega
  have hkq : k + q = N := by dsimp [k]; omega
  have hKq : K * q ≤ N := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self N K
  have hbudget : 4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have hqcast : (r : ℝ) + 2 = (q : ℝ) := by exact_mod_cast hrq
    have hkcast : (k : ℝ) + (q : ℝ) = (N : ℝ) := by exact_mod_cast hkq
    have hprod : (K : ℝ) * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKq
    have hm := mul_le_mul_of_nonneg_right hKreal.le (Nat.cast_nonneg (α := ℝ) q)
    push_cast
    nlinarith
  have hlower : 2 * (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) <
      ∑ w ∈ tests, finiteWeilGramTailCost B w := by
    apply hbound _ tests hcert r k hbudget
    intro i
    apply Finset.mem_range.mpr
    have := i.isLt
    omega
  have hn2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
  have hfactor : (4 : ℝ) ≤ 2 * (((k + 2 : ℕ) : ℝ) ^ 2) := by nlinarith
  have hpower : (2 : ℝ) ^ q ≤ 2 * (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) := by
    calc
      (2 : ℝ) ^ q = (2 : ℝ) ^ (r + 2) := by rw [hrq]
      _ = 4 * (2 : ℝ) ^ r := by rw [pow_add]; norm_num; ring
      _ ≤ (2 * (((k + 2 : ℕ) : ℝ) ^ 2)) * (2 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = 2 * (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) := by ring
  exact hpower.trans_lt hlower

/-- Every positive normalization has an exponential lower bound with a fixed
positive prefactor. -/
theorem finiteWeilGram_cutoff_cost_exponential (B₀ : ℝ) (hB₀ : 0 < B₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∀ tests : Finset FiniteWeilGramTest,
      FiniteWeilGramNormCertificate (Finset.range N) tests →
      c * (2 : ℝ) ^ (N / K) < ∑ w ∈ tests, finiteWeilGramTailCost B₀ w := by
  obtain ⟨B, hB, K, hK, hbound⟩ := exists_finiteWeilGram_cutoff_exponential_cost_bound
  let c : ℝ := B₀ / B
  have hc : 0 < c := div_pos hB₀ hB
  have heq : c * B = B₀ := by dsimp [c]; field_simp
  refine ⟨c, hc, K, hK, ?_⟩
  intro N hN tests hcert
  calc
    c * (2 : ℝ) ^ (N / K) < c * ∑ w ∈ tests, finiteWeilGramTailCost B w :=
      mul_lt_mul_of_pos_left (hbound N hN tests hcert) hc
    _ = ∑ w ∈ tests, finiteWeilGramTailCost B₀ w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [← finiteWeilGramTailCost_scale, heq]

end RHTower
