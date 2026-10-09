import GaloisForLFunctions.RHTower.Sieve.UnitBlockPoissonSummation

/-!
# The reflection of a unit block

For `1 ≤ N < N' ≤ 2N` and `1 ≤ t ≤ N²`, `N ≤ 2t`, the unit block reflects to a dual sum of length
about `t/(2πN)`:

`‖∑_{N < n ≤ N'} n^{-1-it} − ubJ(t) ∑_{k ∈ D} (t/(2πk))^{-it}‖ ≤ C((1 + log t)/N + t^{-1/2})`,

`D = {k : t/(2π(N' + ¼)) + 1 ≤ k ≤ t/(2π(N + ¾)) − 1}` (`exists_norm_mtWattUnitBlock_sub_main_le`),
and `‖ubJ(t)‖ ≤ 23 t^{-1/2}`.  This is van der Corput's B-process for the phase `−t log n`, with
an error controlled by bounds alone.

**Proof.**  Poisson summation writes the block as `∑_{k ∈ ℤ} ubFreq k`.  The edges
`k₀ < k₁ < k₂ < k₃`, the frequencies `t/(2πx)` of `x = N' + 1, N' + ¼, N + ¾, N`, sort the
frequencies:
* `k ≤ k₀ − 1` or `k ≥ k₃ + 1`: no stationary point in the support, `‖ubFreq k‖ ≤ 4/(N·2π·dist)`;
* `k ∈ D`: the stationary point is inside the plateau and `ubFreq k` is the rotated model integral
  up to `(30/π)(16π/t + 1/(N(k₂ − k)) + 1/(N(k − k₁)))`;
* the remaining `k` lie in `(k₀ − 1, k₁ + 1) ∪ (k₂ − 1, k₃ + 1)`, two intervals of length `< 3`
  because `t ≤ N²`; each has `‖ubFreq k‖ ≤ 218/√t`;
* `|k| > V`: the quadratic decay `K(1 + t)²/k²`.
The harmonic sums give `O((1 + log t)/N)`, the boundary frequencies `O(t^{-1/2})`.
-/

open Complex Set MeasureTheory Filter
open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- The dual frequencies of the unit block `(N, N']` at height `t`. -/
def ubDual (N N' : ℕ) (t : ℝ) : Finset ℤ :=
  Finset.Icc ⌈t / (2 * π * ((N' : ℝ) + 1 / 4)) + 1⌉ ⌊t / (2 * π * ((N : ℝ) + 3 / 4)) - 1⌋

theorem mem_ubDual {N N' : ℕ} {t : ℝ} {k : ℤ} :
    k ∈ ubDual N N' t ↔ t / (2 * π * ((N' : ℝ) + 1 / 4)) + 1 ≤ k ∧
      (k : ℝ) ≤ t / (2 * π * ((N : ℝ) + 3 / 4)) - 1 := by
  rw [ubDual, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- The reflected term `(t/(2πk))^{-it}·ubJ(t)`. -/
def ubMainTerm (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (((-(t * Real.log (t / (2 * π * k)))) : ℝ) * I) * ubJ t

variable {N N' : ℕ}

/-- The edges are ordered and the two boundary windows are shorter than `1`. -/
theorem ub_edges (hN : 1 ≤ N) (hNN' : N < N') {t : ℝ} (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ 2) :
    t / (2 * π * ((N' : ℝ) + 1)) < t / (2 * π * ((N' : ℝ) + 1 / 4)) ∧
    t / (2 * π * ((N' : ℝ) + 1 / 4)) < t / (2 * π * ((N : ℝ) + 3 / 4)) ∧
    t / (2 * π * ((N : ℝ) + 3 / 4)) < t / (2 * π * N) ∧
    t / (2 * π * ((N' : ℝ) + 1 / 4)) - t / (2 * π * ((N' : ℝ) + 1)) < 1 ∧
    t / (2 * π * N) - t / (2 * π * ((N : ℝ) + 3 / 4)) < 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN'r : (N : ℝ) + 1 ≤ N' := by exact_mod_cast hNN'
  have hπ : 3 < π := Real.pi_gt_three
  have hc : ∀ a b : ℝ, 0 < a → a < b → t / (2 * π * b) < t / (2 * π * a) := fun a b ha hab =>
    div_lt_div_of_pos_left ht (by positivity) (by nlinarith)
  refine ⟨hc _ _ (by positivity) (by linarith), hc _ _ (by positivity) (by linarith),
    hc _ _ (by positivity) (by linarith), ?_, ?_⟩
  · have e : t / (2 * π * ((N' : ℝ) + 1 / 4)) - t / (2 * π * ((N' : ℝ) + 1)) =
        (3 / 4) * t / (2 * π * (((N' : ℝ) + 1 / 4) * ((N' : ℝ) + 1))) := by
      field_simp; ring
    rw [e, div_lt_one (by positivity)]
    have : (N : ℝ) ^ 2 ≤ ((N' : ℝ) + 1 / 4) * ((N' : ℝ) + 1) := by nlinarith
    nlinarith
  · have e : t / (2 * π * N) - t / (2 * π * ((N : ℝ) + 3 / 4)) =
        (3 / 4) * t / (2 * π * ((N : ℝ) * ((N : ℝ) + 3 / 4))) := by
      field_simp; ring
    rw [e, div_lt_one (by positivity)]
    have : (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) + 3 / 4) := by nlinarith
    nlinarith

/-- **The frequency-by-frequency error.**  The error of the reflected main term at frequency `k`
is bounded by the sum of four class bounds, exactly one of which is active. -/
theorem norm_ubFreq_sub_ite_le (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {t : ℝ}
    (ht : 1 ≤ t) (htN : t ≤ (N : ℝ) ^ 2) (k : ℤ) :
    ‖ubFreq N N' t k - (if k ∈ ubDual N N' t then ubMainTerm t k else 0)‖ ≤
      (if (k : ℝ) + 1 ≤ t / (2 * π * ((N' : ℝ) + 1)) then
          4 / (N * (2 * π * (t / (2 * π * ((N' : ℝ) + 1)) - k))) else 0) +
      (if t / (2 * π * N) + 1 ≤ (k : ℝ) then 4 / (N * (2 * π * (k - t / (2 * π * N)))) else 0) +
      (if k ∈ ubDual N N' t then (30 / π) * (16 * π / t +
          1 / (N * (t / (2 * π * ((N : ℝ) + 3 / 4)) - k)) +
          1 / (N * (k - t / (2 * π * ((N' : ℝ) + 1 / 4))))) else 0) +
      (if ¬ ((k : ℝ) + 1 ≤ t / (2 * π * ((N' : ℝ) + 1))) ∧ ¬ (t / (2 * π * N) + 1 ≤ (k : ℝ)) ∧
          k ∉ ubDual N N' t then 218 / Real.sqrt t else 0) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨e01, e12, e23, -, -⟩ := ub_edges hN hNN' ht0 htN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  by_cases ha : (k : ℝ) + 1 ≤ t / (2 * π * ((N' : ℝ) + 1))
  · have hD : k ∉ ubDual N N' t := fun h => by have := (mem_ubDual.1 h).1; linarith
    have hb : ¬ (t / (2 * π * N) + 1 ≤ (k : ℝ)) := fun h => by linarith
    rw [if_neg hD, sub_zero, if_pos ha, if_neg hb, if_neg hD, if_neg (fun h => h.1 ha)]
    simp only [add_zero]
    exact norm_ubFreq_le_low hN hNN' ht0.le k ha
  · by_cases hb : t / (2 * π * N) + 1 ≤ (k : ℝ)
    · have hD : k ∉ ubDual N N' t := fun h => by have := (mem_ubDual.1 h).2; linarith
      rw [if_neg hD, sub_zero, if_neg ha, if_pos hb, if_neg hD, if_neg (fun h => h.2.1 hb)]
      simp only [zero_add, add_zero]
      exact norm_ubFreq_le_high hN hNN' ht0.le k hb
    · by_cases hD : k ∈ ubDual N N' t
      · obtain ⟨h1, h2⟩ := mem_ubDual.1 hD
        rw [if_pos hD, if_neg ha, if_neg hb, if_pos hD, if_neg (fun h => h.2.2 hD)]
        simp only [zero_add, add_zero]
        exact norm_ubFreq_sub_main_le hN hNN' hN' ht0 (by linarith) (by linarith)
      · rw [if_neg hD, sub_zero, if_neg ha, if_neg hb, if_neg hD, if_pos ⟨ha, hb, hD⟩]
        simp only [zero_add]
        push Not at ha
        rcases le_or_gt 1 k with hk1 | hk1
        · exact norm_ubFreq_le_stationary hN hNN' hN' ht hk1 (by linarith)
        · have hk0 : k ≤ 0 := by omega
          refine le_trans (norm_ubFreq_le_nonpos hN hNN' ht0 k hk0) ?_
          have hN'3 : (N' : ℝ) + 1 ≤ 3 * N := by
            have : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'
            have : (1 : ℝ) ≤ N := by exact_mod_cast hN
            linarith
          have hsq : Real.sqrt t ≤ t := by
            rw [Real.sqrt_le_left]; nlinarith
            linarith
          rw [div_le_div_iff₀ (by positivity) hst]
          have : 4 * ((N' : ℝ) + 1) ≤ 12 * N := by linarith
          nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 12 * N)]

/-- **Summing the class bounds over `|k| ≤ V`.**  Three harmonic sums of length at most `2V`,
at most `8/n` from the interior constants, and six boundary frequencies. -/
theorem sum_ub_class_bounds_le {k₀ k₁ k₂ k₃ t n : ℝ} {V : ℕ} {D : Finset ℤ} (ht : 0 < t)
    (hn : 0 < n) (hV : 1 ≤ V) (h01 : k₀ < k₁) (h12 : k₁ < k₂) (h23 : k₂ < k₃)
    (hw1 : k₁ - k₀ < 1) (hw2 : k₃ - k₂ < 1) (hk0 : 0 ≤ k₀) (hk3V : k₃ ≤ V)
    (hcount : 16 * π / t * k₂ ≤ 8 / n)
    (hD : ∀ k : ℤ, k ∈ D ↔ k₁ + 1 ≤ k ∧ (k : ℝ) ≤ k₂ - 1) :
    ∑ k ∈ Finset.Icc (-(V : ℤ)) V,
      ((if (k : ℝ) + 1 ≤ k₀ then 4 / (n * (2 * π * (k₀ - k))) else 0) +
      (if k₃ + 1 ≤ (k : ℝ) then 4 / (n * (2 * π * (k - k₃))) else 0) +
      (if k ∈ D then (30 / π) * (16 * π / t + 1 / (n * (k₂ - k)) + 1 / (n * (k - k₁))) else 0) +
      (if ¬ ((k : ℝ) + 1 ≤ k₀) ∧ ¬ (k₃ + 1 ≤ (k : ℝ)) ∧ k ∉ D then 218 / Real.sqrt t else 0)) ≤
      (8 / (2 * π * n)) * (1 + Real.log (2 * V)) +
        (30 / π) * (8 / n + (2 / n) * (1 + Real.log (2 * V))) + 6 * (218 / Real.sqrt t) := by
  classical
  set F := Finset.Icc (-(V : ℤ)) V with hF
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have h2V : (1 : ℝ) ≤ 2 * V := by linarith
  have hmemF : ∀ k ∈ F, -(V : ℝ) ≤ k ∧ (k : ℝ) ≤ V := fun k hk => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hk
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hlog : 0 ≤ Real.log (2 * V) := Real.log_nonneg h2V
  have hπ : 0 < π := Real.pi_pos
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- low frequencies
  have s1 : ∑ k ∈ F, (if (k : ℝ) + 1 ≤ k₀ then 4 / (n * (2 * π * (k₀ - k))) else 0) ≤
      (4 / (2 * π * n)) * (1 + Real.log (2 * V)) := by
    rw [← Finset.sum_filter]
    have : ∀ k ∈ F.filter (fun k : ℤ => (k : ℝ) + 1 ≤ k₀),
        4 / (n * (2 * π * (k₀ - k))) = (4 / (2 * π * n)) * (1 / (k₀ - k)) := fun k _ => by
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (sum_one_div_sub_le h2V _ fun k hk => ?_) (by positivity)
    obtain ⟨hkF, hk⟩ := Finset.mem_filter.1 hk
    have := hmemF k hkF
    constructor <;> linarith
  -- high frequencies
  have s2 : ∑ k ∈ F, (if k₃ + 1 ≤ (k : ℝ) then 4 / (n * (2 * π * (k - k₃))) else 0) ≤
      (4 / (2 * π * n)) * (1 + Real.log (2 * V)) := by
    rw [← Finset.sum_filter]
    have : ∀ k ∈ F.filter (fun k : ℤ => k₃ + 1 ≤ (k : ℝ)),
        4 / (n * (2 * π * (k - k₃))) = (4 / (2 * π * n)) * (1 / (k - k₃)) := fun k _ => by
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (sum_one_div_sub_le' h2V _ fun k hk => ?_) (by positivity)
    obtain ⟨hkF, hk⟩ := Finset.mem_filter.1 hk
    have := hmemF k hkF
    constructor <;> linarith
  -- interior frequencies
  have s3 : ∑ k ∈ F, (if k ∈ D then (30 / π) * (16 * π / t + 1 / (n * (k₂ - k)) +
      1 / (n * (k - k₁))) else 0) ≤ (30 / π) * (8 / n + (2 / n) * (1 + Real.log (2 * V))) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    set G := F.filter (fun k => k ∈ D) with hG
    have hGmem : ∀ k ∈ G, k₁ + 1 ≤ k ∧ (k : ℝ) ≤ k₂ - 1 ∧ -(V : ℝ) ≤ k ∧ (k : ℝ) ≤ V :=
      fun k hk => by
        obtain ⟨hkF, hkD⟩ := Finset.mem_filter.1 hk
        exact ⟨((hD k).1 hkD).1, ((hD k).1 hkD).2, (hmemF k hkF).1, (hmemF k hkF).2⟩
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have t1 : ∑ k ∈ G, 16 * π / t ≤ 8 / n := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hsub : G ⊆ Finset.Icc 1 ⌊k₂⌋ := fun k hk => by
        obtain ⟨a1, a2, -, -⟩ := hGmem k hk
        have hk1 : (1 : ℝ) ≤ k := by linarith
        exact Finset.mem_Icc.2 ⟨by exact_mod_cast hk1, Int.le_floor.2 (by linarith)⟩
      have hcard : (G.card : ℝ) ≤ k₂ := by
        have h1 := Finset.card_le_card hsub
        rw [Int.card_Icc, show ⌊k₂⌋ + 1 - 1 = ⌊k₂⌋ by ring] at h1
        have h0 : 0 ≤ ⌊k₂⌋ := Int.floor_nonneg.2 (by linarith)
        have h2 : ((⌊k₂⌋.toNat : ℕ) : ℝ) ≤ k₂ := by
          rw [show ((⌊k₂⌋.toNat : ℕ) : ℝ) = ((⌊k₂⌋.toNat : ℤ) : ℝ) by push_cast; rfl,
            Int.toNat_of_nonneg h0]
          exact Int.floor_le k₂
        exact le_trans (by exact_mod_cast h1) h2
      calc (G.card : ℝ) * (16 * π / t) ≤ k₂ * (16 * π / t) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 16 * π / t * k₂ := by ring
        _ ≤ 8 / n := hcount
    have t2 : ∑ k ∈ G, 1 / (n * (k₂ - k)) ≤ (1 / n) * (1 + Real.log (2 * V)) := by
      have : ∀ k ∈ G, 1 / (n * (k₂ - k)) = (1 / n) * (1 / (k₂ - k)) := fun k _ => by
        rw [one_div_mul_one_div]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (sum_one_div_sub_le h2V _ fun k hk => ?_) (by positivity)
      obtain ⟨a1, a2, a3, a4⟩ := hGmem k hk
      constructor <;> linarith
    have t3 : ∑ k ∈ G, 1 / (n * (k - k₁)) ≤ (1 / n) * (1 + Real.log (2 * V)) := by
      have : ∀ k ∈ G, 1 / (n * (k - k₁)) = (1 / n) * (1 / (k - k₁)) := fun k _ => by
        rw [one_div_mul_one_div]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (sum_one_div_sub_le' h2V _ fun k hk => ?_) (by positivity)
      obtain ⟨a1, a2, a3, a4⟩ := hGmem k hk
      constructor <;> linarith
    have : (2 / n) * (1 + Real.log (2 * V)) = (1 / n) * (1 + Real.log (2 * V)) +
        (1 / n) * (1 + Real.log (2 * V)) := by ring
    linarith
  -- boundary frequencies
  have s4 : ∑ k ∈ F, (if ¬ ((k : ℝ) + 1 ≤ k₀) ∧ ¬ (k₃ + 1 ≤ (k : ℝ)) ∧ k ∉ D then
      218 / Real.sqrt t else 0) ≤ 6 * (218 / Real.sqrt t) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    set B := F.filter (fun k : ℤ => ¬ ((k : ℝ) + 1 ≤ k₀) ∧ ¬ (k₃ + 1 ≤ (k : ℝ)) ∧ k ∉ D)
    have hsplit : B ⊆ B.filter (fun k : ℤ => (k : ℝ) < k₁ + 1) ∪
        B.filter (fun k : ℤ => ¬ ((k : ℝ) < k₁ + 1)) := by
      intro k hk; by_cases h : (k : ℝ) < k₁ + 1
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hk, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hk, h⟩)
    have c1 : (B.filter (fun k : ℤ => (k : ℝ) < k₁ + 1)).card ≤ 3 :=
      card_le_three_of_mem_Ioo (α := k₀ - 1) _ fun k hk => by
        obtain ⟨hkB, hk1⟩ := Finset.mem_filter.1 hk
        obtain ⟨-, ha, -, -⟩ := Finset.mem_filter.1 hkB
        push Not at ha
        constructor <;> linarith
    have c2 : (B.filter (fun k : ℤ => ¬ ((k : ℝ) < k₁ + 1))).card ≤ 3 :=
      card_le_three_of_mem_Ioo (α := k₂ - 1) _ fun k hk => by
        obtain ⟨hkB, hk1⟩ := Finset.mem_filter.1 hk
        obtain ⟨-, -, hb, hkD⟩ := Finset.mem_filter.1 hkB
        push Not at hb hk1
        have : ¬ ((k : ℝ) ≤ k₂ - 1) := fun h => hkD ((hD k).2 ⟨hk1, h⟩)
        push Not at this
        constructor <;> linarith
    have := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
    have h6 : B.card ≤ 6 := by omega
    exact_mod_cast h6
  have e : (8 / (2 * π * n)) * (1 + Real.log (2 * V)) = (4 / (2 * π * n)) * (1 + Real.log (2 * V)) +
      (4 / (2 * π * n)) * (1 + Real.log (2 * V)) := by ring
  linarith

/-- The final bookkeeping: the lattice sums and the tail are `O((1 + log t)/N + t^{-1/2})`. -/
private theorem ub_final_arith {t n K V : ℝ} (ht : 1 ≤ t) (hn : 1 ≤ n) (hnt : n ≤ 2 * t)
    (hK : 0 < K) (hV1 : (1 + t) ^ 2 * n ≤ V) (hV2 : V ≤ (1 + t) ^ 2 * n + t + 2) :
    (8 / (2 * π * n)) * (1 + Real.log (2 * V)) +
      (30 / π) * (8 / n + (2 / n) * (1 + Real.log (2 * V))) + 6 * (218 / Real.sqrt t) +
      K * (1 + t) ^ 2 * (4 / (V + 1)) ≤
      (1500 + 4 * K) * ((1 + Real.log t) / n + 1 / Real.sqrt t) := by
  have ht0 : 0 < t := by linarith
  have hn0 : 0 < n := by linarith
  have hπ : 3 < π := Real.pi_gt_three
  have hπ0 : 0 < π := Real.pi_pos
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hVpos : 0 < V := lt_of_lt_of_le (mul_pos (by positivity) hn0) hV1
  -- `log(2V) ≤ 4 + 3 log t`
  have h2V : 2 * V ≤ 22 * t ^ 3 := by
    have h1 : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    have h2 : (1 + t) ^ 2 * n ≤ 4 * t ^ 2 * (2 * t) :=
      mul_le_mul h1 hnt hn0.le (by positivity)
    have h3 : t + 2 ≤ 3 * t ^ 3 := by nlinarith [sq_nonneg t, mul_le_mul ht ht zero_le_one ht0.le]
    nlinarith
  have hlog22 : Real.log 22 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have he1 := Real.exp_one_gt_d9
    rw [he]; nlinarith [pow_le_pow_left₀ (by norm_num) he1.le 4]
  have hlogV : Real.log (2 * V) ≤ 4 + 3 * Real.log t := by
    calc Real.log (2 * V) ≤ Real.log (22 * t ^ 3) := Real.log_le_log (by positivity) h2V
      _ = Real.log 22 + 3 * Real.log t := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 4 + 3 * Real.log t := by linarith
  have hL : 1 + Real.log (2 * V) ≤ 5 * (1 + Real.log t) := by linarith
  have hlV : 0 ≤ Real.log (2 * V) := Real.log_nonneg (by nlinarith)
  have hlog1 : 0 < 1 + Real.log t := by linarith
  -- the four terms
  have T1 : (8 / (2 * π * n)) * (1 + Real.log (2 * V)) ≤ 7 * ((1 + Real.log t) / n) := by
    have hc : 8 / (2 * π * n) * 5 ≤ 7 / n := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hn0]; nlinarith
    calc (8 / (2 * π * n)) * (1 + Real.log (2 * V)) ≤ (8 / (2 * π * n)) * (5 * (1 + Real.log t)) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (8 / (2 * π * n) * 5) * (1 + Real.log t) := by ring
      _ ≤ (7 / n) * (1 + Real.log t) := mul_le_mul_of_nonneg_right hc hlog1.le
      _ = 7 * ((1 + Real.log t) / n) := by ring
  have T2 : (30 / π) * (8 / n + (2 / n) * (1 + Real.log (2 * V))) ≤
      180 * ((1 + Real.log t) / n) := by
    have hc : 30 / π ≤ 10 := by rw [div_le_iff₀ hπ0]; linarith
    have hin : 8 / n + (2 / n) * (1 + Real.log (2 * V)) ≤ 18 * ((1 + Real.log t) / n) := by
      have a : 8 / n ≤ 8 * ((1 + Real.log t) / n) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by nlinarith) hn0.le
      have b : (2 / n) * (1 + Real.log (2 * V)) ≤ 10 * ((1 + Real.log t) / n) := by
        calc (2 / n) * (1 + Real.log (2 * V)) ≤ (2 / n) * (5 * (1 + Real.log t)) :=
              mul_le_mul_of_nonneg_left hL (by positivity)
          _ = 10 * ((1 + Real.log t) / n) := by ring
      linarith
    calc (30 / π) * (8 / n + (2 / n) * (1 + Real.log (2 * V))) ≤
        10 * (18 * ((1 + Real.log t) / n)) :=
          mul_le_mul hc hin (add_nonneg (by positivity) (mul_nonneg (by positivity)
            (by linarith))) (by norm_num)
      _ = 180 * ((1 + Real.log t) / n) := by ring
  have T4 : K * (1 + t) ^ 2 * (4 / (V + 1)) ≤ 4 * K * ((1 + Real.log t) / n) := by
    have hV' : (1 + t) ^ 2 * n ≤ V + 1 := by linarith
    have a : K * (1 + t) ^ 2 * (4 / (V + 1)) ≤ 4 * K / n := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hn0]
      have := mul_le_mul_of_nonneg_left hV' (by positivity : (0 : ℝ) ≤ 4 * K)
      nlinarith
    refine le_trans a ?_
    have e : 4 * K / n = 4 * K * (1 / n) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hn0.le)
      (by positivity)
  have T3 : 6 * (218 / Real.sqrt t) = 1308 * (1 / Real.sqrt t) := by ring
  have hq : 0 ≤ (1 + Real.log t) / n := by positivity
  have hr : 0 ≤ 1 / Real.sqrt t := by positivity
  nlinarith

/-- **The pointwise reflection of a unit block.**  For `1 ≤ N < N' ≤ 2N` and `1 ≤ t ≤ N²` with
`N ≤ 2t`,
`‖∑_{N<n≤N'} n^{-1-it} − ∑_{k ∈ D} (t/(2πk))^{-it} ubJ(t)‖ ≤ C((1 + log t)/N + t^{-1/2})`. -/
theorem exists_norm_mtWattUnitBlock_sub_main_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N N' : ℕ), 1 ≤ N → N < N' → N' ≤ 2 * N → ∀ t : ℝ, 1 ≤ t →
      t ≤ (N : ℝ) ^ 2 → (N : ℝ) ≤ 2 * t →
      ‖mtWattUnitBlock N N' t - ∑ k ∈ ubDual N N' t, ubMainTerm t k‖ ≤
        C * ((1 + Real.log t) / N + 1 / Real.sqrt t) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_norm_ubFreq_le_decay
  refine ⟨1500 + 4 * K, by positivity, fun N N' hN hNN' hN' t ht htN hNt => ?_⟩
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hπ : 3 < π := Real.pi_gt_three
  obtain ⟨e01, e12, e23, w1, w2⟩ := ub_edges hN hNN' ht0 htN
  set V : ℕ := ⌈(1 + t) ^ 2 * N⌉₊ + ⌈t⌉₊ with hV
  have hV1 : (1 + t) ^ 2 * N ≤ (V : ℝ) := by
    rw [hV]; push_cast
    have := Nat.le_ceil ((1 + t) ^ 2 * (N : ℝ)); have := Nat.cast_nonneg (α := ℝ) ⌈t⌉₊
    linarith
  have hVt : t ≤ (V : ℝ) := by
    rw [hV]; push_cast
    have := Nat.le_ceil t; have := Nat.cast_nonneg (α := ℝ) ⌈(1 + t) ^ 2 * (N : ℝ)⌉₊
    linarith
  have hV2 : (V : ℝ) ≤ (1 + t) ^ 2 * N + t + 2 := by
    rw [hV]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ (1 + t) ^ 2 * (N : ℝ) by positivity)
    have := Nat.ceil_lt_add_one ht0.le
    linarith
  have hV1n : 1 ≤ V := by
    have : (1 : ℝ) ≤ V := le_trans ht hVt
    exact_mod_cast this
  set D := ubDual N N' t with hD
  set g : ℤ → ℂ := fun k => if k ∈ D then ubMainTerm t k else 0 with hg
  have hgs : Summable g := summable_of_ne_finset_zero (s := D) fun k hk => by simp [hg, hk]
  have hgsum : ∑' k, g k = ∑ k ∈ D, ubMainTerm t k := by
    rw [tsum_eq_sum (s := D) fun k hk => by simp [hg, hk]]
    exact Finset.sum_congr rfl fun k hk => by simp [hg, hk]
  have hFs := summable_norm_ubFreq hN hNN' hN' ht0.le
  have hdiff : mtWattUnitBlock N N' t - ∑ k ∈ D, ubMainTerm t k =
      ∑' k, (ubFreq N N' t k - g k) := by
    rw [mtWattUnitBlock_eq_tsum_ubFreq hN hNN' hN' ht0.le, ← hgsum,
      (Summable.of_norm hFs).tsum_sub hgs]
  have hes : Summable fun k => ‖ubFreq N N' t k - g k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_sub_le _ _)
      (hFs.add hgs.norm)
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm hes) ?_
  -- the bound for every finite set of frequencies
  have hclass := sum_ub_class_bounds_le (k₀ := t / (2 * π * ((N' : ℝ) + 1)))
    (k₁ := t / (2 * π * ((N' : ℝ) + 1 / 4))) (k₂ := t / (2 * π * ((N : ℝ) + 3 / 4)))
    (k₃ := t / (2 * π * N)) (n := N) (D := D) ht0 hN0 hV1n e01 e12 e23 w1 w2 (by positivity)
    (by
      have : t / (2 * π * N) ≤ t := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * π * N by nlinarith) ht0.le]
      linarith)
    (by
      rw [show 16 * π / t * (t / (2 * π * ((N : ℝ) + 3 / 4))) = 8 / ((N : ℝ) + 3 / 4) by
        field_simp; ring]
      exact div_le_div_of_nonneg_left (by norm_num) hN0 (by linarith))
    (fun k => mem_ubDual)
  have hF : ∑ k ∈ Finset.Icc (-(V : ℤ)) V, ‖ubFreq N N' t k - g k‖ ≤
      (8 / (2 * π * N)) * (1 + Real.log (2 * V)) +
        (30 / π) * (8 / N + (2 / N) * (1 + Real.log (2 * V))) + 6 * (218 / Real.sqrt t) :=
    le_trans (Finset.sum_le_sum fun k _ => norm_ubFreq_sub_ite_le hN hNN' hN' ht htN k) hclass
  have htail : ∀ s : Finset ℤ, (∀ k ∈ s, (V : ℤ) < |k|) →
      ∑ k ∈ s, ‖ubFreq N N' t k - g k‖ ≤ K * (1 + t) ^ 2 * (4 / ((V : ℝ) + 1)) := by
    intro s hs
    have hpt : ∀ k ∈ s, ‖ubFreq N N' t k - g k‖ ≤ K * (1 + t) ^ 2 * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      have hkV := hs k hk
      have hk0 : k ≠ 0 := by rintro rfl; simp at hkV; omega
      have hkD : k ∉ D := fun h => by
        obtain ⟨-, h2⟩ := (mem_ubDual).1 h
        have h3 : (k : ℝ) ≤ V := by
          have : t / (2 * π * ((N : ℝ) + 3 / 4)) ≤ t := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [mul_le_mul_of_nonneg_left
              (show (1 : ℝ) ≤ 2 * π * ((N : ℝ) + 3 / 4) by nlinarith) ht0.le]
          linarith
        have h4 : (1 : ℝ) ≤ k := by
          have := (mem_ubDual.1 h).1
          have : 0 ≤ t / (2 * π * ((N' : ℝ) + 1 / 4)) := by positivity
          linarith
        have : |k| = k := abs_of_pos (by exact_mod_cast (show (0 : ℝ) < k by linarith))
        rw [this] at hkV
        have : (k : ℝ) > V := by exact_mod_cast hkV
        linarith
      rw [show g k = 0 by simp [hg, hkD], sub_zero, mul_one_div]
      exact hK N N' t k hN hNN' hN' ht0.le hk0
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_le_of_lt_abs V s hs) (by positivity)
  refine le_trans (hes.tsum_le_of_sum_le fun s => ?_) (ub_final_arith ht hN1 hNt
    hK0 hV1 hV2)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => k ∈ Finset.Icc (-(V : ℤ)) V)]
  refine add_le_add (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun k hk =>
    (Finset.mem_filter.1 hk).2) fun k _ _ => norm_nonneg _) hF) (htail _ fun k hk => ?_)
  have := (Finset.mem_filter.1 hk).2
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at this
  rcases this with h | h
  · rw [abs_of_neg (by omega)]; omega
  · rw [abs_of_pos (by omega)]; exact h

end

end RHTower.Sieve
