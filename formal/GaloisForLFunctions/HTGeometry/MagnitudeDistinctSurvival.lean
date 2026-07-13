import GaloisForLFunctions.HTGeometry.SuperIncreasingValuationGap
import GaloisForLFunctions.HTGeometry.MagnitudeConvolutionExtraction

/-!
# Magnitude survival by minimal-valuation domination

`coeff N` of a degree-`D`-homogeneous differential polynomial `∑_μ c_μ ∏ f^{(μ)}` regroups, over the
index-multiset `ν` of each convolution atom, as `∑_ν a_ν · w_ν` where `a_ν = ∏ₙ (coeff n f)^{ν n}`
(magnitude `exp(−V(ν))`, `V(ν) = ∑ₙ ν n · b n`) and `w_ν ∈ ℤ` is the grouped falling-factorial weight
(`coeff_diffPoly_regrouped`).  For a superlacunary magnitude profile `b`, distinct `ν` have distinct
valuations separated by a super-increasing gap, so the minimal-valuation atom with nonzero (hence
`|·| ≥ 1`) integer weight dominates all others — giving survival with no leading-symbol hypothesis.

`norm_aval` records the atom magnitude; the regrouping and the domination toolkit
(`SuperIncreasingValuationGap`) are the two halves of that argument.
-/

open Finset PowerSeries

namespace GaloisForLFunctions

/-- **Regrouped coefficient.**  `coeff N (∑_μ c_μ ∏ₜ f^{(μₜ)})` written as a sum over the index-multiset
`ν` of each atom: the common value `∏ₙ (coeff n f)^{ν n}` times the integer weight
`∑_{fiber} c_μ · ∏ₜ descFactorial`. -/
theorem coeff_diffPoly_regrouped {D : ℕ} (f : ℂ⟦X⟧) (N : ℕ) (S : Finset (Fin D → ℕ))
    (c : (Fin D → ℕ) → ℤ) :
    (coeff N) (∑ μ ∈ S, (c μ : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = ∑ ν ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).image (fun p => key (fun t => p.2 t + p.1 t)),
          (ν.prod (fun n k => (coeff n f) ^ k))
            * (((∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
                  (fun p => key (fun t => p.2 t + p.1 t) = ν),
                c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℤ)) : ℤ) : ℂ) := by
  classical
  have hpair : (coeff N) (∑ μ ∈ S, (c μ : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = ∑ p ∈ S ×ˢ (Finset.univ.finsuppAntidiag N),
          (c p.1 : ℂ) * ((key (fun t => p.2 t + p.1 t)).prod (fun n k => (coeff n f) ^ k))
            * (∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ)) := by
    rw [map_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_smul, smul_eq_mul, coeff_prod_iterate_deriv f μ N, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.prod_mul_distrib, prod_eq_key_prod (fun t => l t + μ t) (fun n => coeff n f)]
    ring
  rw [hpair, ← Finset.sum_fiberwise_of_maps_to
    (g := fun p => key (fun t => p.2 t + p.1 t))
    (fun x hx => Finset.mem_image_of_mem (fun p => key (fun t => p.2 t + p.1 t)) hx)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨_, hkey⟩ := Finset.mem_filter.mp hp
  rw [hkey]
  push_cast
  ring

/-- **Atom magnitude.**  The regrouped atom value `∏ₙ (coeff n f)^{ν n}` has norm `exp(−V(ν))` with
`V(ν) = ∑ₙ ν n · b n` (the key-weighted valuation). -/
theorem norm_aval {f : ℂ⟦X⟧} {b : ℕ → ℝ} (hb : ∀ n, ‖coeff n f‖ = Real.exp (- b n))
    (ν : ℕ →₀ ℕ) :
    ‖ν.prod (fun n k => (coeff n f) ^ k)‖ = Real.exp (- ν.sum (fun n k => (k : ℝ) * b n)) := by
  rw [Finsupp.prod, norm_prod]
  rw [show (- ν.sum (fun n k => (k : ℝ) * b n)) = ∑ n ∈ ν.support, (- (ν n : ℝ) * b n) by
    rw [Finsupp.sum, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun n _ => by ring)]
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [norm_pow, hb n, ← Real.exp_nat_mul]
  ring_nf

/-- **Difference at a large index.**  Two multi-indices of the same total count, one supported only on
`[T,∞)`, that are unequal must differ at some index `≥ T`: agreeing on `[T,∞)` and matching counts
forces the low part of the other to vanish too.  This is what makes the minimal-valuation atom's
difference from any competitor land at a large scale, where `b` is super-increasing. -/
theorem exists_diff_ge_of_count_eq {ν ν' : ℕ →₀ ℕ}
    (hcount : (ν.sum fun _ k => k) = ν'.sum fun _ k => k)
    {T : ℕ} (hν' : ∀ n, ν' n ≠ 0 → T ≤ n) (hne : ν ≠ ν') :
    ∃ n, T ≤ n ∧ ν n ≠ ν' n := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hne
  have hν'0 : ∀ n, n < T → ν' n = 0 := fun n hn => by
    by_contra h; exact absurd (hν' n h) (not_le.mpr hn)
  set U := ν.support ∪ ν'.support with hU
  have hνsum : (ν.sum fun _ k => k) = ∑ n ∈ U, ν n := by
    rw [Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_left (fun n _ hn => Finsupp.notMem_support_iff.mp hn)
  have hν'sum : (ν'.sum fun _ k => k) = ∑ n ∈ U, ν' n := by
    rw [Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_right (fun n _ hn => Finsupp.notMem_support_iff.mp hn)
  rw [hνsum, hν'sum] at hcount
  have hhigh : ∑ n ∈ U.filter (fun n => ¬ n < T), ν n = ∑ n ∈ U.filter (fun n => ¬ n < T), ν' n :=
    Finset.sum_congr rfl (fun n hn => by rw [Finset.mem_filter] at hn; exact hcon n (not_lt.mp hn.2))
  have e1 := Finset.sum_filter_add_sum_filter_not U (fun n => n < T) ν
  have e2 := Finset.sum_filter_add_sum_filter_not U (fun n => n < T) ν'
  have hloweq : ∑ n ∈ U.filter (fun n => n < T), ν n = ∑ n ∈ U.filter (fun n => n < T), ν' n := by omega
  have hzero : ∑ n ∈ U.filter (fun n => n < T), ν' n = 0 :=
    Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_filter] at hn; exact hν'0 n hn.2)
  rw [hzero] at hloweq
  have hνlow : ∀ n, n < T → ν n = 0 := by
    intro n hn
    by_cases hnU : n ∈ U
    · exact (Finset.sum_eq_zero_iff.mp hloweq) n (by rw [Finset.mem_filter]; exact ⟨hnU, hn⟩)
    · exact Finsupp.notMem_support_iff.mp (fun h => hnU (Finset.mem_union_left _ h))
  ext n
  by_cases hnT : T ≤ n
  · exact hcon n hnT
  · rw [hνlow n (not_le.mp hnT), hν'0 n (not_le.mp hnT)]

/-- **Sharp max-index bound.**  For a multi-index of count `D` and weight `W`, the largest support
index dominates: `W ≤ min' + (D−1)·max'`.  Hence a *small* minimum index forces a *large* maximum
index — the geometric reason a small-index atom has a high valuation (its compensating large index
sits far out where `b` is superlacunary), so it cannot be the minimal-valuation atom. -/
theorem weight_le_min_add_max {ν : ℕ →₀ ℕ} {D W : ℕ} (hcount : (∑ n ∈ ν.support, ν n) = D)
    (hweight : (∑ n ∈ ν.support, n * ν n) = W) (hne : ν.support.Nonempty) :
    W ≤ ν.support.min' hne + (D - 1) * ν.support.max' hne := by
  set m := ν.support.min' hne with hm
  set M := ν.support.max' hne with hMx
  have hmM : m ≤ M := Finset.min'_le_max' _ _
  have hmmem : m ∈ ν.support := Finset.min'_mem _ _
  have hνm1 : 1 ≤ ν m := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmmem)
  rw [← hweight, ← Finset.add_sum_erase _ (fun n => n * ν n) hmmem]
  have herase : ∑ n ∈ ν.support.erase m, n * ν n ≤ M * (D - ν m) := by
    calc ∑ n ∈ ν.support.erase m, n * ν n
        ≤ ∑ n ∈ ν.support.erase m, M * ν n := by
          apply Finset.sum_le_sum; intro n hn
          exact Nat.mul_le_mul_right _ (Finset.le_max' _ n (Finset.mem_of_mem_erase hn))
      _ = M * ∑ n ∈ ν.support.erase m, ν n := by rw [Finset.mul_sum]
      _ = M * (D - ν m) := by
          congr 1
          have : ν m + ∑ n ∈ ν.support.erase m, ν n = D := by
            rw [Finset.add_sum_erase _ _ hmmem, hcount]
          omega
  have hcD : ν m ≤ D := hcount ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmmem
  have hD1 : 1 ≤ D := le_trans hνm1 hcD
  have hkey : m * ν m + M * (D - ν m) ≤ m + (D - 1) * M := by
    zify [hcD, hD1]
    nlinarith [mul_nonneg (sub_nonneg.mpr (show (1:ℤ) ≤ (ν m : ℤ) by exact_mod_cast hνm1))
      (sub_nonneg.mpr (show (m : ℤ) ≤ (M : ℤ) by exact_mod_cast hmM))]
  calc m * ν m + ∑ n ∈ ν.support.erase m, n * ν n
      ≤ m * ν m + M * (D - ν m) := by omega
    _ ≤ m + (D - 1) * M := hkey

/-- The valuation of an atom is at least its largest term `b (max')`. -/
theorem valuation_ge_b_max {ν : ℕ →₀ ℕ} {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hne : ν.support.Nonempty) :
    b (ν.support.max' hne) ≤ ν.sum (fun n k => (k : ℝ) * b n) := by
  rw [Finsupp.sum]
  set M := ν.support.max' hne with hMx
  have hMmem : M ∈ ν.support := Finset.max'_mem _ _
  have hνM1 : 1 ≤ ν M := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hMmem)
  calc b M = 1 * b M := (one_mul _).symm
    _ ≤ (ν M : ℝ) * b M := by
        apply mul_le_mul_of_nonneg_right _ (hb M); exact_mod_cast hνM1
    _ ≤ ∑ n ∈ ν.support, (ν n : ℝ) * b n :=
        Finset.single_le_sum (f := fun n => (ν n : ℝ) * b n)
          (fun n _ => mul_nonneg (Nat.cast_nonneg _) (hb n)) hMmem

/-- **Valuation floor ⟹ min-index bound.**  For a count-`D`, weight-`D·M` atom whose valuation is at
most `b K`, the minimum support index satisfies `D·M ≤ min' + (D−1)·K`.  With `b` strictly increasing,
`V ≤ b K` forces `max' ≤ K`; the weight bound then floors the min index.  Applied to the
minimal-valuation atom (bounded above by a near-`M` reference) this pins its min index near `M`. -/
theorem min_index_ge_of_valuation_le {ν : ℕ →₀ ℕ} {b : ℕ → ℝ} {D M K : ℕ}
    (hbnn : ∀ n, 0 ≤ b n) (hbmono : StrictMono b)
    (hcount : (∑ n ∈ ν.support, ν n) = D) (hweight : (∑ n ∈ ν.support, n * ν n) = D * M)
    (hne : ν.support.Nonempty) (hV : ν.sum (fun n k => (k : ℝ) * b n) ≤ b K) :
    D * M ≤ ν.support.min' hne + (D - 1) * K := by
  have hmax_le : ν.support.max' hne ≤ K := by
    by_contra h
    have hbmax : b K < b (ν.support.max' hne) := hbmono (not_le.mp h)
    have := valuation_ge_b_max hbnn hne
    linarith
  calc D * M ≤ ν.support.min' hne + (D - 1) * ν.support.max' hne :=
        weight_le_min_add_max hcount hweight hne
    _ ≤ ν.support.min' hne + (D - 1) * K :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hmax_le) _

end GaloisForLFunctions
