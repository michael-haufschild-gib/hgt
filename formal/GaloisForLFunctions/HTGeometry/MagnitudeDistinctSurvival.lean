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

end GaloisForLFunctions
