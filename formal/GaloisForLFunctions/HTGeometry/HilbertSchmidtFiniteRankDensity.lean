import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import GaloisForLFunctions.RHTower.HilbertSchmidtOperatorBridge

/-!
# Finite-rank density in Hilbert--Schmidt norm

The existing Hilbert-basis truncations were known to converge in operator
norm.  This module proves the stronger exact Hilbert--Schmidt tail identity
and hence density of finite-rank operators in Hilbert--Schmidt norm.
-/

noncomputable section

namespace ContinuousLinearMap

open scoped BigOperators InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem hsTruncation_apply_basis {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (s : Finset ι) (j : ι) :
    hsTruncation b T s (b j) = if j ∈ s then T (b j) else 0 := by
  rw [hsTruncation_apply]
  have horth : ∀ i k : ι,
      inner ℂ (b i) (b k) = if i = k then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  by_cases hj : j ∈ s
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [horth j j]
      simp
    · intro i hi hij
      rw [horth i j, if_neg hij]
      simp
    · exact fun h ↦ False.elim (h hj)
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
    rw [horth i j, if_neg hij]
    simp

theorem isHilbertSchmidt_hsTruncation {ι : Type*}
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (s : Finset ι) :
    IsHilbertSchmidt (hsTruncation b T s) := by
  classical
  rw [hsTruncation]
  induction s using Finset.induction_on with
  | empty => simp [isHilbertSchmidt_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hrank : IsHilbertSchmidt
          ((innerSL ℂ (b i)).smulRight (T (b i))) := by
        simpa [InnerProductSpace.rankOne_def] using
          GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne
            (T (b i)) (b i)
      exact hrank.add ih

/-- Exact Hilbert--Schmidt energy outside a finite basis truncation. -/
theorem hsNormSq_sub_hsTruncation
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (s : Finset (exists_hilbertBasis ℂ H).choose) :
    hsNormSq (T - hsTruncation (hsBasis ℂ H) T s) =
      ∑' i : {i // i ∉ s}, ‖T (hsBasis ℂ H i)‖ ^ (2 : ℕ) := by
  classical
  let b := hsBasis ℂ H
  have htrunc : IsHilbertSchmidt (hsTruncation b T s) :=
    isHilbertSchmidt_hsTruncation b T s
  have hsub : IsHilbertSchmidt (T - hsTruncation b T s) :=
    hT.sub htrunc
  rw [hsNormSq_eq hsub b]
  have htail :
      (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ (2 : ℕ)) =
        ∑' i, ({i | i ∉ s} : Set _).indicator
          (fun j ↦ ‖T (b j)‖ ^ (2 : ℕ)) i :=
    tsum_subtype ({i | i ∉ s} : Set _) (fun j ↦ ‖T (b j)‖ ^ (2 : ℕ))
  change (∑' i, ‖(T - hsTruncation b T s) (b i)‖ ^ (2 : ℕ)) =
    ∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ (2 : ℕ)
  rw [htail]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ s
  · rw [Set.indicator_of_notMem]
    · rw [sub_apply, hsTruncation_apply_basis b T s i, if_pos hi,
        sub_self, norm_zero]
      norm_num
    · simpa using hi
  · rw [Set.indicator_of_mem]
    · rw [sub_apply, hsTruncation_apply_basis b T s i, if_neg hi,
        sub_zero]
    · simpa using hi

/-- Every Hilbert--Schmidt operator admits finite-rank approximation in the
Hilbert--Schmidt norm itself. -/
theorem IsHilbertSchmidt.exists_hasRankLE_hsNorm_sub_lt
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (exists_hilbertBasis ℂ H).choose,
      RHTower.HasRankLE (hsTruncation (hsBasis ℂ H) T s) s.card ∧
      hsNorm (T - hsTruncation (hsBasis ℂ H) T s) < ε := by
  obtain ⟨s, hs⟩ := hT.exists_tail_lt (hsBasis ℂ H)
    (show 0 < ε ^ (2 : ℕ) by positivity)
  refine ⟨s, RHTower.hasRankLE_hsTruncation (hsBasis ℂ H) T s, ?_⟩
  rw [hsNorm, hsNormSq_sub_hsTruncation hT s]
  exact (Real.sqrt_lt' hε).2 hs

/-- Hilbert--Schmidt norm is a left operator ideal norm. -/
theorem IsHilbertSchmidt.hsNorm_comp_left_le
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) (A : F →L[ℂ] G) :
    hsNorm (A ∘L T) ≤ ‖A‖ * hsNorm T := by
  let b := hsBasis ℂ E
  have hcomp : IsHilbertSchmidt (A ∘L T) := hT.comp_left A
  have hpoint : ∀ i,
      ‖(A ∘L T) (b i)‖ ^ (2 : ℕ) ≤ ‖A‖ ^ (2 : ℕ) * ‖T (b i)‖ ^ (2 : ℕ) := by
    intro i
    rw [comp_apply]
    have h := A.le_opNorm (T (b i))
    nlinarith [norm_nonneg (A (T (b i))), norm_nonneg A,
      norm_nonneg (T (b i))]
  have hsum : hsNormSq (A ∘L T) ≤ ‖A‖ ^ (2 : ℕ) * hsNormSq T := by
    rw [hsNormSq_eq hcomp b, hsNormSq_eq hT b, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hpoint hcomp (hT.mul_left (‖A‖ ^ (2 : ℕ)))
  calc
    hsNorm (A ∘L T) = Real.sqrt (hsNormSq (A ∘L T)) := rfl
    _ ≤ Real.sqrt (‖A‖ ^ (2 : ℕ) * hsNormSq T) := Real.sqrt_le_sqrt hsum
    _ = ‖A‖ * hsNorm T := by
      rw [Real.sqrt_mul (sq_nonneg ‖A‖), Real.sqrt_sq (norm_nonneg A)]
      rfl

/-- Hilbert--Schmidt norm is a right operator ideal norm. -/
theorem IsHilbertSchmidt.hsNorm_comp_right_le
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) (B : G →L[ℂ] E) :
    hsNorm (T ∘L B) ≤ hsNorm T * ‖B‖ := by
  have hcomp : IsHilbertSchmidt (T ∘L B) := hT.comp_right B
  have hleft : hsNorm (ContinuousLinearMap.adjoint B ∘L
        ContinuousLinearMap.adjoint T) ≤
      ‖ContinuousLinearMap.adjoint B‖ *
        hsNorm (ContinuousLinearMap.adjoint T) :=
    IsHilbertSchmidt.hsNorm_comp_left_le
      (T := ContinuousLinearMap.adjoint T)
      hT.adjoint (ContinuousLinearMap.adjoint B)
  rw [← ContinuousLinearMap.adjoint_comp] at hleft
  have hcompAdj := hcomp.hsNormSq_adjoint
  have hTAdj := hT.hsNormSq_adjoint
  have hnormAdj : ‖ContinuousLinearMap.adjoint B‖ = ‖B‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint B
  change Real.sqrt (hsNormSq (T ∘L B)) ≤
      Real.sqrt (hsNormSq T) * ‖B‖
  rw [← hcompAdj, ← hTAdj]
  simpa [hsNorm, hnormAdj, mul_comm] using hleft

/-- Hilbert--Schmidt mass is lower semicontinuous under operator-norm
convergence.  A uniform Hilbert--Schmidt bound therefore survives the limit. -/
theorem isHilbertSchmidt_and_hsNorm_le_of_tendsto
    {T : ℕ → H →L[ℂ] H} {S : H →L[ℂ] H} {B : ℝ}
    (hB : 0 ≤ B) (hT : ∀ n, IsHilbertSchmidt (T n))
    (hbound : ∀ n, hsNorm (T n) ≤ B)
    (hlim : Filter.Tendsto T Filter.atTop (nhds S)) :
    IsHilbertSchmidt S ∧ hsNorm S ≤ B := by
  let b := hsBasis ℂ H
  have hfinite (s : Finset (exists_hilbertBasis ℂ H).choose) :
      ∑ i ∈ s, ‖S (b i)‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
    have hsumlim : Filter.Tendsto
        (fun n ↦ ∑ i ∈ s, ‖T n (b i)‖ ^ (2 : ℕ)) Filter.atTop
        (nhds (∑ i ∈ s, ‖S (b i)‖ ^ (2 : ℕ))) := by
      apply tendsto_finsetSum
      intro i _
      have heval : Filter.Tendsto (fun n ↦ T n (b i)) Filter.atTop
          (nhds (S (b i))) :=
        ((ContinuousLinearMap.apply ℂ H (b i)).continuous.tendsto S).comp hlim
      exact (tendsto_norm.comp heval).pow 2
    apply le_of_tendsto hsumlim
    filter_upwards [] with n
    have hpartial := (hT n).summable b |>.sum_le_tsum s
      (fun i _ ↦ sq_nonneg _)
    rw [← hsNormSq_eq (hT n) b] at hpartial
    have hsq : hsNormSq (T n) = hsNorm (T n) ^ (2 : ℕ) := by
      rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg (T n))]
    rw [hsq] at hpartial
    exact hpartial.trans (by nlinarith [hsNorm_nonneg (T n), hbound n])
  have hsum : Summable fun i ↦ ‖S (b i)‖ ^ (2 : ℕ) :=
    summable_of_sum_le (fun i ↦ sq_nonneg _) hfinite
  have hS : IsHilbertSchmidt S := isHilbertSchmidt_of_summable b hsum
  refine ⟨hS, ?_⟩
  rw [hsNorm, hsNormSq_eq hS b]
  apply (Real.sqrt_le_left hB).2
  exact Real.tsum_le_of_sum_le (fun i ↦ sq_nonneg _) hfinite

end ContinuousLinearMap
