import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusContour
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel
import GaloisForLFunctions.RHTower.Sieve.MaynardFactorTrivial

/-!
# Route-T sharp twisted Möbius sums and dyadic-factor transport

The Route-T contour estimate is first converted to an exact sharp partial-sum majorant.  A second
theorem records the cancellation-preserving Abel bridge needed by literal Heath--Brown Möbius
atoms: uniform sharp prefix control on a dyadic block gives the same control after the `n^{-c}`
weight, with only the leading weight and the unavoidable factor two from subtracting global
prefixes.
-/

namespace RHTower.Sieve

open Complex Finset GaloisForLFunctions.HTGeometry

noncomputable section

def routeTMoebiusSmoothBound
    (A C C' δ N H τ U : ℝ) : ℝ :=
  2 * (routeTContourRightBound A (|τ| + U) *
        (C / H ^ 2 * (N + H + 1) ^ 2 *
          (N + H + 1) ^ routeTContourRight A (|τ| + U))) / U
    + routeTContourEdgeBound A (|τ| + U) *
        (C' / H ^ 1 * (N + H + 1) ^ 1 *
          (N + H + 1) ^ routeTContourRight A (|τ| + U)) /
        U ^ (0 + 1) *
          (routeTContourRight A (|τ| + U) -
            routeTContourLeft A δ (|τ| + U))
    + routeTContourEdgeBound A (|τ| + U) *
        (C' / H ^ 1 * (N + H + 1) ^ 1 *
          (N + H + 1) ^ routeTContourRight A (|τ| + U)) /
        U ^ (0 + 1) *
          (routeTContourRight A (|τ| + U) -
            routeTContourLeft A δ (|τ| + U))
    + routeTContourEdgeBound A (|τ| + U) *
        (2 * ((N + H) ^ routeTContourLeft A δ (|τ| + U) /
              routeTContourLeft A δ (|τ| + U))
          + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 *
              (N + H + 1) ^ routeTContourLeft A δ (|τ| + U)))

def routeTMoebiusSharpBound
    (A C C' δ N H τ U : ℝ) : ℝ :=
  routeTMoebiusSmoothBound A C C' δ N H τ U / (2 * Real.pi) + (H + 1)

/-- The explicit sharp majorant is monotone in the cutoff while contour and smoothing parameters
are fixed.  This is the prefix-uniformity needed by Abel summation. -/
theorem routeTMoebiusSharpBound_mono
    {A C C' δ H τ U N₁ N₂ : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hδ : 0 < δ)
    (hH : 0 < H) (hU : 0 < U) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂) :
    routeTMoebiusSharpBound A C C' δ N₁ H τ U ≤
      routeTMoebiusSharpBound A C C' δ N₂ H τ U := by
  have hMd : 0 ≤ routeTContourRightBound A (|τ| + U) := by
    unfold routeTContourRightBound
    have hD := routeTInverseDelta_pos A (|τ| + U)
    positivity
  have hMh : 0 ≤ routeTContourEdgeBound A (|τ| + U) := by
    unfold routeTContourEdgeBound
    positivity
  have hc : 0 < routeTContourLeft A δ (|τ| + U) := routeTContourLeft_pos
  have hd : 0 < routeTContourRight A (|τ| + U) := by
    linarith [routeTContourRight_gt_one A (|τ| + U)]
  have hdc : 0 ≤ routeTContourRight A (|τ| + U) -
      routeTContourLeft A δ (|τ| + U) :=
    sub_nonneg.mpr (routeTContourLeft_le_right hδ)
  have hbase1 : 0 ≤ N₁ + H := by linarith
  have hbase2 : 0 ≤ N₁ + H + 1 := by linarith
  have hN₂ : 0 < N₂ := hN₁.trans_le hN
  have hcoeff : 0 ≤ C' / H ^ 1 * (N₂ + H + 1) ^ 1 := by positivity
  unfold routeTMoebiusSharpBound routeTMoebiusSmoothBound
  gcongr

/-- **Exact sharp Route-T twisted Mertens bound.** -/
theorem exists_norm_sum_moebiusTwist_le_routeTSharp :
    ∃ (A C C' δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < δ ∧
      ∀ N H τ U : ℝ, 0 < N → 0 < H → 1 ≤ U →
      routeTInverseBaseHeight + U ≤ |τ| →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖ ≤
        routeTMoebiusSharpBound A C C' δ N H τ U := by
  obtain ⟨A, C, C', δ, hC, hC', hδ, hmain⟩ :=
    exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT
  refine ⟨A, C, C', δ, hC, hC', hδ, ?_⟩
  intro N H τ U hN hH hU hsep
  let S : ℂ := ∑' n : ℕ, moebiusTwist τ n *
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)
  let P : ℂ := ∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n
  have hraw := hmain N H τ U hN hH hU hsep
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsmul : ‖(2 * Real.pi : ℝ) • S‖ = 2 * Real.pi * ‖S‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpi.le]
  have hS : ‖S‖ ≤ routeTMoebiusSmoothBound A C C' δ N H τ U /
      (2 * Real.pi) := by
    rw [le_div_iff₀ hpi, mul_comm, ← hsmul]
    simpa only [routeTMoebiusSmoothBound, S] using hraw
  have hcmp : ‖S - P‖ ≤ H + 1 := by
    simpa only [S, P] using norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
      (a := moebiusTwist τ) (norm_moebiusTwist_le_one τ) hN hH
  have htri : ‖P‖ ≤ ‖S‖ + ‖S - P‖ := by
    have := norm_sub_le S (S - P)
    simpa using this
  dsimp only [routeTMoebiusSharpBound]
  exact htri.trans (add_le_add hS hcmp)

/-- A truncated Möbius dyadic block is the full twisted Möbius sequence on the interval where both
the dyadic and sharp truncations are active. -/
private theorem LSeries_truncatedMoebius_dyadic_eq_weighted_twist
    {L q : ℕ} (hNL : 2 ^ q ≤ L) (c τ : ℝ) :
    LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((c : ℂ) + (τ : ℝ) * Complex.I) =
      ∑ n ∈ Finset.Ico (2 ^ q) (min (2 ^ (q + 1)) (L + 1)),
        ((((n : ℕ) : ℝ) ^ (-c) : ℝ) : ℂ) * moebiusTwist τ n := by
  classical
  let N : ℕ := 2 ^ q
  let M : ℕ := min (2 ^ (q + 1)) (L + 1)
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact one_le_pow₀ (by norm_num)
  have hNM : N ≤ M := by
    dsimp only [N, M]
    apply le_min
    · rw [pow_succ]
      omega
    · omega
  have hsupp : ∀ n : ℕ,
      complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q) n ≠ 0 →
        n ∈ Finset.Ico N M := by
    intro n hn
    have hblock := complexCoeff_arithmeticDyadicBlock_support_Ico
      (truncatedMoebius L) q n hn
    have hnreal : arithmeticDyadicBlock (truncatedMoebius L) q n ≠ 0 := by
      intro hz
      exact hn (by simp [complexCoeff_apply, hz])
    have hnL : n ≤ L := by
      by_contra hnot
      simp [arithmeticDyadicBlock_apply, truncatedMoebius_apply, hnot] at hnreal
    rw [Finset.mem_Ico] at hblock
    rw [Finset.mem_Ico]
    exact ⟨hblock.1, lt_min hblock.2 (by omega)⟩
  rw [LSeries_eq_sum_term_of_support hsupp]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hnN : N ≤ n := hn.1
  have hn2N : n < 2 ^ (q + 1) := hn.2.trans_le (min_le_left _ _)
  have hnL : n ≤ L := by
    have : n < L + 1 := hn.2.trans_le (min_le_right _ _)
    omega
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hlog : Nat.log 2 n = q := by
    apply (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩)).2
    simpa only [N] using And.intro hnN hn2N
  rw [LSeries.term_def, if_neg hn0, complexCoeff_apply,
    arithmeticDyadicBlock_apply, if_pos hlog, truncatedMoebius_apply, if_pos hnL]
  have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
  rw [div_eq_mul_inv, ← Complex.cpow_neg, moebiusTwist, hcast]
  have hsplit :
      (((n : ℝ) : ℂ) ^ (-((c : ℂ) + (τ : ℂ) * Complex.I))) =
        (((n : ℝ) : ℂ) ^ ((-c : ℝ) : ℂ)) *
          (((n : ℝ) : ℂ) ^ (-((τ : ℂ) * Complex.I))) := by
    rw [show -((c : ℂ) + (τ : ℂ) * Complex.I) =
        ((-c : ℝ) : ℂ) + -((τ : ℂ) * Complex.I) by push_cast; ring,
      Complex.cpow_add _ _ (by exact_mod_cast hn0)]
  rw [hsplit, ← Complex.ofReal_cpow hnpos.le]
  push_cast
  ring

/-- **Cancellation-preserving Abel bridge to a literal truncated Möbius dyadic factor.**
Uniform global sharp-prefix control by `P` on the block gives the natural weighted bound
`2 P N^{-c}`. -/
theorem norm_LSeries_truncatedMoebius_dyadic_le_of_sharp_prefix
    {L q : ℕ} {c τ P : ℝ}
    (hNL : 2 ^ q ≤ L) (hc : 0 ≤ c)
    (hsharp : ∀ m : ℕ, 2 ^ q ≤ m →
      m ≤ min (2 ^ (q + 1)) (L + 1) →
      ‖∑ n ∈ Finset.range m, moebiusTwist τ n‖ ≤ P) :
    ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((c : ℂ) + (τ : ℝ) * Complex.I)‖ ≤
      2 * P * (((2 ^ q : ℕ) : ℝ) ^ (-c)) := by
  let N : ℕ := 2 ^ q
  let M : ℕ := min (2 ^ (q + 1)) (L + 1)
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact one_le_pow₀ (by norm_num)
  have hNM : N ≤ M := by
    dsimp only [N, M]
    apply le_min
    · rw [pow_succ]
      omega
    · omega
  have hpref : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, moebiusTwist τ n‖ ≤ 2 * P := by
    intro m hmN hmM
    rw [Finset.sum_Ico_eq_sub _ hmN]
    have htri := norm_sub_le
      (∑ n ∈ Finset.range m, moebiusTwist τ n)
      (∑ n ∈ Finset.range N, moebiusTwist τ n)
    have hm := hsharp m (by simpa only [N] using hmN) (by simpa only [M] using hmM)
    have hN := hsharp N (le_rfl) (by simpa only [N, M] using hNM)
    linarith
  have hanti : ∀ m, N ≤ m → m < M →
      (((m + 1 : ℕ) : ℝ) ^ (-c)) ≤ (((m : ℕ) : ℝ) ^ (-c)) := by
    intro m hm _
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (hN1.trans hm)
    exact Real.rpow_le_rpow_of_nonpos hm0 (by push_cast; linarith) (by linarith)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ (-c) := Real.rpow_nonneg (by positivity) _
  have hab := abel_block_bound (moebiusTwist τ)
    (fun n => (n : ℝ) ^ (-c)) N M hNM hM0 hanti (2 * P) hpref
  rw [LSeries_truncatedMoebius_dyadic_eq_weighted_twist hNL]
  simpa only [N, M, mul_assoc] using hab

/-- **Route-T bound for the literal Heath--Brown Möbius atom.**  The contour controls all sharp
prefixes with one monotone majorant; Abel summation then inserts the actual Perron abscissa. -/
theorem exists_norm_LSeries_truncatedMoebius_dyadic_le_routeT :
    ∃ (A C C' δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < δ ∧
      ∀ (L q : ℕ) (c τ H U : ℝ), 1 ≤ q → 2 ^ q ≤ L → 0 ≤ c →
      0 < H → 1 ≤ U → routeTInverseBaseHeight + U ≤ |τ| →
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (τ : ℝ) * Complex.I)‖ ≤
        2 * routeTMoebiusSharpBound A C C' δ
              (((min (2 ^ (q + 1)) (L + 1) : ℕ) : ℝ) - 1) H τ U *
            (((2 ^ q : ℕ) : ℝ) ^ (-c)) := by
  obtain ⟨A, C, C', δ, hC, hC', hδ, hmain⟩ :=
    exists_norm_sum_moebiusTwist_le_routeTSharp
  refine ⟨A, C, C', δ, hC, hC', hδ, ?_⟩
  intro L q c τ H U hq hNL hc hH hU hsep
  let N : ℕ := 2 ^ q
  let M : ℕ := min (2 ^ (q + 1)) (L + 1)
  have hN2 : 2 ≤ N := by
    dsimp only [N]
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  have hNM : N ≤ M := by
    dsimp only [N, M]
    apply le_min
    · rw [pow_succ]
      omega
    · omega
  have hM2 : 2 ≤ M := hN2.trans hNM
  have hsharp : ∀ m : ℕ, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.range m, moebiusTwist τ n‖ ≤
        routeTMoebiusSharpBound A C C' δ ((M : ℝ) - 1) H τ U := by
    intro m hmN hmM
    have hm2 : 2 ≤ m := hN2.trans hmN
    have hm2real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hmreal : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hmshape : ⌊((m : ℝ) - 1)⌋₊ + 1 = m := by
      have heq : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
      rw [heq, Nat.floor_natCast]
      omega
    have hraw := hmain ((m : ℝ) - 1) H τ U hmreal hH hU hsep
    rw [hmshape] at hraw
    have hmMreal : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    have hmono := routeTMoebiusSharpBound_mono (A := A) (τ := τ)
      hC hC' hδ hH (by linarith : 0 < U) hmreal
        (by linarith : (m : ℝ) - 1 ≤ (M : ℝ) - 1)
    exact hraw.trans hmono
  have hfactor := norm_LSeries_truncatedMoebius_dyadic_le_of_sharp_prefix
    hNL hc (P := routeTMoebiusSharpBound A C C' δ ((M : ℝ) - 1) H τ U)
      (by simpa only [N, M] using hsharp)
  simpa only [M, N] using hfactor

end

end RHTower.Sieve
