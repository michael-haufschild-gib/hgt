import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.RHTower.WeakSchattenResidue

/-!
# Logarithmic Schatten residues under finite-rank perturbations

Finite-rank perturbations shift approximation-number indices by only a fixed amount.  This file
turns that interlacing into a uniform bound for differences of Schatten-one partial sums, proves
that their logarithmically normalized difference tends to zero, and concludes invariance of the
ordinary logarithmic Schatten residue.  This is the exact perturbation step required for the
finite-rank term in the one-prime quasi-inner decomposition.
-/

namespace RHTower

open ContinuousLinearMap Filter Finset
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Negation preserves a finite rank bound. -/
theorem HasRankLE.neg {F : H →L[ℂ] H} {r : ℕ} (hF : HasRankLE F r) :
    HasRankLE (-F) r := by
  obtain ⟨V, hVfin, hVrank, hVmem⟩ := hF
  exact ⟨V, hVfin, hVrank, fun x => by simpa using V.neg_mem (hVmem x)⟩

/-- The approximation number at a valid rank cutoff vanishes. -/
theorem approxNumber_eq_zero_of_hasRankLE {F : H →L[ℂ] H} {r : ℕ}
    (hF : HasRankLE F r) : approxNumber F r = 0 := by
  apply le_antisymm
  · simpa using approxNumber_le F r F hF
  · exact approxNumber_nonneg F r

/-- Adding an operator of rank at most `r` shifts approximation numbers by at most `r`. -/
theorem approxNumber_add_finiteRank_shift_le
    {A F : H →L[ℂ] H} {r : ℕ} (hF : HasRankLE F r) (n : ℕ) :
    approxNumber (A + F) (n + r) ≤ approxNumber A n := by
  simpa [approxNumber_eq_zero_of_hasRankLE hF] using approxNumber_add_le A F n r

/-- Weak Schatten-one membership is preserved by addition of a finite-rank operator. -/
theorem memWeakSchattenClass_one_add_of_hasRankLE
    {A F : H →L[ℂ] H} {r : ℕ} (hA : MemWeakSchattenClass 1 A)
    (hF : HasRankLE F r) : MemWeakSchattenClass 1 (A + F) := by
  obtain ⟨C, hC, hbound⟩ := hA
  let D : ℝ := ((r : ℝ) + 1) * (C + ‖A + F‖)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, fun n => ?_⟩
  rw [Real.rpow_one]
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hnpos]
  by_cases hnr : n < r
  · have hncast : (n : ℝ) + 1 ≤ (r : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hnr)
    calc
      approxNumber (A + F) n * ((n : ℝ) + 1) ≤
          ‖A + F‖ * ((r : ℝ) + 1) :=
        mul_le_mul (approxNumber_le_norm _ _) hncast (by positivity) (norm_nonneg _)
      _ ≤ D := by dsimp [D]; nlinarith [norm_nonneg (A + F)]
  · have hrn : r ≤ n := Nat.le_of_not_gt hnr
    let k := n - r
    have hkr : k + r = n := Nat.sub_add_cancel hrn
    have hinterlace : approxNumber (A + F) n ≤ approxNumber A k := by
      simpa [hkr] using approxNumber_add_finiteRank_shift_le hF k
    have hAk := hbound k
    rw [Real.rpow_one] at hAk
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hpoint : approxNumber (A + F) n ≤ C / ((k : ℝ) + 1) :=
      hinterlace.trans hAk
    have hratio : (n : ℝ) + 1 ≤ ((r : ℝ) + 1) * ((k : ℝ) + 1) := by
      have hkn : (k : ℝ) + (r : ℝ) = (n : ℝ) := by exact_mod_cast hkr
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hquot : 0 ≤ C / ((k : ℝ) + 1) := div_nonneg hC hkpos.le
    calc
      approxNumber (A + F) n * ((n : ℝ) + 1) ≤
          (C / ((k : ℝ) + 1)) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hpoint hnpos.le
      _ ≤ (C / ((k : ℝ) + 1)) * (((r : ℝ) + 1) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hratio hquot
      _ = ((r : ℝ) + 1) * C := by field_simp [hkpos.ne']
      _ ≤ D := by dsimp [D]; nlinarith [norm_nonneg (A + F)]

/-- Weak Schatten-one membership is invariant under finite-rank perturbation. -/
theorem memWeakSchattenClass_one_iff_of_hasRankLE_sub
    {A B : H →L[ℂ] H} {r : ℕ} (hAB : HasRankLE (A - B) r) :
    MemWeakSchattenClass 1 A ↔ MemWeakSchattenClass 1 B := by
  constructor
  · intro hA
    have h := memWeakSchattenClass_one_add_of_hasRankLE hA hAB.neg
    simpa [show A + -(A - B) = B by abel] using h
  · intro hB
    have h := memWeakSchattenClass_one_add_of_hasRankLE hB hAB
    simpa [show B + (A - B) = A by abel] using h

/-- Additive form of weak Schatten-one finite-rank invariance. -/
theorem memWeakSchattenClass_one_add_iff_of_hasRankLE
    {A F : H →L[ℂ] H} {r : ℕ} (hF : HasRankLE F r) :
    MemWeakSchattenClass 1 (A + F) ↔ MemWeakSchattenClass 1 A := by
  apply memWeakSchattenClass_one_iff_of_hasRankLE_sub (r := r)
  simpa using hF

/-- Trace-class membership gives the sharp weak Schatten-one pointwise bound with trace norm as
constant. -/
theorem approxNumber_mul_succ_le_traceNorm_of_memSchattenClass_one
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) (n : ℕ) :
    approxNumber T n * ((n : ℝ) + 1) ≤ traceNorm H T := by
  have hsum : Summable fun k => approxNumber T k := hT.one_summable
  have hprefix : (∑ k ∈ Finset.range (n + 1), approxNumber T k) ≤ traceNorm H T := by
    exact hsum.sum_le_tsum (Finset.range (n + 1)) (fun k _ => approxNumber_nonneg T k)
  calc
    approxNumber T n * ((n : ℝ) + 1) =
        ∑ k ∈ Finset.range (n + 1), approxNumber T n := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ k ∈ Finset.range (n + 1), approxNumber T k := by
      apply Finset.sum_le_sum
      intro k hk
      exact approxNumber_antitone T (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ ≤ traceNorm H T := hprefix

/-- Every Schatten-one operator belongs to weak Schatten one. -/
theorem memWeakSchattenClass_one_of_memSchattenClass_one
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) :
    MemWeakSchattenClass 1 T := by
  refine ⟨traceNorm H T, traceNorm_nonneg T, fun n => ?_⟩
  rw [Real.rpow_one]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hn]
  exact approxNumber_mul_succ_le_traceNorm_of_memSchattenClass_one hT n

/-- Weak Schatten-one membership is preserved by a Schatten-one perturbation. -/
theorem memWeakSchattenClass_one_add_of_memSchattenClass_one
    {A T : H →L[ℂ] H} (hA : MemWeakSchattenClass 1 A)
    (hT : MemSchattenClass 1 T) : MemWeakSchattenClass 1 (A + T) := by
  obtain ⟨C, hC, hAbound⟩ := hA
  obtain ⟨D, hD, hTbound⟩ := memWeakSchattenClass_one_of_memSchattenClass_one hT
  refine ⟨2 * (C + D), by positivity, fun k => ?_⟩
  let n := k / 2
  have h2n : 2 * n ≤ k := by dsimp [n]; omega
  have hk : k ≤ 2 * n + 1 := by dsimp [n]; omega
  have hinterlace : approxNumber (A + T) k ≤ approxNumber A n + approxNumber T n := by
    calc
      approxNumber (A + T) k ≤ approxNumber (A + T) (n + n) :=
        approxNumber_antitone _ (by omega)
      _ ≤ approxNumber A n + approxNumber T n := approxNumber_add_le A T n n
  have hAn := hAbound n
  have hTn := hTbound n
  rw [Real.rpow_one] at hAn hTn ⊢
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  have hratio : (k : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
    exact_mod_cast Nat.succ_le_succ hk
  rw [le_div_iff₀ hkpos]
  have hsum : approxNumber A n + approxNumber T n ≤ (C + D) / ((n : ℝ) + 1) := by
    calc
      approxNumber A n + approxNumber T n ≤
          C / ((n : ℝ) + 1) + D / ((n : ℝ) + 1) := add_le_add hAn hTn
      _ = (C + D) / ((n : ℝ) + 1) := by ring
  have hCD : 0 ≤ C + D := add_nonneg hC hD
  calc
    approxNumber (A + T) k * ((k : ℝ) + 1) ≤
        (approxNumber A n + approxNumber T n) * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hinterlace hkpos.le
    _ ≤ ((C + D) / ((n : ℝ) + 1)) * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hsum hkpos.le
    _ ≤ ((C + D) / ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hratio (div_nonneg hCD hnpos.le)
    _ = 2 * (C + D) := by field_simp [hnpos.ne']

/-- Weak Schatten-one membership is invariant under Schatten-one perturbation. -/
theorem memWeakSchattenClass_one_iff_of_memSchattenClass_one_sub
    [CompleteSpace H] {A B : H →L[ℂ] H} (hAB : MemSchattenClass 1 (A - B)) :
    MemWeakSchattenClass 1 A ↔ MemWeakSchattenClass 1 B := by
  constructor
  · intro hA
    have hneg := hAB.one_neg
    have h := memWeakSchattenClass_one_add_of_memSchattenClass_one hA hneg
    simpa [show A + -(A - B) = B by abel] using h
  · intro hB
    have h := memWeakSchattenClass_one_add_of_memSchattenClass_one hB hAB
    simpa [show B + (A - B) = A by abel] using h

/-- A shifted pointwise comparison bounds every prefix by a fixed initial prefix plus the
comparison prefix. -/
theorem sum_range_le_prefix_add_of_shift
    {a b : ℕ → ℝ} {r : ℕ} (ha : ∀ n, 0 ≤ a n)
    (hshift : ∀ n, a (r + n) ≤ b n) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n) ≤
      (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range N, b n := by
  calc
    (∑ n ∈ Finset.range N, a n) ≤ ∑ n ∈ Finset.range (r + N), a n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro i hi hni
        exact ha i
    _ = (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range N, a (r + n) :=
      Finset.sum_range_add a r N
    _ ≤ (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range N, b n := by
      exact add_le_add (le_refl _) (Finset.sum_le_sum fun n _ => hshift n)

/-- A rank-`r` perturbation changes every Schatten-one partial sum by at most the sum of the two
fixed rank-`r` prefixes. -/
theorem abs_schattenPowerPartialSum_sub_le_of_hasRankLE_sub
    {A B : H →L[ℂ] H} {r N : ℕ} (hAB : HasRankLE (A - B) r) :
    |schattenPowerPartialSum 1 A N - schattenPowerPartialSum 1 B N| ≤
      schattenPowerPartialSum 1 A r + schattenPowerPartialSum 1 B r := by
  have hAshift : ∀ n, approxNumber A (r + n) ≤ approxNumber B n := by
    intro n
    have h := approxNumber_add_finiteRank_shift_le (A := B) hAB n
    rw [show B + (A - B) = A by abel, Nat.add_comm] at h
    exact h
  have hBshift : ∀ n, approxNumber B (r + n) ≤ approxNumber A n := by
    intro n
    have h := approxNumber_add_finiteRank_shift_le (A := A) hAB.neg n
    rw [show A + -(A - B) = B by abel, Nat.add_comm] at h
    exact h
  have hAle : schattenPowerPartialSum 1 A N ≤
      schattenPowerPartialSum 1 A r + schattenPowerPartialSum 1 B N := by
    simpa [schattenPowerPartialSum, Real.rpow_one] using
      sum_range_le_prefix_add_of_shift (fun n => approxNumber_nonneg A n) hAshift N
  have hBle : schattenPowerPartialSum 1 B N ≤
      schattenPowerPartialSum 1 B r + schattenPowerPartialSum 1 A N := by
    simpa [schattenPowerPartialSum, Real.rpow_one] using
      sum_range_le_prefix_add_of_shift (fun n => approxNumber_nonneg B n) hBshift N
  have hAr : 0 ≤ schattenPowerPartialSum 1 A r := by
    exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (approxNumber_nonneg A n) 1
  have hBr : 0 ≤ schattenPowerPartialSum 1 B r := by
    exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (approxNumber_nonneg B n) 1
  rw [abs_le]
  constructor <;> linarith

/-- The normalized Schatten-one partial sums of finite-rank perturbations differ by `o(1)`. -/
theorem tendsto_schattenPowerPartialSum_div_log_sub_of_hasRankLE_sub
    {A B : H →L[ℂ] H} {r : ℕ} (hAB : HasRankLE (A - B) r) :
    Tendsto (fun N : ℕ =>
      schattenPowerPartialSum 1 A N / Real.log (N + 1) -
        schattenPowerPartialSum 1 B N / Real.log (N + 1)) atTop (nhds 0) := by
  let C := schattenPowerPartialSum 1 A r + schattenPowerPartialSum 1 B r
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hCzero : Tendsto (fun N : ℕ => C / Real.log (N + 1)) atTop (nhds 0) :=
    hlog.const_div_atTop C
  refine squeeze_zero_norm' (a := fun N : ℕ => C / Real.log (N + 1)) ?_ hCzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hlogPos : 0 < Real.log (N + 1) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hN)
  rw [← sub_div]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogPos]
  exact (div_le_div_iff_of_pos_right hlogPos).2
    (abs_schattenPowerPartialSum_sub_le_of_hasRankLE_sub hAB)

/-- Existence and value of the logarithmic Schatten-one residue are invariant under finite-rank
perturbation. -/
theorem hasSchattenLogResidue_one_iff_of_hasRankLE_sub
    {A B : H →L[ℂ] H} {r : ℕ} (hAB : HasRankLE (A - B) r) (R : ℝ) :
    HasSchattenLogResidue 1 A R ↔ HasSchattenLogResidue 1 B R := by
  let fA := fun N : ℕ => schattenPowerPartialSum 1 A N / Real.log (N + 1)
  let fB := fun N : ℕ => schattenPowerPartialSum 1 B N / Real.log (N + 1)
  have hdiff : Tendsto (fun N => fA N - fB N) atTop (nhds 0) := by
    simpa [fA, fB] using
      tendsto_schattenPowerPartialSum_div_log_sub_of_hasRankLE_sub hAB
  constructor
  · intro hA
    have h := hA.sub hdiff
    rw [sub_zero] at h
    exact h.congr fun N => by simp [fA, fB]
  · intro hB
    have h := hB.add hdiff
    rw [add_zero] at h
    exact h.congr fun N => by simp [fA, fB]

/-- Additive form of finite-rank residue invariance. -/
theorem hasSchattenLogResidue_one_add_iff_of_hasRankLE
    {A F : H →L[ℂ] H} {r : ℕ} (hF : HasRankLE F r) (R : ℝ) :
    HasSchattenLogResidue 1 (A + F) R ↔ HasSchattenLogResidue 1 A R := by
  apply hasSchattenLogResidue_one_iff_of_hasRankLE_sub (r := r)
  simpa using hF

end

end RHTower
