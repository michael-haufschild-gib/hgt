import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison
import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation

/-!
# Positive logarithmic Schatten residues under trace-class perturbations

For positive compact operators, compare the singular-value prefix of one operator against the
other operator on the first operator's greedy singular vectors.  Horn majorization controls the
positive term, while the trace norm controls the diagonal of their difference.  Reversing the
operators proves that every pair of Schatten-one partial sums differs by at most the trace norm of
the perturbation.  Division by `log N` then proves invariance of the logarithmic residue.

This is the exact trace-class stability theorem needed after the Connes--Consani modulus-square
reduction.
-/

namespace RHTower

open ContinuousLinearMap Filter Finset
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The greedy vectors of a compact operator's energy are either zero or unit vectors. -/
theorem energySvVec_zero_or_norm_one {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) (n : ℕ) :
    svVec (energyOp T) n = 0 ∨ ‖svVec (energyOp T) n‖ = 1 := by
  rcases eq_or_ne (svVal (energyOp T) n) 0 with hzero | hne
  · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ hzero)
  · exact Or.inr
      (norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
        (energyOp_pos T) hne)

/-- One-sided trace-norm comparison of positive singular-value prefixes. -/
theorem schattenPowerPartialSum_one_le_add_traceNorm_of_nonneg
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B)
    (hAB : MemSchattenClass 1 (A - B)) (N : ℕ) :
    schattenPowerPartialSum 1 A N ≤
      schattenPowerPartialSum 1 B N + traceNorm H (A - B) := by
  let e : ℕ → H := fun n => svVec (energyOp A) n
  have he : ∀ n, e n = 0 ∨ ‖e n‖ = 1 := fun n => energySvVec_zero_or_norm_one hAcpt n
  have heorth : ∀ m n, m ≠ n → inner ℂ (e m) (e n) = 0 := by
    intro m n hmn
    exact inner_svVec_svVec_of_ne _ hmn
  have hdiagA : schattenPowerPartialSum 1 A N =
      ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (e n) (A (e n)) : ℂ) := by
    unfold schattenPowerPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [Real.rpow_one, approxNumber_eq_singVal hAcpt,
      re_inner_svVec_apply_of_nonneg hAcpt hApos]
  have hdiagB : (∑ n ∈ Finset.range N,
      RCLike.re (inner ℂ (e n) (B (e n)) : ℂ)) ≤ schattenPowerPartialSum 1 B N := by
    have h := sum_re_inner_le_sum_singVal hBcpt hBpos e he heorth (Finset.range N)
      (N := N) (by simp)
    unfold schattenPowerPartialSum
    simpa only [Real.rpow_one, approxNumber_eq_singVal hBcpt] using h
  have hABcpt : IsCompactOperator (A - B) := hAB.isCompactOperator one_pos
  have hdiff : (∑ n ∈ Finset.range N, ‖inner ℂ (e n) ((A - B) (e n))‖) ≤
      traceNorm H (A - B) :=
    sum_norm_inner_le_traceNorm hABcpt hAB.one_summable (g := e) (h := e) he heorth he heorth
      (Finset.range N)
  rw [hdiagA]
  have hsplit : (∑ n ∈ Finset.range N,
      RCLike.re (inner ℂ (e n) (A (e n)) : ℂ)) =
      (∑ n ∈ Finset.range N, RCLike.re (inner ℂ (e n) (B (e n)) : ℂ)) +
      ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (e n) ((A - B) (e n)) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [sub_apply, inner_sub_right, map_sub]
    ring
  rw [hsplit]
  calc
    (∑ n ∈ Finset.range N, RCLike.re (inner ℂ (e n) (B (e n)) : ℂ)) +
        ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (e n) ((A - B) (e n)) : ℂ) ≤
      (∑ n ∈ Finset.range N, RCLike.re (inner ℂ (e n) (B (e n)) : ℂ)) +
        ∑ n ∈ Finset.range N, ‖inner ℂ (e n) ((A - B) (e n))‖ := by
      exact add_le_add (le_refl _) (Finset.sum_le_sum fun n _ => Complex.re_le_norm _)
    _ ≤ schattenPowerPartialSum 1 B N + traceNorm H (A - B) :=
      add_le_add hdiagB hdiff

/-- Positive trace-class perturbations change every Schatten-one prefix by at most their trace
norm. -/
theorem abs_schattenPowerPartialSum_one_sub_le_traceNorm_of_nonneg
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B)
    (hAB : MemSchattenClass 1 (A - B)) (N : ℕ) :
    |schattenPowerPartialSum 1 A N - schattenPowerPartialSum 1 B N| ≤
      traceNorm H (A - B) := by
  have hupper := schattenPowerPartialSum_one_le_add_traceNorm_of_nonneg
    hAcpt hBcpt hApos hBpos hAB N
  have hBA : MemSchattenClass 1 (B - A) := by
    have h := hAB.one_neg
    simpa [show -(A - B) = B - A by abel] using h
  have hlower := schattenPowerPartialSum_one_le_add_traceNorm_of_nonneg
    hBcpt hAcpt hBpos hApos hBA N
  have hnormNeg : traceNorm H (B - A) = traceNorm H (A - B) := by
    have h := traceNorm_smul (-1 : ℂ) (A - B)
    simpa [show (-1 : ℂ) • (A - B) = B - A by module] using h
  rw [hnormNeg] at hlower
  rw [abs_le]
  constructor <;> linarith

/-- The logarithmically normalized Schatten-one prefixes of positive trace-class perturbations
differ by `o(1)`. -/
theorem tendsto_schattenPowerPartialSum_one_div_log_sub_of_nonneg_traceClass
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B)
    (hAB : MemSchattenClass 1 (A - B)) :
    Tendsto (fun N : ℕ =>
      schattenPowerPartialSum 1 A N / Real.log (N + 1) -
        schattenPowerPartialSum 1 B N / Real.log (N + 1)) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hzero : Tendsto (fun N : ℕ => traceNorm H (A - B) / Real.log (N + 1))
      atTop (nhds 0) := hlog.const_div_atTop _
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    traceNorm H (A - B) / Real.log (N + 1)) ?_ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hlogPos : 0 < Real.log (N + 1) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hN)
  rw [← sub_div]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogPos]
  exact (div_le_div_iff_of_pos_right hlogPos).2
    (abs_schattenPowerPartialSum_one_sub_le_traceNorm_of_nonneg
      hAcpt hBcpt hApos hBpos hAB N)

/-- Existence and value of the logarithmic Schatten-one residue are invariant under positive
trace-class perturbations. -/
theorem hasSchattenLogResidue_one_iff_of_nonneg_traceClass_sub
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B)
    (hAB : MemSchattenClass 1 (A - B)) (R : ℝ) :
    HasSchattenLogResidue 1 A R ↔ HasSchattenLogResidue 1 B R := by
  let fA := fun N : ℕ => schattenPowerPartialSum 1 A N / Real.log (N + 1)
  let fB := fun N : ℕ => schattenPowerPartialSum 1 B N / Real.log (N + 1)
  have hdiff : Tendsto (fun N => fA N - fB N) atTop (nhds 0) := by
    simpa [fA, fB] using
      tendsto_schattenPowerPartialSum_one_div_log_sub_of_nonneg_traceClass
        hAcpt hBcpt hApos hBpos hAB
  constructor
  · intro hA
    have h := hA.sub hdiff
    rw [sub_zero] at h
    exact h.congr fun N => by simp [fA, fB]
  · intro hB
    have h := hB.add hdiff
    rw [add_zero] at h
    exact h.congr fun N => by simp [fA, fB]

/-- Positive trace-class perturbations preserve both weak trace-ideal membership and the exact
measurable logarithmic residue. -/
theorem weakAndHasSchattenLogResidue_one_of_nonneg_traceClass_sub
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B)
    (hAB : MemSchattenClass 1 (A - B)) {R : ℝ}
    (hBweak : MemWeakSchattenClass 1 B)
    (hBres : HasSchattenLogResidue 1 B R) :
    MemWeakSchattenClass 1 A ∧ HasSchattenLogResidue 1 A R := by
  exact ⟨(memWeakSchattenClass_one_iff_of_memSchattenClass_one_sub hAB).2 hBweak,
    (hasSchattenLogResidue_one_iff_of_nonneg_traceClass_sub
      hAcpt hBcpt hApos hBpos hAB R).2 hBres⟩

end

end RHTower
