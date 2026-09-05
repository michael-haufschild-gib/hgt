/-
# The several-variable sufficiency half of the determinant-completion law

Truncating a pencil coefficient by coefficient and adding the several-variable micro-spectrum block
produces finite-rank pencils that converge to the given pencil in the Schatten norm at every
parameter and whose power traces below the order are *exactly* the prescribed jet, at every
truncation order.  That is the several-variable form of the sufficiency construction.

Main results:
* `schattenNorm_smul`, `memSchattenClass_smul` — the Schatten norm is homogeneous.
* `tendsto_schattenNorm_finsetSum` — a finite sum of Schatten-null sequences is Schatten null.
* `tendsto_schattenNorm_pencil_greedy` — the truncated pencil converges at every parameter.
* `exists_finiteRankPencil_tendsto_lowTrace` — **the several-variable sufficiency construction**.
-/
import GaloisForLFunctions.HTGeometry.PencilSufficiencyStep
import GaloisForLFunctions.HTGeometry.OperatorDeterminantSufficiency

open Filter Topology ContinuousLinearMap Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem schattenNorm_smul {p : ℝ} (hp : 0 < p) (c : ℂ) (T : H →L[ℂ] H) :
    schattenNorm p (c • T) = ‖c‖ * schattenNorm p T := by
  have hnn : (0 : ℝ) ≤ ∑' n, approxNumber T n ^ p :=
    tsum_nonneg fun n => Real.rpow_nonneg (approxNumber_nonneg T n) p
  have hcongr : ∀ n, approxNumber (c • T) n ^ p = ‖c‖ ^ p * approxNumber T n ^ p := by
    intro n
    rw [approxNumber_smul, Real.mul_rpow (norm_nonneg c) (approxNumber_nonneg T n)]
  rw [schattenNorm, schattenNorm, tsum_congr hcongr, tsum_mul_left,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) p) hnn]
  congr 1
  rw [← Real.rpow_mul (norm_nonneg c), mul_one_div, div_self hp.ne', Real.rpow_one]

theorem memSchattenClass_smul {p : ℝ} (c : ℂ) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) : MemSchattenClass p (c • T) := by
  refine (hT.mul_left (‖c‖ ^ p)).congr fun n => ?_
  rw [approxNumber_smul, Real.mul_rpow (norm_nonneg c) (approxNumber_nonneg T n)]

omit [CompleteSpace H] in
theorem memSchattenClass_finsetSum {p : ℝ} (hp : 0 < p) {ι : Type*} (s : Finset ι)
    (X : ι → (H →L[ℂ] H)) (hX : ∀ i ∈ s, MemSchattenClass p (X i)) :
    MemSchattenClass p (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using memSchattenClass_of_hasRankLE hp (hasRankLE_zero (H := H) 0)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact memSchattenClass_add hp (hX a (Finset.mem_insert_self a s))
        (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

omit [CompleteSpace H] in
theorem tendsto_schattenNorm_finsetSum {p : ℝ} (hp : 0 < p) {ι : Type*} (s : Finset ι)
    {X : ι → ℕ → H →L[ℂ] H} (hmem : ∀ i ∈ s, ∀ n, MemSchattenClass p (X i n))
    (htend : ∀ i ∈ s, Tendsto (fun n => schattenNorm p (X i n)) atTop (nhds 0)) :
    Tendsto (fun n => schattenNorm p (∑ i ∈ s, X i n)) atTop (nhds 0) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hzero : ∀ n : ℕ, schattenNorm p (∑ i ∈ (∅ : Finset ι), X i n) = 0 := by
        intro n
        rw [Finset.sum_empty, schattenNorm]
        have : ∀ m, approxNumber (0 : H →L[ℂ] H) m ^ p = 0 := by
          intro m
          rw [approxNumber_zero_op, Real.zero_rpow hp.ne']
        rw [tsum_congr this, tsum_zero, Real.zero_rpow (by positivity)]
      simp only [hzero]
      exact tendsto_const_nhds
  | insert a s ha ih =>
      have hrest := ih (fun i hi => hmem i (Finset.mem_insert_of_mem hi))
        (fun i hi => htend i (Finset.mem_insert_of_mem hi))
      have hsum : ∀ n : ℕ, (∑ i ∈ insert a s, X i n) = X a n + ∑ i ∈ s, X i n := by
        intro n
        rw [Finset.sum_insert ha]
      simp only [hsum]
      refine tendsto_schattenNorm_add hp (fun n => hmem a (Finset.mem_insert_self a s) n)
        (fun n => memSchattenClass_finsetSum hp s (fun i => X i n)
          (fun i hi => hmem i (Finset.mem_insert_of_mem hi) n)) ?_ hrest
      exact htend a (Finset.mem_insert_self a s)

/-! ## The truncated pencil converges -/

theorem tendsto_schattenNorm_pencil_greedy {p : ℝ} (hp : 0 < p) {d : ℕ}
    {A : Fin d → (H →L[ℂ] H)} (hcpt : ∀ j, IsCompactOperator (A j))
    (hA : ∀ j, MemSchattenClass p (A j)) (v : Fin d → ℂ) :
    Tendsto (fun n => schattenNorm p
      (pencilOperator (fun j => greedyTrunc (A j) n) v - pencilOperator A v)) atTop (nhds 0) := by
  classical
  have hneg : ∀ (j : Fin d) (n : ℕ), greedyTrunc (A j) n - A j = -(A j - greedyTrunc (A j) n) := by
    intro j n
    abel
  have hsub : ∀ n : ℕ, pencilOperator (fun j => greedyTrunc (A j) n) v - pencilOperator A v
      = ∑ j, v j • (greedyTrunc (A j) n - A j) := by
    intro n
    rw [pencilOperator, pencilOperator, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_sub]
  simp only [hsub]
  refine tendsto_schattenNorm_finsetSum hp Finset.univ (fun j _ n => ?_) (fun j _ => ?_)
  · refine memSchattenClass_smul _ ?_
    rw [hneg j n]
    exact memSchattenClass_neg (memSchattenClass_sub_greedyTrunc hp (hcpt j) (hA j) n)
  · have hbase : Tendsto (fun n => schattenNorm p (greedyTrunc (A j) n - A j)) atTop (nhds 0) := by
      refine (tendsto_schattenNorm_sub_greedyTrunc hp (hcpt j) (hA j)).congr fun n => ?_
      rw [hneg j n, schattenNorm_neg]
    have hscal : ∀ n : ℕ, schattenNorm p (v j • (greedyTrunc (A j) n - A j))
        = ‖v j‖ * schattenNorm p (greedyTrunc (A j) n - A j) := fun n =>
      schattenNorm_smul hp _ _
    simp only [hscal]
    simpa using hbase.const_mul ‖v j‖

/-! ## Auxiliary Schatten facts -/

theorem memSchattenClass_sub {p : ℝ} (hp : 0 < p) {X Y : H →L[ℂ] H}
    (hX : MemSchattenClass p X) (hY : MemSchattenClass p Y) : MemSchattenClass p (X - Y) := by
  rw [sub_eq_add_neg]
  exact memSchattenClass_add hp hX (memSchattenClass_neg hY)

omit [CompleteSpace H] in
theorem memSchattenClass_pencilOperator_of_hasRankLE {p : ℝ} (hp : 0 < p) {d N : ℕ}
    {X : Fin d → (H →L[ℂ] H)} (hX : ∀ j, HasRankLE (X j) N) (v : Fin d → ℂ) :
    MemSchattenClass p (pencilOperator X v) :=
  memSchattenClass_of_hasRankLE hp (hasRankLE_pencilOperator hX v)

theorem memSchattenClass_pencilOperator {p : ℝ} (hp : 0 < p) {d : ℕ}
    {X : Fin d → (H →L[ℂ] H)} (hX : ∀ j, MemSchattenClass p (X j)) (v : Fin d → ℂ) :
    MemSchattenClass p (pencilOperator X v) :=
  memSchattenClass_finsetSum hp Finset.univ _ fun j _ => memSchattenClass_smul _ (hX j)

omit [CompleteSpace H] in
theorem tendsto_schattenNorm_of_rpow_le {p : ℝ} (hp : 0 < p) {X : ℕ → H →L[ℂ] H} {c : ℝ}
    (hbd : ∀ n : ℕ, schattenNorm p (X n) ^ p ≤ (1 / ((n : ℝ) + 1)) * c) :
    Tendsto (fun n => schattenNorm p (X n)) atTop (nhds 0) := by
  have hmaj : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1)) * c) ^ (1 / p)) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * c) atTop (nhds 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const c
      simpa using this
    have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / p)) 0 :=
      Real.continuousAt_rpow_const 0 (1 / p) (Or.inr (by positivity))
    have hcomp := hcont.tendsto.comp h0
    rwa [Real.zero_rpow (by positivity : (1 : ℝ) / p ≠ 0)] at hcomp
  refine squeeze_zero (fun n => schattenNorm_nonneg _ _) (fun n => ?_) hmaj
  have hnn : (0 : ℝ) ≤ schattenNorm p (X n) := schattenNorm_nonneg _ _
  calc schattenNorm p (X n) = (schattenNorm p (X n) ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul hnn, mul_one_div, div_self hp.ne', Real.rpow_one]
    _ ≤ ((1 / ((n : ℝ) + 1)) * c) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnn _) (hbd n) (by positivity)

/-! ## The several-variable sufficiency construction -/

/-- **The several-variable sufficiency construction.**  For every Schatten-`p` pencil and every jet
of homogeneous defects below the order there are finite-rank pencils converging to it in the
Schatten norm at every parameter whose power traces below the order are *exactly* the jet, at every
truncation order. -/
theorem exists_finiteRankPencil_tendsto_lowTrace (hH : ¬ FiniteDimensional ℂ H) {p d : ℕ}
    (hp : 0 < p) {A : Fin d → (H →L[ℂ] H)} (hA : ∀ j, MemSchattenClass (p : ℝ) (A j))
    (P : ℕ → (Fin d → ℂ) → ℂ)
    (hP : ∀ k, 1 ≤ k → k ≤ p - 1 → P k ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k)) :
    ∃ F : ℕ → Fin d → (H →L[ℂ] H),
      (∀ n j, ∃ N : ℕ, HasRankLE (F n j) N) ∧
      (∀ v : Fin d → ℂ, Tendsto (fun n => schattenNorm (p : ℝ)
        (pencilOperator (F n) v - pencilOperator A v)) atTop (nhds 0)) ∧
      (∀ (n : ℕ) (v : Fin d → ℂ) (k : ℕ), 1 ≤ k → k ≤ p - 1 →
        opTrace ((pencilOperator (F n) v) ^ k) = -(k : ℂ) * P k v) := by
  classical
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hcpt : ∀ j, IsCompactOperator (A j) := fun j => (hA j).isCompactOperator hpR
  have hQ : ∀ n : ℕ, ∀ k, 1 ≤ k → k ≤ p - 1 →
      (fun v : Fin d → ℂ => -(k : ℂ) * P k v
        - opTrace ((pencilOperator (fun j => greedyTrunc (A j) n) v) ^ k))
        ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k) := by
    intro n k hk1 hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine Submodule.sub_mem _ ?_ ?_
    · have hsm : (fun v : Fin d → ℂ => -((k' + 1 : ℕ) : ℂ) * P (k' + 1) v)
          = (-((k' + 1 : ℕ) : ℂ)) • P (k' + 1) := by
        funext v
        rw [Pi.smul_apply, smul_eq_mul]
      rw [hsm]
      exact Submodule.smul_mem _ _ (hP (k' + 1) hk1 hk)
    · exact pencilTraceForm_mem_span (fun j => hasRankLE_greedyTrunc (A j) n)
        (fun j => ContinuousLinearMap.proj j)
  choose F hFrank hFtrace hFcost using fun n : ℕ =>
    exists_finiteRankPencil_lowTrace hH hp A n
      (fun k v => -(k : ℂ) * P k v
        - opTrace ((pencilOperator (fun j => greedyTrunc (A j) n) v) ^ k))
      (hQ n) (show (0 : ℝ) < 1 / (n + 1) by positivity)
  have hrankF : ∀ n : ℕ, ∃ N : ℕ, ∀ j, HasRankLE (F n j) N := by
    intro n
    choose Nf hNf using hFrank n
    exact ⟨Finset.univ.sup Nf, fun j => (hNf j).mono (Finset.le_sup (Finset.mem_univ j))⟩
  refine ⟨F, hFrank, ?_, ?_⟩
  · intro v
    have hsplit : ∀ n : ℕ, pencilOperator (F n) v - pencilOperator A v
        = (pencilOperator (F n) v - pencilOperator (fun j => greedyTrunc (A j) n) v)
          + (pencilOperator (fun j => greedyTrunc (A j) n) v - pencilOperator A v) := by
      intro n
      abel
    simp only [hsplit]
    have hblockmem : ∀ n : ℕ, MemSchattenClass (p : ℝ)
        (pencilOperator (F n) v - pencilOperator (fun j => greedyTrunc (A j) n) v) := by
      intro n
      obtain ⟨N, hN⟩ := hrankF n
      exact memSchattenClass_sub hpR (memSchattenClass_pencilOperator_of_hasRankLE hpR hN v)
        (memSchattenClass_pencilOperator_of_hasRankLE hpR
          (fun j => hasRankLE_greedyTrunc (A j) n) v)
    have hgreedymem : ∀ n : ℕ, MemSchattenClass (p : ℝ)
        (pencilOperator (fun j => greedyTrunc (A j) n) v - pencilOperator A v) :=
      fun n => memSchattenClass_sub hpR
        (memSchattenClass_pencilOperator_of_hasRankLE hpR
          (fun j => hasRankLE_greedyTrunc (A j) n) v)
        (memSchattenClass_pencilOperator hpR hA v)
    refine tendsto_schattenNorm_add hpR hblockmem hgreedymem
      (tendsto_schattenNorm_of_rpow_le hpR (c := ‖v‖ ^ p) (fun n => hFcost n v))
      (tendsto_schattenNorm_pencil_greedy hpR hcpt hA v)
  · intro n v k hk1 hk
    rw [hFtrace n v k hk1 hk]
    ring

end

end GaloisForLFunctions.HTGeometry
