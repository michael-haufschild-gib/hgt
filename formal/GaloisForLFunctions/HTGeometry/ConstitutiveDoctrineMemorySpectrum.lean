import Mathlib
import GaloisForLFunctions.HTGeometry.RealConstantCoefficientAnnihilator

/-!
# Doctrine-relative process memory

A response sequence `m : ℕ → ℂ` is read by three successively richer processor doctrines: constant
linear recurrence, base-dependent linear recurrence, and arbitrary algebraic differential closure.
This file develops the first doctrine at the level of sequences: the Hankel windows

`seqHankel m N = (m (i + j))_{i, j ≤ N}`

have bounded rank exactly when `m` satisfies a nonzero constant-coefficient recurrence, and the
optimal bound is the order of the recurrence.  The forward direction is a column-span induction;
the converse is a compactness argument on the sphere of candidate recurrence vectors, which
replaces the classical "minimal dependent initial family of columns".
-/

namespace GaloisForLFunctions.HTGeometry

open Finset
open scoped Matrix

section SequenceMemory

/-- The Hankel window of a response sequence through time `N`. -/
noncomputable def seqHankel (m : ℕ → ℂ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun i j => m ((i : ℕ) + (j : ℕ))

@[simp] theorem seqHankel_apply (m : ℕ → ℂ) (N : ℕ) (i j : Fin (N + 1)) :
    seqHankel m N i j = m ((i : ℕ) + (j : ℕ)) := rfl

/-- **Equation (6).**  The response sequence obeys a nonzero constant-coefficient recurrence. -/
def SeqConstantRecurrence (m : ℕ → ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p ≠ 0 ∧
    ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * m (n + k) = 0

/-- **Equation (2).**  The constant-response memory `r_cc` is finite. -/
def BddHankelRank (m : ℕ → ℂ) : Prop := ∃ B : ℕ, ∀ N, (seqHankel m N).rank ≤ B

/-- The `j`-th Hankel column, as a vector of length `N + 1`. -/
noncomputable def seqColumn (m : ℕ → ℂ) (N j : ℕ) : Fin (N + 1) → ℂ :=
  fun i => m ((i : ℕ) + j)

theorem transpose_seqHankel_eq_column (m : ℕ → ℂ) (N : ℕ) (j : Fin (N + 1)) :
    (seqHankel m N)ᵀ j = seqColumn m N (j : ℕ) := rfl

/-- Every Hankel column of a recurrent sequence lies in the span of the first `p.natDegree`
columns: the recurrence rewrites each later column through earlier ones. -/
theorem seqColumn_mem_span_of_recurrence {m : ℕ → ℂ} {p : Polynomial ℂ} (hp : p ≠ 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * m (n + k) = 0) (N j : ℕ) :
    seqColumn m N j ∈
      Submodule.span ℂ (Set.range fun k : Fin p.natDegree => seqColumn m N (k : ℕ)) := by
  set r := p.natDegree with hr
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < r
    · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    · -- `j = j' + r` with `j' = j - r`
      have hjr : j - r + r = j := by omega
      have hlead : p.coeff r ≠ 0 := by
        rw [hr]
        exact Polynomial.leadingCoeff_ne_zero.mpr hp
      have hcol : p.coeff r • seqColumn m N j
          = ∑ k ∈ Finset.range r, (-(p.coeff k)) • seqColumn m N (j - r + k) := by
        funext i
        have h := hrec ((i : ℕ) + (j - r))
        rw [Finset.sum_range_succ] at h
        have hidx : ∀ k : ℕ, (i : ℕ) + (j - r + k) = (i : ℕ) + (j - r) + k := fun k => by omega
        have hlast : (i : ℕ) + (j - r) + r = (i : ℕ) + j := by omega
        have hcong : ∑ k ∈ Finset.range r, (-(p.coeff k)) * m ((i : ℕ) + (j - r + k))
            = -∑ k ∈ Finset.range r, p.coeff k * m ((i : ℕ) + (j - r) + k) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun k _ => by rw [hidx k]; ring
        simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, seqColumn]
        rw [hcong, ← hlast]
        linear_combination h
      have hmem : p.coeff r • seqColumn m N j
          ∈ Submodule.span ℂ (Set.range fun k : Fin r => seqColumn m N (k : ℕ)) := by
        rw [hcol]
        refine Submodule.sum_mem _ fun k hk => ?_
        refine Submodule.smul_mem _ _ (ih (j - r + k) ?_)
        have hkr : k < r := Finset.mem_range.mp hk
        omega
      have hinv : seqColumn m N j = (p.coeff r)⁻¹ • (p.coeff r • seqColumn m N j) := by
        rw [smul_smul, inv_mul_cancel₀ hlead, one_smul]
      rw [hinv]
      exact Submodule.smul_mem _ _ hmem

/-- **The recurrence bounds every Hankel rank by its order.** -/
theorem rank_seqHankel_le_of_recurrence {m : ℕ → ℂ} {p : Polynomial ℂ} (hp : p ≠ 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * m (n + k) = 0) (N : ℕ) :
    (seqHankel m N).rank ≤ p.natDegree := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hsub : Submodule.span ℂ (Set.range (seqHankel m N)ᵀ)
      ≤ Submodule.span ℂ (Set.range fun k : Fin p.natDegree => seqColumn m N (k : ℕ)) := by
    rw [Submodule.span_le]
    rintro v ⟨j, rfl⟩
    rw [transpose_seqHankel_eq_column]
    exact seqColumn_mem_span_of_recurrence hp hrec N (j : ℕ)
  calc Module.finrank ℂ (Submodule.span ℂ (Set.range (seqHankel m N)ᵀ))
      ≤ Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun k : Fin p.natDegree => seqColumn m N (k : ℕ))) :=
        Submodule.finrank_mono hsub
    _ ≤ p.natDegree := by
        simpa [Set.finrank] using _root_.finrank_range_le_card (R := ℂ)
          (fun k : Fin p.natDegree => seqColumn m N (k : ℕ))

theorem bddHankelRank_of_seqConstantRecurrence {m : ℕ → ℂ} (h : SeqConstantRecurrence m) :
    BddHankelRank m := by
  obtain ⟨p, hp, hrec⟩ := h
  exact ⟨p.natDegree, fun N => rank_seqHankel_le_of_recurrence hp hrec N⟩

/-- The first `B + 1` Hankel columns through time `N`. -/
noncomputable def seqHankelCols (m : ℕ → ℂ) (N B : ℕ) : Matrix (Fin (N + 1)) (Fin (B + 1)) ℂ :=
  Matrix.of fun i k => m ((i : ℕ) + (k : ℕ))

theorem rank_seqHankelCols_le {m : ℕ → ℂ} {B : ℕ} (hB : ∀ N, (seqHankel m N).rank ≤ B) (N : ℕ) :
    (seqHankelCols m N B).rank ≤ B := by
  have hsub : seqHankelCols m N B
      = (seqHankel m (max N B)).submatrix
          (fun i : Fin (N + 1) => (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin (max N B + 1)))
          (fun k : Fin (B + 1) => (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (max N B + 1))) := rfl
  rw [hsub]
  exact (Matrix.rank_submatrix_le _ _ _).trans (hB (max N B))

/-- A matrix with more columns than its rank has a nonzero kernel vector. -/
theorem exists_ne_zero_mulVec_eq_zero {N B : ℕ} (A : Matrix (Fin (N + 1)) (Fin (B + 1)) ℂ)
    (h : A.rank ≤ B) : ∃ c : Fin (B + 1) → ℂ, c ≠ 0 ∧ A *ᵥ c = 0 := by
  have hdim : Module.finrank ℂ (Fin (B + 1) → ℂ) = B + 1 := by simp
  have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrk : Module.finrank ℂ (LinearMap.range A.mulVecLin) = A.rank := rfl
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker A.mulVecLin) := by
    rw [hrk, hdim] at hsum
    omega
  obtain ⟨c, hc⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨(c : Fin (B + 1) → ℂ), fun h0 => hc (Subtype.ext h0), ?_⟩
  have hker := c.2
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
  exact hker

/-- Unit recurrence vectors surviving the first `N` constraints. -/
def recurrenceCandidates (m : ℕ → ℂ) (B N : ℕ) : Set (Fin (B + 1) → ℂ) :=
  {c | ‖c‖ = 1 ∧ ∀ i ≤ N, ∑ k, c k * m (i + (k : ℕ)) = 0}

theorem isClosed_recurrenceCandidates (m : ℕ → ℂ) (B N : ℕ) :
    IsClosed (recurrenceCandidates m B N) := by
  have h1 : IsClosed {c : Fin (B + 1) → ℂ | ‖c‖ = 1} := isClosed_eq (by fun_prop) continuous_const
  have h2 : ∀ i : ℕ, IsClosed {c : Fin (B + 1) → ℂ | ∑ k, c k * m (i + (k : ℕ)) = 0} := by
    intro i
    exact isClosed_eq (by fun_prop) continuous_const
  have hEq : recurrenceCandidates m B N
      = {c : Fin (B + 1) → ℂ | ‖c‖ = 1}
        ∩ ⋂ i ∈ Finset.range (N + 1), {c : Fin (B + 1) → ℂ | ∑ k, c k * m (i + (k : ℕ)) = 0} := by
    ext c
    simp only [recurrenceCandidates, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range]
    constructor
    · rintro ⟨h, hc⟩
      exact ⟨h, fun i hi => hc i (by omega)⟩
    · rintro ⟨h, hc⟩
      exact ⟨h, fun i hi => hc i (by omega)⟩
  rw [hEq]
  exact h1.inter (isClosed_biInter fun i _ => h2 i)

theorem recurrenceCandidates_nonempty {m : ℕ → ℂ} {B : ℕ}
    (hB : ∀ N, (seqHankel m N).rank ≤ B) (N : ℕ) : (recurrenceCandidates m B N).Nonempty := by
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_mulVec_eq_zero (seqHankelCols m N B)
    (rank_seqHankelCols_le hB N)
  have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
  refine ⟨(‖c‖ : ℂ)⁻¹ • c, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnorm]
  · intro i hi
    have hci := congrFun hc ⟨i, by omega⟩
    have hci' : ∑ k : Fin (B + 1), m (i + (k : ℕ)) * c k = 0 := by
      simpa [Matrix.mulVec, dotProduct, seqHankelCols] using hci
    calc ∑ k : Fin (B + 1), ((‖c‖ : ℂ)⁻¹ • c) k * m (i + (k : ℕ))
        = (‖c‖ : ℂ)⁻¹ * ∑ k : Fin (B + 1), m (i + (k : ℕ)) * c k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
      _ = 0 := by rw [hci', mul_zero]

/-- **The converse of the rank bound.**  Bounded Hankel rank produces a nonzero constant
recurrence vector, by a compactness argument on the sphere of candidate vectors. -/
theorem exists_recurrence_vector {m : ℕ → ℂ} {B : ℕ} (hB : ∀ N, (seqHankel m N).rank ≤ B) :
    ∃ c : Fin (B + 1) → ℂ, c ≠ 0 ∧ ∀ n, ∑ k, c k * m (n + (k : ℕ)) = 0 := by
  have hanti : ∀ N, recurrenceCandidates m B (N + 1) ⊆ recurrenceCandidates m B N := by
    intro N c hc
    exact ⟨hc.1, fun i hi => hc.2 i (by omega)⟩
  have hcompact : IsCompact (recurrenceCandidates m B 0) := by
    refine IsCompact.of_isClosed_subset (isCompact_sphere (0 : Fin (B + 1) → ℂ) 1)
      (isClosed_recurrenceCandidates m B 0) ?_
    intro c hc
    rw [mem_sphere_zero_iff_norm]
    exact hc.1
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (recurrenceCandidates m B) hanti (recurrenceCandidates_nonempty hB) hcompact
    (isClosed_recurrenceCandidates m B)
  rw [Set.mem_iInter] at hc
  refine ⟨c, ?_, fun n => (hc n).2 n le_rfl⟩
  intro h0
  have := (hc 0).1
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- The polynomial of a recurrence vector. -/
noncomputable def recurrencePoly {B : ℕ} (c : Fin (B + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (B + 1), Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)

theorem coeff_recurrencePoly {B : ℕ} (c : Fin (B + 1) → ℂ) (j : Fin (B + 1)) :
    (recurrencePoly c).coeff (j : ℕ) = c j := by
  rw [recurrencePoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hk (Fin.ext h.symm)), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem recurrencePoly_ne_zero {B : ℕ} {c : Fin (B + 1) → ℂ} (hc : c ≠ 0) :
    recurrencePoly c ≠ 0 := by
  intro h
  apply hc
  funext j
  have := coeff_recurrencePoly c j
  rw [h] at this
  simpa using this.symm

theorem natDegree_recurrencePoly_le {B : ℕ} (c : Fin (B + 1) → ℂ) :
    (recurrencePoly c).natDegree ≤ B := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  omega

theorem seqConstantRecurrence_of_bddHankelRank {m : ℕ → ℂ} (h : BddHankelRank m) :
    SeqConstantRecurrence m := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨c, hc0, hc⟩ := exists_recurrence_vector hB
  refine ⟨recurrencePoly c, recurrencePoly_ne_zero hc0, fun n => ?_⟩
  have hdeg := natDegree_recurrencePoly_le c
  have hfull : ∑ k ∈ Finset.range (B + 1), (recurrencePoly c).coeff k * m (n + k) = 0 := by
    have hfin : ∑ k : Fin (B + 1), (recurrencePoly c).coeff (k : ℕ) * m (n + (k : ℕ)) = 0 := by
      rw [Finset.sum_congr rfl fun k _ => by rw [coeff_recurrencePoly c k]]
      exact hc n
    rwa [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (recurrencePoly c).coeff k * m (n + k))] at hfin
  rw [← hfull]
  have hsubset : Finset.range ((recurrencePoly c).natDegree + 1) ⊆ Finset.range (B + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine Finset.sum_subset hsubset fun k hk hk' => ?_
  have hk'' : (recurrencePoly c).natDegree < k := by
    simp only [Finset.mem_range] at hk hk'
    omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk'', zero_mul]

/-- **Theorem 2.1, clauses 1 and 2.**  Finite constant-response memory is exactly a nonzero
constant-coefficient recurrence. -/
theorem seqConstantRecurrence_iff_bddHankelRank (m : ℕ → ℂ) :
    SeqConstantRecurrence m ↔ BddHankelRank m :=
  ⟨bddHankelRank_of_seqConstantRecurrence, seqConstantRecurrence_of_bddHankelRank⟩

end SequenceMemory

/-! ## §2 — the germ and its constant-coefficient doctrine -/

section GermMemory

open Filter Topology

/-- **Equation (1).**  The response sequence of an analytic germ. -/
noncomputable def respSeq (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0

/-- **Clause 3 of Theorem 2.1.**  A nonzero constant-coefficient linear differential equation
holds near the origin. -/
def GermConstantODE (f : ℂ → ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p ≠ 0 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * iteratedDeriv k f z = 0

theorem iteratedDeriv_iteratedDeriv (n k : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n + k) f := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', ih (deriv f), ← iteratedDeriv_succ']
    rfl

theorem analyticAt_iteratedDeriv {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- The differential operator attached to a coefficient sequence. -/
noncomputable def odeSum (a : ℕ → ℂ) (r : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (r + 1), a k * iteratedDeriv k f z

theorem analyticAt_odeSum {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (a : ℕ → ℂ) (r : ℕ) :
    AnalyticAt ℂ (odeSum a r f) x :=
  Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (analyticAt_iteratedDeriv hf k)

/-- Every jet of the operator applied to an analytic germ is the shifted operator. -/
theorem eventually_iteratedDeriv_odeSum {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (a : ℕ → ℂ) (r n : ℕ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), iteratedDeriv n (odeSum a r f) z
      = ∑ k ∈ Finset.range (r + 1), a k * iteratedDeriv (n + k) f z := by
  induction n with
  | zero =>
    filter_upwards with z
    simp only [iteratedDeriv_zero, odeSum, Nat.zero_add]
  | succ n ih =>
    have hanal : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ f z := hf.eventually_analyticAt
    have hstep : ∀ᶠ z in 𝓝 (0 : ℂ),
        deriv (fun w => ∑ k ∈ Finset.range (r + 1), a k * iteratedDeriv (n + k) f w) z
          = ∑ k ∈ Finset.range (r + 1), a k * iteratedDeriv (n + 1 + k) f z := by
      filter_upwards [hanal] with z hz
      rw [deriv_fun_sum (u := Finset.range (r + 1))
        (A := fun k w => a k * iteratedDeriv (n + k) f w)
        fun k _ => (analyticAt_const.mul (analyticAt_iteratedDeriv hz (n + k))).differentiableAt]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [deriv_const_mul _ (analyticAt_iteratedDeriv hz (n + k)).differentiableAt]
      congr 1
      rw [← iteratedDeriv_succ]
      congr 1
      omega
    have hderiv := (Filter.EventuallyEq.deriv (f₁ := iteratedDeriv n (odeSum a r f))
      (f := fun w => ∑ k ∈ Finset.range (r + 1), a k * iteratedDeriv (n + k) f w) ih)
    filter_upwards [hderiv, hstep] with z h1 h2
    rw [iteratedDeriv_succ, h1, h2]

/-- The response jets of the operator are exactly the recurrence sums. -/
theorem iteratedDeriv_odeSum_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (a : ℕ → ℂ) (r n : ℕ) :
    iteratedDeriv n (odeSum a r f) 0
      = ∑ k ∈ Finset.range (r + 1), a k * respSeq f (n + k) := by
  have h := eventually_iteratedDeriv_odeSum hf a r n
  have h0 : iteratedDeriv n (odeSum a r f) 0
      = ∑ k ∈ Finset.range (r + 1), a k * iteratedDeriv (n + k) f 0 := h.self_of_nhds
  rw [h0]
  rfl

/-- **Theorem 2.1, clauses 2 and 3.**  The response recurrence is exactly the constant-coefficient
differential equation of the germ. -/
theorem seqConstantRecurrence_respSeq_iff_germConstantODE {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    SeqConstantRecurrence (respSeq f) ↔ GermConstantODE f := by
  constructor
  · rintro ⟨p, hp, hrec⟩
    refine ⟨p, hp, ?_⟩
    have hzero : ∀ n, iteratedDeriv n (odeSum (fun k => p.coeff k) p.natDegree f) 0 = 0 := by
      intro n
      rw [iteratedDeriv_odeSum_zero hf]
      exact hrec n
    have hanal : AnalyticAt ℂ (odeSum (fun k => p.coeff k) p.natDegree f) 0 :=
      analyticAt_odeSum hf _ _
    have hseries := hanal.hasFPowerSeriesAt
    have hzeroSeries : (FormalMultilinearSeries.ofScalars ℂ
        fun n => iteratedDeriv n (odeSum (fun k => p.coeff k) p.natDegree f) 0
          / (n.factorial : ℂ)) = 0 := by
      have : (fun n => iteratedDeriv n (odeSum (fun k => p.coeff k) p.natDegree f) 0
          / (n.factorial : ℂ)) = fun _ => (0 : ℂ) := by
        funext n
        rw [hzero n, zero_div]
      rw [this]
      ext n
      simp [FormalMultilinearSeries.ofScalars]
    rw [hzeroSeries] at hseries
    exact hseries.eventually_eq_zero
  · rintro ⟨p, hp, hode⟩
    refine ⟨p, hp, fun n => ?_⟩
    have hev : odeSum (fun k => p.coeff k) p.natDegree f =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
      filter_upwards [hode] with z hz using hz
    have := EventuallyEq.iteratedDeriv_eq n hev
    rw [iteratedDeriv_odeSum_zero hf] at this
    rw [this]
    simp

/-! ### The entire Taylor extension of a recurrent response -/

/-- A constant-coefficient recurrence forces geometric growth of the response. -/
theorem exists_geometric_bound_of_seqConstantRecurrence {m : ℕ → ℂ}
    (h : SeqConstantRecurrence m) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ n, ‖m n‖ ≤ C * R ^ n := by
  obtain ⟨p, hp, hrec⟩ := h
  have hlead : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  rcases Nat.eq_zero_or_pos p.natDegree with hr0 | hrpos
  · refine ⟨0, 1, le_rfl, le_rfl, fun n => ?_⟩
    have h := hrec n
    rw [hr0] at h
    have h1 : p.coeff 0 * m n = 0 := by simpa using h
    have hm : m n = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (by rwa [hr0] at hlead)
      · exact h2
    rw [hm]
    simp
  · set r := p.natDegree with hr
    set S := ∑ k ∈ Finset.range r, ‖p.coeff k / p.coeff r‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => norm_nonneg _
    set R := 1 + S with hRdef
    have hR1 : 1 ≤ R := by rw [hRdef]; linarith
    have hR0 : (0 : ℝ) < R := by linarith
    have hne : (Finset.range r).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
    set C := (Finset.range r).sup' hne fun k => ‖m k‖ with hC
    have hC0 : 0 ≤ C := by
      obtain ⟨k, hk⟩ := hne
      exact le_trans (norm_nonneg (m k)) (Finset.le_sup' (fun k => ‖m k‖) hk)
    refine ⟨C, R, hC0, hR1, fun n => ?_⟩
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < r
      · calc ‖m n‖ ≤ C := Finset.le_sup' (fun k => ‖m k‖) (Finset.mem_range.mpr hn)
          _ = C * 1 := (mul_one C).symm
          _ ≤ C * R ^ n := by
              refine mul_le_mul_of_nonneg_left ?_ hC0
              exact one_le_pow₀ hR1
      · have hjr : n - r + r = n := by omega
        have h := hrec (n - r)
        rw [Finset.sum_range_succ, hjr] at h
        have hSigma : ∑ k ∈ Finset.range r, p.coeff k * m (n - r + k)
            = -(p.coeff r * m n) := by linear_combination h
        have hm : m n = -∑ k ∈ Finset.range r, (p.coeff k / p.coeff r) * m (n - r + k) := by
          have hsum_div : ∑ k ∈ Finset.range r, (p.coeff k / p.coeff r) * m (n - r + k)
              = (∑ k ∈ Finset.range r, p.coeff k * m (n - r + k)) / p.coeff r := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hsum_div, hSigma, neg_div, neg_neg, mul_comm, mul_div_assoc, div_self hlead,
            mul_one]
        have hbound : ∀ k ∈ Finset.range r,
            ‖(p.coeff k / p.coeff r) * m (n - r + k)‖
              ≤ ‖p.coeff k / p.coeff r‖ * (C * R ^ (n - 1)) := by
          intro k hk
          have hkr : k < r := Finset.mem_range.mp hk
          have hlt : n - r + k < n := by omega
          have hmk : ‖m (n - r + k)‖ ≤ C * R ^ (n - r + k) := ih _ hlt
          have hpow : R ^ (n - r + k) ≤ R ^ (n - 1) :=
            pow_le_pow_right₀ hR1 (by omega)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact hmk.trans (mul_le_mul_of_nonneg_left hpow hC0)
        have hsum : ‖m n‖ ≤ S * (C * R ^ (n - 1)) := by
          rw [hm, norm_neg]
          calc ‖∑ k ∈ Finset.range r, (p.coeff k / p.coeff r) * m (n - r + k)‖
              ≤ ∑ k ∈ Finset.range r, ‖(p.coeff k / p.coeff r) * m (n - r + k)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range r, ‖p.coeff k / p.coeff r‖ * (C * R ^ (n - 1)) :=
                Finset.sum_le_sum hbound
            _ = S * (C * R ^ (n - 1)) := by rw [hS, Finset.sum_mul]
        have hstep : R ^ (n - 1) * R = R ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        have hfinal : S * (C * R ^ (n - 1)) ≤ C * R ^ n := by
          nlinarith [pow_nonneg hR0.le (n - 1), mul_nonneg hC0 (pow_nonneg hR0.le (n - 1))]
        exact hsum.trans hfinal

/-- The Taylor coefficients of a response sequence. -/
noncomputable def responseTaylorCoeff (m : ℕ → ℂ) (n : ℕ) : ℂ := m n / (n.factorial : ℂ)

/-- The entire function with prescribed response jets. -/
noncomputable def responseTaylorFun (m : ℕ → ℂ) : ℂ → ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)).sum

theorem radius_ofScalars_taylorCoeff_eq_top {m : ℕ → ℂ} {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hbound : ∀ n, ‖m n‖ ≤ C * R ^ n) :
    (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun ρ => ?_
  have hlim : Filter.Tendsto (fun n : ℕ => (R * (ρ : ℝ)) ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop (R * (ρ : ℝ))
  obtain ⟨D, hD⟩ := hlim.bddAbove_range
  refine FormalMultilinearSeries.le_radius_of_bound _ (C * D) fun n => ?_
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnorm : ‖FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m) n‖ = ‖responseTaylorCoeff m n‖ := by
    rw [FormalMultilinearSeries.ofScalars_norm]
  rw [hnorm, responseTaylorCoeff, norm_div, Complex.norm_natCast]
  have hDn : (R * (ρ : ℝ)) ^ n / (n.factorial : ℝ) ≤ D := hD ⟨n, rfl⟩
  have hρ : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  calc ‖m n‖ / (n.factorial : ℝ) * (ρ : ℝ) ^ n
      ≤ (C * R ^ n) / (n.factorial : ℝ) * (ρ : ℝ) ^ n := by
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hfac.le) (by positivity)
        exact hbound n
    _ = C * ((R * (ρ : ℝ)) ^ n / (n.factorial : ℝ)) := by
        rw [mul_pow]
        field_simp
    _ ≤ C * D := mul_le_mul_of_nonneg_left hDn hC

theorem hasFPowerSeriesOnBall_taylorFun {m : ℕ → ℂ}
    (h : (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)).radius = ⊤) :
    HasFPowerSeriesOnBall (responseTaylorFun m) (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)) 0 ⊤ :=
  h ▸ (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)).hasFPowerSeriesOnBall
    (by rw [h]; simp)

theorem differentiable_taylorFun {m : ℕ → ℂ}
    (h : (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)).radius = ⊤) :
    Differentiable ℂ (responseTaylorFun m) := by
  intro z
  have hball := hasFPowerSeriesOnBall_taylorFun h
  have hmem : z ∈ Metric.eball (0 : ℂ) ⊤ := by
    rw [Metric.mem_eball]
    exact edist_lt_top _ _
  exact (hball.analyticOnNhd z hmem).differentiableAt

theorem iteratedDeriv_taylorFun {m : ℕ → ℂ}
    (h : (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff m)).radius = ⊤) (n : ℕ) :
    iteratedDeriv n (responseTaylorFun m) 0 = m n := by
  have hball := hasFPowerSeriesOnBall_taylorFun h
  have hiter := hball.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => (1 : ℂ))
  have hfac : ((n.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hval : iteratedDeriv n (responseTaylorFun m) 0 = (n.factorial : ℂ) * responseTaylorCoeff m n := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hiter]
    simp [FormalMultilinearSeries.ofScalars, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [hval, responseTaylorCoeff, mul_div_cancel₀ _ hfac]

/-! ### Clause 4 — the exponential-polynomial form -/

/-- **Clause 4 of Theorem 2.1.**  Near the origin the germ is an exponential polynomial. -/
def GermExpPoly (f : ℂ → ℂ) : Prop :=
  ∃ G : ℂ → ℂ, G ∈ expPolySpaceC ∧ f =ᶠ[𝓝 (0 : ℂ)] G

theorem analyticAt_of_mem_expPolySpaceC {G : ℂ → ℂ} (hG : G ∈ expPolySpaceC) (z : ℂ) :
    AnalyticAt ℂ G z := by
  induction hG using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨q, rfl⟩ := hu
    exact analyticOnNhd_polyExpC q.1 q.2 z (Set.mem_univ z)
  | zero => exact analyticAt_const
  | add u v _ _ hu hv => exact hu.add hv
  | smul c u _ hu => exact analyticAt_const.mul hu

/-- An entire function vanishing on the real line vanishes identically. -/
theorem eq_zero_of_analytic_of_eqOn_real {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z)
    (h : ∀ x : ℝ, F (x : ℂ) = 0) (z : ℂ) : F z = 0 := by
  have hana : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF w
  have hbase : Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop
      (nhds (0 : ℂ)) := by
    have hreal : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    rw [Complex.ofReal_zero] at h2
    exact h2
  have htend : Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase ?_
    filter_upwards with n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity
  have hfreq : ∃ᶠ w in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, F w = 0 :=
    htend.frequently (Filter.Frequently.of_forall fun n => h _)
  exact hana.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq (Set.mem_univ z)

/-- Real jets of the restriction of an entire function are the complex jets. -/
theorem iteratedDeriv_restrictReal {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z) (k : ℕ) :
    iteratedDeriv k (restrictReal F) = restrictReal (iteratedDeriv k F) := by
  induction k with
  | zero => funext x; simp [iteratedDeriv_zero]
  | succ k ih =>
    funext x
    rw [iteratedDeriv_succ, ih]
    have hd : HasDerivAt (fun t : ℝ => (iteratedDeriv k F) (t : ℂ))
        (deriv (iteratedDeriv k F) (x : ℂ)) x :=
      HasDerivAt.comp_ofReal
        (analyticAt_iteratedDeriv (hF (x : ℂ)) k).differentiableAt.hasDerivAt
    have hfun : restrictReal (iteratedDeriv k F) = fun t : ℝ => (iteratedDeriv k F) (t : ℂ) := rfl
    rw [hfun, hd.deriv, restrictReal_apply, iteratedDeriv_succ]

/-- The entire jets of a germ agree with the jets of its Taylor extension near the origin. -/
theorem eventuallyEq_taylorFun {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h : (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff (respSeq f))).radius = ⊤) :
    f =ᶠ[𝓝 (0 : ℂ)] responseTaylorFun (respSeq f) := by
  have h1 : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)) 0 := hf.hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (responseTaylorFun (respSeq f))
      (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff (respSeq f))) 0 :=
    (hasFPowerSeriesOnBall_taylorFun h).hasFPowerSeriesAt
  have hcoeff : (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff (respSeq f)))
      = FormalMultilinearSeries.ofScalars ℂ fun n => iteratedDeriv n f 0 / (n.factorial : ℂ) := rfl
  rw [hcoeff] at h2
  have hsub := h1.sub h2
  rw [sub_self] at hsub
  filter_upwards [hsub.eventually_eq_zero] with z hz
  have : f z - responseTaylorFun (respSeq f) z = 0 := hz
  linear_combination this

/-- **Theorem 2.1, clause 3 implies clause 4.** -/
theorem germExpPoly_of_germConstantODE {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h : GermConstantODE f) : GermExpPoly f := by
  obtain ⟨p, hp, hode⟩ := h
  have hrec : SeqConstantRecurrence (respSeq f) :=
    (seqConstantRecurrence_respSeq_iff_germConstantODE hf).mpr ⟨p, hp, hode⟩
  obtain ⟨C, R, hC, hR, hbound⟩ := exists_geometric_bound_of_seqConstantRecurrence hrec
  have hrad := radius_ofScalars_taylorCoeff_eq_top hC hR hbound
  set F := responseTaylorFun (respSeq f) with hF
  have hFana : ∀ z, AnalyticAt ℂ F z := by
    intro z
    exact ((hasFPowerSeriesOnBall_taylorFun hrad).analyticOnNhd z (by
      rw [Metric.mem_eball]; exact edist_lt_top _ _))
  have hev : f =ᶠ[𝓝 (0 : ℂ)] F := eventuallyEq_taylorFun hf hrad
  -- the differential equation transports to the entire extension near the origin
  have hjets : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ k : ℕ, iteratedDeriv k f z = iteratedDeriv k F z := by
    filter_upwards [_root_.eventually_eventually_nhds.mpr hev] with z hz k
    exact EventuallyEq.iteratedDeriv_eq k hz
  have hzeroNear : ∀ᶠ z in 𝓝 (0 : ℂ), odeSum (fun k => p.coeff k) p.natDegree F z = 0 := by
    filter_upwards [hode, hjets] with z hz hjz
    rw [odeSum]
    rw [← hz]
    exact Finset.sum_congr rfl fun k _ => by rw [hjz k]
  have hodeAna : AnalyticOnNhd ℂ (odeSum (fun k => p.coeff k) p.natDegree F) Set.univ :=
    fun z _ => analyticAt_odeSum (hFana z) _ _
  have hzeroAll : ∀ z, odeSum (fun k => p.coeff k) p.natDegree F z = 0 := by
    intro z
    exact hodeAna.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ 0) hzeroNear (Set.mem_univ z)
  -- restrict to the real line and use the real annihilator theorem
  have hcontDiffC : ContDiff ℂ (⊤ : ℕ∞) F := by
    rw [contDiff_iff_contDiffAt]
    exact fun z => (hFana z).contDiffAt
  have hcontDiff : ContDiff ℝ (⊤ : ℕ∞) (restrictReal F) :=
    (hcontDiffC.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hopzero : realConstCoeffOp p (restrictReal F) = 0 := by
    funext x
    rw [realConstCoeffOp_eq_sum_range]
    have hx := hzeroAll (x : ℂ)
    rw [odeSum] at hx
    calc ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * iteratedDeriv i (restrictReal F) x
        = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * iteratedDeriv i F (x : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [iteratedDeriv_restrictReal hFana i, restrictReal_apply]
      _ = 0 := hx
  have hmem : restrictReal F ∈ expPolySpace :=
    mem_expPolySpace_of_realConstCoeffOp_eq_zero hcontDiff hp hopzero
  obtain ⟨G, hGmem, hGeq⟩ := exists_entire_extension hmem
  have hGana : ∀ z, AnalyticAt ℂ G z := analyticAt_of_mem_expPolySpaceC hGmem
  have hFG : ∀ z, F z = G z := by
    intro z
    have hdiff : ∀ z, AnalyticAt ℂ (fun w => F w - G w) z := fun z => (hFana z).sub (hGana z)
    have hzero := eq_zero_of_analytic_of_eqOn_real hdiff (fun x => by
      rw [hGeq x]
      exact sub_self _) z
    linear_combination hzero
  refine ⟨G, hGmem, ?_⟩
  filter_upwards [hev] with z hz
  rw [hz, hFG z]

/-- **Theorem 2.1, clause 4 implies clause 3.** -/
theorem germConstantODE_of_germExpPoly {f : ℂ → ℂ} (h : GermExpPoly f) : GermConstantODE f := by
  obtain ⟨G, hGmem, hev⟩ := h
  have hGana : ∀ z, AnalyticAt ℂ G z := analyticAt_of_mem_expPolySpaceC hGmem
  have hreal : restrictReal G ∈ expPolySpace := by
    rw [expPolySpace_eq_map]
    exact ⟨G, hGmem, rfl⟩
  obtain ⟨L, hL, hLzero⟩ := exists_nonzero_realConstCoeffOp_eq_zero_of_mem_expPolySpace hreal
  have hrealODE : ∀ x : ℝ, odeSum (fun k => L.coeff k) L.natDegree G (x : ℂ) = 0 := by
    intro x
    have hx := congrFun hLzero x
    simp only [Pi.zero_apply] at hx
    rw [realConstCoeffOp_eq_sum_range] at hx
    rw [odeSum, ← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedDeriv_restrictReal hGana i, restrictReal_apply]
  have hodeAna : ∀ z, AnalyticAt ℂ (odeSum (fun k => L.coeff k) L.natDegree G) z :=
    fun z => analyticAt_odeSum (hGana z) _ _
  have hzeroAll := eq_zero_of_analytic_of_eqOn_real hodeAna hrealODE
  refine ⟨L, hL, ?_⟩
  have hjets : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ k : ℕ, iteratedDeriv k f z = iteratedDeriv k G z := by
    filter_upwards [_root_.eventually_eventually_nhds.mpr hev] with z hz k
    exact EventuallyEq.iteratedDeriv_eq k hz
  filter_upwards [hjets] with z hz
  have hzz := hzeroAll z
  rw [odeSum] at hzz
  rw [← hzz]
  exact Finset.sum_congr rfl fun k _ => by rw [hz k]

/-- **Theorem 2.1.**  For an analytic germ at the origin the four memory readings coincide:
bounded Hankel rank, a constant-coefficient response recurrence, a constant-coefficient linear
differential equation, and the exponential-polynomial form. -/
theorem constant_memory_tfae {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    (BddHankelRank (respSeq f) ↔ SeqConstantRecurrence (respSeq f))
      ∧ (SeqConstantRecurrence (respSeq f) ↔ GermConstantODE f)
      ∧ (GermConstantODE f ↔ GermExpPoly f) :=
  ⟨(seqConstantRecurrence_iff_bddHankelRank (respSeq f)).symm,
    seqConstantRecurrence_respSeq_iff_germConstantODE hf,
    ⟨germExpPoly_of_germConstantODE hf, germConstantODE_of_germExpPoly⟩⟩

end GermMemory

end GaloisForLFunctions.HTGeometry
