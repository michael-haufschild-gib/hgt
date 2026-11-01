import GaloisForLFunctions.HTGeometry.HilbertBlockOperator
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.RHTower.NuclearRankOneTrace

/-!
# Abstract Hilbert-Space, Schatten-Class, and CLM Trace Identities

Reusable algebraic, self-adjointness, positivity, and Schatten-trace lemmas on generic complex
normed and Hilbert spaces (`[NormedAddCommGroup H] [InnerProductSpace ℂ H]`), isolated from concrete
`Submodule` aperture spaces so finite-sum CLM evaluations, rank-one trace rewrites, Krein
hyperbolic polarizations, and positive-trace carrier obstructions elaborate against canonical
typeclass instances:

1. **Typed CLM evaluation and finite-sum linearity:** `clm_zero_apply`, `clm_add_apply`,
   `clm_sub_apply`, `clm_neg_apply`, `clm_smul_apply`, `clm_one_apply`, `clm_sum_apply`,
   `inner_clm_sum_left`, `re_inner_clm_sum_left`, and `re_inner_clm_sum_eq_zero_of_forall`.
2. **Self-adjointness closure:** real scalar multiples (`isSelfAdjoint_ofReal_smul`), sums,
   differences, and arbitrary `Finset` sums (`isSelfAdjoint_sum`).
3. **Positivity and Schatten-1 / rank-one traces:** nonnegative real scaling
   (`isPositive_nonneg_smul`), operator sandwiches (`isPositive_adjoint_comp_comp`,
   `isPositive_comp_comp_adjoint`), trace monotonicity (`opTrace_re_nonneg_of_isPositive`),
   rank-one trace evaluation (`opTrace_comp_rankOne_self_of_isSelfAdjoint`), the rank-one trace
   characterization of `IsPositive` (`isPositive_iff_forall_opTrace_comp_rankOne_re_nonneg`), and
   the symmetric rank-one Krein split (`rankOne_symm_eq_two_smul_half`).
4. **Universal positive-trace carrier no-go:** any family of functionals `Q : ∀ a, D a → ℝ`
   admitting a single negative value `Q a₀ u₀ < 0` admits neither a positive operator-trace carrier
   (`no_positive_operator_trace_carrier_of_exists_neg`) nor a positive Gram-sandwich trace carrier
   (`no_positive_gram_trace_carrier_of_exists_neg`).
-/

noncomputable section

open Complex Filter Topology BigOperators
open scoped ENNReal InnerProductSpace
open _root_.RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.AbstractToolkit

section GenericNormedCLM

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F]

@[simp] theorem clm_zero_apply (x : E) : (0 : E →L[ℂ] F) x = 0 := rfl

@[simp] theorem clm_add_apply (A B : E →L[ℂ] F) (x : E) : (A + B) x = A x + B x := rfl

@[simp] theorem clm_sub_apply (A B : E →L[ℂ] F) (x : E) : (A - B) x = A x - B x := rfl

@[simp] theorem clm_neg_apply (A : E →L[ℂ] F) (x : E) : (-A) x = -A x := rfl

@[simp] theorem clm_smul_apply (c : ℂ) (A : E →L[ℂ] F) (x : E) : (c • A) x = c • A x := rfl

@[simp] theorem clm_one_apply (x : E) : (1 : E →L[ℂ] E) x = x := rfl

theorem clm_smul_zero (c : ℂ) : c • (0 : E →L[ℂ] F) = 0 := by
  ext x
  exact smul_zero c

theorem clm_smul_comp {G : Type*} [SeminormedAddCommGroup G] [NormedSpace ℂ G]
    (c : ℂ) (A : F →L[ℂ] G) (B : E →L[ℂ] F) : (c • A) ∘L B = c • (A ∘L B) := by
  ext x
  rfl

/-- Pointwise evaluation of a `Finset` sum of continuous linear maps without `Pi` unfolding. -/
theorem clm_sum_apply {ι : Type*} (s : Finset ι) (T : ι → (E →L[ℂ] F)) (x : E) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, clm_zero_apply]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, clm_add_apply, ih]

end GenericNormedCLM

section GenericInnerProduct

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem inner_clm_sum_left {ι : Type*} (s : Finset ι) (T : ι → (H →L[ℂ] H)) (x y : H) :
    inner ℂ ((∑ i ∈ s, T i) x) y = ∑ i ∈ s, inner ℂ (T i x) y := by
  rw [clm_sum_apply, sum_inner]

theorem re_inner_clm_sum_left {ι : Type*} (s : Finset ι) (T : ι → (H →L[ℂ] H)) (x y : H) :
    (inner ℂ ((∑ i ∈ s, T i) x) y).re = ∑ i ∈ s, (inner ℂ (T i x) y).re := by
  rw [inner_clm_sum_left, Complex.re_sum]

theorem re_inner_clm_sum_eq_zero_of_forall {ι : Type*} (s : Finset ι) (T : ι → (H →L[ℂ] H))
    (x y : H) (h : ∀ i ∈ s, (inner ℂ (T i x) y).re = 0) :
    (inner ℂ ((∑ i ∈ s, T i) x) y).re = 0 := by
  rw [re_inner_clm_sum_left]
  exact Finset.sum_eq_zero h

theorem rankOne_hasRankLE_one (x y : H) :
    HasRankLE (InnerProductSpace.rankOne ℂ x y) 1 := by
  simpa using hasRankLE_sum_range_rankOne (fun _ => x) (fun _ => y) 1

theorem comp_rankOne_eq_rankOne (T : H →L[ℂ] H) (u v : H) :
    T ∘L InnerProductSpace.rankOne ℂ u v = InnerProductSpace.rankOne ℂ (T u) v :=
  ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
      InnerProductSpace.rankOne_apply, map_smul]

/-- Symmetric rank-two operator `|u⟩⟨v| + |v⟩⟨u|` rewritten as the difference of two rank-one
operators along `½ (u + v)` and `½ (u - v)`. -/
theorem rankOne_symm_eq_two_smul_half (u v : H) :
    InnerProductSpace.rankOne ℂ u v + InnerProductSpace.rankOne ℂ v u =
      (2 : ℂ) • InnerProductSpace.rankOne ℂ (((1 / 2 : ℝ) : ℂ) • (u + v))
          (((1 / 2 : ℝ) : ℂ) • (u + v)) -
        (2 : ℂ) • InnerProductSpace.rankOne ℂ (((1 / 2 : ℝ) : ℂ) • (u - v))
          (((1 / 2 : ℝ) : ℂ) • (u - v)) := by
  refine ContinuousLinearMap.ext fun f => ext_inner_right ℂ fun g => ?_
  simp only [clm_add_apply, clm_sub_apply, clm_smul_apply,
    InnerProductSpace.rankOne_apply, inner_add_left, inner_sub_left, inner_smul_left,
    map_add, map_sub, map_mul, map_ofNat, Complex.conj_ofReal]
  push_cast
  ring

section Complete

variable [CompleteSpace H] [CompleteSpace K]

theorem isSelfAdjoint_ofReal_smul (r : ℝ) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint ((r : ℂ) • T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hT ⊢
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, Complex.conj_ofReal, hT]

theorem isSelfAdjoint_add {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A + B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hA hB ⊢
  rw [ContinuousLinearMap.adjoint.map_add, hA, hB]

theorem isSelfAdjoint_sub {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A - B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hA hB ⊢
  rw [ContinuousLinearMap.adjoint.map_sub, hA, hB]

/-- Finite sums of self-adjoint operators on a Hilbert space are self-adjoint. -/
theorem isSelfAdjoint_sum {ι : Type*} (s : Finset ι) (T : ι → (H →L[ℂ] H))
    (hT : ∀ i ∈ s, IsSelfAdjoint (T i)) :
    IsSelfAdjoint (∑ i ∈ s, T i) := by
  classical
  revert hT
  induction s using Finset.induction_on with
  | empty =>
      intro _
      rw [Finset.sum_empty, ContinuousLinearMap.isSelfAdjoint_iff', map_zero]
  | @insert i s hi ih =>
      intro hT
      rw [Finset.sum_insert hi]
      exact isSelfAdjoint_add (hT i (Finset.mem_insert_self i s))
        (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem isPositive_nonneg_smul {r : ℝ} (hr : 0 ≤ r) {T : H →L[ℂ] H}
    (hT : ContinuousLinearMap.IsPositive T) :
    ContinuousLinearMap.IsPositive ((r : ℂ) • T) := by
  have hsa : IsSelfAdjoint ((r : ℂ) • T) :=
    isSelfAdjoint_ofReal_smul r (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT.1)
  refine ⟨hsa.isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, clm_smul_apply, inner_smul_left, Complex.conj_ofReal]
  change 0 ≤ ((r : ℂ) * inner ℂ (T x) x).re
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg hr (hT.2 x)

theorem isPositive_adjoint_comp_comp {M : H →L[ℂ] H}
    (hM : ContinuousLinearMap.IsPositive M) (Θ : K →L[ℂ] H) :
    ContinuousLinearMap.IsPositive (ContinuousLinearMap.adjoint Θ ∘L M ∘L Θ) := by
  refine ⟨?_, fun x => ?_⟩
  · intro x y
    have hsym : ⟪M (Θ x), Θ y⟫_ℂ = ⟪Θ x, M (Θ y)⟫_ℂ := hM.1 (Θ x) (Θ y)
    change ⟪ContinuousLinearMap.adjoint Θ (M (Θ x)), y⟫_ℂ =
      ⟪x, ContinuousLinearMap.adjoint Θ (M (Θ y))⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left, hsym, ContinuousLinearMap.adjoint_inner_right]
  · rw [ContinuousLinearMap.reApplyInnerSelf]
    change 0 ≤ RCLike.re ⟪ContinuousLinearMap.adjoint Θ (M (Θ x)), x⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hM.2 (Θ x)

theorem isPositive_comp_comp_adjoint {M : H →L[ℂ] H}
    (hM : ContinuousLinearMap.IsPositive M) (Ψ : H →L[ℂ] K) :
    ContinuousLinearMap.IsPositive (Ψ ∘L M ∘L ContinuousLinearMap.adjoint Ψ) := by
  have heq : Ψ ∘L M ∘L ContinuousLinearMap.adjoint Ψ =
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint Ψ) ∘L M ∘L
        ContinuousLinearMap.adjoint Ψ := by
    rw [ContinuousLinearMap.adjoint_adjoint]
  rw [heq]
  exact isPositive_adjoint_comp_comp hM (ContinuousLinearMap.adjoint Ψ)

theorem opTrace_re_nonneg_of_isPositive {P : H →L[ℂ] H}
    (hP : ContinuousLinearMap.IsPositive P) :
    0 ≤ (ContinuousLinearMap.opTrace P).re := by
  unfold ContinuousLinearMap.opTrace
  set b := ContinuousLinearMap.hsBasis ℂ H
  by_cases hsum : Summable (fun i => inner ℂ (b i) (P (b i)))
  · rw [Complex.re_tsum hsum]
    refine tsum_nonneg fun i => ?_
    have h1 : 0 ≤ (⟪P (b i), b i⟫_ℂ).re := hP.2 (b i)
    have h2 : ⟪b i, P (b i)⟫_ℂ = starRingEnd ℂ ⟪P (b i), b i⟫_ℂ := (inner_conj_symm _ _).symm
    rw [h2, Complex.conj_re]
    exact h1
  · rw [tsum_eq_zero_of_not_summable hsum, Complex.zero_re]

theorem smul_rankOne_isTraceClass (c : ℂ) (x y : H) :
    ContinuousLinearMap.IsTraceClass (c • InnerProductSpace.rankOne ℂ x y) := by
  obtain ⟨V, hVfd, hVdim, hVmem⟩ := rankOne_hasRankLE_one x y
  have hrank : HasRankLE (c • InnerProductSpace.rankOne ℂ x y) 1 :=
    ⟨V, hVfd, hVdim, fun z => by rw [clm_smul_apply]; exact V.smul_mem c (hVmem z)⟩
  exact (memSchattenClass_of_hasRankLE one_pos hrank).one_isTraceClass

theorem comp_rankOne_isTraceClass (T : H →L[ℂ] H) (u v : H) :
    ContinuousLinearMap.IsTraceClass (T ∘L InnerProductSpace.rankOne ℂ u v) := by
  rw [comp_rankOne_eq_rankOne]
  exact (memSchattenClass_of_hasRankLE one_pos (rankOne_hasRankLE_one (T u) v)).one_isTraceClass

theorem opTrace_comp_rankOne_self_of_isSelfAdjoint {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) (u : H) :
    ContinuousLinearMap.opTrace (T ∘L InnerProductSpace.rankOne ℂ u u) = inner ℂ (T u) u := by
  rw [comp_rankOne_eq_rankOne, opTrace_rankOne]
  exact (hT.isSymmetric u u).symm

/-- A self-adjoint operator on a Hilbert space is `IsPositive` iff its composition with every
rank-one projection `|u⟩⟨u|` has nonnegative real operator trace. -/
theorem isPositive_iff_forall_opTrace_comp_rankOne_re_nonneg {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) :
    ContinuousLinearMap.IsPositive T ↔
      ∀ u : H, 0 ≤ (ContinuousLinearMap.opTrace (T ∘L InnerProductSpace.rankOne ℂ u u)).re := by
  constructor
  · intro hpos u
    rw [opTrace_comp_rankOne_self_of_isSelfAdjoint hT u]
    exact hpos.2 u
  · intro htr
    refine ⟨hT.isSymmetric, fun u => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf]
    change 0 ≤ (inner ℂ (T u) u).re
    rw [← opTrace_comp_rankOne_self_of_isSelfAdjoint hT u]
    exact htr u

/-- **Universal positive operator-trace carrier obstruction.**
If `Q a₀ u₀ < 0` for a single pair `(a₀, u₀)`, no family of positive operators `R(a, u)` on a
complex Hilbert space `H` can satisfy `(opTrace (R a u)).re = Q a u` across all `(a, u)`. -/
theorem no_positive_operator_trace_carrier_of_exists_neg {α : Type*} {D : α → Type*}
    {Q : ∀ a : α, D a → ℝ} (hneg : ∃ (a : α) (u : D a), Q a u < 0) :
    ¬ ∃ R : ∀ a : α, D a → (H →L[ℂ] H),
      (∀ a u, ContinuousLinearMap.IsPositive (R a u)) ∧
      (∀ a u, (ContinuousLinearMap.opTrace (R a u)).re = Q a u) := by
  rintro ⟨R, hpos, htr⟩
  obtain ⟨a, u, hlt⟩ := hneg
  have hge := opTrace_re_nonneg_of_isPositive (hpos a u)
  linarith only [hge, htr a u, hlt]

/-- **Universal positive Gram-sandwich trace carrier obstruction.**
If `Q a₀ u₀ < 0` for a single pair `(a₀, u₀)`, no positive operator `M ≥ 0` on `H` and bounded
intertwiner family `Ψ(a, u) : H →L[ℂ] K` can satisfy `(opTrace (Ψ(a, u) M Ψ(a, u)†)).re = Q a u`
across all `(a, u)`. -/
theorem no_positive_gram_trace_carrier_of_exists_neg {α : Type*} {D : α → Type*}
    {Q : ∀ a : α, D a → ℝ} (hneg : ∃ (a : α) (u : D a), Q a u < 0) :
    ¬ ∃ (M : H →L[ℂ] H) (Ψ : ∀ a : α, D a → (H →L[ℂ] K)),
      ContinuousLinearMap.IsPositive M ∧
      (∀ a u, (ContinuousLinearMap.opTrace
        (Ψ a u ∘L M ∘L ContinuousLinearMap.adjoint (Ψ a u))).re = Q a u) := by
  rintro ⟨M, Ψ, hM, htr⟩
  exact no_positive_operator_trace_carrier_of_exists_neg (H := K) hneg
    ⟨fun a u => Ψ a u ∘L M ∘L ContinuousLinearMap.adjoint (Ψ a u),
      fun a u => isPositive_comp_comp_adjoint hM (Ψ a u), htr⟩

end Complete

end GenericInnerProduct

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.AbstractToolkit

end
