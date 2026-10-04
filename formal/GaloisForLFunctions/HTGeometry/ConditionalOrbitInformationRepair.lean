import GaloisForLFunctions.HTGeometry.BoundedFredholmStability
import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionSchatten
import GaloisForLFunctions.HTGeometry.CompactAdjoint
import GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle

/-!
# Conditional-orbit information and essential-coupling no-cancellation

* **Correlated path formation.**  For path laws `P_n, Q_n` on `X₀ × ⋯ × X_{n-1}` with consistent
  marginals and regular conditional laws, the path divergence is the exact sum of the directed
  conditional innovations, `KL(P_n ‖ Q_n) = ∑_{i<n} k_i^P`, and Jeffreys work is
  `J(P_n, Q_n) = ∑_{i<n} (k_i^P + k_i^Q)`.  Correlation cannot cancel fresh information: lower
  bounds on the innovations add up, a uniform gap gives linear growth, a divergent gap series gives
  divergent work, and bounded work forces summable innovations.  A common recovery kernel leaves
  path divergence and Jeffreys work unchanged.
* **Essential operator coupling.**  A compact correction `R` leaves the Calkin class and the
  essential norm unchanged, preserves compactness, Fredholmness and the index; an induced essential
  defect `Ind_a(D)` keeps essential norm `limsup |aᵢ| ‖D‖`; a bounded repair making `A + R` compact
  must carry the opposite Calkin class and at least the original essential size; positive Gram
  completion does not hide a compact repair.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory InformationTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Correlated path formation -/

section PathInformation

universe u

variable (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]

/-- The path space `X₀ × ⋯ × X_{n-1}`, as an iterated product. -/
abbrev PathSpace : ℕ → Type u
  | 0 => PUnit
  | n + 1 => PathSpace n × X n

/-- The product σ-algebra on the path space. -/
@[reducible] def PathSpace.measurableSpace : (n : ℕ) → MeasurableSpace (PathSpace X n)
  | 0 => (inferInstance : MeasurableSpace PUnit)
  | n + 1 => @Prod.instMeasurableSpace (PathSpace X n) (X n) (PathSpace.measurableSpace n) _

instance PathSpace.instMeasurableSpace (n : ℕ) : MeasurableSpace (PathSpace X n) :=
  PathSpace.measurableSpace X n

variable {X}

/-- Finite paths of standard Borel coordinates form a standard Borel space. -/
instance PathSpace.instStandardBorelSpace [∀ i, StandardBorelSpace (X i)] (n : ℕ) :
    StandardBorelSpace (PathSpace X n) := by
  induction n with
  | zero => exact inferInstanceAs (StandardBorelSpace PUnit)
  | succ n ih => exact inferInstanceAs (StandardBorelSpace (PathSpace X n × X n))

/-- A **consistent path law**: the law of the first `n` coordinates is the first marginal of the
law of the first `n + 1`. -/
def IsConsistentPathLaw (P : ∀ n, Measure (PathSpace X n)) : Prop :=
  ∀ n, Measure.fst (α := PathSpace X n) (β := X n) (P (n + 1)) = P n

variable [∀ i, StandardBorelSpace (X i)] [∀ i, Nonempty (X i)]

/-- The regular conditional law of the `n`-th coordinate given the past. -/
def pathConditional (P : ∀ n, Measure (PathSpace X n)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    Kernel (PathSpace X n) (X n) :=
  Measure.condKernel (α := PathSpace X n) (Ω := X n) (P (n + 1))

instance (P : ∀ n, Measure (PathSpace X n)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    IsMarkovKernel (pathConditional P n) :=
  inferInstanceAs (IsMarkovKernel (Measure.condKernel (α := PathSpace X n) (Ω := X n) (P (n + 1))))

/-- The **directed conditional innovation** `k_n^P = ∫ KL(P_n(·|h) ‖ Q_n(·|h)) dP_{<n}(h)`, with
extended value `∞` allowed. -/
def pathInnovation (P Q : ∀ n, Measure (PathSpace X n)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ h, klDiv (pathConditional P n h) (pathConditional Q n h) ∂P n

/-- Jeffreys path work `J(P_n, Q_n) = KL(P_n ‖ Q_n) + KL(Q_n ‖ P_n)`. -/
def pathJeffreys (P Q : ∀ n, Measure (PathSpace X n)) (n : ℕ) : ℝ≥0∞ :=
  klDiv (P n) (Q n) + klDiv (Q n) (P n)

variable {P Q : ∀ n, Measure (PathSpace X n)}

omit [∀ i, StandardBorelSpace (X i)] [∀ i, Nonempty (X i)] in
/-- **Extended conditional chain term.**  The divergence of two composition products with a
common first marginal is the integral of the fibrewise divergences, with no absolute-continuity
hypothesis: off absolute continuity the fibre divergence is `∞` on a set of positive mass. -/
theorem klDiv_compProd_eq_lintegral {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    [MeasurableSpace.CountableOrCountablyGenerated α γ] (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η
  · exact klDiv_compProd_right μ κ η hac
  rw [klDiv_of_not_ac hac]
  rw [Measure.absolutelyContinuous_compProd_right_iff, ae_iff] at hac
  have hS : MeasurableSet {a | ¬ κ a ≪ η a} :=
    (Kernel.measurableSet_absolutelyContinuous κ η).compl
  refine (eq_top_iff.mpr ?_).symm
  calc (⊤ : ℝ≥0∞) = ∫⁻ a, {a | ¬ κ a ≪ η a}.indicator (fun _ => ⊤) a ∂μ := by
        rw [lintegral_indicator_const hS, ENNReal.top_mul hac]
    _ ≤ ∫⁻ a, klDiv (κ a) (η a) ∂μ := lintegral_mono fun a => by
        by_cases ha : a ∈ {a | ¬ κ a ≪ η a}
        · rw [Set.indicator_of_mem ha, klDiv_of_not_ac ha]
        · rw [Set.indicator_of_notMem ha]
          exact zero_le

/-- The innovation is the conditional divergence of the composition products. -/
theorem pathInnovation_eq_klDiv [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (n : ℕ) :
    pathInnovation P Q n = klDiv (P n ⊗ₘ pathConditional P n) (P n ⊗ₘ pathConditional Q n) :=
  (klDiv_compProd_eq_lintegral _ _ _).symm

theorem path_disintegrate [∀ n, IsProbabilityMeasure (P n)] (hP : IsConsistentPathLaw P) (n : ℕ) :
    P n ⊗ₘ pathConditional P n = P (n + 1) := by
  have h := Measure.disintegrate (α := PathSpace X n) (Ω := X n) (P (n + 1))
    (Measure.condKernel (α := PathSpace X n) (Ω := X n) (P (n + 1)))
  rw [hP n] at h
  exact h

omit [∀ i, StandardBorelSpace (X i)] [∀ i, Nonempty (X i)] in
/-- On the empty history all probability laws agree. -/
theorem pathLaw_zero_eq [IsProbabilityMeasure (P 0)] [IsProbabilityMeasure (Q 0)] : P 0 = Q 0 := by
  ext s -
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · rw [Subsingleton.eq_univ_of_nonempty h, measure_univ, measure_univ]

/-- **Theorem 1.1, `(COI.1)`.**  Exact conditional-orbit conservation:
`KL(P_n ‖ Q_n) = ∑_{i<n} k_i^P`. -/
theorem klDiv_path_eq_sum [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q) (n : ℕ) :
    klDiv (P n) (Q n) = ∑ k ∈ Finset.range n, pathInnovation P Q k := by
  induction n with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, pathLaw_zero_eq (P := P) (Q := Q)]
      exact klDiv_self _
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, ← path_disintegrate hP n, ← path_disintegrate hQ n,
        klDiv_compProd_eq_add, pathInnovation_eq_klDiv]

/-- **`(COI.2)`.**  Jeffreys path work is the sum of the two directed innovations. -/
theorem pathJeffreys_eq_sum [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q) (n : ℕ) :
    pathJeffreys P Q n =
      ∑ k ∈ Finset.range n, (pathInnovation P Q k + pathInnovation Q P k) := by
  rw [pathJeffreys, klDiv_path_eq_sum hP hQ, klDiv_path_eq_sum hQ hP, Finset.sum_add_distrib]


/-- **Corollary 1.2, `(COI.3)`.**  Correlation cannot cancel fresh information: lower bounds on the
conditional innovations add up. -/
theorem sum_le_pathJeffreys [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q) {c : ℕ → ℝ≥0∞}
    (hc : ∀ k, c k ≤ pathInnovation P Q k + pathInnovation Q P k) (n : ℕ) :
    ∑ k ∈ Finset.range n, c k ≤ pathJeffreys P Q n := by
  rw [pathJeffreys_eq_sum hP hQ]
  exact Finset.sum_le_sum fun k _ => hc k

/-- **Corollary 1.2 (1).**  A uniform conditional gap gives linear path work `J ≥ n c`. -/
theorem nsmul_le_pathJeffreys [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q)
    {c : ℝ≥0∞} (hc : ∀ k, c ≤ pathInnovation P Q k + pathInnovation Q P k) (n : ℕ) :
    (n : ℝ≥0∞) * c ≤ pathJeffreys P Q n := by
  have h := sum_le_pathJeffreys hP hQ (c := fun _ => c) hc n
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

/-- **Corollary 1.2 (2).**  A divergent gap series forces divergent cofinal path work. -/
theorem tendsto_pathJeffreys_top [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q)
    {c : ℕ → ℝ≥0∞} (hc : ∀ k, c k ≤ pathInnovation P Q k + pathInnovation Q P k)
    (hdiv : ∑' k, c k = ⊤) : Tendsto (pathJeffreys P Q) atTop (𝓝 ⊤) := by
  have hsum := ENNReal.tendsto_nat_tsum c
  rw [hdiv] at hsum
  exact tendsto_nhds_top_mono hsum (.of_forall fun n => sum_le_pathJeffreys hP hQ hc n)

/-- **Corollary 1.2 (3).**  Bounded cofinal path work forces summability of all actual conditional
innovations. -/
theorem tsum_innovation_le_of_pathJeffreys_le [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q)
    {B : ℝ≥0∞} (hB : ∀ n, pathJeffreys P Q n ≤ B) :
    ∑' k, (pathInnovation P Q k + pathInnovation Q P k) ≤ B := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← pathJeffreys_eq_sum hP hQ]
  exact hB n

/-- Finite cofinal path work makes the innovation series converge. -/
theorem tsum_innovation_ne_top_of_pathJeffreys_le [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q)
    {B : ℝ≥0∞} (hBfin : B ≠ ⊤) (hB : ∀ n, pathJeffreys P Q n ≤ B) :
    ∑' k, (pathInnovation P Q k + pathInnovation Q P k) ≠ ⊤ :=
  ne_top_of_le_ne_top hBfin (tsum_innovation_le_of_pathJeffreys_le hP hQ hB)

omit [∀ i, StandardBorelSpace (X i)] [∀ i, Nonempty (X i)] in
/-- **Theorem 2.1, `(COI.4)`.**  A common recovery kernel used identically on both correlated
histories is an isometry for path divergence and Jeffreys work. -/
theorem commonRecovery_pathDivergence {Y : Type*} [MeasurableSpace Y] (n : ℕ)
    [IsFiniteMeasure (P n)] [IsFiniteMeasure (Q n)] (M : Kernel (PathSpace X n) Y)
    [IsMarkovKernel M] :
    klDiv (P n ⊗ₘ M) (Q n ⊗ₘ M) = klDiv (P n) (Q n) ∧
      klDiv (P n ⊗ₘ M) (Q n ⊗ₘ M) + klDiv (Q n ⊗ₘ M) (P n ⊗ₘ M) = pathJeffreys P Q n :=
  ⟨klDiv_compProd_left _ _ _, by rw [klDiv_compProd_left, klDiv_compProd_left]; rfl⟩

end PathInformation

/-! ### The Calkin class and essential norm -/

section Calkin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The Calkin quotient `B(E, F) / K(E, F)` of bounded operators modulo compact operators. -/
abbrev CalkinQuotient (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Type _ :=
  (E →L[ℂ] F) ⧸ compactOperator (RingHom.id ℂ) E F

/-- The Calkin class `q(A)` of a bounded operator. -/
def calkinClass (A : E →L[ℂ] F) : CalkinQuotient E F :=
  Submodule.Quotient.mk A

theorem calkinClass_eq_iff {A B : E →L[ℂ] F} :
    calkinClass A = calkinClass B ↔ IsCompactOperator (A - B) :=
  Submodule.Quotient.eq _

theorem calkinClass_eq_zero_iff {A : E →L[ℂ] F} : calkinClass A = 0 ↔ IsCompactOperator A :=
  Submodule.Quotient.mk_eq_zero _

theorem calkinClass_neg (A : E →L[ℂ] F) : calkinClass (-A) = -calkinClass A :=
  Submodule.Quotient.mk_neg _

theorem calkinClass_add (A B : E →L[ℂ] F) : calkinClass (A + B) = calkinClass A + calkinClass B :=
  Submodule.Quotient.mk_add _

/-- The Calkin norm is the essential norm `‖A‖_ess = inf_{C compact} ‖A - C‖`. -/
theorem norm_calkinClass (A : E →L[ℂ] F) : ‖calkinClass A‖ = rectEssentialNorm A := by
  have hnorm : ‖calkinClass A‖ =
      Metric.infDist A (compactOperator (RingHom.id ℂ) E F : Set (E →L[ℂ] F)) :=
    QuotientAddGroup.norm_mk (S := (compactOperator (RingHom.id ℂ) E F).toAddSubgroup) A
  have hne : (compactOperator (RingHom.id ℂ) E F : Set (E →L[ℂ] F)).Nonempty :=
    ⟨0, isCompactOperator_zero⟩
  rw [hnorm]
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_)
    (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_)
  · obtain ⟨C, hC, hlt⟩ := exists_isCompactOperator_norm_sub_lt hr
    exact ((Metric.infDist_le_dist_of_mem (x := A) hC).trans (by rw [dist_eq_norm])).trans hlt.le
  · obtain ⟨C, hC, hlt⟩ := (Metric.infDist_lt_iff hne).mp hr
    rw [dist_eq_norm] at hlt
    exact (rectEssentialNorm_le A C hC).trans hlt.le

/-- **Theorem 3.1, `(COI.5)`.**  A compact correction leaves the Calkin class unchanged. -/
theorem calkinClass_add_compact {A R : E →L[ℂ] F} (hR : IsCompactOperator R) :
    calkinClass (A + R) = calkinClass A := by
  rw [calkinClass_eq_iff, add_sub_cancel_left]
  exact hR

/-- **`(COI.5)`.**  A compact correction leaves the essential norm unchanged. -/
theorem rectEssentialNorm_add_compact {A R : E →L[ℂ] F} (hR : IsCompactOperator R) :
    rectEssentialNorm (A + R) = rectEssentialNorm A := by
  rw [← norm_calkinClass, ← norm_calkinClass, calkinClass_add_compact hR]

/-- **Theorem 3.1 (1).**  `A + R` is compact exactly when `A` is. -/
theorem isCompactOperator_add_compact_iff {A R : E →L[ℂ] F} (hR : IsCompactOperator R) :
    IsCompactOperator (A + R) ↔ IsCompactOperator A := by
  refine ⟨fun h => ?_, fun h => h.add hR⟩
  have := h.sub hR
  rwa [show ((A + R : E →L[ℂ] F) : E → F) - R = A by
    funext x
    simp] at this

/-- **`(COI.7)`.**  A bounded repair making `A + R` compact carries the opposite Calkin class and
exactly the essential size of `A`. -/
theorem calkinClass_repair {A R : E →L[ℂ] F} (h : IsCompactOperator (A + R)) :
    calkinClass R = -calkinClass A ∧ rectEssentialNorm R = rectEssentialNorm A := by
  have hq : calkinClass R = -calkinClass A := by
    have h1 : calkinClass (A + R) = 0 := calkinClass_eq_zero_iff.mpr h
    rw [calkinClass_add] at h1
    exact eq_neg_of_add_eq_zero_right h1
  refine ⟨hq, ?_⟩
  rw [← norm_calkinClass, ← norm_calkinClass, hq]
  exact norm_neg (calkinClass A)

/-- **`(COI.7)`, norm form.**  A repair has at least the original essential size. -/
theorem rectEssentialNorm_le_of_repair {A R : E →L[ℂ] F} (h : IsCompactOperator (A + R)) :
    rectEssentialNorm A ≤ rectEssentialNorm R :=
  (calkinClass_repair h).2.ge

end Calkin

/-! ### Fredholm stability under compact correction -/

section Fredholm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- Hilbert and quotient cokernels agree: the orthogonal-complement definition of a bounded
Fredholm operator coincides with the quotient-cokernel definition. -/
theorem isBoundedFredholm_iff_isFredholmOp (T : E →L[ℂ] F) :
    IsBoundedFredholm T ↔ IsFredholmOp T := by
  have hrange : (LinearMap.range (T : E →ₗ[ℂ] F) : Set F) = Set.range T := rfl
  constructor
  · rintro ⟨⟨hcl, hker⟩, -, hcoker⟩
    have hcl' : IsClosed (LinearMap.range (T : E →ₗ[ℂ] F) : Set F) := hrange ▸ hcl
    haveI : CompleteSpace (LinearMap.range (T : E →ₗ[ℂ] F)) := hcl'.completeSpace_coe
    exact ⟨hker, hcl', (Submodule.quotientEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal _)).symm.finiteDimensional⟩
  · intro hT
    haveI := hT.hasOrthogonalProjection_range
    haveI := hT.finiteDimensional_orthogonal_range
    have hcl : IsClosed (Set.range T) := hrange ▸ hT.isClosed_range
    exact ⟨⟨hcl, hT.finiteDimensional_ker⟩, hcl, inferInstance⟩

/-- **Theorem 3.1 `(COI.5)`, items 1–3.**  Compact global repair is impossible: a compact
correction preserves the Calkin class, the essential norm, compactness, Fredholmness and the
index. -/
theorem compactRepair_invariants {A R : E →L[ℂ] F} (hR : IsCompactOperator R) :
    calkinClass (A + R) = calkinClass A ∧ rectEssentialNorm (A + R) = rectEssentialNorm A ∧
      (IsCompactOperator (A + R) ↔ IsCompactOperator A) ∧
      (IsFredholmOp (A + R) ↔ IsFredholmOp A) ∧
      (IsFredholmOp A → fredholmIndex (A + R) = fredholmIndex A) :=
  ⟨calkinClass_add_compact hR, rectEssentialNorm_add_compact hR,
    isCompactOperator_add_compact_iff hR, isFredholmOp_add_compact_iff hR,
    fun hA => fredholmIndex_add_compact hA hR⟩

omit [CompleteSpace E] in
/-- Norm limits of finite-rank operators are compact. -/
theorem isCompactOperator_of_tendsto_finiteRank {G : ℕ → E →L[ℂ] F} {R : E →L[ℂ] F}
    (hG : ∀ n, FiniteDimensional ℂ (LinearMap.range (G n : E →ₗ[ℂ] F)))
    (hlim : Tendsto G atTop (𝓝 R)) : IsCompactOperator R :=
  isCompactOperator_of_tendsto hlim (.of_forall fun n =>
    isCompactOperator_of_finiteDimensional_range (hG n))

/-- **Corollary 3.2, scope.**  Finite-rank, trace-class and Schatten-class couplings are compact,
so every conclusion about compact corrections applies to them. -/
theorem compactRepair_invariants_of_memRectSchattenClass {p : ℝ} (hp : 0 < p) {A R : E →L[ℂ] F}
    (hR : RHTower.MemRectSchattenClass p R) :
    calkinClass (A + R) = calkinClass A ∧ rectEssentialNorm (A + R) = rectEssentialNorm A ∧
      (IsCompactOperator (A + R) ↔ IsCompactOperator A) ∧
      (IsFredholmOp (A + R) ↔ IsFredholmOp A) ∧
      (IsFredholmOp A → fredholmIndex (A + R) = fredholmIndex A) :=
  compactRepair_invariants (isCompactOperator_of_memRectSchattenClass hp hR)

/-! ### Positive completion -/

/-- **`(COI.8)`.**  The Gram difference of a corrected operator. -/
theorem gram_add_sub_gram (A R : E →L[ℂ] F) :
    ContinuousLinearMap.adjoint (A + R) ∘L (A + R) - ContinuousLinearMap.adjoint A ∘L A =
      ContinuousLinearMap.adjoint A ∘L R + ContinuousLinearMap.adjoint R ∘L A +
        ContinuousLinearMap.adjoint R ∘L R := by
  have hadj : ContinuousLinearMap.adjoint (A + R) =
      ContinuousLinearMap.adjoint A + ContinuousLinearMap.adjoint R :=
    map_add (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)) A R
  rw [hadj, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.add_comp]
  abel

/-- **`(COI.9)`.**  Positive Gram completion does not see a compact correction: the Gram classes
agree in the Calkin quotient and have equal essential norms. -/
theorem calkinClass_gram_add_compact {A R : E →L[ℂ] F} (hR : IsCompactOperator R) :
    calkinClass (ContinuousLinearMap.adjoint (A + R) ∘L (A + R)) =
        calkinClass (ContinuousLinearMap.adjoint A ∘L A) ∧
      rectEssentialNorm (ContinuousLinearMap.adjoint (A + R) ∘L (A + R)) =
        rectEssentialNorm (ContinuousLinearMap.adjoint A ∘L A) := by
  have hRadj : IsCompactOperator (ContinuousLinearMap.adjoint R) :=
    isCompactOperator_adjoint_rectangular R hR
  have hdiff : IsCompactOperator (ContinuousLinearMap.adjoint (A + R) ∘L (A + R) -
      ContinuousLinearMap.adjoint A ∘L A) := by
    rw [gram_add_sub_gram]
    exact ((hR.clm_comp (ContinuousLinearMap.adjoint A)).add (hRadj.comp_clm A)).add
      (hR.clm_comp (ContinuousLinearMap.adjoint R))
  have hq := calkinClass_eq_iff.mpr hdiff
  exact ⟨hq, by rw [← norm_calkinClass, ← norm_calkinClass, hq]⟩

end Fredholm

/-! ### Induced essential defects -/

section Induced

variable {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Corollary 3.2, `(COI.6)`.**  No compact cross-orbit coupling alters the essential norm
`limsup |aᵢ| ‖D‖` of an induced defect with compact nonzero local block, and none makes it
compact. -/
theorem weightedInduction_add_compact_essential (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (hDne : D ≠ 0)
    (hα : 0 < tailSup a) {R : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2}
    (hR : IsCompactOperator R) :
    rectEssentialNorm (weightedInduction a D U V hbdd + R) = tailSup a * ‖D‖ ∧
      0 < tailSup a * ‖D‖ ∧ ¬ IsCompactOperator (weightedInduction a D U V hbdd + R) := by
  have hpos : 0 < tailSup a * ‖D‖ := mul_pos hα (norm_pos_iff.mpr hDne)
  have hess : rectEssentialNorm (weightedInduction a D U V hbdd + R) = tailSup a * ‖D‖ := by
    rw [rectEssentialNorm_add_compact hR, rectEssentialNorm_weightedInduction a D U V hbdd hD]
  refine ⟨hess, hpos, fun hc => ?_⟩
  have h0 := rectEssentialNorm_eq_zero_of_isCompactOperator hc
  rw [hess] at h0
  exact hpos.ne' h0

omit [DecidableEq I] in
/-- **Corollary 3.2.**  No compact cross-orbit coupling repairs a non-Fredholm induced formation. -/
theorem not_isBoundedFredholm_weightedInduction_add_compact (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hA : ¬ IsBoundedFredholm (weightedInduction a D U V hbdd))
    {R : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2} (hR : IsCompactOperator R) :
    ¬ IsBoundedFredholm (weightedInduction a D U V hbdd + R) := by
  rw [isBoundedFredholm_iff_isFredholmOp] at hA ⊢
  rwa [isFredholmOp_add_compact_iff hR]

/-- **`(COI.7)` for induced defects.**  Any bounded repair making an induced defect compact has
Calkin class `-q(Ind_a D)` and essential norm `limsup |aᵢ| ‖D‖ > 0`; in particular it is not
compact. -/
theorem weightedInduction_repair (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (hDne : D ≠ 0)
    (hα : 0 < tailSup a) {R : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2}
    (h : IsCompactOperator (weightedInduction a D U V hbdd + R)) :
    calkinClass R = -calkinClass (weightedInduction a D U V hbdd) ∧
      rectEssentialNorm R = tailSup a * ‖D‖ ∧ ¬ IsCompactOperator R := by
  obtain ⟨hq, hn⟩ := calkinClass_repair h
  rw [rectEssentialNorm_weightedInduction a D U V hbdd hD] at hn
  refine ⟨hq, hn, fun hc => ?_⟩
  have := (weightedInduction_add_compact_essential a D U V hbdd hD hDne hα hc).2.2
  exact this h

/-- Amplitudes of constant modulus `c` have tail supremum `c` over an infinite orbit. -/
theorem tailSup_eq_of_norm_eq [Infinite I] {a : I → ℂ} {c : ℝ}
    (hc : ∀ i, ‖a i‖ = c) : tailSup a = c := by
  have hamp : ∀ F : Finset I, ampSup (tailAmp F a) = c := by
    intro F
    have hle : ∀ i, ‖tailAmp F a i‖ ≤ c := by
      intro i
      by_cases hi : i ∈ F
      · simp only [tailAmp, hi, if_true, norm_zero]
        rw [← hc i]
        exact norm_nonneg _
      · simp only [tailAmp, hi, if_false, hc i, le_refl]
    obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset F
    refine le_antisymm (ciSup_le hle) ?_
    have : ‖tailAmp F a j‖ = c := by simp only [tailAmp, hj, if_false, hc j]
    rw [← this]
    exact le_ciSup ⟨c, by rintro _ ⟨i, rfl⟩; exact hle i⟩ j
  rw [tailSup]
  simp only [hamp, ciInf_const]

/-- **`(COI.10)`.**  For amplitudes of constant modulus `c` over an infinite orbit and a compact
local block, the positive Gram completion has Calkin norm `c² ‖D‖²`; for a homogeneous induction
(`|aᵢ| = 1`) it is `‖D‖²`. -/
theorem norm_calkinClass_gram_weightedInduction [Infinite I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) {c : ℝ}
    (hc : ∀ i, ‖a i‖ = c) :
    ‖calkinClass (ContinuousLinearMap.adjoint (weightedInduction a D U V hbdd) ∘L
        weightedInduction a D U V hbdd)‖ = c ^ 2 * ‖D‖ ^ 2 := by
  rw [norm_calkinClass, gram_weightedInduction,
    rectEssentialNorm_weightedInduction _ _ _ _ _ (hD.clm_comp (ContinuousLinearMap.adjoint D)),
    ContinuousLinearMap.norm_adjoint_comp_self,
    tailSup_eq_of_norm_eq (c := c ^ 2) fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hc i]]
  ring

theorem norm_calkinClass_gram_weightedInduction_homogeneous [Infinite I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D)
    (hc : ∀ i, ‖a i‖ = 1) :
    ‖calkinClass (ContinuousLinearMap.adjoint (weightedInduction a D U V hbdd) ∘L
        weightedInduction a D U V hbdd)‖ = ‖D‖ ^ 2 := by
  rw [norm_calkinClass_gram_weightedInduction a D U V hbdd hD hc, one_pow, one_mul]

end Induced

/-! ### Joint no-cancellation theorem -/

section Joint

variable {X : ℕ → Type} [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)]
  [∀ i, Nonempty (X i)] {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Theorem 5.1, `(COI.11)`.**  For one source orbit carried by correlated path pairs with
divergent conditional innovations, a common recovery kernel on every finite history, an induced
defect `Ind_a(D)` with compact nonzero local block and `limsup |aᵢ| > 0`, and a compact cross-orbit
correction `R`: the recovered Jeffreys work diverges and `‖Ind_a(D) + R‖_ess = limsup |aᵢ| ‖D‖ > 0`.
-/
theorem conditionalOrbit_essentialCoupling_noCancellation
    {P Q : ∀ n, Measure (PathSpace X n)} [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hP : IsConsistentPathLaw P) (hQ : IsConsistentPathLaw Q)
    (M : ∀ n, Kernel (PathSpace X n) (Y n)) [∀ n, IsMarkovKernel (M n)]
    (hinfo : ∑' k, (pathInnovation P Q k + pathInnovation Q P k) = ⊤)
    (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (hDne : D ≠ 0)
    (hα : 0 < tailSup a) {R : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2}
    (hR : IsCompactOperator R) :
    Tendsto (fun n => klDiv (P n ⊗ₘ M n) (Q n ⊗ₘ M n) + klDiv (Q n ⊗ₘ M n) (P n ⊗ₘ M n))
        atTop (𝓝 ⊤) ∧
      rectEssentialNorm (weightedInduction a D U V hbdd + R) = tailSup a * ‖D‖ ∧
      0 < tailSup a * ‖D‖ := by
  refine ⟨?_, (weightedInduction_add_compact_essential a D U V hbdd hD hDne hα hR).1,
    (weightedInduction_add_compact_essential a D U V hbdd hD hDne hα hR).2.1⟩
  have hJ := tendsto_pathJeffreys_top hP hQ (c := fun k => pathInnovation P Q k +
    pathInnovation Q P k) (fun _ => le_rfl) hinfo
  refine hJ.congr fun n => ?_
  exact ((commonRecovery_pathDivergence (P := P) (Q := Q) n (M n)).2).symm

end Joint

end GaloisForLFunctions.HTGeometry
