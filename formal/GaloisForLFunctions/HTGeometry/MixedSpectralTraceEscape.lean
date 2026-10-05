import GaloisForLFunctions.HTGeometry.MixedSpectralFormation
import GaloisForLFunctions.HTGeometry.AtomlessPhaseFormation
import GaloisForLFunctions.HTGeometry.HaarRankEntropyFormation
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass

/-!
# Mixed spectral formation: atomic retention and continuous trace escape

For a positive trace-class `T` define the atomic and continuous masses
`m_at(T) = tr(T P_at)` and `m_c(T) = tr(T P_c)`; they are nonnegative and add to `tr T`.

* **`(MSF.1)` in trace norm.**  The block sums `∑_{λ ∈ s} P_λ T P_λ` converge to `Π_at(T)` in
  trace norm; the remainder is the positive tail `(1 - Q_s) Π_at(T) (1 - Q_s)`.
* **Theorem 4.1.**  `Π_at(T)` is positive trace class with `tr Π_at(T) = m_at(T)`, while
  `tr M_N(T) = tr T`; hence `tr(M_N(T) - Π_at(T)) = m_c(T)`.
* **Corollary 4.2.**  `‖M_N(T) - Π_at(T)‖₁ ≥ m_c(T)` for every `N ≥ 1`.
* **Theorem 5.1.**  `M_N(T) → Π_at(T)` in trace norm exactly when `m_c(T) = 0`.  If `m_c(T) = 0`
  then `T = P_at T P_at`; truncating to finitely many eigenvalues costs an arbitrarily small trace
  norm (by Hölder `‖AB‖₁ ≤ ‖A‖₂‖B‖₂` against the square root of `T`), and on finitely many
  eigenvalue blocks the off-diagonal blocks are multiplied by Cesàro averages of nontrivial phases.
* **Corollary 5.2.**  `m_c(T) = tr T - tr Π_at(T)`.
-/

open Filter Topology Set
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Trace-class bookkeeping -/

section TraceClass

theorem traceNorm_add_le' {S T : H →L[ℂ] H} (hS : RHTower.MemSchattenClass 1 S)
    (hT : RHTower.MemSchattenClass 1 T) :
    RHTower.traceNorm H (S + T) ≤ RHTower.traceNorm H S + RHTower.traceNorm H T :=
  RHTower.traceNorm_add_le (hS.isCompactOperator one_pos) (hT.isCompactOperator one_pos)
    hS.one_summable_approxNumber hT.one_summable_approxNumber

theorem memSchattenClass_one_add' {S T : H →L[ℂ] H} (hS : RHTower.MemSchattenClass 1 S)
    (hT : RHTower.MemSchattenClass 1 T) : RHTower.MemSchattenClass 1 (S + T) :=
  RHTower.memSchattenClass_one_add (hS.isCompactOperator one_pos) (hT.isCompactOperator one_pos)
    hS hT

theorem memSchattenClass_one_sub' {S T : H →L[ℂ] H} (hS : RHTower.MemSchattenClass 1 S)
    (hT : RHTower.MemSchattenClass 1 T) : RHTower.MemSchattenClass 1 (S - T) := by
  rw [sub_eq_add_neg, show -T = (-1 : ℂ) • T by simp]
  exact memSchattenClass_one_add' hS (RHTower.memSchattenClass_one_smul hT _)

theorem traceNorm_sub_le' {S T : H →L[ℂ] H} (hS : RHTower.MemSchattenClass 1 S)
    (hT : RHTower.MemSchattenClass 1 T) :
    RHTower.traceNorm H (S - T) ≤ RHTower.traceNorm H S + RHTower.traceNorm H T := by
  rw [sub_eq_add_neg, show -T = (-1 : ℂ) • T by simp]
  refine (traceNorm_add_le' hS (RHTower.memSchattenClass_one_smul hT _)).trans ?_
  rw [RHTower.traceNorm_smul]
  simp

theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) {T : ι → H →L[ℂ] H}
    (hT : ∀ i ∈ s, RHTower.MemSchattenClass 1 (T i)) :
    RHTower.traceNorm H (∑ i ∈ s, T i) ≤ ∑ i ∈ s, RHTower.traceNorm H (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [RHTower.traceNorm_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine (traceNorm_add_le' (hT i (Finset.mem_insert_self i s))
        (memSchattenClass_one_sum s T fun j hj => hT j (Finset.mem_insert_of_mem hj))).trans ?_
      gcongr
      exact ih fun j hj => hT j (Finset.mem_insert_of_mem hj)

/-- **Hölder.**  `‖B A‖₁ ≤ ‖A‖₂ ‖B‖₂`. -/
theorem traceNorm_comp_le_hsNorm {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) :
    RHTower.traceNorm H (B ∘L A) ≤ A.hsNorm * B.hsNorm :=
  RHTower.rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hA hB

theorem memSchattenClass_one_comp_hs {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : RHTower.MemSchattenClass 1 (B ∘L A) :=
  RHTower.IsTraceClass.memSchattenClass_one ⟨B, A, hB, hA, rfl⟩

/-- Unitary conjugation preserves the trace norm. -/
theorem traceNorm_hsConj (U : H ≃ₗᵢ[ℂ] H) (X : H →L[ℂ] H) :
    RHTower.traceNorm H (hsConj U X) = RHTower.traceNorm H X := by
  have hV : ContinuousLinearMap.adjoint (unitaryCLM U.symm) ∘L unitaryCLM U.symm =
      ContinuousLinearMap.id ℂ H := by
    rw [adjoint_unitaryCLM, LinearIsometryEquiv.symm_symm]
    ext x
    simp
  rw [hsConj_eq_conj_adjoint]
  exact traceNorm_isometric_conj hV X

theorem hsConj_iterate_properties' (U : H ≃ₗᵢ[ℂ] H) {X : H →L[ℂ] H}
    (hX : RHTower.MemSchattenClass 1 X) (n : ℕ) :
    RHTower.MemSchattenClass 1 ((hsConj U)^[n] X) ∧
      RHTower.traceNorm H ((hsConj U)^[n] X) = RHTower.traceNorm H X ∧
      opTrace ((hsConj U)^[n] X) = opTrace X := by
  induction n with
  | zero => exact ⟨hX, rfl, rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨memSchattenClass_one_hsConj U ih.1, (traceNorm_hsConj U _).trans ih.2.1,
        (opTrace_hsConj U ih.1).trans ih.2.2⟩

theorem memSchattenClass_one_hsCesaro (U : H ≃ₗᵢ[ℂ] H) {X : H →L[ℂ] H}
    (hX : RHTower.MemSchattenClass 1 X) (N : ℕ) :
    RHTower.MemSchattenClass 1 (hsCesaro U N X) :=
  RHTower.memSchattenClass_one_smul (memSchattenClass_one_sum _ _ fun n _ =>
    (hsConj_iterate_properties' U hX n).1) _

/-- The Cesàro formation is a trace-norm contraction. -/
theorem traceNorm_hsCesaro_le (U : H ≃ₗᵢ[ℂ] H) {X : H →L[ℂ] H}
    (hX : RHTower.MemSchattenClass 1 X) (N : ℕ) :
    RHTower.traceNorm H (hsCesaro U N X) ≤ RHTower.traceNorm H X := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hsCesaro, RHTower.traceNorm_zero, RHTower.traceNorm_nonneg]
  rw [hsCesaro, RHTower.traceNorm_smul]
  have hsum := traceNorm_sum_le (Finset.range N) fun n _ => (hsConj_iterate_properties' U hX n).1
  simp only [fun n => (hsConj_iterate_properties' U hX n).2.1, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  rw [norm_inv, Complex.norm_natCast]
  calc ((N : ℝ))⁻¹ * RHTower.traceNorm H (∑ n ∈ Finset.range N, (hsConj U)^[n] X)
      ≤ (N : ℝ)⁻¹ * (N * RHTower.traceNorm H X) := by gcongr
    _ = RHTower.traceNorm H X := by field_simp

/-- **`(MSF.6)`.**  The Cesàro formation preserves the trace. -/
theorem opTrace_hsCesaro (U : H ≃ₗᵢ[ℂ] H) {X : H →L[ℂ] H} (hX : RHTower.MemSchattenClass 1 X)
    {N : ℕ} (hN : 1 ≤ N) : opTrace (hsCesaro U N X) = opTrace X := by
  have hsum : ∀ M, opTrace (∑ n ∈ Finset.range M, (hsConj U)^[n] X) = M * opTrace X := by
    intro M
    induction M with
    | zero => simp [opTrace]
    | succ M ih =>
        rw [Finset.sum_range_succ, RHTower.opTrace_add_of_memSchattenClass_one
          (memSchattenClass_one_sum _ _ fun n _ => (hsConj_iterate_properties' U hX n).1)
          (hsConj_iterate_properties' U hX M).1, ih, (hsConj_iterate_properties' U hX M).2.2]
        push_cast
        ring
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [hsCesaro, RHTower.opTrace_smul, hsum, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]

end TraceClass

/-! ### Positivity is closed under Hilbert–Schmidt limits -/

theorem isPositive_of_tendsto_hsNorm {ι : Type*} {l : Filter ι} [l.NeBot] {A : H →L[ℂ] H}
    {S : ι → H →L[ℂ] H} (hHS : ∀ i, IsHilbertSchmidt (A - S i))
    (hlim : Tendsto (fun i => (A - S i).hsNorm) l (𝓝 0)) (hpos : ∀ i, (S i).IsPositive) :
    A.IsPositive := by
  have hop : Tendsto (fun i => ‖A - S i‖) l (𝓝 0) :=
    squeeze_zero (fun i => norm_nonneg _) (fun i => opNorm_le_hsNorm (hHS i)) hlim
  have hS : Tendsto S l (𝓝 A) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hop
  rw [isPositive_def]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h1 : Tendsto (fun i => ⟪S i x, y⟫_ℂ) l (𝓝 ⟪A x, y⟫_ℂ) :=
      ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto A |>.comp hS).inner tendsto_const_nhds
    have h2 : Tendsto (fun i => ⟪x, S i y⟫_ℂ) l (𝓝 ⟪x, A y⟫_ℂ) :=
      tendsto_const_nhds.inner ((ContinuousLinearMap.apply ℂ H y).continuous.tendsto A |>.comp hS)
    have heq : ∀ i, ⟪S i x, y⟫_ℂ = ⟪x, S i y⟫_ℂ := fun i => ((hpos i).isSymmetric) x y
    exact tendsto_nhds_unique (h1.congr heq) h2
  · have h1 : Tendsto (fun i => (S i).reApplyInnerSelf x) l (𝓝 (A.reApplyInnerSelf x)) := by
      simp only [reApplyInnerSelf_apply]
      exact (Complex.continuous_re.tendsto _).comp
        (((ContinuousLinearMap.apply ℂ H x).continuous.tendsto A |>.comp hS).inner
          tendsto_const_nhds)
    exact ge_of_tendsto' h1 fun i => (isPositive_def.mp (hpos i)).2 x

/-! ### Masses -/

section Masses

variable {U : H ≃ₗᵢ[ℂ] H}

/-- The atomic projection `P_at`. -/
abbrev atomproj (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := (atomicSubspace U).starProjection

theorem atomproj_adaptedVec_inl (d : ℂ) (k : eigenBasisIndex U d) :
    atomproj U (adaptedVec U (Sum.inl ⟨d, k⟩)) = adaptedVec U (Sum.inl ⟨d, k⟩) :=
  Submodule.starProjection_eq_self_iff.mpr (unitaryEigenspace_le_atomic d (adaptedVec_inl_mem d k))

theorem atomproj_adaptedVec_inr (k : continuousBasisIndex U) :
    atomproj U (adaptedVec U (Sum.inr k)) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr (adaptedVec_inr_mem k)

theorem atomproj_add_contproj : atomproj U + contproj U = 1 := by
  ext x
  exact Submodule.starProjection_add_starProjection_orthogonal x

/-- The trace of a trace-class operator on the adapted basis. -/
theorem opTrace_eq_tsum_adapted {X : H →L[ℂ] H} (hX : RHTower.MemSchattenClass 1 X) :
    opTrace X = ∑' i, ⟪adaptedVec U i, X (adaptedVec U i)⟫_ℂ := by
  rw [RHTower.opTrace_eq_tsum_basis_of_memSchattenClass_one hX (adaptedBasis U)]
  simp only [adaptedBasis_apply]

/-- The atomic diagonal: `⟨e, T e⟩` on eigenvectors and `0` on `H_c`. -/
def atomicDiag (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (i : AdaptedIndex U) : ℂ :=
  if i.isLeft then ⟪adaptedVec U i, T (adaptedVec U i)⟫_ℂ else 0

/-- The continuous diagonal. -/
def continuousDiag (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (i : AdaptedIndex U) : ℂ :=
  if i.isLeft then 0 else ⟪adaptedVec U i, T (adaptedVec U i)⟫_ℂ

/-- **`(MSF.5)`.**  The atomic mass `m_at(T) = tr(T P_at)`. -/
def atomicMass (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) : ℂ := opTrace (T ∘L atomproj U)

/-- **`(MSF.5)`.**  The continuous mass `m_c(T) = tr(T P_c)`. -/
def continuousMass (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) : ℂ := opTrace (T ∘L contproj U)

theorem atomicMass_eq_tsum {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    atomicMass U T = ∑' i, atomicDiag U T i := by
  rw [atomicMass, opTrace_eq_tsum_adapted (RHTower.memSchattenClass_one_comp_right hT _)]
  refine tsum_congr fun i => ?_
  rcases i with ⟨d, k⟩ | k
  · simp [atomicDiag, atomproj_adaptedVec_inl]
  · simp [atomicDiag, atomproj_adaptedVec_inr]

theorem continuousMass_eq_tsum {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    continuousMass U T = ∑' i, continuousDiag U T i := by
  rw [continuousMass, opTrace_eq_tsum_adapted (RHTower.memSchattenClass_one_comp_right hT _)]
  refine tsum_congr fun i => ?_
  rcases i with ⟨d, k⟩ | k
  · simp [continuousDiag, contproj_adaptedVec_inl]
  · simp [continuousDiag, contproj_adaptedVec_inr]

/-- **`(MSF.5)`.**  The masses add up to the trace. -/
theorem atomicMass_add_continuousMass {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    atomicMass U T + continuousMass U T = opTrace T := by
  rw [atomicMass, continuousMass, ← RHTower.opTrace_add_of_memSchattenClass_one
    (RHTower.memSchattenClass_one_comp_right hT _) (RHTower.memSchattenClass_one_comp_right hT _),
    ← ContinuousLinearMap.comp_add, atomproj_add_contproj]
  rfl

theorem atomicDiag_nonneg {T : H →L[ℂ] H} (hpos : T.IsPositive) (i : AdaptedIndex U) :
    0 ≤ atomicDiag U T i := by
  unfold atomicDiag
  split_ifs
  · exact hpos.inner_nonneg_right _
  · exact le_rfl

theorem continuousDiag_nonneg {T : H →L[ℂ] H} (hpos : T.IsPositive) (i : AdaptedIndex U) :
    0 ≤ continuousDiag U T i := by
  unfold continuousDiag
  split_ifs
  · exact le_rfl
  · exact hpos.inner_nonneg_right _

/-- **`(MSF.5)`.**  For positive `T` both masses are nonnegative. -/
theorem atomicMass_nonneg {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) : 0 ≤ atomicMass U T := by
  rw [atomicMass_eq_tsum hT]
  exact tsum_nonneg (atomicDiag_nonneg hpos)

theorem continuousMass_nonneg {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) : 0 ≤ continuousMass U T := by
  rw [continuousMass_eq_tsum hT]
  exact tsum_nonneg (continuousDiag_nonneg hpos)

end Masses

/-! ### Atomic retention -/

section Retention

variable {U : H ≃ₗᵢ[ℂ] H}

theorem isSelfAdjoint_eigenproj (c : ℂ) : IsSelfAdjoint (eigenproj U c) :=
  isSelfAdjoint_iff_isSymmetric.mpr (Submodule.starProjection_isSymmetric _)

theorem isPositive_eigenproj_conj {T : H →L[ℂ] H} (hpos : T.IsPositive) (c : ℂ) :
    (eigenproj U c ∘L T ∘L eigenproj U c).IsPositive := by
  have h := hpos.conj_adjoint (eigenproj U c)
  rwa [(isSelfAdjoint_eigenproj c).adjoint_eq] at h

theorem isHilbertSchmidt_blockSum {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (s : Finset ℂ) :
    IsHilbertSchmidt (∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHilbertSchmidt_zero
  | insert c s hcs ih =>
      rw [Finset.sum_insert hcs]
      exact ((hT.comp_right _).comp_left _).add ih

theorem isPositive_blockSum {T : H →L[ℂ] H} (hpos : T.IsPositive) (s : Finset ℂ) :
    (∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c).IsPositive := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isPositive_zero]
  | insert c s hcs ih =>
      rw [Finset.sum_insert hcs]
      exact (isPositive_eigenproj_conj hpos c).add ih

/-- **Theorem 4.1.**  The atomic pinching of a positive operator is positive. -/
theorem isPositive_atomicPinch {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (hpos : T.IsPositive) :
    (atomicPinch U hT).IsPositive :=
  isPositive_of_tendsto_hsNorm (l := atTop)
    (fun s => (isHilbertSchmidt_atomicPinch hT).sub (isHilbertSchmidt_blockSum hT s))
    (tendsto_hsNorm_atomicPinch_sub_sum hT) (isPositive_blockSum hpos)

theorem inner_atomicPinch_adaptedVec {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (i : AdaptedIndex U) :
    ⟪adaptedVec U i, atomicPinch U hT (adaptedVec U i)⟫_ℂ = atomicDiag U T i := by
  rw [atomicPinch_apply]
  rcases i with ⟨d, k⟩ | k
  · simp only [atomicPinchCol, atomicDiag, Sum.isLeft_inl, if_true]
    calc ⟪adaptedVec U (Sum.inl ⟨d, k⟩), eigenproj U d (T (adaptedVec U (Sum.inl ⟨d, k⟩)))⟫_ℂ
        = ⟪eigenproj U d (adaptedVec U (Sum.inl ⟨d, k⟩)), T (adaptedVec U (Sum.inl ⟨d, k⟩))⟫_ℂ :=
          (Submodule.starProjection_isSymmetric _ _ _).symm
      _ = _ := by rw [eigenproj_adaptedVec_inl, if_pos rfl]
  · simp [atomicPinchCol, atomicDiag]

theorem summable_atomicDiag {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    Summable (atomicDiag U T) := by
  have h := (hT.one_summable_inner_diag_basis (adaptedBasis U)).indicator {i | i.isLeft = true}
  refine h.congr fun i => ?_
  simp only [Set.indicator, Set.mem_setOf_eq, atomicDiag, adaptedBasis_apply]

/-- **Theorem 4.1, `(MSF.6)`.**  The atomic pinching of a positive trace-class operator is
positive trace class and retains exactly the atomic mass: `tr Π_at(T) = m_at(T)`. -/
theorem atomicPinch_traceClass {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) :
    (atomicPinch U hT.one_isHilbertSchmidt).IsPositive ∧
      RHTower.MemSchattenClass 1 (atomicPinch U hT.one_isHilbertSchmidt) ∧
      opTrace (atomicPinch U hT.one_isHilbertSchmidt) = atomicMass U T := by
  have hP := isPositive_atomicPinch (U := U) hT.one_isHilbertSchmidt hpos
  have hsum : Summable fun i => ⟪adaptedBasis U i,
      atomicPinch U hT.one_isHilbertSchmidt (adaptedBasis U i)⟫_ℂ := by
    simp only [adaptedBasis_apply, inner_atomicPinch_adaptedVec]
    exact summable_atomicDiag hT
  have hmem := RHTower.memSchattenClass_one_of_isPositive_of_summable_diagonal _ hP hsum
  refine ⟨hP, hmem, ?_⟩
  rw [opTrace_eq_tsum_adapted hmem, atomicMass_eq_tsum hT]
  exact tsum_congr fun i => inner_atomicPinch_adaptedVec _ i

/-- **`(MSF.7)`.**  `tr(M_N(T) - Π_at(T)) = m_c(T)`. -/
theorem opTrace_hsCesaro_sub_atomicPinch {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) {N : ℕ} (hN : 1 ≤ N) :
    opTrace (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt) = continuousMass U T := by
  obtain ⟨-, hmem, htr⟩ := atomicPinch_traceClass (U := U) hT hpos
  rw [RHTower.opTrace_sub_of_memSchattenClass_one (memSchattenClass_one_hsCesaro U hT N) hmem,
    opTrace_hsCesaro U hT hN, htr, ← atomicMass_add_continuousMass (U := U) hT]
  ring

/-- **Corollary 4.2, `(MSF.8)`.**  The continuous mass bounds the trace-norm mismatch from below:
`‖M_N(T) - Π_at(T)‖₁ ≥ m_c(T)`. -/
theorem norm_continuousMass_le_traceNorm {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) {N : ℕ} (hN : 1 ≤ N) :
    ‖continuousMass U T‖ ≤
      RHTower.traceNorm H (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt) := by
  obtain ⟨-, hmem, -⟩ := atomicPinch_traceClass (U := U) hT hpos
  rw [← opTrace_hsCesaro_sub_atomicPinch hT hpos hN]
  exact RHTower.norm_opTrace_le_traceNorm (memSchattenClass_one_sub'
    (memSchattenClass_one_hsCesaro U hT N) hmem)

/-- **Corollary 5.2, `(MSF.10)`.**  `m_c(T) = tr T - tr Π_at(T)`. -/
theorem continuousMass_eq_sub {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) :
    continuousMass U T = opTrace T - opTrace (atomicPinch U hT.one_isHilbertSchmidt) := by
  rw [(atomicPinch_traceClass (U := U) hT hpos).2.2, ← atomicMass_add_continuousMass (U := U) hT]
  ring

/-- **Theorem 5.1, necessity.**  Trace-norm convergence of the formation forces zero continuous
mass. -/
theorem continuousMass_eq_zero_of_tendsto {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive)
    (hlim : Tendsto (fun N => RHTower.traceNorm H
      (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt)) atTop (𝓝 0)) :
    continuousMass U T = 0 := by
  have hb : ∀ᶠ N in atTop, ‖continuousMass U T‖ ≤
      RHTower.traceNorm H (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt) :=
    eventually_atTop.mpr ⟨1, fun N hN => norm_continuousMass_le_traceNorm hT hpos hN⟩
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hb)

end Retention

/-! ### Finite eigenvalue apertures -/

section Aperture

variable {U : H ≃ₗᵢ[ℂ] H}

/-- The projection onto the eigenspaces of a finite set `s` of eigenvalues. -/
def apertureProj (U : H ≃ₗᵢ[ℂ] H) (s : Finset ℂ) : H →L[ℂ] H := ∑ c ∈ s, eigenproj U c

theorem apertureProj_adaptedVec_inl (s : Finset ℂ) (d : ℂ) (k : eigenBasisIndex U d) :
    apertureProj U s (adaptedVec U (Sum.inl ⟨d, k⟩)) =
      if d ∈ s then adaptedVec U (Sum.inl ⟨d, k⟩) else 0 := by
  rw [apertureProj, sum_apply]
  simp_rw [eigenproj_adaptedVec_inl]
  exact Finset.sum_ite_eq s d _

theorem apertureProj_adaptedVec_inr (s : Finset ℂ) (k : continuousBasisIndex U) :
    apertureProj U s (adaptedVec U (Sum.inr k)) = 0 := by
  rw [apertureProj, sum_apply]
  simp [eigenproj_adaptedVec_inr]

theorem isSelfAdjoint_apertureProj (s : Finset ℂ) : IsSelfAdjoint (apertureProj U s) := by
  classical
  rw [apertureProj]
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hcs ih =>
      rw [Finset.sum_insert hcs]
      exact (isSelfAdjoint_eigenproj c).add ih

theorem eigenproj_apertureProj (c : ℂ) (s : Finset ℂ) (y : H) :
    eigenproj U c (apertureProj U s y) = if c ∈ s then eigenproj U c y else 0 := by
  rw [apertureProj, sum_apply, map_sum]
  have : ∀ d ∈ s, eigenproj U c (eigenproj U d y) = if d = c then eigenproj U c y else 0 := by
    intro d _
    split_ifs with h
    · subst h
      exact eigenproj_idem d y
    · exact eigenproj_eigenproj_of_ne h y
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']

theorem apertureProj_eigenproj (c : ℂ) (s : Finset ℂ) (y : H) :
    apertureProj U s (eigenproj U c y) = if c ∈ s then eigenproj U c y else 0 := by
  rw [apertureProj, sum_apply]
  have : ∀ d ∈ s, eigenproj U d (eigenproj U c y) = if c = d then eigenproj U c y else 0 := by
    intro d _
    split_ifs with h
    · subst h
      exact eigenproj_idem c y
    · exact eigenproj_eigenproj_of_ne h y
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

/-- Conjugation acts on the block `P_λ X P_μ` by the phase ratio `λ̄ μ`. -/
theorem hsConj_block (c d : ℂ) (X : H →L[ℂ] H) :
    hsConj U (eigenproj U c ∘L X ∘L eigenproj U d) =
      ((starRingEnd ℂ) c * d) • (eigenproj U c ∘L X ∘L eigenproj U d) := by
  have hcomm : ∀ x, eigenproj U d (U x) = U (eigenproj U d x) := by
    intro x
    have h := commute_eigenprojection (T := unitaryCLM U) (fun y => rfl) d
    exact (congrArg (fun L : H →L[ℂ] H => L x) h).symm
  ext x
  simp only [hsConj_apply, ContinuousLinearMap.comp_apply, smul_apply, hcomm]
  by_cases hx : eigenproj U d x = 0
  · simp [hx]
  have hd : ‖d‖ = 1 :=
    norm_eq_one_of_mem_unitaryEigenspace (Submodule.starProjection_apply_mem _ x) hx
  rw [mem_unitaryEigenspace.mp (Submodule.starProjection_apply_mem _ x), map_smul, map_smul]
  set y := eigenproj U c (X (eigenproj U d x))
  by_cases hy : y = 0
  · simp [hy]
  have hc : ‖c‖ = 1 :=
    norm_eq_one_of_mem_unitaryEigenspace (Submodule.starProjection_apply_mem _ _) hy
  rw [map_smul, unitary_symm_apply_of_mem (Submodule.starProjection_apply_mem _ _) hc, smul_smul,
    mul_comm]

theorem hsCesaro_block (c d : ℂ) (X : H →L[ℂ] H) (N : ℕ) :
    hsCesaro U N (eigenproj U c ∘L X ∘L eigenproj U d) =
      cesaroCoeff ((starRingEnd ℂ) c * d) N • (eigenproj U c ∘L X ∘L eigenproj U d) := by
  have hiter : ∀ n, (hsConj U)^[n] (eigenproj U c ∘L X ∘L eigenproj U d) =
      ((starRingEnd ℂ) c * d) ^ n • (eigenproj U c ∘L X ∘L eigenproj U d) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hsConj_smul, hsConj_block, smul_smul, pow_succ]
  rw [hsCesaro, cesaroCoeff, mul_smul, Finset.sum_congr rfl fun n _ => hiter n,
    ← Finset.sum_smul]

omit [CompleteSpace H] in
theorem hsCesaro_zero (U : H ≃ₗᵢ[ℂ] H) (N : ℕ) : hsCesaro U N (0 : H →L[ℂ] H) = 0 := by
  have hiter : ∀ n, (hsConj U)^[n] (0 : H →L[ℂ] H) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        ext x
        simp
  simp [hsCesaro, hiter]

omit [CompleteSpace H] in
theorem hsCesaro_add (U : H ≃ₗᵢ[ℂ] H) (N : ℕ) (A B : H →L[ℂ] H) :
    hsCesaro U N (A + B) = hsCesaro U N A + hsCesaro U N B := by
  have hiter : ∀ n, (hsConj U)^[n] (A + B) = (hsConj U)^[n] A + (hsConj U)^[n] B := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hsConj_add,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
  rw [hsCesaro, hsCesaro, hsCesaro, Finset.sum_congr rfl fun n _ => hiter n,
    Finset.sum_add_distrib, smul_add]

omit [CompleteSpace H] in
theorem hsCesaro_sum (U : H ≃ₗᵢ[ℂ] H) (N : ℕ) {ι : Type*} (t : Finset ι) (A : ι → H →L[ℂ] H) :
    hsCesaro U N (∑ i ∈ t, A i) = ∑ i ∈ t, hsCesaro U N (A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hsCesaro_zero]
  | insert i t hit ih => rw [Finset.sum_insert hit, Finset.sum_insert hit, hsCesaro_add, ih]

end Aperture

/-! ### Sufficiency: zero continuous mass gives trace-norm convergence -/

section Sufficiency

variable {U : H ≃ₗᵢ[ℂ] H} {T : H →L[ℂ] H}

theorem sqrtOp_comp_self (hpos : T.IsPositive) :
    RHTower.traceClassRoot T ∘L RHTower.traceClassRoot T = T := by
  rw [RHTower.traceClassRoot_comp_self,
    ContinuousLinearMap.absOp_of_nonneg ((nonneg_iff_isPositive T).mpr hpos)]

theorem isSymmetric_traceClassRoot (T : H →L[ℂ] H) :
    (RHTower.traceClassRoot T : H →ₗ[ℂ] H).IsSymmetric :=
  isSelfAdjoint_iff_isSymmetric.mp (RHTower.isSelfAdjoint_traceClassRoot T)

/-- `⟨x, T x⟩ = ‖T^{1/2} x‖²`. -/
theorem inner_eq_norm_sqrtOp_sq (hpos : T.IsPositive) (x : H) :
    ⟪x, T x⟫_ℂ = ((‖RHTower.traceClassRoot T x‖ ^ 2 : ℝ) : ℂ) := by
  conv_lhs => rw [← sqrtOp_comp_self hpos]
  calc ⟪x, (RHTower.traceClassRoot T ∘L RHTower.traceClassRoot T) x⟫_ℂ
      = ⟪RHTower.traceClassRoot T x, RHTower.traceClassRoot T x⟫_ℂ :=
        (isSymmetric_traceClassRoot T x (RHTower.traceClassRoot T x)).symm
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

theorem summable_continuousDiag (hT : RHTower.MemSchattenClass 1 T) :
    Summable (continuousDiag U T) := by
  have h := (hT.one_summable_inner_diag_basis (adaptedBasis U)).indicator {i | i.isLeft = false}
  refine h.congr fun i => ?_
  rcases i with j | k <;> simp [Set.indicator, continuousDiag, adaptedBasis_apply]

/-- Zero continuous mass kills `T^{1/2}` on `H_c`. -/
theorem sqrtOp_adaptedVec_inr (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (hmc : continuousMass U T = 0) (k : continuousBasisIndex U) :
    RHTower.traceClassRoot T (adaptedVec U (Sum.inr k)) = 0 := by
  have hsum := (summable_continuousDiag (U := U) hT).hasSum
  rw [← continuousMass_eq_tsum hT, hmc] at hsum
  have h0 := (hasSum_zero_iff_of_nonneg (continuousDiag_nonneg hpos)).mp hsum
  have hk := congrFun h0 (Sum.inr k)
  simp only [continuousDiag, Sum.isLeft_inr, Bool.false_eq_true, if_false, Pi.zero_apply,
    inner_eq_norm_sqrtOp_sq hpos] at hk
  have hsq : ‖RHTower.traceClassRoot T (adaptedVec U (Sum.inr k))‖ ^ 2 = 0 := by exact_mod_cast hk
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

theorem one_sub_apertureProj_adaptedVec (s : Finset ℂ) (i : AdaptedIndex U) :
    (1 - apertureProj U s) (adaptedVec U i) =
      if adaptedLabel i ∈ s ∧ i.isLeft then 0 else adaptedVec U i := by
  rcases i with ⟨d, k⟩ | k
  · rw [sub_apply, one_apply_eq_self, apertureProj_adaptedVec_inl]
    simp only [adaptedLabel, Sum.isLeft_inl, and_true]
    split_ifs <;> simp
  · rw [sub_apply, one_apply_eq_self, apertureProj_adaptedVec_inr]
    simp

/-- The truncation tail `‖T^{1/2}(1 - Q_s)‖₂²` written on the adapted basis. -/
theorem hsNormSq_sqrtOp_tail (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (hmc : continuousMass U T = 0) (s : Finset ℂ) :
    hsNormSq (RHTower.traceClassRoot T ∘L (1 - apertureProj U s)) =
      ∑' i, Set.indicator {i | adaptedLabel i ∉ s}
        (fun i => ‖RHTower.traceClassRoot T (adaptedVec U i)‖ ^ 2) i := by
  have hR := RHTower.traceClassRoot_isHilbertSchmidt hT
  rw [hsNormSq_eq (hR.comp_right _) (adaptedBasis U)]
  refine tsum_congr fun i => ?_
  rw [adaptedBasis_apply, ContinuousLinearMap.comp_apply, one_sub_apertureProj_adaptedVec]
  rcases i with ⟨d, k⟩ | k
  · simp only [adaptedLabel, Sum.isLeft_inl, and_true, Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  · simp [Set.indicator, sqrtOp_adaptedVec_inr hT hpos hmc k]

/-- The truncation tail tends to zero along finite eigenvalue apertures. -/
theorem tendsto_hsNormSq_sqrtOp_tail (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (hmc : continuousMass U T = 0) :
    Tendsto (fun s => hsNormSq (RHTower.traceClassRoot T ∘L (1 - apertureProj U s))) atTop
      (𝓝 0) := by
  classical
  set g : AdaptedIndex U → ℝ := fun i => ‖RHTower.traceClassRoot T (adaptedVec U i)‖ ^ 2
  have hg : Summable g := by
    have h := (RHTower.traceClassRoot_isHilbertSchmidt hT).summable (adaptedBasis U)
    simpa only [adaptedBasis_apply] using h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp (tendsto_tsum_compl_atTop_zero g)) ε hε
  refine ⟨J.image adaptedLabel, fun s hs => ?_⟩
  have htail := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at htail
  have hnn : 0 ≤ ∑' i : {x // x ∉ J}, g i := tsum_nonneg fun _ => sq_nonneg _
  rw [abs_of_nonneg hnn] at htail
  have hle : hsNormSq (RHTower.traceClassRoot T ∘L (1 - apertureProj U s)) ≤
      ∑' i : {x // x ∉ J}, g i := by
    rw [hsNormSq_sqrtOp_tail hT hpos hmc s]
    have hsub : (∑' i : {x // x ∉ J}, g i) = ∑' i, Set.indicator {x | x ∉ J} g i :=
      tsum_subtype ({x | x ∉ J} : Set (AdaptedIndex U)) g
    rw [hsub]
    refine Summable.tsum_le_tsum (fun i => ?_) (hg.indicator _) (hg.indicator _)
    by_cases hi : i ∈ J
    · have : adaptedLabel i ∈ s := hs (Finset.mem_image_of_mem _ hi)
      simp [Set.indicator, this, hi]
    · simp only [Set.indicator, Set.mem_setOf_eq, hi, not_false_eq_true, if_true]
      split_ifs
      · exact sq_nonneg ‖RHTower.traceClassRoot T (adaptedVec U i)‖
      · exact le_of_eq rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNormSq_nonneg _)]
  exact lt_of_le_of_lt hle htail

theorem isSelfAdjoint_one_sub_apertureProj (s : Finset ℂ) :
    IsSelfAdjoint (1 - apertureProj U s) :=
  (IsSelfAdjoint.one (H →L[ℂ] H)).sub (isSelfAdjoint_apertureProj s)

theorem hsNorm_comp_eq_adjoint {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAB : IsHilbertSchmidt (A ∘L B)) : (A ∘L B).hsNorm = (B ∘L A).hsNorm := by
  have h := hAB.hsNormSq_adjoint
  rw [ContinuousLinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq] at h
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm, h]

/-- `‖T^{1/2} Q_s‖₂ ≤ ‖T^{1/2}‖₂`: the aperture projection acts diagonally on the adapted basis. -/
theorem hsNorm_sqrtOp_apertureProj_le (hT : RHTower.MemSchattenClass 1 T) (s : Finset ℂ) :
    (RHTower.traceClassRoot T ∘L apertureProj U s).hsNorm ≤ (RHTower.traceClassRoot T).hsNorm := by
  have hR := RHTower.traceClassRoot_isHilbertSchmidt hT
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm]
  refine Real.sqrt_le_sqrt ?_
  rw [hsNormSq_eq (hR.comp_right _) (adaptedBasis U), hsNormSq_eq hR (adaptedBasis U)]
  refine Summable.tsum_le_tsum (fun i => ?_) ((hR.comp_right _).summable _) (hR.summable _)
  rw [adaptedBasis_apply, ContinuousLinearMap.comp_apply]
  rcases i with ⟨d, k⟩ | k
  · rw [apertureProj_adaptedVec_inl]
    split_ifs <;> simp
  · rw [apertureProj_adaptedVec_inr]
    simp

/-- **Truncation estimate.**  `‖T - Q_s T Q_s‖₁ ≤ 2 ‖T^{1/2}‖₂ ‖T^{1/2}(1 - Q_s)‖₂`. -/
theorem traceNorm_sub_aperture_le (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (s : Finset ℂ) :
    RHTower.traceNorm H (T - apertureProj U s ∘L T ∘L apertureProj U s) ≤
      2 * (RHTower.traceClassRoot T).hsNorm *
        (RHTower.traceClassRoot T ∘L (1 - apertureProj U s)).hsNorm := by
  set R := RHTower.traceClassRoot T
  set Q := apertureProj U s
  have hR : IsHilbertSchmidt R := RHTower.traceClassRoot_isHilbertSchmidt hT
  have hRsa : IsSelfAdjoint R := RHTower.isSelfAdjoint_traceClassRoot T
  have hId : T - Q ∘L T ∘L Q = ((1 - Q) ∘L R) ∘L R + (Q ∘L R) ∘L (R ∘L (1 - Q)) := by
    have hRR : R ∘L R = T := sqrtOp_comp_self hpos
    ext x
    have h1 : ((1 - Q) ∘L R) ∘L R = (1 - Q) ∘L T := by
      rw [ContinuousLinearMap.comp_assoc, hRR]
    have h2 : (Q ∘L R) ∘L (R ∘L (1 - Q)) = Q ∘L T ∘L (1 - Q) := by
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc R R, hRR]
    rw [h1, h2]
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self, map_sub]
    abel
  have hA1 : IsHilbertSchmidt ((1 - Q) ∘L R) := hR.comp_left _
  have hA2 : IsHilbertSchmidt (Q ∘L R) := hR.comp_left _
  have hA3 : IsHilbertSchmidt (R ∘L (1 - Q)) := hR.comp_right _
  have ht1 : ((1 - Q) ∘L R).hsNorm = (R ∘L (1 - Q)).hsNorm :=
    hsNorm_comp_eq_adjoint (isSelfAdjoint_one_sub_apertureProj s) hRsa hA1
  have ht2 : (Q ∘L R).hsNorm ≤ R.hsNorm := by
    rw [hsNorm_comp_eq_adjoint (isSelfAdjoint_apertureProj s) hRsa hA2]
    exact hsNorm_sqrtOp_apertureProj_le hT s
  rw [hId]
  calc RHTower.traceNorm H (((1 - Q) ∘L R) ∘L R + (Q ∘L R) ∘L (R ∘L (1 - Q)))
      ≤ RHTower.traceNorm H (((1 - Q) ∘L R) ∘L R) +
          RHTower.traceNorm H ((Q ∘L R) ∘L (R ∘L (1 - Q))) :=
        traceNorm_add_le' (memSchattenClass_one_comp_hs hR hA1)
          (memSchattenClass_one_comp_hs hA3 hA2)
    _ ≤ R.hsNorm * ((1 - Q) ∘L R).hsNorm + (R ∘L (1 - Q)).hsNorm * (Q ∘L R).hsNorm :=
        add_le_add (traceNorm_comp_le_hsNorm hR hA1) (traceNorm_comp_le_hsNorm hA3 hA2)
    _ ≤ R.hsNorm * (R ∘L (1 - Q)).hsNorm + (R ∘L (1 - Q)).hsNorm * R.hsNorm := by
        rw [ht1]
        gcongr
        exact ContinuousLinearMap.hsNorm_nonneg _
    _ = 2 * R.hsNorm * (R ∘L (1 - Q)).hsNorm := by ring

theorem aperture_conj_eq_sum (s : Finset ℂ) (X : H →L[ℂ] H) :
    apertureProj U s ∘L X ∘L apertureProj U s =
      ∑ c ∈ s, ∑ d ∈ s, eigenproj U c ∘L X ∘L eigenproj U d := by
  ext x
  simp only [apertureProj, ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  exact Finset.sum_comm

theorem isHilbertSchmidt_aperture_conj {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (s : Finset ℂ) :
    IsHilbertSchmidt (apertureProj U s ∘L X ∘L apertureProj U s) :=
  (hX.comp_right _).comp_left _

/-- On a finite aperture the pinching keeps the diagonal blocks. -/
theorem atomicPinch_aperture {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (s : Finset ℂ) :
    atomicPinch U (isHilbertSchmidt_aperture_conj (U := U) hX s) =
      ∑ c ∈ s, eigenproj U c ∘L X ∘L eigenproj U c := by
  refine ext_adapted (U := U) fun i => ?_
  rw [atomicPinch_apply, sum_apply]
  rcases i with ⟨d, k⟩ | k
  · simp only [atomicPinchCol, ContinuousLinearMap.comp_apply, apertureProj_adaptedVec_inl,
      eigenproj_apertureProj, eigenproj_adaptedVec_inl]
    have hsum : ∑ c ∈ s, eigenproj U c (X (if d = c then adaptedVec U (Sum.inl ⟨d, k⟩) else 0)) =
        if d ∈ s then eigenproj U d (X (adaptedVec U (Sum.inl ⟨d, k⟩))) else 0 := by
      rw [Finset.sum_congr rfl fun c _ => by rw [apply_ite X, map_zero,
        apply_ite (eigenproj U c), map_zero], Finset.sum_ite_eq]
    rw [hsum]
    split_ifs <;> simp
  · simp [atomicPinchCol, eigenproj_adaptedVec_inr]

/-- **Finite apertures.**  On finitely many eigenvalue blocks the formation converges in trace
norm: the off-diagonal blocks carry Cesàro averages of nontrivial phases. -/
theorem tendsto_traceNorm_aperture (hT : RHTower.MemSchattenClass 1 T) (s : Finset ℂ) :
    Tendsto (fun N => RHTower.traceNorm H
      (hsCesaro U N (apertureProj U s ∘L T ∘L apertureProj U s) -
        atomicPinch U (isHilbertSchmidt_aperture_conj (U := U) hT.one_isHilbertSchmidt s)))
      atTop (𝓝 0) := by
  classical
  set B : ℂ → ℂ → H →L[ℂ] H := fun c d => eigenproj U c ∘L T ∘L eigenproj U d
  set coef : ℕ → ℂ → ℂ → ℂ := fun N c d =>
    cesaroCoeff ((starRingEnd ℂ) c * d) N - if c = d then 1 else 0
  have hB : ∀ c d, RHTower.MemSchattenClass 1 (B c d) := fun c d =>
    RHTower.memSchattenClass_one_comp_left (RHTower.memSchattenClass_one_comp_right hT _) _
  have hdecomp : ∀ N, hsCesaro U N (apertureProj U s ∘L T ∘L apertureProj U s) -
      atomicPinch U (isHilbertSchmidt_aperture_conj (U := U) hT.one_isHilbertSchmidt s) =
      ∑ c ∈ s, ∑ d ∈ s, coef N c d • B c d := by
    intro N
    rw [atomicPinch_aperture hT.one_isHilbertSchmidt s, aperture_conj_eq_sum, hsCesaro_sum]
    simp_rw [hsCesaro_sum, hsCesaro_block]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have : B c c = ∑ d ∈ s, (if c = d then (1 : ℂ) else 0) • B c d := by
      simp only [ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq s c (fun d => B c d), if_pos hc]
    rw [show eigenproj U c ∘L T ∘L eigenproj U c = B c c from rfl, this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [coef, sub_smul]
    rfl
  have hbound : ∀ N, RHTower.traceNorm H
      (hsCesaro U N (apertureProj U s ∘L T ∘L apertureProj U s) -
        atomicPinch U (isHilbertSchmidt_aperture_conj (U := U) hT.one_isHilbertSchmidt s)) ≤
      ∑ c ∈ s, ∑ d ∈ s, ‖coef N c d‖ * RHTower.traceNorm H (B c d) := by
    intro N
    rw [hdecomp]
    refine (traceNorm_sum_le s fun c _ => memSchattenClass_one_sum _ _ fun d _ =>
      RHTower.memSchattenClass_one_smul (hB c d) _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (traceNorm_sum_le s fun d _ => RHTower.memSchattenClass_one_smul (hB c d) _).trans
      (le_of_eq (Finset.sum_congr rfl fun d _ => ?_))
    rw [RHTower.traceNorm_smul]
  have hterm : ∀ c d, Tendsto (fun N => ‖coef N c d‖ * RHTower.traceNorm H (B c d)) atTop
      (𝓝 0) := by
    intro c d
    by_cases hBz : B c d = 0
    · simp only [hBz, RHTower.traceNorm_zero, mul_zero]
      exact tendsto_const_nhds
    obtain ⟨x, hx⟩ : ∃ x, B c d x ≠ 0 := by
      by_contra h
      push Not at h
      exact hBz (ContinuousLinearMap.ext h)
    have hc : ‖c‖ = 1 :=
      norm_eq_one_of_mem_unitaryEigenspace (Submodule.starProjection_apply_mem _ _) hx
    have hdx : eigenproj U d x ≠ 0 := fun h => hx (by simp [B, h])
    have hd : ‖d‖ = 1 :=
      norm_eq_one_of_mem_unitaryEigenspace (Submodule.starProjection_apply_mem _ x) hdx
    have hr : ‖(starRingEnd ℂ) c * d‖ = 1 := by rw [norm_mul, Complex.norm_conj, hc, hd, one_mul]
    have hlim := tendsto_cesaroCoeff hr
    have hcoef : Tendsto (fun N => coef N c d) atTop (𝓝 0) := by
      have := hlim.sub_const (if c = d then (1 : ℂ) else 0)
      have heq : (if (starRingEnd ℂ) c * d = 1 then (1 : ℂ) else 0) -
          (if c = d then 1 else 0) = 0 := by
        by_cases hcd : c = d
        · rw [if_pos ((conj_mul_eq_one_iff hc).mpr hcd), if_pos hcd, sub_self]
        · rw [if_neg (fun h => hcd ((conj_mul_eq_one_iff hc).mp h)), if_neg hcd, sub_self]
      rwa [heq] at this
    simpa using (hcoef.norm.mul_const (RHTower.traceNorm H (B c d)))
  have hsum : Tendsto (fun N => ∑ c ∈ s, ∑ d ∈ s, ‖coef N c d‖ * RHTower.traceNorm H (B c d))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum s fun c _ => tendsto_finsetSum s fun d _ => hterm c d
    simpa using this
  exact squeeze_zero (fun N => RHTower.traceNorm_nonneg _) hbound hsum

/-- `Π_at(X) - Π_at(Q_s X Q_s) = (1 - Q_s) Π_at(X) (1 - Q_s)`. -/
theorem atomicPinch_sub_aperture_eq {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (s : Finset ℂ) :
    atomicPinch U hX - atomicPinch U (isHilbertSchmidt_aperture_conj (U := U) hX s) =
      (1 - apertureProj U s) ∘L atomicPinch U hX ∘L (1 - apertureProj U s) := by
  rw [atomicPinch_aperture hX s]
  refine ext_adapted (U := U) fun i => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    one_sub_apertureProj_adaptedVec, sub_apply, sum_apply]
  rcases i with ⟨d, k⟩ | k
  · simp only [adaptedLabel, Sum.isLeft_inl, and_true, ContinuousLinearMap.comp_apply,
      eigenproj_adaptedVec_inl]
    have hsum : ∑ c ∈ s, eigenproj U c (X (if d = c then adaptedVec U (Sum.inl ⟨d, k⟩) else 0)) =
        if d ∈ s then eigenproj U d (X (adaptedVec U (Sum.inl ⟨d, k⟩))) else 0 := by
      rw [Finset.sum_congr rfl fun c _ => by rw [apply_ite X, map_zero,
        apply_ite (eigenproj U c), map_zero], Finset.sum_ite_eq]
    rw [hsum, atomicPinch_apply]
    by_cases hds : d ∈ s
    · simp only [hds, if_true, map_zero, atomicPinchCol, sub_self]
    · simp only [hds, if_false, sub_zero, atomicPinchCol]
      rw [atomicPinch_apply, sub_apply, one_apply_eq_self]
      simp only [atomicPinchCol]
      rw [apertureProj_eigenproj, if_neg hds, sub_zero]
  · simp [adaptedLabel, atomicPinch_apply, atomicPinchCol, eigenproj_adaptedVec_inr]

/-- The aperture tail `(1 - Q_s) Π_at(T) (1 - Q_s)` of a positive trace-class `T` is positive and
trace class. -/
theorem aperture_tail_traceClass (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (s : Finset ℂ) :
    ((1 - apertureProj U s) ∘L atomicPinch U hT.one_isHilbertSchmidt ∘L
        (1 - apertureProj U s)).IsPositive ∧
      RHTower.MemSchattenClass 1 ((1 - apertureProj U s) ∘L
        atomicPinch U hT.one_isHilbertSchmidt ∘L (1 - apertureProj U s)) := by
  have hsa := isSelfAdjoint_one_sub_apertureProj (U := U) s
  obtain ⟨hPpos, hPmem, -⟩ := atomicPinch_traceClass (U := U) hT hpos
  refine ⟨?_, RHTower.memSchattenClass_one_comp_left
    (RHTower.memSchattenClass_one_comp_right hPmem _) _⟩
  have h := hPpos.conj_adjoint (1 - apertureProj U s)
  rwa [hsa.adjoint_eq] at h

/-- The diagonal of the aperture tail on the adapted basis. -/
theorem inner_aperture_tail_adaptedVec {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (s : Finset ℂ)
    (i : AdaptedIndex U) :
    ⟪adaptedVec U i, ((1 - apertureProj U s) ∘L atomicPinch U hX ∘L (1 - apertureProj U s))
        (adaptedVec U i)⟫_ℂ =
      if adaptedLabel i ∈ s ∧ i.isLeft then 0 else atomicDiag U X i := by
  have hsym : ∀ x y : H, ⟪x, (1 - apertureProj U s) y⟫_ℂ = ⟪(1 - apertureProj U s) x, y⟫_ℂ :=
    fun x y => ((isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_one_sub_apertureProj (U := U) s)) x y).symm
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hsym,
    one_sub_apertureProj_adaptedVec]
  split_ifs with h
  · simp
  · rw [inner_atomicPinch_adaptedVec]

/-- **The escaped tail.**  With zero continuous mass, `Π_at(T) - Π_at(Q_s T Q_s)` is positive and
its trace norm is exactly the truncation tail `‖T^{1/2}(1 - Q_s)‖₂²`. -/
theorem traceNorm_atomicPinch_sub_aperture (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (hmc : continuousMass U T = 0) (s : Finset ℂ) :
    RHTower.traceNorm H (atomicPinch U hT.one_isHilbertSchmidt -
        atomicPinch U (isHilbertSchmidt_aperture_conj (U := U) hT.one_isHilbertSchmidt s)) =
      hsNormSq (RHTower.traceClassRoot T ∘L (1 - apertureProj U s)) := by
  obtain ⟨hDpos, hDmem⟩ := aperture_tail_traceClass (U := U) hT hpos s
  rw [atomicPinch_sub_aperture_eq, RHTower.traceNorm_eq_re_opTrace_of_isPositive hDmem hDpos,
    opTrace_eq_tsum_adapted hDmem,
    hsNormSq_eq ((RHTower.traceClassRoot_isHilbertSchmidt hT).comp_right _) (adaptedBasis U)]
  have hterm : ∀ i, ⟪adaptedVec U i, ((1 - apertureProj U s) ∘L
      atomicPinch U hT.one_isHilbertSchmidt ∘L (1 - apertureProj U s)) (adaptedVec U i)⟫_ℂ =
      ((‖(RHTower.traceClassRoot T ∘L (1 - apertureProj U s)) (adaptedBasis U i)‖ ^ 2 : ℝ) :
        ℂ) := by
    intro i
    rw [inner_aperture_tail_adaptedVec, adaptedBasis_apply, ContinuousLinearMap.comp_apply,
      one_sub_apertureProj_adaptedVec]
    split_ifs with h
    · simp
    · rcases i with ⟨d, k⟩ | k
      · simp only [atomicDiag, Sum.isLeft_inl, if_true]
        exact inner_eq_norm_sqrtOp_sq hpos _
      · simp [atomicDiag, sqrtOp_adaptedVec_inr hT hpos hmc k]
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-- **`(MSF.1)` in trace norm.**  For positive trace-class `T`, the finite block sums
`∑_{λ ∈ s} P_λ T P_λ` converge to the atomic pinching in trace norm. -/
theorem tendsto_traceNorm_atomicPinch_sub_sum (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) :
    Tendsto (fun s : Finset ℂ => RHTower.traceNorm H (atomicPinch U hT.one_isHilbertSchmidt -
      ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c)) atTop (𝓝 0) := by
  classical
  set g : AdaptedIndex U → ℝ := fun i => (atomicDiag U T i).re
  have hg : Summable g := Complex.reCLM.summable (summable_atomicDiag (U := U) hT)
  have hg0 : ∀ i, 0 ≤ g i := fun i => (Complex.nonneg_iff.mp (atomicDiag_nonneg hpos i)).1
  have hval : ∀ s : Finset ℂ, RHTower.traceNorm H (atomicPinch U hT.one_isHilbertSchmidt -
      ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c) =
      ∑' i, (if adaptedLabel i ∈ s ∧ i.isLeft then 0 else g i) := by
    intro s
    obtain ⟨hDpos, hDmem⟩ := aperture_tail_traceClass (U := U) hT hpos s
    have hsumD : Summable fun i => ⟪adaptedVec U i, ((1 - apertureProj U s) ∘L
        atomicPinch U hT.one_isHilbertSchmidt ∘L (1 - apertureProj U s)) (adaptedVec U i)⟫_ℂ := by
      simpa only [adaptedBasis_apply] using hDmem.one_summable_inner_diag_basis (adaptedBasis U)
    rw [← atomicPinch_aperture hT.one_isHilbertSchmidt s, atomicPinch_sub_aperture_eq,
      RHTower.traceNorm_eq_re_opTrace_of_isPositive hDmem hDpos, opTrace_eq_tsum_adapted hDmem,
      Complex.re_tsum hsumD]
    refine tsum_congr fun i => ?_
    rw [inner_aperture_tail_adaptedVec]
    split_ifs <;> simp [g]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp (tendsto_tsum_compl_atTop_zero g)) ε hε
  refine ⟨J.image adaptedLabel, fun s hs => ?_⟩
  have htail := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at htail
  have hnn : 0 ≤ ∑' i : {x // x ∉ J}, g i := tsum_nonneg fun i => hg0 i
  rw [abs_of_nonneg hnn] at htail
  have hle : ∑' i, (if adaptedLabel i ∈ s ∧ i.isLeft then 0 else g i) ≤
      ∑' i : {x // x ∉ J}, g i := by
    have hsub : (∑' i : {x // x ∉ J}, g i) = ∑' i, Set.indicator {x | x ∉ J} g i :=
      tsum_subtype ({x | x ∉ J} : Set (AdaptedIndex U)) g
    rw [hsub]
    have hs1 : Summable fun i => if adaptedLabel i ∈ s ∧ i.isLeft then 0 else g i :=
      hg.of_nonneg_of_le (fun i => by split_ifs; exacts [le_rfl, hg0 i])
        (fun i => by split_ifs; exacts [hg0 i, le_rfl])
    refine Summable.tsum_le_tsum (fun i => ?_) hs1 (hg.indicator _)
    by_cases hi : i ∈ J
    · rcases i with ⟨d, k⟩ | k
      · have hd : adaptedLabel (Sum.inl ⟨d, k⟩ : AdaptedIndex U) ∈ s :=
          hs (Finset.mem_image_of_mem _ hi)
        simp [hd, hi]
      · simp [Set.indicator, hi, g, atomicDiag]
    · simp only [Set.indicator, Set.mem_setOf_eq, hi, not_false_eq_true, if_true]
      split_ifs
      · exact hg0 i
      · exact le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (RHTower.traceNorm_nonneg _), hval]
  exact lt_of_le_of_lt hle htail

/-- **Theorem 5.1, sufficiency.**  Zero continuous mass gives trace-norm convergence of the
formation to the atomic pinching. -/
theorem tendsto_traceNorm_of_continuousMass_eq_zero (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) (hmc : continuousMass U T = 0) :
    Tendsto (fun N => RHTower.traceNorm H
      (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt)) atTop (𝓝 0) := by
  set R := RHTower.traceClassRoot T
  set τ : Finset ℂ → ℝ := fun s => hsNormSq (R ∘L (1 - apertureProj U s))
  have hτ := tendsto_hsNormSq_sqrtOp_tail (U := U) hT hpos hmc
  have hbig : Tendsto (fun s => 2 * R.hsNorm * Real.sqrt (τ s) + τ s) atTop (𝓝 0) := by
    have h1 := (Real.continuous_sqrt.tendsto 0).comp hτ
    rw [Real.sqrt_zero] at h1
    have := ((h1.const_mul (2 * R.hsNorm)).add hτ)
    rwa [mul_zero, add_zero] at this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s, hs⟩ := (hbig.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (tendsto_traceNorm_aperture (U := U) hT s) (ε / 2)
    (half_pos hε)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  set Q := apertureProj U s
  have hQTQ := isHilbertSchmidt_aperture_conj (U := U) hT.one_isHilbertSchmidt s
  have hQmem : RHTower.MemSchattenClass 1 (Q ∘L T ∘L Q) :=
    RHTower.memSchattenClass_one_comp_left (RHTower.memSchattenClass_one_comp_right hT _) _
  have hdiff : RHTower.MemSchattenClass 1 (T - Q ∘L T ∘L Q) := memSchattenClass_one_sub' hT hQmem
  have hQpos : (Q ∘L T ∘L Q).IsPositive := by
    have h := hpos.conj_adjoint Q
    rwa [(isSelfAdjoint_apertureProj s).adjoint_eq] at h
  have hPQ := (atomicPinch_traceClass (U := U) hQmem hQpos).2.1
  have hPT := (atomicPinch_traceClass (U := U) hT hpos).2.1
  have hsplit : hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt =
      hsCesaro U N (T - Q ∘L T ∘L Q) +
        (hsCesaro U N (Q ∘L T ∘L Q) - atomicPinch U hQTQ) -
        (atomicPinch U hT.one_isHilbertSchmidt - atomicPinch U hQTQ) := by
    have : hsCesaro U N T = hsCesaro U N (T - Q ∘L T ∘L Q) + hsCesaro U N (Q ∘L T ∘L Q) := by
      rw [← hsCesaro_add, sub_add_cancel]
    rw [this]
    abel
  have hm1 := memSchattenClass_one_hsCesaro U hdiff N
  have hm2 := memSchattenClass_one_sub' (memSchattenClass_one_hsCesaro U hQmem N) hPQ
  have hm3 := memSchattenClass_one_sub' hPT hPQ
  have hest : RHTower.traceNorm H (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt) ≤
      2 * R.hsNorm * Real.sqrt (τ s) + RHTower.traceNorm H
        (hsCesaro U N (Q ∘L T ∘L Q) - atomicPinch U hQTQ) + τ s := by
    rw [hsplit]
    refine (traceNorm_sub_le' (memSchattenClass_one_add' hm1 hm2) hm3).trans ?_
    refine add_le_add ((traceNorm_add_le' hm1 hm2).trans (add_le_add ?_ le_rfl)) (le_of_eq ?_)
    · refine (traceNorm_hsCesaro_le U hdiff N).trans ?_
      exact traceNorm_sub_aperture_le hT hpos s
    · exact traceNorm_atomicPinch_sub_aperture hT hpos hmc s
  have h2 := hN₀ N (le_of_max_le_left hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (RHTower.traceNorm_nonneg _)] at h2 ⊢
  linarith

/-- **Theorem 5.1, `(MSF.9)`.**  For positive trace-class `T`, the Cesàro formation converges to
the atomic pinching in trace norm exactly when the continuous mass vanishes. -/
theorem tendsto_traceNorm_iff_continuousMass_eq_zero (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) :
    Tendsto (fun N => RHTower.traceNorm H
        (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt)) atTop (𝓝 0) ↔
      continuousMass U T = 0 :=
  ⟨continuousMass_eq_zero_of_tendsto hT hpos, tendsto_traceNorm_of_continuousMass_eq_zero hT hpos⟩

end Sufficiency

end GaloisForLFunctions.HTGeometry
