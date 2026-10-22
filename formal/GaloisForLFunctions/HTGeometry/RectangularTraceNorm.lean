/-
# Rectangular trace norm

The existing approximation-number and Schatten infrastructure treats Hilbert endomorphisms.
Sheet--target incidence operators are naturally rectangular.  This module develops their exact
finite-rank approximation numbers and nuclear norm, proves the two-sided ideal laws, proves
invariance under Hilbert adjoint, and recovers the existing square theory definitionally.
-/
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.RHTower.Deninger.DeningerHilbertSchmidtNuclear
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

namespace RHTower

open ContinuousLinearMap

section Rank

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- A rectangular operator has rank at most `n` when its range lies in an at-most-`n` dimensional
target subspace. -/
def HasRectRankLE (T : E →L[ℂ] F) (n : ℕ) : Prop :=
  ∃ V : Submodule ℂ F, FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ n ∧
    ∀ x, T x ∈ V

theorem hasRectRankLE_zero (n : ℕ) : HasRectRankLE (0 : E →L[ℂ] F) n :=
  ⟨⊥, inferInstance, by simp, fun x => by simp⟩

theorem HasRectRankLE.mono {T : E →L[ℂ] F} {m n : ℕ}
    (hT : HasRectRankLE T m) (hmn : m ≤ n) : HasRectRankLE T n := by
  obtain ⟨V, hV, hdim, hrange⟩ := hT
  exact ⟨V, hV, hdim.trans hmn, hrange⟩

theorem HasRectRankLE.comp_right {T : E →L[ℂ] F} {n : ℕ}
    (hT : HasRectRankLE T n) (B : G →L[ℂ] E) :
    HasRectRankLE (T ∘L B) n := by
  obtain ⟨V, hV, hdim, hrange⟩ := hT
  exact ⟨V, hV, hdim, fun x => by rw [comp_apply]; exact hrange (B x)⟩

theorem HasRectRankLE.comp_left {T : E →L[ℂ] F} {n : ℕ}
    (hT : HasRectRankLE T n) (A : F →L[ℂ] G) :
    HasRectRankLE (A ∘L T) n := by
  obtain ⟨V, hV, hdim, hrange⟩ := hT
  letI : FiniteDimensional ℂ V := hV
  haveI : Module.Finite ℂ (V.map (A : F →ₗ[ℂ] G)) := Module.Finite.map V _
  refine ⟨V.map (A : F →ₗ[ℂ] G), inferInstance,
    (Submodule.finrank_map_le _ V).trans hdim, fun x => ?_⟩
  rw [comp_apply]
  exact Submodule.mem_map_of_mem (hrange x)

end Rank

section ApproximationNumbers

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The `n`th rectangular approximation number: distance from operators of rank at most `n`. -/
def rectApproxNumber (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ A : E →L[ℂ] F, HasRectRankLE A n ∧ ‖T - A‖ = r}

theorem rectApproxNumber_set_nonempty (T : E →L[ℂ] F) (n : ℕ) :
    {r : ℝ | ∃ A : E →L[ℂ] F, HasRectRankLE A n ∧ ‖T - A‖ = r}.Nonempty :=
  ⟨‖T‖, 0, hasRectRankLE_zero n, by rw [sub_zero]⟩

theorem rectApproxNumber_set_bddBelow (T : E →L[ℂ] F) (n : ℕ) :
    BddBelow {r : ℝ | ∃ A : E →L[ℂ] F, HasRectRankLE A n ∧ ‖T - A‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨A, -, rfl⟩
  positivity

theorem rectApproxNumber_le (T : E →L[ℂ] F) (n : ℕ)
    (A : E →L[ℂ] F) (hA : HasRectRankLE A n) :
    rectApproxNumber T n ≤ ‖T - A‖ :=
  csInf_le (rectApproxNumber_set_bddBelow T n) ⟨A, hA, rfl⟩

theorem rectApproxNumber_nonneg (T : E →L[ℂ] F) (n : ℕ) :
    0 ≤ rectApproxNumber T n := by
  refine le_csInf (rectApproxNumber_set_nonempty T n) ?_
  rintro r ⟨A, -, rfl⟩
  positivity

theorem rectApproxNumber_le_norm (T : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber T n ≤ ‖T‖ := by
  simpa using rectApproxNumber_le T n 0 (hasRectRankLE_zero n)

theorem rectApproxNumber_zero (n : ℕ) :
    rectApproxNumber (0 : E →L[ℂ] F) n = 0 := by
  exact le_antisymm (by simpa using
    rectApproxNumber_le_norm (0 : E →L[ℂ] F) n)
    (rectApproxNumber_nonneg 0 n)

theorem rectApproxNumber_antitone (T : E →L[ℂ] F) :
    Antitone (rectApproxNumber T) := by
  intro m n hmn
  refine csInf_le_csInf (rectApproxNumber_set_bddBelow T n)
    (rectApproxNumber_set_nonempty T m) ?_
  rintro r ⟨A, hA, rfl⟩
  exact ⟨A, hA.mono hmn, rfl⟩

theorem rectApproxNumber_zero_eq_norm (T : E →L[ℂ] F) :
    rectApproxNumber T 0 = ‖T‖ := by
  refine le_antisymm (rectApproxNumber_le_norm T 0) ?_
  refine le_csInf (rectApproxNumber_set_nonempty T 0) ?_
  rintro r ⟨A, hA, rfl⟩
  obtain ⟨V, hV, hdim, hrange⟩ := hA
  have hVbot : V = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hdim)
  have hA0 : A = 0 := by
    ext x
    have hx := hrange x
    rw [hVbot, Submodule.mem_bot] at hx
    exact hx
  rw [hA0, sub_zero]

theorem rectApproxNumber_comp_le_left (A : F →L[ℂ] G)
    (T : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber (A ∘L T) n ≤ ‖A‖ * rectApproxNumber T n := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [zero_comp, norm_zero, zero_mul]
    simpa using rectApproxNumber_le_norm (0 : E →L[ℂ] G) n
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hlt : rectApproxNumber T n < rectApproxNumber T n + ε / ‖A‖ := by
      exact lt_add_of_pos_right _ (div_pos hε hAnorm)
    obtain ⟨B, hB, hBlt⟩ :=
      (csInf_lt_iff (rectApproxNumber_set_bddBelow T n)
        (rectApproxNumber_set_nonempty T n)).mp hlt
    obtain ⟨S, hS, rfl⟩ := hB
    have hbound := rectApproxNumber_le (A ∘L T) n (A ∘L S) (hS.comp_left A)
    rw [← comp_sub] at hbound
    calc
      rectApproxNumber (A ∘L T) n ≤ ‖A ∘L (T - S)‖ := hbound
      _ ≤ ‖A‖ * ‖T - S‖ := A.opNorm_comp_le (T - S)
      _ ≤ ‖A‖ * (rectApproxNumber T n + ε / ‖A‖) :=
        mul_le_mul_of_nonneg_left hBlt.le (norm_nonneg A)
      _ = ‖A‖ * rectApproxNumber T n + ε := by field_simp

theorem rectApproxNumber_comp_le_right (T : E →L[ℂ] F)
    (B : G →L[ℂ] E) (n : ℕ) :
    rectApproxNumber (T ∘L B) n ≤ rectApproxNumber T n * ‖B‖ := by
  rcases eq_or_ne B 0 with rfl | hB
  · rw [comp_zero, norm_zero, mul_zero]
    simpa using rectApproxNumber_le_norm (0 : G →L[ℂ] F) n
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hBnorm : 0 < ‖B‖ := norm_pos_iff.mpr hB
    have hlt : rectApproxNumber T n < rectApproxNumber T n + ε / ‖B‖ := by
      exact lt_add_of_pos_right _ (div_pos hε hBnorm)
    obtain ⟨A, hA, hAlt⟩ :=
      (csInf_lt_iff (rectApproxNumber_set_bddBelow T n)
        (rectApproxNumber_set_nonempty T n)).mp hlt
    obtain ⟨S, hS, rfl⟩ := hA
    have hbound := rectApproxNumber_le (T ∘L B) n (S ∘L B) (hS.comp_right B)
    rw [← sub_comp] at hbound
    calc
      rectApproxNumber (T ∘L B) n ≤ ‖(T - S) ∘L B‖ := hbound
      _ ≤ ‖T - S‖ * ‖B‖ := (T - S).opNorm_comp_le B
      _ ≤ (rectApproxNumber T n + ε / ‖B‖) * ‖B‖ :=
        mul_le_mul_of_nonneg_right hAlt.le (norm_nonneg B)
      _ = rectApproxNumber T n * ‖B‖ + ε := by field_simp

end ApproximationNumbers

section Adjoint

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Taking the Hilbert adjoint preserves every finite-rank cutoff, including its exact rank
budget. -/
theorem HasRectRankLE.adjoint {T : E →L[ℂ] F} {n : ℕ}
    (hT : HasRectRankLE T n) : HasRectRankLE (adjoint T) n := by
  obtain ⟨V, hV, hdim, hrange⟩ := hT
  letI : FiniteDimensional ℂ V := hV
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let S : E →L[ℂ] V := T.codRestrict V hrange
  let W : Submodule ℂ E :=
    Submodule.map (ContinuousLinearMap.adjoint S : V →ₗ[ℂ] E) ⊤
  haveI : Module.Finite ℂ W := Module.Finite.map (⊤ : Submodule ℂ V)
    (ContinuousLinearMap.adjoint S : V →ₗ[ℂ] E)
  have hfactor : V.subtypeL ∘L S = T := by
    ext x
    rfl
  refine ⟨W, inferInstance, ?_, ?_⟩
  · calc
      Module.finrank ℂ W ≤ Module.finrank ℂ (⊤ : Submodule ℂ V) :=
        Submodule.finrank_map_le (ContinuousLinearMap.adjoint S : V →ₗ[ℂ] E) ⊤
      _ = Module.finrank ℂ V := by simp
      _ ≤ n := hdim
  · intro y
    rw [← hfactor, adjoint_comp, comp_apply]
    change ContinuousLinearMap.adjoint S
      (ContinuousLinearMap.adjoint V.subtypeL y) ∈ W
    exact ⟨ContinuousLinearMap.adjoint V.subtypeL y, by simp, rfl⟩

theorem rectApproxNumber_adjoint_le (T : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber (adjoint T) n ≤ rectApproxNumber T n := by
  refine le_csInf (rectApproxNumber_set_nonempty T n) ?_
  rintro r ⟨A, hA, rfl⟩
  calc
    rectApproxNumber (adjoint T) n ≤ ‖adjoint T - adjoint A‖ :=
      rectApproxNumber_le _ _ _ hA.adjoint
    _ = ‖T - A‖ := by
      simpa using
        (ContinuousLinearMap.adjoint :
          (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).norm_map (T - A)

/-- Rectangular approximation numbers are invariant under adjoint, with every multiplicity
retained. -/
theorem rectApproxNumber_adjoint (T : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber (adjoint T) n = rectApproxNumber T n := by
  apply le_antisymm (rectApproxNumber_adjoint_le T n)
  have h := rectApproxNumber_adjoint_le (adjoint T) n
  simpa using h

end Adjoint

section TraceNorm

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable (E F) in
/-- Nuclear norm of a rectangular operator: sum of all approximation numbers. -/
noncomputable def rectTraceNorm (T : E →L[ℂ] F) : ℝ :=
  ∑' n, rectApproxNumber T n

/-- Rectangular Schatten membership through approximation-number summability. -/
def MemRectSchattenClass (p : ℝ) (T : E →L[ℂ] F) : Prop :=
  Summable fun n => rectApproxNumber T n ^ p

theorem rectTraceNorm_nonneg (T : E →L[ℂ] F) :
    0 ≤ rectTraceNorm E F T :=
  tsum_nonneg fun n => rectApproxNumber_nonneg T n

theorem rectTraceNorm_zero :
    rectTraceNorm E F (0 : E →L[ℂ] F) = 0 := by
  unfold rectTraceNorm
  simp [rectApproxNumber_zero]

/-- Operator norm is dominated by rectangular nuclear norm on its summability domain. -/
theorem norm_le_rectTraceNorm {T : E →L[ℂ] F}
    (hT : Summable fun n => rectApproxNumber T n) :
    ‖T‖ ≤ rectTraceNorm E F T := by
  rw [← rectApproxNumber_zero_eq_norm]
  exact hT.le_tsum 0 fun n _ => rectApproxNumber_nonneg T n

/-- Rectangular nuclear norm is definite on its summability domain. -/
theorem rectTraceNorm_eq_zero_iff {T : E →L[ℂ] F}
    (hT : Summable fun n => rectApproxNumber T n) :
    rectTraceNorm E F T = 0 ↔ T = 0 := by
  constructor
  · intro hzero
    have hnorm := norm_le_rectTraceNorm hT
    rw [hzero] at hnorm
    exact norm_le_zero_iff.mp hnorm
  · rintro rfl
    exact rectTraceNorm_zero

theorem summable_rectApproxNumber_comp_left
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {T : E →L[ℂ] F} (hT : Summable fun n => rectApproxNumber T n)
    (A : F →L[ℂ] G) :
    Summable fun n => rectApproxNumber (A ∘L T) n :=
  Summable.of_nonneg_of_le (fun n => rectApproxNumber_nonneg _ n)
    (fun n => rectApproxNumber_comp_le_left A T n) (hT.mul_left ‖A‖)

theorem summable_rectApproxNumber_comp_right
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {T : E →L[ℂ] F} (hT : Summable fun n => rectApproxNumber T n)
    (B : G →L[ℂ] E) :
    Summable fun n => rectApproxNumber (T ∘L B) n :=
  Summable.of_nonneg_of_le (fun n => rectApproxNumber_nonneg _ n)
    (fun n => rectApproxNumber_comp_le_right T B n) (hT.mul_right ‖B‖)

/-- Left ideal law for rectangular nuclear norm. -/
theorem rectTraceNorm_comp_left_le
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {T : E →L[ℂ] F} (hT : Summable fun n => rectApproxNumber T n)
    (A : F →L[ℂ] G) :
    rectTraceNorm E G (A ∘L T) ≤ ‖A‖ * rectTraceNorm E F T := by
  unfold rectTraceNorm
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => rectApproxNumber_comp_le_left A T n)
    (summable_rectApproxNumber_comp_left hT A) (hT.mul_left ‖A‖)

/-- Right ideal law for rectangular nuclear norm. -/
theorem rectTraceNorm_comp_right_le
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {T : E →L[ℂ] F} (hT : Summable fun n => rectApproxNumber T n)
    (B : G →L[ℂ] E) :
    rectTraceNorm G F (T ∘L B) ≤ rectTraceNorm E F T * ‖B‖ := by
  unfold rectTraceNorm
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun n => rectApproxNumber_comp_le_right T B n)
    (summable_rectApproxNumber_comp_right hT B) (hT.mul_right ‖B‖)

theorem memRectSchattenClass_one_iff (T : E →L[ℂ] F) :
    MemRectSchattenClass 1 T ↔ Summable (fun n => rectApproxNumber T n) := by
  unfold MemRectSchattenClass
  simp only [Real.rpow_one]

theorem rectTraceNorm_eq_traceNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) :
    rectTraceNorm H H T = traceNorm H T := by
  rfl

theorem memRectSchattenClass_iff_memSchattenClass
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p : ℝ) (T : H →L[ℂ] H) :
    MemRectSchattenClass p T ↔ MemSchattenClass p T := by
  rfl

end TraceNorm

section TraceNormAdjoint

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The rectangular nuclear norm is exactly invariant under Hilbert adjoint. -/
theorem rectTraceNorm_adjoint (T : E →L[ℂ] F) :
    rectTraceNorm F E (adjoint T) = rectTraceNorm E F T := by
  unfold rectTraceNorm
  exact tsum_congr fun n => rectApproxNumber_adjoint T n

/-- Every rectangular Schatten class is adjoint invariant. -/
theorem memRectSchattenClass_adjoint_iff (p : ℝ) (T : E →L[ℂ] F) :
    MemRectSchattenClass p (adjoint T) ↔ MemRectSchattenClass p T := by
  unfold MemRectSchattenClass
  simp_rw [rectApproxNumber_adjoint T]

end TraceNormAdjoint

section SquareBlockBridge

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Hilbert direct sum used for the square realization of a rectangular map. -/
abbrev rectangularHilbertSum (E F : Type*) := WithLp 2 (E × F)

/-- Isometric inclusion of the rectangular source into the left summand. -/
noncomputable def rectangularLeftInclusion :
    E →L[ℂ] rectangularHilbertSum E F :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm ∘L
    ContinuousLinearMap.inl ℂ E F

/-- Isometric inclusion of the rectangular target into the right summand. -/
noncomputable def rectangularRightInclusion :
    F →L[ℂ] rectangularHilbertSum E F :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm ∘L
    ContinuousLinearMap.inr ℂ E F

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem rectangularLeftInclusion_apply (x : E) :
    rectangularLeftInclusion (E := E) (F := F) x = WithLp.toLp 2 (x, 0) := by
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem rectangularRightInclusion_apply (y : F) :
    rectangularRightInclusion (E := E) (F := F) y = WithLp.toLp 2 (0, y) := by
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_rectangularLeftInclusion_apply (x : E) :
    ‖rectangularLeftInclusion (E := E) (F := F) x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2]
  simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_rectangularRightInclusion_apply (y : F) :
    ‖rectangularRightInclusion (E := E) (F := F) y‖ = ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2]
  simp

omit [InnerProductSpace ℂ E] [CompleteSpace E]
    [InnerProductSpace ℂ F] [CompleteSpace F] in
theorem norm_fst_le_rectangularHilbertSum (z : rectangularHilbertSum E F) :
    ‖z.fst‖ ≤ ‖z‖ := by
  have hsquare := WithLp.prod_norm_sq_eq_of_L2 z
  nlinarith [sq_nonneg ‖z.snd‖, norm_nonneg z.fst, norm_nonneg z]

omit [InnerProductSpace ℂ E] [CompleteSpace E]
    [InnerProductSpace ℂ F] [CompleteSpace F] in
theorem norm_snd_le_rectangularHilbertSum (z : rectangularHilbertSum E F) :
    ‖z.snd‖ ≤ ‖z‖ := by
  have hsquare := WithLp.prod_norm_sq_eq_of_L2 z
  nlinarith [sq_nonneg ‖z.fst‖, norm_nonneg z.snd, norm_nonneg z]

/-- Lower off-diagonal square block `[(0,0);(T,0)]`. -/
noncomputable def rectangularLowerBlock (T : E →L[ℂ] F) :
    rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F :=
  rectangularRightInclusion (E := E) (F := F) ∘L T ∘L
    WithLp.fstL 2 ℂ E F

/-- Compress a square block back from the left source port to the right target port. -/
noncomputable def rectangularCompression
    (S : rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F) : E →L[ℂ] F :=
  WithLp.sndL 2 ℂ E F ∘L S ∘L
    rectangularLeftInclusion (E := E) (F := F)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem rectangularLowerBlock_apply (T : E →L[ℂ] F)
    (z : rectangularHilbertSum E F) :
    rectangularLowerBlock T z = WithLp.toLp 2 (0, T z.fst) := by
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem rectangularCompression_apply
    (S : rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F) (x : E) :
    rectangularCompression S x = (S (WithLp.toLp 2 (x, 0))).snd := by
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem rectangularCompression_lowerBlock (T : E →L[ℂ] F) :
    rectangularCompression (rectangularLowerBlock T) = T := by
  ext x
  simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- Off-diagonal embedding is exactly isometric in operator norm. -/
theorem norm_rectangularLowerBlock (T : E →L[ℂ] F) :
    ‖rectangularLowerBlock T‖ = ‖T‖ := by
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg T)
    intro z
    rw [rectangularLowerBlock_apply]
    change ‖rectangularRightInclusion (E := E) (F := F) (T z.fst)‖ ≤ _
    rw [norm_rectangularRightInclusion_apply]
    exact (T.le_opNorm z.fst).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le_rectangularHilbertSum z) (norm_nonneg T))
  · apply opNorm_le_bound T (norm_nonneg (rectangularLowerBlock T))
    intro x
    have h := (rectangularLowerBlock T).le_opNorm
      (rectangularLeftInclusion (E := E) (F := F) x)
    simpa [norm_rectangularLeftInclusion_apply,
      norm_rectangularRightInclusion_apply] using h

omit [CompleteSpace E] [CompleteSpace F] in
/-- Compression from the square block is contractive in operator norm. -/
theorem norm_rectangularCompression_le
    (S : rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F) :
    ‖rectangularCompression S‖ ≤ ‖S‖ := by
  apply opNorm_le_bound _ (norm_nonneg S)
  intro x
  calc
    ‖rectangularCompression S x‖ =
        ‖(S (rectangularLeftInclusion (E := E) (F := F) x)).snd‖ := by rfl
    _ ≤ ‖S (rectangularLeftInclusion (E := E) (F := F) x)‖ :=
      norm_snd_le_rectangularHilbertSum _
    _ ≤ ‖S‖ * ‖rectangularLeftInclusion (E := E) (F := F) x‖ := S.le_opNorm _
    _ = ‖S‖ * ‖x‖ := by rw [norm_rectangularLeftInclusion_apply]

omit [CompleteSpace E] [CompleteSpace F] in
theorem rectangularLowerBlock_sub (T A : E →L[ℂ] F) :
    rectangularLowerBlock (T - A) =
      rectangularLowerBlock T - rectangularLowerBlock A := by
  ext z
  simp only [rectangularLowerBlock_apply, sub_apply]
  change (WithLp.linearEquiv 2 ℂ (E × F)).symm ((0 : E), T z.fst - A z.fst) =
    (WithLp.linearEquiv 2 ℂ (E × F)).symm ((0 : E), T z.fst) -
      (WithLp.linearEquiv 2 ℂ (E × F)).symm ((0 : E), A z.fst)
  rw [← map_sub]
  apply congrArg (WithLp.linearEquiv 2 ℂ (E × F)).symm
  ext <;> simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem rectangularCompression_sub
    (S Q : rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F) :
    rectangularCompression (S - Q) =
      rectangularCompression S - rectangularCompression Q := by
  ext x
  simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_rectangularLowerBlock_sub (T A : E →L[ℂ] F) :
    ‖rectangularLowerBlock T - rectangularLowerBlock A‖ = ‖T - A‖ := by
  rw [← rectangularLowerBlock_sub, norm_rectangularLowerBlock]

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_sub_rectangularCompression_le
    (T : E →L[ℂ] F)
    (Q : rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F) :
    ‖T - rectangularCompression Q‖ ≤ ‖rectangularLowerBlock T - Q‖ := by
  rw [← rectangularCompression_lowerBlock T, ← rectangularCompression_sub]
  exact norm_rectangularCompression_le _

omit [CompleteSpace E] [CompleteSpace F] in
/-- A rectangular rank budget gives the same rank budget after block embedding. -/
theorem HasRectRankLE.lowerBlock {T : E →L[ℂ] F} {n : ℕ}
    (hT : HasRectRankLE T n) : HasRankLE (rectangularLowerBlock T) n := by
  have hrect := (hT.comp_right (WithLp.fstL 2 ℂ E F)).comp_left
    (rectangularRightInclusion (E := E) (F := F))
  simpa [HasRankLE, HasRectRankLE, rectangularLowerBlock] using hrect

omit [CompleteSpace E] [CompleteSpace F] in
/-- A square rank budget gives the same rank budget after rectangular compression. -/
theorem HasRankLE.rectangularCompression
    {S : rectangularHilbertSum E F →L[ℂ] rectangularHilbertSum E F} {n : ℕ}
    (hS : HasRankLE S n) : HasRectRankLE (rectangularCompression S) n := by
  have hrect : HasRectRankLE S n := by
    simpa [HasRankLE, HasRectRankLE] using hS
  exact (hrect.comp_right (rectangularLeftInclusion (E := E) (F := F))).comp_left
    (WithLp.sndL 2 ℂ E F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Exact square-block law.** Every rectangular approximation number, including zeros and
multiplicity, equals the corresponding approximation number of its lower block. -/
theorem rectApproxNumber_eq_approxNumber_lowerBlock (T : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber T n = approxNumber (rectangularLowerBlock T) n := by
  apply le_antisymm
  · refine le_csInf (approxNumber_set_nonempty (rectangularLowerBlock T) n) ?_
    rintro r ⟨Q, hQ, rfl⟩
    exact (rectApproxNumber_le T n (rectangularCompression Q)
      hQ.rectangularCompression).trans (norm_sub_rectangularCompression_le T Q)
  · refine le_csInf (rectApproxNumber_set_nonempty T n) ?_
    rintro r ⟨A, hA, rfl⟩
    exact (approxNumber_le (rectangularLowerBlock T) n
      (rectangularLowerBlock A) hA.lowerBlock).trans_eq
        (norm_rectangularLowerBlock_sub T A)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rectangular nuclear norm is exactly the square-block trace norm. -/
theorem rectTraceNorm_eq_traceNorm_lowerBlock (T : E →L[ℂ] F) :
    rectTraceNorm E F T = traceNorm (rectangularHilbertSum E F)
      (rectangularLowerBlock T) := by
  unfold rectTraceNorm traceNorm
  exact tsum_congr fun n => rectApproxNumber_eq_approxNumber_lowerBlock T n

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rectangular and square-block Schatten membership are equivalent at every exponent. -/
theorem memRectSchattenClass_iff_lowerBlock (p : ℝ) (T : E →L[ℂ] F) :
    MemRectSchattenClass p T ↔ MemSchattenClass p (rectangularLowerBlock T) := by
  unfold MemRectSchattenClass MemSchattenClass
  simp_rw [rectApproxNumber_eq_approxNumber_lowerBlock T]

/-- Every nuclear map between Hilbert spaces belongs to the rectangular Schatten-one class. -/
theorem DeningerIsNuclear.memRectSchattenClass_one {T : E →L[ℂ] F}
    (hT : DeningerIsNuclear T) : MemRectSchattenClass 1 T := by
  have hblock : DeningerIsNuclear (rectangularLowerBlock T) :=
    (hT.compR (WithLp.fstL 2 ℂ E F)).compL
      (rectangularRightInclusion (E := E) (F := F))
  exact (memRectSchattenClass_iff_lowerBlock 1 T).2 hblock.memSchattenClass_one

/-- Reindex a Hilbert basis along an arbitrary equivalence of index types. -/
noncomputable def hilbertBasisReindexEquiv
    {ι κ : Type*} (b : HilbertBasis ι ℂ F) (e : κ ≃ ι) :
    HilbertBasis κ ℂ F := by
  let v : κ → F := fun k => b (e k)
  have hv : Orthonormal ℂ v := by
    exact b.orthonormal.comp e e.injective
  apply HilbertBasis.mk hv
  have hrange : Set.range v = Set.range b := by
    apply Set.Subset.antisymm
    · rintro x ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
    · rintro x ⟨i, rfl⟩
      obtain ⟨k, rfl⟩ := e.surjective i
      exact ⟨k, rfl⟩
  rw [hrange, b.dense_span]

/-- A separable Hilbert space admits a Hilbert basis whose index lives in universe zero. -/
theorem exists_small_hilbertBasis [TopologicalSpace.SeparableSpace F] :
    ∃ (ι : Type), Nonempty (HilbertBasis ι ℂ F) := by
  obtain ⟨I, b, -⟩ := exists_hilbertBasis ℂ F
  letI : Countable I := b.orthonormal.countable_index
  letI : Encodable I := Encodable.ofCountable I
  let e := Equiv.ofInjective (Encodable.encode : I → ℕ) Encodable.encode_injective
  exact ⟨Set.range (Encodable.encode : I → ℕ),
    ⟨hilbertBasisReindexEquiv b e.symm⟩⟩

/-- **Rectangular Hilbert--Schmidt product law.** A composite of Hilbert--Schmidt maps between
three arbitrary Hilbert carriers is Schatten one. -/
theorem memRectSchattenClass_one_comp_of_hilbertSchmidt
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace F]
    {A : E →L[ℂ] F} {B : F →L[ℂ] G}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    MemRectSchattenClass 1 (B ∘L A) := by
  obtain ⟨ι, ⟨c⟩⟩ := exists_small_hilbertBasis (F := F)
  have hN : DeningerIsNuclear (B.comp A) :=
    deningerIsNuclear_comp_of_hilbertSchmidt c A B
      (by simpa [DeningerIsHilbertSchmidtOn] using hA.adjoint.summable c)
      (by simpa [DeningerIsHilbertSchmidtOn] using hB.summable c)
  exact hN.memRectSchattenClass_one

/-- **Unrestricted rectangular Hilbert--Schmidt product law.** A composite of Hilbert--Schmidt
maps is Schatten one without separability of the intermediate Hilbert space.  Although an ambient
Hilbert basis may live in a large universe, summability forces the active rank-one coefficient
support to be countable.  Reindexing that support inside `ℕ` supplies the universe-zero nuclear
decomposition required by `DeningerIsNuclear`. -/
theorem memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {A : E →L[ℂ] F} {B : F →L[ℂ] G}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    MemRectSchattenClass 1 (B ∘L A) := by
  let c := ContinuousLinearMap.hsBasis ℂ F
  let phi := fun i => innerSL ℂ (adjoint A (c i))
  let y := fun i => B (c i)
  let w := fun i => ‖phi i‖ * ‖y i‖
  have hphi : Summable (fun i => ‖adjoint A (c i)‖ ^ 2) := hA.adjoint.summable c
  have hy : Summable (fun i => ‖B (c i)‖ ^ 2) := hB.summable c
  have hw : Summable w := by
    have hnorm : w = fun i => ‖adjoint A (c i)‖ * ‖B (c i)‖ := by
      funext i
      simp [w, phi, y, innerSL_apply_norm]
    rw [hnorm]
    exact deningerSummable_mul_of_sq hphi hy (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let S := Function.support w
  have hScountable : S.Countable := hw.countable_support
  letI : Countable S := hScountable.to_subtype
  letI : Encodable S := Encodable.ofCountable S
  let e : S ≃ Set.range (Encodable.encode : S → ℕ) :=
    Equiv.ofInjective Encodable.encode Encodable.encode_injective
  have hwS : Summable (w ∘ (fun z : S => (z : _))) := hw.subtype (fun i => i ∈ S)
  have hwJ : Summable ((w ∘ (fun z : S => (z : _))) ∘ e.symm) :=
    (e.symm.summable_iff).2 hwS
  have hN : DeningerIsNuclear (B.comp A) := by
    refine ⟨Set.range (Encodable.encode : S → ℕ),
      fun j => phi (e.symm j), fun j => y (e.symm j), ?_, ?_⟩
    · exact hwJ.congr fun j => by rfl
    · intro x
      have h1 : HasSum (fun i => (c.repr (A x)) i • c i) (A x) := c.hasSum_repr (A x)
      have h2 := B.hasSum h1
      have hfull : HasSum (fun i => phi i x • y i) ((B.comp A) x) := by
        have heq : (fun i => phi i x • y i) =
            fun i => B ((c.repr (A x)) i • c i) := by
          funext i
          rw [map_smul]
          congr 1
          show inner ℂ (adjoint A (c i)) x = (c.repr (A x)) i
          rw [c.repr_apply_apply, ContinuousLinearMap.adjoint_inner_left]
        rw [heq]
        exact h2
      have hsupp : Function.support (fun i => phi i x • y i) ⊆ S := by
        intro i hi
        change w i ≠ 0
        intro hwi
        apply hi
        have hzero : ‖phi i‖ = 0 ∨ ‖y i‖ = 0 := mul_eq_zero.mp hwi
        rcases hzero with hzero | hzero
        · have hphi0 : phi i = 0 := norm_eq_zero.mp hzero
          simp [hphi0]
        · have hy0 : y i = 0 := norm_eq_zero.mp hzero
          simp [hy0]
      have hsub : HasSum
          ((fun i => phi i x • y i) ∘ (fun z : S => (z : _))) ((B.comp A) x) :=
        (hasSum_subtype_iff_of_support_subset hsupp).2 hfull
      exact (e.symm.hasSum_iff).2 hsub
  exact hN.memRectSchattenClass_one

end SquareBlockBridge

/-! ## Rectangular Douglas factorization -/

section RectangularDouglas

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Rectangular Gram order is exactly the adjoint norm domination used by Douglas factorization.
The two operators may have unrelated source carriers. -/
theorem adjoint_norm_le_of_rectangular_gram_sub_gram_isPositive
    (A : E →L[ℂ] G) (B : F →L[ℂ] G)
    (hpos : (B ∘L adjoint B - A ∘L adjoint A).IsPositive)
    (y : G) :
    ‖adjoint A y‖ ≤ ‖adjoint B y‖ := by
  have hq := (ContinuousLinearMap.isPositive_def'.mp hpos).2 y
  have hB :
      (inner ℂ ((B ∘L adjoint B) y) y).re = ‖adjoint B y‖ ^ 2 := by
    have hinner : inner ℂ ((B ∘L adjoint B) y) y =
        inner ℂ (adjoint B y) (adjoint B y) :=
      (adjoint_inner_right B _ _).symm
    rw [hinner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hA :
      (inner ℂ ((A ∘L adjoint A) y) y).re = ‖adjoint A y‖ ^ 2 := by
    have hinner : inner ℂ ((A ∘L adjoint A) y) y =
        inner ℂ (adjoint A y) (adjoint A y) :=
      (adjoint_inner_right A _ _).symm
    rw [hinner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  change 0 ≤ (inner ℂ ((B ∘L adjoint B - A ∘L adjoint A) y) y).re at hq
  rw [sub_apply, inner_sub_left, Complex.sub_re, hB, hA] at hq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- **Rectangular Douglas theorem.** If `A A† ≤ B B†`, with arbitrary source carriers, then
`A = B C` for a contraction `C`. No compactness or closed-range hypothesis is used. -/
theorem exists_contractive_rectangular_rightFactor_of_gram_sub_gram_isPositive
    (A : E →L[ℂ] G) (B : F →L[ℂ] G)
    (hpos : (B ∘L adjoint B - A ∘L adjoint A).IsPositive) :
    ∃ C : E →L[ℂ] F, ‖C‖ ≤ 1 ∧ A = B ∘L C := by
  let Bstar : G →L[ℂ] F := adjoint B
  let Astar : G →L[ℂ] E := adjoint A
  let N : Submodule ℂ F := LinearMap.range Bstar.toLinearMap
  let M : Submodule ℂ F := N.topologicalClosure
  let i : N →L[ℂ] M := N.subtypeL.codRestrict M
    (fun x => N.le_topologicalClosure x.property)
  let rB : G →L[ℂ] N := Bstar.rangeRestrict
  let eL : G →L[ℂ] M := i ∘L rB
  let e : G →ₗ[ℂ] M := eL.toLinearMap
  have hi : DenseRange i := by
    change DenseRange (Set.inclusion N.le_topologicalClosure)
    apply (denseRange_inclusion_iff N.le_topologicalClosure).2
    simpa only [M, Submodule.topologicalClosure_coe] using
      (subset_rfl : closure (N : Set F) ⊆ closure (N : Set F))
  have hrB : DenseRange rB :=
    (LinearMap.surjective_rangeRestrict Bstar.toLinearMap).denseRange
  have heL : DenseRange eL := hi.comp hrB i.continuous
  have he : DenseRange e := heL
  have hbound : ∀ y : G, ‖Astar y‖ ≤ (1 : ℝ) * ‖e y‖ := by
    intro y
    rw [one_mul]
    change ‖adjoint A y‖ ≤ ‖adjoint B y‖
    exact adjoint_norm_le_of_rectangular_gram_sub_gram_isPositive A B hpos y
  let D : M →L[ℂ] E := Astar.toLinearMap.extendOfNorm e
  have hD : ‖D‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le he zero_le_one hbound
  let P : F →L[ℂ] M := M.orthogonalProjectionOnto
  let Dfull : F →L[ℂ] E := D ∘L P
  have hDfull : ‖Dfull‖ ≤ 1 := by
    calc
      ‖Dfull‖ ≤ ‖D‖ * ‖P‖ := D.opNorm_comp_le P
      _ ≤ 1 * 1 := mul_le_mul hD M.orthogonalProjectionOnto_norm_le
        (norm_nonneg P) zero_le_one
      _ = 1 := one_mul 1
  have hcomp : Dfull ∘L Bstar = Astar := by
    apply ContinuousLinearMap.ext
    intro y
    change D (M.orthogonalProjectionOnto (Bstar y)) = Astar y
    have hmem : Bstar y ∈ M :=
      N.le_topologicalClosure (LinearMap.mem_range_self Bstar.toLinearMap y)
    have hproj : M.orthogonalProjectionOnto (Bstar y) = e y := by
      have hfix := M.orthogonalProjectionOnto_mem_subspace_eq_self
        (⟨Bstar y, hmem⟩ : M)
      exact hfix
    rw [hproj]
    exact LinearMap.extendOfNorm_eq he ⟨1, hbound⟩ y
  let C : E →L[ℂ] F := adjoint Dfull
  refine ⟨C, ?_, ?_⟩
  · change ‖adjoint Dfull‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact hDfull
  · have hadj := congrArg adjoint hcomp
    rw [adjoint_comp, adjoint_adjoint, adjoint_adjoint] at hadj
    exact hadj.symm

end RectangularDouglas

/-! ## Exact infinite-dimensional Bures incidence identity -/

section RectangularBuresIncidence

variable {E F H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Range covariance `T T†` of an arbitrary rectangular synthesis map. -/
noncomputable def rangeCovariance (T : E →L[ℂ] H) : H →L[ℂ] H :=
  T ∘L adjoint T

/-- Positive covariance square root. -/
noncomputable def rangeCovarianceRoot (T : E →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt (rangeCovariance T)

/-- Every range covariance is positive. -/
theorem rangeCovariance_isPositive (T : E →L[ℂ] H) :
    (rangeCovariance T).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint T

theorem rangeCovariance_nonneg (T : E →L[ℂ] H) :
    0 ≤ rangeCovariance T :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).2 (rangeCovariance_isPositive T)

theorem rangeCovarianceRoot_adjoint (T : E →L[ℂ] H) :
    adjoint (rangeCovarianceRoot T) = rangeCovarianceRoot T := by
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (rangeCovariance T))

theorem rangeCovarianceRoot_comp_self (T : E →L[ℂ] H) :
    rangeCovarianceRoot T ∘L rangeCovarianceRoot T = rangeCovariance T := by
  exact CFC.sqrt_mul_sqrt_self (rangeCovariance T) (rangeCovariance_nonneg T)

omit [CompleteSpace H] in
private theorem zero_operator_isPositive :
    (0 : H →L[ℂ] H).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).1 le_rfl

/-- A synthesis map factors contractively through its covariance square root. -/
theorem exists_factor_through_rangeCovarianceRoot (T : E →L[ℂ] H) :
    ∃ R : E →L[ℂ] H, ‖R‖ ≤ 1 ∧ T = rangeCovarianceRoot T ∘L R := by
  have hgram : rangeCovarianceRoot T ∘L adjoint (rangeCovarianceRoot T) =
      T ∘L adjoint T := by
    rw [rangeCovarianceRoot_adjoint, rangeCovarianceRoot_comp_self, rangeCovariance]
  apply exists_contractive_rectangular_rightFactor_of_gram_sub_gram_isPositive
  rw [hgram, sub_self]
  exact zero_operator_isPositive

/-- Conversely, the covariance square root factors contractively through its synthesis map. -/
theorem exists_rangeCovarianceRoot_factor_through (T : E →L[ℂ] H) :
    ∃ S : H →L[ℂ] E, ‖S‖ ≤ 1 ∧ rangeCovarianceRoot T = T ∘L S := by
  have hgram : T ∘L adjoint T =
      rangeCovarianceRoot T ∘L adjoint (rangeCovarianceRoot T) := by
    rw [rangeCovarianceRoot_adjoint, rangeCovarianceRoot_comp_self, rangeCovariance]
  apply exists_contractive_rectangular_rightFactor_of_gram_sub_gram_isPositive
  rw [hgram, sub_self]
  exact zero_operator_isPositive

/-- Sheet--target incidence operator `U†V`; source sheets remain separate source coordinates. -/
noncomputable def sheetTargetIncidence (U : E →L[ℂ] H) (V : F →L[ℂ] H) :
    F →L[ℂ] E := adjoint U ∘L V

/-- Product of the two covariance square roots. -/
noncomputable def covarianceRootProduct (U : E →L[ℂ] H) (V : F →L[ℂ] H) :
    H →L[ℂ] H := rangeCovarianceRoot U ∘L rangeCovarianceRoot V

/-- Operator Bures root fidelity, defined as the nuclear norm of `sqrt(C) sqrt(M)`. -/
noncomputable def operatorBuresRootFidelity (C M : H →L[ℂ] H) : ℝ :=
  traceNorm H (CFC.sqrt C ∘L CFC.sqrt M)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Mutual contractive sandwiches preserve every rectangular approximation number exactly. -/
theorem rectApproxNumber_eq_of_mutual_contractive_factorization
    {E' F' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
    {T : E →L[ℂ] F} {S : E' →L[ℂ] F'}
    (A : F' →L[ℂ] F) (B : E →L[ℂ] E')
    (C : F →L[ℂ] F') (D : E' →L[ℂ] E)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) (hD : ‖D‖ ≤ 1)
    (hT : T = A ∘L S ∘L B) (hS : S = C ∘L T ∘L D) (n : ℕ) :
    rectApproxNumber T n = rectApproxNumber S n := by
  apply le_antisymm
  · rw [hT]
    calc
      rectApproxNumber (A ∘L S ∘L B) n ≤
          rectApproxNumber (A ∘L S) n * ‖B‖ :=
        rectApproxNumber_comp_le_right (A ∘L S) B n
      _ ≤ (‖A‖ * rectApproxNumber S n) * ‖B‖ :=
        mul_le_mul_of_nonneg_right (rectApproxNumber_comp_le_left A S n) (norm_nonneg B)
      _ ≤ (1 * rectApproxNumber S n) * 1 :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right hA (rectApproxNumber_nonneg S n)) hB
          (norm_nonneg B)
          (mul_nonneg zero_le_one (rectApproxNumber_nonneg S n))
      _ = rectApproxNumber S n := by ring
  · rw [hS]
    calc
      rectApproxNumber (C ∘L T ∘L D) n ≤
          rectApproxNumber (C ∘L T) n * ‖D‖ :=
        rectApproxNumber_comp_le_right (C ∘L T) D n
      _ ≤ (‖C‖ * rectApproxNumber T n) * ‖D‖ :=
        mul_le_mul_of_nonneg_right (rectApproxNumber_comp_le_left C T n) (norm_nonneg D)
      _ ≤ (1 * rectApproxNumber T n) * 1 :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right hC (rectApproxNumber_nonneg T n)) hD
          (norm_nonneg D)
          (mul_nonneg zero_le_one (rectApproxNumber_nonneg T n))
      _ = rectApproxNumber T n := by ring

/-- **Infinite sheet--target singular-profile identity.** For arbitrary Hilbert synthesis maps,
every approximation number of `U†V` equals the corresponding approximation number of
`sqrt(UU†) sqrt(VV†)`. Thus zeros, nonzero singular values, and all multiplicities agree. -/
theorem rectApproxNumber_sheetTargetIncidence_eq_covarianceRootProduct
    (U : E →L[ℂ] H) (V : F →L[ℂ] H) (n : ℕ) :
    rectApproxNumber (sheetTargetIncidence U V) n =
      rectApproxNumber (covarianceRootProduct U V) n := by
  obtain ⟨RU, hRU, hU⟩ := exists_factor_through_rangeCovarianceRoot U
  obtain ⟨RV, hRV, hV⟩ := exists_factor_through_rangeCovarianceRoot V
  obtain ⟨SU, hSU, hCU⟩ := exists_rangeCovarianceRoot_factor_through U
  obtain ⟨SV, hSV, hCV⟩ := exists_rangeCovarianceRoot_factor_through V
  have hAdjRU : ‖adjoint RU‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hRU
  have hAdjSU : ‖adjoint SU‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hSU
  have hAdjU : adjoint U = adjoint RU ∘L rangeCovarianceRoot U := by
    have h := congrArg adjoint hU
    rw [adjoint_comp, rangeCovarianceRoot_adjoint] at h
    exact h
  have hK : sheetTargetIncidence U V =
      adjoint RU ∘L covarianceRootProduct U V ∘L RV := by
    unfold sheetTargetIncidence covarianceRootProduct
    calc
      adjoint U ∘L V = (adjoint RU ∘L rangeCovarianceRoot U) ∘L V :=
        congrArg (fun A => A ∘L V) hAdjU
      _ = (adjoint RU ∘L rangeCovarianceRoot U) ∘L
          (rangeCovarianceRoot V ∘L RV) :=
        congrArg (fun B => (adjoint RU ∘L rangeCovarianceRoot U) ∘L B) hV
      _ = adjoint RU ∘L (rangeCovarianceRoot U ∘L rangeCovarianceRoot V) ∘L RV := by
        ext x
        rfl
  have hCU' : rangeCovarianceRoot U = adjoint SU ∘L adjoint U := by
    have h := congrArg adjoint hCU
    rw [rangeCovarianceRoot_adjoint, adjoint_comp] at h
    exact h
  have hL : covarianceRootProduct U V =
      adjoint SU ∘L sheetTargetIncidence U V ∘L SV := by
    rw [covarianceRootProduct, hCU', hCV, sheetTargetIncidence]
    ext x
    rfl
  exact rectApproxNumber_eq_of_mutual_contractive_factorization
    (adjoint RU) RV (adjoint SU) SV hAdjRU hRV hAdjSU hSV hK hL n

/-- **Infinite incidence/Bures nuclear identity (INC2).** No rank, injectivity, finite-dimensional,
or closed-range assumption is required. -/
theorem rectTraceNorm_sheetTargetIncidence_eq_operatorBuresRootFidelity
    (U : E →L[ℂ] H) (V : F →L[ℂ] H) :
    rectTraceNorm F E (sheetTargetIncidence U V) =
      operatorBuresRootFidelity (rangeCovariance U) (rangeCovariance V) := by
  change rectTraceNorm F E (sheetTargetIncidence U V) =
    traceNorm H (covarianceRootProduct U V)
  rw [← rectTraceNorm_eq_traceNorm]
  unfold rectTraceNorm
  exact tsum_congr fun n =>
    rectApproxNumber_sheetTargetIncidence_eq_covarianceRootProduct U V n

/-- Trace-class status of incidence and Bures covariance-root product is equivalent. -/
theorem memRectSchattenClass_sheetTargetIncidence_iff_covarianceRootProduct
    (p : ℝ) (U : E →L[ℂ] H) (V : F →L[ℂ] H) :
    MemRectSchattenClass p (sheetTargetIncidence U V) ↔
      MemRectSchattenClass p (covarianceRootProduct U V) := by
  unfold MemRectSchattenClass
  simp_rw [rectApproxNumber_sheetTargetIncidence_eq_covarianceRootProduct U V]

/-- Hilbert--Schmidt source and target synthesis make the exact incidence operator trace class. -/
theorem sheetTargetIncidence_memRectSchattenClass_one_of_hilbertSchmidt
    {U : E →L[ℂ] H} {V : F →L[ℂ] H}
    (hU : U.IsHilbertSchmidt) (hV : V.IsHilbertSchmidt) :
    MemRectSchattenClass 1 (sheetTargetIncidence U V) := by
  exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hV hU.adjoint

/-- Under the paper's separable Hilbert--Schmidt hypotheses, the covariance-root product is also
trace class, with the same complete singular profile. -/
theorem covarianceRootProduct_memSchattenClass_one_of_hilbertSchmidt
    {U : E →L[ℂ] H} {V : F →L[ℂ] H}
    (hU : U.IsHilbertSchmidt) (hV : V.IsHilbertSchmidt) :
    MemSchattenClass 1 (covarianceRootProduct U V) := by
  rw [← memRectSchattenClass_iff_memSchattenClass]
  exact (memRectSchattenClass_sheetTargetIncidence_iff_covarianceRootProduct 1 U V).1
    (sheetTargetIncidence_memRectSchattenClass_one_of_hilbertSchmidt hU hV)

end RectangularBuresIncidence

/-! ## Bochner `L²` synthesis and exact incidence kernels -/

section L2BuresIncidence

open MeasureTheory
open scoped ENNReal

variable {X Y H : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- The Riesz-dual field of a Bochner `L²` vector field.  The construction is valid for an
arbitrary measure; no finite-measure or sigma-finiteness premise is needed. -/
omit [CompleteSpace H] in
private theorem l2DualField_memLp (μ : Measure X) (u : Lp H 2 μ) :
    MemLp (fun x => InnerProductSpace.toDualMap ℂ H (u x)) 2 μ := by
  apply (Lp.memLp u).congr_norm
  · exact (InnerProductSpace.toDualMap ℂ H).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)
  · exact Filter.Eventually.of_forall fun x =>
      ((InnerProductSpace.toDualMap ℂ H).norm_map (u x)).symm

/-- Square-integrable field of Riesz functionals `x ↦ ⟪u(x), ·⟫`. -/
noncomputable def l2DualField (μ : Measure X) (u : Lp H 2 μ) :
    Lp (H →L[ℂ] ℂ) 2 μ :=
  (l2DualField_memLp μ u).toLp
    (fun x => InnerProductSpace.toDualMap ℂ H (u x))

/- The dual field has its intended pointwise representative almost everywhere. -/
omit [CompleteSpace H] in
theorem l2DualField_coeFn (μ : Measure X) (u : Lp H 2 μ) :
    (l2DualField μ u : X → H →L[ℂ] ℂ) =ᵐ[μ]
      fun x => InnerProductSpace.toDualMap ℂ H (u x) := by
  exact MemLp.coeFn_toLp _

/-- Pointwise evaluation, bilinear in a continuous functional and its argument. -/
def dualEvaluation : (H →L[ℂ] ℂ) →L[ℂ] H →L[ℂ] ℂ :=
  ContinuousLinearMap.flip (ContinuousLinearMap.apply ℂ ℂ)

/- A constant function belongs to `L∞` for an arbitrary measure.  Mathlib's bundled `Lp.const`
currently carries a finite-measure premise because it is uniform in the exponent; the endpoint
`p=∞` needs no such premise. -/
omit [InnerProductSpace ℂ H] [CompleteSpace H] in
private theorem constant_memLp_top (μ : Measure X) (v : H) :
    MemLp (fun _ : X => v) ∞ μ := by
  exact memLp_top_of_bound aestronglyMeasurable_const ‖v‖
    (Filter.Eventually.of_forall fun _ => le_rfl)

/-- Arbitrary-measure constant embedding into `L∞`. -/
noncomputable def lInfConstLinear (μ : Measure X) : H →ₗ[ℂ] Lp H ∞ μ where
  toFun v := (constant_memLp_top μ v).toLp (fun _ => v)
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

/- The arbitrary-measure constant embedding has its intended representative. -/
omit [CompleteSpace H] in
theorem lInfConstLinear_coeFn (μ : Measure X) (v : H) :
    (lInfConstLinear μ v : X → H) =ᵐ[μ] fun _ => v := by
  change ((constant_memLp_top μ v).toLp (fun _ : X => v) : X → H) =ᵐ[μ] fun _ => v
  exact MemLp.coeFn_toLp (constant_memLp_top μ v)

/- Constant `L∞` embedding is contractive, including for the zero measure. -/
omit [CompleteSpace H] in
theorem norm_lInfConstLinear_le (μ : Measure X) (v : H) :
    ‖lInfConstLinear μ v‖ ≤ ‖v‖ := by
  change ‖(constant_memLp_top μ v).toLp (fun _ : X => v)‖ ≤ ‖v‖
  rw [Lp.norm_toLp]
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [eLpNorm_const v (by simp) hμ]
    simp

/-- Arbitrary-measure constant embedding as a continuous linear map. -/
noncomputable def lInfConstL (μ : Measure X) : H →L[ℂ] Lp H ∞ μ :=
  LinearMap.mkContinuous (lInfConstLinear μ) 1 fun v => by
    simpa only [one_mul] using norm_lInfConstLinear_le μ v

/-- Analysis map of a Bochner `L²` field: `v ↦ (x ↦ ⟪u(x),v⟫)`.

Unlike the older finite-measure kernel-operator wrapper, this definition works for every measure:
the constant argument belongs to `L∞`, and Hölder sends `L² · L∞` to `L²`. -/
noncomputable def l2ObserverAnalysis (μ : Measure X) (u : Lp H 2 μ) :
    H →L[ℂ] Lp ℂ 2 μ :=
  ((dualEvaluation (H := H)).holderL μ 2 ∞ 2 (l2DualField μ u)) ∘L
    lInfConstL μ

/- Exact almost-everywhere analysis kernel. -/
omit [CompleteSpace H] in
theorem l2ObserverAnalysis_coeFn (μ : Measure X) (u : Lp H 2 μ) (v : H) :
    (l2ObserverAnalysis μ u v : X → ℂ) =ᵐ[μ]
      fun x => inner ℂ (u x) v := by
  have hholder := (dualEvaluation (H := H)).coeFn_holder
    (r := (2 : ENNReal)) (l2DualField μ u) (lInfConstLinear μ v)
  have hconst := lInfConstLinear_coeFn μ v
  filter_upwards [hholder, l2DualField_coeFn μ u, hconst] with x hh hu hv
  change ((dualEvaluation (H := H)).holder 2 (l2DualField μ u)
    (lInfConstLinear μ v) : X → ℂ) x = inner ℂ (u x) v
  rw [hh, hu, hv]
  rfl

/-- **Measure-universal Hilbert--Schmidt analysis law.** Every Bochner `L²` field induces a
Hilbert--Schmidt observer analysis map.  The proof uses finite Bessel sums, so it requires neither
separability nor a finite underlying measure. -/
theorem l2ObserverAnalysis_isHilbertSchmidt (μ : Measure X) (u : Lp H 2 μ) :
    (l2ObserverAnalysis μ u).IsHilbertSchmidt := by
  let b := ContinuousLinearMap.hsBasis ℂ H
  show Summable (fun i => ‖l2ObserverAnalysis μ u (b i)‖ ^ 2)
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := ‖u‖ ^ 2)
  intro s
  simp_rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  rw [← integral_finsetSum]
  · apply integral_mono_ae
    · exact integrable_finsetSum s fun i _ =>
        (memLp_two_iff_integrable_sq_norm
          (Lp.aestronglyMeasurable (l2ObserverAnalysis μ u (b i)))).mp
          (Lp.memLp (l2ObserverAnalysis μ u (b i)))
    · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp
        (Lp.memLp u)
    · have hall : ∀ᵐ x ∂μ, ∀ i ∈ s,
          l2ObserverAnalysis μ u (b i) x = inner ℂ (u x) (b i) := by
        rw [Finset.eventually_all]
        intro i hi
        exact l2ObserverAnalysis_coeFn μ u (b i)
      filter_upwards [hall] with x hx
      calc
        ∑ i ∈ s, ‖l2ObserverAnalysis μ u (b i) x‖ ^ 2 =
            ∑ i ∈ s, ‖inner ℂ (u x) (b i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hx i hi]
        _ = ∑ i ∈ s, ‖inner ℂ (b i) (u x)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_inner_symm]
        _ ≤ ‖u x‖ ^ 2 := b.orthonormal.sum_inner_products_le (u x)
  · intro i hi
    exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (l2ObserverAnalysis μ u (b i)))).mp
      (Lp.memLp (l2ObserverAnalysis μ u (b i)))

/-- **Exact analysis energy.** On a separable Hilbert carrier, Parseval and monotone integration
identify the Hilbert--Schmidt energy with the complete Bochner `L²` energy. -/
theorem hsNormSq_l2ObserverAnalysis_eq_norm_sq
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ) :
    ContinuousLinearMap.hsNormSq (l2ObserverAnalysis μ u) = ‖u‖ ^ 2 := by
  let b := ContinuousLinearMap.hsBasis ℂ H
  letI : Countable (exists_hilbertBasis ℂ H).choose :=
    b.orthonormal.countable_index
  have hT := l2ObserverAnalysis_isHilbertSchmidt μ u
  have hint (i) : Integrable (fun x => ‖inner ℂ (u x) (b i)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm ((Lp.memLp u).inner_const (b i)).1).mp
      ((Lp.memLp u).inner_const (b i))
  have hnorm (i) : ‖l2ObserverAnalysis μ u (b i)‖ ^ 2 =
      ∫ x, ‖inner ℂ (u x) (b i)‖ ^ 2 ∂μ := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [l2ObserverAnalysis_coeFn μ u (b i)] with x hx
    rw [hx]
  have hsum : Summable (fun i => ∫ x, ‖inner ℂ (u x) (b i)‖ ^ 2 ∂μ) := by
    exact (hT.summable b).congr hnorm
  have hsumNorm : Summable
      (fun i => ∫ x, ‖‖inner ℂ (u x) (b i)‖ ^ 2‖ ∂μ) := by
    refine hsum.congr (fun i => ?_)
    apply integral_congr_ae
    filter_upwards with x
    exact (Real.norm_of_nonneg (sq_nonneg ‖inner ℂ (u x) (b i)‖)).symm
  rw [ContinuousLinearMap.hsNormSq_eq hT b]
  calc
    ∑' i, ‖l2ObserverAnalysis μ u (b i)‖ ^ 2 =
        ∑' i, ∫ x, ‖inner ℂ (u x) (b i)‖ ^ 2 ∂μ := by
      exact tsum_congr hnorm
    _ = ∫ x, ∑' i, ‖inner ℂ (u x) (b i)‖ ^ 2 ∂μ :=
      integral_tsum_of_summable_integral_norm hint hsumNorm
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      calc
        ∑' i, ‖inner ℂ (u x) (b i)‖ ^ 2 =
            ∑' i, ‖inner ℂ (b i) (u x)‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [norm_inner_symm]
        _ = ‖u x‖ ^ 2 := b.tsum_norm_inner_sq (u x)
    _ = ‖u‖ ^ 2 := (HTGeometry.norm_l2_sq_eq_integral_norm_sq μ u).symm

/-- Bochner synthesis `f ↦ ∫ x, f(x) • u(x)`. -/
noncomputable def l2Synthesis (μ : Measure X) (u : Lp H 2 μ) :
    Lp ℂ 2 μ →L[ℂ] H :=
  ContinuousLinearMap.flip
    ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).lpPairing μ 2 2) u

/-- Synthesis is exactly the Bochner integral of the scalar-weighted field. -/
theorem l2Synthesis_apply (μ : Measure X) (u : Lp H 2 μ) (f : Lp ℂ 2 μ) :
    l2Synthesis μ u f = ∫ x, f x • u x ∂μ := by
  change (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).lpPairing μ 2 2 f u = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- Riesz analysis and Bochner synthesis are exact Hilbert adjoints. -/
theorem adjoint_l2ObserverAnalysis (μ : Measure X) (u : Lp H 2 μ) :
    adjoint (l2ObserverAnalysis μ u) = l2Synthesis μ u := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, MeasureTheory.L2.inner_def,
    l2Synthesis_apply]
  have hint : Integrable (fun x => f x • u x) μ := by
    exact memLp_one_iff_integrable.mp ((Lp.memLp u).smul (Lp.memLp f))
  rw [← integral_inner hint v]
  apply integral_congr_ae
  filter_upwards [l2ObserverAnalysis_coeFn μ u v] with x hx
  rw [hx]
  simp [RCLike.inner_apply, inner_smul_right, inner_conj_symm, mul_comm]

/-- The synthesis map is Hilbert--Schmidt for every Bochner `L²` field. -/
theorem l2Synthesis_isHilbertSchmidt (μ : Measure X) (u : Lp H 2 μ) :
    (l2Synthesis μ u).IsHilbertSchmidt := by
  rw [← adjoint_l2ObserverAnalysis μ u]
  exact (l2ObserverAnalysis_isHilbertSchmidt μ u).adjoint

/-- Exact Hilbert--Schmidt energy of Bochner synthesis. -/
theorem hsNormSq_l2Synthesis_eq_norm_sq
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ) :
    ContinuousLinearMap.hsNormSq (l2Synthesis μ u) = ‖u‖ ^ 2 := by
  rw [← adjoint_l2ObserverAnalysis μ u,
    (l2ObserverAnalysis_isHilbertSchmidt μ u).hsNormSq_adjoint]
  exact hsNormSq_l2ObserverAnalysis_eq_norm_sq μ u

/-- The adjoint of synthesis is the pointwise observer analysis. -/
theorem adjoint_l2Synthesis (μ : Measure X) (u : Lp H 2 μ) :
    adjoint (l2Synthesis μ u) = l2ObserverAnalysis μ u := by
  rw [← adjoint_l2ObserverAnalysis μ u, adjoint_adjoint]

/-- Exact covariance action of a Bochner `L²` field. -/
theorem rangeCovariance_l2Synthesis_apply (μ : Measure X) (u : Lp H 2 μ) (v : H) :
    rangeCovariance (l2Synthesis μ u) v =
      ∫ x, inner ℂ (u x) v • u x ∂μ := by
  rw [rangeCovariance, ContinuousLinearMap.comp_apply, adjoint_l2Synthesis,
    l2Synthesis_apply]
  apply integral_congr_ae
  filter_upwards [l2ObserverAnalysis_coeFn μ u v] with x hx
  rw [hx]

/-- Covariance of every Bochner `L²` field is trace class. -/
theorem rangeCovariance_l2Synthesis_memSchattenClass_one
    (μ : Measure X) (u : Lp H 2 μ) :
    MemSchattenClass 1 (rangeCovariance (l2Synthesis μ u)) := by
  rw [← memRectSchattenClass_iff_memSchattenClass]
  exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
    (l2Synthesis_isHilbertSchmidt μ u).adjoint
    (l2Synthesis_isHilbertSchmidt μ u)

/-- Exact trace of the positive Bochner covariance: `Tr C = ∫ ‖u(x)‖² dμ`. -/
theorem re_opTrace_rangeCovariance_l2Synthesis_eq_norm_sq
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ) :
    Complex.re (ContinuousLinearMap.opTrace (rangeCovariance (l2Synthesis μ u))) =
      ‖u‖ ^ 2 := by
  let U := l2Synthesis μ u
  have hU : U.IsHilbertSchmidt := l2Synthesis_isHilbertSchmidt μ u
  calc
    Complex.re (ContinuousLinearMap.opTrace (rangeCovariance U)) =
        ContinuousLinearMap.hsNormSq (adjoint U) := by
      rw [rangeCovariance]
      simpa using ContinuousLinearMap.re_opTrace_adjoint_comp_self hU.adjoint
    _ = ContinuousLinearMap.hsNormSq U := hU.hsNormSq_adjoint
    _ = ‖u‖ ^ 2 := hsNormSq_l2Synthesis_eq_norm_sq μ u

/-- Concrete sheet--target incidence between two arbitrary Bochner `L²` fields. -/
noncomputable def l2SheetTargetIncidence
    (μ : Measure X) (ν : Measure Y) (u : Lp H 2 μ) (v : Lp H 2 ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  sheetTargetIncidence (l2Synthesis μ u) (l2Synthesis ν v)

/-- **Exact Bochner incidence kernel (INC1).** The source coordinate is not pushed forward or
quotiented: every source sheet remains a separate `L²(X,μ)` coordinate. -/
theorem l2SheetTargetIncidence_coeFn
    (μ : Measure X) (ν : Measure Y) (u : Lp H 2 μ) (v : Lp H 2 ν)
    (g : Lp ℂ 2 ν) :
    (l2SheetTargetIncidence μ ν u v g : X → ℂ) =ᵐ[μ]
      fun x => ∫ y, g y * inner ℂ (u x) (v y) ∂ν := by
  have hint : Integrable (fun y => g y • v y) ν := by
    exact memLp_one_iff_integrable.mp ((Lp.memLp v).smul (Lp.memLp g))
  have hsource := l2ObserverAnalysis_coeFn μ u (l2Synthesis ν v g)
  filter_upwards [hsource] with x hx
  rw [l2SheetTargetIncidence, sheetTargetIncidence,
    ContinuousLinearMap.comp_apply, adjoint_l2Synthesis, hx,
    l2Synthesis_apply, ← integral_inner hint]
  apply integral_congr_ae
  filter_upwards with y
  simp [inner_smul_right, mul_comm]

/-- **Concrete infinite incidence/Bures identity (INC2).** It is unconditional for arbitrary
Bochner `L²` source and target fields; separability is unnecessary for the identity itself. -/
theorem rectTraceNorm_l2SheetTargetIncidence_eq_operatorBuresRootFidelity
    (μ : Measure X) (ν : Measure Y) (u : Lp H 2 μ) (v : Lp H 2 ν) :
    rectTraceNorm (Lp ℂ 2 ν) (Lp ℂ 2 μ)
        (l2SheetTargetIncidence μ ν u v) =
      operatorBuresRootFidelity
        (rangeCovariance (l2Synthesis μ u))
        (rangeCovariance (l2Synthesis ν v)) := by
  exact rectTraceNorm_sheetTargetIncidence_eq_operatorBuresRootFidelity
    (l2Synthesis μ u) (l2Synthesis ν v)

/-- The concrete Bochner incidence kernel is trace class in rectangular Schatten sense. -/
theorem l2SheetTargetIncidence_memRectSchattenClass_one
    (μ : Measure X) (ν : Measure Y) (u : Lp H 2 μ) (v : Lp H 2 ν) :
    MemRectSchattenClass 1 (l2SheetTargetIncidence μ ν u v) := by
  exact sheetTargetIncidence_memRectSchattenClass_one_of_hilbertSchmidt
    (l2Synthesis_isHilbertSchmidt μ u) (l2Synthesis_isHilbertSchmidt ν v)

/-- The covariance-root product associated with two Bochner `L²` fields is trace class. -/
theorem l2CovarianceRootProduct_memSchattenClass_one
    (μ : Measure X) (ν : Measure Y) (u : Lp H 2 μ) (v : Lp H 2 ν) :
    MemSchattenClass 1
      (covarianceRootProduct (l2Synthesis μ u) (l2Synthesis ν v)) := by
  exact covarianceRootProduct_memSchattenClass_one_of_hilbertSchmidt
    (l2Synthesis_isHilbertSchmidt μ u) (l2Synthesis_isHilbertSchmidt ν v)

end L2BuresIncidence

end RHTower
