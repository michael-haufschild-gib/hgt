import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-!
# The Hilbert space of Hilbert–Schmidt operators

The Hilbert–Schmidt operators on a Hilbert space `E` form a Hilbert space `HSpace 𝕜 E` under the
inner product `⟨S, T⟩ = ∑ᵢ ⟨S eᵢ, T eᵢ⟩`.  The type is a synonym for the underlying submodule of
`E →L[𝕜] E`, so it does not inherit the operator norm; the norm is the Hilbert–Schmidt norm.
Completeness follows from `exists_hsNorm_limit`: a Hilbert–Schmidt Cauchy sequence is Cauchy in
the operator norm, and its operator-norm limit is Hilbert–Schmidt by the Fatou lemma.
-/

open scoped BigOperators InnerProductSpace
open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The Hilbert–Schmidt operators as a submodule of the bounded operators. -/
def hsSubmodule : Submodule 𝕜 (E →L[𝕜] E) where
  carrier := {T | IsHilbertSchmidt T}
  add_mem' h1 h2 := IsHilbertSchmidt.add h1 h2
  zero_mem' := isHilbertSchmidt_zero
  smul_mem' c _ h := IsHilbertSchmidt.smul h c

/-- The Hilbert space of Hilbert–Schmidt operators. -/
def HSpace : Type _ := ↥(hsSubmodule 𝕜 E)

namespace HSpace

variable {𝕜 E}

instance : AddCommGroup (HSpace 𝕜 E) := inferInstanceAs (AddCommGroup ↥(hsSubmodule 𝕜 E))
instance : Module 𝕜 (HSpace 𝕜 E) := inferInstanceAs (Module 𝕜 ↥(hsSubmodule 𝕜 E))

/-- The underlying bounded operator. -/
def op (S : HSpace 𝕜 E) : E →L[𝕜] E := (S : ↥(hsSubmodule 𝕜 E)).1

lemma isHS (S : HSpace 𝕜 E) : IsHilbertSchmidt S.op := (S : ↥(hsSubmodule 𝕜 E)).2

/-- Package a Hilbert–Schmidt operator. -/
def mk (T : E →L[𝕜] E) (hT : IsHilbertSchmidt T) : HSpace 𝕜 E := ⟨T, hT⟩

@[simp] lemma op_mk (T : E →L[𝕜] E) (hT : IsHilbertSchmidt T) : (mk T hT).op = T := rfl

@[ext] lemma ext {S T : HSpace 𝕜 E} (h : S.op = T.op) : S = T := Subtype.ext h

lemma op_injective : Function.Injective (op : HSpace 𝕜 E → E →L[𝕜] E) := fun _ _ h => ext h

@[simp] lemma op_add (S T : HSpace 𝕜 E) : (S + T).op = S.op + T.op := rfl
@[simp] lemma op_zero : (0 : HSpace 𝕜 E).op = 0 := rfl
@[simp] lemma op_neg (S : HSpace 𝕜 E) : (-S).op = -S.op := rfl
@[simp] lemma op_sub (S T : HSpace 𝕜 E) : (S - T).op = S.op - T.op := rfl
@[simp] lemma op_smul (c : 𝕜) (S : HSpace 𝕜 E) : (c • S).op = c • S.op := rfl

/-- The Hilbert–Schmidt norm as a group norm. -/
noncomputable def hsAddGroupNorm : AddGroupNorm (HSpace 𝕜 E) where
  toFun S := hsNorm S.op
  map_zero' := by simp only [op_zero]; exact hsNorm_zero
  add_le' S T := by
    simp only [op_add]
    exact hsNorm_add_le S.isHS T.isHS
  neg' S := by
    simp only [op_neg]
    show Real.sqrt (hsNormSq (-S.op)) = Real.sqrt (hsNormSq S.op)
    rw [hsNormSq_neg_eq_self]
  eq_zero_of_map_eq_zero' S h := by
    refine ext ?_
    rw [op_zero]
    exact (hsNorm_eq_zero_iff S.isHS).mp h

noncomputable instance : NormedAddCommGroup (HSpace 𝕜 E) :=
  AddGroupNorm.toNormedAddCommGroup hsAddGroupNorm

@[simp] lemma norm_def (S : HSpace 𝕜 E) : ‖S‖ = hsNorm S.op := rfl

noncomputable instance : InnerProductSpace 𝕜 (HSpace 𝕜 E) :=
  { inner := fun S T => hsInner S.op T.op
    norm_smul_le := fun c S => by
      simp only [norm_def, op_smul]
      exact le_of_eq (hsNorm_smul c S.op)
    norm_sq_eq_re_inner := fun S => by
      show (hsNorm S.op) ^ (2 : ℕ) = RCLike.re (hsInner S.op S.op)
      rw [sq_hsNorm, hsInner_self_re S.isHS]
    conj_inner_symm := fun S T => (hsInner_conj_symm S.op T.op).symm
    add_left := fun S T U => by
      show hsInner (S + T).op U.op = hsInner S.op U.op + hsInner T.op U.op
      rw [op_add]
      exact hsInner_add_left S.isHS T.isHS U.isHS
    smul_left := fun S T c => by
      show hsInner (c • S).op T.op = starRingEnd 𝕜 c * hsInner S.op T.op
      rw [op_smul]
      exact hsInner_smul_left c S.op T.op }

@[simp] lemma inner_def (S T : HSpace 𝕜 E) :
    (inner 𝕜 S T : 𝕜) = hsInner S.op T.op := rfl

/-- **The Hilbert–Schmidt operators form a complete space.** -/
instance : CompleteSpace (HSpace 𝕜 E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun Sn hSn => ?_
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hsNorm ((Sn m).op - (Sn n).op) ≤ ε := by
    intro ε hε
    rw [Metric.cauchySeq_iff] at hSn
    obtain ⟨N, hN⟩ := hSn (ε/2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm] at h
    have hval : ‖Sn m - Sn n‖ = hsNorm ((Sn m).op - (Sn n).op) := by
      rw [norm_def, op_sub]
    rw [hval] at h
    linarith
  obtain ⟨T, hTHS, hTlim⟩ :=
    exists_hsNorm_limit (fun n => (Sn n).isHS) hcauchy
  refine ⟨mk T hTHS, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hTlim
  obtain ⟨N, hN⟩ := hTlim ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _)] at h
  rw [dist_eq_norm, norm_def, op_sub, op_mk]
  exact h

end HSpace

end GaloisForLFunctions.HTGeometry
