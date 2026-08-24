import GaloisForLFunctions.HTGeometry.CommutingProjectionIntersectionEnergy
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Closed relations between disjoint Hilbert-space operator families
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

noncomputable section

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- Orthogonal Hilbert sum of two possibly different Hilbert spaces. -/
abbrev HilbertSum (H₁ H₂ : Type*) := WithLp 2 (H₁ × H₂)

/-- First coordinate of an orthogonal Hilbert sum. -/
def hilbertSumFst : HilbertSum H₁ H₂ →L[ℂ] H₁ :=
  (ContinuousLinearMap.fst ℂ H₁ H₂) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap

/-- Second coordinate of an orthogonal Hilbert sum. -/
def hilbertSumSnd : HilbertSum H₁ H₂ →L[ℂ] H₂ :=
  (ContinuousLinearMap.snd ℂ H₁ H₂) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap

/-- Inclusion of the first summand. -/
def hilbertSumInl : H₁ →L[ℂ] HilbertSum H₁ H₂ :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ H₁ H₂

/-- Inclusion of the second summand. -/
def hilbertSumInr : H₂ →L[ℂ] HilbertSum H₁ H₂ :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ H₁ H₂

@[simp] theorem hilbertSumFst_apply (x : HilbertSum H₁ H₂) : hilbertSumFst x = x.ofLp.1 := rfl
@[simp] theorem hilbertSumSnd_apply (x : HilbertSum H₁ H₂) : hilbertSumSnd x = x.ofLp.2 := rfl
@[simp] theorem hilbertSumFst_inl (x : H₁) : hilbertSumFst (hilbertSumInl x : HilbertSum H₁ H₂) = x := rfl
@[simp] theorem hilbertSumSnd_inl (x : H₁) : hilbertSumSnd (hilbertSumInl x : HilbertSum H₁ H₂) = 0 := rfl
@[simp] theorem hilbertSumFst_inr (y : H₂) : hilbertSumFst (hilbertSumInr y : HilbertSum H₁ H₂) = 0 := rfl
@[simp] theorem hilbertSumSnd_inr (y : H₂) : hilbertSumSnd (hilbertSumInr y : HilbertSum H₁ H₂) = y := rfl

theorem hilbertSum_ext {x y : HilbertSum H₁ H₂}
    (hfst : hilbertSumFst x = hilbertSumFst y)
    (hsnd : hilbertSumSnd x = hilbertSumSnd y) : x = y := by
  have hpair : x.ofLp = y.ofLp := Prod.ext hfst hsnd
  calc
    x = WithLp.toLp 2 x.ofLp := rfl
    _ = WithLp.toLp 2 y.ofLp := by rw [hpair]
    _ = y := rfl

theorem hilbertSum_inl_add_inr (z : HilbertSum H₁ H₂) :
    hilbertSumInl (hilbertSumFst z) + hilbertSumInr (hilbertSumSnd z) = z := by
  apply hilbertSum_ext
  · rw [map_add, hilbertSumFst_inl, hilbertSumFst_inr, add_zero]
  · rw [map_add, hilbertSumSnd_inl, hilbertSumSnd_inr, zero_add]

/-- Block-diagonal bounded operator on an orthogonal Hilbert sum. -/
def hilbertBlockDiagonal (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) :
    HilbertSum H₁ H₂ →L[ℂ] HilbertSum H₁ H₂ :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ((A.prodMap B) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap)

@[simp] theorem hilbertBlockDiagonal_fst (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (z : HilbertSum H₁ H₂) :
    hilbertSumFst (hilbertBlockDiagonal A B z) = A (hilbertSumFst z) := rfl

@[simp] theorem hilbertBlockDiagonal_snd (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (z : HilbertSum H₁ H₂) :
    hilbertSumSnd (hilbertBlockDiagonal A B z) = B (hilbertSumSnd z) := rfl

@[simp] theorem hilbertBlockDiagonal_inl (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (x : H₁) :
    hilbertBlockDiagonal A B (hilbertSumInl x) = hilbertSumInl (A x) := by
  apply hilbertSum_ext
  · change A x = A x
    rfl
  · change B 0 = 0
    simp

@[simp] theorem hilbertBlockDiagonal_inr (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (y : H₂) :
    hilbertBlockDiagonal A B (hilbertSumInr y) = hilbertSumInr (B y) := by
  apply hilbertSum_ext
  · change A 0 = 0
    simp
  · change B y = B y
    rfl

variable [CompleteSpace H₁] [CompleteSpace H₂]

theorem adjoint_hilbertBlockDiagonal (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) :
    (hilbertBlockDiagonal A B).adjoint = hilbertBlockDiagonal A.adjoint B.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change inner ℂ (A.adjoint x.ofLp.1) y.ofLp.1 +
      inner ℂ (B.adjoint x.ofLp.2) y.ofLp.2 =
    inner ℂ x.ofLp.1 (A y.ofLp.1) + inner ℂ x.ofLp.2 (B y.ofLp.2)
  rw [
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- Invariance under an operator and its adjoint makes a closed subspace reducing. -/
theorem starProjection_comm_of_invariant_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Submodule ℂ H) [R.HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hT : ∀ x ∈ R, T x ∈ R)
    (hTadj : ∀ x ∈ R, T.adjoint x ∈ R) :
    R.starProjection ∘L T = T ∘L R.starProjection := by
  have horth : ∀ y ∈ Rᗮ, T y ∈ Rᗮ := by
    intro y hy
    rw [Submodule.mem_orthogonal] at hy ⊢
    intro r hr
    calc
      inner ℂ r (T y) = inner ℂ (T.adjoint r) y :=
        (T.adjoint_inner_left y r).symm
      _ = 0 := hy _ (hTadj r hr)
  ext x
  have hp : R.starProjection x ∈ R := R.starProjection_apply_mem x
  have hq : x - R.starProjection x ∈ Rᗮ := R.sub_starProjection_mem_orthogonal x
  have hsplit : T x = T (R.starProjection x) + T (x - R.starProjection x) := by
    rw [← map_add]
    congr 1
    abel
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hsplit, map_add,
    Submodule.starProjection_eq_self_iff.mpr (hT _ hp),
    (Submodule.starProjection_apply_eq_zero_iff R).mpr (horth _ hq), add_zero]

/-- Two operator families are disjoint when every bounded intertwiner in either direction is zero. -/
def OperatorFamiliesDisjoint {I : Type*}
    (A : I → H₁ →L[ℂ] H₁) (B : I → H₂ →L[ℂ] H₂) : Prop :=
  (∀ V : H₁ →L[ℂ] H₂, (∀ i, V ∘L A i = B i ∘L V) → V = 0) ∧
  (∀ W : H₂ →L[ℂ] H₁, (∀ i, W ∘L B i = A i ∘L W) → W = 0)

/-- Off-diagonal lower block of an operator on a Hilbert sum. -/
def hilbertLowerBlock (P : HilbertSum H₁ H₂ →L[ℂ] HilbertSum H₁ H₂) : H₁ →L[ℂ] H₂ :=
  hilbertSumSnd ∘L P ∘L hilbertSumInl

/-- Off-diagonal upper block of an operator on a Hilbert sum. -/
def hilbertUpperBlock (P : HilbertSum H₁ H₂ →L[ℂ] HilbertSum H₁ H₂) : H₂ →L[ℂ] H₁ :=
  hilbertSumFst ∘L P ∘L hilbertSumInr

omit [CompleteSpace H₁] [CompleteSpace H₂] in
@[simp] theorem hilbertLowerBlock_apply
    (P : HilbertSum H₁ H₂ →L[ℂ] HilbertSum H₁ H₂) (x : H₁) :
    hilbertLowerBlock P x = hilbertSumSnd (P (hilbertSumInl x)) := rfl

omit [CompleteSpace H₁] [CompleteSpace H₂] in
@[simp] theorem hilbertUpperBlock_apply
    (P : HilbertSum H₁ H₂ →L[ℂ] HilbertSum H₁ H₂) (y : H₂) :
    hilbertUpperBlock P y = hilbertSumFst (P (hilbertSumInr y)) := rfl

/-- A closed relation invariant under two disjoint operator families splits coordinatewise. -/
theorem closedRelation_mem_iff_coordinate_mem_of_disjoint
    {I : Type*} (A : I → H₁ →L[ℂ] H₁) (B : I → H₂ →L[ℂ] H₂)
    (hdisj : OperatorFamiliesDisjoint A B)
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (hclosed : IsClosed (R : Set (HilbertSum H₁ H₂)))
    (hinv : ∀ i z, z ∈ R → hilbertBlockDiagonal (A i) (B i) z ∈ R)
    (hinvAdj : ∀ i z, z ∈ R →
      hilbertBlockDiagonal (A i).adjoint (B i).adjoint z ∈ R)
    (z : HilbertSum H₁ H₂) :
    z ∈ R ↔ hilbertSumInl (hilbertSumFst z) ∈ R ∧
      hilbertSumInr (hilbertSumSnd z) ∈ R := by
  letI : R.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hclosed
  let P : HilbertSum H₁ H₂ →L[ℂ] HilbertSum H₁ H₂ := R.starProjection
  have hcomm : ∀ i, P ∘L hilbertBlockDiagonal (A i) (B i) =
      hilbertBlockDiagonal (A i) (B i) ∘L P := by
    intro i
    apply starProjection_comm_of_invariant_adjoint R
    · exact hinv i
    · rw [adjoint_hilbertBlockDiagonal]
      exact hinvAdj i
  have hlowerIntertwines : ∀ i,
      hilbertLowerBlock P ∘L A i = B i ∘L hilbertLowerBlock P := by
    intro i
    ext x
    have hc := DFunLike.congr_fun (hcomm i) (hilbertSumInl x)
    simpa only [ContinuousLinearMap.comp_apply, hilbertLowerBlock_apply,
      hilbertBlockDiagonal_fst, hilbertBlockDiagonal_snd,
      hilbertBlockDiagonal_inl, hilbertSumFst_inl, hilbertSumSnd_inl] using
        congrArg hilbertSumSnd hc
  have hupperIntertwines : ∀ i,
      hilbertUpperBlock P ∘L B i = A i ∘L hilbertUpperBlock P := by
    intro i
    ext y
    have hc := DFunLike.congr_fun (hcomm i) (hilbertSumInr y)
    simpa only [ContinuousLinearMap.comp_apply, hilbertUpperBlock_apply,
      hilbertBlockDiagonal_fst, hilbertBlockDiagonal_snd,
      hilbertBlockDiagonal_inr, hilbertSumFst_inr, hilbertSumSnd_inr] using
        congrArg hilbertSumFst hc
  have hlower : hilbertLowerBlock P = 0 := hdisj.1 _ hlowerIntertwines
  have hupper : hilbertUpperBlock P = 0 := hdisj.2 _ hupperIntertwines
  have hlowerApply : ∀ x : H₁, hilbertSumSnd (P (hilbertSumInl x)) = 0 := by
    intro x
    have := DFunLike.congr_fun hlower x
    exact this
  have hupperApply : ∀ y : H₂, hilbertSumFst (P (hilbertSumInr y)) = 0 := by
    intro y
    have := DFunLike.congr_fun hupper y
    exact this
  constructor
  · intro hz
    have hpz : P z = z := Submodule.starProjection_eq_self_iff.mpr hz
    have hPdecomp : P (hilbertSumInl (hilbertSumFst z)) +
        P (hilbertSumInr (hilbertSumSnd z)) = z := by
      rw [← map_add, hilbertSum_inl_add_inr, hpz]
    have hleftFst : hilbertSumFst (P (hilbertSumInl (hilbertSumFst z))) =
        hilbertSumFst z := by
      have := congrArg hilbertSumFst hPdecomp
      rw [map_add, hupperApply, add_zero] at this
      exact this
    have hrightSnd : hilbertSumSnd (P (hilbertSumInr (hilbertSumSnd z))) =
        hilbertSumSnd z := by
      have := congrArg hilbertSumSnd hPdecomp
      rw [map_add, hlowerApply, zero_add] at this
      exact this
    have hleft : P (hilbertSumInl (hilbertSumFst z)) =
        hilbertSumInl (hilbertSumFst z) := by
      apply hilbertSum_ext
      · change hilbertSumFst (P (hilbertSumInl (hilbertSumFst z))) = hilbertSumFst z
        exact hleftFst
      · change hilbertSumSnd (P (hilbertSumInl (hilbertSumFst z))) = 0
        exact hlowerApply _
    have hright : P (hilbertSumInr (hilbertSumSnd z)) =
        hilbertSumInr (hilbertSumSnd z) := by
      apply hilbertSum_ext
      · change hilbertSumFst (P (hilbertSumInr (hilbertSumSnd z))) = 0
        exact hupperApply _
      · change hilbertSumSnd (P (hilbertSumInr (hilbertSumSnd z))) = hilbertSumSnd z
        exact hrightSnd
    constructor
    · rw [← hleft]
      exact R.starProjection_apply_mem _
    · rw [← hright]
      exact R.starProjection_apply_mem _
  · rintro ⟨hleft, hright⟩
    rw [← hilbertSum_inl_add_inr z]
    exact R.add_mem hleft hright

/-- Domain of a Hilbert-space linear relation. -/
def hilbertRelationDomain (R : Submodule ℂ (HilbertSum H₁ H₂)) : Submodule ℂ H₁ :=
  R.map hilbertSumFst.toLinearMap

/-- Single-valuedness of a Hilbert-space linear relation: its vertical fibre is zero. -/
def HilbertRelationSingleValued (R : Submodule ℂ (HilbertSum H₁ H₂)) : Prop :=
  ∀ y : H₂, hilbertSumInr y ∈ R → y = 0

/-- Existence of a genuinely coupled closed densely defined single-valued relation intertwining
two operator families. -/
def NonzeroClosedSourceLinearSewing {I : Type*}
    (A : I → H₁ →L[ℂ] H₁) (B : I → H₂ →L[ℂ] H₂) : Prop :=
  ∃ R : Submodule ℂ (HilbertSum H₁ H₂),
    IsClosed (R : Set (HilbertSum H₁ H₂)) ∧
    Dense (hilbertRelationDomain R : Set H₁) ∧
    HilbertRelationSingleValued R ∧
    (∀ i z, z ∈ R → hilbertBlockDiagonal (A i) (B i) z ∈ R) ∧
    ∃ z ∈ R, hilbertSumSnd z ≠ 0

/-- Graph of the identity operator, regarded as a closed Hilbert-space relation. -/
def hilbertDiagonalRelation (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Submodule ℂ (HilbertSum H H) :=
  LinearMap.ker ((hilbertSumSnd - hilbertSumFst : HilbertSum H H →L[ℂ] H).toLinearMap)

theorem mem_hilbertDiagonalRelation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (z : HilbertSum H H) :
    z ∈ hilbertDiagonalRelation H ↔ hilbertSumSnd z = hilbertSumFst z := by
  change hilbertSumSnd z - hilbertSumFst z = 0 ↔ _
  exact sub_eq_zero

theorem isClosed_hilbertDiagonalRelation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    IsClosed (hilbertDiagonalRelation H : Set (HilbertSum H H)) :=
  ContinuousLinearMap.isClosed_ker _

theorem hilbertDiagonalRelation_domain_eq_top
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    hilbertRelationDomain (hilbertDiagonalRelation H) = ⊤ := by
  apply top_unique
  intro x _
  rw [hilbertRelationDomain, Submodule.mem_map]
  refine ⟨hilbertSumInl x + hilbertSumInr x, ?_, ?_⟩
  · rw [mem_hilbertDiagonalRelation, map_add, map_add]
    change (0 : H) + x = x + 0
    simp
  · change x + 0 = x
    simp

theorem hilbertDiagonalRelation_singleValued
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    HilbertRelationSingleValued (hilbertDiagonalRelation H) := by
  intro y hy
  rw [mem_hilbertDiagonalRelation] at hy
  change y = 0 at hy
  exact hy

theorem hilbertDiagonalRelation_invariant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (z : HilbertSum H H) (hz : z ∈ hilbertDiagonalRelation H) :
    hilbertBlockDiagonal A A z ∈ hilbertDiagonalRelation H := by
  rw [mem_hilbertDiagonalRelation, hilbertBlockDiagonal_snd, hilbertBlockDiagonal_fst]
  exact congrArg A ((mem_hilbertDiagonalRelation z).mp hz)

/-- Every operator family has a nonzero closed source-linear sewing with itself as soon as its
Hilbert space is nonzero: the diagonal graph. -/
theorem nonzeroClosedSourceLinearSewing_self
    {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : I → H →L[ℂ] H) (u : H) (hu : u ≠ 0) :
    NonzeroClosedSourceLinearSewing A A := by
  refine ⟨hilbertDiagonalRelation H, isClosed_hilbertDiagonalRelation, ?_,
    hilbertDiagonalRelation_singleValued, ?_, ?_⟩
  · rw [hilbertDiagonalRelation_domain_eq_top]
    exact dense_univ
  · intro i z hz
    exact hilbertDiagonalRelation_invariant (A i) z hz
  · refine ⟨hilbertSumInl u + hilbertSumInr u, ?_, ?_⟩
    · rw [mem_hilbertDiagonalRelation, map_add, map_add]
      change (0 : H) + u = u + 0
      simp
    · rw [map_add]
      change (0 : H) + u ≠ 0
      simpa using hu

/-- A closed single-valued relation between disjoint families is exactly the zero operator on its
possibly nonclosed domain.  This version applies directly to operators on reducing
subrepresentations, without requiring their domain to be dense in the ambient representation. -/
theorem closedSingleValuedRelation_mem_iff_domain_and_output_zero_of_disjoint
    {I : Type*} (A : I → H₁ →L[ℂ] H₁) (B : I → H₂ →L[ℂ] H₂)
    (hdisj : OperatorFamiliesDisjoint A B)
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (hclosed : IsClosed (R : Set (HilbertSum H₁ H₂)))
    (hsingle : HilbertRelationSingleValued R)
    (hinv : ∀ i z, z ∈ R → hilbertBlockDiagonal (A i) (B i) z ∈ R)
    (hinvAdj : ∀ i z, z ∈ R →
      hilbertBlockDiagonal (A i).adjoint (B i).adjoint z ∈ R)
    (z : HilbertSum H₁ H₂) :
    z ∈ R ↔ hilbertSumFst z ∈ hilbertRelationDomain R ∧ hilbertSumSnd z = 0 := by
  have hsplit := closedRelation_mem_iff_coordinate_mem_of_disjoint
    A B hdisj R hclosed hinv hinvAdj
  constructor
  · intro hz
    constructor
    · rw [hilbertRelationDomain, Submodule.mem_map]
      exact ⟨z, hz, rfl⟩
    · exact hsingle _ ((hsplit z).mp hz).2
  · rintro ⟨hdom, hout⟩
    rw [hilbertRelationDomain, Submodule.mem_map] at hdom
    rcases hdom with ⟨w, hw, hfst⟩
    have hleft := (hsplit w).mp hw |>.1
    have hinl : hilbertSumInl (hilbertSumFst w) =
        (hilbertSumInl (hilbertSumFst z) : HilbertSum H₁ H₂) :=
      congrArg (fun x : H₁ => (hilbertSumInl x : HilbertSum H₁ H₂)) hfst
    rw [hinl] at hleft
    rw [← hilbertSum_inl_add_inr z, hout, map_zero, add_zero]
    exact hleft

/-- A closed, densely defined, single-valued relation between disjoint families is the full zero
graph.  This is the unbounded-operator corollary of closed-relation splitting. -/
theorem closedDenseSingleValuedRelation_mem_iff_output_eq_zero_of_disjoint
    {I : Type*} (A : I → H₁ →L[ℂ] H₁) (B : I → H₂ →L[ℂ] H₂)
    (hdisj : OperatorFamiliesDisjoint A B)
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (hclosed : IsClosed (R : Set (HilbertSum H₁ H₂)))
    (hdense : Dense (hilbertRelationDomain R : Set H₁))
    (hsingle : HilbertRelationSingleValued R)
    (hinv : ∀ i z, z ∈ R → hilbertBlockDiagonal (A i) (B i) z ∈ R)
    (hinvAdj : ∀ i z, z ∈ R →
      hilbertBlockDiagonal (A i).adjoint (B i).adjoint z ∈ R)
    (z : HilbertSum H₁ H₂) :
    z ∈ R ↔ hilbertSumSnd z = 0 := by
  have hsplit := closedRelation_mem_iff_coordinate_mem_of_disjoint
    A B hdisj R hclosed hinv hinvAdj
  have hdomainHorizontal (x : H₁) :
      x ∈ hilbertRelationDomain R ↔ hilbertSumInl x ∈ R := by
    constructor
    · intro hx
      rw [hilbertRelationDomain, Submodule.mem_map] at hx
      rcases hx with ⟨w, hw, hfst⟩
      have hleft := (hsplit w).mp hw |>.1
      have hinl : hilbertSumInl (hilbertSumFst w) = hilbertSumInl x :=
        congrArg (fun u : H₁ => (hilbertSumInl u : HilbertSum H₁ H₂)) hfst
      rw [← hinl]
      exact hleft
    · intro hx
      rw [hilbertRelationDomain, Submodule.mem_map]
      exact ⟨hilbertSumInl x, hx, hilbertSumFst_inl x⟩
  have hdomainClosed : IsClosed (hilbertRelationDomain R : Set H₁) := by
    have heq : (hilbertRelationDomain R : Set H₁) =
        (fun x : H₁ => hilbertSumInl x) ⁻¹' (R : Set (HilbertSum H₁ H₂)) := by
      ext x
      exact hdomainHorizontal x
    rw [heq]
    exact hclosed.preimage hilbertSumInl.continuous
  have hdomainTop : hilbertRelationDomain R = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ closure (hilbertRelationDomain R : Set H₁) := by
      rw [hdense.closure_eq]
      exact Set.mem_univ x
    exact closure_minimal (Set.Subset.rfl) hdomainClosed hx
  constructor
  · intro hz
    have hright : hilbertSumInr (hilbertSumSnd z) ∈ R := (hsplit z).mp hz |>.2
    exact hsingle _ hright
  · intro hout
    apply (hsplit z).mpr
    constructor
    · apply (hdomainHorizontal (hilbertSumFst z)).mp
      rw [hdomainTop]
      exact Submodule.mem_top
    · rw [hout, map_zero]
      exact R.zero_mem

end

end GaloisForLFunctions.HTGeometry
