import GaloisForLFunctions.RepresentationLifting.Probability.FittingStrata
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting ordered complementary subspaces

The general linear group acts transitively on complementary pairs of fixed
dimensions. The stabilizer is the product of the general linear groups of
the two summands. Orbit--stabilizer gives the exact count used in Fitting
stratification of finite-field endomorphisms.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Transport a complementary pair by an ambient automorphism. -/
def mapComplementaryPair (e : V ≃ₗ[K] V) (P : ComplementaryPair K V) :
    ComplementaryPair K V :=
  ⟨(P.1.1.map e.toLinearMap, P.1.2.map e.toLinearMap),
    (Submodule.orderIsoMapComap e).isCompl_iff.mp P.2⟩

private theorem map_linearEquiv_mul (e f : V ≃ₗ[K] V) (U : Submodule K V) :
    U.map (e * f).toLinearMap = (U.map f.toLinearMap).map e.toLinearMap := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨f u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

instance complementaryPairAction : MulAction (V ≃ₗ[K] V) (ComplementaryPair K V) where
  smul := mapComplementaryPair
  one_smul P := by
    apply Subtype.ext
    apply Prod.ext
    · exact Submodule.map_id P.1.1
    · exact Submodule.map_id P.1.2
  mul_smul e f P := by
    apply Subtype.ext
    exact Prod.ext (map_linearEquiv_mul e f P.1.1) (map_linearEquiv_mul e f P.1.2)

/-- Assemble isomorphisms between the two corresponding summands. -/
def complementaryPairEquiv (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).symm.trans
    ((a.prodCongr b).trans (Submodule.prodEquivOfIsCompl Q.1.1 Q.1.2 Q.2))

/-- Assembly agrees with the first chosen isomorphism on the first summand. -/
theorem complementaryPairEquiv_left (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) (x : P.1.1) :
    complementaryPairEquiv P Q a b x = (a x : V) := by
  change (Submodule.prodEquivOfIsCompl Q.1.1 Q.1.2 Q.2)
    ((a.prodCongr b) ((Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).symm x)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  change (a x : V) + (b 0 : V) = (a x : V)
  rw [map_zero, Submodule.coe_zero, add_zero]

/-- Assembly agrees with the second chosen isomorphism on the second summand. -/
theorem complementaryPairEquiv_right (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) (x : P.1.2) :
    complementaryPairEquiv P Q a b x = (b x : V) := by
  change (Submodule.prodEquivOfIsCompl Q.1.1 Q.1.2 Q.2)
    ((a.prodCongr b) ((Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).symm x)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  change (a 0 : V) + (b x : V) = (b x : V)
  rw [map_zero, Submodule.coe_zero, zero_add]

/-- The assembled isomorphism sends the whole ordered pair to the target pair. -/
theorem complementaryPairEquiv_smul (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) :
    complementaryPairEquiv P Q a b • P = Q := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change complementaryPairEquiv P Q a b u ∈ Q.1.1
      rw [complementaryPairEquiv_left P Q a b ⟨u, hu⟩]
      exact (a ⟨u, hu⟩).2
    · intro hx
      refine ⟨(a.symm ⟨x, hx⟩ : V), (a.symm ⟨x, hx⟩).2, ?_⟩
      change complementaryPairEquiv P Q a b (a.symm ⟨x, hx⟩ : V) = x
      rw [complementaryPairEquiv_left]
      exact congrArg Subtype.val (a.apply_symm_apply ⟨x, hx⟩)
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change complementaryPairEquiv P Q a b u ∈ Q.1.2
      rw [complementaryPairEquiv_right P Q a b ⟨u, hu⟩]
      exact (b ⟨u, hu⟩).2
    · intro hx
      refine ⟨(b.symm ⟨x, hx⟩ : V), (b.symm ⟨x, hx⟩).2, ?_⟩
      change complementaryPairEquiv P Q a b (b.symm ⟨x, hx⟩ : V) = x
      rw [complementaryPairEquiv_right]
      exact congrArg Subtype.val (b.apply_symm_apply ⟨x, hx⟩)

private theorem stabilizer_map_left (P : ComplementaryPair K V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) P) : P.1.1.map g.1.toLinearMap = P.1.1 :=
  congrArg (fun Q : ComplementaryPair K V => Q.1.1)
    (MulAction.mem_stabilizer_iff.mp g.2)

private theorem stabilizer_map_right (P : ComplementaryPair K V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) P) : P.1.2.map g.1.toLinearMap = P.1.2 :=
  congrArg (fun Q : ComplementaryPair K V => Q.1.2)
    (MulAction.mem_stabilizer_iff.mp g.2)

private def stabilizerLeft (P : ComplementaryPair K V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) P) : P.1.1 ≃ₗ[K] P.1.1 :=
  (g.1.submoduleMap P.1.1).trans
    (LinearEquiv.ofEq _ _ (stabilizer_map_left P g))

private def stabilizerRight (P : ComplementaryPair K V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) P) : P.1.2 ≃ₗ[K] P.1.2 :=
  (g.1.submoduleMap P.1.2).trans
    (LinearEquiv.ofEq _ _ (stabilizer_map_right P g))

private theorem stabilizerLeft_apply (P : ComplementaryPair K V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) P) (x : P.1.1) :
    (stabilizerLeft P g x : V) = g.1 x := rfl

private theorem stabilizerRight_apply (P : ComplementaryPair K V)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) P) (x : P.1.2) :
    (stabilizerRight P g x : V) = g.1 x := rfl

/-- Preserving both complementary summands is equivalent to independent automorphisms of them. -/
def complementaryPairStabilizerEquiv (P : ComplementaryPair K V) :
    MulAction.stabilizer (V ≃ₗ[K] V) P ≃
      ((P.1.1 ≃ₗ[K] P.1.1) × (P.1.2 ≃ₗ[K] P.1.2)) :=
  Equiv.ofBijective (fun g => (stabilizerLeft P g, stabilizerRight P g)) ⟨by
    intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨⟨u, v⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).surjective x
    change g.1 ((u : V) + (v : V)) = h.1 ((u : V) + (v : V))
    rw [map_add, map_add]
    have hu := congrArg (fun z : (P.1.1 ≃ₗ[K] P.1.1) × (P.1.2 ≃ₗ[K] P.1.2) =>
      (z.1 u : V)) he
    have hv := congrArg (fun z : (P.1.1 ≃ₗ[K] P.1.1) × (P.1.2 ≃ₗ[K] P.1.2) =>
      (z.2 v : V)) he
    exact congrArg₂ (· + ·) hu hv,
    by
    rintro ⟨a, b⟩
    refine ⟨⟨complementaryPairEquiv P P a b,
      MulAction.mem_stabilizer_iff.mpr (complementaryPairEquiv_smul P P a b)⟩, ?_⟩
    apply Prod.ext
    · apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      exact complementaryPairEquiv_left P P a b u
    · apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      exact complementaryPairEquiv_right P P a b v⟩

variable [FiniteDimensional K V]

/-- The orbit of a complementary pair is determined by the dimension of its first summand. -/
theorem mem_complementaryPair_orbit_iff (P Q : ComplementaryPair K V) :
    Q ∈ MulAction.orbit (V ≃ₗ[K] V) P ↔ Module.finrank K Q.1.1 = Module.finrank K P.1.1 := by
  constructor
  · rintro ⟨e, rfl⟩
    exact (e.submoduleMap P.1.1).finrank_eq.symm
  · intro hdim
    have hP := Submodule.finrank_add_eq_of_isCompl P.2
    have hQ := Submodule.finrank_add_eq_of_isCompl Q.2
    let a : P.1.1 ≃ₗ[K] Q.1.1 := LinearEquiv.ofFinrankEq _ _ hdim.symm
    let b : P.1.2 ≃ₗ[K] Q.1.2 := LinearEquiv.ofFinrankEq _ _ (by omega)
    exact ⟨complementaryPairEquiv P Q a b, complementaryPairEquiv_smul P Q a b⟩


/-- Every dimension from zero to the ambient dimension occurs as the first summand. -/
theorem exists_complementaryPair_dimension (d : Fin (Module.finrank K V + 1)) :
    ∃ P : ComplementaryPair K V, Module.finrank K P.1.1 = (d : ℕ) := by
  let b := Module.finBasis K V
  let f : Fin (d : ℕ) → Fin (Module.finrank K V) :=
    fun i => ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ d.isLt)⟩
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin (Module.finrank K V) => z.val) h)
  have hi : LinearIndependent K (fun i => b (f i)) := b.linearIndependent.comp f hf
  let U := Submodule.span K (Set.range (fun i => b (f i)))
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨⟨(U, W), hW⟩, ?_⟩
  simpa only [Fintype.card_fin] using finrank_span_eq_card hi

/-- A finite basis identifies automorphisms with the matrix general linear group. -/
def automorphismMatrixEquiv :
    (V ≃ₗ[K] V) ≃*
      (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toMulEquiv)

section FiniteField
variable [Finite K]

local instance : Finite (Submodule K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun P : Submodule K V => (P : Set V)) SetLike.coe_injective

local instance : Finite (V ≃ₗ[K] V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- The automorphism count depends only on the field size and vector-space dimension. -/
theorem card_automorphisms_eq_prod :
    Nat.card (V ≃ₗ[K] V) =
      ∏ i : Fin (Module.finrank K V),
        (Nat.card K ^ Module.finrank K V - Nat.card K ^ (i : ℕ)) := by
  rw [Nat.card_congr (automorphismMatrixEquiv (K := K) (V := V)).toEquiv,
    Matrix.card_GL_field]
  simp only [Nat.card_eq_fintype_card]

/-- Orbit--stabilizer counts complementary pairs of prescribed dimensions exactly. -/
theorem card_complementaryPair_mul_card_blocks (P : ComplementaryPair K V) :
    Nat.card {Q : ComplementaryPair K V // Module.finrank K Q.1.1 = Module.finrank K P.1.1} *
      Nat.card (P.1.1 ≃ₗ[K] P.1.1) * Nat.card (P.1.2 ≃ₗ[K] P.1.2) =
      Nat.card (V ≃ₗ[K] V) := by
  let e : MulAction.orbit (V ≃ₗ[K] V) P ≃
      {Q : ComplementaryPair K V // Module.finrank K Q.1.1 = Module.finrank K P.1.1} :=
    { toFun x := ⟨x.1, (mem_complementaryPair_orbit_iff P x.1).mp x.2⟩
      invFun x := ⟨x.1, (mem_complementaryPair_orbit_iff P x.1).mpr x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (V ≃ₗ[K] V) P
  simp only [← Nat.card_eq_fintype_card] at h
  rw [Nat.card_congr e,
    Nat.card_congr (complementaryPairStabilizerEquiv P), Nat.card_prod] at h
  simpa only [mul_assoc] using h

end FiniteField

#print axioms complementaryPairStabilizerEquiv
#print axioms mem_complementaryPair_orbit_iff
#print axioms card_complementaryPair_mul_card_blocks
#print axioms card_automorphisms_eq_prod
#print axioms exists_complementaryPair_dimension

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
