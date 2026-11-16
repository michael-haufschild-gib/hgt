import GaloisForLFunctions.RepresentationLifting.OperatorKernels.FittingPairs
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Parameterization of finite-field Fitting strata

A fixed complementary pair supports exactly a nilpotent endomorphism on
the first summand and an automorphism on the second. Uniqueness of the
Fitting pair makes these parameterizations disjoint over all pairs.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Nilpotent endomorphisms, retaining their actual underlying operator. -/
abbrev NilpotentEnd (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {N : Module.End K V // IsNilpotent N}

/-- Assemble two operators using a specified complementary pair. -/
def fittingAssembly (U W : Submodule K V) (hc : IsCompl U W)
    (N : Module.End K U) (S : Module.End K W) : Module.End K V :=
  (Submodule.prodEquivOfIsCompl U W hc).conj (N.prodMap S)

/-- The assembled operator restricts to the first chosen block. -/
theorem fittingAssembly_left (U W : Submodule K V) (hc : IsCompl U W)
    (N : Module.End K U) (S : Module.End K W) (x : U) :
    fittingAssembly U W hc N S x = (N x : V) := by
  simp only [fittingAssembly, LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Submodule.prodEquivOfIsCompl_symm_apply_left,
    LinearMap.prodMap_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
    Submodule.coe_zero, add_zero]

/-- The assembled operator restricts to the second chosen block. -/
theorem fittingAssembly_right (U W : Submodule K V) (hc : IsCompl U W)
    (N : Module.End K U) (S : Module.End K W) (x : W) :
    fittingAssembly U W hc N S x = (S x : V) := by
  simp only [fittingAssembly, LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Submodule.prodEquivOfIsCompl_symm_apply_right,
    LinearMap.prodMap_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
    Submodule.coe_zero, zero_add]

/-- Iterating the assembled operator on the first summand iterates its first block. -/
theorem fittingAssembly_pow_left (U W : Submodule K V) (hc : IsCompl U W)
    (N : Module.End K U) (S : Module.End K W) (n : ℕ) (x : U) :
    (fittingAssembly U W hc N S ^ n) x = ((N ^ n) x : V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, fittingAssembly_left,
      pow_succ', Module.End.mul_apply]

/-- Nilpotence and invertibility of the two blocks recover the specified Fitting pair. -/
theorem fittingAssembly_isFittingPair (U W : Submodule K V) (hc : IsCompl U W)
    (N : NilpotentEnd K U) (S : W ≃ₗ[K] W) :
    IsFittingPair (fittingAssembly U W hc N.1 S.toLinearMap) U W := by
  obtain ⟨n, hn⟩ := N.2
  refine ⟨hc, ⟨n, ?_⟩, ?_⟩
  · intro x hx
    change (fittingAssembly U W hc N.1 S.toLinearMap ^ n) x = 0
    rw [fittingAssembly_pow_left U W hc N.1 S.toLinearMap n ⟨x, hx⟩, hn]
    rfl
  · intro x hx
    refine ⟨(S.symm ⟨x, hx⟩ : V), (S.symm ⟨x, hx⟩).2, ?_⟩
    rw [fittingAssembly_right]
    exact congrArg Subtype.val (S.apply_symm_apply ⟨x, hx⟩)

/-- Endomorphisms with this exact Fitting pair. -/
abbrev FittingStratum (U W : Submodule K V) :=
  {T : Module.End K V // IsFittingPair T U W}

variable [FiniteDimensional K V]

/-- Every Fitting stratum is exactly the product of its nilpotent and invertible blocks. -/
def fittingStratumEquiv (U W : Submodule K V) (hc : IsCompl U W) :
    (NilpotentEnd K U × (W ≃ₗ[K] W)) ≃ FittingStratum U W :=
  Equiv.ofBijective
    (fun x => ⟨fittingAssembly U W hc x.1.1 x.2.toLinearMap,
      fittingAssembly_isFittingPair U W hc x.1 x.2⟩) ⟨by
      intro x y h
      have he := congrArg Subtype.val h
      apply Prod.ext
      · apply Subtype.ext
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        simpa only [fittingAssembly_left] using congrArg (fun T => T (u : V)) he
      · apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        simpa only [fittingAssembly_right, LinearEquiv.coe_coe] using
          congrArg (fun T => T (w : V)) he,
    by
      rintro ⟨T, hT⟩
      obtain ⟨rfl, rfl⟩ := (isFittingPair_iff T U W).mp hT
      refine ⟨(⟨nilpotentPartOperator T, nilpotentPartOperator_isNilpotent T⟩,
        stableImageEquiv T), Subtype.ext ?_⟩
      exact fittingEquiv_conj T⟩

/-- Ordered pairs of complementary subspaces. -/
abbrev ComplementaryPair (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {P : Submodule K V × Submodule K V // IsCompl P.1 P.2}

/-- Uniqueness makes the Fitting strata a disjoint partition of all endomorphisms. -/
def fittingPartitionEquiv : Module.End K V ≃
    (Σ P : ComplementaryPair K V, FittingStratum P.1.1 P.1.2) where
  toFun T := ⟨⟨(nilpotentPart T, stableImage T), (canonical_isFittingPair T).1⟩,
    ⟨T, canonical_isFittingPair T⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨⟨U, W⟩, hc⟩, T, hT⟩
    obtain ⟨rfl, rfl⟩ := (isFittingPair_iff T U W).mp hT
    rfl

/-- Global coordinates for every operator, with no duplicated complementary pair. -/
def fittingDataEquiv : Module.End K V ≃
    (Σ P : ComplementaryPair K V, NilpotentEnd K P.1.1 × (P.1.2 ≃ₗ[K] P.1.2)) :=
  fittingPartitionEquiv.trans (Equiv.sigmaCongrRight fun P =>
    (fittingStratumEquiv P.1.1 P.1.2 P.2).symm)

section FiniteField
variable [Finite K]

local instance : Finite (Submodule K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun P : Submodule K V => (P : Set V)) SetLike.coe_injective

local instance : Finite (V ≃ₗ[K] V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective

local instance : Finite (Module.End K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : Module.End K V => (e : V → V)) DFunLike.coe_injective

attribute [local instance] Fintype.ofFinite

omit [Finite K] in
/-- Counting a fixed Fitting stratum multiplies the two independent block counts. -/
theorem card_fittingStratum (U W : Submodule K V) (hc : IsCompl U W) :
    Nat.card (FittingStratum U W) =
      Nat.card (NilpotentEnd K U) * Nat.card (W ≃ₗ[K] W) := by
  rw [Nat.card_congr (fittingStratumEquiv U W hc).symm, Nat.card_prod]

/-- The exact finite-field count is a disjoint sum over complementary subspace pairs. -/
theorem card_end_eq_sum_fitting :
    Nat.card (Module.End K V) =
      ∑ P : ComplementaryPair K V,
        Nat.card (NilpotentEnd K P.1.1) * Nat.card (P.1.2 ≃ₗ[K] P.1.2) := by
  rw [Nat.card_congr (fittingDataEquiv (K := K) (V := V)), Nat.card_sigma]
  simp only [Nat.card_prod]

/-- Matrix coordinates evaluate the total count as the square-dimension power of the field size. -/
theorem sum_fitting_eq_field_pow :
    (∑ P : ComplementaryPair K V,
        Nat.card (NilpotentEnd K P.1.1) * Nat.card (P.1.2 ≃ₗ[K] P.1.2)) =
      Nat.card K ^ (Module.finrank K V * Module.finrank K V) := by
  classical
  rw [← card_end_eq_sum_fitting,
    Nat.card_congr (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toEquiv]
  simp only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul]

end FiniteField

#print axioms fittingAssembly_isFittingPair
#print axioms fittingStratumEquiv
#print axioms fittingDataEquiv
#print axioms sum_fitting_eq_field_pow

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
