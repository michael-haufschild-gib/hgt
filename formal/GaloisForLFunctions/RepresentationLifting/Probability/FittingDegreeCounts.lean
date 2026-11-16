import GaloisForLFunctions.RepresentationLifting.Probability.ComplementaryPairCardinality

/-!
# Counting endomorphisms by generalized zero-eigenspace dimension

Fixing the nilpotent dimension leaves a single orbit of complementary
pairs. The stabilizer factors cancel, leaving the ambient automorphism
count times the nilpotent count in that dimension.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Conjugation transports nilpotent endomorphisms bijectively. -/
def nilpotentEndCongr (e : V ≃ₗ[K] W) : NilpotentEnd K V ≃ NilpotentEnd K W where
  toFun N := ⟨e.conjRingEquiv N.1, N.2.map e.conjRingEquiv⟩
  invFun N := ⟨e.conjRingEquiv.symm N.1, N.2.map e.conjRingEquiv.symm⟩
  left_inv N := Subtype.ext (e.conjRingEquiv.symm_apply_apply N.1)
  right_inv N := Subtype.ext (e.conjRingEquiv.apply_symm_apply N.1)

variable [FiniteDimensional K V]

/-- Endomorphisms whose generalized zero-eigenspace has dimension `d`. -/
abbrev FittingDegreeStratum (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :=
  {T : Module.End K V // Module.finrank K (nilpotentPart T) = d}

/-- Complementary pairs whose first summand has dimension `d`. -/
abbrev ComplementaryDegreeStratum (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :=
  {P : ComplementaryPair K V // Module.finrank K P.1.1 = d}

/-- Partition a fixed-degree stratum by its unique complementary pair. -/
def fittingDegreePartitionEquiv (d : ℕ) :
    FittingDegreeStratum K V d ≃
      (Σ P : ComplementaryDegreeStratum K V d, FittingStratum P.1.1.1 P.1.1.2) where
  toFun T :=
    ⟨⟨⟨(nilpotentPart T.1, stableImage T.1), (canonical_isFittingPair T.1).1⟩, T.2⟩,
      ⟨T.1, canonical_isFittingPair T.1⟩⟩
  invFun x := ⟨x.2.1, by
    have h := (isFittingPair_iff x.2.1 x.1.1.1.1 x.1.1.1.2).mp x.2.2
    rw [← h.1]
    exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨⟨⟨U, W⟩, hc⟩, hd⟩, T, hT⟩
    obtain ⟨rfl, rfl⟩ := (isFittingPair_iff T U W).mp hT
    rfl

/-- Fixed-degree endomorphisms are parameterized by their pair and their two blocks. -/
def fittingDegreeDataEquiv (d : ℕ) :
    FittingDegreeStratum K V d ≃
      (Σ P : ComplementaryDegreeStratum K V d,
        NilpotentEnd K P.1.1.1 × (P.1.1.2 ≃ₗ[K] P.1.1.2)) :=
  (fittingDegreePartitionEquiv d).trans (Equiv.sigmaCongrRight fun P =>
    (fittingStratumEquiv P.1.1.1 P.1.1.2 P.1.2).symm)

/-- Every operator has one generalized-zero dimension in the full finite range. -/
def allFittingDegreesEquiv : Module.End K V ≃
    (Σ d : Fin (Module.finrank K V + 1), FittingDegreeStratum K V (d : ℕ)) where
  toFun T := ⟨⟨Module.finrank K (nilpotentPart T),
    Nat.lt_succ_of_le (nilpotentPart T).finrank_le⟩, ⟨T, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨d, hd⟩, T, hT⟩
    change Module.finrank K (nilpotentPart T) = d at hT
    subst d
    rfl

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

/-- Every pair of the same dimensions contributes the same number of operators. -/
theorem card_fittingDegreeStratum (P : ComplementaryPair K V) :
    Nat.card (FittingDegreeStratum K V (Module.finrank K P.1.1)) =
      Nat.card (ComplementaryDegreeStratum K V (Module.finrank K P.1.1)) *
        Nat.card (NilpotentEnd K P.1.1) * Nat.card (P.1.2 ≃ₗ[K] P.1.2) := by
  rw [Nat.card_congr (fittingDegreeDataEquiv (K := K) (V := V) (Module.finrank K P.1.1)),
    Nat.card_sigma]
  have hconst (Q : ComplementaryDegreeStratum K V (Module.finrank K P.1.1)) :
      Nat.card (NilpotentEnd K Q.1.1.1 × (Q.1.1.2 ≃ₗ[K] Q.1.1.2)) =
        Nat.card (NilpotentEnd K P.1.1) * Nat.card (P.1.2 ≃ₗ[K] P.1.2) := by
    let e : Q.1.1.1 ≃ₗ[K] P.1.1 := LinearEquiv.ofFinrankEq _ _ Q.2
    have hP := Submodule.finrank_add_eq_of_isCompl P.2
    have hQ := Submodule.finrank_add_eq_of_isCompl Q.1.2
    have hs : Module.finrank K Q.1.1.2 = Module.finrank K P.1.2 := by
      have hd := Q.2
      omega
    rw [Nat.card_prod, Nat.card_congr (nilpotentEndCongr e),
      card_automorphisms_eq_prod, card_automorphisms_eq_prod, hs]
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, mul_assoc]
  rfl

/-- The invertible complementary block cancels out of the fixed-degree count. -/
theorem card_fittingDegreeStratum_mul_aut (P : ComplementaryPair K V) :
    Nat.card (FittingDegreeStratum K V (Module.finrank K P.1.1)) *
      Nat.card (P.1.1 ≃ₗ[K] P.1.1) =
        Nat.card (V ≃ₗ[K] V) * Nat.card (NilpotentEnd K P.1.1) := by
  rw [card_fittingDegreeStratum]
  calc
    _ = (Nat.card (ComplementaryDegreeStratum K V (Module.finrank K P.1.1)) *
        Nat.card (P.1.1 ≃ₗ[K] P.1.1) * Nat.card (P.1.2 ≃ₗ[K] P.1.2)) *
          Nat.card (NilpotentEnd K P.1.1) := by ac_rfl
    _ = _ := by rw [card_complementaryPair_mul_card_blocks]

/-- The degree strata exhaust the full endomorphism count. -/
theorem sum_card_fittingDegreeStratum :
    (∑ d : Fin (Module.finrank K V + 1), Nat.card (FittingDegreeStratum K V (d : ℕ))) =
      Nat.card (Module.End K V) := by
  have h := Nat.card_congr (allFittingDegreesEquiv (K := K) (V := V))
  rw [Nat.card_sigma] at h
  exact h.symm

/-- The fixed-degree count uses only standard coordinate-space counts in that degree. -/
theorem card_fittingDegreeStratum_mul_standard_aut (d : Fin (Module.finrank K V + 1)) :
    Nat.card (FittingDegreeStratum K V (d : ℕ)) *
      Nat.card ((Fin (d : ℕ) → K) ≃ₗ[K] (Fin (d : ℕ) → K)) =
        Nat.card (V ≃ₗ[K] V) * Nat.card (NilpotentEnd K (Fin (d : ℕ) → K)) := by
  obtain ⟨P, hP⟩ := exists_complementaryPair_dimension (K := K) (V := V) d
  have h := card_fittingDegreeStratum_mul_aut P
  have hd : Module.finrank K P.1.1 = Module.finrank K (Fin (d : ℕ) → K) := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using hP
  let e : P.1.1 ≃ₗ[K] (Fin (d : ℕ) → K) := LinearEquiv.ofFinrankEq _ _ hd
  have ha : Nat.card (P.1.1 ≃ₗ[K] P.1.1) =
      Nat.card ((Fin (d : ℕ) → K) ≃ₗ[K] (Fin (d : ℕ) → K)) := by
    rw [card_automorphisms_eq_prod, card_automorphisms_eq_prod, hd]
  rw [hP, ha, Nat.card_congr (nilpotentEndCongr e)] at h
  exact h

end FiniteField

#print axioms fittingDegreeDataEquiv
#print axioms card_fittingDegreeStratum_mul_aut
#print axioms card_fittingDegreeStratum_mul_standard_aut
#print axioms sum_card_fittingDegreeStratum

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
