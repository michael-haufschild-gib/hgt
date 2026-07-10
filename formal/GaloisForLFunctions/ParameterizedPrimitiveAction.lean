import GaloisForLFunctions.DifferentialPolynomialOver

/-!
# Affine difference actions for compatible additive primitive systems

This file constructs the semilinear affine action on differential polynomials associated to a
several-automorphism primitive system.  Coefficients transform by the base automorphism and each
formal jet transforms by translation by the corresponding jet of the additive cocycle.  The
action commutes with the total differential-polynomial derivation, compatible cocycles give
commuting actions, and evaluation at an actual primitive system intertwines the formal action with
the automorphisms of the extension field.  Consequently the differential relation ideal of the
primitive tuple is invariant under every affine action.

This is the algebraic input needed before a parameterized Picard--Vessiot torsor can turn a
nontrivial relation ideal into an additive differential Hopf ideal.  It does not assume or assert
that Galois correspondence.
-/

open scoped Differential

namespace GaloisForLFunctions
noncomputable section

/-- The affine semilinear action induced by the additive data `a`. -/
def differentialPolynomialAffineHom
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) :
    DifferentialPolynomial κ K →+* DifferentialPolynomial κ K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (S.aut i).toRingHom) fun p =>
    MvPolynomial.X p + MvPolynomial.C (differentialJet p.2 (a i p.1))

@[simp] theorem differentialPolynomialAffineHom_C
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (c : K) :
    differentialPolynomialAffineHom S a i (MvPolynomial.C c) =
      MvPolynomial.C (S.aut i c) := by
  simp [differentialPolynomialAffineHom]

@[simp] theorem differentialPolynomialAffineHom_X
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (k : κ) (n : ℕ) :
    differentialPolynomialAffineHom S a i (MvPolynomial.X (k,n)) =
      MvPolynomial.X (k,n) + MvPolynomial.C (differentialJet n (a i k)) := by
  simp [differentialPolynomialAffineHom]

/-- The inverse affine semilinear action. -/
def differentialPolynomialAffineInvHom
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) :
    DifferentialPolynomial κ K →+* DifferentialPolynomial κ K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (S.aut i).symm.toRingHom) fun p =>
    MvPolynomial.X p -
      MvPolynomial.C ((S.aut i).symm (differentialJet p.2 (a i p.1)))

@[simp] theorem differentialPolynomialAffineInvHom_C
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (c : K) :
    differentialPolynomialAffineInvHom S a i (MvPolynomial.C c) =
      MvPolynomial.C ((S.aut i).symm c) := by
  simp [differentialPolynomialAffineInvHom]

@[simp] theorem differentialPolynomialAffineInvHom_X
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (k : κ) (n : ℕ) :
    differentialPolynomialAffineInvHom S a i (MvPolynomial.X (k,n)) =
      MvPolynomial.X (k,n) -
        MvPolynomial.C ((S.aut i).symm (differentialJet n (a i k))) := by
  simp [differentialPolynomialAffineInvHom]

theorem differentialPolynomialAffineInvHom_apply_affineHom
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialAffineInvHom S a i (differentialPolynomialAffineHom S a i P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rcases p with ⟨k,n⟩
      simp [hP]

theorem differentialPolynomialAffineHom_apply_invHom
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialAffineHom S a i (differentialPolynomialAffineInvHom S a i P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rcases p with ⟨k,n⟩
      simp [hP]

def differentialPolynomialAffineEquiv
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) :
    DifferentialPolynomial κ K ≃+* DifferentialPolynomial κ K where
  toFun := differentialPolynomialAffineHom S a i
  invFun := differentialPolynomialAffineInvHom S a i
  left_inv := differentialPolynomialAffineInvHom_apply_affineHom S a i
  right_inv := differentialPolynomialAffineHom_apply_invHom S a i
  map_mul' := map_mul _
  map_add' := map_add _

/-- The affine action commutes with the total derivation over the differential base. -/
theorem differentialPolynomialAffineHom_overDerivation
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (i : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialAffineHom S a i (differentialPolynomialOverDerivation κ K P) =
      differentialPolynomialOverDerivation κ K (differentialPolynomialAffineHom S a i P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialOverDerivation_C, differentialPolynomialAffineHom_C]
      exact congrArg MvPolynomial.C (S.aut_deriv i c)
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P p hP =>
      rcases p with ⟨k,n⟩
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, hP, differentialPolynomialAffineHom_X]
      rw [differentialPolynomialOverDerivation_X]
      simp only [differentialPolynomialAffineHom_X]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, differentialPolynomialOverDerivation_X,
        differentialPolynomialOverDerivation_C]
      rw [← differentialJet_succ]

/-- The pairwise compatibility equation for an additive several-automorphism cocycle. -/
def CompatibleAdditiveCocycle
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K) : Prop :=
  ∀ i j k, S.defect i (a j k) = S.defect j (a i k)

theorem CompatiblePrimitiveSystem.toCompatibleAdditiveCocycle
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    {y : κ → K} {a : ι → κ → K} (h : CompatiblePrimitiveSystem S y a) :
    CompatibleAdditiveCocycle S a := by
  exact h.cocycle S

theorem CompatibleAdditiveCocycle.jet
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    {a : ι → κ → K} (h : CompatibleAdditiveCocycle S a)
    (i j : ι) (k : κ) (n : ℕ) :
    differentialJet n (a i k) + S.aut i (differentialJet n (a j k)) =
      differentialJet n (a j k) + S.aut j (differentialJet n (a i k)) := by
  have hc := congrArg (differentialJet n) (h i j k)
  simp only [CommutingDifferenceDifferentialField.defect] at hc
  rw [differentialJet_sub, differentialJet_sub, ← S.aut_differentialJet,
    ← S.aut_differentialJet] at hc
  linear_combination hc

/-- Compatible cocycles induce commuting affine actions. -/
theorem differentialPolynomialAffineHom_comm
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (a : ι → κ → K) (ha : CompatibleAdditiveCocycle S a)
    (i j : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialAffineHom S a i (differentialPolynomialAffineHom S a j P) =
      differentialPolynomialAffineHom S a j (differentialPolynomialAffineHom S a i P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialAffineHom_C]
      exact congrArg MvPolynomial.C (S.aut_comm i j c)
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rcases p with ⟨k,n⟩
      simp only [map_mul, hP, differentialPolynomialAffineHom_X, map_add,
        differentialPolynomialAffineHom_C]
      have hc := congrArg
        (fun x : K => (MvPolynomial.C x : DifferentialPolynomial κ K))
        (ha.jet S i j k n)
      have hc' :
          (MvPolynomial.C (differentialJet n (a i k)) : DifferentialPolynomial κ K) +
              MvPolynomial.C (S.aut i (differentialJet n (a j k))) =
            (MvPolynomial.C (differentialJet n (a j k)) : DifferentialPolynomial κ K) +
              MvPolynomial.C (S.aut j (differentialJet n (a i k))) := by
        simpa only [map_add] using hc
      ring_nf at hc' ⊢
      linear_combination
        (differentialPolynomialAffineHom S a j
          (differentialPolynomialAffineHom S a i P)) * hc'

/-- A compatible primitive system in a difference-differential extension. -/
def CompatiblePrimitiveExtensionSystem
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [Differential K] [Differential L]
    (SL : CommutingDifferenceDifferentialField ι C L)
    (y : κ → L) (a : ι → κ → K) : Prop :=
  ∀ i k, SL.defect i (y k) = algebraMap K L (a i k)

/-- Compatibility of an actual primitive system descends through the injective base-field map to
the additive cocycle equation in the base field. -/
theorem CompatiblePrimitiveExtensionSystem.toCompatibleAdditiveCocycle
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [Differential K] [Differential L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    {y : κ → L} {a : ι → κ → K}
    (hsys : CompatiblePrimitiveExtensionSystem SL y a) :
    CompatibleAdditiveCocycle SK a := by
  let aL : ι → κ → L := fun i k => algebraMap K L (a i k)
  have hsysL : CompatiblePrimitiveSystem SL y aL := hsys
  have hc := hsysL.cocycle SL
  intro i j k
  apply (algebraMap K L).injective
  have h := hc i j k
  simpa only [aL, CommutingDifferenceDifferentialField.defect, map_sub, hσ] using h

private theorem differentialJet_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (n : ℕ) (x : K) :
    differentialJet n (algebraMap K L x) = algebraMap K L (differentialJet n x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, ih,
        DifferentialAlgebra.deriv_algebraMap]

private theorem differentialJet_additive
    {L : Type*} [Field L] [Differential L] (n : ℕ) (x y : L) :
    differentialJet n (x + y) = differentialJet n x + differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ, ih, map_add]

/-- Evaluation at an actual compatible primitive tuple intertwines the formal affine action with
the corresponding automorphism of the extension field. -/
theorem differentialPolynomialEvalOver_affineHom
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    (y : κ → L) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveExtensionSystem SL y a)
    (i : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialEvalOver (K := K) y (differentialPolynomialAffineHom SK a i P) =
      SL.aut i (differentialPolynomialEvalOver (K := K) y P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialAffineHom_C, differentialPolynomialEvalOver_C]
      exact hσ i c |>.symm
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
      rcases p with ⟨k,n⟩
      simp only [map_mul, hP, differentialPolynomialAffineHom_X,
        differentialPolynomialEvalOver_X, map_add, differentialPolynomialEvalOver_C]
      have hy : SL.aut i (y k) = y k + algebraMap K L (a i k) := by
        have h := hsys i k
        simp only [CommutingDifferenceDifferentialField.defect] at h
        linear_combination h
      rw [SL.aut_differentialJet, hy, ← differentialJet_algebraMap,
        ← differentialJet_additive]

/-- Every affine difference action preserves the differential relation ideal of an actual
compatible primitive tuple. -/
theorem differentialPolynomialAffineHom_mem_relationIdealOver
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    (y : κ → L) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveExtensionSystem SL y a)
    (i : ι) {P : DifferentialPolynomial κ K}
    (hP : P ∈ differentialRelationIdealOver y) :
    differentialPolynomialAffineHom SK a i P ∈ differentialRelationIdealOver y := by
  rw [mem_differentialRelationIdealOver_iff,
    differentialPolynomialEvalOver_affineHom SK SL hσ y a hsys]
  rw [mem_differentialRelationIdealOver_iff] at hP
  rw [hP, map_zero]

/-- Membership in the relation ideal is reflected as well as preserved: applying an affine
difference action cannot create or destroy a relation because evaluation is intertwined with a
field automorphism. -/
theorem differentialPolynomialAffineHom_mem_relationIdealOver_iff
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    (y : κ → L) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveExtensionSystem SL y a)
    (i : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialAffineHom SK a i P ∈ differentialRelationIdealOver y ↔
      P ∈ differentialRelationIdealOver y := by
  rw [mem_differentialRelationIdealOver_iff, mem_differentialRelationIdealOver_iff,
    differentialPolynomialEvalOver_affineHom SK SL hσ y a hsys]
  simp

/-- The full relation ideal is invariant, as an ideal, under every affine difference action. -/
theorem differentialPolynomialAffineHom_map_relationIdealOver
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    (y : κ → L) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveExtensionSystem SL y a)
    (i : ι) :
    Ideal.map (differentialPolynomialAffineHom SK a i)
        (differentialRelationIdealOver y) = differentialRelationIdealOver y := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    exact differentialPolynomialAffineHom_mem_relationIdealOver SK SL hσ y a hsys i hP
  · intro Q hQ
    let P := differentialPolynomialAffineInvHom SK a i Q
    have hforward : differentialPolynomialAffineHom SK a i P ∈
        differentialRelationIdealOver y := by
      simpa only [P, differentialPolynomialAffineHom_apply_invHom] using hQ
    have hP : P ∈ differentialRelationIdealOver y :=
      (differentialPolynomialAffineHom_mem_relationIdealOver_iff
        SK SL hσ y a hsys i P).mp hforward
    rw [← differentialPolynomialAffineHom_apply_invHom SK a i Q]
    exact Ideal.mem_map_of_mem (differentialPolynomialAffineHom SK a i) hP

/-- A dependent compatible primitive tuple produces a nonzero proper differential ideal which is
invariant under all commuting affine difference actions.  This is the exact unconditional ideal
available before the PPV maximal-ideal and torsor steps. -/
theorem dependent_compatiblePrimitiveSystem_relationIdeal
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    (y : κ → L) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveExtensionSystem SL y a)
    (hdep : ¬ DifferentialIndependent K y) :
    differentialRelationIdealOver (K := K) y ≠ ⊥ ∧
      differentialRelationIdealOver (K := K) y ≠ ⊤ ∧
      (∀ ⦃P : DifferentialPolynomial κ K⦄,
        P ∈ differentialRelationIdealOver (K := K) y →
        differentialPolynomialOverDerivation κ K P ∈
          differentialRelationIdealOver (K := K) y) ∧
      ∀ i, Ideal.map (differentialPolynomialAffineHom SK a i)
        (differentialRelationIdealOver (K := K) y) =
          differentialRelationIdealOver (K := K) y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hdep ((differentialIndependent_iff_relationIdealOver_eq_bot y).2 hbot)
  · rw [Ideal.ne_top_iff_one]
    change differentialPolynomialEvalOver (K := K) y 1 ≠ 0
    simp
  · intro P hP
    exact differentialPolynomialOverDerivation_mem_relationIdeal y hP
  · intro i
    exact differentialPolynomialAffineHom_map_relationIdealOver SK SL hσ y a hsys i

end
end GaloisForLFunctions
