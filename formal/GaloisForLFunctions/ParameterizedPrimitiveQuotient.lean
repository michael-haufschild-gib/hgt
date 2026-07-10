import GaloisForLFunctions.ParameterizedPrimitiveMaximalIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients by affine differential ideals

An affine differential ideal gives a quotient differential ring carrying the induced commuting
affine difference actions.  The images of the order-zero jet variables form the universal
compatible primitive tuple in this quotient.  This is the quotient-ring layer of the additive
unipotent parameterized Picard--Vessiot construction.
-/

open scoped Differential

namespace GaloisForLFunctions
noncomputable section

/-- The additive map induced on a quotient by a derivation preserving the ideal. -/
def quotientDerivationAddHom
    {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R)
    (hI : ∀ x, x ∈ I → D x ∈ I) : R ⧸ I →+ R ⧸ I :=
  QuotientAddGroup.lift I.toAddSubgroup
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hI x hx))

@[simp] theorem quotientDerivationAddHom_mk
    {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R)
    (hI : ∀ x, x ∈ I → D x ∈ I) (x : R) :
    quotientDerivationAddHom D I hI (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (D x) := rfl

/-- A derivation preserving an ideal descends to the quotient ring. -/
def quotientDerivation
    {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) (I : Ideal R)
    (hI : ∀ x, x ∈ I → D x ∈ I) :
    Derivation ℤ (R ⧸ I) (R ⧸ I) where
  toLinearMap := (quotientDerivationAddHom D I hI).toIntLinearMap
  map_one_eq_zero' := by
    change Ideal.Quotient.mk I (D 1) = 0
    rw [D.map_one_eq_zero, map_zero]
  leibniz' := by
    intro x y
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y =>
        change Ideal.Quotient.mk I (D (x * y)) =
          Ideal.Quotient.mk I x * Ideal.Quotient.mk I (D y) +
            Ideal.Quotient.mk I y * Ideal.Quotient.mk I (D x)
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, map_add, map_mul]

/-- The differential structure on a quotient by an affine differential ideal. -/
@[reducible] def differentialPolynomialQuotientDifferential
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) :
    Differential (DifferentialPolynomial κ K ⧸ I) :=
  ⟨quotientDerivation (differentialPolynomialOverDerivation κ K) I
    (fun _ hP => IsAffineDifferentialIdeal.derivation_mem hI hP)⟩

theorem IsAffineDifferentialIdeal.map_affine
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    {S : CommutingDifferenceDifferentialField ι C K} {a : ι → κ → K}
    {I : Ideal (DifferentialPolynomial κ K)}
    (hI : IsAffineDifferentialIdeal S a I) (i : ι) :
    Ideal.map (differentialPolynomialAffineEquiv S a i).toRingHom I = I := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    exact (hI.affine_mem_iff i P).mpr hP
  · intro Q hQ
    let P := differentialPolynomialAffineInvHom S a i Q
    have hforward : differentialPolynomialAffineHom S a i P ∈ I := by
      simpa only [P, differentialPolynomialAffineHom_apply_invHom] using hQ
    have hP : P ∈ I := (hI.affine_mem_iff i P).mp hforward
    rw [← differentialPolynomialAffineHom_apply_invHom S a i Q]
    exact Ideal.mem_map_of_mem (differentialPolynomialAffineEquiv S a i).toRingHom hP

/-- The affine difference automorphism induced on the quotient. -/
def differentialPolynomialQuotientAffineEquiv
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) (i : ι) :
    (DifferentialPolynomial κ K ⧸ I) ≃+* (DifferentialPolynomial κ K ⧸ I) :=
  Ideal.quotientEquiv I I (differentialPolynomialAffineEquiv S a i)
    (IsAffineDifferentialIdeal.map_affine hI i).symm

@[simp] theorem differentialPolynomialQuotientAffineEquiv_mk
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) (i : ι)
    (P : DifferentialPolynomial κ K) :
    differentialPolynomialQuotientAffineEquiv S a I hI i (Ideal.Quotient.mk I P) =
      Ideal.Quotient.mk I (differentialPolynomialAffineHom S a i P) := rfl

/-- Compatible additive cocycles give commuting quotient automorphisms. -/
theorem differentialPolynomialQuotientAffineEquiv_comm
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (ha : CompatibleAdditiveCocycle S a)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) (i j : ι)
    (x : DifferentialPolynomial κ K ⧸ I) :
    differentialPolynomialQuotientAffineEquiv S a I hI i
        (differentialPolynomialQuotientAffineEquiv S a I hI j x) =
      differentialPolynomialQuotientAffineEquiv S a I hI j
        (differentialPolynomialQuotientAffineEquiv S a I hI i x) := by
  induction x using Quotient.inductionOn' with
  | _ P =>
      change Ideal.Quotient.mk I
          (differentialPolynomialAffineHom S a i
            (differentialPolynomialAffineHom S a j P)) =
        Ideal.Quotient.mk I
          (differentialPolynomialAffineHom S a j
            (differentialPolynomialAffineHom S a i P))
      rw [differentialPolynomialAffineHom_comm S a ha]

/-- The induced quotient automorphisms commute with the induced derivation. -/
theorem differentialPolynomialQuotientAffineEquiv_derivation
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) (i : ι)
    (x : DifferentialPolynomial κ K ⧸ I) :
    differentialPolynomialQuotientAffineEquiv S a I hI i
        (quotientDerivation (differentialPolynomialOverDerivation κ K) I
          (fun _ hP => hI.derivation_mem hP) x) =
      quotientDerivation (differentialPolynomialOverDerivation κ K) I
          (fun _ hP => hI.derivation_mem hP)
        (differentialPolynomialQuotientAffineEquiv S a I hI i x) := by
  induction x using Quotient.inductionOn' with
  | _ P =>
      change Ideal.Quotient.mk I
          (differentialPolynomialAffineHom S a i
            (differentialPolynomialOverDerivation κ K P)) =
        Ideal.Quotient.mk I
          (differentialPolynomialOverDerivation κ K
            (differentialPolynomialAffineHom S a i P))
      rw [differentialPolynomialAffineHom_overDerivation]

/-- The universal order-zero primitive tuple in the affine differential quotient. -/
def differentialPolynomialQuotientPrimitive
    {κ K : Type*} [Field K] (I : Ideal (DifferentialPolynomial κ K))
    (k : κ) : DifferentialPolynomial κ K ⧸ I :=
  Ideal.Quotient.mk I (MvPolynomial.X (k,0))

/-- The quotient primitive tuple satisfies the prescribed affine primitive equations exactly. -/
theorem differentialPolynomialQuotientPrimitive_equation
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) (i : ι) (k : κ) :
    differentialPolynomialQuotientAffineEquiv S a I hI i
        (differentialPolynomialQuotientPrimitive I k) -
      differentialPolynomialQuotientPrimitive I k =
        Ideal.Quotient.mk I (MvPolynomial.C (a i k)) := by
  simp [differentialPolynomialQuotientPrimitive,
    differentialPolynomialAffineHom_X]

/-- Stability of an ideal in the affine differential quotient. -/
def IsQuotientAffineDifferentialIdeal
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I)
    (J : Ideal (DifferentialPolynomial κ K ⧸ I)) : Prop :=
  (∀ ⦃x : DifferentialPolynomial κ K ⧸ I⦄, x ∈ J →
      quotientDerivation (differentialPolynomialOverDerivation κ K) I
        (fun _ hP => hI.derivation_mem hP) x ∈ J) ∧
    ∀ i x, differentialPolynomialQuotientAffineEquiv S a I hI i x ∈ J ↔ x ∈ J

/-- The inverse image of a quotient affine differential ideal is an affine differential ideal in
the universal solution ring. -/
theorem IsQuotientAffineDifferentialIdeal.comap_mk
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    {S : CommutingDifferenceDifferentialField ι C K} {a : ι → κ → K}
    {I : Ideal (DifferentialPolynomial κ K)}
    {hI : IsAffineDifferentialIdeal S a I}
    {J : Ideal (DifferentialPolynomial κ K ⧸ I)}
    (hJ : IsQuotientAffineDifferentialIdeal S a I hI J) :
    IsAffineDifferentialIdeal S a (J.comap (Ideal.Quotient.mk I)) := by
  constructor
  · intro P hP
    change Ideal.Quotient.mk I P ∈ J at hP
    change Ideal.Quotient.mk I (differentialPolynomialOverDerivation κ K P) ∈ J
    exact hJ.1 hP
  · intro i P
    change Ideal.Quotient.mk I (differentialPolynomialAffineHom S a i P) ∈ J ↔
      Ideal.Quotient.mk I P ∈ J
    exact hJ.2 i (Ideal.Quotient.mk I P)

/-- A maximal proper affine differential ideal gives an affine-differentially simple quotient:
the only quotient ideals stable under the induced derivation and every induced affine action are
`⊥` and `⊤`. -/
theorem quotient_affineDifferentialIdeal_eq_bot_or_top_of_maximal
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (M : Ideal (DifferentialPolynomial κ K))
    (hMstable : IsAffineDifferentialIdeal S a M)
    (hMmax : ∀ J : Ideal (DifferentialPolynomial κ K),
      M ≤ J → J ≠ ⊤ → IsAffineDifferentialIdeal S a J → J = M)
    (J : Ideal (DifferentialPolynomial κ K ⧸ M))
    (hJ : IsQuotientAffineDifferentialIdeal S a M hMstable J) :
    J = ⊥ ∨ J = ⊤ := by
  by_cases hJtop : J = ⊤
  · exact Or.inr hJtop
  · left
    let Jc : Ideal (DifferentialPolynomial κ K) := J.comap (Ideal.Quotient.mk M)
    have hMJc : M ≤ Jc := by
      intro P hPM
      change Ideal.Quotient.mk M P ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hPM]
      exact J.zero_mem
    have hJcproper : Jc ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one]
      intro h1
      apply hJtop
      rw [Ideal.eq_top_iff_one]
      change Ideal.Quotient.mk M 1 ∈ J
      exact h1
    have hJcstable : IsAffineDifferentialIdeal S a Jc := hJ.comap_mk
    have hJcM : Jc = M := hMmax Jc hMJc hJcproper hJcstable
    apply le_antisymm
    · intro x hx
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hPc : P ∈ Jc := hx
      rw [hJcM] at hPc
      change Ideal.Quotient.mk M P = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hPc
    · exact bot_le

end
end GaloisForLFunctions
