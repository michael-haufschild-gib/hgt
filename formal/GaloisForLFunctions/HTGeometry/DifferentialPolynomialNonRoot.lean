import GaloisForLFunctions.HTGeometry.LinearSystemFundamentalMatrix
import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange

/-!
# A nonzero differential polynomial has a non-root over a differentially closed field

Differential closedness is stated for *systems of equations*, but an inequation is an equation in
one more indeterminate: `F(x) ≠ 0` is `t·F(x) = 1`.  The auxiliary system has a solution in the
free differential field `C⟨y⟩` — the generic point, where `F` evaluates to itself — so it has one
in `C`.

* `differentialPolynomialEvalOver_generic` — evaluating at the generic point is the identity;
* `scalarDiffFieldExt` — `C⟨y⟩` as a differential field extension of `C`;
* `exists_evalOver_ne_zero` — **a nonzero differential polynomial does not vanish identically.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable {C : Type u} [Field C] [Algebra ℚ C] [Differential C]

omit [Algebra ℚ C] [Differential C] in
/-- **Evaluating a differential polynomial at the generic point returns it unchanged.** -/
theorem differentialPolynomialEvalOver_generic {ι : Type*}
    [Differential (DifferentialPolynomial ι C)]
    (hX : ∀ (i : ι) (n : ℕ), (MvPolynomial.X ((i, n) : ι × ℕ) : DifferentialPolynomial ι C)′
      = MvPolynomial.X ((i, n + 1) : ι × ℕ))
    (F : DifferentialPolynomial ι C) :
    differentialPolynomialEvalOver (K := C) (fun i => MvPolynomial.X (i, 0)) F = F := by
  have hjet : ∀ (i : ι) (n : ℕ),
      differentialJet n (MvPolynomial.X ((i, 0) : ι × ℕ) : DifferentialPolynomial ι C)
        = MvPolynomial.X ((i, n) : ι × ℕ) := by
    intro i n
    induction n with
    | zero => rw [differentialJet_zero]
    | succ n ih => rw [differentialJet_succ, ih, hX]
  have hpt : (fun v : ι × ℕ =>
      differentialJet v.2 (MvPolynomial.X ((v.1, 0) : ι × ℕ) : DifferentialPolynomial ι C))
      = MvPolynomial.X := funext fun v => hjet v.1 v.2
  show (MvPolynomial.aeval (fun v : ι × ℕ =>
    differentialJet v.2 (MvPolynomial.X ((v.1, 0) : ι × ℕ)
      : DifferentialPolynomial ι C))) F = F
  rw [hpt, MvPolynomial.aeval_X_left, AlgHom.id_apply]

/-- The free differential field `C⟨y⟩` as a differential field extension of `C`. -/
def scalarDiffFieldExt (C : Type u) [Field C] [Algebra ℚ C] [Differential C] : DiffFieldExt C :=
  letI : Differential (DifferentialPolynomial Unit C) := differentialPolynomialOverDifferential Unit C
  letI : Differential (FractionRing (DifferentialPolynomial Unit C)) := fractionRingDifferential _
  { carrier := FractionRing (DifferentialPolynomial Unit C)
    compat := by
      intro a
      have halg : algebraMap C (FractionRing (DifferentialPolynomial Unit C)) a
          = algebraMap (DifferentialPolynomial Unit C) (FractionRing (DifferentialPolynomial Unit C))
              (algebraMap C (DifferentialPolynomial Unit C) a) := by
        rw [← IsScalarTower.algebraMap_apply]
      have halg' : algebraMap C (FractionRing (DifferentialPolynomial Unit C)) (a′)
          = algebraMap (DifferentialPolynomial Unit C) (FractionRing (DifferentialPolynomial Unit C))
              (algebraMap C (DifferentialPolynomial Unit C) (a′)) := by
        rw [← IsScalarTower.algebraMap_apply]
      rw [halg, halg', fractionRingDifferential_algebraMap]
      congr 1
      show differentialPolynomialOverDerivation Unit C (MvPolynomial.C a) = MvPolynomial.C (a′)
      rw [differentialPolynomialOverDerivation_C] }

/-- **A nonzero differential polynomial over a differentially closed field has a non-root.** -/
theorem exists_evalOver_ne_zero [IsDifferentiallyClosed C]
    {F : DifferentialPolynomial Unit C} (hF : F ≠ 0) :
    ∃ c : C, differentialPolynomialEvalOver (K := C) (fun _ : Unit => c) F ≠ 0 := by
  classical
  letI : Differential (DifferentialPolynomial Unit C) := differentialPolynomialOverDifferential Unit C
  letI : Differential (FractionRing (DifferentialPolynomial Unit C)) := fractionRingDifferential _
  set E : DiffFieldExt C := scalarDiffFieldExt C with hE
  set P : DifferentialPolynomial Bool C :=
    differentialRename (K := C) (fun _ : Unit => false) F with hP
  set Q : DifferentialPolynomial Bool C := P * MvPolynomial.X (true, 0) - 1 with hQ
  -- the generic point solves the auxiliary system
  set g : FractionRing (DifferentialPolynomial Unit C) :=
    algebraMap (DifferentialPolynomial Unit C) (FractionRing (DifferentialPolynomial Unit C)) F
    with hg
  have hgne : g ≠ 0 := by
    rw [hg]
    exact fun hcon => hF ((IsFractionRing.injective (DifferentialPolynomial Unit C)
      (FractionRing (DifferentialPolynomial Unit C))) (by simpa using hcon))
  set z : Bool → E.carrier := fun b =>
    cond b g⁻¹
      (algebraMap (DifferentialPolynomial Unit C) (FractionRing (DifferentialPolynomial Unit C))
        (MvPolynomial.X (((), 0) : Unit × ℕ))) with hz
  have hXover : ∀ (i : Unit) (n : ℕ),
      (MvPolynomial.X ((i, n) : Unit × ℕ) : DifferentialPolynomial Unit C)′
        = MvPolynomial.X ((i, n + 1) : Unit × ℕ) := by
    intro i n
    show differentialPolynomialOverDerivation Unit C (MvPolynomial.X (i, n)) = _
    rw [differentialPolynomialOverDerivation_X]
  have hPz : differentialPolynomialEvalOver (K := C) z P = g := by
    rw [hP, differentialPolynomialEvalOver_differentialRename]
    have hmap := map_differentialPolynomialEvalOver
      (φ := (algebraMap (DifferentialPolynomial Unit C)
        (FractionRing (DifferentialPolynomial Unit C)) : _ →+* _))
      (fun x => (fractionRingDifferential_algebraMap (DifferentialPolynomial Unit C) x).symm)
      (fun a => by rw [← IsScalarTower.algebraMap_apply])
      (fun i : Unit => (MvPolynomial.X ((i, 0) : Unit × ℕ) : DifferentialPolynomial Unit C)) F
    rw [differentialPolynomialEvalOver_generic hXover] at hmap
    rw [hg, hmap]
    congr 1
  have hsol : ∀ p ∈ ({Q} : Finset (DifferentialPolynomial Bool C)),
      differentialPolynomialEvalOver (K := C) z p = 0 := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    have hzt : z true = g⁻¹ := rfl
    rw [hQ, map_sub, map_mul, map_one, hPz, differentialPolynomialEvalOver_X,
      differentialJet_zero, hzt]
    rw [sub_eq_zero]
    exact mul_inv_cancel₀ hgne
  obtain ⟨y, hy⟩ := IsDifferentiallyClosed.exists_point_finite (C := C) {Q} E z hsol
  have hyQ := hy Q (Finset.mem_singleton_self Q)
  rw [hQ, map_sub, map_mul, map_one, hP, differentialPolynomialEvalOver_differentialRename] at hyQ
  refine ⟨y false, fun hcon => ?_⟩
  rw [hcon, zero_mul, zero_sub, neg_eq_zero] at hyQ
  exact one_ne_zero hyQ

end

end GaloisForLFunctions.HTGeometry
