import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The free differential rational field

`JetField C ι` is the field of rational functions in the jet coordinates `x_j^{(m)}`,
`j ∈ ι`, `m ∈ ℕ`, equipped with the derivation that advances every jet:

`δ (x_j^{(m)}) = x_j^{(m+1)}`.

It is the free differential rational field `C⟨x_j : j ∈ ι⟩`: the coordinates `x_j = x_j^{(0)}`
are differentially independent over `C` and generate the field.

This file also introduces the coordinate partial derivations `∂/∂x_j^{(m)}` and proves the two
structural facts used by the Frechet calculus:

* the commutation rule `∂_{j,m} ∘ δ = δ ∘ ∂_{j,m} + ∂_{j,m-1}`, obtained from the fact that the
  commutator of two derivations is a derivation and agrees with `∂_{j,m-1}` on coordinates;
* every element has only finitely many nonvanishing partial derivatives, obtained from a
  fractional representation and the corresponding statement for polynomials.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- The polynomial ring on the jet coordinates. -/
abbrev JetPoly (C : Type u) (ι : Type v) [Field C] : Type (max u v) :=
  MvPolynomial (ι × ℕ) C

/-- The free differential rational field on the coordinates `x_j`, `j ∈ ι`. -/
def JetField (C : Type u) (ι : Type v) [Field C] : Type (max u v) :=
  FractionRing (JetPoly C ι)

namespace JetField

variable {C : Type u} {ι : Type v} [Field C]

noncomputable instance : Field (JetField C ι) :=
  inferInstanceAs (Field (FractionRing (JetPoly C ι)))

noncomputable instance : Algebra (JetPoly C ι) (JetField C ι) :=
  inferInstanceAs (Algebra (JetPoly C ι) (FractionRing (JetPoly C ι)))

instance : IsFractionRing (JetPoly C ι) (JetField C ι) :=
  inferInstanceAs (IsFractionRing (JetPoly C ι) (FractionRing (JetPoly C ι)))

noncomputable instance : Algebra C (JetField C ι) :=
  inferInstanceAs (Algebra C (FractionRing (JetPoly C ι)))

instance : IsScalarTower C (JetPoly C ι) (JetField C ι) :=
  inferInstanceAs (IsScalarTower C (JetPoly C ι) (FractionRing (JetPoly C ι)))

instance [CharZero C] : CharZero (JetPoly C ι) :=
  charZero_of_injective_algebraMap (MvPolynomial.C_injective (ι × ℕ) C)

instance [CharZero C] : CharZero (JetField C ι) :=
  charZero_of_injective_algebraMap
    (IsFractionRing.injective (JetPoly C ι) (JetField C ι))

/-- The jet coordinate `x_j^{(m)}` for `p = (j, m)`. -/
noncomputable def jet (p : ι × ℕ) : JetField C ι :=
  algebraMap (JetPoly C ι) (JetField C ι) (MvPolynomial.X p)

/-- The derivation of the polynomial ring advancing every jet coordinate. -/
noncomputable def jetDerivationPoly : Derivation C (JetPoly C ι) (JetField C ι) :=
  (Algebra.linearMap (JetPoly C ι) (JetField C ι)).compDer
    (MvPolynomial.mkDerivation C fun p : ι × ℕ =>
      (MvPolynomial.X (p.1, p.2 + 1) : JetPoly C ι))

/-- The derivation of the free differential field advancing every jet coordinate. -/
noncomputable def jetDerivation : Derivation C (JetField C ι) (JetField C ι) :=
  fractionRingDerivation jetDerivationPoly

noncomputable instance : Differential (JetField C ι) :=
  ⟨Derivation.restrictScalars ℤ jetDerivation⟩

theorem deriv_eq (u : JetField C ι) : u′ = jetDerivation u := rfl

@[simp] theorem deriv_jet (p : ι × ℕ) :
    (jet p : JetField C ι)′ = jet (p.1, p.2 + 1) := by
  rw [deriv_eq, jetDerivation, jet, fractionRingDerivation_algebraMap]
  show (Algebra.linearMap (JetPoly C ι) (JetField C ι))
      ((MvPolynomial.mkDerivation C fun p : ι × ℕ =>
        (MvPolynomial.X (p.1, p.2 + 1) : JetPoly C ι)) (MvPolynomial.X p)) = _
  rw [MvPolynomial.mkDerivation_X]
  rfl

/-- The coordinate partial derivation `∂/∂x_j^{(m)}` on the polynomial ring. -/
noncomputable def pdPoly (p : ι × ℕ) : Derivation C (JetPoly C ι) (JetField C ι) :=
  (Algebra.linearMap (JetPoly C ι) (JetField C ι)).compDer (MvPolynomial.pderiv p)

/-- The coordinate partial derivation `∂/∂x_j^{(m)}`. -/
noncomputable def pd (p : ι × ℕ) : Derivation C (JetField C ι) (JetField C ι) :=
  fractionRingDerivation (pdPoly p)

theorem pdPoly_apply (p : ι × ℕ) (a : JetPoly C ι) :
    pdPoly p a = algebraMap (JetPoly C ι) (JetField C ι) (MvPolynomial.pderiv p a) := rfl

theorem pd_algebraMap (p : ι × ℕ) (a : JetPoly C ι) :
    pd p (algebraMap (JetPoly C ι) (JetField C ι) a)
      = algebraMap (JetPoly C ι) (JetField C ι) (MvPolynomial.pderiv p a) := by
  rw [pd, fractionRingDerivation_algebraMap, pdPoly_apply]

@[simp] theorem pd_jet_self (p : ι × ℕ) : pd p (jet p : JetField C ι) = 1 := by
  classical
  rw [jet, pd_algebraMap, MvPolynomial.pderiv_X]
  simp

theorem pd_jet_of_ne {p q : ι × ℕ} (h : p ≠ q) : pd p (jet q : JetField C ι) = 0 := by
  classical
  rw [jet, pd_algebraMap, MvPolynomial.pderiv_X]
  simp [h]

/-- Two derivations of the free differential field agreeing on all jet coordinates are equal. -/
theorem derivation_ext {D₁ D₂ : Derivation C (JetField C ι) (JetField C ι)}
    (h : ∀ p, D₁ (jet p) = D₂ (jet p)) : D₁ = D₂ := by
  refine fractionRing_derivation_ext (A := JetPoly C ι) D₁ D₂ fun a => ?_
  have hres : D₁.compAlgebraMap (JetPoly C ι) = D₂.compAlgebraMap (JetPoly C ι) := by
    refine MvPolynomial.derivation_ext fun p => ?_
    exact h p
  exact congrArg (fun D : Derivation C (JetPoly C ι) (JetField C ι) => D a) hres

/-- The jet derivation kills every partial derivative of a coordinate, since those are `0` or
`1`. -/
theorem deriv_pd_jet (p q : ι × ℕ) :
    jetDerivation (pd p (jet q) : JetField C ι) = 0 := by
  by_cases h : p = q
  · subst h
    rw [pd_jet_self]
    exact (jetDerivation (C := C) (ι := ι)).map_one_eq_zero
  · rw [pd_jet_of_ne h, map_zero]

theorem jetDerivation_jet (q : ι × ℕ) :
    jetDerivation (jet q : JetField C ι) = jet (q.1, q.2 + 1) := by
  rw [← deriv_eq]
  exact deriv_jet q

/-- The commutator of a coordinate partial with the jet derivation is the previous coordinate
partial. -/
theorem commutator_pd_succ (j : ι) (m : ℕ) :
    ⁅pd (C := C) (ι := ι) (j, m + 1), jetDerivation (C := C) (ι := ι)⁆ = pd (j, m) := by
  refine derivation_ext fun q => ?_
  rw [Derivation.commutator_apply, jetDerivation_jet, deriv_pd_jet, sub_zero]
  by_cases hq : ((j, m) : ι × ℕ) = q
  · subst hq
    rw [pd_jet_self, pd_jet_self]
  · have hne : ((j, m + 1) : ι × ℕ) ≠ (q.1, q.2 + 1) := by
      intro hcon
      have hcon' := Prod.ext_iff.mp hcon
      have h1 : j = q.1 := hcon'.1
      have h2 : m + 1 = q.2 + 1 := hcon'.2
      have h3 : m = q.2 := by omega
      exact hq (Prod.ext_iff.mpr ⟨h1, h3⟩)
    rw [pd_jet_of_ne hne, pd_jet_of_ne hq]

/-- The commutator of the lowest coordinate partial with the jet derivation vanishes. -/
theorem commutator_pd_zero (j : ι) :
    ⁅pd (C := C) (ι := ι) (j, 0), jetDerivation (C := C) (ι := ι)⁆ = 0 := by
  refine derivation_ext fun q => ?_
  rw [Derivation.commutator_apply, jetDerivation_jet, deriv_pd_jet, sub_zero]
  have hne : ((j, 0) : ι × ℕ) ≠ (q.1, q.2 + 1) := by
    intro hcon
    exact absurd (congrArg Prod.snd hcon) (by omega)
  rw [pd_jet_of_ne hne]
  simp

/-- The commutation rule `∂_{j,m+1} (δ u) = δ (∂_{j,m+1} u) + ∂_{j,m} u`. -/
theorem pd_deriv_succ (j : ι) (m : ℕ) (u : JetField C ι) :
    pd ((j, m + 1) : ι × ℕ) (u′) = (pd ((j, m + 1) : ι × ℕ) u)′ + pd ((j, m) : ι × ℕ) u := by
  have h := congrArg (fun D : Derivation C (JetField C ι) (JetField C ι) => D u)
    (commutator_pd_succ (C := C) (ι := ι) j m)
  simp only [Derivation.commutator_apply] at h
  rw [deriv_eq, deriv_eq, ← h]
  abel

/-- The lowest partial commutes with the jet derivation. -/
theorem pd_deriv_zero (j : ι) (u : JetField C ι) :
    pd ((j, 0) : ι × ℕ) (u′) = (pd ((j, 0) : ι × ℕ) u)′ := by
  have h := congrArg (fun D : Derivation C (JetField C ι) (JetField C ι) => D u)
    (commutator_pd_zero (C := C) (ι := ι) j)
  simp only [Derivation.commutator_apply] at h
  rw [deriv_eq, deriv_eq]
  have h0 : pd ((j, 0) : ι × ℕ) (jetDerivation u) - jetDerivation (pd ((j, 0) : ι × ℕ) u) = 0 := by
    simpa using h
  exact sub_eq_zero.mp h0

/-- Only finitely many coordinate partials of an element are nonzero. -/
theorem exists_finset_pd_eq_zero (u : JetField C ι) :
    ∃ s : Finset (ι × ℕ), ∀ p ∉ s, pd p u = 0 := by
  classical
  obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors (JetPoly C ι)) u
  refine ⟨a.vars ∪ (b : JetPoly C ι).vars, fun p hp => ?_⟩
  have hpa : p ∉ a.vars := fun h => hp (Finset.mem_union_left _ h)
  have hpb : p ∉ (b : JetPoly C ι).vars := fun h => hp (Finset.mem_union_right _ h)
  have hda : pd p (algebraMap (JetPoly C ι) (JetField C ι) a) = 0 := by
    rw [pd_algebraMap, MvPolynomial.pderiv_eq_zero_of_notMem_vars hpa, map_zero]
  have hdb : pd p (algebraMap (JetPoly C ι) (JetField C ι) (b : JetPoly C ι)) = 0 := by
    rw [pd_algebraMap, MvPolynomial.pderiv_eq_zero_of_notMem_vars hpb, map_zero]
  have hbne : algebraMap (JetPoly C ι) (JetField C ι) (b : JetPoly C ι) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hmul := congrArg (pd p) hb
  rw [Derivation.leibniz, hdb, hda, smul_zero, zero_add, smul_eq_mul] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hbne

end JetField

end GaloisForLFunctions.HTGeometry
