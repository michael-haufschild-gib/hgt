import GaloisForLFunctions.HTGeometry.DifferentialTangentAdjoint

/-!
# The differential evaluation commutes with a differential algebra map

Evaluating a differential polynomial at a point is `aeval` on the jets of the coordinates, so it
commutes with any algebra map that commutes with the derivation: the map moves through every jet by
induction, and two algebra maps out of a polynomial ring agreeing on the variables are equal.

Consequently a differential algebra map carries the zero set of a family of differential
polynomials into the zero set of the same family over the target — the transfer used whenever a
construction moves between a differential ring and an extension of it, for instance between a ring
and its dual numbers.

* `differentialJet_algHom`, `evalOver_algHom`;
* `evalOver_ringHom`, `matrixZeroSet_algHom`, `matrixZeroSet_ringHom`;
* `evalOver_inl'` — the base-embedding case, recovered from the general statement.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C]

/-- **A derivation-compatible ring map moves through every jet.** -/
theorem differentialJet_algHom {A B : Type*} [CommRing A] [CommRing B]
    [Differential A] [Differential B] (φ : A →+* B)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a)) (n : ℕ) (a : A) :
    φ (differentialJet n a) = differentialJet n (φ a) := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, hφ, ih]

omit [Differential C] in
/-- **The differential evaluation commutes with a differential algebra map.** -/
theorem evalOver_algHom {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] [Differential A] [Differential B] (φ : A →ₐ[C] B)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    {ι : Type*} (x : ι → A) (P : DifferentialPolynomial ι C) :
    φ (differentialPolynomialEvalOver (K := C) x P)
      = differentialPolynomialEvalOver (K := C) (fun i => φ (x i)) P := by
  have key : φ.comp (differentialPolynomialEvalOver (K := C) x)
      = differentialPolynomialEvalOver (K := C) (fun i => φ (x i)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, differentialPolynomialEvalOver_X, differentialPolynomialEvalOver_X]
    exact differentialJet_algHom (φ : A →+* B) hφ v.2 (x v.1)
  rw [← key, AlgHom.comp_apply]

omit [Differential C] in
/-- **The ring-map form.**  Only compatibility with the derivation and with the constants is
needed; no algebra structure on the target over the source has to be found. -/
theorem evalOver_ringHom {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] [Differential A] [Differential B] (φ : A →+* B)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    (hC : ∀ c : C, φ (algebraMap C A c) = algebraMap C B c)
    {ι : Type*} (x : ι → A) (P : DifferentialPolynomial ι C) :
    φ (differentialPolynomialEvalOver (K := C) x P)
      = differentialPolynomialEvalOver (K := C) (fun i => φ (x i)) P := by
  have key : φ.comp ((differentialPolynomialEvalOver (K := C) x).toRingHom)
      = (differentialPolynomialEvalOver (K := C) (fun i => φ (x i))).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · rw [RingHom.comp_apply]
      show φ (differentialPolynomialEvalOver (K := C) x (MvPolynomial.C c)) = _
      rw [differentialPolynomialEvalOver_C, hC]
      exact (differentialPolynomialEvalOver_C (K := C) (fun i => φ (x i)) c).symm
    · rw [RingHom.comp_apply]
      show φ (differentialPolynomialEvalOver (K := C) x (MvPolynomial.X v)) = _
      rw [differentialPolynomialEvalOver_X]
      show _ = differentialPolynomialEvalOver (K := C) (fun i => φ (x i)) (MvPolynomial.X v)
      rw [differentialPolynomialEvalOver_X]
      exact differentialJet_algHom φ hφ v.2 (x v.1)
  exact congrArg (fun f => f P) key

section ZeroSetRingHom

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

omit [Differential C] in
/-- **A derivation- and constant-compatible ring map carries the zero set into the zero set.** -/
theorem matrixZeroSet_ringHom {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] [Differential A] [Differential B] (φ : A →+* B)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    (hC : ∀ c : C, φ (algebraMap C A c) = algebraMap C B c)
    {g : Matrix (Fin 2) (Fin 2) A} (hg : g ∈ matrixZeroSet (C := C) (A := A) S) :
    (fun i j => φ (g i j)) ∈ matrixZeroSet (C := C) (A := B) S := by
  intro P hP
  have h := evalOver_ringHom (C := C) φ hφ hC (fun q : Fin 2 × Fin 2 => g q.1 q.2) P
  rw [hg P hP, map_zero] at h
  exact h.symm

end ZeroSetRingHom

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

omit [Differential C] in
/-- **A differential algebra map carries the zero set into the zero set.** -/
theorem matrixZeroSet_algHom {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] [Differential A] [Differential B] (φ : A →ₐ[C] B)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    {g : Matrix (Fin 2) (Fin 2) A} (hg : g ∈ matrixZeroSet (C := C) (A := A) S) :
    (fun i j => φ (g i j)) ∈ matrixZeroSet (C := C) (A := B) S := by
  intro P hP
  have h := evalOver_algHom (C := C) φ hφ (fun q : Fin 2 × Fin 2 => g q.1 q.2) P
  rw [hg P hP, map_zero] at h
  exact h.symm

/-- The base-embedding case, recovered from the general statement. -/
theorem evalOver_inl' {ι : Type*} (x : ι → C) (P : DifferentialPolynomial ι C) :
    differentialPolynomialEvalOver (K := C)
        (fun i => (TrivSqZeroExt.inl (x i) : DualNumber C)) P
      = TrivSqZeroExt.inl (differentialPolynomialEvalOver (K := C) x P) :=
  (evalOver_algHom (C := C) (TrivSqZeroExt.inlAlgHom C C C)
    (fun a => by
      show TrivSqZeroExt.inl (Differential.deriv a) = Differential.deriv
        (TrivSqZeroExt.inl a : DualNumber C)
      apply TrivSqZeroExt.ext
      · simp
      · simp) x P).symm

end

end GaloisForLFunctions.HTGeometry
