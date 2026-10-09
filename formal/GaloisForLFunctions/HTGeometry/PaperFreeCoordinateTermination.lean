import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoordinateDerivation
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import GaloisForLFunctions.HTGeometry.LocallyNilpotentDerivationSlice

/-! # Exact termination criterion for native rational coordinate derivatives

The paper's local nilpotence theorem and the native slice theorem identify exactly
which rational functions have a terminating coordinate-derivative chain. They are
the polynomials in that coordinate with coefficients in the complementary
coordinate field, and their polynomial expression is unique.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

local instance paperFreeCoordinateRatModule {σ : Type*} :
    Module ℚ (FreeCoordinateRationalField ℂ σ) := Algebra.toModule

private theorem derivation_aeval_single {B : Type*} [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (s : B) (hs : D s = 1)
    (p : MvPolynomial Unit (derivationKernel D)) :
    D (MvPolynomial.aeval (fun _ : Unit => s) p) =
      MvPolynomial.aeval (fun _ : Unit => s) (MvPolynomial.pderiv () p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero]
      exact c.property
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      cases j
      simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hp, hs,
        MvPolynomial.pderiv_X_self, smul_eq_mul, map_add, map_one]

private theorem iterate_derivation_aeval_single {B : Type*} [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (s : B) (hs : D s = 1)
    (p : MvPolynomial Unit (derivationKernel D)) (n : ℕ) :
    ((D : B → B)^[n]) (MvPolynomial.aeval (fun _ : Unit => s) p) =
      MvPolynomial.aeval (fun _ : Unit => s)
        (((MvPolynomial.pderiv () : Derivation (derivationKernel D)
          (MvPolynomial Unit (derivationKernel D)) (MvPolynomial Unit (derivationKernel D))) :
          MvPolynomial Unit (derivationKernel D) → MvPolynomial Unit (derivationKernel D))^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih, derivation_aeval_single D s hs]

private theorem polynomial_in_slice_terminates {B : Type*} [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (s : B) (hs : D s = 1)
    (p : Polynomial (derivationKernel D)) :
    ∃ n : ℕ, ((D : B → B)^[n]) (Polynomial.aeval s p) = 0 := by
  let e : MvPolynomial Unit (derivationKernel D) →ₐ[derivationKernel D] B :=
    MvPolynomial.aeval (fun _ => s)
  let q : MvPolynomial Unit (derivationKernel D) := Polynomial.aeval (MvPolynomial.X ()) p
  have he : e q = Polynomial.aeval s p := by
    have h := congrArg (fun h : Polynomial (derivationKernel D) →ₐ[derivationKernel D] B => h p)
      (Polynomial.aeval_algHom e (MvPolynomial.X ()))
    simpa only [AlgHom.comp_apply, e, MvPolynomial.aeval_X] using h.symm
  obtain ⟨n, hn⟩ := StableCoordinate.CoordinateDerivation.pderiv_locallyNilpotent () q
  refine ⟨n, ?_⟩
  rw [← he]
  change ((D : B → B)^[n]) (MvPolynomial.aeval (fun _ : Unit => s) q) = 0
  rw [iterate_derivation_aeval_single D s hs, hn, map_zero]

/-- The actual constants of one native coordinate derivative, retaining the native field. -/
def paperFreeCoordinateConstants {σ : Type*} (i : σ) :
    Subalgebra ℚ (FreeCoordinateRationalField ℂ σ) :=
  derivationKernel ((freeCoordinateDerivation ℂ σ i).restrictScalars ℚ)

/-- The coefficient ring is exactly the rational field on all the other coordinates. -/
theorem paperFreeCoordinateConstants_iff {σ : Type*} (i : σ)
    (f : FreeCoordinateRationalField ℂ σ) :
    f ∈ paperFreeCoordinateConstants i ↔ f ∈ freeCoordinateField ℂ σ {i}ᶜ := by
  change freeCoordinateDerivation ℂ σ i f = 0 ↔ _
  rw [mem_freeCoordinateField_iff]
  simp

/-- Iteration of the native quotient-rule derivative preserves the literal polynomial embedding. -/
theorem paperFreeCoordinate_iterate_polynomial {σ : Type*} (i : σ)
    (p : MvPolynomial σ ℂ) (n : ℕ) :
    ((freeCoordinateDerivation ℂ σ i : FreeCoordinateRationalField ℂ σ →
      FreeCoordinateRationalField ℂ σ)^[n])
        (algebraMap (MvPolynomial σ ℂ) (FreeCoordinateRationalField ℂ σ) p) =
      algebraMap (MvPolynomial σ ℂ) (FreeCoordinateRationalField ℂ σ)
        (((MvPolynomial.pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
          MvPolynomial σ ℂ → MvPolynomial σ ℂ)^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, freeCoordinateDerivation_algebraMap]

/-- Every literal polynomial has a terminating derivative chain inside the native fraction field. -/
theorem paperFreeCoordinate_polynomial_terminates {σ : Type*} (i : σ)
    (p : MvPolynomial σ ℂ) :
    ∃ n : ℕ, ((freeCoordinateDerivation ℂ σ i : FreeCoordinateRationalField ℂ σ →
      FreeCoordinateRationalField ℂ σ)^[n])
        (algebraMap (MvPolynomial σ ℂ) (FreeCoordinateRationalField ℂ σ) p) = 0 := by
  obtain ⟨n, hn⟩ := StableCoordinate.CoordinateDerivation.pderiv_locallyNilpotent i p
  exact ⟨n, by rw [paperFreeCoordinate_iterate_polynomial, hn, map_zero]⟩

/-- Polynomial expressions over the complementary coordinate field are unique. -/
theorem paperFreeCoordinate_polynomial_eval_injective {σ : Type*} (i : σ) :
    Function.Injective (Polynomial.aeval (freeCoordinate ℂ σ i) :
      Polynomial (paperFreeCoordinateConstants i) → FreeCoordinateRationalField ℂ σ) :=
  aeval_slice_injective ((freeCoordinateDerivation ℂ σ i).restrictScalars ℚ)
    (freeCoordinateDerivation_freeCoordinate_self (C := ℂ) i)

/-- Exact classification of all rational functions with a finite coordinate-derivative chain. -/
theorem paperFreeCoordinate_termination_iff {σ : Type*} (i : σ)
    (f : FreeCoordinateRationalField ℂ σ) :
    (∃ n : ℕ, ((freeCoordinateDerivation ℂ σ i : FreeCoordinateRationalField ℂ σ →
      FreeCoordinateRationalField ℂ σ)^[n]) f = 0) ↔
      ∃ p : Polynomial (paperFreeCoordinateConstants i),
        Polynomial.aeval (freeCoordinate ℂ σ i) p = f := by
  constructor
  · rintro ⟨n, hn⟩
    exact exists_polynomial_of_iterate_eq_zero
      ((freeCoordinateDerivation ℂ σ i).restrictScalars ℚ)
      (freeCoordinateDerivation_freeCoordinate_self (C := ℂ) i) n f hn
  · rintro ⟨p, rfl⟩
    exact polynomial_in_slice_terminates ((freeCoordinateDerivation ℂ σ i).restrictScalars ℚ)
      (freeCoordinate ℂ σ i) (freeCoordinateDerivation_freeCoordinate_self (C := ℂ) i) p

/-- The finite-chain condition gives a unique polynomial normal form over the other coordinates. -/
theorem paperFreeCoordinate_termination_iff_unique {σ : Type*} (i : σ)
    (f : FreeCoordinateRationalField ℂ σ) :
    (∃ n : ℕ, ((freeCoordinateDerivation ℂ σ i : FreeCoordinateRationalField ℂ σ →
      FreeCoordinateRationalField ℂ σ)^[n]) f = 0) ↔
      ∃! p : Polynomial (paperFreeCoordinateConstants i),
        Polynomial.aeval (freeCoordinate ℂ σ i) p = f := by
  rw [paperFreeCoordinate_termination_iff]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hp, fun q hq => paperFreeCoordinate_polynomial_eval_injective i (hq.trans hp.symm)⟩
  · rintro ⟨p, hp, _⟩
    exact ⟨p, hp⟩

/-- Inverting the selected coordinate destroys termination at every finite derivative order. -/
theorem paperFreeCoordinate_reciprocal_iterate_ne_zero {σ : Type*} (i : σ) (n : ℕ) :
    ((freeCoordinateDerivation ℂ σ i : FreeCoordinateRationalField ℂ σ →
      FreeCoordinateRationalField ℂ σ)^[n]) (freeCoordinate ℂ σ i)⁻¹ ≠ 0 := by
  intro hn
  obtain ⟨p, hp⟩ := (paperFreeCoordinate_termination_iff i (freeCoordinate ℂ σ i)⁻¹).mp ⟨n, hn⟩
  have hx : freeCoordinate ℂ σ i ≠ 0 := by
    intro h
    have hd := freeCoordinateDerivation_freeCoordinate_self (C := ℂ) i
    rw [h, map_zero] at hd
    exact zero_ne_one hd
  have hpoly : (Polynomial.X : Polynomial (paperFreeCoordinateConstants i)) * p = 1 :=
    paperFreeCoordinate_polynomial_eval_injective i (by
      simp only [map_mul, Polynomial.aeval_X, hp, map_one, mul_inv_cancel₀ hx])
  have hz := congrArg (Polynomial.eval (0 : paperFreeCoordinateConstants i)) hpoly
  simp at hz

end
end GaloisForLFunctions.HTGeometry
