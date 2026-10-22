import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Lifting homomorphisms along an integral extension

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the mechanism behind
Theorem 1.4 and Corollary 1.5(1).

If `B` is integral over `A` and the structure map `A → B` is injective, then every ring
homomorphism from `A` into an algebraically closed field extends to `B`.  One takes the prime
`𝔭 = ker φ`, produces a prime `𝔮` of `B` lying over it, and extends the induced embedding
`A / 𝔭 ↪ C` along the algebraic extension `B / 𝔮`.

Mathlib has the two ingredients — lying over and `IsAlgClosed.lift` — but not this statement.
-/

namespace RHTower

open Ideal

variable {A B C : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field C]

/-- **Lifting along an integral extension.**  A homomorphism into an algebraically closed field
extends along an injective integral ring extension. -/
theorem deningerHom_exists_extension_of_isIntegral [Algebra.IsIntegral A B] [FaithfulSMul A B]
    [IsAlgClosed C] (φ : A →+* C) :
    ∃ ψ : B →+* C, ∀ a : A, ψ (algebraMap A B a) = φ a := by
  classical
  haveI hPp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQp, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker φ) ⊥
      (fun a ha => by
        have h0 : algebraMap A B a = 0 := by simpa using ha
        have ha0 : a = 0 :=
          FaithfulSMul.algebraMap_injective A B (by rw [h0, map_zero])
        rw [ha0]
        exact Ideal.zero_mem _)
  haveI := hQp
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQ.symm⟩
  set P : Ideal A := RingHom.ker φ with hPdef
  letI φbar : (A ⧸ P) →+* C := Ideal.Quotient.lift P φ (fun a ha => ha)
  have hφbarinj : Function.Injective φbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxa : φ a = 0 := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxa
  letI : Algebra (A ⧸ P) C := φbar.toAlgebra
  haveI : FaithfulSMul (A ⧸ P) C :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) C).mpr hφbarinj
  have hinjq : Function.Injective (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : (algebraMap (A ⧸ P) (B ⧸ Q)) (Ideal.Quotient.mk P a)
        = Ideal.Quotient.mk Q (algebraMap A B a) := rfl
    rw [h1, Ideal.Quotient.eq_zero_iff_mem] at hx
    have hmem : a ∈ Ideal.comap (algebraMap A B) Q := hx
    rw [hQ] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  haveI : FaithfulSMul (A ⧸ P) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) (B ⧸ Q)).mpr hinjq
  haveI : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  let f : (B ⧸ Q) →ₐ[A ⧸ P] C := IsAlgClosed.lift
  refine ⟨(f : (B ⧸ Q) →+* C).comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  show f (Ideal.Quotient.mk Q (algebraMap A B a)) = φ a
  have h1 : (Ideal.Quotient.mk Q (algebraMap A B a))
      = algebraMap (A ⧸ P) (B ⧸ Q) (Ideal.Quotient.mk P a) := rfl
  rw [h1, AlgHom.commutes]
  rfl

/-- **Lifting along an integral extension**, in restriction form. -/
theorem deningerHom_restrict_surjective_of_isIntegral [Algebra.IsIntegral A B] [FaithfulSMul A B]
    [IsAlgClosed C] :
    Function.Surjective (fun ψ : B →+* C => ψ.comp (algebraMap A B)) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := deningerHom_exists_extension_of_isIntegral (A := A) (B := B) φ
  exact ⟨ψ, RingHom.ext hψ⟩

end RHTower

namespace RHTower

/-- **Lifting along an integral extension, unbundled form.**  A homomorphism into an algebraically
closed field extends along an injective integral ring homomorphism. -/
theorem deningerHom_exists_extension_of_ringHom_isIntegral {A B C : Type*} [CommRing A]
    [CommRing B] [Field C] [IsAlgClosed C] (f : A →+* B) (hf : f.IsIntegral)
    (hinj : Function.Injective f) (φ : A →+* C) :
    ∃ ψ : B →+* C, ψ.comp f = φ := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨fun x => hf x⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  obtain ⟨ψ, hψ⟩ := deningerHom_exists_extension_of_isIntegral (A := A) (B := B) (C := C) φ
  exact ⟨ψ, RingHom.ext hψ⟩

end RHTower
