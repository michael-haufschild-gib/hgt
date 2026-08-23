import GaloisForLFunctions.RHTower.DeningerDynSysGaloisOrbitFinite
import GaloisForLFunctions.RHTower.DeningerDynSysInsepSubringHom
import GaloisForLFunctions.RHTower.DeningerDynSysWittHomCharacters

/-!
# Corollary 1.5(1): homomorphisms of `W_rat (κ₀)` come from characters of `κˣ`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1)
(`t28n`).

By Proposition 1.3 the image of `W_rat (κ₀)` inside `ℤ̲κ` is `(ℤ̲κ / κ₀)^H`.  The Galois orbits on
`ℤ̲κ / κ₀` are finite, so that ring is integral over its invariants and a homomorphism into an
algebraically closed field extends; a further extension along `ℤ̲κ / κ₀ ⊆ ℤ̲κ` — bijective on
homomorphisms — turns it into a character of `κˣ`.  Hence every homomorphism `W_rat (κ₀) → C` is
induced by a character of `κˣ`, which is the surjectivity in Deninger's chain of bijections.
-/

namespace RHTower

noncomputable section

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [Algebra.IsAlgebraic F E] [IsAlgClosed E]

/-- The Galois action restricts to Deninger's subring. -/
scoped instance deningerInsepSubringGaloisAction :
    MulSemiringAction (E ≃ₐ[F] E) ↥(deningerInsepSubring F E q) where
  smul σ x := ⟨σ • (x : MonoidAlgebra ℤ Eˣ), deningerInsepSubring_smul_mem q σ x.2⟩
  one_smul _x := Subtype.ext (one_smul _ _)
  mul_smul _σ _τ _x := Subtype.ext (mul_smul _ _ _)
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ _x _y := Subtype.ext (smul_add σ _ _)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ _x _y := Subtype.ext (smul_mul' σ _ _)

omit [IsAlgClosed E] in
theorem deningerInsepSubring_smul_val (σ : E ≃ₐ[F] E) (x : ↥(deningerInsepSubring F E q)) :
    ((σ • x : ↥(deningerInsepSubring F E q)) : MonoidAlgebra ℤ Eˣ)
      = σ • (x : MonoidAlgebra ℤ Eˣ) := rfl

omit [IsAlgClosed E] in
/-- The Galois orbits on `ℤ̲κ / κ₀` are finite. -/
theorem deningerInsepSubringOrbit_finite (x : ↥(deningerInsepSubring F E q)) :
    (MulAction.orbit (E ≃ₐ[F] E) x).Finite := by
  refine Set.Finite.of_finite_image ?_ (Subtype.val_injective.injOn)
  refine Set.Finite.subset
    (deningerMonoidAlgebraOrbit_finite (F := F) (x : MonoidAlgebra ℤ Eˣ)) ?_
  rintro _ ⟨y, ⟨σ, rfl⟩, rfl⟩
  exact ⟨σ, rfl⟩

end

end RHTower

namespace RHTower

noncomputable section

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [IsAlgClosure F E] [IsAlgClosed E] [Algebra.IsAlgebraic F E]

/-- The comparison `W_rat (κ₀) → ℤ̲κ`. -/
def deningerWittToMonoidAlgebra :
    DeningerCanonicalRationalWittRing F →+* MonoidAlgebra ℤ Eˣ :=
  ((deningerOmegaRingEquiv E).symm : DeningerCanonicalRationalWittRing E →+*
      MonoidAlgebra ℤ Eˣ).comp (deningerCanonicalRationalWittMap (algebraMap F E))

omit [IsAlgClosure F E] [Algebra.IsAlgebraic F E] in
theorem deningerWittToMonoidAlgebra_omega (w₀ : DeningerCanonicalRationalWittRing F) :
    deningerOmegaAddHom E (deningerWittToMonoidAlgebra (F := F) (E := E) w₀)
      = deningerCanonicalRationalWittMap (algebraMap F E) w₀ :=
  (deningerOmegaRingEquiv E).apply_symm_apply _

omit [IsAlgClosure F E] [Algebra.IsAlgebraic F E] in
theorem deningerWittToMonoidAlgebra_injective :
    Function.Injective (deningerWittToMonoidAlgebra (F := F) (E := E)) := by
  intro x y hxy
  have h := congrArg (deningerOmegaAddHom E) hxy
  rw [deningerWittToMonoidAlgebra_omega (F := F) (E := E),
    deningerWittToMonoidAlgebra_omega (F := F) (E := E)] at h
  exact deningerCanonicalRationalWittMap_injective (algebraMap F E)
    (algebraMap F E).injective h

/-- The image of `W_rat (κ₀)` in `ℤ̲κ` is invariant and lies in `ℤ̲κ / κ₀`. -/
theorem deningerWittToMonoidAlgebra_mem [DecidableEq Eˣ]
    [DecidableEq (Polynomial (perfectClosure F E))] (w₀ : DeningerCanonicalRationalWittRing F) :
    (∀ σ : E ≃ₐ[F] E, σ • (deningerWittToMonoidAlgebra (F := F) (E := E) w₀)
        = deningerWittToMonoidAlgebra (F := F) (E := E) w₀)
      ∧ deningerWittToMonoidAlgebra (F := F) (E := E) w₀ ∈ deningerInsepSubring F E q :=
  (deningerOmega_mem_image_iff (F := F) (E := E) q
    (deningerWittToMonoidAlgebra (F := F) (E := E) w₀)).1
    ⟨w₀, (deningerWittToMonoidAlgebra_omega (F := F) (E := E) w₀).symm⟩

/-- Conversely, an invariant class in `ℤ̲κ / κ₀` comes from `W_rat (κ₀)`. -/
theorem deningerWittToMonoidAlgebra_exists [DecidableEq Eˣ]
    [DecidableEq (Polynomial (perfectClosure F E))] {ξ : MonoidAlgebra ℤ Eˣ}
    (hinv : ∀ σ : E ≃ₐ[F] E, σ • ξ = ξ) (hmem : ξ ∈ deningerInsepSubring F E q) :
    ∃ w₀ : DeningerCanonicalRationalWittRing F,
      deningerWittToMonoidAlgebra (F := F) (E := E) w₀ = ξ := by
  obtain ⟨w₀, hw₀⟩ := (deningerOmega_mem_image_iff (F := F) (E := E) q ξ).2 ⟨hinv, hmem⟩
  refine ⟨w₀, ?_⟩
  refine (deningerOmegaRingEquiv E).injective ?_
  show deningerOmegaAddHom E (deningerWittToMonoidAlgebra (F := F) (E := E) w₀)
    = deningerOmegaAddHom E ξ
  rw [deningerWittToMonoidAlgebra_omega]
  exact hw₀

end

end RHTower

namespace RHTower

noncomputable section

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [IsAlgClosure F E] [IsAlgClosed E] [Algebra.IsAlgebraic F E]

omit [IsAlgClosure F E] [IsAlgClosed E] in
/-- The orbit polynomial of an element of `ℤ̲κ / κ₀` has coefficients in `ℤ̲κ / κ₀`. -/
theorem deningerOrbitPolynomial_coeff_mem {ξ : MonoidAlgebra ℤ Eˣ}
    (hmem : ξ ∈ deningerInsepSubring F E q) (n : ℕ) :
    (deningerOrbitPolynomial (fun b : MonoidAlgebra ℤ Eˣ =>
        deningerMonoidAlgebraOrbit_finite (F := F) b) ξ).coeff n
      ∈ deningerInsepSubring F E q := by
  classical
  set hfin : ∀ b : MonoidAlgebra ℤ Eˣ, (MulAction.orbit (E ≃ₐ[F] E) b).Finite :=
    fun b => deningerMonoidAlgebraOrbit_finite (F := F) b with hfindef
  have hlift : deningerOrbitPolynomial hfin ξ
      ∈ Polynomial.lifts ((deningerInsepSubring F E q).subtype) := by
    rw [deningerOrbitPolynomial]
    refine Subsemiring.prod_mem _ ?_
    intro c hc
    have hcmem : c ∈ deningerInsepSubring F E q := by
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨σ, rfl⟩ := hc
      exact deningerInsepSubring_smul_mem q σ hmem
    have hX : (Polynomial.X : Polynomial (MonoidAlgebra ℤ Eˣ))
        ∈ Polynomial.lifts ((deningerInsepSubring F E q).subtype) :=
      Polynomial.X_mem_lifts _
    have hC : (Polynomial.C (-c) : Polynomial (MonoidAlgebra ℤ Eˣ))
        ∈ Polynomial.lifts ((deningerInsepSubring F E q).subtype) := by
      have := Polynomial.C_mem_lifts ((deningerInsepSubring F E q).subtype)
        (⟨-c, neg_mem hcmem⟩ : ↥(deningerInsepSubring F E q))
      exact this
    have hsub : (Polynomial.X - Polynomial.C c : Polynomial (MonoidAlgebra ℤ Eˣ))
        = Polynomial.X + Polynomial.C (-c) := by
      rw [map_neg]
      ring
    rw [hsub]
    exact add_mem hX hC
  rw [Polynomial.lifts_iff_coeff_lifts] at hlift
  obtain ⟨y, hy⟩ := hlift n
  rw [← hy]
  exact y.2

omit [IsAlgClosure F E] [IsAlgClosed E] in
/-- The orbit polynomial of an element of `ℤ̲κ / κ₀` has invariant coefficients. -/
theorem deningerOrbitPolynomial_coeff_invariant (ξ : MonoidAlgebra ℤ Eˣ) (n : ℕ)
    (σ : E ≃ₐ[F] E) :
    σ • (deningerOrbitPolynomial (fun b : MonoidAlgebra ℤ Eˣ =>
        deningerMonoidAlgebraOrbit_finite (F := F) b) ξ).coeff n
      = (deningerOrbitPolynomial (fun b : MonoidAlgebra ℤ Eˣ =>
        deningerMonoidAlgebraOrbit_finite (F := F) b) ξ).coeff n := by
  set hfin : ∀ b : MonoidAlgebra ℤ Eˣ, (MulAction.orbit (E ≃ₐ[F] E) b).Finite :=
    fun b => deningerMonoidAlgebraOrbit_finite (F := F) b with hfindef
  have h := deningerOrbitPolynomial_smul hfin ξ σ
  have h2 := congrArg (fun p : Polynomial (MonoidAlgebra ℤ Eˣ) => p.coeff n) h
  simpa [Polynomial.coeff_map] using h2

end

end RHTower

namespace RHTower

noncomputable section

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [IsAlgClosure F E] [IsAlgClosed E] [Algebra.IsAlgebraic F E]
variable [DecidableEq Eˣ] [DecidableEq (Polynomial (perfectClosure F E))]

/-- The comparison `W_rat (κ₀) → ℤ̲κ / κ₀`. -/
def deningerWittToInsep :
    DeningerCanonicalRationalWittRing F →+* ↥(deningerInsepSubring F E q) :=
  RingHom.codRestrict (deningerWittToMonoidAlgebra (F := F) (E := E))
    (deningerInsepSubring F E q) (fun w => (deningerWittToMonoidAlgebra_mem q w).2)

theorem deningerWittToInsep_val (w : DeningerCanonicalRationalWittRing F) :
    ((deningerWittToInsep (F := F) (E := E) q w : ↥(deningerInsepSubring F E q)) :
        MonoidAlgebra ℤ Eˣ)
      = deningerWittToMonoidAlgebra (F := F) (E := E) w := rfl

theorem deningerWittToInsep_injective :
    Function.Injective (deningerWittToInsep (F := F) (E := E) q) := by
  intro x y hxy
  refine deningerWittToMonoidAlgebra_injective (F := F) (E := E) ?_
  rw [← deningerWittToInsep_val q x, ← deningerWittToInsep_val q y, hxy]

/-- **Deninger, Corollary 1.5(1) (`t28n`).**  Every element of `ℤ̲κ / κ₀` is integral over
`W_rat (κ₀)`: its orbit polynomial has invariant coefficients lying in `ℤ̲κ / κ₀`, hence coming
from `W_rat (κ₀)` by Proposition 1.3. -/
theorem deningerInsep_isIntegral_over_witt (x : ↥(deningerInsepSubring F E q)) :
    ∃ p : Polynomial (DeningerCanonicalRationalWittRing F), p.Monic ∧
      Polynomial.eval₂ (deningerWittToMonoidAlgebra (F := F) (E := E))
        ((x : MonoidAlgebra ℤ Eˣ)) p = 0 := by
  classical
  set hfin : ∀ b : MonoidAlgebra ℤ Eˣ, (MulAction.orbit (E ≃ₐ[F] E) b).Finite :=
    fun b => deningerMonoidAlgebraOrbit_finite (F := F) b with hfindef
  have hlift : deningerOrbitPolynomial hfin (x : MonoidAlgebra ℤ Eˣ)
      ∈ Polynomial.lifts (deningerWittToMonoidAlgebra (F := F) (E := E)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact deningerWittToMonoidAlgebra_exists q
      (fun σ => deningerOrbitPolynomial_coeff_invariant (F := F) (x : MonoidAlgebra ℤ Eˣ) n σ)
      (deningerOrbitPolynomial_coeff_mem q x.2 n)
  obtain ⟨p, hp, -, hpmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift
    (deningerOrbitPolynomial_monic hfin (x : MonoidAlgebra ℤ Eˣ))
  refine ⟨p, hpmonic, ?_⟩
  have heval : Polynomial.eval₂ (deningerWittToMonoidAlgebra (F := F) (E := E))
      ((x : MonoidAlgebra ℤ Eˣ)) p
      = (deningerOrbitPolynomial hfin (x : MonoidAlgebra ℤ Eˣ)).eval
        ((x : MonoidAlgebra ℤ Eˣ)) := by
    rw [← hp, Polynomial.eval_map]
  rw [heval]
  exact deningerOrbitPolynomial_eval hfin (x : MonoidAlgebra ℤ Eˣ)

include q in
/-- **Deninger, Corollary 1.5(1) (`t28n`).**  Every homomorphism of `W_rat (κ₀)` into an
algebraically closed field is induced by a character of `κˣ`. -/
theorem deningerCor15_surjective {C : Type*} [Field C] [IsAlgClosed C]
    (φ : DeningerCanonicalRationalWittRing F →+* C) :
    ∃ f : Eˣ →* Cˣ,
      ((deningerMonoidAlgebraRingHomEquiv Eˣ C).symm f).comp
        (deningerWittToMonoidAlgebra (F := F) (E := E)) = φ := by
  classical
  letI : Algebra (DeningerCanonicalRationalWittRing F) ↥(deningerInsepSubring F E q) :=
    (deningerWittToInsep (F := F) (E := E) q).toAlgebra
  have hval : ∀ (x : ↥(deningerInsepSubring F E q))
      (p : Polynomial (DeningerCanonicalRationalWittRing F)),
      ((Polynomial.eval₂
        (algebraMap (DeningerCanonicalRationalWittRing F) ↥(deningerInsepSubring F E q)) x p :
        ↥(deningerInsepSubring F E q)) : MonoidAlgebra ℤ Eˣ)
        = Polynomial.eval₂ (deningerWittToMonoidAlgebra (F := F) (E := E))
          ((x : MonoidAlgebra ℤ Eˣ)) p := by
    intro x p
    induction p using Polynomial.induction_on with
    | C a => rw [Polynomial.eval₂_C, Polynomial.eval₂_C]; rfl
    | add p₁ p₂ h₁ h₂ =>
        rw [Polynomial.eval₂_add, Polynomial.eval₂_add, ← h₁, ← h₂]
        rfl
    | monomial n a _ =>
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C,
          Polynomial.eval₂_pow, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_X]
        rfl
  haveI : Algebra.IsIntegral (DeningerCanonicalRationalWittRing F)
      ↥(deningerInsepSubring F E q) := by
    constructor
    intro x
    obtain ⟨p, hpmonic, hpeval⟩ := deningerInsep_isIntegral_over_witt q x
    refine ⟨p, hpmonic, ?_⟩
    apply Subtype.ext
    rw [hval x p, hpeval]
    rfl
  haveI : FaithfulSMul (DeningerCanonicalRationalWittRing F)
      ↥(deningerInsepSubring F E q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (deningerWittToInsep_injective q)
  obtain ⟨ψ, hψ⟩ := deningerHom_exists_extension_of_isIntegral
    (A := DeningerCanonicalRationalWittRing F) (B := ↥(deningerInsepSubring F E q)) (C := C) φ
  obtain ⟨χ, hχ⟩ := deningerInsepSubring_restrict_surjective (F := F) (E := E) (q := q) (C := C) ψ
  refine ⟨deningerMonoidAlgebraRingHomEquiv Eˣ C χ, ?_⟩
  rw [(deningerMonoidAlgebraRingHomEquiv Eˣ C).symm_apply_apply]
  refine RingHom.ext fun w₀ => ?_
  show χ (deningerWittToMonoidAlgebra (F := F) (E := E) w₀) = φ w₀
  have h1 : χ (deningerWittToMonoidAlgebra (F := F) (E := E) w₀)
      = ψ (deningerWittToInsep (F := F) (E := E) q w₀) := by
    have h := congrArg (fun g : ↥(deningerInsepSubring F E q) →+* C =>
      g (deningerWittToInsep (F := F) (E := E) q w₀)) hχ
    exact h
  rw [h1]
  exact hψ w₀

end

end RHTower
