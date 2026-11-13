import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductIsAProductOfAbelianEulerProducts
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors

/-!
# The Artin Euler product of a linear character

Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear character of
`G`. The **Artin symbol** of `χ` at a prime `v` of `K` is `χ(Frob_v)` if `χ` is trivial on the
inertia group at `v`, and `0` otherwise (`artinSymbol`, `artinSymbol_eq_frobeniusValue`).

* The local Euler polynomial of `χ` at `v` is `1 − (χ, v) X`
  (`numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine`): the mean of `χ` over the
  coset `φ^m I` is `χ(φ)^m` if `χ` is trivial on `I` and `0` otherwise.
* **Artin and Hecke** (`artinEulerProduct_linearCharacter_eq_heckeL`): if the Artin symbol of
  `χ` is the value of a ray class character `ψ` at every prime, then
  `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`. The reciprocity law is the statement that such a
  `ψ` exists.
* The trivial character gives the Dedekind zeta function of `K`
  (`artinEulerProduct_one_eq_dedekindZeta`). Hence the Dedekind zeta function of an
  intermediate field `M` is the Artin Euler product over `K` of the permutation character of
  `G` on the cosets of `Gal(L/M)` (`artinEulerProduct_induced_one_eq_dedekindZeta`).
-/

open scoped Classical BigOperators NumberField
open Polynomial IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### Frobenius traces of a linear character -/

section Group

variable {Γ : Type u} [Group Γ] [Fintype Γ]

/-- The Frobenius value of a linear character for an inertia group `I` and a Frobenius element
`φ`: `χ(φ)` if `χ` is trivial on `I`, and `0` otherwise. -/
def frobeniusValue (χ : LinearCharacter Γ) (I : Subgroup Γ) (φ : Γ) : ℂ :=
  if ∀ τ ∈ I, χ τ = 1 then (χ φ : ℂ) else 0

theorem cosetSum_linearCharacter (χ : LinearCharacter Γ) (I : Subgroup Γ) (g : Γ) :
    cosetSum (fun x => (χ x : ℂ)) I g = (χ g : ℂ) * ∑ τ : I, (χ τ : ℂ) := by
  unfold cosetSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show (χ (g * τ) : ℂ) = (χ g : ℂ) * (χ τ : ℂ)
  rw [map_mul, Units.val_mul]

/-- The sum of a linear character over a subgroup: its order if the character is trivial on the
subgroup, and `0` otherwise. -/
theorem sum_linearCharacter_subgroup (χ : LinearCharacter Γ) (I : Subgroup Γ) :
    ∑ τ : I, (χ τ : ℂ) = if ∀ τ ∈ I, χ τ = 1 then (Nat.card I : ℂ) else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl fun τ _ => by rw [h τ τ.2, Units.val_one], Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  · refine sum_hom_units_eq_zero ((Units.coeHom ℂ).comp (χ.comp I.subtype)) fun h1 =>
      h fun τ hτ => ?_
    have h2 := DFunLike.congr_fun h1 (⟨τ, hτ⟩ : I)
    exact Units.ext h2

/-- **The Frobenius traces of a linear character are the powers of its Frobenius value.** -/
theorem frobeniusTrace_linearCharacter (χ : LinearCharacter Γ) (I : Subgroup Γ) (φ : Γ)
    {m : ℕ} (hm : 1 ≤ m) :
    frobeniusTrace (fun x => (χ x : ℂ)) I φ m = frobeniusValue χ I φ ^ m := by
  unfold frobeniusTrace frobeniusValue
  rw [cosetSum_linearCharacter, sum_linearCharacter_subgroup]
  split_ifs with h
  · have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [map_pow, Units.val_pow_eq_pow_val, mul_comm ((χ φ : ℂ) ^ m), ← mul_assoc,
      inv_mul_cancel₀ hI, one_mul]
  · rw [mul_zero, mul_zero, zero_pow (by omega)]

/-- A polynomial with constant term `1` and the Frobenius traces of a linear character is
`1 − χ(φ) X` or `1`. -/
theorem eulerPolynomial_linearCharacter {P : ℂ[X]} (χ : LinearCharacter Γ) (I : Subgroup Γ)
    (φ : Γ) (hP : HasPowerTraces P (frobeniusTrace (fun x => (χ x : ℂ)) I φ))
    (hP0 : P.coeff 0 = 1) : P = 1 - C (frobeniusValue χ I φ) * X := by
  refine (hP.congr fun m hm => frobeniusTrace_linearCharacter χ I φ hm).eq_of_coeff_zero
    (hasPowerTraces_one_sub_C_mul_X _) ?_
  rw [hP0, coeff_sub, coeff_one_zero, coeff_C_mul, coeff_X_zero, mul_zero, sub_zero]

end Group

/-! ### The Artin symbol -/

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Artin symbol** of a linear character `χ` of the Galois group at a prime `v` of the
base field: `χ(Frob_v)` if `χ` is unramified at `v`, and `0` otherwise. It is defined as the
linear coefficient of the local Euler polynomial, with the opposite sign. -/
def artinSymbol (χ : LinearCharacter G) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  -(numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v
    (linearCharacterLine χ)).coeff 1

/-- The local Euler polynomial of a linear character, for a prime `Q` of `L` above `v`. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine_of_liesOver
    (χ : LinearCharacter G) (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q.LiesOver v.asIdeal] :
    numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v (linearCharacterLine χ) =
      1 - C (frobeniusValue χ (Q.inertia G) (arithFrobAt (𝓞 K) G Q)) * X := by
  haveI := (inferInstance : Q.IsMaximal).isPrime
  rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
    (K := K) (L := L) (G := G) v Q (linearCharacterLine χ)]
  refine eulerPolynomial_linearCharacter χ _ _ ?_ (localEulerPolynomial_coeff_zero _ _ _)
  have h := hasPowerTraces_frobeniusInertiaEulerPolynomial (A := 𝓞 K) Q (linearCharacterLine χ)
  rwa [linearCharacterLine_character] at h

/-- **The Artin symbol is the value of the character at a Frobenius element**, for every prime
`Q` of `L` above `v`: `χ(Frob_Q)` if `χ` is trivial on the inertia group of `Q`, else `0`. -/
theorem artinSymbol_eq_frobeniusValue (χ : LinearCharacter G) (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q.LiesOver v.asIdeal] :
    artinSymbol K L χ v = frobeniusValue χ (Q.inertia G) (arithFrobAt (𝓞 K) G Q) := by
  rw [artinSymbol,
    numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine_of_liesOver K L χ v Q,
    coeff_sub, coeff_C_mul, coeff_X_one, mul_one, Polynomial.coeff_one, if_neg one_ne_zero,
    zero_sub, neg_neg]

/-- **The local Euler polynomial of a linear character is `1 − (χ, v) X`.** -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine (χ : LinearCharacter G)
    (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v (linearCharacterLine χ) =
      1 - C (artinSymbol K L χ v) * X := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  rw [artinSymbol_eq_frobeniusValue K L χ v Q]
  exact numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine_of_liesOver K L χ v Q

/-- The Euler factor of a linear character: `(1 − (χ, v) N(v)^{-s})^{-1}`. -/
theorem numberFieldFinitePlaceArtinEulerReciprocal_linearCharacterLine (χ : LinearCharacter G)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (linearCharacterLine χ) v s =
      (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ := by
  unfold numberFieldFinitePlaceArtinEulerReciprocal
  rw [numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine, eval_sub, eval_one,
    eval_mul, eval_C, eval_X]

/-- The trivial character has Artin symbol `1` at every prime. -/
theorem artinSymbol_one (v : HeightOneSpectrum (𝓞 K)) :
    artinSymbol K L (1 : LinearCharacter G) v = 1 := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have h1 : ∀ τ ∈ Q.inertia G, (1 : LinearCharacter G) τ = 1 := fun _ _ => rfl
  rw [artinSymbol_eq_frobeniusValue K L 1 v Q, frobeniusValue, if_pos h1]
  rfl

/-! ### Artin and Hecke -/

/-- **An Artin Euler product with ray class values is a Hecke `L`-series.** If the Artin symbol
of the linear character `χ` is the value of the ray class character `ψ` at every prime of `K`,
then `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`. -/
theorem artinEulerProduct_linearCharacter_eq_heckeL (χ : LinearCharacter G)
    (𝔪 : HeckeLFunctions.Modulus K) (ψ : HeckeLFunctions.HeckeCharacter 𝔪)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      artinSymbol K L χ v = HeckeLFunctions.heckeValue 𝔪 ψ v.asIdeal)
    {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
      (linearCharacterLine χ) s = HeckeLFunctions.heckeL 𝔪 ψ s := by
  have hA : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (linearCharacterLine χ) v s)
      (numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
        (linearCharacterLine χ) s) :=
    (hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
      (K := K) (L := L) (linearCharacterLine χ)).hasProd
      (show s ∈ artinEulerAbsoluteHalfPlane from hs)
  have hfun : (fun v : HeightOneSpectrum (𝓞 K) =>
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (linearCharacterLine χ) v s) =
      fun v => (1 - HeckeLFunctions.heckePrimeTerm 𝔪 ψ s v)⁻¹ := by
    funext v
    rw [numberFieldFinitePlaceArtinEulerReciprocal_linearCharacterLine, h v]
    rfl
  rw [hfun] at hA
  exact hA.unique (HeckeLFunctions.heckeL_eulerProduct_hasProd 𝔪 ψ hs)

/-- **The Artin Euler product of the trivial character is the Dedekind zeta function** of the
base field, for `Re s > 1`. -/
theorem artinEulerProduct_one_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
      (linearCharacterLine (1 : LinearCharacter G)) s = NumberField.dedekindZeta K s := by
  have h : ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L (1 : LinearCharacter G) v =
      HeckeLFunctions.heckeValue (HeckeLFunctions.trivialModulus K) 1 v.asIdeal := fun v => by
    rw [artinSymbol_one, HeckeLFunctions.heckeValue_trivialModulus_one v.ne_bot]
  rw [artinEulerProduct_linearCharacter_eq_heckeL K L 1 (HeckeLFunctions.trivialModulus K) 1 h hs,
    HeckeLFunctions.heckeL_trivialModulus_one]

/-- **The Dedekind zeta function of an intermediate field is an Artin Euler product over the
base field**: for `K ⊂ M ⊂ L` with `H = Gal(L/M)` and a representation `ρ` of `G` whose
character is the permutation character `Ind_H^G 1`, `L(s, ρ, L/K) = ζ_M(s)` for `Re s > 1`. -/
theorem artinEulerProduct_induced_one_eq_dedekindZeta {M V : Type u} [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L] (H : Subgroup G) [IsGaloisGroup H M L]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.character = inducedFunction H fun _ => 1) {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
      NumberField.dedekindZeta M s := by
  have hσ : ρ.character =
      inducedFunction H (linearCharacterLine (1 : LinearCharacter H)).character := by
    rw [hρ, linearCharacterLine_character]
    rfl
  rw [numberFieldFinitePlaceArtinEulerReciprocalProduct_induced (M := M) H ρ
    (linearCharacterLine (1 : LinearCharacter H)) hσ hs]
  exact artinEulerProduct_one_eq_dedekindZeta M L hs

end GaloisForLFunctions
