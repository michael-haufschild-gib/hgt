import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInducedRepresentation
import GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldEulerProductAnalytic

/-!
# The Artin Euler product on integer relations between characters

Let `L/K` be a Galois extension of number fields with group `G`, and let `ρ`, `τ_i` be
representations of `G` with `χ_ρ = Σ_i n_i χ_{τ_i}`, `n_i ∈ ℤ`. Then for `Re s > 1`

  `L(s, ρ) = Π_i L(s, τ_i)^{n_i}`

(`numberFieldFinitePlaceArtinEulerReciprocalProduct_eq_prod_zpow`): the Artin Euler product
depends only on the character and is a homomorphism on the virtual characters.

The local statement is an identity of polynomials. A local Euler polynomial has constant term
`1` and the Frobenius traces of its character as power traces; the Frobenius traces are linear
in the character; products add power traces; and a polynomial is determined by its constant
term and its power traces. So, with `n = n⁺ − n⁻`,

  `P_v(ρ) Π_i P_v(τ_i)^{n_i⁻} = Π_i P_v(τ_i)^{n_i⁺}`

(`numberFieldFinitePlaceLocalEulerPolynomial_mul_prod_pow_eq`). The global statement follows,
because finite products and powers of convergent products converge and the Euler products do
not vanish for `Re s > 1`.
-/

open scoped Classical BigOperators NumberField
open Polynomial IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### Linearity of the Frobenius traces -/

/-- The Frobenius traces are linear in the function. -/
theorem frobeniusTrace_sum_zsmul {Γ : Type u} [Group Γ] [Fintype Γ] {ι : Type*} (S : Finset ι)
    (n : ι → ℤ) (θ : ι → Γ → ℂ) (I : Subgroup Γ) (φ : Γ) (m : ℕ) :
    frobeniusTrace (∑ i ∈ S, n i • θ i) I φ m =
      ∑ i ∈ S, (n i : ℂ) * frobeniusTrace (θ i) I φ m := by
  unfold frobeniusTrace cosetSum
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  ring

/-! ### Polynomials with given power traces -/

/-- The power `P^k` has the power traces `k a_m`. -/
theorem HasPowerTraces.pow {P : ℂ[X]} {a : ℕ → ℂ} (hP : HasPowerTraces P a) (k : ℕ) :
    HasPowerTraces (P ^ k) fun m => (k : ℂ) * a m := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact hasPowerTraces_one.congr fun m _ => by simp
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul hP).congr fun m _ => ?_
    push_cast
    ring

/-- **A relation between power traces is a relation between polynomials.** If `P` and the `R_i`
have constant term `1` and the power traces of `P` are the combination `Σ_i n_i b_i` of the
power traces of the `R_i`, then `P Π_i R_i^{n_i⁻} = Π_i R_i^{n_i⁺}`. -/
theorem HasPowerTraces.mul_prod_pow_toNat_eq {ι : Type*} (S : Finset ι) (n : ι → ℤ)
    {P : ℂ[X]} {R : ι → ℂ[X]} {a : ℕ → ℂ} {b : ι → ℕ → ℂ} (hP : HasPowerTraces P a)
    (hR : ∀ i ∈ S, HasPowerTraces (R i) (b i)) (hP0 : P.coeff 0 = 1)
    (hR0 : ∀ i ∈ S, (R i).coeff 0 = 1)
    (h : ∀ m, 1 ≤ m → a m = ∑ i ∈ S, (n i : ℂ) * b i m) :
    P * ∏ i ∈ S, R i ^ (-n i).toNat = ∏ i ∈ S, R i ^ (n i).toNat := by
  have hneg := hasPowerTraces_prod S (fun i => R i ^ (-n i).toNat)
    (fun i m => ((-n i).toNat : ℂ) * b i m) fun i hi => (hR i hi).pow _
  have hpos := hasPowerTraces_prod S (fun i => R i ^ (n i).toNat)
    (fun i m => ((n i).toNat : ℂ) * b i m) fun i hi => (hR i hi).pow _
  have hprod : ∀ k : ι → ℕ, (∏ i ∈ S, R i ^ k i).coeff 0 = 1 := by
    intro k
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    refine Finset.prod_eq_one fun i hi => ?_
    rw [Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero, hR0 i hi, one_pow]
  refine ((hP.mul hneg).congr fun m hm => ?_).eq_of_coeff_zero hpos ?_
  · show a m + ∑ i ∈ S, ((-n i).toNat : ℂ) * b i m = ∑ i ∈ S, ((n i).toNat : ℂ) * b i m
    rw [h m hm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (n i : ℂ) = ((n i).toNat : ℂ) - ((-n i).toNat : ℂ) := by
      exact_mod_cast (Int.toNat_sub_toNat_neg (n i)).symm
    rw [hi]
    ring
  · rw [Polynomial.mul_coeff_zero, hP0, one_mul, hprod, hprod]

/-! ### Number fields -/

variable {K L G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} (S : Finset ι) (n : ι → ℤ) {W : ι → Type u} [∀ i, AddCommGroup (W i)]
  [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]

/-- **The local Euler polynomial on an integer relation between characters**: if
`χ_ρ = Σ_i n_i χ_{τ_i}`, then `P_v(ρ) Π_i P_v(τ_i)^{n_i⁻} = Π_i P_v(τ_i)^{n_i⁺}`. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_mul_prod_pow_eq (ρ : Representation ℂ G V)
    (τ : ∀ i, Representation ℂ G (W i))
    (hρ : ρ.character = ∑ i ∈ S, n i • (τ i).character) (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ *
        ∏ i ∈ S, numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v (τ i) ^
          (-n i).toNat =
      ∏ i ∈ S, numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v (τ i) ^
        (n i).toNat := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  haveI := hQmax.isPrime
  -- every local polynomial at `v` has constant term `1` and the Frobenius traces at `Q`
  have hT : ∀ {U : Type u} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
      (π : Representation ℂ G U),
      HasPowerTraces (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v π)
        (frobeniusTrace π.character (Q.inertia G) (arithFrobAt (𝓞 K) G Q)) ∧
      (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v π).coeff 0 = 1 := by
    intro U _ _ _ π
    rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
      (K := K) (L := L) (G := G) v Q π]
    exact ⟨hasPowerTraces_frobeniusInertiaEulerPolynomial (A := 𝓞 K) Q π,
      localEulerPolynomial_coeff_zero _ _ _⟩
  refine HasPowerTraces.mul_prod_pow_toNat_eq S n (hT ρ).1 (fun i _ => (hT (τ i)).1) (hT ρ).2
    (fun i _ => (hT (τ i)).2) fun m _ => ?_
  rw [hρ]
  exact frobeniusTrace_sum_zsmul S n (fun i => (τ i).character) _ _ m

/-- The same relation for the Euler factors. -/
theorem numberFieldFinitePlaceArtinEulerReciprocal_mul_prod_pow_eq (ρ : Representation ℂ G V)
    (τ : ∀ i, Representation ℂ G (W i))
    (hρ : ρ.character = ∑ i ∈ S, n i • (τ i).character) (v : HeightOneSpectrum (𝓞 K))
    (s : ℂ) :
    numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s *
        ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (τ i) v s ^
          (-n i).toNat =
      ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (τ i) v s ^
        (n i).toNat := by
  have h := congrArg (fun P : ℂ[X] => (P.eval ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹)
    (numberFieldFinitePlaceLocalEulerPolynomial_mul_prod_pow_eq (K := K) (L := L) S n ρ τ hρ v)
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_pow, mul_inv,
    ← Finset.prod_inv_distrib, ← inv_pow] at h
  exact h

/-- **The Artin Euler product is a homomorphism on integer relations between characters**: if
`χ_ρ = Σ_i n_i χ_{τ_i}` with `n_i ∈ ℤ`, then `L(s, ρ) = Π_i L(s, τ_i)^{n_i}` for `Re s > 1`. -/
theorem numberFieldFinitePlaceArtinEulerReciprocalProduct_eq_prod_zpow
    (ρ : Representation ℂ G V) (τ : ∀ i, Representation ℂ G (W i))
    (hρ : ρ.character = ∑ i ∈ S, n i • (τ i).character) {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
      ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) (τ i) s ^
        n i := by
  have hmem : s ∈ artinEulerAbsoluteHalfPlane := hs
  have hρ' := (hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
    (K := K) (L := L) ρ).hasProd hmem
  have hτ := fun i => (hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
    (K := K) (L := L) (τ i)).hasProd hmem
  -- products and powers of convergent products
  have hneg : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s *
        ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (τ i) v s ^
          (-n i).toNat)
      (numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s *
        ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) (τ i) s ^
          (-n i).toNat) :=
    hρ'.mul (hasProd_prod fun i _ => (hτ i).pow (-n i).toNat)
  have hpos : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (τ i) v s ^
        (n i).toNat)
      (∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) (τ i) s ^
        (n i).toNat) :=
    hasProd_prod fun i _ => (hτ i).pow (n i).toNat
  have hfun : (fun v : HeightOneSpectrum (𝓞 K) =>
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s *
        ∏ i ∈ S, numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (τ i) v s ^
          (-n i).toNat) =
      fun v => ∏ i ∈ S,
        numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (τ i) v s ^ (n i).toNat :=
    funext fun v => numberFieldFinitePlaceArtinEulerReciprocal_mul_prod_pow_eq S n ρ τ hρ v s
  rw [hfun] at hneg
  have key := hneg.unique hpos
  -- the Euler products do not vanish
  have hne : ∀ i, numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) (τ i) s ≠
      0 := fun i =>
    numberFieldFinitePlaceArtinEulerReciprocalProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
      (τ i) hmem
  have hne' : ∏ i ∈ S,
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) (τ i) s ^
        (-n i).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i)
  rw [eq_div_of_mul_eq hne' key, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hne i), Int.toNat_sub_toNat_neg]

end GaloisForLFunctions
