import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArtinLFunctionOfALinearCharacterIsTheLFunctionOfItsPrimitiveRayClassCharacter
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrdersOfAnArtinLFunctionAreTheNetMultiplicitiesOfItsVirtualConfiguration
import GaloisForLFunctions.RHTower.Artin.TheArtinEulerProductOfTheConjugateRepresentationRunsOverTheInverseCharacters

/-!
# Every Artin `L`-function has a completion with a functional equation

Let `L/K` be a Galois extension of number fields with group `G`. `Ξ(s, ψ)` is the entire
completion of a primitive ray class character `ψ`: `Ξ = P γ L(·, ψ)` on `Re s > 1`, with `P`
the polynomial clearing the poles and `γ` the conductor and Gamma factor, and
`Ξ(1 − s, ψ) = W(ψ) Ξ(s, ψ⁻¹)`.

* **Linear characters** (`exists_completion_linearCharacter`). A linear character `χ` of `G`
  has a primitive ray class character `ψ` with `(χ, v) = ψ(v)` at every prime, and `ψ⁻¹` is the
  one of `χ⁻¹`. So `Ξ(·, ψ) = P γ L(·, χ, L/K)` and `Ξ(·, ψ⁻¹) = P γ' L(·, χ⁻¹, L/K)` on
  `Re s > 1`, with the functional equation between them, and the von Mangoldt coefficients of
  `ψ` are `Σ_{N v^k = n} (χ, v)^k log N v` (`artinMangoldt`): the explicit formula of the zeros
  has the Artin symbols of `χ` on its prime side, at every prime.
* **Representations** (`exists_artinEulerProduct_eq_prod_zpow_primitive_heckeL`,
  `exists_completion_artin`). Let `ρ` be a representation of `G` and `ρ*` one with the
  conjugate character. There are integers `n_q` on the Brauer pairs `q = (E_q, χ_q)` and
  primitive ray class characters `ψ_q` of the fixed fields of the `E_q` with

  `L(s, ρ, L/K) = Π_q L(s, ψ_q)^{n_q}`,  `L(s, ρ*, L/K) = Π_q L(s, ψ_q⁻¹)^{n_q}`  (`Re s > 1`),

  with no correcting Euler factor. The completions `Ξ_ρ = Π_q Ξ(·, ψ_q)^{n_q}` and
  `Ξ_{ρ*} = Π_q Ξ(·, ψ_q⁻¹)^{n_q}` are quotients of entire functions, `Ξ_ρ = γ_ρ L(·, ρ)` on
  `Re s > 1`, and `Ξ_ρ(1 − s) = W Ξ_{ρ*}(s)` on `ℂ` with `|W| = 1`. If `A`, `B` are entire,
  `B ≢ 0` and `A = B Ξ_ρ` on `Re s > 1`, then at every point of `ℂ` the order of `A / B` is the
  net multiplicity of the virtual configuration `Σ_q n_q Z_{ψ_q}`, and the form
  `Σ_q n_q W_{Z_q}` has `m` negative squares on some family of `m` tests iff at least `m`
  points are zeros or poles of `A / B` right of the critical line, or poles on the line.

The entire functions `Ξ(·, ψ_q)` have no zeros on `Re s > 1` and their zeros with orders are
the configurations `Z_{ψ_q}`; an identity between entire functions on `Re s > 1` holds on `ℂ`.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical ComplexConjugate

universe u

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry IsDedekindDomain Zeta23 ArithmeticCastelnuovoSeveri ArtinMertens

/-! ### Products of integer powers of entire functions -/

/-- **Orders of a product of integer powers of entire functions.** Let `Ξ_q` be entire without
zeros on `Re s > 1`, with the orders of the configurations `Z_q`, and `A`, `B` entire, `B ≢ 0`,
with `A = B Π_q Ξ_q^{n_q}` on `Re s > 1`. Then `ord_z A − ord_z B` is the net multiplicity of
`Σ_q n_q Z_q` at every `z ∈ ℂ`. -/
theorem analyticOrderNatAt_sub_of_entire_configurations {ι : Type*} (n : ι →₀ ℤ)
    (Z : ι → ZeroConfig) (Ξ : ι → ℂ → ℂ) (hΞ : ∀ q, Differentiable ℂ (Ξ q))
    (hΞ0 : ∀ q, ∀ s : ℂ, 1 < s.re → Ξ q s ≠ 0)
    (hord : ∀ q, ∀ z : ℂ, analyticOrderNatAt (Ξ q) z = extMult (Z q) z) {A B : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hB0 : ∃ u : ℂ, B u ≠ 0)
    (hAB : ∀ s : ℂ, 1 < s.re → A s = B s * n.prod fun q k => Ξ q s ^ k) (z : ℂ) :
    (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z = netMult n Z z := by
  obtain ⟨u, hu⟩ := hB0
  have hBu : analyticOrderAt B u ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hu)]
    exact ENat.coe_ne_top 0
  have h := (analyticOrderNatAt_sub_eq_sum_of_eq_mul_prod_zpow isOpen_univ isPreconnected_univ
    (isOpen_lt continuous_const Complex.continuous_re) (subset_univ {s : ℂ | 1 < s.re})
    ⟨2, show (1 : ℝ) < (2 : ℂ).re by norm_num⟩ hA.differentiableOn hB.differentiableOn
    ⟨u, mem_univ u, hBu⟩ Ξ (fun q => (hΞ q).differentiableOn) hΞ0 n hAB (mem_univ z)).2.2
  rw [h, netMult]
  exact Finsupp.sum_congr fun q _ => by rw [hord q z]

/-- The defect points of a combination of configurations, through the orders of a quotient
`A / B` with these net multiplicities at every point. -/
theorem combinationDefect_eq_of_forall_orders {ι : Type*} (n : ι →₀ ℤ) (Z : ι → ZeroConfig)
    {A B : ℂ → ℂ}
    (hord : ∀ z : ℂ, (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z = netMult n Z z) :
    combinationDefect n Z =
      {w : ℂ | 1 / 2 < w.re ∧ analyticOrderNatAt A w ≠ analyticOrderNatAt B w} ∪
        {w : ℂ | w.re = 1 / 2 ∧ analyticOrderNatAt A w < analyticOrderNatAt B w} := by
  ext w
  simp only [combinationDefect, Set.mem_union, Set.mem_setOf_eq]
  rw [← hord w]
  refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
  · exact not_congr (sub_eq_zero.trans Nat.cast_inj)
  · exact sub_neg.trans Nat.cast_lt

/-- A product of integer powers of entire functions without zeros on `Re s > 1` is there a
quotient of entire functions. -/
theorem exists_entire_quotient_of_prod_zpow {ι : Type*} (n : ι →₀ ℤ) (Ξ : ι → ℂ → ℂ)
    (hΞ : ∀ q, Differentiable ℂ (Ξ q)) (hΞ0 : ∀ q, ∀ s : ℂ, 1 < s.re → Ξ q s ≠ 0) :
    ∃ A B : ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧ (∀ s : ℂ, 1 < s.re → B s ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → A s = B s * n.prod fun q k => Ξ q s ^ k := by
  have hpow : ∀ e : ι → ℕ, Differentiable ℂ fun s : ℂ => ∏ q ∈ n.support, Ξ q s ^ e q :=
    fun e => differentiableOn_univ.mp
      (DifferentiableOn.fun_finsetProd fun q _ => (hΞ q).differentiableOn.pow (e q))
  refine ⟨fun s => ∏ q ∈ n.support, Ξ q s ^ (n q).toNat,
    fun s => ∏ q ∈ n.support, Ξ q s ^ (-(n q)).toNat, hpow _, hpow _,
    fun s hs => Finset.prod_ne_zero_iff.mpr fun q _ => pow_ne_zero _ (hΞ0 q s hs),
    fun s hs => ?_⟩
  rw [Finsupp.prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [← zpow_natCast (Ξ q s) (n q).toNat, ← zpow_natCast (Ξ q s) (-(n q)).toNat,
    ← zpow_add₀ (hΞ0 q s hs)]
  congr 1
  omega

/-! ### Linear characters -/

variable (K L : Type u) {G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The von Mangoldt coefficients of a linear character: `Σ_{N v^k = n} (χ, v)^k log N v`, over
the powers of the primes `v` of `K`. -/
def artinMangoldt (χ : LinearCharacter G) (n : ℕ) : ℂ :=
  ∑ pk ∈ (primePowersLe K n).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = n),
    (if h : pk.1.IsPrime ∧ pk.1 ≠ ⊥ then artinSymbol K L χ ⟨pk.1, h.1, h.2⟩ else 0) ^ pk.2 *
      (Real.log (Ideal.absNorm pk.1) : ℂ)

/-- A ray class character with the Artin symbols of `χ` at every prime has the von Mangoldt
coefficients of `χ`. -/
theorem heckeMangoldt_eq_artinMangoldt (χ : LinearCharacter G) {𝔫 : Modulus K}
    {ψ : HeckeCharacter 𝔫}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔫 ψ v.asIdeal)
    (n : ℕ) : heckeMangoldt 𝔫 ψ n = artinMangoldt K L χ n := by
  unfold heckeMangoldt artinMangoldt
  refine Finset.sum_congr rfl fun pk hpk => ?_
  obtain ⟨P, k⟩ := pk
  obtain ⟨hP, hP0, -, -⟩ := mem_primePowersLe.mp (Finset.mem_filter.mp hpk).1
  dsimp only
  rw [dif_pos ⟨hP, hP0⟩, h ⟨P, hP, hP0⟩]

/-- **The completion of the Artin `L`-function of a linear character.** For a linear character
`χ` of the group of a Galois extension `L/K` of number fields there is a primitive ray class
character `ψ`, with conductor divisible exactly by the primes at which `χ` is ramified, such
that the entire completions of `ψ` and `ψ⁻¹` are those of the Euler products of `χ` and `χ⁻¹`
on `Re s > 1`, `Ξ(1 − s, ψ) = W Ξ(s, ψ⁻¹)`, and the von Mangoldt coefficients of `ψ` are those
of `χ`. For `χ ≠ 1` the character `ψ` is not trivial. -/
theorem exists_completion_linearCharacter (χ : LinearCharacter G) :
    ∃ (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫), heckeFiniteConductor 𝔫 ψ = 𝔫.fin ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔫.fin ↔ artinSymbol K L χ v = 0) ∧
      (χ ≠ 1 → ψ ≠ 1) ∧
      (∀ s : ℂ, 1 < s.re → heckeXi 𝔫 ψ s = heckePoleFactor 𝔫 ψ s *
        (heckeCompletionFactor 𝔫 s * heckeGammaFactor 𝔫 ψ s *
          numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
            (linearCharacterLine χ) s)) ∧
      (∀ s : ℂ, 1 < s.re → heckeXi 𝔫 ψ⁻¹ s = heckePoleFactor 𝔫 ψ⁻¹ s *
        (heckeCompletionFactor 𝔫 s * heckeGammaFactor 𝔫 ψ⁻¹ s *
          numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
            (linearCharacterLine χ⁻¹) s)) ∧
      (∀ s : ℂ, heckeXi 𝔫 ψ (1 - s) = heckeRootNumber 𝔫 ψ * heckeXi 𝔫 ψ⁻¹ s) ∧
      ∀ n : ℕ, heckeMangoldt 𝔫 ψ n = artinMangoldt K L χ n := by
  obtain ⟨𝔫, ψ, hprim, hdvd, hval, hL⟩ :=
    exists_primitive_heckeCharacter_forall_artinSymbol K L χ
  -- `ψ⁻¹` has the Artin symbols of `χ⁻¹`
  have hval' : ∀ v : HeightOneSpectrum (𝓞 K),
      artinSymbol K L χ⁻¹ v = heckeValue 𝔫 ψ⁻¹ v.asIdeal := fun v => by
    rw [artinSymbol_inv K L χ v, hval v, heckeValue_inv_eq_conj]
  refine ⟨𝔫, ψ, hprim, hdvd,
    fun hχ => heckeCharacter_ne_one_of_artinSymbol K L hχ 𝔫 ψ fun v _ => hval v,
    fun s hs => ?_, fun s hs => ?_, heckeXi_one_sub 𝔫 ψ hprim,
    heckeMangoldt_eq_artinMangoldt K L χ hval⟩
  · rw [heckeXi_eq 𝔫 ψ hs, hL s hs]
  · rw [heckeXi_eq 𝔫 ψ⁻¹ hs,
      artinEulerProduct_linearCharacter_eq_heckeL K L χ⁻¹ 𝔫 ψ⁻¹ hval' hs]

/-! ### Representations -/

/-- **Every Artin Euler product is a product of integer powers of `L`-series of primitive ray
class characters**, with no correcting Euler factor. There are integers `n_q` on the Brauer
pairs `q = (E, χ)` and primitive ray class characters `ψ_q` of the fixed fields, with
`(χ_q, v) = ψ_q(v)` at every prime, such that for `Re s > 1`
`L(s, ρ, L/K) = Π_q L(s, ψ_q)^{n_q}`, and `L(s, ρ*, L/K) = Π_q L(s, ψ_q⁻¹)^{n_q}` for every
representation `ρ*` with the conjugate character. -/
theorem exists_artinEulerProduct_eq_prod_zpow_primitive_heckeL (ρ : Representation ℂ G V) :
    ∃ (n : brauerElementaryMonomialIndex G →₀ ℤ)
      (𝔫 : ∀ q : brauerElementaryMonomialIndex G,
        Modulus (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L))
      (ψ : ∀ q, HeckeCharacter (𝔫 q)),
      (∀ q, heckeFiniteConductor (𝔫 q) (ψ q) = (𝔫 q).fin) ∧
      (∀ (q : brauerElementaryMonomialIndex G) (v : HeightOneSpectrum
          (𝓞 (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L))),
        artinSymbol (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L
          q.2 v = heckeValue (𝔫 q) (ψ q) v.asIdeal) ∧
      (∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
          n.prod fun q k => heckeL (𝔫 q) (ψ q) s ^ k) ∧
      ∀ {V' : Type u} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
        (ρ' : Representation ℂ G V'), (∀ g : G, ρ'.character g = conj (ρ.character g)) →
        ∀ s : ℂ, 1 < s.re →
          numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ' s =
            n.prod fun q k => heckeL (𝔫 q) (ψ q)⁻¹ s ^ k := by
  obtain ⟨n, hn, hn'⟩ := exists_artinEulerProduct_eq_prod_zpow_abelian_conj K L ρ
  choose 𝔫 ψ hprim hdvd hval hL using fun q : brauerElementaryMonomialIndex G =>
    exists_primitive_heckeCharacter_forall_artinSymbol
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L q.2
  refine ⟨n, 𝔫, ψ, hprim, hval, fun s hs => ?_, ?_⟩
  · rw [hn s hs]
    exact Finsupp.prod_congr fun q _ => congrArg (fun x => x ^ n q) (hL q s hs)
  · intro V' _ _ _ ρ' hρ' s hs
    rw [hn' ρ' hρ' s hs]
    refine Finsupp.prod_congr fun q _ => congrArg (fun x => x ^ n q) ?_
    exact artinEulerProduct_linearCharacter_eq_heckeL
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L q.2⁻¹ (𝔫 q)
      (ψ q)⁻¹ (fun v => by
        rw [artinSymbol_inv _ L q.2 v, hval q v, heckeValue_inv_eq_conj]) hs

/-- **Every Artin `L`-function has a completion with a functional equation.** With integers
`n_q` and primitive ray class characters `ψ_q` of the fixed fields of the Brauer pairs, let
`Ξ_ρ = Π_q Ξ(·, ψ_q)^{n_q}` and `Ξ_{ρ*} = Π_q Ξ(·, ψ_q⁻¹)^{n_q}`. Then

* `Ξ_ρ = γ_ρ L(·, ρ, L/K)` on `Re s > 1`, `γ_ρ = Π_q (P_q γ_q)^{n_q}`, and the same for every
  representation `ρ*` with the conjugate character, with `ψ_q⁻¹`;
* `Ξ_ρ(1 − s) = W Ξ_{ρ*}(s)` on `ℂ`, `W = Π_q W(ψ_q)^{n_q}` of absolute value `1`;
* `Ξ_ρ` is a quotient of entire functions on `Re s > 1`, and whenever `A`, `B` are entire,
  `B ≢ 0`, `A = B Ξ_ρ` on `Re s > 1`: `ord_w A − ord_w B = Σ_q n_q m_{Z_q}(w)` at every
  `w ∈ ℂ`, and `Σ_q n_q W_{Z_q}` has `m` negative squares on some family of `m` tests iff at
  least `m` points are zeros or poles of `A / B` right of the critical line or poles on it. -/
theorem exists_completion_artin (ρ : Representation ℂ G V) :
    ∃ (n : brauerElementaryMonomialIndex G →₀ ℤ)
      (𝔫 : ∀ q : brauerElementaryMonomialIndex G,
        Modulus (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L))
      (ψ : ∀ q, HeckeCharacter (𝔫 q))
      (hprim : ∀ q, heckeFiniteConductor (𝔫 q) (ψ q) = (𝔫 q).fin),
      (∀ s : ℂ, 1 < s.re → (n.prod fun q k => heckeXi (𝔫 q) (ψ q) s ^ k) =
        (n.prod fun q k => (heckePoleFactor (𝔫 q) (ψ q) s *
          (heckeCompletionFactor (𝔫 q) s * heckeGammaFactor (𝔫 q) (ψ q) s)) ^ k) *
          numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s) ∧
      (∀ {V' : Type u} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
        (ρ' : Representation ℂ G V'), (∀ g : G, ρ'.character g = conj (ρ.character g)) →
        ∀ s : ℂ, 1 < s.re → (n.prod fun q k => heckeXi (𝔫 q) (ψ q)⁻¹ s ^ k) =
          (n.prod fun q k => (heckePoleFactor (𝔫 q) (ψ q)⁻¹ s *
            (heckeCompletionFactor (𝔫 q) s * heckeGammaFactor (𝔫 q) (ψ q)⁻¹ s)) ^ k) *
            numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ' s) ∧
      (∀ s : ℂ, (n.prod fun q k => heckeXi (𝔫 q) (ψ q) (1 - s) ^ k) =
        (n.prod fun q k => heckeRootNumber (𝔫 q) (ψ q) ^ k) *
          n.prod fun q k => heckeXi (𝔫 q) (ψ q)⁻¹ s ^ k) ∧
      ‖n.prod fun q k => heckeRootNumber (𝔫 q) (ψ q) ^ k‖ = 1 ∧
      (∃ A B : ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧
        (∀ s : ℂ, 1 < s.re → B s ≠ 0) ∧
        ∀ s : ℂ, 1 < s.re → A s = B s * n.prod fun q k => heckeXi (𝔫 q) (ψ q) s ^ k) ∧
      ∀ A B : ℂ → ℂ, Differentiable ℂ A → Differentiable ℂ B → (∃ u : ℂ, B u ≠ 0) →
        (∀ s : ℂ, 1 < s.re → A s = B s * n.prod fun q k => heckeXi (𝔫 q) (ψ q) s ^ k) →
        (∀ w : ℂ, (analyticOrderNatAt A w : ℤ) - analyticOrderNatAt B w =
          netMult n (fun q => heckeZeros (𝔫 q) (ψ q) (hprim q)) w) ∧
        ∀ m : ℕ, (∃ f : Fin m → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
            (∀ i, HasCompactSupport (f i)) ∧
            m ≤ hermNegIndex (n.sum fun q k =>
              (k : ℂ) • zeroGram (heckeZeros (𝔫 q) (ψ q) (hprim q)) f)) ↔
          (m : ℕ∞) ≤ ({w : ℂ | 1 / 2 < w.re ∧
              analyticOrderNatAt A w ≠ analyticOrderNatAt B w} ∪
            {w : ℂ | w.re = 1 / 2 ∧
              analyticOrderNatAt A w < analyticOrderNatAt B w}).encard := by
  obtain ⟨n, 𝔫, ψ, hprim, -, hE, hE'⟩ :=
    exists_artinEulerProduct_eq_prod_zpow_primitive_heckeL K L ρ
  -- a completion is the pole, conductor and Gamma factors times the `L`-series
  have hfac : ∀ (q : brauerElementaryMonomialIndex G) (φ : HeckeCharacter (𝔫 q)) (k : ℤ)
      {s : ℂ}, 1 < s.re → heckeXi (𝔫 q) φ s ^ k =
        (heckePoleFactor (𝔫 q) φ s *
          (heckeCompletionFactor (𝔫 q) s * heckeGammaFactor (𝔫 q) φ s)) ^ k *
          heckeL (𝔫 q) φ s ^ k := fun q φ k s hs => by
    rw [heckeXi_eq (𝔫 q) φ hs, ← mul_zpow]
    congr 1
    ring
  have hΞ : ∀ q, Differentiable ℂ (heckeXi (𝔫 q) (ψ q)) := fun q =>
    differentiable_heckeXi (𝔫 q) (ψ q)
  have hΞ0 : ∀ q, ∀ s : ℂ, 1 < s.re → heckeXi (𝔫 q) (ψ q) s ≠ 0 := fun q s hs =>
    heckeXi_ne_zero (𝔫 q) (ψ q) hs
  refine ⟨n, 𝔫, ψ, hprim, fun s hs => ?_, ?_, fun s => ?_, ?_,
    exists_entire_quotient_of_prod_zpow n (fun q => heckeXi (𝔫 q) (ψ q)) hΞ hΞ0,
    fun A B hA hB hB0 hAB => ?_⟩
  · rw [hE s hs, ← Finsupp.prod_mul]
    exact Finsupp.prod_congr fun q _ => hfac q (ψ q) (n q) hs
  · intro V' _ _ _ ρ' hρ' s hs
    rw [hE' ρ' hρ' s hs, ← Finsupp.prod_mul]
    exact Finsupp.prod_congr fun q _ => hfac q (ψ q)⁻¹ (n q) hs
  · -- the functional equations of the factors
    rw [← Finsupp.prod_mul]
    exact Finsupp.prod_congr fun q _ => by
      rw [heckeXi_one_sub (𝔫 q) (ψ q) (hprim q), mul_zpow]
  · rw [Finsupp.prod, norm_prod]
    exact Finset.prod_eq_one fun q _ => by
      rw [norm_zpow, norm_heckeRootNumber (𝔫 q) (ψ q) (hprim q), one_zpow]
  · -- orders on the whole plane, then the index of the combination
    have hord := analyticOrderNatAt_sub_of_entire_configurations n
      (fun q => heckeZeros (𝔫 q) (ψ q) (hprim q)) (fun q => heckeXi (𝔫 q) (ψ q)) hΞ hΞ0
      (fun q z => (congrArg ENat.toNat
        (extMult_heckeZeros (𝔫 q) (ψ q) (hprim q) z)).symm.trans (ENat.toNat_coe _))
      hA hB hB0 hAB
    refine ⟨hord, fun m => ?_⟩
    have hidx := exists_le_negIndex_combination_iff n
      (fun q => heckeZeros (𝔫 q) (ψ q) (hprim q))
      (fun q => temperedConfig_heckeZeros (𝔫 q) (ψ q) (hprim q)) m
    rw [combinationDefect_eq_of_forall_orders n
      (fun q => heckeZeros (𝔫 q) (ψ q) (hprim q)) hord] at hidx
    exact hidx

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
