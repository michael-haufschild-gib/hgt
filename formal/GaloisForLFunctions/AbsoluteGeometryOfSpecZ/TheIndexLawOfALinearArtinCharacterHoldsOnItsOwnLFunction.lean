import GaloisForLFunctions.RHTower.Artin.ALinearCharacterWithTrivialArtinSymbolsAtAlmostAllPrimesIsTrivial
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheZerosOfARayClassLFunctionAreTheZerosOfItsPrimitiveCharacter

/-!
# The index law of a linear Artin character holds on its own `L`-function

Let `L/K` be a Galois extension of number fields with group `G` and `χ ≠ 1` a linear character
of `G`, with Euler product `L(s, χ, L/K)` on `Re s > 1`.

* **Quotients of Euler factors** (`eulerFactorQuotient`): a finite product of factors
  `(1 − a_v N v^{−s}) / (1 − b_v N v^{−s})` with `|a_v|, |b_v| ≤ 1` is analytic without zeros on
  `Re s > 0`.
* **Continuations** (`rightZeros_heckeZeros_eq_of_eq_mul_eulerFactorQuotient`). Let `ψ ≠ 1` be a
  primitive ray class character and `Λ` analytic on `Re s > 1/2` with
  `Λ = L(·, ψ) · (quotient of Euler factors)` on `Re s > 1`. The half plane is connected, so the
  identity holds on it, and the zeros of `Λ` right of the critical line are the right zeros of
  the configuration of `ψ`.
* **The index law** (`exists_zeroConfig_linearCharacter`). There is a tempered configuration `Z`
  such that for every `Λ` analytic on `Re s > 1/2` and equal to the Euler product of `χ` on
  `Re s > 1`: the zeros of `Λ` right of the line are the right zeros of `Z`, Weil's form of `Z`
  has `n` negative squares on some family of `n` tests iff `Λ` has at least `n` distinct zeros
  right of the line, and it has no negative square iff `Λ` has no zero there. `Z` is the
  configuration of the primitive ray class character of `χ`, nontrivial since `χ` is.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical

universe u

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry IsDedekindDomain

/-! ### Quotients of Euler factors -/

section EulerFactors

variable {K : Type*} [Field K] [NumberField K]

/-- A finite product of quotients of Euler factors:
`Π_{v ∈ S} (1 − a_v N v^{−s}) (1 − b_v N v^{−s})^{−1}`. -/
def eulerFactorQuotient (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a b : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏ v ∈ S, ((1 - a v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
    (1 - b v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)

/-- A quotient of Euler factors with coefficients of absolute value at most `1` does not vanish
for `Re s > 0`. -/
theorem eulerFactorQuotient_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a b : HeightOneSpectrum (𝓞 K) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) (hb : ∀ v, ‖b v‖ ≤ 1) {s : ℂ}
    (hs : 0 < s.re) : eulerFactorQuotient S a b s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero
    (one_sub_mul_absNorm_cpow_ne_zero v (ha v) hs)
    (inv_ne_zero (one_sub_mul_absNorm_cpow_ne_zero v (hb v) hs))

/-- A quotient of Euler factors with denominators of coefficients at most `1` is analytic on
`Re s > 0`. -/
theorem differentiableOn_eulerFactorQuotient (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) {b : HeightOneSpectrum (𝓞 K) → ℂ}
    (hb : ∀ v, ‖b v‖ ≤ 1) :
    DifferentiableOn ℂ (eulerFactorQuotient S a b) {s : ℂ | 0 < s.re} := by
  show DifferentiableOn ℂ (fun s : ℂ => ∏ v ∈ S,
    ((1 - a v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
      (1 - b v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)) _
  refine DifferentiableOn.fun_finsetProd fun v _ => ?_
  exact (differentiable_one_sub_mul_absNorm_cpow v (a v)).differentiableOn.mul
    ((differentiable_one_sub_mul_absNorm_cpow v (b v)).differentiableOn.inv fun s hs =>
      one_sub_mul_absNorm_cpow_ne_zero v (hb v) hs)

/-- **A continuation of `L(s, ψ)` times a quotient of Euler factors has the right zeros of
`ψ`.** For a primitive ray class character `ψ ≠ 1` and `Λ` analytic on `Re s > 1/2` with
`Λ = L(·, ψ) · Q` on `Re s > 1`, `Q` a quotient of Euler factors: the zeros of `Λ` right of the
critical line are the zeros of the configuration of `ψ` there. -/
theorem rightZeros_heckeZeros_eq_of_eq_mul_eulerFactorQuotient {𝔫 : Modulus K}
    {ψ : HeckeCharacter 𝔫} (hprim : heckeFiniteConductor 𝔫 ψ = 𝔫.fin) (hψ : ψ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {a b : HeightOneSpectrum (𝓞 K) → ℂ}
    (ha : ∀ v, ‖a v‖ ≤ 1) (hb : ∀ v, ‖b v‖ ≤ 1) {Λ : ℂ → ℂ}
    (hΛ : DifferentiableOn ℂ Λ {s : ℂ | 1 / 2 < s.re})
    (hΛL : ∀ s : ℂ, 1 < s.re → Λ s = heckeL 𝔫 ψ s * eulerFactorQuotient S a b s) :
    ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔫 ψ hprim) =
      {ρ : ℂ | 1 / 2 < ρ.re ∧ Λ ρ = 0} := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {s : ℂ | 1 / 2 < s.re} :=
    convex_halfSpace_gt ⟨fun _ _ => rfl, fun a z => by simp⟩ _
  have hF : DifferentiableOn ℂ (fun s => heckeLFunction 𝔫 ψ s * eulerFactorQuotient S a b s)
      {s : ℂ | 1 / 2 < s.re} :=
    (differentiable_heckeLFunction 𝔫 hψ).differentiableOn.mul
      ((differentiableOn_eulerFactorQuotient S a hb).mono fun s (hs : 1 / 2 < s.re) =>
        show 0 < s.re by linarith)
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 / 2 : ℝ) < (2 : ℂ).re
    norm_num
  -- `Λ` and the continuation agree on `Re s > 1`, hence on the half plane
  have he : Λ =ᶠ[𝓝 2] fun s => heckeLFunction 𝔫 ψ s * eulerFactorQuotient S a b s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    rw [hΛL s hs, heckeLFunction_eq_heckeL 𝔫 ψ hs]
  have heq : ∀ ρ : ℂ, 1 / 2 < ρ.re →
      Λ ρ = heckeLFunction 𝔫 ψ ρ * eulerFactorQuotient S a b ρ := fun ρ hρ =>
    (hΛ.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hF.analyticOnNhd hU)
      hconv.isPreconnected h2 he hρ
  ext ρ
  constructor
  · rintro ⟨hρ, hre⟩
    have hre' : 1 / 2 < ρ.re := hre
    have hρ' : heckeXi 𝔫 ψ ρ = 0 := hρ
    refine ⟨hre, ?_⟩
    rw [heq ρ hre', (heckeXi_eq_zero_iff 𝔫 hψ (by linarith)).mp hρ', zero_mul]
  · rintro ⟨hre, hρ⟩
    have hre' : 1 / 2 < ρ.re := hre
    rw [heq ρ hre', mul_eq_zero,
      or_iff_left (eulerFactorQuotient_ne_zero S ha hb (by linarith))] at hρ
    have hρ' : heckeXi 𝔫 ψ ρ = 0 := (heckeXi_eq_zero_iff 𝔫 hψ (by linarith)).mpr hρ
    exact ⟨hρ', hre⟩

end EulerFactors

/-! ### Linear Artin characters -/

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The zeros of the `L`-function of a linear Artin character right of the critical line are
the right zeros of the configuration of a primitive ray class character `ψ ≠ 1`**, for every
continuation of the Euler product that is analytic on `Re s > 1/2`. -/
theorem exists_heckeZeros_linearCharacter {χ : LinearCharacter G} (hχ : χ ≠ 1) :
    ∃ (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫) (hprim : heckeFiniteConductor 𝔫 ψ = 𝔫.fin),
      ψ ≠ 1 ∧ ∀ Λ : ℂ → ℂ, DifferentiableOn ℂ Λ {s : ℂ | 1 / 2 < s.re} →
        (∀ s : ℂ, 1 < s.re → Λ s = numberFieldFinitePlaceArtinEulerReciprocalProduct
          (K := K) (L := L) (linearCharacterLine χ) s) →
        ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔫 ψ hprim) =
          {ρ : ℂ | 1 / 2 < ρ.re ∧ Λ ρ = 0} := by
  obtain ⟨c, hc, 𝔫, ψ, hprim, hψ, -, hL⟩ :=
    exists_primitive_heckeCharacter_ne_one_artinSymbol K L hχ
  exact ⟨𝔫, ψ, hprim, hψ, fun Λ hΛ hΛL =>
    rightZeros_heckeZeros_eq_of_eq_mul_eulerFactorQuotient hprim hψ
      (finite_primes_dvd (normModulus K c)).toFinset
      (a := fun v => heckeValue 𝔫 ψ v.asIdeal) (b := fun v => artinSymbol K L χ v)
      (fun v => norm_heckeValue_le_one 𝔫 ψ v.asIdeal) (norm_artinSymbol_le_one K L χ) hΛ
      fun s hs => (hΛL s hs).trans (hL s hs)⟩

/-- **The index law of a linear Artin character.** For `χ ≠ 1` there is a tempered
configuration `Z` such that, for every `Λ` analytic on `Re s > 1/2` and equal to the Euler
product of `χ` on `Re s > 1`: the right zeros of `Z` are the zeros of `Λ` right of the critical
line; Weil's form of `Z` has `n` negative squares on some family of `n` tests iff `Λ` has at
least `n` distinct zeros right of the line; and it has no negative square on any family iff
`Λ` has no zero right of the line. -/
theorem exists_zeroConfig_linearCharacter {χ : LinearCharacter G} (hχ : χ ≠ 1) :
    ∃ Z : Zeta23.ZeroConfig, SquareRootThreshold.TemperedConfig Z ∧
      ∀ Λ : ℂ → ℂ, DifferentiableOn ℂ Λ {s : ℂ | 1 / 2 < s.re} →
        (∀ s : ℂ, 1 < s.re → Λ s = numberFieldFinitePlaceArtinEulerReciprocalProduct
          (K := K) (L := L) (linearCharacterLine χ) s) →
        ArithmeticCastelnuovoSeveri.rightZeros Z = {ρ : ℂ | 1 / 2 < ρ.re ∧ Λ ρ = 0} ∧
        (∀ n : ℕ, (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
            (∀ i, HasCompactSupport (f i)) ∧
            n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram Z f)) ↔
          (n : ℕ∞) ≤ {ρ : ℂ | 1 / 2 < ρ.re ∧ Λ ρ = 0}.encard) ∧
        ((∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
            (∀ i, HasCompactSupport (f i)) →
            hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram Z f) = 0) ↔
          ∀ ρ : ℂ, 1 / 2 < ρ.re → Λ ρ ≠ 0) := by
  obtain ⟨𝔫, ψ, hprim, -, hright⟩ := exists_heckeZeros_linearCharacter K L hχ
  refine ⟨heckeZeros 𝔫 ψ hprim, temperedConfig_heckeZeros 𝔫 ψ hprim, fun Λ hΛ hΛL => ?_⟩
  have hr := hright Λ hΛ hΛL
  refine ⟨hr, fun n => ?_, ?_⟩
  · rw [← hr]
    exact exists_le_negIndex_heckeGram_iff 𝔫 ψ hprim n
  · rw [forall_negIndex_heckeGram_eq_zero_iff 𝔫 ψ hprim,
      ← rightZeros_heckeZeros_eq_empty_iff 𝔫 ψ hprim, hr]
    exact ⟨fun h ρ hre hρ => (Set.eq_empty_iff_forall_notMem.mp h) ρ ⟨hre, hρ⟩,
      fun h => Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => h ρ hρ.1 hρ.2⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
