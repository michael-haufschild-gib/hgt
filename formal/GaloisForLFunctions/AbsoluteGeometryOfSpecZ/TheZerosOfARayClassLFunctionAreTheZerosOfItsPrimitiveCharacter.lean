import GaloisForLFunctions.RHTower.Artin.EveryRayClassCharacterIsInducedFromAPrimitiveCharacterOfItsConductor
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheZerosOfAHeckeLFunctionSatisfyWeilsExplicitFormula
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsDoNotVanishOnTheLineReOne

/-!
# The zeros of a ray class `L`-function are the zeros of its primitive character

Let `ψ` be a ray class character modulo `𝔪 = 𝔪₀ 𝔪∞` of a number field, with no hypothesis on its
conductor, and `ψ'` its primitive character, modulo `𝔣(ψ) 𝔪∞`.

* **The `L`-functions** (`heckeLFunction_eq_primitiveHecke_mul`). On `ℂ ∖ {1}`,

  `L(s, ψ) = L(s, ψ') Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})`:

  the identity of the Euler products continues, `ℂ ∖ {1}` being connected.
* **The zeros** (`heckeLFunction_eq_zero_iff_heckeXi_primitiveHecke`). An Euler factor
  `1 − a N v^{−s}`, `|a| ≤ 1`, does not vanish for `Re s > 0`. So for `ψ ≠ 1` the zeros of
  `L(s, ψ)` in `Re s > 0` are the zeros of the completion of `ψ'`.
* **The index law of a ray class character** (`rayClassZeros`,
  `exists_le_negIndex_rayClassGram_iff`, `forall_negIndex_rayClassGram_eq_zero_iff`). Weil's form
  of the configuration of `ψ'` has `n` negative squares on some family of `n` tests iff `L(s, ψ)`
  has at least `n` distinct zeros right of the critical line; it has none on every family iff
  `L(s, ψ)` has no zero with `Re s > 1/2`.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### Euler factors -/

/-- An Euler factor `1 − a N v^{−s}` with `|a| ≤ 1` does not vanish for `Re s > 0`. -/
theorem one_sub_mul_absNorm_cpow_ne_zero (v : HeightOneSpectrum (𝓞 K)) {a : ℂ} (ha : ‖a‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : 1 - a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  have hv : 2 ≤ Ideal.absNorm v.asIdeal :=
    ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hlt : ‖a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    calc ‖a‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)
        ≤ 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ < 1 := by
          rw [one_mul]
          exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hv) (by linarith)
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- An Euler factor is entire. -/
theorem differentiable_one_sub_mul_absNorm_cpow (v : HeightOneSpectrum (𝓞 K)) (a : ℂ) :
    Differentiable ℂ fun s : ℂ => 1 - a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
  have hv : 2 ≤ Ideal.absNorm v.asIdeal :=
    ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (differentiable_const _).sub ((differentiable_const _).mul
    (differentiable_id.neg.const_cpow (Or.inl hN)))

/-- The Euler factors of the primitive character at the primes of the modulus:
`Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})`. -/
def modulusEulerFactor (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
    (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

theorem differentiable_modulusEulerFactor (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (modulusEulerFactor 𝔪 ψ) := by
  show Differentiable ℂ fun s : ℂ => ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
    (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
  exact Differentiable.fun_finsetProd fun (v : HeightOneSpectrum (𝓞 K)) _ =>
    differentiable_one_sub_mul_absNorm_cpow v _

theorem modulusEulerFactor_ne_zero (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 0 < s.re) :
    modulusEulerFactor 𝔪 ψ s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ =>
    one_sub_mul_absNorm_cpow_ne_zero v (norm_heckeValue_le_one _ _ _) hs

/-! ### The `L`-function and its zeros -/

/-- **Every Hecke `L`-function is the `L`-function of its primitive character times the Euler
factors at the modulus**, on `ℂ ∖ {1}`. -/
theorem heckeLFunction_eq_primitiveHecke_mul (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : s ≠ 1) :
    heckeLFunction 𝔪 ψ s =
      heckeLFunction (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s *
        modulusEulerFactor 𝔪 ψ s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ (heckeLFunction 𝔪 ψ) {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_heckeLFunction 𝔪 ψ hz).differentiableWithinAt) hU
  have hg : AnalyticOnNhd ℂ (fun z => heckeLFunction (conductorModulus 𝔪 ψ)
      (primitiveHecke 𝔪 ψ) z * modulusEulerFactor 𝔪 ψ z) {1}ᶜ :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((differentiableAt_heckeLFunction (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) hz).mul
        (differentiable_modulusEulerFactor 𝔪 ψ z)).differentiableWithinAt) hU
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [mem_compl_singleton_iff]
    norm_num
  -- the two sides agree on `Re s > 1`
  have he : heckeLFunction 𝔪 ψ =ᶠ[𝓝 2] fun z => heckeLFunction (conductorModulus 𝔪 ψ)
      (primitiveHecke 𝔪 ψ) z * modulusEulerFactor 𝔪 ψ z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [heckeLFunction_eq_heckeL 𝔪 ψ hz, heckeLFunction_eq_heckeL _ _ hz]
    exact heckeL_eq_heckeL_primitiveHecke_mul 𝔪 ψ hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 he hs

/-- In `Re s > 0`, `s ≠ 1`, the zeros of `L(s, ψ)` are the zeros of `L(s, ψ')`. -/
theorem heckeLFunction_eq_zero_iff_primitiveHecke (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    heckeLFunction 𝔪 ψ s = 0 ↔
      heckeLFunction (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s = 0 := by
  rw [heckeLFunction_eq_primitiveHecke_mul 𝔪 ψ h1, mul_eq_zero,
    or_iff_left (modulusEulerFactor_ne_zero 𝔪 ψ hs)]

/-- **The zeros of `L(s, ψ)`, `ψ ≠ 1`, in `Re s > 0` are the zeros of the completion of the
primitive character.** -/
theorem heckeLFunction_eq_zero_iff_heckeXi_primitiveHecke {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    heckeLFunction 𝔪 ψ s = 0 ↔
      heckeXi (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s = 0 := by
  have hψ' : primitiveHecke 𝔪 ψ ≠ 1 := fun h => hψ ((primitiveHecke_eq_one_iff 𝔪 ψ).mp h)
  rw [heckeXi_eq_zero_iff (conductorModulus 𝔪 ψ) hψ' hs]
  by_cases h1 : s = 1
  · -- neither function vanishes at `1`
    subst h1
    exact iff_of_false
      (heckeLFunction_ne_zero_of_one_le_re 𝔪 ψ (by simp) (Or.inl hψ))
      (heckeLFunction_ne_zero_of_one_le_re (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
        (by simp) (Or.inl hψ'))
  · exact heckeLFunction_eq_zero_iff_primitiveHecke 𝔪 ψ hs h1

/-! ### The configuration and the index law -/

/-- **The zero configuration of a ray class character**: the zeros of the completion of its
primitive character, with their orders. -/
def rayClassZeros (ψ : HeckeCharacter 𝔪) : Zeta23.ZeroConfig :=
  heckeZeros (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
    (heckeFiniteConductor_primitiveHecke 𝔪 ψ)

theorem temperedConfig_rayClassZeros (ψ : HeckeCharacter 𝔪) :
    SquareRootThreshold.TemperedConfig (rayClassZeros 𝔪 ψ) :=
  temperedConfig_heckeZeros (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
    (heckeFiniteConductor_primitiveHecke 𝔪 ψ)

/-- The zeros of the configuration right of the critical line are the zeros of `L(s, ψ)`
there. -/
theorem rightZeros_rayClassZeros {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ArithmeticCastelnuovoSeveri.rightZeros (rayClassZeros 𝔪 ψ) =
      {ρ : ℂ | 1 / 2 < ρ.re ∧ heckeLFunction 𝔪 ψ ρ = 0} := by
  ext ρ
  constructor
  · rintro ⟨hρ, hre⟩
    have hre' : 1 / 2 < ρ.re := hre
    have hρ' : heckeXi (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) ρ = 0 := hρ
    exact ⟨hre, (heckeLFunction_eq_zero_iff_heckeXi_primitiveHecke 𝔪 hψ
      (by linarith)).mpr hρ'⟩
  · rintro ⟨hre, hρ⟩
    have hre' : 1 / 2 < ρ.re := hre
    have hρ' : heckeXi (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) ρ = 0 :=
      (heckeLFunction_eq_zero_iff_heckeXi_primitiveHecke 𝔪 hψ (by linarith)).mp hρ
    exact ⟨hρ', hre⟩

/-- **The index law of a ray class character.** For a nontrivial ray class character `ψ`,
primitive or not, Weil's form of its configuration has `n` negative squares on some family of
`n` tests iff `L(s, ψ)` has at least `n` distinct zeros right of the critical line. -/
theorem exists_le_negIndex_rayClassGram_iff {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (rayClassZeros 𝔪 ψ) f)) ↔
      (n : ℕ∞) ≤ {ρ : ℂ | 1 / 2 < ρ.re ∧ heckeLFunction 𝔪 ψ ρ = 0}.encard := by
  rw [← rightZeros_rayClassZeros 𝔪 hψ]
  exact exists_le_negIndex_heckeGram_iff (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
    (heckeFiniteConductor_primitiveHecke 𝔪 ψ) n

/-- **Castelnuovo and Severi for a ray class character.** Weil's form of the configuration of
a nontrivial ray class character `ψ` has no negative square on any family of tests iff
`L(s, ψ)` has no zero right of the critical line. -/
theorem forall_negIndex_rayClassGram_eq_zero_iff {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (rayClassZeros 𝔪 ψ) f) = 0) ↔
      ∀ ρ : ℂ, 1 / 2 < ρ.re → heckeLFunction 𝔪 ψ ρ ≠ 0 := by
  constructor
  · intro h ρ hre hρ
    have h1 : ((1 : ℕ) : ℕ∞) ≤
        {ρ : ℂ | 1 / 2 < ρ.re ∧ heckeLFunction 𝔪 ψ ρ = 0}.encard := by
      rw [Nat.cast_one, Set.one_le_encard_iff_nonempty]
      exact ⟨ρ, hre, hρ⟩
    obtain ⟨f, hf, hfc, hle⟩ := (exists_le_negIndex_rayClassGram_iff 𝔪 hψ 1).mpr h1
    rw [h 1 f hf hfc] at hle
    exact absurd hle (by norm_num)
  · intro h n f hf hfc
    by_contra hne
    have hpos : 1 ≤ hermNegIndex
        (ArithmeticCastelnuovoSeveri.zeroGram (rayClassZeros 𝔪 ψ) f) :=
      Nat.one_le_iff_ne_zero.mpr hne
    -- one negative square on one combination of the tests gives a zero right of the line
    have hempty : {ρ : ℂ | 1 / 2 < ρ.re ∧ heckeLFunction 𝔪 ψ ρ = 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => h ρ hρ.1 hρ.2
    have hright : ArithmeticCastelnuovoSeveri.rightZeros (rayClassZeros 𝔪 ψ) = ∅ := by
      rw [rightZeros_rayClassZeros 𝔪 hψ, hempty]
    have hzero := (forall_negIndex_heckeGram_eq_zero_iff (conductorModulus 𝔪 ψ)
      (primitiveHecke 𝔪 ψ) (heckeFiniteConductor_primitiveHecke 𝔪 ψ)).mpr
      ((rightZeros_heckeZeros_eq_empty_iff (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
        (heckeFiniteConductor_primitiveHecke 𝔪 ψ)).mp hright) n f hf hfc
    exact hne hzero

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
