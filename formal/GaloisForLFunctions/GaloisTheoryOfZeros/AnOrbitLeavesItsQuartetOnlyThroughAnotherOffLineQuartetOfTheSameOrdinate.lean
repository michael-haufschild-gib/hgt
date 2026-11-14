import GaloisForLFunctions.GaloisTheoryOfZeros.TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField

/-!
# An orbit leaves its quartet only through another off-line quartet of the same ordinate

`B` is the prime trace field and `G = Gal(E/B)` acts on the zeros, keeping the absolute ordinate;
an orbit meets the critical line only if it starts there. For a zero `ρ = β + iγ` the quartet is
`{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`.

* **Leaving the quartet** (`exists_offLine_of_not_mem_quartet`). If some `σ` sends `ρ` outside
  its quartet, then `ρ` is off the line and `σρ` is an off-line zero of the same absolute
  ordinate with real part outside `{β, 1 − β}`: two off-line quartets share an ordinate.
* **One quartet per ordinate** (`sum_prod_mem_of_offLine_unique`). If the off-line zeros of
  absolute ordinate `|γ|` all have real part `β` or `1 − β`, the orbit lies in the quartet, so
  `u + v, uv ∈ B` (`u`, `v` the ordinate and width values) and the three orbit types of the
  quartet criterion are the only ones.
* **Central conjugation** (`primeWeightValue_map_of_ordinate_mem`,
  `mem_quartet_iff_weight_conjugates`). If the ordinate value of `ρ` lies in `B`, every `σ`
  carries the weight value `p^{2β}` to `p^{2 Re σρ}`: the conjugates of `p^{2β}` are the weight
  values of the orbit, and the orbit leaves the quartet iff `p^{2β}` has a conjugate other than
  `p^{2β}` and `p^{2−2β}`.

So leaving the quartet is not a Galois phenomenon of one quartet: it needs a coincidence of
ordinates between distinct off-line quartets, a statement about the zero configuration.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local notation "Δ" => rawZeroRelationGroup
local instance : IsGalois B E := ⟨⟩

/-! ## Leaving the quartet -/

/-- **Leaving the quartet.** An image of `ρ` outside its quartet is an off-line zero of the same
absolute ordinate whose real part is neither `β` nor `1 − β`, and `ρ` itself is off the line. -/
theorem exists_offLine_of_not_mem_quartet (ρ : XiDivisorSupport) (σ : G)
    (h : ¬ (primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ))) :
    (ρ : ℂ).re ≠ 1 / 2 ∧ |(primeTraceZeroMap σ ρ : ℂ).im| = |(ρ : ℂ).im| ∧
      (primeTraceZeroMap σ ρ : ℂ).re ≠ 1 / 2 ∧ (primeTraceZeroMap σ ρ : ℂ).re ≠ (ρ : ℂ).re ∧
        (primeTraceZeroMap σ ρ : ℂ).re ≠ 1 - (ρ : ℂ).re := by
  rw [mem_quartet_iff_re] at h
  obtain ⟨h1, h2⟩ := not_or.1 h
  have hβ : (ρ : ℂ).re ≠ 1 / 2 := by
    intro e
    rcases primeTraceZeroMap_rational_orbit ρ ⟨1 / 2, by rw [e]; norm_num⟩ σ with e' | e'
    · exact h1 (by rw [e'])
    · exact h1 (by rw [e']; exact Complex.conj_re _)
  exact ⟨hβ, primeTraceZeroMap_height σ ρ,
    fun e => hβ ((primeTraceOrbit_meets_critical_iff ρ).1 ⟨σ, e⟩), h1, h2⟩

/-- If the off-line zeros of absolute ordinate `|γ|` have real part `β` or `1 − β`, every
arithmetic automorphism keeps the quartet of `ρ`. -/
theorem mem_quartet_of_offLine_unique (ρ : XiDivisorSupport)
    (hu : ∀ ρ' : XiDivisorSupport, |(ρ' : ℂ).im| = |(ρ : ℂ).im| → (ρ' : ℂ).re ≠ 1 / 2 →
      (ρ' : ℂ).re = (ρ : ℂ).re ∨ (ρ' : ℂ).re = 1 - (ρ : ℂ).re) (σ : G) :
    primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ) := by
  by_contra h
  obtain ⟨-, hi, hc, h1, h2⟩ := exists_offLine_of_not_mem_quartet ρ σ h
  rcases hu _ hi hc with e | e
  · exact h1 e
  · exact h2 e

/-- **One quartet per ordinate.** If the off-line zeros of absolute ordinate `|γ|` have real part
`β` or `1 − β`, then the ordinate and width values of `ρ` solve a quadratic over `B`. -/
theorem sum_prod_mem_of_offLine_unique (p : Nat.Primes) (ρ : XiDivisorSupport)
    (hu : ∀ ρ' : XiDivisorSupport, |(ρ' : ℂ).im| = |(ρ : ℂ).im| → (ρ' : ℂ).re ≠ 1 / 2 →
      (ρ' : ℂ).re = (ρ : ℂ).re ∨ (ρ' : ℂ).re = 1 - (ρ : ℂ).re) :
    ((primeOrdinateValue p ρ + primeWidthValue p ρ : E) : ℂ) ∈ B ∧
      ((primeOrdinateValue p ρ * primeWidthValue p ρ : E) : ℂ) ∈ B :=
  (sum_prod_mem_iff_mem_quartet p ρ).2 (mem_quartet_of_offLine_unique ρ hu)

/-! ## Central conjugation: the conjugates of the weight -/

/-- If `σ` keeps `ρ, ρ̄` conjugate, it carries the weight of `ρ` to the weight of `σρ`. -/
theorem primeTraceExponentHom_weight_of_conj (σ : G) (ρ : XiDivisorSupport)
    (hc : primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ)) :
    primeTraceExponentHom σ (primeTraceWeight ρ) = primeTraceWeight (primeTraceZeroMap σ ρ) := by
  rw [primeTraceWeight, map_add, primeTraceExponentHom_root, primeTraceExponentHom_root, hc]
  rfl

/-- If the ordinate value of `ρ` lies in `B`, each `σ` carries `p^{2β}` to `p^{2 Re σρ}`. -/
theorem primeWeightValue_map_of_ordinate_mem (p q : Nat.Primes) (ρ : XiDivisorSupport)
    (hu : (primeOrdinateValue q ρ : ℂ) ∈ B) (σ : G) :
    σ (primeWeightValue p ρ) = primeWeightValue p (primeTraceZeroMap σ ρ) := by
  rw [primeWeightValue, ← primeTraceExponentHom_value,
    primeTraceExponentHom_weight_of_conj σ ρ ((primeOrdinateValue_mem_iff_conj q ρ).1 hu σ)]
  rfl

/-- Weight values are equal iff the real parts are. -/
theorem primeWeightValue_eq_iff (p : Nat.Primes) (x y : XiDivisorSupport) :
    primeWeightValue p x = primeWeightValue p y ↔ (x : ℂ).re = (y : ℂ).re := by
  have hp : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  rw [Subtype.ext_iff, primeWeightValue_coe, primeWeightValue_coe, Complex.ofReal_inj]
  constructor
  · intro h
    have h1 := (Real.rpow_le_rpow_left_iff hp).1 h.le
    have h2 := (Real.rpow_le_rpow_left_iff hp).1 h.ge
    linarith only [h1, h2]
  · intro h
    rw [h]

/-- **Central conjugation.** If the ordinate value of `ρ` lies in `B`, the orbit of `ρ` stays in
its quartet iff every conjugate of `p^{2β}` is `p^{2β}` or `p^{2−2β}`. -/
theorem mem_quartet_iff_weight_conjugates (p q : Nat.Primes) (ρ : XiDivisorSupport)
    (hu : (primeOrdinateValue q ρ : ℂ) ∈ B) :
    (∀ σ : G, primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ)) ↔
    ∀ σ : G, σ (primeWeightValue p ρ) = primeWeightValue p ρ ∨
      σ (primeWeightValue p ρ) = primeWeightValue p (xiZeroReflectEquiv ρ) := by
  refine forall_congr' fun σ => ?_
  rw [mem_quartet_iff_re, primeWeightValue_map_of_ordinate_mem p q ρ hu σ,
    primeWeightValue_eq_iff, primeWeightValue_eq_iff, xiZeroReflectEquiv_apply, Complex.sub_re,
    Complex.one_re]

end GaloisForLFunctions.GaloisTheoryOfZeros
