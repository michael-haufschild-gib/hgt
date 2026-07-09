/-
# Baker's theorem and the algebraic independence of the weld spectrum

The archimedean–difference weld `𝓜⁺` glues the generator `∂_s` to the prime shifts `{σ_p}`; the
rate of `σ_p` is `log p`, and the founding weld is spanned by the rate group `⟨log p⟩ ⊆ ℝ`.  Unique
factorization already gives the **`ℤ`-linear independence** of the rates `{log p}`
(`primeLog_linearIndependent`, `two_prime_log_indep`): no nontrivial *integer* combination of prime
logs vanishes.  The one-exponential Hermite/Lindemann engine already in this tree refines each single
rate to transcendental (`primeLog_transcendental`), and Gelfond–Schneider handles a single *ratio*
`log q / log p` (`log_ratio_transcendental`).

The next tier of relation structure is the **`ℚ̄`-linear independence** of the whole family
`{log p}`: no nontrivial combination with *algebraic* coefficients vanishes.  This is strictly
stronger than the `ℤ`-independence above and lies beyond the two-variable Gelfond–Schneider method —
it is Baker's theorem (1966): the logarithms of distinct primes (indeed of multiplicatively
independent algebraic numbers) are linearly independent over `ℚ̄`.

The hard analytic content — Baker's theorem itself — is carried here as the single explicit interface
`BakerLinearIndependence`, encoded with complex coefficients each `IsAlgebraic ℤ` (the clean encoding
of "`ℚ̄`-linear independence" that avoids constructing `ℚ̄` as a field type).  Everything downstream is
derived unconditionally-modulo-that-interface:

* `primeLog_algIndep` — the real-coefficient form: any real algebraic linear relation among distinct
  prime logs is trivial (the direct strengthening of `primeLog_linearIndependent` from `ℤ` to `ℚ̄`);
* `baker_prime_mult_indep` — the multiplicative form, through the `log`-bridge: for distinct primes
  and real algebraic exponents, `∏ pᵢ ^ cᵢ = 1` forces every exponent to vanish;
* `baker_recovers_two_prime_log_indep` — the interface recovers the tree's `two_prime_log_indep`, so
  it sits above the proven `ℤ` layer;
* `baker_intFragment_unconditional` — the integer-coefficient fragment is *already* a theorem
  (`primeLog_linearIndependent`), locating Baker's genuinely new content exactly in the extension to
  non-integer algebraic coefficients.
-/

import Mathlib
import GaloisForLFunctions.RHTower.WeldRateLattice

open scoped Classical

namespace GaloisForLFunctions.RHTower

/-! ### §1 The Baker interface (the analytic residual) -/

/-- **Baker's theorem (linear forms in logarithms of primes).**  For every finite injective family of
primes `p : Fin n → ℕ` and every family of complex coefficients `β : Fin n → ℂ` each algebraic over
`ℤ`, a vanishing linear form `∑ᵢ βᵢ · log pᵢ = 0` forces every coefficient `βᵢ = 0`.  Equivalently:
the prime logarithms `{log p}` are linearly independent over the algebraic numbers `ℚ̄` (encoded here
as complex coefficients each `IsAlgebraic ℤ`, avoiding `ℚ̄` as an explicit field).

This is the single hard analytic input, not proved here.  It is strictly stronger than the
unique-factorization `ℤ`-independence already in this tree and lies beyond the two-variable
Gelfond–Schneider method: its proof is Baker's method — auxiliary functions in *several* complex
variables, with an interpolation/extrapolation determinant estimate and a zero bound, extending the
Gelfond–Schneider construction to `n` logarithms simultaneously. -/
def BakerLinearIndependence : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℕ) (β : Fin n → ℂ),
    Function.Injective p → (∀ i, (p i).Prime) → (∀ i, IsAlgebraic ℤ (β i)) →
    ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0 → ∀ i, β i = 0

/-- The target-shape restatement of the interface: under `BakerLinearIndependence`, any complex
algebraic-coefficient linear form in distinct prime logs that vanishes is trivial. -/
theorem baker_linearIndependence (hB : BakerLinearIndependence) {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime) (β : Fin n → ℂ)
    (hβ : ∀ i, IsAlgebraic ℤ (β i)) (hrel : ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0) :
    ∀ i, β i = 0 :=
  hB n p β hp hprime hβ hrel

/-! ### §2 Algebraicity transfers: `ℝ ↪ ℂ` and integer casts -/

/-- A real number algebraic over `ℤ` stays algebraic over `ℤ` under the embedding `ℝ ↪ ℂ`. -/
private lemma isAlgebraic_ofReal {x : ℝ} (h : IsAlgebraic ℤ x) : IsAlgebraic ℤ (x : ℂ) := by
  have h2 := h.algHom (IsScalarTower.toAlgHom ℤ ℝ ℂ)
  have hx : (IsScalarTower.toAlgHom ℤ ℝ ℂ) x = (x : ℂ) := by simp [Complex.coe_algebraMap]
  rwa [hx] at h2

/-- Every rational integer, viewed as a real number, is algebraic over `ℤ`. -/
private lemma isAlgebraic_intCast (a : ℤ) : IsAlgebraic ℤ ((a : ℤ) : ℝ) := by
  rw [show ((a : ℤ) : ℝ) = algebraMap ℤ ℝ a from by rw [algebraMap_int_eq]; simp]
  exact isAlgebraic_algebraMap a

/-! ### §3 Native consequences of the interface -/

/-- **Algebraic independence of the prime rates (real form).**  From `BakerLinearIndependence`, any
linear relation `∑ᵢ cᵢ · log pᵢ = 0` among distinct prime logs with *real algebraic* coefficients
`cᵢ` is trivial.  This is the direct strengthening of the tree's `ℤ`-independence
(`primeLog_linearIndependent`) to algebraic coefficients: the weld's rate group `⟨log p⟩` is not
merely `ℤ`-free but `ℚ̄`-free.  Proof: embed the real relation along `ℝ ↪ ℂ` (algebraicity transfers
by `isAlgebraic_ofReal`) and apply the interface, then descend the vanishing coefficients back to
`ℝ`. -/
theorem primeLog_algIndep (hB : BakerLinearIndependence) {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : Fin n → ℝ) (halg : ∀ i, IsAlgebraic ℤ (c i))
    (hrel : ∑ i, c i * Real.log (p i) = 0) : ∀ i, c i = 0 := by
  have hrelC : ∑ i, ((c i : ℝ) : ℂ) * ((Real.log (p i) : ℝ) : ℂ) = 0 := by
    have hz : ((∑ i, c i * Real.log (p i) : ℝ) : ℂ) = 0 := by rw [hrel]; simp
    rw [Complex.ofReal_sum] at hz
    simp only [Complex.ofReal_mul] at hz
    exact hz
  have hcC : ∀ i, ((c i : ℝ) : ℂ) = 0 :=
    hB n p (fun i => (c i : ℂ)) hp hprime (fun i => isAlgebraic_ofReal (halg i)) hrelC
  intro i
  exact Complex.ofReal_eq_zero.mp (hcC i)

/-- **Multiplicative independence of the prime bases (algebraic exponents).**  From
`BakerLinearIndependence`, for distinct primes `pᵢ` and *real algebraic* exponents `cᵢ`, a
multiplicative relation `∏ᵢ pᵢ ^ cᵢ = 1` (real `rpow`) forces every exponent `cᵢ = 0`.  This is the
genuine downstream of the additive statement through the logarithm bridge: taking `Real.log` of the
product (each factor positive, hence nonzero) turns `∏ pᵢ ^ cᵢ = 1` into `∑ᵢ cᵢ · log pᵢ = 0`, to
which `primeLog_algIndep` applies.  With integer exponents this is unique factorization; with
algebraic exponents it is Baker. -/
theorem baker_prime_mult_indep (hB : BakerLinearIndependence) {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : Fin n → ℝ) (halg : ∀ i, IsAlgebraic ℤ (c i))
    (hprod : ∏ i, (p i : ℝ) ^ (c i) = 1) : ∀ i, c i = 0 := by
  apply primeLog_algIndep hB p hp hprime c halg
  have hpos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by exact_mod_cast (hprime i).pos
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), (p i : ℝ) ^ (c i) ≠ 0 :=
    fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hpos i) (c i))
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod hne, Real.log_one] at hlog
  rw [← hlog]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_rpow (hpos i)]

/-! ### §4 Sitting above the proven `ℤ` layer -/

/-- **The interface recovers the tree's two-prime `ℤ`-independence.**  From
`BakerLinearIndependence`, for distinct primes `p ≠ q` an integer relation
`a · log p + b · log q = 0` forces `a = b = 0` — the exact statement of the unconditional
`two_prime_log_indep`, obtained here as the two-variable, integer-coefficient special case of
`primeLog_algIndep`.  The interface therefore sits above the proven `ℤ` layer. -/
theorem baker_recovers_two_prime_log_indep (hB : BakerLinearIndependence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b : ℤ)
    (h : (a : ℝ) * Real.log p + (b : ℝ) * Real.log q = 0) : a = 0 ∧ b = 0 := by
  have hinj : Function.Injective (![p, q] : Fin 2 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hprime : ∀ i, ((![p, q] : Fin 2 → ℕ) i).Prime := by
    intro i; fin_cases i <;> assumption
  have halg : ∀ i, IsAlgebraic ℤ ((![(a : ℝ), (b : ℝ)] : Fin 2 → ℝ) i) := by
    intro i; fin_cases i
    · exact isAlgebraic_intCast a
    · exact isAlgebraic_intCast b
  have hrel : ∑ i, (![(a : ℝ), (b : ℝ)] : Fin 2 → ℝ) i
      * Real.log ((![p, q] : Fin 2 → ℕ) i) = 0 := by
    rw [Fin.sum_univ_two]; simpa using h
  have hall := primeLog_algIndep hB (![p, q] : Fin 2 → ℕ) hinj hprime
    (![(a : ℝ), (b : ℝ)] : Fin 2 → ℝ) halg hrel
  have h0 := hall 0
  have h1 := hall 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

/-- **The integer-coefficient fragment needs no interface.**  For distinct primes `p : Fin n → ℕ`
and *integer* coefficients `z`, a vanishing form `∑ᵢ zᵢ · log pᵢ = 0` already forces `zᵢ = 0`
unconditionally — this is the tree's unique-factorization `ℤ`-independence
(`primeLog_linearIndependent`), pulled back along the injective index map `i ↦ pᵢ`.  Contrasted with
`primeLog_algIndep`, it pins down exactly what Baker adds: nothing at integer coefficients, and the
whole of the `ℚ̄`-independence at non-integer algebraic coefficients. -/
theorem baker_intFragment_unconditional {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (z : Fin n → ℤ) (hrel : ∑ i, (z i : ℝ) * Real.log (p i) = 0) : ∀ i, z i = 0 := by
  have hf : Function.Injective (fun i => (⟨p i, hprime i⟩ : Nat.Primes)) :=
    fun i j hij => hp (congrArg Subtype.val hij)
  have hLI := primeLog_linearIndependent.comp _ hf
  refine (Fintype.linearIndependent_iff.mp hLI) z ?_
  simpa [Function.comp, zsmul_eq_mul] using hrel

end GaloisForLFunctions.RHTower
