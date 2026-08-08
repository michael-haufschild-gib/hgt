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

This file fixes the stable proposition `BakerLinearIndependence`, encoded with complex coefficients
each `IsAlgebraic ℤ`, and proves the reductions that consume it.  The downstream
`BakerProof.BakerIteration` module proves the proposition and exports the premise-free public forms:

* `primeLog_algIndep_of_baker` — the interface-consuming real-coefficient reduction; its public
  premise-free theorem is `primeLog_algIndep`;
  prime logs is trivial (the direct strengthening of `primeLog_linearIndependent` from `ℤ` to `ℚ̄`);
* `baker_prime_mult_indep_of_baker` — the interface-consuming multiplicative reduction; its public
  premise-free theorem is `baker_prime_mult_indep`;
* `twoPrimeLog_algIndep_complex` — the two-prime algebraic-coefficient fragment, now unconditional
  from the formalized Gelfond--Schneider theorem;
* `baker_intFragment_unconditional` — the integer-coefficient fragment is *already* a theorem
  (`primeLog_linearIndependent`), locating Baker's genuinely new content exactly in the extension to
  non-integer algebraic coefficients.
-/

import Mathlib
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.HTGeometry.WeldRateLattice

open scoped Classical

namespace GaloisForLFunctions.RHTower

/-! ### §1 The Baker interface (the analytic residual) -/

/-- **Baker's theorem (linear forms in logarithms of primes).**  For every finite injective family of
primes `p : Fin n → ℕ` and every family of complex coefficients `β : Fin n → ℂ` each algebraic over
`ℤ`, a vanishing linear form `∑ᵢ βᵢ · log pᵢ = 0` forces every coefficient `βᵢ = 0`.  Equivalently:
the prime logarithms `{log p}` are linearly independent over the algebraic numbers `ℚ̄` (encoded here
as complex coefficients each `IsAlgebraic ℤ`, avoiding `ℚ̄` as an explicit field).

This file records the stable interface.  Its unconditional proof is supplied downstream by
`bakerLinearIndependence_holds`: a several-variable integral auxiliary matrix, finite
long extrapolation with decreasing multiplicity, and a terminal Vandermonde zero estimate. -/
def BakerLinearIndependence : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℕ) (β : Fin n → ℂ),
    Function.Injective p → (∀ i, (p i).Prime) → (∀ i, IsAlgebraic ℤ (β i)) →
    ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0 → ∀ i, β i = 0

/-- The project interface is exactly linear independence of the prime logarithms over the field of
algebraic numbers `algebraicClosure ℚ ℂ`. -/
theorem bakerLinearIndependence_iff_algClosure : BakerLinearIndependence ↔
    ∀ (n : ℕ) (p : Fin n → ℕ), Function.Injective p → (∀ i, (p i).Prime) →
      LinearIndependent (algebraicClosure ℚ ℂ) (fun i => (Real.log (p i) : ℂ)) := by
  constructor
  · intro hB n p hp hprime
    rw [Fintype.linearIndependent_iff]
    intro b hsum i
    have hβalg : ∀ j, IsAlgebraic ℤ (((b j : algebraicClosure ℚ ℂ) : ℂ)) := fun j =>
      (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr
        (mem_algebraicClosure_iff.mp (b j).property)
    have hrel : ∑ j, ((b j : algebraicClosure ℚ ℂ) : ℂ) *
        ((Real.log (p j) : ℝ) : ℂ) = 0 := by
      simpa [IntermediateField.smul_def, smul_eq_mul] using hsum
    apply Subtype.ext
    exact hB n p (fun j => ((b j : algebraicClosure ℚ ℂ) : ℂ)) hp hprime hβalg hrel i
  · intro hLI n p β hp hprime hβalg hrel
    have hmem : ∀ i, β i ∈ algebraicClosure ℚ ℂ := fun i =>
      mem_algebraicClosure_iff.mpr
        ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (hβalg i))
    let b : Fin n → algebraicClosure ℚ ℂ := fun i => ⟨β i, hmem i⟩
    have hsum : ∑ i, b i • (fun j => (Real.log (p j) : ℂ)) i = 0 := by
      simpa [b, IntermediateField.smul_def, smul_eq_mul] using hrel
    have hb0 : ∀ i, b i = 0 :=
      (Fintype.linearIndependent_iff.mp (hLI n p hp hprime)) b hsum
    intro i
    exact congrArg Subtype.val (hb0 i)

/-- **Two-prime complex Baker fragment, unconditionally.**  A complex algebraic relation between
the logarithms of two distinct primes would make their real logarithm ratio algebraic.  The
formalized Gelfond--Schneider theorem says that ratio is transcendental. -/
theorem twoPrimeLog_algIndep_complex {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a b : ℂ) (ha : IsAlgebraic ℤ a) (hb : IsAlgebraic ℤ b)
    (hrel : a * ((Real.log p : ℝ) : ℂ) + b * ((Real.log q : ℝ) : ℂ) = 0) :
    a = 0 ∧ b = 0 := by
  have hlogpR : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  have hlogqR : Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hq.one_lt))
  have hlogpC : ((Real.log p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogpR
  have hlogqC : ((Real.log q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogqR
  by_cases hb0 : b = 0
  · subst b
    simp only [zero_mul, add_zero, mul_eq_zero] at hrel
    exact ⟨hrel.resolve_right hlogpC, rfl⟩
  · have hratio : (((Real.log q / Real.log p : ℝ) : ℂ)) = -a / b := by
      rw [Complex.ofReal_div, div_eq_div_iff hlogpC hb0]
      simpa [mul_comm] using eq_neg_of_add_eq_zero_right hrel
    have haQ : IsAlgebraic ℚ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp ha
    have hbQ : IsAlgebraic ℚ b := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hb
    have hratioC : IsAlgebraic ℚ (((Real.log q / Real.log p : ℝ) : ℂ)) := by
      rw [hratio]
      simpa [div_eq_mul_inv] using haQ.neg.mul hbQ.inv
    have hratioR : IsAlgebraic ℚ (Real.log q / Real.log p) :=
      (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ)
        Complex.ofReal_injective).mp hratioC
    exact (log_ratio_transcendental hp hq hpq hratioR).elim

/-- The exact Baker interface is unconditional for families of at most two primes.  Thus the open
analytic core of `BakerLinearIndependence` begins at arity three. -/
theorem bakerLinearIndependence_of_card_le_two (n : ℕ) (hn : n ≤ 2)
    (p : Fin n → ℕ) (β : Fin n → ℂ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (hβ : ∀ i, IsAlgebraic ℤ (β i))
    (hrel : ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0) : ∀ i, β i = 0 := by
  interval_cases n
  · intro i
    exact Fin.elim0 i
  · intro i
    fin_cases i
    have hlog : ((Real.log (p 0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.log_pos (by exact_mod_cast (hprime 0).one_lt)))
    rw [Fin.sum_univ_one] at hrel
    exact (mul_eq_zero.mp hrel).resolve_right hlog
  · have hpq : p 0 ≠ p 1 := fun h => Fin.zero_ne_one (hp h)
    have htwo := twoPrimeLog_algIndep_complex (hprime 0) (hprime 1) hpq
      (β 0) (β 1) (hβ 0) (hβ 1)
    have hrelTwo : β 0 * ((Real.log (p 0) : ℝ) : ℂ) +
        β 1 * ((Real.log (p 1) : ℝ) : ℂ) = 0 := by
      simpa [Fin.sum_univ_two] using hrel
    have hz := htwo hrelTwo
    intro i
    fin_cases i
    · exact hz.1
    · exact hz.2

/-! ### §2 Algebraicity transfers: `ℝ ↪ ℂ` and integer casts -/

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
theorem primeLog_algIndep_of_baker (hB : BakerLinearIndependence) {n : ℕ} (p : Fin n → ℕ)
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
theorem baker_prime_mult_indep_of_baker (hB : BakerLinearIndependence) {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : Fin n → ℝ) (halg : ∀ i, IsAlgebraic ℤ (c i))
    (hprod : ∏ i, (p i : ℝ) ^ (c i) = 1) : ∀ i, c i = 0 := by
  apply primeLog_algIndep_of_baker hB p hp hprime c halg
  have hpos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by exact_mod_cast (hprime i).pos
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), (p i : ℝ) ^ (c i) ≠ 0 :=
    fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hpos i) (c i))
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod hne, Real.log_one] at hlog
  rw [← hlog]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_rpow (hpos i)]

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
