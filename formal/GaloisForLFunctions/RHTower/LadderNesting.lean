import Mathlib
import GaloisForLFunctions.RHTower.SchanuelWeldApex
import GaloisForLFunctions.RHTower.BakerWeldIndependence
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# The weld-spectrum independence ladder nests into a single hierarchy

The archimedean–difference weld `𝓜⁺` carries the prime-log rate spectrum `{log p} ⊆ ℝ`, whose
independence is graded in ever finer statements:

* `ℤ`-linear independence (`primeLog_linearIndependent`) — unique factorization;
* `ℚ̄`-linear independence (`BakerLinearIndependence`) — Baker's theorem;
* transcendence of the pairwise ratio `log q / log p` (`log_ratio_transcendental`) —
  Gelfond–Schneider;
* **algebraic independence over `ℚ`** (`primeLogs_algebraicallyIndependent`) — the apex, exactly
  Schanuel's conjecture on the family `x_i = log p_i`.

Each rung was carried as its own analytic interface.  This file proves the apex is genuinely on top:
**Schanuel's conjecture implies the two lower analytic rungs**, so the ladder is one nested
hierarchy rather than four independent inputs.

The engine is base change of the transcendence structure.  Algebraic independence of `{log p}` over
`ℚ` upgrades, along the tower `ℚ → ℚ̄ = algebraicClosure ℚ ℂ → ℂ`, to algebraic independence over the
field of algebraic numbers `ℚ̄` (`AlgebraicIndependent.algebraicClosure`), and algebraic independence
always entails linear independence (`AlgebraicIndependent.linearIndependent`).  Thus `{log p}` is
`ℚ̄`-linearly independent — which is precisely `BakerLinearIndependence` once the algebraic
coefficients are read as elements of `ℚ̄`.  The Gelfond–Schneider conclusion then follows from the
Baker rung without ever touching the `GelfondSchneider` interface: a rational value of the ratio
`log q / log p` would be a `ℚ̄`-linear relation with coefficient `1 ≠ 0` between `log p` and `log q`.
-/

namespace GaloisForLFunctions.RHTower

/-! ### §1 The core base-change step: `ℚ̄`-linear independence of the prime spectrum -/

/-- **The prime rates are linearly independent over the algebraic numbers, given Schanuel.**  For
distinct primes `p₁, …, pₙ` the archimedean rates `log p₁, …, log pₙ` are linearly independent over
`ℚ̄ = algebraicClosure ℚ ℂ`.  This is the `ℚ̄`-linear shadow of the apex: algebraic independence over
`ℚ` (`primeLogs_algebraicallyIndependent`) is preserved when the scalars are enlarged from `ℚ` to
its algebraic closure inside `ℂ` (`AlgebraicIndependent.algebraicClosure`), and algebraic
independence entails linear independence (`AlgebraicIndependent.linearIndependent`). -/
theorem primeLogs_algClosure_linearIndependent (hS : SchanuelConjecture)
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    LinearIndependent (algebraicClosure ℚ ℂ) (fun i => (Real.log (p i) : ℂ)) :=
  (primeLogs_algebraicallyIndependent hS p hp hpinj).algebraicClosure.linearIndependent

/-! ### §2 Rung 1 — Schanuel implies Baker -/

/-- **Schanuel's conjecture implies Baker's linear-independence interface.**  Under
`SchanuelConjecture`, for every finite injective family of primes and complex coefficients each
algebraic over `ℤ`, a vanishing linear form `∑ᵢ βᵢ · log pᵢ = 0` forces every `βᵢ = 0` — i.e.
`BakerLinearIndependence` holds.

Proof.  Each `βᵢ`, being algebraic over `ℤ` hence over `ℚ` (`IsFractionRing.isAlgebraic_iff`), is an
element of `ℚ̄ = algebraicClosure ℚ ℂ` (`mem_algebraicClosure_iff`); lift it to `bᵢ ∈ ℚ̄`.  The scalar
action of `ℚ̄` on `ℂ` is multiplication (`IntermediateField.smul_def`), so the hypothesised relation
reads `∑ᵢ bᵢ • log pᵢ = 0`.  Since `{log p}` is `ℚ̄`-linearly independent
(`primeLogs_algClosure_linearIndependent`), every `bᵢ = 0`, hence every `βᵢ = 0`. -/
theorem schanuel_imp_baker (hS : SchanuelConjecture) : BakerLinearIndependence := by
  intro n p β hpinj hprime hβalg hrel
  have hLI : LinearIndependent (algebraicClosure ℚ ℂ) (fun i => (Real.log (p i) : ℂ)) :=
    primeLogs_algClosure_linearIndependent hS p hprime hpinj
  -- Lift each algebraic coefficient `β i` into `ℚ̄ = algebraicClosure ℚ ℂ`.
  have hmem : ∀ i, β i ∈ algebraicClosure ℚ ℂ := fun i =>
    mem_algebraicClosure_iff.mpr ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (hβalg i))
  let b : Fin n → algebraicClosure ℚ ℂ := fun i => ⟨β i, hmem i⟩
  have hbcoe : ∀ i, ((b i : algebraicClosure ℚ ℂ) : ℂ) = β i := fun _ => rfl
  -- The `ℚ̄`-linear form induced by the lifted coefficients is exactly the hypothesised relation.
  have hconv : ∀ i, b i • (fun j => (Real.log (p j) : ℂ)) i
      = β i * ((Real.log (p i) : ℝ) : ℂ) := by
    intro i
    rw [IntermediateField.smul_def, smul_eq_mul, hbcoe i]
  have hsum : ∑ i, b i • (fun j => (Real.log (p j) : ℂ)) i = 0 := by
    have hcongr : ∑ i, b i • (fun j => (Real.log (p j) : ℂ)) i
        = ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) :=
      Finset.sum_congr rfl (fun i _ => hconv i)
    rw [hcongr]; exact hrel
  have hb0 : ∀ i, b i = 0 := (Fintype.linearIndependent_iff.mp hLI) b hsum
  intro i
  rw [← hbcoe i, hb0 i]
  simp

/-! ### §3 Rung 2 — Schanuel implies the Gelfond–Schneider ratio conclusion -/

/-- **Schanuel's conjecture implies transcendence of a prime-rate ratio.**  For distinct primes
`p, q`, the ratio `log q / log p` is transcendental over `ℚ` — the conclusion of
`log_ratio_transcendental`, obtained here from the apex *without* invoking the `GelfondSchneider`
interface.

Proof.  Were `ρ = log q / log p` algebraic over `ℚ`, then `1 · log q + (−ρ) · log p = 0` is a
linear relation among the two prime logs with real algebraic coefficients, the first equal to `1`.
Schanuel supplies the Baker rung (`schanuel_imp_baker`), whose real form (`primeLog_algIndep`) forces
every coefficient to vanish — contradicting the coefficient `1 ≠ 0`. -/
theorem schanuel_ratio_transcendental (hS : SchanuelConjecture) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (Real.log q / Real.log p) := by
  have hB : BakerLinearIndependence := schanuel_imp_baker hS
  set ρ : ℝ := Real.log q / Real.log p with hρ
  intro hρalg
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hcancel : Real.log p * ρ = Real.log q := by rw [hρ]; field_simp
  have hρℤ : IsAlgebraic ℤ ρ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hρalg
  have hinj : Function.Injective (![p, q] : Fin 2 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hprime : ∀ i, ((![p, q] : Fin 2 → ℕ) i).Prime := by
    intro i; fin_cases i <;> assumption
  have halg : ∀ i, IsAlgebraic ℤ ((![(-ρ), (1 : ℝ)] : Fin 2 → ℝ) i) := by
    intro i; fin_cases i
    · exact hρℤ.neg
    · exact isAlgebraic_one
  have hrel : ∑ i, (![(-ρ), (1 : ℝ)] : Fin 2 → ℝ) i
      * Real.log ((![p, q] : Fin 2 → ℕ) i : ℝ) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hcancel]; ring
  have hall := primeLog_algIndep hB (![p, q] : Fin 2 → ℕ) hinj hprime
    (![(-ρ), (1 : ℝ)] : Fin 2 → ℝ) halg hrel
  have h1 := hall 1
  simp only [Matrix.cons_val_one] at h1
  exact one_ne_zero h1

end GaloisForLFunctions.RHTower
