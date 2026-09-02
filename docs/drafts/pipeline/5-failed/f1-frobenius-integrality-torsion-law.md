# Door 1: an integral Frobenius with the zeros as eigenvalues, and a producer positivity — refuted

- **ID:** ULF-F1-002
- **Stage:** 5-failed (paper proofs A–E 2026-09-02; Lean no-go `RHTower.FrobeniusTorsionLaw`;
  all Lean targets closed)
- **Type:** ROUTE (construction attempted, falsified) → NO-GO THEOREMS
- **Source:** `0-backlog/terminal-classification-two-doors.md` door 1; `XiArakelovKroneckerChamber`
  (integrality + contractive packets ⇒ RH); `XiArakelovHurwitzAlgebraicityCollision`;
  `DeningerArithmeticSemisimpleHodge` (positivity is not the missing datum, Frobenius
  compatibility of the Hodge star is RH); `GaussHodgeWeilSymmetryInsufficiency`;
  `GelfondSchneider`, `BakerProof` (qualitative Baker in Lean); Connes–Consani (Weil positivity
  at the archimedean place, Selecta 2021; Riemann–Roch strategy 1805.10501); Deninger
  (1807.06400 and the rational Witt space programme).
- **Task:** construct a Frobenius endomorphism whose eigenvalues are the zeros of ξ and which
  carries an integrality of Weil–Deligne type; construct a positivity that produces RH rather
  than restates it.
- **Verdict:** [REFUTED] for every integrality of Weil–Deligne type, in both coordinates in
  which a Frobenius eigenvalue can be normalised; [RH-EQUIVALENT] for every positivity that
  reaches all apertures, [BLIND] at every finite aperture.

## 1. What the Weil–Deligne template needs, exactly

Weil (curves) and Deligne (Weil I) locate zeros by three ingredients: (i) the eigenvalues `α` of
Frobenius on a finite-rank ℤ-lattice, hence algebraic integers with a characteristic polynomial
in `ℤ[T]`; (ii) a bound `|ι(α)| ≤ q^{w/2}` for *every* complex embedding `ι`, from positivity
(Hodge index / Rosati) or from amplification (Rankin on tensor powers); (iii) a lower bound from
duality or from the integer norm `∏_ι ι(α) ∈ ℤ ∖ {0}`. The corpus's chamber theorem is the
literal transport of (i)+(ii)+(iii) to ξ in the Arakelov coordinate `w(ρ) = 1 − 1/ρ`, where the
critical line is the unit circle: integrality plus contractive conjugate packets gives RH. The
task is to *produce* (i) and (ii). The theorems below show that (i) cannot hold in the
normalised coordinate, cannot hold at three primes in the unnormalised coordinate, and that (ii)
in producer form is RH.

## 2. Paper proofs

**Theorem A (Frobenius torsion law).** Suppose every zero coordinate `w(ρ)` is an algebraic
integer and the structure is *faithful*: every Galois conjugate of `w(ρ)` is `w(ρ')` for a zero
`ρ'`. Then RH is false. Consequently integrality, faithfulness, and the chamber's contractive
orientation are jointly contradictory.
*Proof.* Assume RH. Then every conjugate of `w(ρ)` is some `w(ρ')` and lies on the unit circle,
so by Kronecker's theorem `w(ρ)` is a root of unity, of some order `m(ρ)`. Distinct zeros have
distinct coordinates (the Arakelov map is injective), and `{z : z^m = 1}` is finite, so each
order occurs for finitely many zeros; Hardy's theorem gives infinitely many zeros, so infinitely
many orders occur. For an order `m ≥ 8` pick a totative `k` with `m ≤ 4k ≤ 3m` (`k = (m−1)/2`,
`m/2 − 1`, or `m/2 − 2` according to `m` mod 4); `z = exp(2πik/m)` is a primitive `m`-th root,
hence a conjugate of `w(ρ)` (the cyclotomic polynomial is the minimal polynomial), hence `w(ρ')`
for a zero `ρ' = 1/(1 − z)`; since `cos(2πk/m) ≤ 0`, `|1 − z| ≥ 1`, so `|ρ'| ≤ 1`. Distinct
orders give distinct `z`, hence distinct zeros in the closed unit disc; infinitely many zeros in
a compact set accumulate, and ξ, entire and not identically zero, cannot have an accumulating
zero set. ∎
*What it means.* Over `𝔽_q` Kronecker does not bite because `|α| = q^{1/2} ≠ 1`; the scale `q`
separates Frobenius from torsion. Over ξ the scale is `1`, and any Frobenius that is both
integral and unitary is torsion. The zeros of ξ are not torsion points in the Arakelov
coordinate (that would make every ordinate `½·cot(πk/m)`), so the F₁-Frobenius cannot carry
Weil–Deligne integrality in the normalised coordinate — and this is not a failure of RH: under
RH the structure is *more* impossible, not less.

**Theorem B (per-prime integrality bound).** For every nonreal `ρ`, at most two primes `p`
have `p^ρ` algebraic. *Proof.* For three primes the numbers `1, ρ` are ℚ-linearly independent
and `log p₁, log p₂, log p₃` are ℚ-linearly independent; the six exponentials
`e^{x_i y_j} ∈ {p_j, p_j^ρ}` cannot all be algebraic (six exponentials theorem, Lang–Ramachandra),
and the `p_j` are. ∎ So a Frobenius family `F_p` with eigenvalue `p^{ρ}` (Deninger's flow at time
`log p`, Connes' scaling by the idele of norm `p`) cannot be integral at three primes; the full
flow at all rational times has no finite-rank integral sublattice containing a mode.

**Theorem C (the two integralities exclude each other).** If `p^ρ` is algebraic for one `p ≥ 2`
and `ρ` is nonreal, then `ρ` is transcendental, hence `w(ρ)` is transcendental. *Proof.*
Gelfond–Schneider with base `p` and exponent `ρ` (irrational because nonreal); the Arakelov
coordinate is algebraic iff `ρ` is. ∎ (Lean: `not_isAlgebraic_arakelovW_of_nat_cpow_isAlgebraic`.)

**Theorem D (positivity cannot be produced below RH).** Weil's criterion makes positivity of the
explicit-formula form on all test functions equivalent to RH; the corpus's ledger ceilings
(C1–C4, Selberg ledger) show that positivity on any fixed aperture leaves every zero closer than
the crowd invisible; `GaussHodgeWeilSymmetryInsufficiency` shows the symmetry package alone
never sources it; `DeningerArithmeticSemisimpleHodge` shows that on the divisor carrier the
positive Hodge identification exists unconditionally and its Frobenius compatibility *is* RH.
Connes–Consani's semi-local positivity (archimedean place plus finitely many primes) is exactly
the finite-aperture form. Hence a "producer positivity" is either finite-aperture (blind) or
all-aperture (RH). There is nothing to construct that is not one of these two.

**Theorem E (what survives).** A Frobenius with the zeros as eigenvalues exists tautologically
(the graded carrier `XiZeroCopy →₀ ℂ` with Frobenius acting by the support eigenvalue; Lefschetz
numbers = Li coefficients = explicit-formula sums). Its only admissible integrality is not of
characteristic-polynomial type: it must be an integrality of the *test-function side* (integer
Lefschetz numbers such as `lcm(1..n) = e^{ψ(n)}`), whose content is the explicit formula itself
and carries no lower bound of type (iii).

## 3. Lean

| statement | declaration | status |
|---|---|---|
| Kronecker for an algebraic integer with unit-norm conjugates | `exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one` | proved |
| middle totative of every period `m ≥ 8` | `exists_middle_totative` | proved |
| `|1 − exp(2πik/m)| ≥ 1` for `m ≤ 4k ≤ 3m` | `one_le_norm_one_sub_exp` | proved |
| conjugates of a primitive root are the primitive roots | `exp_mem_rootSet_minpoly` | proved |
| ξ has infinitely many zeros | `xiZeros_infinite` | proved |
| RH ⇒ unitary coordinates | `xiArakelovUnitary_of_riemannHypothesis` | proved |
| **torsion law**: integral ∧ faithful ∧ unitary ⇒ False | `not_xiArakelovIntegral_faithful_unitary` | proved |
| integral ∧ faithful ⇒ ¬RH | `not_riemannHypothesis_of_xiArakelovIntegral_faithful` | proved |
| integral ∧ contractive ∧ faithful ⇒ False | `not_xiArakelovIntegral_contractive_faithful` | proved |
| `p^ρ` algebraic ⇒ `ρ`, `w(ρ)` transcendental | `not_isAlgebraic_of_nat_cpow_isAlgebraic`, `not_isAlgebraic_arakelovW_of_nat_cpow_isAlgebraic` | proved |
| six exponentials theorem; at most two of three primes with `p^ρ` algebraic | `SixExponentials.six_exponentials`, `SixExponentials.not_all_three_prime_cpow_isAlgebraic` | proved (`3-formalized/six-exponentials-lean.md`) |

Module `GaloisForLFunctions.RHTower.FrobeniusTorsionLaw`, wired into `RHTower`, axioms
`propext, Classical.choice, Quot.sound`.

## No-go closure
- **Exact killing theorem/mechanism:** Theorem A (Kronecker + middle totative + accumulation)
  for normalised integrality; six exponentials for per-prime integrality at three primes;
  Gelfond–Schneider for the mutual exclusion; Weil's criterion + ledger ceilings for positivity.
- **Strongest positive survivor:** `RHTower.FrobeniusTorsionLaw`; the reading that the
  `q = 1` scale is what turns Weil's mechanism into torsion over ξ.
- **New insight:** Weil–Deligne integrality is not merely absent over ℚ; in the normalised
  coordinate it is *incompatible with RH*, and in the unnormalised coordinate it is
  incompatible with three primes. The F₁-door must be built without characteristic polynomials.
- **Status:** closed for characteristic-polynomial integrality; every Lean item closed.

## Log
- 2026-09-02 — created; paper proofs A–E; Lean module built and wired.
- 2026-09-02 — six exponentials theorem and the prime corollary formalized; Theorem B now Lean-certified.
