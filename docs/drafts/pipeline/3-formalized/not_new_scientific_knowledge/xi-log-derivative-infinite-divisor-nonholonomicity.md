# Xi logarithmic derivative: infinite-divisor non-holonomicity

- **ID:** `xi-log-derivative-infinite-divisor-nonholonomicity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / route-boundary certificate
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean files:**
  - `formal/GaloisForLFunctions/HTGeometry/PoleHolonomicDegreeBudget.lean`
  - `formal/GaloisForLFunctions/RHTower/XiZerosInfinite.lean`
  - `formal/GaloisForLFunctions/RHTower/XiLogDerivNonholonomic.lean`
  - `formal/GaloisForLFunctions/RHTower/FiniteSpectralTraceNoGo.lean`
- **Lane:** general infinite-divisor obstruction; completed-zeta logarithmic carrier

## Statement

The global divisor support of the actual completed Riemann zeta function `xi` is infinite:

```lean
theorem xiDivisorSupport_infinite :
    (MeromorphicOn.divisor xi Set.univ).support.Infinite
```

At every actual zero `rho`, the logarithmic derivative has a genuine simple pole, independently of
the multiplicity of the zero:

```lean
theorem meromorphicOrderAt_logDeriv_xi_eq_neg_one {ρ : ℂ} (hzero : xi ρ = 0) :
    meromorphicOrderAt (logDeriv xi) ρ = ((-1 : ℤ) : WithTop ℤ)
```

Consequently `xi'/xi` is not holonomic.  Every global polynomial-coefficient linear differential
relation is trivial:

```lean
theorem xi_logDeriv_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ Finset.range (n + 1),
      (c j).eval s * iteratedDeriv j (logDeriv xi) s = 0) →
    ∀ j ∈ Finset.range (n + 1), c j = 0
```

The finite form is quantitative.  If a meromorphic approximant has genuine simple poles at the
first `N` chosen actual `xi` zeros and satisfies a polynomial-coefficient linear ODE with nonzero
leading coefficient `c_n`, then

```lean
theorem xiZeroPacket_linear_top_natDegree_ge ... :
    N ≤ (c n).natDegree
```

This bound is independent of differential order: more derivatives do not buy additional divisor
capacity.  Every captured simple pole costs one degree in the leading coefficient.

## Paper mechanism

The proof uses no imported assertion that `xi` has infinitely many zeros.  The exact Hadamard
factorization already formalized in the project writes the centered `XiC` as a nonzero constant
times the genus-one canonical product over its actual divisor.  If that divisor were finite, the
functional-equation involution would pair centered zeros `a` and `-a`; hence the sum of reciprocal
locations would vanish and all exponential corrections in the finite genus-one product would
cancel.  `XiC` would therefore be a nonzero polynomial.

On the horizontal line `z=n-(5/2)i`, this polynomial equals `xi(3+ni)` up to its fixed nonzero
constant.  The formal theorem `xi_vertical_decay` gives `|xi(3+ni)| -> 0`.  A nonzero polynomial is
either a nonzero constant or tends to infinity in norm along the natural numbers.  Both alternatives
contradict decay.  Thus the divisor support is infinite.

If `xi` has order `m>=1` at `rho`, its derivative has order `m-1`; therefore `(xi'/xi)` has
meromorphic order `(m-1)-m=-1`.  Choosing an injective sequence of distinct divisor points feeds
these simple poles into the already formalized general pole-domination theorem
`GaloisForLFunctions.not_holonomic_of_meromorphic_simplePoles`.  At differential order `n`, multiply
a proposed relation by `(s-rho)^(n+1)` and approach a pole outside the zero set of its leading
polynomial.  Only the top derivative survives, forcing the leading polynomial to have infinitely
many roots.  Descending induction kills every coefficient.

For a finite pole packet, the same limit proves that the leading polynomial vanishes at every
packet point.  Its distinct-root count is bounded by its degree.  The intrinsic meromorphic wrapper
extracts the local pole factors directly from `meromorphicOrderAt f p = -1`, giving the finite-pole
coefficient-degree budget without assuming a particular pole geometry.

## Exact route consequences

This theorem does not invalidate any RH-equivalent criterion.  It excludes implementations only
when they require the actual completed logarithmic carrier to be holonomic.

1. **Li / Keiper coefficients.**  The Li generating function is a rational Möbius pullback and
   rational multiple of `xi'/xi`.  D-finite functions are closed under rational pullback and
   rational multiplication.  Hence a closed P-recursive recurrence for the entire Li sequence
   would make `xi'/xi` holonomic, contradicting the theorem.  The rational-pullback closure step is
   proved on paper in
   `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius-logarithmic-jet-ht-transfer-li-no-holonomic-route.md`;
   it is not yet a Lean theorem.
2. **Finite-dimensional Hilbert--Pólya models.**  A finite matrix characteristic determinant has a
   finite atomic logarithmic derivative.  Lean theorem
   `xi_logDeriv_ne_finiteSpectralTrace` now proves directly that no finite support with arbitrary
   complex multiplicity weights can equal `xi'/xi`.  Infinite unbounded self-adjoint operator
   models are not excluded.  A holonomic spectral approximant reproducing `N` actual poles needs
   leading ODE coefficient degree at least `N`.
3. **Finite-rank Connes trace carriers.**  Any realization whose completed spectral trace closes to
   a finite holonomic carrier cannot reproduce the actual divisor.  Infinite noncommutative trace
   formulas are not excluded; fixed coefficient degree cannot stabilize along an unbounded divisor
   exhaustion.
4. **Finite-dimensional de Branges/canonical systems.**  Finite transfer matrices and polynomial
   Hermite--Biehler determinants have holonomic logarithmic derivatives, so they cannot realize the
   completed divisor exactly.  A holonomic truncation matching `N` completed poles must spend
   leading coefficient degree at least `N`.  Infinite canonical systems are not excluded.
5. **Finite-state Weil-positivity readers.**  A reader that compresses the full explicit-formula
   carrier to a single holonomic generating function cannot be exact.  The full test-function
   positivity criterion is not excluded.
6. **Finite-state Nyman--Beurling certificates.**  The theorem excludes only certificates that first
   encode the completed divisor by a finite holonomic determinant or recurrence.  It does not
   exclude the genuine infinite-dimensional closure problem in `L^2(0,1)`.

The common wall is therefore precise:

> The actual completed divisor cannot pass through a finite holonomic logarithmic carrier.

## Gates

- [x] Paper proof: finite-divisor Hadamard collapse contradicts vertical decay.
- [x] Lean proof that the actual `xi` divisor support is infinite.
- [x] Lean proof that every actual zero produces a simple pole of `xi'/xi`.
- [x] Lean proof that `xi'/xi` satisfies no polynomial-coefficient linear ODE.
- [x] Lean proof of the general finite-pole coefficient-degree budget.
- [x] Lean specialization to approximants at finite packets of actual `xi` zeros.
- [x] Direct target-module builds pass.
- [x] Formal lint passes with no new `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- [x] `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] Formalize the Möbius pullback to obtain the Li-generator theorem itself in Lean.
- [x] Formalize the common finite atomic resolvent-trace corollary covering finite-dimensional
  matrix, finite-rank trace-carrier, and finite spectral-support implementations; see
  `finite-spectral-trace-xi-nogo.md`.
- [ ] Formalize any stronger named canonical-system corollary whose hypotheses are not already
  exactly a finite atomic resolvent trace.

## Scientific gate

The infinite-zero theorem and the pole-domination mechanism are classical in content.  The
formalization closes a real project gap and produces a useful common route boundary, but it is not
new scientific knowledge.  Its role is to give an unconditional stage-3 target for genuinely new
general HT laws without pretending that a finite surrogate is the actual zeta carrier.

## Log

- 2026-07-11 -- Proved the infinite actual `xi` divisor internally from Hadamard factorization,
  reflection pairing, and vertical decay.  Specialized the general simple-pole engine to prove
  unconditional non-holonomicity of `xi'/xi`; direct builds, lint, and axiom audit pass.
