# Actual Liouville short Fourier sums

- **ID:** twin-prime-short-fourier-formalization
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION TARGET
- **Source:** [growing affine cancellation](../2-fully-proven/twin-prime-polylogarithmic-affine-cancellation.md).

## Exact certificate required

Prove an absolute constant `C>0` such that, for natural `h0,m`,
`H=h0+10`, `N=H+m`, and every real frequency `alpha`,

```text
sum_(x=0..N-1) |sum_(n=x+1..x+H) lambda(n) exp(2*pi*i*alpha*n)|
 <= C N H [log(log H)/log H + (log N)^(-1/700)].
```

The frequency is fixed across the outer sum. No analytic input
may be placed in a binder, structure, typeclass, or imported axiom.
Keep every directly related Lean declaration in `twin-prime/`.

## Source audit and actual remaining work

[Matomäki--Radziwiłł--Tao, Theorem 1.3](https://arxiv.org/pdf/1503.05121v3)
states the corresponding integral estimate. Integer interval lengths
make its integrand constant between consecutive integer endpoints,
giving the displayed discrete target.

Inspected: Theorems 1.3/1.7, (1.12), the Proposition 2.4 reduction,
parts of §§3--4, and Appendix A's principal statements. The full
proof and its dependencies are not yet audited here.

Required proof components include:

- Conductor- and height-uniform Liouville nonpretentiousness, (1.12).
- Complex mean-square estimates, Appendix A.
- Minor-arc decomposition, prime energy and frequency counting, §3.
- Major-arc character and interval estimates, §4.
- Factorization-complement and endpoint costs.

The current plain Möbius window theorem does not supply this
frequency-uniform quantitative conclusion. Search results must be
checked at their actual statements before reuse.

Corpus checks: `DirichletTwistDistanceStability` proves exact
transport of the distance under character multiplication, with
no lower bound for the actual twisted Liouville row.
`AffineMeanSquareL1` supplies a general first-moment bound but
no required small error. `MoebiusDistanceAllFreq` applies to
prime values identically `-1`; a nonprincipal character changes
those values. None discharges the character-uniform input.

The subsequent exact lexical searches `Dirichlet Korobov` and
`Dirichlet zeroFree` found no applicable quantitative theorem.
The semantic search timed out and supplies no absence evidence.
The later major-arc audit covered the argument after (4.4).
Appendix A has now been read through its conclusion. Its cited
inputs and the full ancestral proof chain still require audit.

Two points now constrain the implementation:

- The mean-square application has a minimum window length.
  Its partial-summation integral extends to zero, so that range
  needs a separate payment. The complete elementary proof is on
  the [short-window endpoint card](../3-formalized/twin-prime-short-fourier-endpoint.md),
  now fully formalized in Lean with fifteen standard-foundation axiom audits.
- A sufficiently large actual twisted distance makes Appendix
  A's near-minimizing-frequency set empty. This could remove
  the near-resonant branch for `lambda*chi`, but only after
  proving the conductor-uniform distance lower bound. The
  distance cannot be supplied as an assumption.

The new corpus file
`BezoutValuationIncidence/BilinearDispersionOfTheActualRowsAndTailSummation.lean`
was checked at `eventually_abs_rowBilinear_moebiusWindowRow_tail_summed_le`
and `eventually_moebiusWindowRow_pure_largeSieve_le`.
Their left sides retain explicit mean and beta compensators.
They are actual compensated incidence estimates, but do not
provide the twisted Liouville short Fourier estimate here.
The checked Dirichlet lower-bound hits apply far to the right
of the critical strip; the uniform Riemann--von Mangoldt hits
are zero counts, not the required near-one estimate.
These are scoped statement audits, not a corpus-wide absence claim.

Continue with the precise character-uniform analytic input and
the large-distance branch of Appendix A. Do not replace either
by a transported-distance identity or a cancellation assumption.

The subsequent import audit located actual Dirichlet logarithmic-strip,
reciprocal and Siegel theorems. Their precise constants, usable ranges
and remaining gaps are recorded on the
[character-uniform distance card](twin-prime-character-uniform-nonpretentiousness.md).
In particular, an existing logarithmic strip is not the stronger
high-frequency bound required by the full argument.

## Gates

- [x] Concrete actual-row target; frequency placement fixed.
- [ ] Complete dependency audit and paper proof for the selected implementation.
- [ ] Lean proofs of every arithmetic and analytic input.
- [ ] Foreground leaf check, transitive axiom audit and umbrella wiring.

## Log

- 2026-10-24 — Recorded the next analytic certificate while
  completing the finite squarefree transfers. Twin-prime
  infinitude remains the main, unmet completion condition.
