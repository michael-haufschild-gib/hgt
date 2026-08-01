# Deninger two-prime Kummer dense/nonclosed range

**Status:** fully proved on paper; Lean formalization pending  
**Route:** `L`  
**Exact label:** `DAC_TWO_PRIME_KUMMER_DENSE_NONCLOSED_RANGE`  
**Positive survivor:** `DAC_KUMMER_REDUCED_UNREDUCED_COHOMOLOGY_DICHOTOMY`

## Claim

Let

\[
  v=(\log 2,\log 3)\subset\mathbf R\subset\mathbf C,
  \qquad L=\mathbf Z\log2+\mathbf Z\log3.
\]

Index the Hilbert space `\mathcal H=\ell^2(L\setminus\{0\})` by nonzero signed two-prime Kummer
frequencies.  Define the bounded transform of the phase generator by

\[
  (Bf)(\mu)=b(\mu)f(\mu),
  \qquad b(\mu)=\frac{\mu}{1+|\mu|}.                           \tag{1}
\]

Then, unconditionally:

1. `B` is a bounded injective contraction;
2. `\operatorname{ran}B` is dense in `\mathcal H`;
3. `\operatorname{ran}B` is not closed;
4. every finite nonzero modal truncation of `B` is bijective;
5. no bounded inverse or bounded Kummer Green contraction exists on `\mathcal H`.

Consequently

\[
 H^1_{\mathrm{alg}}=\mathcal H/\operatorname{ran}B\ne0
 \quad\text{but is non-Hausdorff},                            \tag{2}
\]

whereas reduced Hilbert cohomology is

\[
 \overline H^1
 =\mathcal H/\overline{\operatorname{ran}B}=0.                \tag{3}
\]

Pure two-prime Kummer small-divisor cokernel therefore cannot be the nonzero separated positive
Hodge space demanded by Route L.

## Proof

The ratio `\log3/\log2` is irrational: a rational ratio would give a nontrivial integer relation
between `\log2` and `\log3`, contradicting unique factorization.  Thus the pair is
`\mathbf Q`-linearly independent.  It is `\mathbf R`-linearly dependent because both periods lie on
the real line.  The integer span of a rationally independent but real-dependent pair is
nondiscrete.  Hence there are nonzero `\mu_n\in L` with `\mu_n\to0`.

For every nonzero `\mu`, `b(\mu)\ne0` and `|b(\mu)|\le1`, proving boundedness and injectivity.
Every coordinate vector `e_\mu` belongs to the range because

\[
 e_\mu=B\bigl(b(\mu)^{-1}e_\mu\bigr).
\]

Finite-support vectors are dense in `\ell^2`, so the range is dense.

On the unit vectors `e_{\mu_n}`,

\[
 \|Be_{\mu_n}\|=|b(\mu_n)|\longrightarrow0.                  \tag{4}
\]

If the injective range were closed, the inverse from the range to `\mathcal H` would be bounded;
`(4)` would then force `e_{\mu_n}\to0`, contradicting their unit norm.  Thus the range is not
closed.  A finite diagonal matrix with nonzero entries is bijective, proving item 4.  Items
`(2)`--`(3)` follow from dense nonclosed range.

## Hostile audit

- **No fake global class.** Algebraic quotient is explicitly non-Hausdorff; it is not promoted to a
  Hilbert Hodge space.
- **No finite-stage fallacy.** Every finite truncation is exact; obstruction exists only after the
  cofinal Hilbert completion.
- **No cup/inverse conflation.** Normalized cup remains bounded by
  `DAC_KUMMER_NORMALIZED_CUP_SMALL_DIVISOR_CANCELLATION`; only inverse/contraction fails.
- **No RH premise.** Result depends only on two prime logarithms and Hilbert topology.
- **Positive salvage.** Exact reduced/unreduced dichotomy localizes what a viable relative complex
  must change: domain, boundary condition, or cross-sector incidence—not scalar completion.

## Collision and novelty audit

Internal `PeriodIncidenceMultiplier.lean` proves a general discrete/nondiscrete range dichotomy for
a regularized period multiplier on `\ell^\infty`.  `SeamSpectrumDensity.lean` proves prime-log
gaplessness.  Internal Kummer files construct the `\ell^2` phase generator and its bounded
multipliers.  Search found no arithmetic two-prime `\ell^2` instantiation, no dense-range theorem
for nonvanishing Deninger multipliers, and no reduced/unreduced Route-L conclusion `(2)`--`(3)`.

New knowledge is the exact Hilbert-complex diagnosis.  General facts about diagonal operators are
not claimed as new.

## Formalization target

Formalize unconditionally:

1. injectivity, coordinate action, and dense range of a nonvanishing diagonal `\ell^2` multiplier;
2. nonclosed range from unit coordinate vectors whose weights tend to zero;
3. rational independence and real dependence of `(\log2,\log3)`;
4. arithmetic bounded-transform dense/nonclosed range and a closure-only witness.

## Route-L effect

Retire the claim that raw Kummer small-divisor cokernel itself supplies global positive `H^1`.
Surviving hard claim:

`[CONJECTURE] DAC_RELATIVE_KUMMER_MILNOR_REDUCED_COHOMOLOGY`:

> construct a relative-domain/cross-sector complex whose reduced cohomology is nonzero and whose
> bounded normalized cup descends nondegenerately; prove this cohomology agrees with Paugam/Meyer
> `H^1` under Cauchy and residue transition maps.

This remains a genuine construction problem, not a closure convention.
