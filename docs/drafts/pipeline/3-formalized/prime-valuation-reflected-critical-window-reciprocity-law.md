# Reflected prime-valuation critical-window reciprocity law

- **ID:** `prime-valuation-reflected-critical-window-reciprocity-law`
- **Stage:** 3-formalized
- **Type:** EXACT CRITICAL-WINDOW LAW / SOURCE RECIPROCITY
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [LITERATURE-AUDITED] [NOT RH]`
- **Formal modules:**
  - `formal/GaloisForLFunctions/RHTower/PrimeValuationReflectedHellingerCriticalProfile.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeClockCriticalProfile.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeBoundaryWickCriticalProfileUniversalityLaw.lean`
- **Publication target:**
  - `docs/drafts/pipeline/4-publication-ready/riemann-divisor-prime-transfer-spectrum/main.tex`

## Theorem

For
\[
\mu_{p,\varepsilon}(k)
=(1-p^{-1+2\varepsilon})p^{-k(1-2\varepsilon)}
\]
and the reflected finite-prime Hellinger affinity
\[
\mathcal R_N(c)=
\prod_{p\le N}\sum_{k\ge0}
\sqrt{\mu_{p,c/\log N}(k)\mu_{p,-c/\log N}(k)},
\]
the exact local squared factor is
\[
1-
\frac{4p^{-1}\sinh^2(c\log p/\log N)}{(1-p^{-1})^2}.
\]
For every real \(c\),
\[
\mathcal R_N(c)^2\longrightarrow e^{-\Phi(c)},\qquad
\Phi(c)=4\int_0^1\frac{\sinh^2(cu)}u\,du.
\]

The symmetric prime-log Poisson cumulant
\[
K_N(z)=\sum_{p\le N}\frac{2(\cosh(z\log p)-1)}p
\]
satisfies
\[
K_N(2c/\log N)\longrightarrow\Phi(c),\qquad
\mathcal R_N(c)^2e^{K_N(2c/\log N)}\longrightarrow1.
\]

Thus reflected Hellinger loss and prime-clock fluctuation are two exact representations of one
critical-window action.

## Outer type law

The fixed-displacement law in
`prime-valuation-reflection-type-conservation-law.md` is the oriented outer regime:
\[
c<0:\ A_N(c)=\Theta(a_N^{1/2}),\qquad
c=0:\ A_N(c)=1,\qquad
c>0:\ A(c)\in\mathfrak F_\infty(a).
\]
The two off-line faces are not unequal finite grades. One is half-normal; the other is flat
beyond every finite Rees order. The all-orders-flat radical is preserved by every bounded
operator family whose full norm has fixed finite Rees order, in arbitrary dimension. More
sharply, every exact sewing family has norm dominating every inverse Rees power.

## Novelty boundary

The weak limit
\[
\frac1{\log N}\sum_{p\le N}\frac{\log p}{p}
f\!\left(\frac{\log p}{\log N}\right)\to\int_0^1f(u)\,du
\]
is a standard weighted Mertens test-function argument. In particular, Jana, *Math. Ann.* 380
(2021), Lemma 5.2, uses the same Stieltjes mechanism. No novelty is claimed for that engine or
for \(\Phi\) viewed only as its hyperbolic test function.

Candidate novelty is the exact reflected Hellinger defect, its product limit, the
Hellinger--Wick reciprocal identity, and its connection to the independently proved
half-normal/all-orders-flat type fracture and signed Fisher--Ward orientation carrier.

## Scope

- No zero exclusion is claimed.
- “Universal” is restricted to cutoff scaling and the two source representations for the
  rational-prime valuation family.
- The theorem does not assert that every zeta functional-equation lift is finite-Rees-moderate.
- Formal verification controls truth only and contributes no novelty or significance.
