# Hedenmalm--theta Möbius prime-cell parity-fibre chirality no-go

- **ID:** P-G53
- **Stage:** 1-in-progress
- **Type:** NO-GO THEOREM (paper) + LEAN SOURCE-CLEAN
- **Source:** P-G52 parity reporter; `EulerSquarefreeDyadicFockLocal`; existing source-horizontal fibre-balanced KL producer socket
- **Statement:** Canonical valuation-parity observer has a doubled-parameter hidden KL chirality with same strict orientation, vanishing only at Route-P saturation.

## Goal

Test most direct exact-sufficiency producer suggested by P-G52: use canonical geometric-valuation
source, parity as Boolean observer, and source reversal to instantiate existing fibre-balanced KL
selection theorem.  Compute hidden directed information before asserting sufficiency.

## Gates

- [x] 0 → 1 in-progress: exact geometric exponential-family chirality and parity split fixed
- [x] 1 → 2 fully-proven: dyadic information chain, sign, and equality classification
- [ ] 2 → 3 formalized: umbrella build, lint, and axiom audit green
- [ ] 3 → 4 publication-ready: merge with P-G52 exposition and external novelty audit

## Geometric chirality `[PROVED HERE]`

For negative geometric natural parameter `x`, let

\[
 A_B(x)=-\log(1-e^x),\qquad
 m_B(x)=\frac{e^x}{1-e^x},\qquad
 V_B(x)=\frac{e^x}{(1-e^x)^2}.
\]

For endpoint parameters `c+s,c-s<0`, geometric directed KL chirality is

\[
 \chi_B(c,s)
 =2s\bigl(m_B(c+s)+m_B(c-s)\bigr)
  -2\bigl(A_B(c+s)-A_B(c-s)\bigr).
\tag{1}
\]

Lean proves `A_B'=m_B`, `m_B'=V_B`, and `V_B` is strictly increasing on `(-∞,0)`.  Hence

\[
 \boxed{\chi_B(c,s)=0\iff s=0\qquad(|s|<-c).}
\tag{P-G53a}
\]

## Exact hidden-fibre split `[PROVED HERE]`

Corpus parity/residual factorization sends geometric exponent `K` to independent
`(K mod 2, floor(K/2))`; parity is Bernoulli/Fermi with natural parameter `x`, while residual is
geometric with parameter `2x`.  Partition and mean identities are

\[
 A_B(x)=A_F(x)+A_B(2x),\qquad
 m_B(x)=m_F(x)+2m_B(2x).
\tag{2}
\]

Substitution into `(1)` yields exact KL chain decomposition

\[
 \boxed{
 \chi_B(c,s)=\chi_F(c,s)+\chi_B(2c,2s).
 }
\tag{P-G53b}
\]

Here `χ_F` is exact Bernoulli chirality used by existing
`SourceHorizontalAdaptiveFisherChiralitySelection`.  Therefore canonical parity hidden-fibre
chirality is

\[
 \chi_{\rm fibre}(c,s)=\chi_B(2c,2s),
\]

and

\[
 \boxed{\chi_{\rm fibre}(c,s)=0\iff s=0.}
\tag{P-G53c}
\]

For `s>0`, `χ_fibre>0` and `χ_B>χ_F`: hidden information has same orientation as visible parity
information.

## Conjecture loop verdict

### Conjecture P-G53.A

Canonical valuation parity may itself provide fibre-balanced Boolean observer required by existing
source-reversal producer.

**Killed.** Off-center hidden residual chirality is strictly nonzero and reinforces visible
chirality.  Declaring parity sufficient would assume saturation through `(P-G53c)`.

### Strongest positive survivor

P-G52 exact-sufficiency gap now has directed-information orientation: discarded dyadic valuation
is not neutral noise.  It carries same horizontal chirality recursively at doubled rate.  This
explains both Hellinger strictness and failure of naive KL recovery as shadows of one dyadic
information flow.

### New insight

Missing observer cannot be bare valuation parity or any construction that leaves residual
geometric fibre unchanged.  Viable source law must act on residual dyadic tower and create an
opposite conditional orientation before Boolean scalarization.  Asymptotic disappearance of higher
digits is insufficient because existing producer requires exact fibre balance.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellParityFibreChiralityNoGo.lean
```

Key declarations:

- `sourceHorizontalHasDerivAt_boseLogPartition`;
- `sourceHorizontalHasDerivAt_boseMean`;
- `sourceHorizontalBoseVariance_strictMonoOn_neg`;
- `sourceHorizontalCenteredGeometricKLChirality_eq_zero_iff`;
- `sourceHorizontalBoseLogPartition_dyadic_split`;
- `sourceHorizontalBoseMean_dyadic_split`;
- `sourceHorizontalCenteredGeometricKLChirality_dyadic_split`;
- `sourceHorizontalParityFibreKLChirality_eq_zero_iff`;
- `sourceHorizontalParityFibreKLChirality_pos`;
- `sourceHorizontalGeometricKLChirality_gt_parity`.

The probability meaning of `(P-G53b)` uses already formalized parity/residual product
factorization; this module formalizes exact exponential-family chain identity and sign
classification.  It adds no sufficiency assumption.

## Next hard gate

Search actual Gamma/co-Poisson action on residual dyadic tower for orientation reversal.  Required
candidate must transform `χ_B(2c,2s)` to its negative or an exact coboundary without depending on
Xi zero locations.  Kill fixed scalar damping immediately: positive Markov post-processing cannot
reverse directed fibre orientation.

## Log

- 2026-08-12 — proved geometric KL chirality rigidity, exact parity/residual chain split, and
  canonical parity fibre-balance no-go.
