# Bézout–Valuation Incidence

Bézout–Valuation Incidence studies cancellation in **finite divisor rows on
windows much shorter than their period**. It asks what divisibility, prime-power
valuations and consecutive integers force before period orthogonality becomes
available. The desired output is a signed estimate for the actual Möbius or
prime source, with enough uniformity to control a growing arithmetic receiver.

The three words name concrete inputs. **Bézout** supplies coprimality across
$n,n+1$ and relations $pa-qb=1$. **Valuation** determines which prime-power
modes a lag can see. **Incidence** is the matrix $\mathbf1_{d\mid n}$ linking
moduli to positions. The programme reorganizes this matrix without erasing its
source coefficients or boundary terms.

## Objects and scales

For weights $c(d)$ supported on $1\le d\le N$, define

$$
s_{N,c}(k)=\sum_{d\le N,\ d\mid k}c(d),\qquad
Y_{N,c}(q)=\sum_{q\mid d\le N}\frac{c(d)}d.
$$

The $Y$ are **Selberg coordinates**. They are the coefficients in the finite
Ramanujan expansion of the response. The mean is $m_c=Y_{N,c}(1)$, and

$$
A_c(M)=\sum_{k\le M}(s_{N,c}(k)-m_c)
      =-\sum_{d\le N}c(d)\{M/d\}.
$$

The complete period is $\operatorname{lcm}(1,\ldots,N)$, exponentially large in
$N$. The interesting observation windows are polynomial in $N$. In this regime
moduli larger than the window contribute drift before producing a divisibility
event, and successor boundary terms can be as large as the main term.

The **pronic norm** is

$$
\|A\|_T^2=\sum_{n=1}^T\frac{A(n)^2}{n(n+1)}.
$$

It is the reciprocal-cell $L^2$ norm used by the analytic receiver. For
$c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$, use the full divisor response and
mean $1/\zeta(1+\varepsilon)$. Bounded pronic energy at positive dampings
accumulating at zero implies RH. Control at a fixed finite horizon does not
supply this quantifier.

## Foundational mechanisms

**Diagonalization with a window cost.** Selberg/Ramanujan coordinates diagonalize
complete-period forms. Window Poincaré and large-sieve laws quantify when that
information transfers to a shorter interval and what error survives at its
endpoints. The finite arithmetic does not require waiting for the full period.

**Successor polarization.** Coprimality of adjacent integers gives exact
energy identities and separates the receiver into diagonal, boundary and
signed interior contributions. Canonical compensation pays specified pieces;
the remaining Bézout interior term is the place where a new signed estimate is
needed. Treating the complete split as a positivity proof would omit that term.

**The residue Gram.** Products of sawtooth prefixes admit exact residue and
Bernoulli-kernel formulas. Cross-scale bilinear forms can consequently be
rewritten as single-modulus statistics of the large-scale row. This is a
useful reduction: it identifies where the actual Möbius or centred prime row
can outperform a generic coefficient bound.

**Readout–energy duality.** The approximation problem has a dual form: seek
rows with large von Mangoldt readout relative to centred energy. The uncertainty
law caps this squared ratio at logarithmic order in the cutoff. A divergent
ratio within that ceiling is meaningful; asking for faster-than-logarithmic
growth contradicts the known bound. See
[ReadoutEnergyUncertaintyPrinciple](ReadoutEnergyUncertaintyPrinciple.lean).

**Actual-source savings.** Short-window cancellation gives growing-modulus
improvements for Möbius and centred prime rows, including balanced estimates
with remainders summed. Root-of-unity minor-arc arguments give power savings
below the diagonal; balanced scales have subpower savings. Composite roots
require their own resonance terms. These distinctions are developed in
[TheCentredPrimeRowIsMinorArcBelowTheDiagonal](TheCentredPrimeRowIsMinorArcBelowTheDiagonal.lean)
and [MinorArcSumsAtCompositeRootsOfUnity](MinorArcSumsAtCompositeRootsOfUnity.lean).
A power saving in the specified short-window mean square at some fixed power
length is equivalent to a fixed zero-free strip; a qualitative saving is weaker.

## Research questions

- Can the signed interior energy be bounded uniformly in horizon at a fixed
  damping below $1/2$?
- Which actual-row dual-norm estimate assembles across all relevant moduli and
  scales into that receiver bound?
- Can one explicitly construct dual rows whose readout-to-energy ratio tends
  to infinity, respecting the logarithmic ceiling?
- Can successor or mixed valuation information improve the signed estimate at
  balanced scales, where generic large-sieve bounds leave the critical cost?

The tools sought are quantitative: an interior contraction, a usable dual row,
or a mixed bilinear estimate with every remainder paid. Exact recovery of a
row and an exact Gram formula are foundations for those tools, not substitutes.

## Place in the wider research

[Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) supplies full-period
observations; BVI prices their finite windows.
[Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md)
asks what happens beyond the coefficient cutoff and through receiver transfer.
[Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md)
uses the pronic receiver as a function of damping.
[Signed Successor Arithmetic](../SignedSuccessorArithmetic/README.md) develops
new additive–multiplicative source constraints, while
[Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) studies the
states that could escape the existing energy bounds.

Begin with the row, its mean and its norm; then choose the appropriate window
or Gram theorem. The [programme umbrella](../BezoutValuationIncidence.lean)
provides the detailed module map.
