# Arithmetic Positivity Theory

Arithmetic Positivity Theory asks how a literal arithmetic source can force the
sign of the **complete Weil form**. Its laboratory is a family of factorial and
Bernoulli sources whose prime weights, endpoint jumps and pole corrections are
explicit. The aim is to turn their arithmetic into estimates that remain useful
when sources are combined, approximated and passed to a limit.

The central distinction is between **a positive family** and **a family that
controls every test**. Large positive subspaces are known. Extending their sign
to the complete receiver requires an estimate on the approximation error and
mixed terms in the same energy. Density in an unrelated norm does not do this.

## Objects and language

For a source $f$ on the logarithmic line, write

$$
F_f(s)=\int_{\mathbb R}f(x)e^{(s-1/2)x}\,dx.
$$

With zeros counted by multiplicity, the absolute sampling mass and signed
Weil pairing are

$$
\mathcal Z(f)=\sum_\rho m_\rho|F_f(\rho)|^2,
\qquad
\mathcal W(f,g)=\sum_\rho m_\rho F_f(\rho)
                    \overline{F_g(1-\overline\rho)}.
$$

These sums are used only on their proved summability domain. Reflection in the
critical line gives the fundamental identity

$$
\mathcal Z(f)-\Re\mathcal W(f,f)
=\frac12\sum_\rho m_\rho
  |F_f(\rho)-F_f(1-\overline\rho)|^2.
$$

Thus positive square mass and positive Weil energy are different statements.
The former supplies the independent norm for controlling mixed terms.

On smooth compact sources, the explicit formula identifies $\Re\mathcal W(f,f)$
with **archimedean energy minus prime energy plus the two pole terms**. For a
real source, its autocorrelation $a_f(t)=\int f(x)f(x+t)\,dx$ exposes the prime
term as $2\sum_n\Lambda(n)n^{-1/2}a_f(\log n)$. The archimedean term contains
translation increments against the singular weight $e^{t/2}/\sinh t$.
Nonnegativity of the complete form on every compact test is the Weil criterion
for RH.

Keep three parameters separate: **arithmetic scale** of a factorial source,
**aperture** of its support, and **truncation** used to make a tail compact.
The critical rescaling removes a favourable high-scale archimedean gain and
reveals the arithmetic sign that must survive on its own.

## How the theory works

**Exact source construction.** Divisor identities and Bernoulli remainders
produce sources whose Mellin transforms and pole corrections are known.
Their jumps and shrinking collars are part of the source. Translation
increments, rather than uncontrolled derivatives, pay their regularity costs.

**Sampling and stability.** Absolute zero sampling has a logarithmic loss over
physical mass on the factorial tails. Estimates in $\mathcal Z$ then control
$\mathcal W(f,g)$ without assuming positivity of $\mathcal W$. Relative stability
and Schur-complement laws quantify how much error a positive source can tolerate.
This is the bridge needed before approximation can transfer a sign.

**The critical prime kernel.** The limiting prime kernel of the factorial
family is strictly negative, so its contribution to the Weil form is favourable.
The sign is uniform on suitable growing linear windows. Complete-form
positivity also holds on high-scale spans and specified polynomial or lacunary
windows. The different uniformities matter: a theorem for each fixed pattern
need not hold uniformly as its support grows.

**Compact receivers.** Grid-tent approximation transfers the complete form with
explicit error, and negative zero detectors can be approximated by these tests.
This makes the receiver concrete. It does not prove that the positive
factorial subfamilies approximate every detector at an affordable cost. See
[QuantitativeGridTentDetection](QuantitativeGridTentDetection.lean).

**Small-shift transport.** The Suzuki deficit has the complete Weil form as its
first variation. Common shifts are available on bounded-envelope families;
joint $L^2$ limits and moving apertures are controlled under the stated common
decay or approximation bounds. These theorems transport an existing floor.
See [CommonShiftForTheSuzukiDeficit](CommonShiftForTheSuzukiDeficit.lean) and
[SuzukiCriticalMovingAperture](../RHTower/Suzuki/SuzukiCriticalMovingAperture.lean).

## Sharp boundaries

The source-selection theorems recover prime coefficients and exclude nonzero
single-index perturbations of $\Lambda$ from the full Weil cone. Identification
of the actual source still leaves its sign to prove. Likewise, high-scale
positivity shared by tempered prime weights cannot alone distinguish $\zeta$
from the perturbations relevant to RH.

The spectral route has a concrete boundary. At Sonin cutoff $1$, trace
domination fails even after imposing both pole cancellations and any finite
list of continuous moment constraints. At each fixed cutoff above $1$, a
positive comparison survives on sufficiently separated finite packets with a
sufficiently narrow seed. Real-rooted full ground states also exist, but their
uniform Gaussian-growth or Poisson-balance bounds remain separate inputs.
These are the obstruction and usable survivor in
[SpectralRealisationAndOperatorConstraints](SpectralRealisationAndOperatorConstraints.lean).

## Research questions

- **Complete receiver transfer.** Which positive arithmetic families approximate
  arbitrary compact tests with mixed-energy and error costs controlled uniformly?
- **Critical prime cancellation.** Which signed estimate survives after the
  high-scale archimedean gain is removed, at arbitrary aperture?
- **Moving families.** Can Suzuki transport reach the critical correlation-decay
  boundary while preserving the prime–polar cancellation?
- **Positive realization.** Can arithmetic supply the uniform bounds needed by
  a spectral or ground-state construction, beyond real-rootedness and exact
  operator identities?

A useful answer specifies its source class, norm and uniform parameters. A
partial floor is meaningful: its exponential loss can bound zero width even
when it does not prove nonnegativity.

## Place in the wider research

[Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) supplies correlation
geometry; APT constructs and estimates literal sources within it.
[Square-Root Threshold](../SquareRootThreshold/README.md) supplies the detectors
that complete receiver transfer must reach.
[Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) studies
the same form through ground energy, while
[Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md)
seeks a direct allocation of its signed prime and pole costs.

Start with those interfaces and the mechanisms above. The
[programme umbrella](../ArithmeticPositivityTheory.lean) is the module map;
module docstrings contain the detailed constants and theorem statements.
