# Bi-Scale Uncertainty

Bi-Scale Uncertainty studies what happens when one source must satisfy both
**logarithmic arithmetic sampling** and **archimedean energy constraints**.
The integers become nodes $\log n$, whose spacing shrinks like $1/n$; the poles
and Gamma factor impose hyperbolic weights on the same line. Their interaction
sets the cost of imposing zeros, correlations and cancellations on a source.

The programme has two connected aims: compute sharp uncertainty laws for
these constraints, and turn signed prime–polar discrepancy into measurable
energies. The first supplies geometry and counterexamples. The second supplies
receivers whose critical bounds would imply RH.

## Objects and language

For a real source $f$, let

$$
h_f(t)=\int_{\mathbb R}f(x)f(x+t)\,dx,
\qquad
\mathcal J(f)=\int_0^\infty
 [h_f(0)-h_f(t)]\frac{e^{t/2}}{\sinh t}\,dt.
$$

The autocorrelation is positive definite, $h_f(0)=\|f\|_2^2$, and its increment
is half the squared translation distance. The weight behaves like $1/t$ near
zero and $2e^{-t/2}$ at infinity. Thus $\mathcal J$ measures translation
regularity without requiring a spectral second moment.

A source is **blind on a node set** when $h_f(\log n)=0$ at those nodes.
**Polar balance** means its hyperbolically weighted correlation has zero
integral. The uncertainty problem asks how small $\mathcal J(f)/\|f\|_2^2$ can
be under these constraints. On prime-power-blind, polar-balanced sources,
the complete Weil sign becomes exactly an archimedean energy floor.

The signed measure behind the analytic receiver is the difference between
prime-power atoms $\Lambda(n)n^{-1/2}\delta_{\log n}$ and the polar density
$2\cosh(t/2)\,dt$, truncated at a common horizon. A **packet** probes this
measure with translated sources; a **band** reads its Fourier energy on a
specified frequency interval. Both retain the subtraction before estimating.

Finite divisor signals form a second laboratory. Their translated moments
on a complete period are **observations**: the questions are what they recover,
which symmetries they miss, and how stable the recovery is.

## Foundational mechanisms

**Krein increment geometry.** The inequality

$$
(h_f(x)-h_f(y))^2
\le 2h_f(0)\,[h_f(0)-h_f(x-y)]
$$

turns the Lévy energy into a budget for moving correlations across shrinking
logarithmic cells. It is the basic tool for rough sources and arithmetic cusps.

**Folded symbols and node criticality.** On power grids, folding the spectral
measure reduces the uncertainty problem to an exact moment problem. This
computes slacks and completion costs rather than estimating each node
separately. For the full zero-pole positivity criterion, every prime-power node
is necessary: deleting $\log4$ has a nonzero arithmetic price, whereas adding
or deleting the non-prime-power node $\log6$ does not. The full criterion still
contains RH; node classification does not prove its floor.

**Band and packet laws.** With $\psi$ the Chebyshev function, the energy

$$
\int_0^L[e^{-t/2}(\psi(e^t)-e^t)]^2\,dt
$$

is equivalent, at the stated normalizations, to a signed-measure Gram energy
and to a critical-line Dirichlet band energy. Its linear bound is an RH
criterion. Packet expansions identify which zeros a probe sees and retain
multiplicity and mixed terms when packets overlap.

**An attained endpoint for the integrated deficit.** Put

$$
I(T)=e^{-T/2}\int_0^T(e^t-\psi(e^t))\,dt,
\qquad \Delta=\sup_\rho|\Re\rho-1/2|.
$$

Its reciprocal-square zero expansion gives $|I(T)|\le B e^{\Delta T}$ with
one constant. The admissible absolute growth rates are exactly $[\Delta,\infty)$;
boundedness is equivalent to RH. Under RH its mean-square limit involves
$\sum m_\rho^2/|\rho|^4$, unlike the reciprocal-square energy of the
unintegrated Chebyshev error. See
[WeilLagCriticalDeficitEndpointAndLimitLaw](WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

**Observation and completion.** Finite moments can recover divisor signals,
but complete-period magnitudes can lose arithmetic phase. Conversely, suitable
summed phase-sensitive receivers distinguish sources with identical extremal
sizes. Pole-free sources and coherent packets supply useful completion tools;
the fixed single-scale construction has a logarithmic cost obstruction.

## Research questions

- Which arithmetic estimate bounds the actual signed band or packet at its
  critical rate, or lowers its exponential growth rate?
- Can a source-derived uncertainty slack survive growing aperture and the
  entrance of new prime-power nodes?
- Which multiscale completion controls both its own energy and the cost of
  transferring to the desired receiver?
- Which finite observations retain the phase information needed for those
  bounds at a usable, uniform conditioning cost?

The main traps are separating prime and polar sizes before cancellation,
confusing complete-period recovery with short-window control, and treating a
sharp receiver dictionary as an estimate on its input. A fixed probe can also
be blind to zeros; visibility hypotheses belong in every rate claim.

## Place in the wider research

[Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md)
constructs exact factorial sources and transfers their complete energies.
[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) and
[Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md)
move observations from full periods to finite windows and arithmetic receivers.
[Square-Root Threshold](../SquareRootThreshold/README.md) studies the aperture
needed to detect the zeros these observations can miss.
[Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md)
abstracts their information limits.

The [programme umbrella](../BiScaleUncertainty.lean) maps the modules. Start
with correlation geometry, then the band/packet receiver; use folded-symbol
and observation results for the particular constraint or source under study.
