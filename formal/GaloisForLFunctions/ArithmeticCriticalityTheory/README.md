# Arithmetic Criticality Theory

Arithmetic Criticality Theory studies the Weil sign problem through **jump
operators, ground states and gauges**. Its question is whether arithmetic can
supply a certificate for a form whose coefficients have no spare positive
margin. A useful gauge must expose a payable signed remainder; changing the
representation alone does not change the sign.

The programme connects a local existence problem—constructing a suitable
supersolution—to a global one: controlling the lowest Weil energy as the
support aperture grows.

## Objects and language

Let $\Theta$ be the positive, even Riemann kernel whose Fourier transform is
$\Xi$. In theta coordinates a test is $F=\Theta v$. The associated
Schrödinger-type form is

$$
Q(v)=E_{\rm arch}(v)+E_{\rm prime}(v)
      -\int\Theta(x)\cosh(x/2)v(x)^2\,dx.
$$

The two energies measure squared differences across continuous archimedean
jumps and jumps of length $\log n$ with weight $\Lambda(n)n^{-1/2}$. The
potential comes from the pole. Nonnegativity on all odd compact tests is an
RH criterion. The parity restriction matters: the unrestricted Markov form
has an adverse even direction.

A **gauge** $\omega$ writes $v=\omega u$; its test coordinate is
$M=\Theta\omega$. A ground-state representation expresses the original form
as a jump energy in $u$ plus the gauge's source term. A **supersolution** has a
source of the sign needed to certify positivity. Folding an odd test onto the
half-line produces signed conductances, so positivity results for ordinary
nonnegative-conductance graphs do not automatically apply.

A nonnegative form is **critical** if no nonzero nonnegative Hardy weight can
be subtracted while preserving its sign. A negative test makes it
**supercritical**. A **null sequence** rules out a positive improvement, but
does not by itself prove that the original form is nonnegative.

For the complete Weil form on tests supported in $[-A,A]$, write

$$
\mu(A)=\inf_{F\ne0}\frac{\Re\mathcal W(F,F)}{\|F\|_2^2}.
$$

The infimum is taken on the stated form domain. This is the **ground-energy
path**; it differs from a floor normalized by a derivative or archimedean norm.

## Foundational mechanisms

**Ground-state identities and moment obstructions.** Translated and smeared
theta gauges have explicit sources. The two-moment law excludes positive
half-line supersolutions in the specified decaying profile class. Its positive
content is an exact description of the remaining signed source, which directs
the problem towards sign-changing gauges and compensation.

**The gauge-independent zero form.** Subtracting the pole isolates a form whose
theta span is radical. In a gauge it becomes signed jump energy plus a precisely
calibrated variance. Null families show why removing a prime contribution or
losing part of that variance can destroy the intended inequality. The open
quotient problem is a coercive estimate beyond the null directions.

**Constructive window gauges.** Plateau, curved and folded gauges prove
positive floors on specified windows. All profiles are paid through aperture
$3/10$; odd profiles through $181/500$, beyond the first prime atom at
$(\log2)/2$. These are genuine certificates on their domains, not evidence
that the same gauge works at every aperture.

**The ceiling on positive transport.** Theta-derived trial states give a doubly
exponential upper bound on $\mu(A)$. Any positive lower floor must decay at
least fast enough to respect it. The upper bound is neither an asymptotic
formula nor a proof of positivity.

**Aperture geometry.**
[Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md)
proves that the literal ground-energy path is strictly decreasing. RH is
strict positivity at every finite aperture; otherwise there is one zero
contact, with negative energy thereafter. Its shell identity splits the drop
into geometric relaxation and signed new-prime work. The monotone path and
finite-step identity already exist; their quantitative arithmetic control is
what remains.

## Research questions

- Which signed gauge certificate pays the prime anti-diagonals and pole
  contribution at arbitrary aperture?
- Does the quotient by the theta radical admit a useful coercive norm, with
  the full signed form controlled in that norm?
- Can one extend the explicit all-profile positive window, or prove a graded
  floor $\mu(A)\ge-Ce^{2\sigma A}$ with $\sigma<1/2$?
- Can weighted frustration or the prime-shell identity bound the ground-energy
  loss without assuming the floor it is meant to produce?

The norm is part of each question. All-parity Sobolev floors already attain
the zero-width exponent in
[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md).
Their derivative cost does not settle the unrestricted $L^2$ question.
Likewise, counting frustrated edges cannot pay their continuum weights,
pole moments and approximation errors without an additional theorem.

## Place in the wider research

[Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md)
constructs sources for the same complete form.
[Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md)
resolves the signed gauge identity into individual pairs and shared budgets.
[Square-Root Threshold](../SquareRootThreshold/README.md) converts aperture
floors into zero-visibility and width statements.
[Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md)
explains why the cancellation must be estimated before taking absolute values.

The [programme umbrella](../ArithmeticCriticalityTheory.lean) is the module
map. Start with the coordinate and parity conventions, then the exact
ground-state identity for the gauge under consideration.
