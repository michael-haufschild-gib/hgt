# Arithmetic Continuation and Critical Energy

Arithmetic Continuation and Critical Energy studies **transport of an arithmetic
bound through a parameter**. A source is controlled at half damping or on a
small aperture. What signed work must be paid to continue that control?

The distinguishing requirement is uniformity in an independent observation
horizon. Smooth dependence at every finite horizon gives no such bound. The
programme identifies the exact transport budget and the weaker observations
that cannot replace it.

## The damping receiver

For $\varepsilon>0$, define the centred Möbius divisor prefix and its energy by

$$
A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor
                 -\frac n{\zeta(1+\varepsilon)},\qquad
E_T(\varepsilon)=\sum_{n=1}^T\frac{A_\varepsilon(n)^2}{n(n+1)}.
$$

**Admission at $\varepsilon$** means $\exists B_\varepsilon\ \forall T:
E_T(\varepsilon)\le B_\varepsilon$. **Cofinal admission** means admission at
positive dampings arbitrarily close to zero; the bounds may deteriorate with
damping. This is an RH criterion. **Uniform admission on an interval** asks
for one bound throughout that interval and is a stronger statement.

Admission is known at and above $1/2$. Because the energy is nondecreasing in
$T$, a bound on cofinal horizons or on the appropriate horizon averages
suffices. The parameter and horizon quantifiers must nevertheless stay separate.

## Exact work and transport

The **signed damping work** pairs the receiver with its own tangent:

$$
W_T(\varepsilon)=\sum_{n\le T}
 \frac{A_\varepsilon(n)\,\partial_\varepsilon A_\varepsilon(n)}{n(n+1)},
\qquad \partial_\varepsilon E_T=2W_T.
$$

Consequently, for $0<a<c$,

$$
E_T(a)=E_T(c)-2\int_a^c W_T(\varepsilon)\,d\varepsilon.
$$

This is the basic transport law. With an admitted right endpoint, a suitable
horizon-uniform signed averaged budget is equivalent to admission at the left
endpoint. Linear and Osgood differential bounds are sufficient ways to produce
that budget, but pointwise or positive-part bounds can be strictly stronger
than necessary. Large tangent norm is harmless if its signed work cancels.

The arithmetic derivative also has a Markov decomposition into boundary flux,
dilation jump energy and forcing with the pole correction retained. It exposes
terms a source estimate could control. Estimating all terms absolutely can
lose the cancellation the work identity needs.

**Integer dilation is exact.** On zero-origin rows,
$D_jv(n)=v(\lfloor n/j\rfloor)$ represents multiplicative composition and has
the sharp pronic contraction factor $j^{-1/2}$. Absolute summation of damped
dilations stops at half damping. Below it the source signs are essential.
One-step dilation-block energy is equivalent to the full receiver norm, giving
a smaller but complete observation for a proposed estimate.

## Aperture flow

The second main application is the lowest complete Weil energy $\mu(a)$ on
aperture $a$. If $u_a$ is an $L^2$-normalized ground state and is extended to
aperture $b\ge a$, then for every scalar $c$,

$$
\mu(a)-\mu(b)
=(q_b-\mu(b)\langle\cdot,\cdot\rangle)
 (\operatorname{ext}u_a-cu_b,\operatorname{ext}u_a-cu_b)\ge0.
$$

This is the exact relaxation energy of the old ground state in the larger
space. For the literal Weil form the decrease is strict when $a<b$. RH is
strict positivity at every finite aperture; if RH fails, the path crosses
zero exactly once. These are finite-step statements, not assertions about a
nonzero derivative at contact. See
[TheApertureFlowIsAShellFlux](TheApertureFlowIsAShellFlux.lean) and
[TheApertureFlowNeverStalls](TheApertureFlowNeverStalls.lean).

Freezing prime terms through $N=\lfloor e^{2a}\rfloor$ further gives

$$
\mu(a)-\mu(b)
=[\mu^{[N]}(a)-\mu^{[N]}(b)]+[\mu^{[N]}(b)-\mu(b)].
$$

The first term is nonnegative geometric relaxation. The second is sandwiched
between signed new-prime correlations of the frozen and literal ground states
at $b$; their lags couple only boundary collars. This localizes the arithmetic
estimate required by transport. See
[ThePrimeShellBetaFunction](ThePrimeShellBetaFunction.lean).

## Research questions

- Which independently estimated source terms give a signed work budget below
  half damping, first on one interval and then towards zero?
- Can block energy or the cofactor decomposition produce a budget without
  substituting the unknown receiver energy back into the premise?
- Can the signed prime-shell correlation control aperture relaxation enough
  to prevent contact or produce a graded negative floor?
- Which cutoff limits preserve the same horizon-uniform budget, including
  boundary cells entering with the cutoff?

A positive aperture floor must respect the doubly exponential ceiling from
criticality theory. A graded floor can be a more usable target. Neither a
changed energy nor a relative-step condition is an arithmetic proof until its
comparison constants and source budget are established.

## Place in the wider research

[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) and
[Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md)
supply the receiver and finite arithmetic.
[Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md)
studies how the work's large pieces cancel.
[Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md)
supplies the aperture form and gauges.
[Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) studies
possible unbounded states compatible with the cofactor identities.

Start with admission, then the averaged work identity. The
[programme umbrella](../ArithmeticContinuationAndCriticalEnergy.lean) maps the
transport, dilation and shell-flow modules.
