# Arithmetic Incidence Positivity

Arithmetic Incidence Positivity studies the Weil sign problem **pair by pair**.
Which pairs carry negative conductance, which positive interactions can pay
for them, and can the payments be made simultaneously without spending one
positive contribution several times?

The programme's distinguishing object is a weighted incidence graph on the
logarithmic line. Same-side pairs read ratios; reflected pairs read products.
This makes prime-power divisibility visible inside the continuous form and
turns a global positivity question into an allocation problem.

## Objects and language

Use an odd gauge $M$, positive on the positive half-line, and write an odd
test as $F=Mu$ with even profile $u$. Its gauge-independent zero form is a
signed jump energy plus a variance term. The jump measure is

$$
dm(t)=\frac{e^{-t/2}}{1-e^{-2t}}\,dt
      +\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\,\delta_{\log n},
\qquad t>0.
$$

The jump contribution pairs $(u(x)-u(y))^2$ with $M(x)M(y)$ and $dm(|x-y|)$.
The polar variance adds the pair weight
$2M(x)M(y)\sinh(x/2)\sinh(y/2)$. The factor two records the two orders in
the variance integral.

On a **same-side pair**, the gauge factors have the same sign. On a
**crossing pair** $x<0<y$, their product is negative, so a positive jump atom
creates an adverse contribution. The pole supplies a favourable crossing
term, but vanishes near the axes where some prime costs concentrate.

On the lattice $\{\pm\log a\}$:

- $(\log a,\log b)$ has a prime atom when $b/a$ is a prime power;
- $(-\log a,\log b)$ has one when $ab$ is a prime power, forcing both
  integers onto one prime tower.

A **strip** is a neighbourhood of a prime anti-diagonal $|x|+y=\log n$.
A **surplus** is a proved positive remainder available for allocation.
A **global allocation** pays every strip, pole term and gauge remainder with
one common accounting of that surplus.

## Foundational mechanisms

**Ratio/product classification.** Exact lattice comparisons locate the adverse
axis and small-pair terms. In the continuum, polar compensation pays much of
the archimedean crossing density, leaving thin axis collars and prime atoms.
A scalar comparison of weights is only a guide: a Dirac atom cannot be paid
by a density until both have been integrated against the test.

**Reflection and shared surplus.** Folded gauges, Schur estimates and crossing
identities transfer same-side energy towards adverse reflected interactions.
They give positive window certificates, including odd windows past the first
prime atom. Extending a certificate requires controlling overlap: a separate
valid payment for each strip need not be a valid joint payment.

**Tower and translate calculus.** Gram identities compress all powers of one
prime into first-power translate correlations. Within a tower the structure
is exact; between towers the mixed terms remain. The method exposes a smaller
signed correlation problem without granting orthogonality to different primes.

**Prime–polar cancellation.** Abel summation expresses their difference using
the two-pole Chebyshev defect

$$
E(t)=e^t+t-1-\psi(e^t).
$$

This keeps the pole cancellation before estimating and yields graded floors
in the stated norms. The reflected pole is part of the defect; replacing it
by the usual one-pole error changes the form.

**The raw-comb obstruction.** The half-power prime comb and its cross-prime
energy have sharp exponential growth on smooth odd unit tests. A universal
polynomial bound for that unchanged aggregate is false. The constructive
survivor is its horizon translation/resolvent description, developed in
[Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md),
which directs attention to a signed first-power pairing or a precisely
subtracted residual.

## Research questions

- Can one allocation pay the entire odd form at arbitrary aperture, including
  all overlap weights and the single shared Gamma/polar reserve?
- Which signed first-power prime–polar estimate improves the elementary
  exponential rate?
- Does a specified compensated correlation kernel admit a useful Schur bound,
  with its subtraction and receiver norm justified?
- Can discrete ratio/product comparisons be transferred to all compact
  profiles with a uniform continuum approximation cost?

The complete allocation criterion is RH-equivalent. A graded loss can instead
bound zero width, but its normalization matters: a derivative-dependent floor
is weaker than an unrestricted mass-norm floor. Identifying the actual prime
source is also weaker than bounding its signed contribution.

## Place in the wider research

[Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md)
supplies the gauges and zero form; AIP resolves their conductances and budgets.
[Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md)
supplies exact source families and approximation tools.
[Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md)
asks how source signs survive passage to energy and global allocation.
[Square-Root Threshold](../SquareRootThreshold/README.md) translates growing
aperture estimates into visibility and width bounds.

Start with the pair convention, then the reflected energy identity and the
allocation being proposed. The
[programme umbrella](../ArithmeticIncidencePositivity.lean) maps the lattice,
window, tower and continuum tools.
