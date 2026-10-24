# Trans-Horizon Incidence Mechanics

A divisor sieve with cutoff $N$ observes an integer only through its divisors
at most $N$. What can that observer recover or control when read at positions
far beyond $N$? Trans-Horizon Incidence Mechanics studies the exact information,
energy and boundary laws of this mismatch.

Its central problem is **receiver transfer**: turn finite arithmetic identities
into a bound on a growing source in the norm that the analytic application
uses. Exact reconstruction, small period variance and local convergence are
different achievements; none alone supplies that bound.

## Objects and language

For a finite row $c$ supported on $1\le d\le N$, define

$$
s_{N,c}(k)=\sum_{d\mid k,\ d\le N}c(d),\qquad
m_c=\sum_{d\le N}\frac{c(d)}d,\qquad
A_c(n)=\sum_{k\le n}(s_{N,c}(k)-m_c).
$$

The **coefficient horizon** is $N$; the **observation horizon** is the largest
position read. The observation state $\gcd(k,\operatorname{lcm}(1,\ldots,N))$
determines every response at $k$. Squarefree-supported rows need only its
radical information. These finite states explain what the observer cannot see.

The principal receiver norm is the **pronic energy**

$$
E_T(c)=\sum_{n=1}^T\frac{A_c(n)^2}{n(n+1)}.
$$

Its weight is the length of the reciprocal cell $(1/(n+1),1/n]$. This connects
integer prefixes to Nyman–Beurling approximation and Fermi traces. It also
retains the small-index contributions that a long-period average can erase.

For the infinite damped Möbius source $c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$,
$\varepsilon>0$, use the full divisor response and mean
$m_\varepsilon=1/\zeta(1+\varepsilon)$. **Admission** means
$\sup_T E_T(\varepsilon)<\infty$. Admission is known at and above half damping;
admission at positive dampings accumulating at zero is an RH criterion.
The constant may depend on damping, but not on $T$.

## Foundational mechanisms

**Finite observation and inversion.** Divisibility responses, valuation clocks
and reciprocal-cell jumps each recover specified finite data with explicit
conditioning. The boundary terms quantify the price of reconstruction.
Knowing that an observation is injective does not make its inverse uniformly
bounded as the cutoff grows.

**Successor and horizon laws.** Discrete polarization separates energy into
interior differences and endpoint work. Below the coefficient horizon the
truncated divisor response agrees with the complete one. Above it, omitted
composite divisors as well as omitted primes change the endpoint response.
The resulting conservation and dissipation identities retain those terms
instead of extending a below-horizon sign past its domain.

**Signed receiver classification.** Complete-period quadratic data can identify
parity-related rows with different receiver behaviour. The transfer theorems
therefore distinguish sign-blind bounds from estimates using the actual source.
They also distinguish the full collection of truncated rows from its infinite
limit: cancellation may admit the latter while the former remains unbounded.
The horizon and damping limits cannot be exchanged for free.

**Mellin and cofactor bridges.** The prefix receiver has Mellin identities
involving the zeta quotient and exact cofactor decompositions. These translate
admission into zero constraints and expose the cancellation that must be paid.
Actual Möbius estimates supply horizon-dependent sub-half-damping bands;
those bands shrink towards half damping and do not establish admission at a
fixed smaller damping.

**Selectivity of conservation laws.** The programme distinguishes laws shared
by multiplicative models, laws that lose signs, and laws using integer
successor/Bézout structure. This classifies the information in these
mechanisms. It is not a theorem that every possible analytic proof must use
successor arithmetic. The exact signed-energy decomposition is developed in
[CompleteSignedTransHorizonEnergyAndTransferSelectivity](CompleteSignedTransHorizonEnergyAndTransferSelectivity.lean).

## What the programme seeks to build

- A horizon-uniform signed estimate for the actual Möbius receiver at a fixed
  damping below $1/2$, followed by estimates at dampings approaching zero.
- An observation or inverse theorem whose constants remain affordable at the
  receiver scale, including the newly entering boundary cells.
- A quantitative successor or mixed-cofactor law that improves the actual
  source estimate rather than merely reconstructing its coefficients.
- A transfer from finite rows to the infinite receiver with both the bulk and
  reciprocal-origin tail controlled in the same normalization.

These questions should be posed for a specified row, norm and order of limits.
A bound on a tail alone does not identify the weak limit. A full-period
identity does not control an unknown short-window phase. A power saving in
one finite statistic needs a proved assembly theorem before it becomes an
admission result.

## Place in the wider research

[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) supplies the
finite window and pronic Gram arithmetic. THIM studies what survives beyond
the cutoff and through receiver transfer.
[Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md)
then asks whether an admitted receiver can be transported in damping.
[Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md)
prices the signed work involved.

[Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) uses the
same receiver to study possible escape of normalized energy: its cofactor
Gram identity and paid forcing subtraction retain signed information that
finite observations lose.
[Signed Successor Arithmetic](../SignedSuccessorArithmetic/README.md) seeks
new source laws from consecutive integers.

Read the receiver and its quantifiers first, then the relevant finite
observation or conservation law. The
[programme umbrella](../TransHorizonIncidenceMechanics.lean) provides the module
map; the detailed classification constants belong with those theorems.
