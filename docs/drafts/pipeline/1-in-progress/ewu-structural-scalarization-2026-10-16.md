# EWU structural scalarization

Status: conjecturing; no new theorem claimed.

Goal: remove a structural obstruction in EWU beyond the completed critical one-pole and exact even-polar energy-fibre recovery results.

Constraints: unconditional source theorems, no new axioms or RH premise; no web, numerical computations, or literature novelty audit. Corpus search and Lean source are authoritative.

Conjecture log:

1. Recover an arbitrary spectral density with even rows. FALSE as stated: every even row has even real-line spectral density, whereas a general complex source need not. Survivor: only symmetrized densities can be targets.
2. Scalarize every finite positive smooth even-polar mixture exactly: its entire autocorrelation transform is the spectral square of one smooth compact even-polar source. OPEN CORE: divisor splitting must preserve exponential type and compact support. For merely C² inputs, modulus control initially gives Sobolev regularity, not automatically C²; do not claim that upgrade.

Current plan: inspect corpus factorization and source-division mechanisms; attack scalarization; produce a complete paper proof before writing Lean; if it fails, record obstruction and continue with its positive survivor.

## Paper proof target: smooth exact scalarization

For a finite positive mixture of smooth compact even complex sources, form
P(z) = sum c_j F_j(z) conjugate(F_j(conjugate(z))). Then P is even, entire,
Schwarz-real and nonnegative on both coordinate axes. The imaginary-axis
nonnegativity uses evenness, and is essential; arbitrary real-line spectral
densities do not have this property.

1. At every nonzero point of either axis, nonnegativity along that axis forces
even zero order. At zero the order is divisible by four: write the real and
imaginary source components as real even transforms; their first nonzero
Taylor orders are even, and the leading sum of their squared real coefficients
cannot cancel. Remove z^(4k); the remaining P has positive value at zero.
2. Split the divisor: retain all copies in quadrants I and III, none in II and
IV, and half the copies on each axis. The retained divisor is invariant under
z -> -z. Its sum with its conjugate is exactly the original divisor.
3. Jensen and logarithmic buckets give summability of inverse p-th powers for
every p > 1. The genus-one product Q of the retained copies is entire and even.
Its conjugate product has the complementary divisor. Their product has the
same divisor as P. The existing even fixed-divisor rigidity, with subquadratic
proximity, makes the quotient constant. Normalize Q by sqrt(P(0)). Thus
P(z)=Q(z) conjugate(Q(conjugate(z))). Restore the factor z^(2k).
4. For 1 < p < 2, each genus-one factor has log norm at most
2 min(|z/a|, |z/a|²) <= 2 |z/a|^p. Therefore Q has growth exp(C |z|^p).
On both axes |Q|²=P. On the real axis Q has arbitrarily rapid polynomial decay;
on the imaginary axis it has the original exponential-type bound with half
the exponent. Apply quadrant Phragmen-Lindelof to polynomial multiples of Q
times exp(±iAz), with A strictly above that half-type. This yields strip
decay |Q(x+iy)| <= C_N exp(A|y|)/(1+|x+iy|)^N.
5. The inverse Fourier integral of Q is smooth (all frequency moments are
integrable), even, and compactly supported: shifting the contour to imaginary
height ±s and letting s tend to infinity makes it zero when |x|>A. Fourier
inversion identifies its entire transform with Q.
6. Consequently its autocorrelation equals the original mixture pointwise,
by Fourier inversion. All raw integer atoms, all pole values, and the complete
archimedean functional agree exactly. If the original rows are pole-free,
P(i/2)=0 and |Q(i/2)|²=0, so the scalar source is pole-free as well.

This is an actual source construction. Its conclusion is equality of the
smooth even-polar autocorrelation cone with its finite positive hull. No
positivity of the Weil functional is assumed or concluded. The C² extension
is deliberately not claimed before regularity is paid.

Formalization tasks: divisor split and growth; axis-zero multiplicities;
Fourier compact-support recovery; exact EWU source scalarization; leaf builds,
direct audits, axiom checks, umbrella wiring and cleanup.

No external novelty claim is made. Existing research Markdown is not used as evidence.
