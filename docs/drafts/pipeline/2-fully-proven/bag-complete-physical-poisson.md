# BAG complete physical Poisson matching

Parent: bag-complete-lattice-fourier-transfer.md. Continuation 01ab.
Route: signed physical BAG cubic. Paper proof and all three production Lean leaves complete;
axiom and index audits passed; global lint has31 unrelated unreachable modules. No signed cancellation estimate is claimed.

For the actual compact smooth amplitude A_N constructed in
ChiPrimeGaussianCubicFourierLattice, every a in Euclidean three-space satisfies

    sum_(k in Z^3) hat(A_N)(k-a)
      = sum_(n in Z^3) exp(2*pi*i*<n,a>)*A_N(n).

The physical sum is finite by compact support. The Fourier sum is absolutely
convergent at every shift by the previous all-shift Schwartz sampling theorem.
Every lattice lift is retained. No Mellin/lattice interchange is required.

Proof. Work first in raw real coordinates X=(Fin 3 -> R), Z=(Fin 3 -> Z).
For compact continuous f, P_f(x)=sum_n f(x+n) is a fixed finite sum locally:
if ||x||<=R and f(x+n) is nonzero, compactness bounds every |n_i| by B+R.
This allows arbitrary overlap, without an invalid unit-cube support premise.
Reindexing proves P_f(x+m)=P_f(x). The open quotient map X -> (R/Z)^3
therefore descends P_f to a continuous function on the full torus.

The cube (0,1]^3 is a fundamental domain: the unique integer translation of
x into it is n_i=1-ceil(x_i). Translation invariance of Lebesgue measure and
fundamental-domain unfolding give integral_cube P_f = integral_X f.
The same locally finite sum justifies the integral interchange. Multiplication
by the integer Fourier character commutes with periodization, so every torus
coefficient is precisely integral_X exp(-2*pi*i*<k,x>)*f(x).

Absolute summability of those coefficients and the corpus's multidimensional
Fourier convergence recover P_f(0). The volume-preserving raw-coordinate /
Euclidean-space equivalence identifies the coefficient with the literal
Euclidean Fourier transform. Apply this to exp(2*pi*i*<x,a>)*A_N(x): the
coefficient is hat(A_N)(k-a), with no sign or volume normalization loss.
The explicit Fin-3 / nested-integer-triple equivalence preserves every index.

The existing unconditional cutoff family discharges compactness and absolute
summability. Its exact physical formula, cutoff plateau and original
negligible sharp/smooth edge error remain in the final statement.

The finite physical/projector matching is resolved below. Remaining hard
mathematics: prove signed o(N/log(N)^2) cancellation for the growing complete
action, including near-cone lifts and tails. Growing moments,
moving cofactors, common-height self-return and RH remain open. A fixed-scale
Poisson identity does not supply any estimate uniform in N.

## Complete finite critical action — next conjecture proved

Define L_N(a)=sum_k hat(A_N)(k-a), now with a in the literal nested real
triple coordinates used by the rational atom/projector corpus. Poisson and
compact support imply L_N equals the finite cube test with coefficient
A_N(p,q,r), on ALL natural triples in (floor(N),floor(2N)]. This step first
proves that every nonzero integer sample has three positive natural indices
in that band; no negative, zero or boundary contribution is silently removed.
An explicit injection handles the r,p,q order used by the finite cube test.

The exact natural coefficient formula is
eta(p)*eta(q)*eta(r)*mainEntry(N,p,q,r)/(log(p)*log(q)*log(r)).
Apply the existing complete projected-cube atom theorem. Its source selects
three prime logarithms exactly, and its denominator floor(2N)+1 makes the two
literal projectors remove exactly p=r or q=r. For prime triples all logarithms
are nonzero, so cancellation gives the literal smoothed signed cubic. All
nonprime terms vanish. Finite sum reordering agrees with the original p,q,r
order. Both contractions AND their intersection remain in the composed
projector; no average is replaced by its central atom.

Consequently, for an unconditional actual family,

    smoothedCubic_N = criticalAtomAction_N(projector_N(L_N)),

and log(N)^2/N times the norm of the difference between this full action and
the ORIGINAL sharp physical cubic tends to zero. Every Fourier lattice at
every shift is absolutely summable. This resolves the finite matching gap
listed above. It gives no signed asymptotic cancellation of the action.

Three production leaves passed: ChiCompactLatticePoisson (51112),
ChiPrimeGaussianCubicPoisson (11522), ChiPrimeGaussianCubicLiftedAction (58567).
All exit0 with empty logs. All12 public declarations passed axiom11043;
only propext, Classical.choice and Quot.sound. Index18738 passed, all12 API
entries and single imports verified. Lint56265 exited1 with31 unrelated unreachable modules; no new-leaf or
proof-debt errors. Global lint is not clean.
