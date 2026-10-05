# BAG exact critical physical cubic atom identity

- ID: C28.56ag.3, continuation01a7.
- Route: complete signed physical BAG cubic.
- Paper status: dependency-closed finite identity below.
- Lean status: all three production leaf and all24 public declaration axiom
  audits passed. Index refreshed; global lint has33 unrelated unreachable
  modules. See the corresponding 3-formalized card.
- Parent: ../1-in-progress/bag-three-frequency-ramanujan-source.md.

## Exact statement

For each real N>=1 set M=floor(2N), P=range(M+1), Q=rad(P), D=M+1 and
I={floor(N)+1,...,M}. Define the literal finite signed rational sources

    tau_P = sum_(d|Q) -mu(d)*log(d)/d * sum_(a mod d) delta_(a/d),
    sigma_P = sum_(d|Q) mu(d)/d^2 * sum_(b mod d^2) delta_(b/d^2),
    rho_P = tau_P * sigma_P.

Every pair of atoms is retained in the convolution, adding their rational
nodes and multiplying weights. There is no damping parameter. Let A_N(p,q,r)
be the ACTUAL `primeGaussianCubicMainEntry`, including its literal W/V
amplitudes, reciprocal r, conjugation and phase exp(2*pi*i*p*q/r). Define

    F_N(x,y,z) = sum_(p,q,r in I)
      A_N(p,q,r)/(log(p)*log(q)*log(r)) * exp(2*pi*i*(p*x+q*y+r*z)).

This finite Fourier test has no prime or equality-contraction mask. Define

    E13 F(x,y,z) = (1/D) sum_(a mod D) F(x+a/D,y,z-a/D),
    E23 F(x,y,z) = (1/D) sum_(b mod D) F(x,y+b/D,z-b/D).

Then the original complete signed noncontracting physical cubic is exactly

    primeGaussianCubicOffDiagonal(N)
      = rho_P^tensor3 [ (Id-E13)(Id-E23) F_N ].

All original-band prime triples remain, with exactly p=r and q=r removed
and the overlap counted once. No asymptotic, positive-damping composite
correction, selected rational mode or unproved analytic premise occurs.

## Proof

1. Each finite damped divisor atom has weight mu(d)*d^(-e)/d. Since d>0,
   differentiation at zero gives exactly -mu(d)*log(d)/d. The difference
   quotient used in ag.1 converges to this derivative at each individual
   atom. Multiplication by the finite square-divisor weight gives the
   critical convolved atom weight. All sums are finite.
2. For 1<n<=M, the existing finite-source theorem gives the Fourier
   multiplier 1_(Squarefree n)*D_e(n)/e. The current Wold derivative and
   exact squarefree-Mangoldt identity give its limit log(n) on primes and
   zero otherwise. Finite-sum convergence and uniqueness of limits identify
   this with the LITERAL Fourier coefficient of rho_P. Thus exact prime
   selection holds at finite P before N grows.
3. Finite product distributivity identifies the three-coordinate tensor
   coefficient with the product of those three prime logarithms. Each test
   coefficient is supported on I, whose integers satisfy 1<n<=M. No
   statement about uncovered integer frequencies is needed.
4. Translation of the (p,q,r) Fourier character by (a/D,0,-a/D) multiplies
   it by exp(2*pi*i*(p-r)*a/D). Audited finite torsion orthogonality makes
   E13's multiplier 1_(D divides p-r). Since p,r<=M<D, this is exactly
   1_(p=r). Likewise E23 selects q=r. Their complementary composition
   therefore gives the exact logical union of the two exclusions, with
   their intersection restored. These are literal translation operators,
   not an assumed identification with a multiplicative trace axis.
5. The finite atom action and the projectors are complex linear. Distribute
   both over the complete finite Fourier test. By steps2–4, only prime
   triples survive and the two desired equality families vanish. Real.log
   is nonzero at each prime, so its three factors cancel their denominator
   exactly. The remaining summand is A_N(p,q,r) for every surviving triple,
   precisely the corpus definition of the original physical cubic.

## Phase information retained for the hard next step

For r!=0 the complete dual phase is exactly

    p*q/r+x*p+y*q+z*r
      = (p+y*r)*(q+x*r)/r+(z-x*y)*r.

Writing delta=z-x*y, simultaneous shifts by (a,0,-a) and (0,b,-b) send it to

    delta-(1+y)*a-(1+x)*b-a*b.

The mixed term and translated amplitudes remain. Tangency at y=-1 or x=-1
alone does not justify replacing the finite projectors by axis deletion in
the multiplicative six-zeta trace.

## Frontier limitation

This is the full ADDITIVE finite physical identity, not a cancellation
estimate. Its source changes with N and its test oscillates with N. The
complete signed transverse action at o(N/log(N)^2), with every integer lift,
near-cone neighborhood, tail and physical weight, remains open. The existing
smooth-edge theorem is available for the next Poisson/stationary analysis;
it does not bound the signed interior. Growing moments, moving cofactors,
common-height self-return and RH remain open.
