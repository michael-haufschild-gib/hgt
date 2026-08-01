# Prime--Gamma reflection-decimation defect resolvent to RH

- **ID:** `prime-gamma-reflection-decimation-defect-resolvent-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, TOP-DOWN SOURCE PRODUCER, STATIC REFLECTION GEOMETRY
- **Scientific status:** `[OPEN] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  `../3-formalized/not_new_scientific_knowledge/bv-prime-window-dilation-residue-orientation.md`;
  `../3-formalized/not_new_scientific_knowledge/euclidean-spectral-pushforward-hankel-rh-capstone.md`;
  `../3-formalized/not_new_scientific_knowledge/prime-arch-positive-moment-representation-to-rh.md`;
  `../3-formalized/not_new_scientific_knowledge/inverse-tilted-prime-gamma-central-source-value-relation.md`;
  `../3-formalized/not_new_scientific_knowledge/finite-skew-green-trace-positivity.md`;
  `../3-formalized/not_new_scientific_knowledge/simplex-effective-harmonic-positive-parity.md`;
  `../3-formalized/not_new_scientific_knowledge/von-mangoldt-gamma-all-depth-oriented-anomaly.md`;
  `../3-formalized/not_new_scientific_knowledge/von-mangoldt-gamma-all-depth-cauchy-gram.md`;
  `../2-fully-proven/not_new_scientific_knowledge/ccm-gamma-damped-cauchy-frame-trace-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/prime-arch-explicit-circle-state-reflection-law.md`.
- **Statement:** `[CONJECTURE]` The normalized prime--Gamma moment germ is the cyclic resolvent of
  a positive reflection-sewn decimation-defect operator constructed from resolved prime channels,
  the Gamma cyclic source, and the finite BV square-decimation identity before continuation.

## Goal

Construct positivity rather than postulate a positive measure.  The desired object must retain all
four data which divisor sets, finite jets, abstract fields, and principal symbols lose:

1. functional-equation reflection exchanges the two source channels;
2. the positive cone selects one orientation of that exchange;
3. prime channels and the archimedean counterterm enter one completed identity;
4. every vector and operator is produced from explicit finite source incidence before any Xi zero
   or target moment measure is read.

The consumer end is already closed in Lean.  If a positive operator `A` and a source vector
`Omega` satisfy

```text
normalizedPrimeArchMoment(n)=<Omega,A^n Omega>           (1)
```

for every `n`, then the spectral measure of `(A,Omega)` is a positive moment representation and
RH follows.  No infinite-support, determinacy, compactness, simplicity, or determinant hypothesis
is required.

## Source evidence already proved

Let `W` be an actual compact-BV prime window.  For a positive integer `r`, Lean now proves that its
forward and inverse argument dilations obey the exact finite coefficient law

```text
p_(W(r·))(n)=p_(W(·/r))(r^2 n).                         (2)
```

The coefficient includes both the finite von-Mangoldt window and its archimedean Mellin
counterterm.  After canonical continuation, the two actual Laurent residues transform by

```text
R_+(rho)=r^(rho-1/2)R_W(rho),
R_-(rho)=r^(1/2-rho)R_W(rho),                            (3)
```

and their squared-norm difference has the strict sign of `Re(rho)-1/2`.  Thus orientation is the
continued image of a finite prime--Gamma source action; it is not added as a divisor predicate.

On coefficient space, square-index decimation `D` has the exact positive defect

```text
||a||^2-||Da||^2
 =sum_(r^2 does not divide n)|a(n)|^2.                   (4)
```

The Gamma-damped channel-resolved Cauchy construction supplies the complementary ingredient: a
positive prime-channel covariance whose trace remains Euler-additive and whose Gamma diagonal
crosses the critical half-weight.  Its exact critical prime--Gamma relative channel is not yet
constructed.

## Medalist conjecture

`[CONJECTURE]` There is a source-defined singular boundary completion `H_src`, a completed
prime--Gamma incidence map `V`, a reflection-compatible square-decimation contraction `D_src`, and
a distinguished source vector `Omega` such that

```text
Delta_src = I-D_src^*D_src >= 0,
A_src     = V^* Delta_src V >= 0,                         (5)

normalizedPrimeArchMomentGerm(z)
 = <Omega,(I-z A_src)^(-1)Omega>                         (6)
```

near `z=0`.

The notation in `(5)` is schematic only to the extent that `V` and the singular completion remain
to be constructed.  The required content is exact:

- `Delta_src` must descend from the off-multiple sum in `(4)`;
- `V` must contain the resolved von-Mangoldt channels and Gamma boundary channel before trace;
- reflection must exchange the forward and inverse BV source channels;
- `(6)` must be proved from the continued prime--Gamma source formula, not used to define `A_src`.

Expanding `(6)` gives `(1)`, hence the formal chain

```text
source reflection-decimation defect resolvent identity
  -> positive cyclic moment representation
  -> complete prime--Gamma trace-Hankel cone
  -> RH.                                                   (7)
```

This is a constraint construction.  `A_src` is a static positive observable obtained by
compression of a source defect; it is not a Hamiltonian or a flow whose evolution is assumed to
carry the proof.

## Strong weakening: local finite source certificates

The global operator is stronger than the Lean consumer needs.  It is enough that for every `N`
the finite source incidence produce a finite-dimensional `H_N`, `A_N>=0`, and `Omega_N` with

```text
normalizedPrimeArchMoment(k)=<Omega_N,A_N^k Omega_N>
for 0<=k<2N.                                              (8)
```

The witnesses may vary with `N`; no compatibility, limiting measure, or support theorem is an
input.  Equation `(8)` makes the first `N` by `N` source Hankel block a literal Gram matrix.  The
existing local finite-positive-atomic closure theorem then closes `(7)`.

This is the operational meaning of removing the infinite-support hypothesis.  It does not make a
single finite global spectrum plausible.  The corpus proves that no fixed finite KMS/Wightman
system realizes the complete normalized moment tower.  Since every finite positive-atomic moment
sequence has such a KMS realization, a fixed finite positive-atomic global model is also excluded.
Spectral proliferation is therefore an automatic consequence of exact source matching, not a
condition to establish before positivity.

## Sharper conjecture: finite reflected-scale Green Gram jets

The weakest source-producing target is smaller than `(8)`.  No operator powers, common spectrum,
or compatibility between cutoffs are needed.  For every `N` it is enough to construct a
source-defined net of positive semidefinite matrices

```text
G_(N,X)(i,j),   0<=i,j<N,
```

from finitely many BV dilation channels, their positive off-square decimation defects, a finite
inverse of the centered scale generator, and the Gamma/boundary channel, such that

```text
lim_(X->infinity) G_(N,X)(i,j)
  =normalizedPrimeArchMoment(i+j).                       (10)
```

The cutoff form must be positive before the comparison with the target moments, for example in
the schematic source form

```text
G_(N,X)(i,j)
 =<Delta_(r,X)^(1/2) Psi_(N,X,i),
    Delta_(r,X)^(1/2) Psi_(N,X,j)>
  +<Gamma_(N,X,i),Gamma_(N,X,j)>,                        (11)
```

where `Delta_(r,X)` is the literal finite off-`r^2` projection supplied by square-index
decimation.  Neither `Psi`, `Gamma`, nor the renormalization may be defined from the Xi divisor,
the target Hankel matrix, or a Cholesky factor of that matrix.

`[CONJECTURE]` Such finite reflected-scale Green Gram jets exist with an explicit prime--Gamma
boundary subtraction depending on `N` but not on any zero.  The now-formalized inverse-tilted
source identity then proves `(10)`.  Since the positive semidefinite cone is closed in every fixed
matrix size, `(10)` gives every finite prime--Gamma Hankel block and hence RH.

This is the exact gain from removing support assumptions.  A global scale-zero Hilbert completion,
bounded Laurent evaluation, tightness of spectral measures, and a common thermodynamic family are
all optional.  The only limiting statement is entrywise convergence of one finite source Gram at
a time.  The resulting chain is

```text
finite BV off-square defect + completed Gamma boundary jet
  -> source-built positive finite Gram packet
  -> entrywise prime--Gamma moment-jet comparison
  -> complete source Hankel cone
  -> RH.                                                   (12)
```

The proposed packet is a static reflection constraint on a finite scale set.  The dilation
parameter labels the two reflected source channels; it is not used as an evolution producing Xi.

### Exact value relation `[CLOSED]`

Lean now identifies the normalized centered moments with the Taylor coefficients of one explicit
inverse-tilted prime--Gamma source.  At `s=1+iz`, the zero-free inverse-tilted Mellin aperture is
divided out of the continued finite-prime source after subtracting its explicit quadrature
correction; adding the fixed Gamma connection gives exactly
`continuedPrimeArchSourceRelativeTrace`.  Every normalized moment is the corresponding even Taylor
coefficient of this reconstructed source.  The theorem uses no divisor data.

What remains is therefore only the positive lift:

```text
finite positive reflected BV/Gamma Green kernel
  --source trace comparison-->
Taylor-Hankel kernel of inverseTiltedPrimeGammaSourceTrace.       (13)
```

Proving only positivity of the continued Cauchy kernel is not an acceptable substitute: that sign
is already an RH-equivalent consumer.  The left side of `(13)` must be positive by its finite
prime-channel construction before the value identity is invoked.

### Why the inverse centered scale generator is forced

The BV dilation orbit acts on an uncensored Laurent fibre by

```text
exp(t*(rho-1/2)).                                         (14)
```

Taylor differentiation in `t` therefore produces positive powers of `rho-1/2`.  The canonical
moment node is instead

```text
lambda_rho=-(rho-1/2)^(-2).                              (15)
```

Consequently dilation and finite decimation alone cannot produce the moment tower.  A Green
operator for the centered scale generator is mathematically forced.

The corpus already proves the source algebra.  For `C=D+1/2`, weight-one inversion gives
`CJ=-JC`; on a Mellin power of exponent `rho`, `C` has symbol `1/2-rho`.  Hence

```text
A=-C^(-2)                                                (16)
```

has precisely the symbol `(15)`.  On the natural `L^2(dt)` scale space, the paper-proven closure
makes `C` skew-adjoint, so whenever its inverse is defined,

```text
A=(C^(-1))^* C^(-1) >= 0.                               (17)
```

This is the structural reason that a positive Euclidean representation appeared: it is the Green
square of the reflection-odd centered scale constraint, not an independently postulated spectrum.

### Finite Hodge--Green target

For each source cutoff `X`, construct a finite completed prime--Gamma complex with:

```text
Gamma_X       grading,
d_X           odd source differential,
P_X           orthogonal harmonic projection,
C_X           invertible skew-Hermitian centered scale generator,
A_X=-C_X^(-2)>=0.                                       (18)
```

Require `P_X` to commute with `C_X`.  The finite vectors

```text
V_(X,i)=P_X C_X^(-1) A_X^i                              (19)
```

in Hilbert--Schmidt space then satisfy

```text
<V_(X,i),V_(X,j)>_HS=Tr(P_X A_X^(i+j+1))>=0.            (20)
```

The matrix algebra in `(20)` is now closed in Lean.  A left inverse `G_X` of a skew-Hermitian
`C_X` is automatically skew-Hermitian, its Green square

```text
A_X=G_X^*G_X=-G_X^2
```

is positive semidefinite, and the shifted trace powers `Re Tr(A_X^(n+1))` form a
reflection-positive Hankel sequence.  Thus no spectral theorem, diagonalization, support
hypothesis, or independently chosen measure remains in this finite step.

The source theorem to prove is

```text
Tr(P_X A_X^(n+1))
  -> normalizedPrimeArchMoment(n)                       (21)
```

for every fixed `n`.  No common spectrum, support theorem, determinant identity, or compatible
choice between unrelated finite cutoffs is required.

There is one essential sign firewall.  `SeamSuspensionTrace` currently compresses a **graded**
trace.  To obtain the ordinary positive trace in `(20)`, the source construction must prove

```text
Gamma_X P_X=P_X                                         (22)
```

or an equivalent positive-parity/effectivity theorem.  Without `(22)`, Hodge compression yields a
signed supertrace and does not produce the Euclidean/Hankel cone.  This is the precise
constraint-orientation junction; it must not be hidden inside the words “spectral realization.”

Lean now also proves the exact parity interface: graded Hodge compression together with
`Gamma_X P_X=P_X` equals the ordinary compressed trace.  Therefore trace cyclicity and the
graded-to-ungraded conversion are no longer open.  Lean also constructs a canonical finite model
with this parity: unaugmented full-simplex descent retains one constant degree-zero harmonic line,
whose projection is positive and has trace one, while its complement has an explicit positive
Hodge Green operator.  Thus positive parity is not an abstract existence problem.

This closes only bookkeeping.  It remains necessary to identify the actual completed
prime--Gamma source-selection complex with such a positive block.  More importantly,
source-effectivity or `Gamma_X P_X=P_X` alone does not make the continued prime--Gamma values
positive.  The positive form must be produced by an explicit source identity before the moment
comparison.

### All-depth von Mangoldt--Gamma orientation `[CLOSED]`

For a resolved positive exponential atom of weight `q`, logarithmic rate `lambda`, base point `x`,
and positive Gamma depth `N`, Lean identifies every Gamma-descent anomaly coordinate exactly as

```text
(alpha_N(q,lambda,x))_i
 =q exp(-x lambda)(-lambda)^i
   (sum_(j<N-i)(-lambda)^j/j! - exp(-lambda)).           (22c)
```

Taylor's theorem gives

```text
(-1)^(N+1)(alpha_N(q,lambda,x))_i>0.                    (22d)
```

For the actual resolved Euler atom, `q=Lambda(n)/n` and `lambda=log n`; hence every prime-power
atom and every jet coordinate lie in the same strict depth-`N` cone.  This extends the existing
depth-one Cauchy positivity and adjacent-depth Bianchi current to an unconditional all-depth
orientation theorem.  It is
source-specific and uses no Xi divisor, reconstruction theorem, target moment measure, or
source-effectivity implication.

Lean now also proves that the sign survives the actual finite aperture, not merely each atom.
For every nonempty cutoff `M` and every `i<N`, the complete finite von Mangoldt anomaly has the
same strict sign `(-1)^(N+1)`.  The prime `2` contribution is a strictly positive coordinatewise
lower floor independent of `M`.  Hence neither higher Gamma jets nor finite Euler aggregation can
be the source of the critical sign loss.

### Finite radial Gauss--Ward packet `[CLOSED]`

The full finite Cauchy polarization is now also formalized.  With the oriented residual
`R_(N-i)(lambda)` define

```text
A_(N,i)(w;p)
 =sqrt(q_p) lambda_p^i R_(N-i)(lambda_p)/(w+lambda_p).  (22e)
```

Lean proves that restoring the other factor `sqrt(q_p)(w+lambda_p)` gives exactly the actual
oriented anomaly coordinate.  The vectors indexed jointly by prime-power atoms and Gamma-jet
coordinates therefore form an unconditional positive semidefinite finite Gram at arbitrary
Cauchy points.  This is positivity before continuation, not positivity inferred from the target
moment matrix.

### Two-boundary source balance `[CLOSED FINITELY]`

The literature identifies the correct reduction as two constraints, not one unexplained charge:
the Mellin characters at `+1/2` and `-1/2` must both vanish before applying the Weil square.  Lean
now performs the finite source construction canonically.  At each aperture and Gamma depth it
orthogonally projects every anomaly Cauchy vector onto the complement of the span of its two
boundary vectors at `w=+1/2` and `w=-1/2`.  Both boundary vectors and both boundary pairings vanish
after compression, and the compressed Gram remains positive semidefinite.

This removes the finite source charge modes without asserting that the RH-faithful divisor seam
charge vanishes.  The remaining theorem is that these balanced projections converge through the
nonnormal Euler boundary and that their limit is the completed inverse-tilted source form.  That
source value identity, not the finite projection algebra, carries the unresolved RH content.

### Cutoff-compatible affine boundary balance `[CLOSED ALGEBRAICALLY]`

Orthogonal projection is not compatible under changing apertures.  The two boundary characters
force a second balance with cutoff-independent coefficients.  Subtracting the affine interpolant
of the Cauchy cells at `w=±1/2` gives the exact residual

```text
(w^2-1/4)
 /((lambda+w)(lambda+1/2)(lambda-1/2)).                 (22g)
```

Lean proves `(22g)`, both boundary vanishings, positive finite Grams, and literal prefix
compatibility as the aperture grows.  The triple denominator gives a genuine cofinal `ell^2`
limit at Gamma depths two and three: depth two follows from `Lambda(n)<=log n` and convergence of
`sum 1/(n log(n)^3)`; depth three follows by partial summation from Chebyshev's unconditional
`psi(x)=O(x)` bound.  This analytic convergence frontier is proved on paper and awaits Lean.

The same construction fails sharply from depth four onward.  Its last jet coordinate has square
asymptotic to a nonzero multiple of `Lambda(n)/n` away from the two boundary points, so the norm
diverges.  Therefore one fixed two-boundary subtraction cannot produce the complete Hankel tower.
It salvages the first two-/three-jet discriminators and forces an order-growing boundary divisor.

### Arbitrary-order boundary-jet balance `[CLOSED ALGEBRAICALLY; CONVERGENCE PROVED ON PAPER]`

Multiplicity `k` at both boundary characters, monic degree at most `2k`, and unit regularized
coefficient at the original Cauchy pole uniquely force

```text
B_(k,a)(w,lambda)
 = ((w^2-a^2)/(lambda^2-a^2))^k/(w+lambda).             (22h)
```

Lean proves the polynomial uniqueness, pole normalization, order-one recovery of `(22g)`, both
boundary vanishings, literal cutoff-prefix compatibility, and finite Gram positivity at every
order.  The degree-less-than-`2k` Hermite interpolant of `1/(w+lambda)` at `w=±a`, matching the
first `k` boundary jets, has exactly `(22h)` as its remainder.  Thus this is the boundary-jet
subtraction forced by the source constraints, not an arbitrary damping inserted to obtain a
Gram.

For nonempty depth `N`, match the boundary multiplicity to the source depth, `k=N`.  This is the
canonical depth-matched choice; using `N+1` would insert an unforced extra damping factor.  On a
compact central `w`-set, the resulting squared feature is
bounded by

```text
C_N*Lambda(n)/(n*(log n)^(2*N+4)).                     (22i)
```

Chebyshev plus partial summation gives unconditional summability.  Lean now proves the stronger
fact needed here without invoking Chebyshev: the exact Taylor bound and `Lambda(n)<=log n` dominate
the squared depth-`N`, order-`N` feature by
`C_(N,w)*Lambda(n)/(n*(log n)^(2N+2))`, and Cauchy condensation proves joint square summability
over every finite Gamma depth and all source atoms.  Hence every fixed finite Gamma depth has a
cofinal positive `ell^2` packet.  This removes the decay obstruction, but it does not identify the
limit with the completed moment jet.

The limiting Gram is indexed by Cauchy parameters, not by moment degree.  Its internal Gamma
coordinate is summed in the norm.  Therefore the next map cannot be a relabelling.  There is a
sharp frequency mismatch.  At `s=1+iz`, the inverse-tilted source is initially a Dirichlet series,
so its `r`-th centered Mellin jet carries positive prime-log powers

```text
n^(-1) (-i log n)^r.                                    (22j0)
```

The depth-`N`, order-`N` balanced Cauchy feature instead contains

```text
((w^2-1/4)/((log n)^2-1/4))^N /(w+log n),               (22j1)
```

and hence inverse prime-log powers.  Undoing the forced boundary divisor multiplies the `n`-th
channel by `((log n)^2-1/4)^N`; it is an unbounded channel operation and destroys the very
square-summability used to obtain the positive cofinal packets at the depths needed for the full
moment tower.  This is consistent with the
formalized prime-log Cauchy seam theorem: no finite rational/log-order correction can perform the
required transport modulo the positive prime Hilbert class.  The exact real-ray
Cauchy/Euler/polar/Mellin colligation does not remove the problem, because its signed critical
Mellin channel remains inside the incidence identity.

Lean now proves the sharper diagonal obstruction directly at the target Mellin jets.  If the
`r`-th positive-log jet is restored separately in every resolved prime channel, its squared
energy on the prime slice is

```text
sum_p (Lambda(p)/p)*(log p)^(2r)
 =sum_p (log p)^(2r+1)/p=infinity.                       (22j2)
```

This uses only `Lambda(p)=log p`, `log p>=log 2`, and Euler's divergence of the prime harmonic
series.  Therefore the infinite-rank repair cannot remain diagonal in the resolved prime basis,
even if arbitrary phases are attached to individual channels.

The stronger Euler-subset lift classification is now formalized.  Let `b` be an arbitrary fixed
Gamma/polar boundary vector and `v_p` arbitrary off-diagonal prime outputs.  If every finite Euler
subproduct has the exact positive source energy

```text
||b + sum_(p in F) v_p||^2
  = B + sum_(p in F) (log p)^(2r+1)/p,                   (22j2a)
```

then the four-subset mixed difference forces `Re <v_p,v_q>=0` for distinct primes, while finite
packet norms are unbounded.  Hence arbitrary off-diagonal mixing is only a real-orthogonal
re-embedding whenever finite Euler subproducts remain source-functorial.  Gamma/polar data already
present before the norm do not help.  A survivor must instead break subsetwise Euler norm
additivity, make the boundary depend nonlocally on the whole Euler product, or postpone positivity
until after signed global completion.  Calling the required map merely "off-diagonal" is no
longer a live mechanism.

There is now one unconditional positive off-diagonal completion surviving this obstruction.
Place the source conductance `Lambda(n)/n` on the integral successor edge `n -> n+1` and take the
discrete derivative before the norm.  For the logarithmic jet `f_r(n)=(log n)^r`, define

```text
E_r(n)=(Lambda(n)/n)*(f_r(n+1)-f_r(n))^2.                (22j3)
```

Lean proves `sum_n E_r(n)<infinity` for every `r`, using the source bound
`Lambda(n)<=log n` and the discrete mean-value estimate

```text
|f_r(n+1)-f_r(n)| <= r*(log(n+1))^(r-1)/n.              (22j4)
```

Thus the edge features

```text
v_r(n)=sqrt(Lambda(n)/n)*(f_r(n+1)-f_r(n))              (22j5)
```

are genuine `ell^2` vectors.  Their mixed products are absolutely summable and every finite
all-order section

```text
G_N(r,s)=sum_n v_r(n)v_s(n),  0<=r,s<N,                 (22j6)
```

is literally a positive-semidefinite Hilbert Gram matrix.  This is an integral, unbounded
source incidence rather than a diagonal reweighting: its Laplacian is `d^* C_Lambda d` on the
successor graph.  It supplies a canonical positive completion of all positive-log Mellin jets and
removes the resolved-prime diagonal divergence.

This completion is not yet an RH source producer.  The successor graph uses additive order and
does not visibly preserve Euler multiplication.  No proved identity currently identifies
`G_N`, or a Gamma/polar boundary Schur complement of its Laplacian, with the normalized
prime--archimedean Hankel section.  Direct identification is now formally ruled out: the
successor derivative annihilates the constant jet, hence `G_N` has a zero zeroth row at every
nonempty size, whereas the normalized prime--archimedean Hankel section has strictly positive
zeroth entry.  Thus a pointed boundary jet is necessary, not optional.  The discriminating open
theorem is therefore a completed discrete Green formula, derived before reading the target
moments,

```text
Schur_Gamma,polar(d^* C_Lambda d)(r,s)
 = normalizedPrimeArchMoment(r+s),  0<=r,s<N.           (22j7)
```

If `(22j7)` holds for every `N`, positivity of `(22j6)` transports through the forced boundary
completion to the complete prime--Gamma Hankel cone and the existing Lean endpoint gives RH.  If
the left side cannot preserve the Euler source law, the successor completion is only a new
positive carrier and this route is killed; positivity alone is not evidence for `(22j7)`.

Thus even locally uniform convergence of the balanced kernel would only give positive jets of the
balanced resolvent law, not the Taylor-Hankel moments of the inverse-tilted Mellin germ.  A valid
next theorem must construct an infinite-rank, off-diagonal incidence transform which mixes the
resolved prime channels and performs this unbalancing together with Gamma/polar completion before
proving positivity after transport.  Let
`K_N(z,w)` be the formalized infinite positive von Mangoldt-anomaly kernel.  The desired completed
kernel `K_N^comp` may be introduced only after that incidence transform is defined independently
of the target moments.  Its terminal comparison would then be

```text
(1/(r!*s!)) d_z^r d_conj(w)^s K_N^comp(z,w)|_(z=w=0)
 =normalizedPrimeArchMoment(r+s),   0<=r,s<N.             (22j)
```

The prime and Gamma inputs are source-positive before comparison; the unbounded completed
incidence must preserve positivity with its forced signs.  The right side is already the explicit
inverse-tilted prime--Gamma Taylor coefficient.  Equation `(22j)` without that incidence theorem
would merely restate the desired moment positivity.  Equation `(22j)` together with a
source-defined positive incidence is the sole RH-bearing theorem on this branch.

The live bridge is consequently:

```text
full finite-aperture von Mangoldt--Gamma jet cone with first-prime floor
  -> positive finite radial Cauchy/Gauss--Ward source Gram
  -> positive finite two-boundary balanced source Gram
  -> depth-2/3 cutoff-compatible affine Euler-boundary limit
  -> arbitrary-order Hermite boundary-jet source packet
  -> all-depth cofinal positive ell^2 packets [formalized]
  -> additive successor Dirichlet completion of every positive-log jet [formalized]
  -> [OPEN] Gamma/polar Green--Schur identity preserving the Euler source law
  -> [ALTERNATIVE OPEN] infinite-rank channel-resolved unbalancing transform
  -> completed positive mixed center-jet Gram [coupling and analytic formalization open]
  -> [OPEN] exact identity (22j) with inverse-tilted completed moment jets
  -> complete prime--Gamma Hankel cone
  -> RH.                                                  (22f)
```

### Hodge--Stieltjes source conjecture

`[CONJECTURE]` The inverse-tilted finite-prime source admits cutoff complexes for which the
completed source germ is the locally uniform Green-resolvent trace limit

```text
normalizedTraceMomentGerm(inverseTiltedPrimeGammaSourceTrace)(z)
 =lim_(X->infinity) Tr(P_X A_X (I-z^2 A_X)^(-1)),         (22a)
```

with `C_X`, `G_X`, `A_X`, and `P_X` constructed from the finite prime channels, quadrature
correction, Gamma boundary channel, and reflection before the right side is compared with the
target germ.  Source degree is effective:

```text
Gamma_X P_X=P_X.                                         (22b)
```

Expanding `(22a)` produces `(21)` simultaneously for all fixed moments.  The Green square and
`(22b)` make the finite compressed trace positive once the actual source complex has been
constructed.  They do not prove that this trace equals the continued source germ.  That comparison
must come from the all-depth anomaly and its reduced Gauss--Ward factorization; the formalized
inverse-tilted value relation can then identify the resulting limit with the canonical
prime--Gamma moments.  This would give RH without a global spectrum, an infinite-support argument,
or a flow.

The geometric content of `(22b)` may be modeled by the now-formalized unaugmented-simplex
effective line, but that model is useful only after a source-specific chain equivalence is proved.
It must not be promoted from abstract effectivity, reconstruction of Xi, or packaging several
conservative shadows.

The former proposal to identify the common first-prime seam charge solely with the negative
harmonic block is insufficient.  Exact orientation reversal of a physical defect packet contains
an independent exponential factor governed by the first source moment.  Positive harmonic parity
can remove a grading sign but cannot cancel that source-balance anomaly.  Common-charge vanishing,
if needed, must therefore follow from the explicit prime--Gamma causal/polar subtraction in the
reduced Gauss--Ward identity, not from effectivity alone.

## Discriminator

The first nontrivial test is not another global RH equivalent.  Construct directly from the
completed source channels a vector `Psi_src` and a positive defect `Delta_src` for which

```text
m_0 m_2-m_1^2 = ||Delta_src^(1/2) Psi_src||^2,           (23)
```

where `m_k=normalizedPrimeArchMoment(k)`.  The right side must be defined without `m_0 m_2-m_1^2`
and without Xi divisor coordinates.  Equation `(23)` would discharge the first genuinely
nonconstant Hankel block and distinguish this mechanism from a generic positive carrier or a
renamed moment criterion.

The next discriminator is the `3 x 3` block: the same construction must provide three source
vectors with Gram entries `m_(i+j)`.  A mechanism which proves only `(23)` by a special scalar
identity but has no three-vector source polarization is not the sought carrier.

For the finite-jet formulation the corresponding first test is a positive `2 x 2` cutoff Gram
whose three entries converge separately to `m_0,m_1,m_2`.  This is stronger evidence for the
mechanism than a posteriori algebraic rewriting of `m_0*m_2-m_1^2`: it forces one common
source packet to produce the mixed value `m_1` as well as both diagonal values.

## Attacks and positive residues

1. **Arbitrary positive measure.**  Choosing a representing measure after reading the moments is
   exactly the RH-equivalent consumer.
   **Positive requirement:** construct `Delta_src`, `V`, and `Omega` before moment comparison.
2. **Fixed finite spectrum.**  The formal finite-KMS obstruction excludes one finite system
   matching the entire source tower.
   **Positive requirement:** use either the singular global source carrier or independently
   source-produced finite blocks of growing width.
3. **Raw coefficient `ell^2`.**  Every uncensored meromorphic prime-window coefficient lies outside
   the ordinary Dirichlet--Hardy space; completing there deletes the Laurent boundary data.
   **Positive requirement:** use the pole-cancelled graph and retain its principal-part boundary
   coordinate.
4. **Diagonal prime damping.**  The Gamma diagonal fixes summability but scalar coherent summation
   creates cross-prime terms absent from the Euler trace.
   **Positive requirement:** preserve prime-channel resolution until the positive Gram is formed,
   then take its trace or source compression.
5. **Scale-free orientation.**  Orientation alone cannot pay a fixed archimedean budget under
   positive rescaling.
   **Positive requirement:** the exact Mellin counterterm and Gamma normalization must occur in
   the same defect identity as the von-Mangoldt channels.
6. **Ordinary circle positivity.**  The explicit positive analytic circle state is unconditional,
   but generic densities arbitrarily close to Haar have negative reflected Hankel directions.
   **Positive requirement:** `(5)` must perform source-specific positive radialization, not use
   density coercivity or Schur norm alone.
7. **Hidden divisor norm.**  Summing squared residues over Xi zeros would manufacture the desired
   sign.
   **Positive requirement:** residues may be used only after the source Gram and its bounded
   evaluation map have been constructed.

## Ranked research targets

1. **Global nonlocal completed quotient.**  Fixed prime packets satisfying finite-subproduct Euler
   norm law are now excluded even under arbitrary off-diagonal mixing and a fixed completed
   boundary.  Construct instead a global signed prime–Gamma object whose positive quotient is
   formed only after all Euler, Gamma, and polar modes have been combined.  Prove its positivity
   without target moments or zero locations, then prove `(22j)`.  On any hidden positive source,
   the resulting observable must be a target-shaped quantizer: every canonical thermal value has
   an uncountable positive-measure fibre with its forced divisor weight.  A cutoff-dependent fitted
   counterterm, target-fed quantile map, or chosen conditionally convergent prime order is not
   source-functorial evidence.
2. **Two-vector completed comparison.**  For `N=2`, identify three entries of that one source
   packet with `m_0,m_1,m_2` through the inverse-tilted central source relation.  This subsumes
   `(23)` without defining its square root from the determinant.
3. **Channel-resolved relative incidence.**  Construct the exact archimedean/boundary channel
   missing from the Gamma-damped Cauchy frame so that its reduced trace is the centered
   prime--Gamma source, not merely the absolute-Euler source.
4. **Finite centered Green square.**  Construct `C_X`, `P_X`, and `A_X` in `(18)` directly from the
   reduced finite prime--Gamma anomaly complex.  The skew-inverse, positive-square, Hodge
   complement, and trace-Hankel algebra are already formalized.
5. **Source-complex identification.**  Prove that the completed source-selection harmonic block
   is the positive unaugmented-simplex effective line.  This discharges `(22)` but does not replace
   the source value identity.
6. **Finite source trace comparison.**  Prove the entrywise limit `(21)` using the reduced
   Gauss--Ward identity and the formalized inverse-tilted central source identity.
7. **Arbitrary finite Gram value identity.**  The positive arbitrary-`N` source packet now exists;
   prove that its limiting entries are exactly `(10)`.  This is sufficient for RH and avoids a
   premature global completion.
8. **Singular boundary completion.**  Only if the finite packets reveal natural compatibility,
   construct `H_src` and prove `(5)`--`(6)`.  Bounded Laurent evaluation must follow from the
   pole-cancelled graph norm, not be assumed.
9. **HTGeometry abstraction.**  Extract a general theorem: a reflected hypertranscendental source
   constraint with a positive decimation defect and an exact completed incidence resolvent
   produces a positive cyclic state.  The zeta source is the pressure test, not the definition of
   the abstraction.
10. **No residual boundary charge.**  Prove that the finite two-boundary orthogonality survives the
    Euler limit and matches the causal/polar moments of the completed relative source.  This is a
    source-limit theorem; it must not be replaced by assuming the RH-equivalent divisor seam charge
    vanishes.  A grading-index identity alone is not sufficient.

## Gates

- [x] source-pure finite square-decimation identity formalized
- [x] forward/inverse Mellin residue orientation formalized
- [x] arbitrary positive moment representation to RH formalized
- [x] Euclidean spectral specialization without support assumptions formalized
- [x] fixed finite KMS realization of the complete tower excluded in Lean
- [x] channel-resolved Gamma-damped critical Cauchy domain formalized
- [x] inverse-tilted finite-prime/Gamma source reconstructed the complete central trace in Lean
- [x] every normalized prime--Gamma moment transferred to that explicit source germ
- [x] arbitrary cutoff-dependent finite positive certificates identified as sufficient
- [x] inverse centered scale generator identified as the forced reciprocal-square mechanism
- [x] finite skew-inverse Green square and trace-power Hankel positivity formalized
- [x] positive harmonic parity isolated as sufficient for graded-to-ordinary trace compression
- [x] canonical finite unaugmented-simplex harmonic line with positive parity formalized
- [x] all-depth strict orientation of each resolved von Mangoldt--Gamma anomaly atom formalized
- [x] all-coordinate anomaly factorization and common depth orientation formalized
- [x] finite radial all-depth Cauchy/Gauss--Ward Gram constructed from the actual anomaly
- [x] exact Cauchy numerator-to-anomaly equality formalized
- [x] canonical finite two-boundary balanced compression formalized
- [x] both boundary modes and pairings proved zero; balanced Gram positivity proved
- [x] cutoff-compatible affine boundary residual and positive prefix Grams formalized
- [x] arbitrary-order Hermite boundary divisor, pole normalization, and positive prefix Grams formalized
- [x] arbitrary-depth cofinal summability proved on paper
- [x] arbitrary-depth packet square summability formalized in Lean
- [x] finite-prefix Grams identified with a common infinite kernel and proved entrywise convergent
- [x] limiting finite packet Grams proved positive semidefinite
- [x] finite rational/log-order seam corrections excluded by the prime-log transport theorem
- [x] coefficientwise nonnegative Gamma/positive corrections proved unable to lower the canonical
      sharp-source critical abscissa
- [x] scalar Gamma-conductor completion excluded by divergent prime Schur capacity
- [x] diagonal positive-log Mellin unbalancing excluded by divergent resolved-prime energy
- [x] integral successor Dirichlet completion of every logarithmic jet formalized
- [x] mixed absolute summability and all-order positive successor Gram formalized
- [x] direct successor-Gram identification with the target Hankel section excluded in Lean
- [x] Euler-subset-natural off-diagonal channel-mixing unbalancing excluded in Lean, even with an
      arbitrary fixed Gamma/polar boundary vector
- [x] unrestricted observable carriers classified in Lean: their reporter pushforward is the
      canonical Xi law, every thermal node has an uncountable positive-measure fibre, and every
      countable-to-one reporter on the atomless theta-cusp source is excluded
- [ ] construct a genuinely global nonlocal signed prime–Gamma quotient whose positivity appears
      only after completion and is proved without target moments or zero locations
- [ ] construct its source-defined uncountable positive-measure fibre partition/correspondence
      without selecting Xi zeros or importing the target moment law
- [ ] formalize the positive mixed center-jet Gram of the infinite kernel
- [ ] couple the Gamma spectral clock and polar boundary modes with the prime anomaly kernel
- [ ] prove Euler-boundary causal/polar cancellation, including common-charge cancellation
- [ ] construct the common positive `2 x 2` source cutoff packet
- [ ] prove its three entrywise moment limits
- [ ] construct the finite skew-Hermitian centered Green square
- [ ] identify the actual completed source harmonic block with the positive effective line
- [ ] prove the finite reflected-scale Gram jet theorem for arbitrary cutoff
- [ ] prove the first source defect norm identity `(23)`
- [ ] construct the exact completed relative prime--Gamma incidence
- [ ] prove the arbitrary finite block identity `(8)`
- [ ] construct the global singular defect resolvent `(5)`--`(6)` if needed
- [ ] compose an unconditional proof of RH

## Log

- 2026-07-16 -- Created after the arbitrary-support Euclidean capstone and the exact BV
  reflection-decimation source law.  Infinite support was demoted from input to automatic output;
  the live carrier was isolated as a source-produced reflection-decimation defect resolvent.
- 2026-07-16 -- Closed the inverse-tilted finite-prime/Gamma central value relation in Lean.  The
  scale-character/moment-node mismatch forced replacement of raw dilation jets by the centered
  Green square `-C^(-2)`.  The new open core is a finite positive-parity Hodge--Green trace
  comparison, not a representing-measure or support theorem.
- 2026-07-16 -- Formalized the positive effective harmonic line of unaugmented simplex descent and
  the strict all-depth orientation of actual resolved von Mangoldt--Gamma anomaly atoms.  The
  exclusion gate now forbids reconstruction or source-effectivity from supplying positivity.  The
  live open core is the reduced Euler-boundary Gauss--Ward source identity, including cancellation
  of its independent first-moment charge anomaly.
- 2026-07-17 -- Corrected the cofinal boundary-jet route after the exact source audit.  The positive
  balanced Cauchy packet has inverse prime-log jets, whereas the reconstructed inverse-tilted
  Mellin germ has positive prime-log jets.  Undoing the boundary divisor is unbounded; finite-rank,
  scalar-conductor, and coefficientwise positive corrections are already excluded by formal
  theorems.  The open producer is therefore an infinite-rank channel-resolved unbalancing incidence
  which remains positive after completed Gamma/polar transport.  The bare comparison `(22j)` is not
  itself a source theorem.
- 2026-08-01 -- Closed the proposed off-diagonal escape under its finite-Euler source-functoriality
  requirement.  Exact subset energy forces zero real covariance between distinct prime outputs and
  divergent completed packet norms, even with an arbitrary fixed Gamma/polar boundary.  Also proved
  unrestricted positive carrier rigidity: every all-moment witness is the canonical compact atomic
  Xi-divisor measure, so moment indeterminacy supplies no alternative carrier.  The only survivor is
  a global signed boundary/domain defect formed before positivity; its resolvent-flux identification
  is the irreducible Weil/RH clause.
- 2026-08-01 -- Classified every deterministic observable on an arbitrary hidden positive source.
  Its pushforward is forced to the canonical Xi-divisor law, and each thermal value has an
  uncountable positive-measure source fibre.  Hence countable-to-one reporters on the atomless
  theta-cusp density cannot be the producer.  The surviving source problem is an explicit
  uncountable-to-one fibre quantization forced by prime--Gamma completion rather than encoded
  from zeros; this is another exact form of the same global Weil-positivity clause.
