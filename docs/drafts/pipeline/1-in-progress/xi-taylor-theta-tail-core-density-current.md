# Xi Taylor theta-tail core density current

- **ID:** `xi-taylor-theta-tail-core-density-current`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / DIRECT SOURCE PRODUCER
- **Scientific status:** `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Parent target:** `xi-taylor-oriented-finite-coefficient-sublinear-flux.md`
- **Statement:** Prove anisotropic sublinear upper current for the raw theta-tail/seam mixed
  correlation `(4)`.  The completed-source channel is an exact feedback copy of the next Xi
  Taylor section and supplies no independent positive term.

## Exact target

For a source-selected odd super-accurate schedule `D`, prove

```text
for every sigma with 0 < Re sigma < 1/2 and every epsilon > 0,
eventually in n,

J_(U_(D(k_n)))(z_n)
  < epsilon (n+1) |P_(2D(k_n)+3)(z_n)|^2,

k_n = xiCTaylorAnisotropicScheduleStage sigma n,
z_n = xiCTaylorAnisotropicCenteredPoint sigma n.
```

This is `XiCTaylorThetaTailCoreCurrentSublinearUpper D` in Lean.

Its exact logical strength is now formalized.  For every source-selected odd super-accurate
schedule `D`, Lean proves

```text
XiCTaylorThetaTailCoreCurrentSublinearUpper D <-> RiemannHypothesis.       (0)
```

The forward implication is the existing anisotropic pole-amplification gate.  For the reverse
implication, RH keeps `XiC` nonzero at the limiting centered point of each open left-strip fibre;
the Taylor value is then eventually bounded below, while the core value and derivative are bounded
above by Taylor super-accuracy and rapid decay of the explicit top defect.  Hence the core current
is `O(1)` and therefore `o(n)|P|^2`.  This reverse implication uses RH only as a logical audit and is
not an admissible producer for the open direction.  Equation `(0)` proves that any unconditional
estimate closing this card is itself a proof of RH, rather than a weaker finite approximation
lemma.

## Non-circularity boundary

No method class is excluded.  Any input must nevertheless prove a sign or cancellation for `(4)`
rather than restating the target Taylor current, assuming an RH-equivalent sign, or routing the
unknown Taylor section through an identity and calling the returned copy an error term.

## Exact source coordinate

Let

```text
rho(x) = 4 T''(x),
S_d(z,x) = sum_(k=0)^d (-1)^k z^(2k)x^(2k+2)/(2k+2)!,
H_d(z,x) = 1-(z^2+1/4)S_d(z,x).
```

Then `rho>0`, `integral rho=1`, and

```text
U_d(z)  = (1/2) integral rho(x) H_d(z,x) dx,
U_d'(z) = (1/2) integral rho(x) partial_z H_d(z,x) dx.       (1)
```

Consequently

```text
J_(U_d)(z)
 = (1/4) integral integral rho(x)rho(y) K_d(z;x,y) dx dy,    (2)

K_d(z;x,y)
 = (1/2) Im(
     partial_z H_d(z,x) conjugate(H_d(z,y))
     + partial_z H_d(z,y) conjugate(H_d(z,x))).
```

Equations `(1)` and `(2)` are proved on paper and in Lean.  They expose the exact correlation that
must cancel the positive-current atoms; positivity of `rho` alone cannot do so.

## Candidate cancellation

The shifted section satisfies the exact static relation

```text
partial_x^2 S_d(z,x) = C_d(z,x),
```

where `C_d` is the ordinary truncated cosine section.  Since `rho=4T''`, two integrations by parts
in either source variable replace `H_d` by `-(z^2+1/4)C_d` plus explicit seam terms.  The fully
integrated representation returns the already indefinite cosine two-point kernel.  The live
possibility is therefore the asymmetric or mixed representation obtained by integrating one
source variable at a time: its seam term and mixed `H_d/C_d` kernel must be tested together rather
than signed separately.

The exact one-variable identity, now proved in Lean, is

```text
integral rho(x) H_d(z,x) dx
 = 1 - 4(z^2+1/4) integral T(y) C_d(z,y)dy,                (3)

J_(U_d)(z)
 = (1/4) integral Im(rho(x) partial_z H_d(z,x))dx
   - integral integral rho(x)T(y)
       Im(partial_z H_d(z,x)
          conjugate((z^2+1/4)C_d(z,y)))dxdy.              (4)
```

The seam term in `(4)` is not disposable: the mixed term is a cross energy, not a square, and the
already proved Wigner--Eisenstein analysis shows that the corresponding ambient pair form is
indefinite.  Thus `(4)` is an exact coordinate but not yet a producer.

There is a distinct one-derivative polarization which retains a positive source without returning
immediately to the cosine kernel.  Define the raw-tail survival function

```text
eta(x)=-4T'(x).
```

Then `rho=-eta'`, `eta(0)=1`, and `eta(infinity)=0`.  A single integration by parts gives the exact
finite identity

```text
integral rho(x)H_d(z,x)dx
 =1+integral eta(x) partial_x H_d(z,x)dx,                 (4a)

partial_x H_d(z,x)
 =-(z^2+1/4) sum_(k=0)^d (-1)^k z^(2k)x^(2k+1)/(2k+1)!.
```

Thus the seam-compensated core is a constant plus a weighted truncated-sine transform.  Equation
`(4a)`, including integrability and both endpoint limits, is proved in Lean in
`XiCTaylorThetaTailSurvivalPolarization.lean`.  Commuting the source and spectral derivatives gives
the exact current polarization.  Put

```text
B_d(z)=integral eta(x) partial_x H_d(z,x)dx,
A_d(z)=integral eta(x) partial_x partial_z H_d(z,x)dx.
```

Then, with all differentiations, integrability claims, and endpoint limits proved in Lean,

```text
U_d(z)=(1/2)(1+B_d(z)),  U_d'(z)=(1/2)A_d(z),

J_(U_d)(z)
 =(1/4)Im A_d(z)+(1/4)Im(A_d(z) conjugate(B_d(z))).       (4b)
```

This is formalized in `XiCTaylorThetaTailSurvivalMixedCurrent.lean`.  It avoids the indefinite
cosine kernel, but it also shows that the seam is inseparable from the raw survival cross current:
`A_d` is the spectral derivative of `B_d`, so `(4b)` is an exact new source coordinate rather than
an independent positive correction.  The remaining producer must use an exact theta-specific
relation inside the full `eta`-weighted sine cross term.

The survival moments are not independent theta data.  A further exact integration by parts gives,
for every `m>=0`,

```text
(m+1) integral x^m eta(x)dx = integral x^(m+1) rho(x)dx. (4c)
```

Equation `(4c)` is formalized as `integral_pow_mul_thetaCuspTailSurvival_shift`.  Thus the survival
polarization reindexes the canonical density moments; any cancellation must use their full
cross-phase relation, not a new favorable moment sequence hidden in `eta`.

The reflection character nevertheless yields a non-generic positive completion remainder.  Put

```text
g(x)=exp(-x/2)-eta(x).
```

For every positive integer Gaussian atom, direct comparison of the first- and second-derivative
atom polynomials gives

```text
rho_n(x) >= (1/2)eta_n(x),  x>=0.
```

Hence `rho>=(1/2)eta`, the function `exp(x/2)eta(x)` decreases from one, and

```text
g(-x)=-g(x),  g(x)>=0 for x>=0.                          (4d)
```

These statements are formalized in
`XiCTaylorThetaTailCompletedSurvivalRemainder.lean`.  The exponential moments telescope against
the finite source derivative exactly:

```text
integral exp(-x/2) partial_x H_d(z,x)dx
 =(-4z^2)^(d+1)-1.
```

Combining this with `(4a)` gives the exact completed-survival coordinate

```text
integral rho(x)H_d(z,x)dx
 =(-4z^2)^(d+1)-integral g(x)partial_x H_d(z,x)dx.        (4e)
```

Equation `(4e)`, including the exponential moment evaluation and integrability, is formalized in
`XiCTaylorThetaTailCompletedSurvivalTransform.lean`.  It is not a positive-error decomposition:
the `g` transform cancels the explicit degree-`2d+2` monomial.  The live possibility is a
polarized energy in which the favorable monomial current absorbs the mixed `g` cross current
without replacing that cancellation by absolute values.

The remainder is itself the derivative of an exact completed theta potential.  Put

```text
p(x)=(1/2)exp(-x/2)-T(x).
```

The theta reflection and `(4d)` give

```text
p(-x)=p(x),  p(x)>=0 for x>=0,  p(x)->0,
p'(x)=-(1/4)g(x),
p''(x)-(1/4)p(x)=-Phi(x).                                (4f)
```

Thus the positive remainder is the decreasing derivative of the classical even completed-tail
potential; it is not a second independent source.  If

```text
G_d(z)=integral g(x) partial_x H_d(z,x)dx,
M_d(z)=(-4z^2)^(d+1),
```

then the exact finite value relation and its derivative are

```text
2U_d=M_d-G_d,
2U_d'=M_d'-G_d',

J_(U_d)(z)
 =(1/4) Im((M_d'(z)-G_d'(z)) conjugate(M_d(z)-G_d(z))).  (4g)
```

Here `G_d'` is obtained by differentiating the exact polynomial identity, so `(4g)` uses no
unproved differentiation under the integral.  Equations `(4f)`--`(4g)` are formalized in
`XiCTaylorThetaTailCompletedPotential.lean`.  They close the naive monomial-absorption route:
`G_d` cancels `M_d` at both value and derivative level, and for `|2z|>1` the two terms can each
grow exponentially with `d` while their difference remains the canonical core.  Bounding the
cross terms by their norms therefore destroys precisely the cancellation to be proved.  A
successful use of `g>=0` must furnish a signed polarization of the complete difference in `(4g)`;
positivity or monotonicity of the potential alone supplies no such sign.

These potential properties are rigorously insufficient even as a package.  Let `0<a<b`, `c>0`,
and take the positive even decreasing Gaussian mixture whose bilateral Fourier transform is

```text
K(z)=exp(-a z^2)+c exp(-b z^2).
```

Its zeros satisfy

```text
z^2=(log c-(2m+1)pi i)/(b-a),  m in Z,                  (4h)
```

and are nonreal; choosing `c=1` and `b-a>2pi` puts a pair in `0<|Im z|<1/2`.  Convolve this
source with the positive Green kernel `exp(-|x|/2)`.  The resulting potential `p` is positive,
even, decreasing on the positive half-line, tends to zero, and satisfies

```text
p''-(1/4)p=-k,  g=-4p'>=0.
```

Its Fourier transform is `K(z)/(z^2+1/4)`, so it retains every zero in `(4h)`.  Therefore
evenness, positive completion source, positive completed remainder, monotone potential, and the
exact Green relation `(4f)` do not imply the required orientation.  The remaining proof must use
an arithmetic value relation specific to the canonical theta sum inside the full polarization
`(4g)`.

There is a second finite value relation, also proved in Lean,

```text
z^2 S_d(z,x) = 1-C_(d+1)(z,x),
z^2 H_d(z,x) = (z^2+1/4)C_(d+1)(z,x)-1/4.                (5)
```

Equation `(5)` exposes the completion boundary `|Im z|=1/2` without division at `z=0`.  The live
residue is a completion-compensated cosine correlation.  A proof must orient this distinguished
canonical average; positivity of every cosine atom or of the ambient coefficient form is neither
true nor required.

The canonical density has the further exact completed-source split

```text
rho(x)=T(x)+4 Phi(x),
Phi(x)=T''(x)-(1/4)T(x),                                  (6)
```

where `Phi` is the even theta-cusp source.  The completed part is not an independent correction.
The exact finite transform and core identities are

```text
2 integral Phi(x) C_d(z,x) dx = P_(2d+1)(z),

z^2 [2 integral Phi(x) H_d(z,x) dx]
 = (z^2+1/4)P_(2(d+1)+1)(z) - (1/4)P_1(0),

z^4 [2 integral Phi(x) partial_z H_d(z,x) dx]
 =z^2(z^2+1/4)P'_(2(d+1)+1)(z)
   +(z/2)(P_1(0)-P_(2(d+1)+1)(z)).                       (7)
```

Thus substitution of `(6)` feeds the next canonical Taylor section directly back into the current.
Any attempted positive bound on the `Phi` term is circular.  The only unresolved producer is the
raw `T` cross correlation together with the seam in `(4)`.

The central completion seam point gives a genuine non-circular value relation:

```text
U_d(i/2)=1/2,
J_(U_d)(i/2)=-(1/2) A_d(1/4)<0,                           (8)
```

where `A_d=thetaCuspTailEvenPolynomial d` has strictly positive coefficients.  Equation `(8)` is
proved in Lean.  It signs only the single point `z=i/2`: on the rest of the horizontal line
`Im z=1/2`, the factor `z^2+1/4` does not vanish.  Thus `(8)` supplies no boundary-line control and
does not localize the positive-current obstruction by itself.

The exact coefficient telescope strengthens this isolated seam value in one genuine direction.
Writing `B_d(w)=1/2+(w-1/4)A_d(w)`, Lean now proves

```text
B_d(w)=M_(d+1)(w)+(1/4)a_(d+1)w^(d+1),
M_(d+1)(w)=sum_(k=0)^(d+1) mu_k w^k/(2k)!,              (8a)
```

where `mu_k>=0`, `mu_0,mu_1>0`, and `a_(d+1)>0`.  Consequently, for every `w>=0`,

```text
B_d(w)>0,  B_d'(w)>0,
J_(U_d)(iy)=-2y B_d'(y^2)B_d(y^2)<0  for y>0.           (8b)
```

Thus the full canonical value relations orient the entire positive imaginary axis, not merely
`i/2`.  This is stronger than positivity of the density and fails for a generic individual core
atom.  It still does not reach an anisotropic fibre with nonzero real part.  The exact polynomial
reflections are

```text
J_(U_d)(conjugate z)=-J_(U_d)(z),
J_(U_d)(-z)=-J_(U_d)(z),
J_(U_d)(-conjugate z)=J_(U_d)(z).                        (8c)
```

In particular reflection across the imaginary axis preserves the unknown current, so conjugate
mesh fibres reinforce rather than cancel each other.

The source reflection is equally exact.  With
`h(x)=(exp(x/2)-exp(-x/2))/2`, Lean proves

```text
T(-x)=T(x)+h(x),
rho(-x)=rho(x)+h(x),
(rho-T)(-x)=(rho-T)(x)=4 Phi(x).                         (8d)
```

This does not yield a full-line antisymmetrization: `h` grows exponentially on one end and its
pairing with a finite polynomial cosine section is not integrable.  Removing `h` leaves the even
completed source `4 Phi`, whose finite transform is the circular Taylor feedback `(7)`.

For every polynomial `P`, Lean also proves the exact value-coordinate identity

```text
d/dy |P(x+iy)|^2 = -2 J_P(x+iy).                           (9)
```

There is no hidden boundary parameter left in a higher integration-by-parts scheme.  The modular
reflection gives, for every odd `m`,

```text
Phi^(m)(0)=0,
T^(m+2)(0)=(1/4)T^m(0),
T^(2r+1)(0)=-4^(-(r+1)).                                  (8e)
```

These identities are proved in Lean.  They make every odd seam jet explicit, but repeated
integration by parts still terminates in the raw two-variable correlation `(4)` or in the
completed Taylor feedback `(7)`; the seam recurrence is therefore exact data, not a sign
producer.

The source dilation gives a further exact cancellation coordinate.  Put

```text
g(x)=rho(x)+x rho'(x),
s(x)=g(x)/rho(x)=1+x rho'(x)/rho(x).
```

The finite section and core satisfy the Euler identities

```text
x partial_x S_d=z partial_z S_d+2S_d,
z partial_z H_d=x partial_x H_d+(1/2)S_d.                 (8f)
```

Since `g=(x rho)'`, integration by parts gives

```text
integral g=0,
integral x^m g(x)dx=-m integral x^m rho(x)dx,

(z^2+1/4)z U_d'(z)
 =-(1/2)(z^2+1/4) integral g(x)H_d(z,x)dx
   +1/4-(1/2)U_d(z).                                     (8g)
```

Equations `(8f)`--`(8g)`, including all cusp and seam boundary terms, are proved in Lean.  They
use the full canonical density and expose a literal mean-zero score covariance.  The score does
not supply independent moments: its entire moment sequence is the Euler multiple `-m` of the
original density moments.  Moreover the naive Chebyshev orientation of the core phase is false.
For `d=2`, `z=2+i/5`, the ordered cross determinant

```text
Im(H_d(z,x) conjugate(H_d(z,y)))
```

is negative at `(x,y)=(1/10,0)` and positive at `(11/5,9/10)`; both strict rational evaluations
are certified in Lean.  Hence monotonicity of the scalar score, even if established, cannot sign
the covariance pointwise.  A surviving score proof must retain the complete weighted integral
and obtain cancellation across the phase reversals.

The whole real boundary has a second exact value relation.  Together with `(8b)` this signs the two
coordinate axes, but the anisotropic target lies on general vertical fibres.  Since `U_d` has real
coefficients,

```text
J_(U_d)(x)=0,

J_(U_d)(x+iy)
 = integral_(0..y) [Re(U_d'' conjugate(U_d))-|U_d'|^2](x+it)dt.  (10)
```

Equation `(10)` is proved in Lean.  It is the genuine boundary-to-interior formula on every
anisotropic fibre.  In the density coordinate its integrand is

```text
Re(U_d'' conjugate(U_d))-|U_d'|^2
 = (1/4) integral integral rho(a)rho(b) L_d(z;a,b) da db,

L_d(z;a,b)
 = (1/2) Re(
     partial_z^2 H_d(z,a) conjugate(H_d(z,b))
     + partial_z^2 H_d(z,b) conjugate(H_d(z,a))
     - 2 partial_z H_d(z,a) conjugate(partial_z H_d(z,b))). (11)
```

Thus the narrowed target is an integrated upper bound for the canonical complex Laguerre defect
`(11)`, not pointwise positivity of `rho`.  In the raw-tail coordinate

```text
w=-z^2,
B_d(w)=1/2+(w-1/4)A_d(w),
U_d(z)=B_d(-z^2),

Re(U_d'' conjugate(U_d))-|U_d'|^2
 = -2 Re(B_d' conjugate(B_d))
   -4 Re(w B_d'' conjugate(B_d))
   -4 |z|^2 |B_d'|^2.                                   (12)
```

The last term in `(12)` is favorable.  The open producer is a cancellation estimate for the first
two raw moment terms after integrating over `0<=t<=Im z`; imposing their pointwise sign would be a
complex Laguerre/anti-Herglotz condition and would simply repackage the target.

## Dominant first density atom

The exact density has a sharper source split than undifferentiated theta positivity.  If

```text
T_1(x)=exp(x/2-pi exp(2x)),
rho_1(x)=4T_1''(x),
```

then direct evaluation of the endpoint derivative gives

```text
integral_(0..infinity) rho_1(x)dx
  = -4T_1'(0) = (8pi-2)exp(-pi),                          (12a)
```

while the sum of all `n>=2` density atoms has mass
`1-(8pi-2)exp(-pi)`.  Thus the first differentiated theta atom carries more than `0.999` of the
canonical probability mass.  This does not by itself orient the core: the finite integrated
`rho_1` cores already have nonreal zero pairs from degree two, so neither pointwise positivity nor
dominant mass yields finite hyperbolicity.  `[CONJECTURE]` The only live first-atom use is a
compact-window estimate in which the modular seam and the `n>=2` tail are retained together and
the escaping finite-section zero pairs are controlled uniformly away from the window.  No such
oriented estimate is yet proved.

The density domination itself is now quantitative and formalized.  For `x>=0` and `n>=1`, Lean
proves

```text
rho_n(x) <= 5 n^4 exp(-pi(n^2-1)) rho_1(x).              (12b)
```

The proof uses the exact quartic atom polynomial
`P_2(u)=1/4-6pi u^2+4pi^2u^4`, the bounds
`pi^2u^4<=P_2(u)<=5pi^2u^4` for `u>=1`, and Gaussian separation.  Equation `(12b)` controls every
positive moment of the higher-atom tail by the corresponding first-atom moment.  It does not
control an oscillatory transform relative to its value: near a cancellation of the first-atom
transform, the absolute majorant furnished by `(12b)` remains positive.  Thus a Rouché/current
argument would additionally require an expanding zero-free or quantitative phase region for the
incomplete-gamma theta truncations.  That is not an independent known input: Haglund's truncation
program isolates precisely such an expanding-region conjecture and observes that it would imply
RH.  Dominant-atom mass and pointwise domination are therefore certified infrastructure, not the
missing oriented producer.

The density atoms do have one further exact arithmetic relation.  For every `n>=1`, every
polynomial Gaussian profile `P`, and every real `x`,

```text
Atom_P(n,x)=n^(-1/2) Atom_P(1,x+log n),
rho_n(x)=n^(-1/2) rho_1(x+log n),

rho(x)=sum_(n>=1) n^(-1/2) rho_1(x+log n),

integral_(0..infinity) rho_n(x)K(x)dx
 =n^(-1/2) integral_(log n..infinity)
    rho_1(u)K(u-log n)du.                                  (12c)
```

Equation `(12c)`, including the shifted-half-line pairing for an arbitrary complex test function
`K`, is proved in Lean.  It identifies the non-generic datum that an eventual
cancellation theorem must retain: one fixed differentiated Gaussian profile sampled on the
logarithmic integer lattice.  Replacing the translates by their masses or absolute majorants
removes the phases `z log n` and cannot control the mixed current.  The unresolved finite problem
can therefore be restated as an upper estimate for the complete weighted pair interference of
these arithmetic translates.

The sum--integral exchange and the full ordered pair expansion are now also exact.  Put

```text
R_(m,n)(z;x,y)
 =rho_m(x)rho_n(y)K_d(z;x,y),

Q_(m,n)(z;x,y)
 =rho_1(x+log m)rho_1(y+log n)K_d(z;x,y).
```

Lean proves, with the full symmetric correlation as the `L^1` majorant,

```text
integral x^r rho(x)dx
 =sum_(n>=1) integral x^r rho_n(x)dx,

J_(U_d)(z)
 =(1/4)sum_(m,n>=1) integral integral R_(m,n)(z;x,y)dxdy
 =(1/4)sum_(m,n>=1)(mn)^(-1/2)
    integral integral Q_(m,n)(z;x,y)dxdy.                 (12d)
```

Thus `(12d)` is not a formal expansion of a conditionally convergent object: the ordered pair
series is obtained by an explicit Bochner `L^1` interchange.  At a fixed translated profile
coordinate `u`, only the integers `n<exp u` occur after shifting the lower endpoints, so the
infinite translate sum becomes a finite Dirichlet packet.  Two integrations by parts against
`rho_1=4T_1''` produce jump terms at `u=log n`; the value packet jumps by
`n^(-1/2)H_d(z,0)=n^(-1/2)`, while its first source derivative has no jump.  Summing those jumps
reconstructs the seam in `(3)`--`(4)`.  Hence ordinary coordinatewise integration by parts in the
packet form is equivalent to the already indefinite mixed identity and supplies no new sign.

There is nevertheless an independent signed polarization of the *full square-index packet*.
For one ordered atom pair put

```text
X=pi m^2 exp(2x),  Y=pi n^2 exp(2y),
w=exp(x/2+y/2-X-Y),
Q=X+Y-3/4-12XY,  L=1-16XY.
```

The exact value polynomial of `rho=4T''` satisfies the algebraic identity

```text
(1-24X+16X^2)(1-24Y+16Y^2)=16Q^2-8L^2,               (12d.1)
rho_m(x)rho_n(y)=w(16Q^2-8L^2).                       (12d.2)
```

Both channels in `(12d.2)` are pointwise nonnegative before the displayed subtraction.  Summing
over all ordered positive square indices is justified by the existing absolute atom-pair
expansion, so Lean proves

```text
rho(x)rho(y)=sum_(m,n>=1) w_(m,n)(x,y)
  (16Q_(m,n)(x,y)^2-8L_(m,n)(x,y)^2),                 (12d.3)

J_(U_d)(z)=(1/4)sum_(m,n>=1) integral integral
  w_(m,n)(16Q_(m,n)^2-8L_(m,n)^2)K_d(z;x,y)dxdy.      (12d.4)
```

The polarization also has a genuinely arithmetic swap form.  In diagonal coordinates
`x=u+v`, `y=u-v`, write

```text
A=pi exp(2u)(m^2+n^2)cosh(2v),
B=pi exp(2u)(m^2-n^2)sinh(2v),
P=pi^2 exp(4u)m^2n^2,
C=A-3/4-12P,  L=1-16P.
```

Pairing `(m,n)` with `(n,m)` gives the exact signed hyperbolic packet

```text
rho_m(u+v)rho_n(u-v)+rho_n(u+v)rho_m(u-v)
 =16 exp(u-A)
   ((C-B)^2 exp(B)+(C+B)^2 exp(-B)-L^2 cosh(B)).       (12d.5)
```

Equations `(12d.1)`--`(12d.4)` are formalized in
`XiCTaylorThetaTailSquareIndexPolarization.lean`; `(12d.5)` follows from them by the square-index
swap and the exponential addition law.  This relation is specific to the full canonical second
density: replacing `4T''` by a generic positive source destroys the two exact forms `Q` and `L`.
It exposes the required cancellation channel without using Xi divisors, a limiting measure, or a
sign of a Cauchy sequence.  The remaining sign problem is precise: the same oriented kernel
`K_d` multiplies both squares, so pointwise comparison of the two source channels is not an
oriented-current comparison.  A successful estimate must couple the swap in `(12d.5)` to the
`v`-orientation of `K_d`, or show that the uncoupled top edge is `o(d)` on the anisotropic mesh.

The multiples-row identity yields a second polarization which is global and cofinal rather than
atomwise.  Let `S` be the critical dyadic shift

```text
(Sf)(x)=2^(-1/2)f(x+log 2).
```

The exact even-index row is `E=S rho`; hence the odd row and parity wavelet are

```text
O=(I-S)rho,  V=(2S-I)rho,
V(x)=sqrt(2)rho(x+log 2)-rho(x).                         (12d.6)
```

At dyadic depth `k`, put `F_k=S^k rho`, `O_k=F_k-F_(k+1)`, and
`V_k=2F_(k+1)-F_k`.  The row `F_k` is exactly the sum of the density atoms whose square index is
divisible by `2^k`; `O_k` is therefore the row of exact `2`-adic valuation `k`.  The elementary
Haar identity

```text
F_k(x)F_k(y)
 =2O_k(x)O_k(y)-V_k(x)V_k(y)+2F_(k+1)(x)F_(k+1)(y)
```

telescopes with its exact arithmetic weights to

```text
rho(x)rho(y)
 =sum_(0<=k<N) [2^(k+1)O_k(x)O_k(y)-2^k V_k(x)V_k(y)]
  +2^N F_N(x)F_N(y).                                    (12d.7)
```

Lean proves the multiples-row interpretation, every finite identity `(12d.7)`, and its exact lift
through `K_d` to `J_(U_d)`.  The remainder is a single row translated by `N log 2` toward the
Gaussian cusp.  Lean proves the explicit bound, for `x>=0` and
`q=exp(-pi/2)<1`,

```text
0<=F_N(x)<=C_x 2^N q^(2^N),
0<=2^N F_N(x)F_N(y)<=C_(x,y) 2^(3N)q^(2^(N+1))->0.      (12d.7a)
```

The top row is now eliminated at the integrated current level, not merely pointwise.  Put

```text
M_(m,N)=integral_(0..infinity) x^m F_N(x)dx.
```

Lean proves every fixed moment is integrable and satisfies an explicit Gaussian bound tending to
zero, and more sharply

```text
2^N M_(m,N)M_(n,N) -> 0                                 (12d.7b)
```

for every fixed `m,n`.  Since both the finite core atom and its spectral derivative are finite
linear combinations of source powers, product-measure factorization gives the exact identity

```text
integral integral 2^N F_N(x)F_N(y)K_d(z;x,y)dxdy
 =Im(2^N D_(d,z,N) conjugate(A_(d,z,N))) -> 0,           (12d.7c)
```

where `A_(d,z,N)` and `D_(d,z,N)` are their explicit finite moment packets.  Thus no dominated-
convergence or degree-uniform top-row hypothesis is needed: for each scheduled finite pair
`(d,z)`, the exact Haar identity permits choosing the dyadic depth after `(d,z)`.  The finite Haar
sum is still not oriented: each parity wavelet has bilateral Mellin factor
`(2^(1-s)-1)zeta(s)` and therefore retains the nontrivial Xi factor.  Dropping the negative Haar
currents would silently assume their sign.  The live theorem is consequently narrower: prove a
joint upper estimate for the signed *finite sum* in `(12d.7)`; its explicit top row has already
been removed without a sign assumption.  No termwise positivity statement is available.

The parity and odd layers also satisfy the exact Poisson reflection required for a possible joint
estimate.  With `w=2^(-1/2)` and
`R(x)=(exp(x/2)-exp(-x/2))/2`, Lean proves

```text
V(-x)=2w O(x-log 2)+2w R(x-log 2)-R(x).                 (12d.8)
```

Thus the coefficient ratio in `(12d.7)` is exactly the square of the reflection amplitude:
`(2w)^2=2`.  After reflection, the positive exact-valuation square and the negative parity square
therefore cancel at the source-amplitude level; only a translation and the two completion
characters remain.  The relation persists at every arithmetic depth, but its displacement grows.
Put

```text
a=2w=sqrt(2),  ell_k=(2k+1)log 2,
D_k(x)=2^(-k/2)[a R(x-(k+1)log 2)-R(x-k log 2)]
      =-(1/2)exp(-x/2).
```

The exact rescalings `O_k(x)=2^(-k/2)O(x+k log 2)` and
`V_k(x)=2^(-k/2)V(x+k log 2)` give

```text
V_k(-x)=a O_k(x-ell_k)+D_k(x),                            (12d.8a)

2^(k+1)O_k(x-ell_k)O_k(y-ell_k)-2^k V_k(-x)V_k(-y)
 =-2^k[a O_k(x-ell_k)D_k(y)
       +a D_k(x)O_k(y-ell_k)+D_k(x)D_k(y)].               (12d.8b)
```

Lean proves both formulas.  Equation `(12d.8b)` is the independent arithmetic signed
polarization of the full square-index translate packet: the two RH-bearing square channels
disappear algebraically.  The growing completion character cancels as well: the sole surviving
character is the universal decaying mode `-exp(-x/2)/2`, independent of `k`.  Thus `(12d.8b)`
consists of two explicit odd-row/decaying-character cross terms and a negative radial source square
`-2^(k-2)exp(-(x+y)/2)`.  The latter is not favorable by itself: its finite-core transform has
strictly negative current in the upper half-plane, so the negative source coefficient contributes
positive upper current.  This is stronger than the atomwise Lorentz polarization because it
cancels the complete exact-valuation/parity pair before any sign is taken.

The universal character can itself be removed without an estimate.  For every finite coefficient
packet `(c_k)` satisfying `sum_k c_k=0`, Lean proves

```text
sum_k c_k V_k(-x)
 =sqrt(2) sum_k c_k O_k(x-(2k+1)log 2),                  (12d.8c)

[sum_k c_k V_k(-x)][sum_k c_k V_k(-y)]
 =2[sum_k c_k O_k(x-(2k+1)log 2)]
    [sum_k c_k O_k(y-(2k+1)log 2)].                     (12d.8d)
```

This is a completion-free signed polarization of an arbitrary balanced finite square-index
packet.  It is independent of Xi values and divisor data.  Its remaining difficulty is geometric:
the different arithmetic depths carry different shifts, so the positive-half-line current does
not identify the right side of `(12d.8d)` with the diagonal Haar form in `(12d.7)`.

The whole finite parity diagonal can nevertheless be resolved into balanced packets.  If
`w_k=2^k` and `W_N=sum_(k<N)w_k`, the weighted-variance identity gives

```text
2W_N sum_(k<N)w_k V_k(x)V_k(y)
 =2[sum_(k<N)w_k V_k(x)][sum_(k<N)w_k V_k(y)]
  +sum_(i,j<N)w_iw_j[V_i(x)-V_j(x)][V_i(y)-V_j(y)],      (12d.8e)

sum_(k<N)2^k V_k(x)=2^N F_N(x)-rho(x).                  (12d.8f)
```

Lean proves `(12d.8e)`--`(12d.8f)`.  Every double-sum term is a completion-free balanced packet
covered by `(12d.8c)`--`(12d.8d)`.  The entire non-balanced direction has rank one and is exactly
`2^N F_N-rho`; no hidden completion mode remains.  Since `F_N` is the already controlled top row,
the unresolved orientation is compressed to transporting the pairwise shifted odd packets through
the finite core kernel and handling the single reappearing full-density rank-one term.  The latter
shows why the variance identity alone is not a proof: moving it to the left rescales the original
current rather than assigning it a sign.

There is now a sharper telescoping identity that bypasses the pairwise variance expansion.  Put
`L=log 2`, `D_k=thetaSquareIndexDyadicDensity k`, and keep `ell_k=(2k+1)L`.  Lean proves

```text
sum_(k<N) 2^k 2^(-1/2) O_k(x-ell_k)
 =1/2[2^N D_N(x-2NL)-rho(x)].                            (12d.8g)
```

Every intermediate translated odd row cancels.  Combining `(12d.8g)` with the reflected
one-layer polarization `(12d.8b)` gives the complete pointwise diagonal

```text
sum_(k<N){2^(k+1)O_k(x-ell_k)O_k(y-ell_k)
          -2^k V_k(-x)V_k(-y)}
 =2^(N-1)[D_N(x-2NL)e^(-y/2)+e^(-x/2)D_N(y-2NL)]
  -1/2[rho(x)e^(-y/2)+e^(-x/2)rho(y)]
  -(2^N-1)/4 e^(-(x+y)/2).                               (12d.8h)
```

Thus the conjectured cancellation of the *intermediate* fixed-half-line seams is exact.  It does
not remove the RH-bearing direction: it concentrates it in the single remote row
`D_N(x-2NL)`.  That row must be retained together with the density cross and the elementary
exponential square.  Separating them is invalid: before their pointwise cancellation the reflected
top and completion pieces are not individually integrable.  Equations `(12d.8g)`--`(12d.8h)` are
formalized as `thetaSquareIndexDyadicShiftedOddLayer_weightedSum_eq_topDifference` and
`thetaSquareIndexDyadicHaarLayer_reflected_sum_eq_topDifference`.

It is not yet the current theorem.  Equation `(12d.8h)` has replaced all layerwise seams by the
single remote translate `D_N(x-2N log 2)`.  Transporting that row to the already controlled
positive top row `D_N(x)` sweeps one interval of length `2N log 2`, and `H_d(z,x+2N log 2)` is not
equal to `H_d(z,x)`: its finite cosine translation mixes the even and odd Taylor sections.  The
next exact gate is therefore to polarize this one two-component finite translation while retaining
the two cross terms and exponential square in `(12d.8h)`.

The infinite-phase part of that gate is now exact in Lean.  For
`p_a(z)=exp(iaz)` and any value/derivative pair `(F,F')`,

```text
Im(p_a(F'+iaF) conjugate(p_a F))
 =|p_a|^2 (Im(F' conjugate(F))+a|F|^2).                 (12d.9)
```

Thus a genuine logarithmic translation contributes only the fixed drift `a|F|^2`, which is
automatically sublinear after division by the mesh resolution.  The sole unresolved part is now
the finite-section translation defect: the terms lost when `exp(iaz)` and the translated source
transform are both truncated to the canonical degree schedule.  Controlling that defect requires
the exact triangular cosine/sine coefficient relation, not another source positivity estimate.

That triangular relation is now exact on paper and in Lean.  Write

```text
C_d(z,x)=sum_(0<=j<=d) (-1)^j (zx)^(2j)/(2j)!,
S_d(z,x)=sum_(0<=j<d)  (-1)^j (zx)^(2j+1)/(2j+1)!.
```

Then there is a unique top-edge polynomial `E_d(z;x,a)` such that

```text
C_d(z,x+a)=C_d(z,x)C_d(z,a)-S_d(z,x)S_d(z,a)-E_d(z;x,a). (12d.9a)
```

It has no odd coefficients and no even coefficient through degree `2d`.  More precisely, for
`d<r<=2d`,

```text
[z^(2r)]E_d=(-1)^r(
  sum_(p+q=r, p,q<=d) x^(2p)a^(2q)/((2p)!(2q)!)
 +sum_(p+q=r-1, p,q<d) x^(2p+1)a^(2q+1)/((2p+1)!(2q+1)!)).  (12d.9b)
```

For `r<=d`, the unrestricted even--even and odd--odd binomial splits add to
`(x+a)^(2r)/(2r)!`; this is the exact cancellation that removes the entire low triangle.  Hence,
for `x,a>=0`,

```text
|E_d(z;x,a)|
 <= sum_(r>d) (|z|(x+a))^(2r)/(2r)!,                    (12d.9c)
|partial_z E_d(z;x,a)|
 <= (x+a) sum_(r>d) (|z|(x+a))^(2r-1)/(2r-1)!.         (12d.9d)
```

The completion-compensated core therefore obeys the exact two-component law

```text
z^2 H_d(z,x+a)
 =(z^2+1/4)(C_(d+1)(z,x)C_(d+1)(z,a)
            -S_(d+1)(z,x)S_(d+1)(z,a)
            -E_(d+1)(z;x,a))-1/4.                     (12d.9e)
```

Lean proves `(12d.9a)` and `(12d.9e)` in
`XiCTaylorThetaTailFiniteTranslation`; the formal top edge is defined as the product minus its
power-series truncation and is proved coefficientwise zero below the cutoff, with the corresponding
one-degree-lower derivative support law.  `XiCTaylorThetaTailFiniteTranslationCurrent` also proves
the exact oriented-current subtraction formula, retaining both mixed value--derivative currents and
the edge self-current.  This completes the algebraic part of the requested finite translation
theorem.  It does **not** complete the current estimate: the remaining gate is to prove that exact
three-term edge current has integrated sum `o(n)|P_(2d+3)(z_n)|^2` on the anisotropic mesh.
Estimating its value and derivative factors separately before the signed Haar summation would
discard exactly the cancellation required near scheduled small values of `P`.

The raw-tail moment estimate needed for the edge is now also formal.  The explicit Gaussian tail
has every prescribed natural exponential rate: for each integer `p>0` there is `A_p<infinity`
such that, for every `m>=0`,

```text
(1/m!) integral_(0..infinity) x^m |T(x)| dx
 <= A_p p^(-(m+1)).                                      (12d.9f)
```

Lean proves `(12d.9f)` in `XiCTaylorThetaTailFiniteTranslationBounds`.  The same module now
combines the exact shifted gamma moment with the arbitrary exponential decay of `T''` and proves
the stronger density-integrated bounds below.  If `|z|<=R`, `p>0`, `a>=0`, and
`A_(p,R)=thetaCuspTailDerivativeNatExpConstant(2,p+R)`, then

```text
integral |rho(x)| |E_d(z;x,a)| dx
 <=12 A_(p,R) R^(2d+1)/p^(2d+2) exp((p+R)a),

integral |rho(x)| |partial_z E_d(z;x,a)| dx
 <=12(2d+1)A_(p,R) R^(2d+1)/p^(2d+2) exp((p+R)a)
   +8(2d+2)A_(p,R) R^(2d+2)/p^(2d+3) exp((p+R)a).        (12d.9g)
```

The proof bounds the entire edge before expanding its source/shift bidegrees.  The finite phase
product differs from the full exponential product by three factorial tails; its spectral
derivative differs by three order-`2d+1` and two order-`2d+2` tails.  The exact formula

```text
integral_0^infinity (x+a)^N exp(-p x) dx
 =sum_(m<=N) binom(N,m)a^(N-m)m!/p^(m+1)
 <=N!/p^(N+1) exp(p a)
```

then cancels the Taylor factorial without separating the mixed terms.  Thus, after choosing
`p>R`, `(12d.9g)` decays geometrically in `d` with only `exp((p+R)a)` translation loss.  In
particular, if `d_n>=n` and `a_n=O(n^(1/4))`, it is smaller than every inverse power of `n`.

`[CONJECTURE]` The exact diagonal should now be taken at Haar depth
`N_n=floor(n^(1/4))`, not after an unrestricted fixed-`(d,z)` limit.  The critical rescaling
cancels the factors `2^k` against the two depth-`k` source amplitudes.  Hence the untruncated phase
drifts in the finite diagonal have total size at worst `O(N_n^3)|P|^2=o(n)|P|^2` (the cubic count
allows the pairwise balanced-packet decomposition), while every displacement is at most
`(2N_n+1)log 2`.  Bound `(12d.9g)` then makes the complete translation edge exponentially small
because every admissible odd schedule has `d_n>=n`.  The explicit Gaussian formula also gives a
degree-uniform top-row bound by dominating all finite cosine/sine sections by `exp(Rx)` and using
an exponential decay rate for `rho` larger than `R`; this makes the depth-`N_n` row smaller than
every inverse power of `n`.  What remains before promotion is the exact integrated bookkeeping:
prove that no unbalanced seam term survives when `(12d.9g)` is inserted into the formal balanced
Haar packets.  The numerical check of the raw-tail edge shows the predicted exponential onset,
including on a larger bounded fibre where the edge first grows for small degrees and then decays.

The degree-uniform top-row assertion in that paragraph is now formal, without dominated
convergence.  For `||z||<=r`, put

```text
A_r=4 thetaCuspTailDerivativeNatExpConstant(2,r+2),
q(z)=||z^2+1/4||,  s_(r,k)=exp(-(r+2)k log 2).
```

Lean proves, uniformly in the finite cutoff `d`,

```text
||<F_k,H_d>|| <= A_r s_(r,k) (1/2+q(z)/4),
||<F_k,partial_z H_d>||
  <= A_r s_(r,k) (||z||/2+3q(z)/8),                    (12d.9h)
```

and hence the absolute integrated Haar top-row current is bounded by

```text
2^k [A_r s_(r,k)]^2
 (1/2+q(z)/4)(||z||/2+3q(z)/8).                        (12d.9i)
```

The proof first establishes the cutoff-free pointwise envelopes

```text
||H_d(z,x)|| <= (1+q(z)x^2)exp(||z||x),
||partial_z H_d(z,x)||
 <= (2||z||x^2+q(z)x^3)exp(||z||x),
```

then pairs them with the arbitrary-rate exact bound for the translated density.  Since `(12d.9i)`
decays like `exp(-(2r+3)k log 2)`, the cofinal top row is super-polynomially small at
`k=floor(n^(1/4))`, independently of the scheduled Taylor degree.  These theorems are formalized
in `XiCTaylorThetaTailFiniteTranslationTopRow.lean`.

There is, however, a separate fixed-half-line translation seam which must not be conflated with
the finite Taylor top edge.  Let `F,F'` be the positive-half value and spectral derivative before
translation, and let `J_a,J_a'` be the value and derivative of the interval swept across the fixed
boundary.  The exact translated pair is

```text
p_a(F+J_a),
p_a(F'+J_a'+ia(F+J_a)).
```

Therefore the phase-current identity gives

```text
Q(p_a(F+J_a))=|p_a|^2[
  Q(F)+Q(J_a)
  +Im(F' conjugate(J_a))+Im(J_a' conjugate(F))
  +a|F+J_a|^2].                                        (12d.9j)
```

Lean proves `(12d.9j)` as `orientedPhaseCurrent_add_boundary_identity`.  The existence and exact
projection-commutator form of `J_a` were already formalized in `XiThetaLogTranslationSeam.lean`
and `XiThetaBoundaryCoboundary.lean`.  Thus the bare phase theorem does not by itself reduce the
untruncated fixed-half-line transport to `a|F|^2`: the seam self-current and two mixed currents
remain.  Equation `(12d.8h)` now performs the complete signed Haar summation: all intermediate
`J_a` terms cancel, but their total is not the already discharged positive cofinal row.  It is the
remote row `D_N(x-2N log 2)` coupled to the original-density/exponential cross and the negative
exponential square.  The sharpened open gate is to orient this **combined three-term current**
without separating its nonintegrable reflection pieces.  Once that untruncated identity is
controlled, `(12d.9g)` makes its finite Taylor translation edge the sole analytic remainder.

`[CONJECTURE]` The remaining arithmetic possibility is a *polarized jump energy*: integrate in a
diagonal or difference coordinate before resolving the jumps, so that paired jumps at
`(log m,log n)` contribute a square or a summable top-edge defect rather than the asymmetric seam.
Any viable identity must be checked against the exact phase reversals in `(8i)` and must not
replace the off-diagonal pair current by its diagonal part.

The diagonal-coordinate differentiation itself is exact but does not produce that square.  Put

```text
x=u+v,  y=u-v,
R(u,v)=T(u+v)T(u-v),
Box=partial_u^2-partial_v^2.
```

Then direct differentiation gives

```text
Box R=4T'(x)T'(y),
Box^2 R=16T''(x)T''(y)=rho(x)rho(y).                    (12d')
```

The positive quadrant becomes the characteristic cone `u>|v|`, and `dx dy=2 du dv`.  Thus the
pair source is a literal square of the wave operator.  Its characteristic Green boundary is,
however, exactly the two original seams `x=0` and `y=0`.  Using
`H_d(z,0)=1`, `partial_x H_d(z,0)=0`, `T'(0)=-1/4`, and decay at infinity,
the twice-integrated value is again

```text
integral rho(x)H_d(z,x)dx
 =1-4(z^2+1/4)integral T(x)C_d(z,x)dx.
```

Hence the cone Green formula returns `(3)`--`(4)`: the bulk is the same indefinite cosine cross
current and the null-boundary flux is the same seam.  Fourier transformation in `v` makes the
bulk wave symbol a nonnegative square, but it acts on the sign-changing theta Wigner slice; it
does not make the mixed current a squared norm.  Equation `(12d')` is proved on paper and retires
the unqualified diagonal-wave-square route.  A live polarized-jump theorem would need an
additional arithmetic boundary relation not contained in `rho=4T''` or in the wave factorization.

## Two-endpoint Prouhet prefix packet

There is an exact finite arithmetic packet which simultaneously preserves a Haar-prefix identity,
cancels its half-exponential square, and annihilates an arbitrarily high finite translation edge.
Put

```text
q=2^(-1/2),
B_m(X)=product_(r<m)(1-X^(2^r)).
```

For every `N,m` there is a unique affine factor `alpha+beta X` such that

```text
A_(N,m)(X)=B_m(X)(alpha+beta X),
A_(N,m)(q)=1,
A_(N,m)(q^(-1))=2^(-N).                                (12d.9k)
```

The interpolation is nonsingular because `B_m(q)` and `B_m(q^(-1))` are nonzero.  If
`A_(N,m)(X)=sum_j a_j X^j` and `c_j=a_j q^j`, then `(12d.9k)` is exactly

```text
sum_j c_j=1,
sum_j c_j 2^j=2^(-N),
sum_j c_j(2^(N+j)-1)=0.                                (12d.9l)
```

Consequently a `c_j`-weighted combination of the exact Haar-prefix identities at depths `N+j`
still has coefficient one on the original core current, while the entire elementary square in
`(12d.8h)` cancels rather than being estimated.

Every factor of `B_m` is divisible by `X-1`, so

```text
(X-1)^m divides A_(N,m)(X).                             (12d.9m)
```

Equivalently, for every polynomial `p` of degree `<m`,

```text
sum_j a_j p(N+j)=0.                                    (12d.9n)
```

The remote-row amplitude in the same prefix combination is

```text
c_j 2^((N+j)/2)=2^(N/2)a_j.                            (12d.9o)
```

Thus `(12d.9n)` applies directly to every finite cosine--sine translation defect once `m` is
larger than its degree.  No estimate of that edge is needed.  The endpoint identities,
nonvanishing of the two binary products, and divisibility `(12d.9m)` are formalized in
`XiCTaylorThetaTailProuhetPacket.lean`.

The full converse coefficient statement is now formal.  Divisibility by `(X-1)^m` kills every
binomial moment and, by triangular falling-factorial induction, every ordinary power moment below
`m`.  Expanding an arbitrary polynomial in powers then proves `(12d.9n)` exactly, including the
base-depth shift `N+j`.  The reusable theorems are in
`HTGeometry/ProuhetMomentDivisibility.lean` and their two-endpoint specialization is in
`XiCTaylorThetaTailProuhetPacket.lean`.

The hoped-for removal of the whole fixed-half-line seam by this packet is false.  Put

```text
g(x)=rho(x)-exp(-x/2)/2.
```

The exact reflection law gives `g(-x)=g(x)`.  If `R_k` denotes the positive-cusp transform of
`rho(x+k log 2)` and `E` the transform of `exp(-x/2)`, then splitting a remote reflected row into
its full-line part and its omitted negative tail gives, for the packet coefficients in
`(12d.9k)`--`(12d.9o)`,

```text
2^(N/2) sum_j a_j integral_0^infinity g(x-(N+j)log 2)H_d(x)dx
 = E/2-2^(N/2)sum_j a_j R_(N+j).                       (12d.9p)
```

The full-line polynomial vanishes by Prouhet and the remaining positive-cusp rows tend to zero.
After the unshifted density cross is restored, however, the limiting value--derivative vector is
not zero but `E-2U_d`.  Its symmetric polarization with `E`, divided by two, is identically

```text
Q(U_d-E)-Q(U_d).                                        (12d.9q)
```

This residual is forced by the two endpoint constraints: total packet mass one preserves the
original prefix, while cancellation of the elementary square fixes the second endpoint.  It is
independent of Haar and Prouhet depth.  The exact evenness of `g` and the current identity
`(12d.9q)` are formalized in `XiCTaylorThetaTailProuhetSeamInvariant.lean`.  Numerical evaluation
also shows that `Q(U_d-E)` is positive at some low-degree upper-half-plane points, so the residual
has no unconditional favorable sign.  The two-endpoint packet remains a valid exact annihilator
of the finite translation polynomial, but it cannot by itself orient the fixed-half-line seam.

The remainder also satisfies the exact pointwise value relation

```text
g(x)+V(x)=4 Phi(x),                                     (12d.9r)
```

where `V(x)=exp(-x/2)/2-T(x)` is the even completed potential and `Phi=T''-T/4` is the canonical
Xi Fourier source.  Together with `V''=-g/4`, this gives on the Fourier--Laplace strip
`g_hat(z)=4z^2 V_hat(z)` and `XiC(z)=(z^2+1/4)V_hat(z)`.  Hence
`g_hat(z)=4z^2 XiC(z)/(z^2+1/4)`: the invariant is Xi itself times an elementary zero-free
multiplier in the open strip, not a removable tail error.  The pointwise identity `(12d.9r)` is
formalized in `XiCTaylorThetaTailProuhetSeamInvariant.lean`; the transform statement is currently
used only at paper level.

The associated one-sided-potential Hermite--Biehler shortcut is false.  If
`E(z)=integral_(0..infinity)V(x)exp(-izx)dx`, high-precision evaluation of
`|E(z)|^2-|E#(z)|^2` changes sign near `z=15.5+0.02i` (stable from 40 through 100 digits).
Thus positivity, monotonicity, and the observed log-concavity of `V` do not supply the missing
orientation; a proof must use an additional arithmetic constraint rather than a generic shape
criterion for the completed potential.

The translate operator has an exact signed inverse on the canonical source.  For `x>=0`, Lean
proves absolute convergence and the critical Möbius identity

```text
rho_1(x)=sum_(n>=1) mu(n)n^(-1/2)rho(x+log n).             (12e)
```

The proof does not use a boundary value of `1/zeta`: Gaussian decay first supplies an absolutely
summable double Lambert series, after which the finite divisor identity
`sum_(d|k)mu(d)=[k=1]` is applied.  This is a genuine signed value relation specific to the full
canonical density.

It does not orient `(12d)`.  Substituting `(12e)` into each shifted `rho_1` factor and changing the
lower endpoint turns every term into a function of the product index `k=mn`; Möbius regrouping
then annihilates every `k>1` and returns the original `rho(x)rho(y)K_d(z;x,y)` integral.  Thus the
critical Möbius constraint is an exact inverse coordinate, but its complete use is the identity
operator rather than a negative square.  A truncated inverse leaves a cofinal divisor-edge defect;
the existing critical-mass-escape theorem shows that no fixed compact synthesis can control that
edge uniformly.  The Möbius-inverse route is therefore retired as a direct current producer.

The reflection defect of a *finite* critical Möbius packet can nevertheless be removed exactly,
without estimating a Mertens sum.  Write

```text
M_N=sum_(n<=N)mu(n),  H_N=sum_(n<=N)mu(n)/n,
a=N+1, b=N+2,
alpha_N=a M_N-ab H_N,  beta_N=ab H_N-b M_N.
```

Then

```text
M_N+alpha_N+beta_N=0,
H_N+alpha_N/a+beta_N/b=0.                                (12f)
```

If `c_n=mu(n)` for `n<=N`, `c_a=alpha_N`, and `c_b=beta_N`, the exact source reflection law gives

```text
sum_n c_n n^(-1/2)rho(-x+log n)
 =sum_n c_n n^(-1/2)rho(x-log n).                        (12g)
```

Lean proves `(12f)`--`(12g)`.  The two corrections are also negligible on the positive half-line.
Indeed `|M_N|<=N`, `|H_N|<=N`, so

```text
|alpha_N|+|beta_N| <= 4(N+2)^3.
```

The Gaussian majorant already used in the absolute Möbius inversion gives, for
`q=exp(-pi/2)<1` and `x>=0`,

```text
R_n(x):=n^(-1/2)rho(x+log n)
       =sum_(m>=1)rho_(nm)(x)
       <= C exp(-x) n q^n/(1-q)^2.
```

Consequently the total correction is `O((N+2)^4 q^N)`, uniformly for `x>=0`, and tends to zero.
Lean now proves the row majorant, the polynomial coefficient bound, the explicit correction
majorant, and its convergence to zero in
`XiCTaylorThetaTailMobiusConstraint.lean`.

Thus the two nonintegrable completion characters can be cancelled
by two remote Gaussian translates rather than bounded by RH-strength Mertens information.  This
permits full-line polarization at asymptotically zero positive-half-line cost.  It does not orient
the pair current:
after applying `(12g)` in both variables, the remaining right-shift/left-shift cross terms still
contain the complete off-diagonal kernel `K_d`.  The next gate is to show that their polarized
half-line boundary is a nonpositive square or an upper-sublinear finite edge, while retaining the
two remote correction translates.

The balancing equations are exactly two endpoint zeros of a finite Dirichlet symbol.  For the
finite coefficient packet `c=(c_n)`, put

```text
C_c(s)=sum_n c_n n^(-s),
R_c(x)=sum_n c_n n^(-1/2)rho(x+log n).
```

Then `(12f)` says

```text
C_c(0)=C_c(1)=0.                                         (12h)
```

Both endpoint identities are formalized as
`finiteMoebiusBalancedCoefficientMoment_one` and
`finiteMoebiusBalancedCoefficientMoment_inv`.  The exact reflection law and evenness of the core
give the corresponding half-line identities

```text
integral_(0,infinity) R_c^left(x) H_d(z,x)dx
  = integral_(-infinity,0] R_c(x) H_d(z,x)dx,

integral_(0,infinity) R_c^left(x) partial_z H_d(z,x)dx
  = integral_(-infinity,0] R_c(x) partial_z H_d(z,x)dx.   (12i)
```

These are formalized in `XiCTaylorThetaTailBalancedMobiusPairCurrent.lean`.  They show that the
left packet is not a second positive source: it is exactly the missing negative half of the same
signed bilateral packet, with the original orientation retained.

The bilateral Mellin transform also identifies the limit of this route exactly.  Write
`rho_k=4(d/dx)^2 exp(x/2-pi k^2 exp(2x))` and
`b_k=sum_(n|k)c_n`.  In the half-plane of absolute convergence, Mellin substitution gives

```text
integral_R rho_k(x)exp(i t x)dx
 =-2t^2 pi^(-(1/4+it/2)) Gamma(1/4+it/2) k^(-(1/2+it)),

sum_k b_k k^(-s)=zeta(s)C_c(s).
```

The zeros `(12h)` cancel the two completion singularities, while `(12g)` gives rapid decay at
both source ends.  Analytic continuation therefore yields, for real `t`,

```text
integral_R R_c(x)exp(i t x)dx
 = [4t^2/(t^2+1/4)] XiC(t) C_c(1/2+it).                  (12j)
```

Thus bilateralization does not remove the RH-bearing factor: it multiplies `XiC` by a finite
Dirichlet symbol.  A sign estimate for the bilateral current without a separate estimate of the
right/left cross term would consequently be the target orientation in another coordinate.  The
only surviving use of `(12j)` is an edge estimate proving that the logarithmic derivative of the
finite symbol and the escaping bilateral mass are `o(n)` on the anisotropic mesh; no such estimate
is currently proved.

The survival source has the complementary reflection parity.  Differentiating the raw theta
reflection gives

```text
eta(-x)=-eta(x)+exp(x/2)+exp(-x/2).                       (12k)
```

Consequently the same balanced coefficient packet `c`, using `C_c(0)=C_c(1)=0`, satisfies

```text
sum_n c_n n^(-1/2)eta(-x+log n)
 =-sum_n c_n n^(-1/2)eta(x-log n).                       (12l)
```

Equations `(12k)`--`(12l)` are proved in Lean in
`XiCTaylorThetaTailSurvivalMobiusReflection.lean`.  The source derivatives
`partial_x H_d` and `partial_x partial_z H_d` are odd, so the two minus signs cancel in their
pairing.  Lean therefore proves the survival analogues of `(12i)`: the reflected right-packet
integrals equal the left-packet integrals on the opposite half-line with the original current
orientation.  This supplies an exact odd bilateralization, but not an antisymmetric current
cancellation.

## Critical-Laguerre scale coordinate

The mechanism of Haufschild's critical-Laguerre moment deformation yields one exact new coordinate.
Let

```text
L_d(u)=sum_(k=0)^d (-1)^k d^(falling k) u^(2k)/(d^k(2k)!),
G_d ~ Gamma(shape=d+1, rate=d).
```

Then, for `0<=k<=d`,

```text
E[G_d^(-k)]=d^k/d^(falling k),
```

and hence the ordinary truncated cosine has the exact positive scale average

```text
C_d(z,x)=E[L_d(zx/sqrt(G_d))].                            (13)
```

Thus the raw theta transform in `(3)` is a double positive average of rescaled critical-Laguerre
polynomials.  Equation `(13)` is proved on paper by a finite coefficient comparison.  It is not yet
a sign theorem: the inverse-gamma scale law is continuous, unbounded, and has no identity atom,
whereas Haufschild's sign-transfer theorem uses an atom of mass `p>1/2` at scale one.  Indeed generic
positive scale averaging has exactly the cross-current obstruction already exposed in `(4)`.
The loss is already exact at degree three: writing the ordinary section as

```text
Q_3(s)=1-s/2+s^2/24-s^3/720,  s=z^2,
Q_3'(s)=-(s^2-20s+120)/240<0  for every real s,
```

shows that `Q_3` has only one real root and hence its even lift has four nonreal zeros, despite
being the positive inverse-gamma average `(13)` of hyperbolic critical-Laguerre copies.

The Laguerre energy does not transfer directly to `(13)`.  Its favorable identity is horizontal,

```text
partial_x (|L_d(x+iy)|^2+|L_d'(x+iy)|^2)=(x/d)|L_d'(x+iy)|^2.
```

The scale in `(13)` moves instead on the radial path `r -> rz`.  The Kummer ODE gives the exact
radial identity

```text
d/dr (|L_d(rz)|^2+|L_d'(rz)|^2)
 = -4 Im(z) J_(L_d)(rz)
   +(r/d) Re(z^2)|L_d'(rz)|^2.                            (13a)
```

Thus the individual-copy radial energy already contains the unknown oriented current.  More
decisively, the current of the average in `(13)` is a double-scale cross current, not the average
of the diagonal currents in `(13a)`.  The only surviving Laguerre possibility is a *polarized*
two-scale energy identity whose mismatch terms cancel under the exact product of the inverse-gamma
scale and `T(x)dx`; the one-copy energy and hyperbolicity of each Laguerre copy are insufficient.

There is nevertheless a second exact relation in the same coordinate.  Put
`R_d=G_d^(-1/2)` and

```text
S_d(r)=2(d+1)-2d/r^2.
```

The inverse-gamma density gives the Stein identity

```text
E[R_d f'(R_d)]=E[S_d(R_d)f(R_d)],  E[S_d(R_d)]=0.         (13b)
```

Hence, if `F_d(w)=E[L_d(R_d w)]=C_d(w)` is the ordinary truncated cosine and
`M_d(z)=integral T(x)F_d(zx)dx`, then

```text
w F_d'(w)=E[S_d(R_d)L_d(R_d w)],
z M_d'(z)=integral T(x)E[S_d(R_d)L_d(R_dzx)]dx.           (13c)
```

After polarization with independent `(x,r)` and `(y,s)`, this becomes the exact score--phase
covariance

```text
Im(z M_d'(z) conjugate(M_d(z)))
 = (1/2) integral integral T(x)T(y)
     E[(S_d(r)-S_d(s))
       Im(L_d(rzx)conjugate(L_d(szy)))] dxdy.             (13d)
```

Equations `(13b)`--`(13d)` are proved on paper by integration by parts in the explicit
inverse-gamma density.  `[OPEN CORE]` The score is increasing in `r`, but the two source variables
`x,y` are independent, so real-rooted radial phase monotonicity of each `L_d` does not sign the
cross phase in `(13d)`.  A surviving Laguerre proof must show that the exact `T`-weighted product
law makes this score--phase covariance upper-sublinear; replacing it by a diagonal or an absolute
value loses the required cancellation.

The identity-atom part of the Theorem-M mechanism is in fact unavailable for *any* critical-
Laguerre representation of the raw moment section.  Normalize the raw moments to `mu_0=1`, write
`r_k=mu_(k+1)/mu_k`, and note that positivity of the tail measure makes `r_k` nondecreasing.  If

```text
sum_(k=0)^d (-1)^k mu_k z^(2k)/(2k)!
  = integral_[0,1] L_d(lambda v z) dnu(v),
```

then coefficient comparison gives

```text
M_k := integral v^(2k)dnu(v)
     = mu_k d^k/(lambda^(2k) d^(falling k)).              (14)
```

If `nu` has an identity atom of mass `p`, then `p<=M_d`.  Since `[0,1]` moments decrease,
`M_d<=M_(d-1)`, so the last ratio in `(14)` gives `d r_(d-1)/lambda^2<=1`.  For every `k<d`,

```text
M_(k+1)/M_k
 = d r_k/(lambda^2(d-k)) <= 1/(d-k).
```

Multiplication yields

```text
p <= M_d <= 1/d!.                                       (15)
```

Thus for every `d>=2` an identity atom of mass `p>1/2` is impossible, even if one allows an
alternative truncated Hausdorff representing measure instead of the natural inverse-gamma law.
Equations `(14)`--`(15)` are proved on paper.  Theorem M therefore supplies the Laguerre coordinate
and energy identity, but its coercive sign-copy step is rigorously retired for the raw theta
moments.  Any surviving use of `(13)` must estimate the averaged cross current directly.

The same atom mechanism also fails if it is applied directly to the *core* polynomial from `(8a)`.
Let `N=d+1`.  Its first `N` unnormalized moments `q_0,...,q_(N-1)` are the genuine moments of the
positive completed theta source, hence their ratios
`r_k=q_(k+1)/q_k` are nondecreasing for `k<=N-2`; only the artificial top moment `q_N` differs.
For any critical-Laguerre representation on `[0,1]`, Hausdorff monotonicity gives

```text
M_(k+1)/M_k = N r_k/(lambda^2(N-k)),
lambda^2 >= N r_(N-2)/2.
```

Consequently, for `k=0,1,2`,

```text
M_(k+1)/M_k <= 2/(N-k),
p <= M_N <= M_3 <= 8/[N(N-1)(N-2)] <= 1/3  (N>=4).       (15a)
```

Thus an identity atom `p>1/2` is impossible for every core degree `N>=4`, regardless of the special
top coefficient.  Equation `(15a)` is proved on paper from Cauchy--Schwarz log-convexity and the
finite Hausdorff moment inequalities.  It is now formalized in Lean: all-order theta-moment
log-convexity and ratio monotonicity are
`thetaCuspRawEvenMoment_sq_le_adjacent` and
`thetaCuspRawEvenMoment_ratio_mono`; the abstract endpoint bound is
`thetaCoreCriticalLaguerre_endpointAtom_le_third`.

## Literature/value-relation audit

- Haglund's incomplete-gamma truncations are the direct parent of the dominant-atom coordinate.
  The proposed theorem is not that each truncation is hyperbolic; it is that a zero-free/ordered
  region expands with the truncation, and the paper proves that such expansion would imply RH.
  Hence importing that conjecture would rename the present compact-window obstruction rather than
  discharge it.  Primary source: <https://arxiv.org/abs/0910.5228>.
- Gershon's June 2026 revision proves strict log-concavity (`TP_2`) of the Riemann--Jacobi kernel
  analytically, but explicitly leaves the passage to `TP_infinity`/Laguerre--Pólya open.  Thus it
  is a genuine new exact source inequality, yet it does not orient the finite complex pair current
  `(11)`.  The earlier version's suggestion that log-concavity alone implied RH is not the claim of
  the revised paper.  Primary source: <https://www.preprints.org/manuscript/202604.0159>.
- Michałowski gives an interval-certified negative order-five Toeplitz minor for the actual
  de Bruijn--Newman kernel.  Hence a `PF_infinity` or all-order Toeplitz-total-positivity shortcut
  is not merely unproved for this kernel: the reported `PF_5` obstruction rules out that proposed
  source property.  Primary source: <https://arxiv.org/abs/2602.20313>.
- Freedman's finite-core Volterra manuscript derives the same second-order theta-mode identity
  and an exact boundary-plus-tail formula for a Weyl kernel.  It explicitly leaves the
  quotient-to-original Weyl lift, uniform coverage of `|omega|<1/2`, and the final KLM/de Branges
  bridge open.  Its normalized quotient certificate therefore supplies no sign theorem for the
  present raw theta-tail current; the individual boundary and fixed-Volterra layers are also
  reported indefinite.  Primary source: <https://arxiv.org/abs/2606.29555>.
- Polson's June 2026 incomplete-gamma/Thorin framework separates an unconditional Gaussian
  "trivial tier" from a zero-ordinate tier whose generalized-gamma-convolution positivity is
  equivalent to RH.  It supplies no finite cancellation between those tiers and cannot be used as
  an independent sign for `(12d)`.  Primary source:
  <https://papers.ssrn.com/sol3/Delivery.cfm/6954119.pdf?abstractid=6954119&mirid=1>.
- Jenkins--McLaughlin prove a global growing-degree asymptotic for the Taylor sections of `xi`.
  Their result separates outward-moving spurious zeros from bounded Hurwitz zeros converging
  super-exponentially to the zeros of the limiting function.  It validates a moving top-edge
  analysis for truncation artifacts, but it cannot sign a bounded anisotropic fibre independently
  of the limiting theta transform.  Primary source: <https://arxiv.org/abs/1609.05965>.
- DeFranco derives positive integral formulas and integration-by-parts recurrences for the Xi
  Taylor coefficients.  Those relations control the scalar coefficient sequence; they contain no
  finite logarithmic-translation law and no cancellation of the mixed value--derivative current
  created by `E_d`.  They therefore complement `(12d.9b)` but do not discharge its oriented-current
  estimate.  Primary source: <https://arxiv.org/abs/1907.08984>.
- The classical theta-kernel formulas give positivity and modular balance of `Phi`, the Mellin
  representation of `xi`, the Fourier/cosine representation of `Xi`, and the raw even-moment
  formula.  These relations are present in Lean.
- Romik's orthogonal-polynomial expansions give positive coefficient sequences and compact-uniform
  convergence in the Hermite, Meixner--Pollaczek, and continuous-Hahn bases.  Their finite partial
  sums are not the monomial Taylor cores `U_d`; the Meixner--Pollaczek Poisson flow does not preserve
  hyperbolicity.  No transfer theorem in that work supplies the sign of `(4)`.
- Hedenmalm's theta-source boundary-value problem gives an eigenvalue characterization and a
  conditional self-adjointness program.  It supplies no finite Taylor-section identity beyond the
  theta/Mellin relations already used here, and the required inner-product sign remains an input.
- The 2025 backward-parabolic-barrier preprint claiming to propagate Pick positivity from a
  de Bruijn real-zero slice cannot supply the sign.  Its collision bridge requires a uniform
  differential inequality up to a collision.  The exact heat-flow polynomial
  `E_t(z)=z^2+1-2t` is a counterexample: `E_1` has two real zeros, `E_0` has zeros `+-i`, and the
  zero speed and separation constants blow up at the collision `t=1/2`.  Continuity of a tube
  energy at that time does not imply it remains zero on the earlier side.
- The Wigner--Eisenstein/Bessel coordinate has a positive real Mellin signature but an indefinite
  ordered-pair kernel.  Positivity on a real Mellin line is not a positive power-mixture
  representation, because Mellin inversion uses a complex vertical line.  Hence it does not orient
  the distinguished raw mixed correlation.
- Schoenberg total positivity does not provide an independent source-side shortcut.  For the
  symmetric coordinate `Xi(s)=Xi_1(-s^2)`, a one-sided Pólya-frequency representation of
  `1/Xi_1` is equivalent to RH, while the Pólya-frequency condition on its Taylor coefficients is
  the restricted Laguerre--Pólya condition.  The totally positive Jacobi-theta example attached to
  the zero set `{-n^2}` is a different transform and does not orient the differentiated Riemann
  theta-tail correlation `(4)`.
- Csordas's positive-definite-kernel results connect theta-kernel concavity to generalized *real*
  Laguerre inequalities.  They control restrictions to the real axis, where `(10)` already starts
  from zero, but do not sign the complex defect on `x+it`, `t>0`; making that extension for every
  fibre is a Laguerre--Pólya/RH condition.
- Effective Jensen-polynomial hyperbolicity applies to fixed degree and sufficiently large
  coefficient shift.  The cores here are unshifted initial sections whose degree grows with the
  approximation stage.  The literature explicitly retains all degrees and all shifts in the RH
  equivalence, so the high-shift Hermite asymptotic does not bound `(12)`.
- Haufschild's critical-Laguerre theorem is genuinely family-specific: an explicit moment law with
  an identity atom of mass `sqrt(2/e)>1/2` transfers the alternating critical signs of a Kummer-ODE
  base polynomial.  Its conclusion does not apply to `U_d`, but its mechanism gives the exact
  inverse-gamma scale representation `(13)` and a concrete energy estimate to test.
- The existing theta-tail first-moment Bezoutian and critical-tilt cards already contain the
  relevant full-source correlation identity.  Their positive-entry kernel is not a positive
  operator: its quadratic form on exponential packets is the Xi Hermitian orientation diagonal,
  and nonnegativity on the required cofinal family is equivalent to RH.  Replacing the exponential
  by its finite Taylor packet produces the same finite cross-current rather than a new square.
  Consequently the Volterra contraction in those cards can close the present task only if it is
  constructed on the finite source packets independently; assuming its contractivity merely
  renames the desired sign.
- The current formal tree now proves that Hedenmalm center mixing turns the full theta source into
  an explicit strictly positive, even, continuous, integrable density whose Fourier transform is
  the radial Wigner current.  This is a real source improvement, but Fourier nonnegativity of that
  density throughout the critical aperture is exactly the RH-equivalent second positivity.  The
  elementary Pólya shortcut by convex decrease is unavailable: a nonconstant smooth even density
  decreasing from its central maximum is necessarily concave at the center, and the actual density
  has that behavior.  A Gaussian-scale-mixture shortcut is also not supplied by the value relation;
  it would require complete monotonicity in the squared center variable, a strictly stronger
  factorization not present in the formal source identities.
- The new finite-local-spectral-frame obstruction proves that no finite constant-coefficient
  differential autocorrelation frame can orient the Hedenmalm diagonal: such a frame would create
  an entire finite-difference coboundary and propagate every Xi zero out of the critical strip.
  Thus the score covariance cannot be closed by replacing its phase reversals with finitely many
  local spectral squares; a successful carrier must remain nonlocal or cofinally arithmetic.

## Gates

- [x] positive normalized density coordinate formalized
- [x] finite section derivative formalized
- [x] derivative integral identity formalized
- [x] exact symmetric two-point current identity formalized
- [x] positive-current atom shortcut excluded
- [x] derive the exact one-variable integration-by-parts correlation identity
- [x] derive the completion-compensated finite cosine identity
- [x] expose the raw-tail plus completed-source density split
- [x] prove the completed-source feedback identity and remove that circular channel
- [x] prove the exact negative current at the central completion seam point
- [x] strengthen the seam sign to strict negativity on the whole positive imaginary axis
- [x] formalize the source and polynomial reflection laws and exclude reflected-fibre cancellation
- [x] determine every odd raw-tail seam jet and close the repeated-IBP boundary data
- [x] prove exact atom masses and pointwise Gaussian domination by the first density atom
- [x] expose the exact logarithmic-integer translate law for every density atom
- [x] derive and formalize the exact signed square-index polarization of the full atom packet
- [x] derive and formalize the cofinal dyadic Haar polarization and exact current lift
- [x] eliminate the cofinal dyadic top row at the integrated finite-core current level
- [x] derive the exact mean-zero density-score covariance and rule out pointwise phase ordering
- [x] identify the current with the vertical derivative of the finite squared modulus
- [x] derive and formalize the real-boundary-to-interior complex Laguerre-defect identity
- [x] audit classical theta, orthogonal-polynomial, spectral, and Wigner value relations
- [ ] prove an integrated cancellation bound for the raw moment terms in `(12)`
- [ ] obtain the eventual scaled core-current inequality on every anisotropic fibre
- [ ] complete paper proof and Lean theorem

## Centered Green packet and product-fibre translation cancellation

**[PROVED, BRIDGE]** Put `V=thetaCuspCompletedTailPotential` and
`Phi=thetaCuspFullSource`.  The exact source relation gives

```text
-V''(x)+V(x)/4=Phi(x).
```

For every real `L,x`, the Wronskian endpoint identity in the two opposite translation directions
cancels the completed-survival slope and yields

```text
2 cosh(L/2)V(x)-V(x+L)-V(x-L)
 = integral_0^L 2 sinh((L-u)/2)(Phi(x+u)+Phi(x-u)) du.       (14)
```

For `L>=0` the right side is nonnegative.  Both the exact identity and its nonnegativity are
formalized in `XiCTaylorThetaTailCenteredGreenPacket.lean`.  On the Fourier--Laplace strip its
multiplier is

```text
2(cosh(L/2)-cos(Lz))/(z^2+1/4).
```

Thus `(14)` is not an independent orientation theorem: it is Xi multiplied by an elementary
centered-translation factor.  In particular the limit `L->0` recovers the canonical source, so
positive smoothing of `(14)` alone would re-state the missing Xi current sign.

**[PROVED, LIVE REDUCTION]** There is a separate arithmetic cancellation on each positive product
fibre.  For `mn=k`, set

```text
delta(m,n)=(log m-log n)/2.
```

Divisor reflection `(m,n)<->(n,m)` fixes `k` and sends `delta` to `-delta`; moreover the critical
atom weights multiply to the fibre-constant `k^(-1/2)`, and

```text
rho_m(x)rho_n(y)
 = k^(-1/2) rho_1(x+log(k)/2+delta)
              rho_1(y+log(k)/2-delta).                     (15)
```

The finite sine section is exactly odd.  Hence, on every finite product fibre,

```text
sum_(mn=k) S_d(delta(m,n))=0,

sum_(mn=k) H_d(x+delta(m,n))
 = H_d(x) sum_(mn=k) H_d(delta(m,n))
   - sum_(mn=k) TopEdge_d(x,delta(m,n)).                    (16)
```

All identities in `(15)`--`(16)` are formalized in
`XiCTaylorThetaTailProductFiberTranslation.lean`.  This removes the entire cosine--sine mixing
channel before any estimate and leaves only one even divisor-fibre top-edge packet.  The remaining
open core is now precise: regroup the absolutely convergent atom-pair current by product fibres and
prove that the sum of the even packets in the last term of `(16)` is `o(n)|P_{2d+3}(z_n)|^2` after
the source-selected fibre/depth choice.  No positivity of an individual atom or scalar Xi
multiplier can supply this bound.

The product-fibre module also proves the general absolutely summable regrouping theorem
`tsum_eq_tsum_thetaPositiveFactorPairs`: every ordered positive-index packet is the iterated sum
of its finite `mn=k` fibres.  The remaining formal integration step is therefore not a reindexing
problem; it is to expose absolute summability of the already-integrated atom-pair current as a
named theorem and instantiate this regrouping.

## Integrated product-fibre current

**[PROVED, LIVE REDUCTION]** The product-fibre decomposition now applies to the integrated raw
current, not only to the pointwise density packet.  For the positive-index atom `n`, let

```text
V_n(d,z)=integral_(0,infinity) rho_(n+1)(x) H_d(z,x) dx,
D_n(d,z)=integral_(0,infinity) rho_(n+1)(x) partial_z H_d(z,x) dx.
```

Each is an explicit finite packet of raw atom moments.  Gaussian domination proves that both
sequences are absolutely summable in `n`.  Fubini then gives the exact ordered-pair identity

```text
integral rho_(m+1)(x)rho_(n+1)(y) K_d(z;x,y) dxdy
 =1/2[Im(D_m conjugate(V_n))+Im(D_n conjugate(V_m))].       (17)
```

The right side is absolutely summable over ordered pairs.  Therefore it may be regrouped by
`k=(m+1)(n+1)` without a conditional rearrangement.  If `C_k(d,z)` denotes the finite sum over
that product fibre, then

```text
Q(U_d(z))=1/4 sum_(k>=1) C_k(d,z),                          (18)
```

and the outer series is absolutely convergent.  Divisor reflection makes the two halves of `(17)`
identical after summation over a fibre, so in fact

```text
C_k(d,z)=sum_((m+1)(n+1)=k) Im(D_m(d,z) conjugate(V_n(d,z))). (19)
```

Thus the remaining arithmetic object is one unsymmetrized Dirichlet-convolution coefficient; no
pair-current averaging remains.  Equations `(17)`--`(19)`, the moment summability, and the exact
current regrouping are formalized in `XiCTaylorThetaTailProductFiberCurrent.lean`.

This completes the integration/reindexing gate following `(16)`.  It does not assign a sign to
`C_k`: the live theorem is now to exploit the full canonical relations among the convolution
coefficients, or equivalently to prove the summed even finite-translation edge is upper-sublinear
on the admissible anisotropic schedules.

## Prime-power divisor-phase orientation

**[PROVED, BRIDGE]** The analytic phase carried by one prime-power divisor fibre has an intrinsic
orientation before conjugate pairing.  For a polynomial `P` with every root on the unit circle,
`P != 0`, and `deg P>0`, the root expansion gives, for `|w|<1`,

```text
Re(w P'(w)/P(w)) < deg(P)/2.                               (20)
```

Indeed each unit root `zeta` contributes
`Re(w/(w-zeta))<1/2`.  Therefore the degree-centered exponential phase

```text
B_(P,L)(z)=exp(-i deg(P)Lz/2) P(exp(iLz))
```

has strict negative upper oriented current whenever `L>0` and `Im z>0`:

```text
Im(B'_(P,L)(z) conjugate(B_(P,L)(z))) < 0.                 (21)
```

For the `N`-term geometric polynomial `G_N(X)=sum_(j<N)X^j`, all roots are nontrivial
`N`th roots of unity.  With `L=log p`, `(21)` is exactly the centered divisor phase of the prime
power `p^(N-1)`.  This gives an arithmetic sign before the value--derivative packet is conjugate
polarized; it uses neither Xi divisor data nor a limiting measure.

The same packet has an exact signed Fejer polarization.  In polynomial form,

```text
G_(2a+1)=G_(a+1)^2-X G_a^2,
G_(2a+2)=G_(a+1)G_(a+2)-X G_a G_(a+1).                    (22)
```

Thus even prime-power exponents are differences of consecutive analytic squares and odd exponents
are differences of adjacent Gram cross-products.  Equations `(20)`--`(22)`, the explicit analytic
derivative, and strict current sign are formalized in
`HTGeometry/UnitCircleRootRadialOrientation.lean`.

This is not yet the core-current theorem.  If the logarithmic translates are first extended from
the positive half-line to a common full line and then conjugate-polarized, divisor reflection
removes the displacement derivative that carries `(21)` and leaves a common-centre term with no
fixed sign.  Hence `(21)` must be applied inside the finite cosine--sine translation identity,
before integrated conjugate polarization.  The remaining exact obstruction is the nested swept
window `0<u<log m` created by translating the positive-half-line endpoint.  It is part of the
canonical packet, not an independently small positive error.

## Exact arithmetic phase seam

**[PROVED, LIVE REDUCTION]** Let

```text
F(z)=integral_(0,infinity) rho_1(u)exp(iuz)du,
W_a(z)=integral_0^a rho_1(u)exp(iuz)du.
```

For every positive integer `n`, translation of the `n`th density atom across the fixed positive
endpoint is exactly

```text
A_n(z)=n^(-1/2)exp(-i log(n) z)[F(z)-W_(log n)(z)],
A_n'(z)=n^(-1/2)exp(-i log(n) z)
  [F'(z)-W'_(log n)(z)-i log(n)(F(z)-W_(log n)(z))].       (23)
```

Consequently its oriented current is

```text
Q(A_n)=|n^(-1/2)exp(-i log(n)z)|^2[
  Q(F)+Q(W_(log n))
  -Im(F' conjugate(W_(log n)))
  -Im(W'_(log n) conjugate(F))
  -log(n)|F-W_(log n)|^2].                                (24)
```

Thus the arithmetic phase contributes the favorable negative square predicted by the radial
orientation theorem.  Every failure of atomwise negativity is confined exactly to the self-current
and two mixed currents of the nested swept window.  Equations `(23)`--`(24)`, including the needed
half-line integrability and interval splitting, are formalized in
`XiCTaylorThetaTailArithmeticPhaseSeam.lean`.

Equation `(24)` is not an invitation to estimate `F` and `W_a` separately.  On the target strip the
formal full-tail Dirichlet packet is not the convergent object; its divergence is cancelled by the
nested windows.  The next gate is therefore a packet-level Abel polarization of the family
`F-W_(log n)`, retaining the negative drift and the window cross terms in one finite identity.

## Nested-seam Abel polarization

**[PROVED, LIVE REDUCTION]** The swept windows in `(23)` are nested, so they admit an exact finite
layer-cake decomposition rather than a termwise estimate.  Put `L>0`,

```text
p_j(z)=exp(-jL/2)exp(-ijLz),
P_N(z)=sum_(j<N)p_j(z),
I_r(z)=integral_(rL..(r+1)L) rho_1(u)exp(iuz)du,
T_N(z)=integral_(NL..infinity) rho_1(u)exp(iuz)du.
```

Finite Abel summation gives

```text
sum_(j<N) p_j T_j
 =sum_(r<N) P_(r+1) I_r + P_N T_N,                       (25)

sum_(j<N) [p_j T'_j+p'_j T_j]
 =sum_(r<N) [P_(r+1)I'_r+P'_(r+1)I_r]
   +P_NT'_N+P'_NT_N.                                     (26)
```

Thus every moving boundary interval is absorbed into a disjoint logarithmic block with its whole
geometric prefix, and the value--derivative pairing is retained.  There is no remaining collection
of independently estimated seams.  Equations `(25)`--`(26)` are formalized as
`criticalLogPhase_tail_packet_eq_prefix_blocks` and
`criticalLogPhase_tail_packetDerivative_eq_prefix_blocks` in
`XiCTaylorThetaTailArithmeticPhaseSeam.lean`.

The prefix itself is the reverse critical evaluation

```text
P_N(z)=G_N(exp(iL(-z+i/2))).                              (27)
```

For `Im z<1/2`, write `r=exp(-L(1/2-Im z))<1`.  The unit-root expansion now gives the complementary
radial inequality

```text
Re(w G_N'(w)/G_N(w)) >= -(N-1)r/(1-r),
Q(P_N)(z) <= L(N-1)r/(1-r)|P_N(z)|^2.                    (28)
```

This is the finite orientation-sensitive estimate needed for a sublinear Haar depth: on each fixed
left-strip fibre its constant is fixed and its growth is only linear in the prefix length.  The
rootwise lower bound, the general polynomial theorem, the exact identification `(27)`, and `(28)`
are formalized in `HTGeometry/UnitCircleRootRadialOrientation.lean` and
`XiCTaylorThetaTailArithmeticPhaseSeam.lean`.

The unresolved term is now narrower and genuinely Hermitian: when the current of the block sum in
`(25)` is expanded, `(28)` controls every diagonal block current, while distinct blocks produce
cross currents.  A valid finish must prove that the signed Haar combination of those off-diagonal
block currents is upper-sublinear relative to the final Taylor value.  Bounding block norms
separately is still invalid near a cancellation of the total value.

## Universal arity-Haar polarization

**[PROVED, NO-GO FOR MULTI-PRIME ESCAPE]** The dyadic Haar decomposition is the `L=log 2`
specialization of a continuous logarithmic-scale identity.  For any `L != 0`, put `q=exp L` and

```text
D_k^L(x)=exp(-kL/2)rho(x+kL),
S_k^L=D_k^L-D_(k+1)^L,
A_k^L=q D_(k+1)^L-D_k^L.
```

Then

```text
D_k^L(x)D_k^L(y)
 =q/(q-1) S_k^L(x)S_k^L(y)
  -1/(q-1) A_k^L(x)A_k^L(y)
  +q D_(k+1)^L(x)D_(k+1)^L(y).                          (29)
```

For `L=log p`, `(29)` is the signed `p`-ary valuation polarization of the full square-index
translate packet.  Theta reflection gives, at every depth,

```text
A_k^L(-x)
 =exp(L/2)S_k^L(x-(2k+1)L)
  -(q-1)/2 exp(-x/2).                                    (30)
```

The amplitude square `exp L=q` is exactly the ratio of the two square coefficients in `(29)`.
Consequently those square channels cancel for every arity, not only for `p=2`.  The translated
exact-valuation row is a discrete coboundary, and the complete reflected prefix is

```text
sum_(k<N) q^k[ q/(q-1) S_k^L(x-(2k+1)L)S_k^L(y-(2k+1)L)
                    -1/(q-1) A_k^L(-x)A_k^L(-y)]
 =1/2 q^N[D_N^L(x-2NL)e^(-y/2)+e^(-x/2)D_N^L(y-2NL)]
  -1/2[rho(x)e^(-y/2)+e^(-x/2)rho(y)]
  -(q^N-1)/4 e^(-(x+y)/2).                               (31)
```

Equations `(29)`--`(31)` are formalized in
`XiCTaylorThetaTailArityHaarPolarization.lean`.  They show that changing or combining primes cannot
supply an independent terminal orientation: after exact reflection and telescoping, every arity
lands on the same remote-row/density/exponential three-term source already present in `(12d.8h)`.
The obstruction is universal under logarithmic scale, not a defect of dyadic parity.

## Aggregate rank-two square difference

**[PROVED, LEAN]** The complete reflected Haar prefix in `(31)` is a symmetric rank-two tensor,
not a family of layerwise cross terms.  Put

```text
a_N=N log 2,
E(x)=exp(-x/2),
R_N(x)=2^N D_N(x-2N log 2)-rho(x)-(2^N-1)E(x)/4.
```

Then the source prefix is

```text
1/2[R_N(x)E(y)+E(x)R_N(y)].                              (32)
```

The residual is the critical coboundary of the unique quarter-completed profile

```text
h=rho-E/4,
R_N(x)=exp(a_N/2)h(x-a_N)-h(x).                          (33)
```

There are two canonical square channels around this midpoint.  With
`c_N=(2^N-1)/4` and `g=rho-E/2` (which is exactly even), Lean proves

```text
R_N+c_N E = exp(a_N/2)rho(x-a_N)-rho(x),
R_N-c_N E = exp(a_N/2)g(x-a_N)-g(x).                    (34)
```

For the value--derivative transforms `(A,A')` of the first channel and `(E,E')` of the seam,
the integrated current of `(32)` is therefore the normalized difference of the two aggregate
square currents:

```text
1/2 Cross(A-c_N E,E)
 = [Q(A)-Q(A-2c_N E)]/(2^N-1).                          (35)
```

The source identities `(32)`--`(34)` and the complex value--derivative identity `(35)` are
formalized in `XiCTaylorThetaTailHaarResidualRankTwo.lean`.  Naming the Fubini instantiation that
identifies the integral of `(32)` with its two transform pairs remains formal bookkeeping.  The
identities retain the whole completion cancellation and do not compare packet norms.  The two
square channels are the uncompleted density coboundary and the exactly-even-remainder coboundary.

The apparent phase-contraction shortcut does not survive the fixed half-line.  Translating the
even remainder through the endpoint contributes the limiting value--derivative vector `E-2U_d`;
its seam polarization is exactly the invariant `(12d.9q)`.  Consequently moving the returned
copy of `Q(U_d)` to the left cancels the same copy supplied by the swept window.  A closing
estimate must orient the finite difference in `(35)` before this endpoint invariant is separated,
or introduce an additional arithmetic value relation that also cancels the invariant.

## Phase-adapted Prouhet annihilation

**[PROVED, LEAN; LIVE ALGEBRAIC REDUCTION]** The two endpoint values and the Prouhet jet do not
exhaust the finite coefficient freedom.  For an arbitrary complex phase `u`, put

```text
Q_u(X)=X^2-2 Re(u)X+|u|^2=(X-u)(X-conj(u)),
B_(m,u)(X)=B_m(X)Q_u(X)^2.
```

Multiplying `B_(m,u)` by one affine factor again permits arbitrary prescribed values at the two
real completion characters `q` and `r`, provided neither endpoint equals `u`.  The resulting real
polynomial `A_(m,u;q,r,tau)` satisfies simultaneously

```text
A(q)=1,  A(r)=tau,
(X-1)^m divides A(X),
A(u)=A'(u)=A(conj(u))=A'(conj(u))=0.                    (36)
```

The double phase root is needed by the actual rank-two residual.  That residual has one translated
density channel crossed with the fixed completion channel, rather than two translated copies of
the same vector.  For the full complex logarithmic phase

```text
u=exp(iLz),
```

the two root equations give, for every base shift `a` and every value--derivative vector `(F,F')`,

```text
sum_j a_j u^j=0,                 sum_j j a_j u^j=0,
sum_j a_j p_(a+jL)F=0,
sum_j a_j p_(a+jL)(F'+i(a+jL)F)=0.                     (37)
```

Thus the complete coefficient-weighted one-sided untruncated translated value and derivative
vectors vanish before polarization.  These identities are formalized by
`phaseAdaptedProuhet_oneSidedTranslationValue_sum_eq_zero` and
`phaseAdaptedProuhet_oneSidedTranslationDerivative_sum_eq_zero` in
`XiCTaylorThetaTailPhaseAdaptedProuhetPacket.lean`.  The same packet retains every ordinary
translation-moment cancellation below depth `m`, so inserting the phase roots does not recreate a
finite Taylor edge.  The earlier opposite-phase cosine cancellation remains as a weaker corollary.

The endpoint bookkeeping also has a conservation correction.  If `c_j=a_jq^j` and `r=2q`, then

```text
sum_j c_j(2^(N+j)-1)=2^N A(r)-A(q)=2^N tau-1.          (38)
```

After `rho=g+E/2`, the remote-row completion cross changes by `(2^N tau-1)/2`, while the explicit
Haar square subtracts `(2^N tau-1)/4`.  Hence the net endpoint square is
`(2^N tau-1)Q(E)/4`, not an independently assignable square.  If the fixed-endpoint invariant
`Q(E)-Cross(U,E)` deforms only by this net square, its scalar cancellation endpoint is

```text
tau_N=(4 Cross(U,E)/Q(E)-3)/2^N.                        (39)
```

Equations `(38)`--`(39)`, including existence of a real packet satisfying the endpoints, Prouhet
jet, double phase root, and scalar cancellation equation, are formalized in the same module.

`[OPEN CORE]` The remaining issue is now exact rather than estimative: prove the fixed-half-line
Fubini identity with arbitrary `tau` and determine its returned canonical-density vector.  The
finite algebra proves how the completion square changes, but does not yet prove that the entire
boundary current is the old invariant plus that square.  A returned copy of `Q(U_d)` would make
the endpoint cancellation tautological.  This composition must be settled before `(39)` can be
used as an orientation theorem.

## Finite cosine--sine translation edge: discharged

**[PROVED, LEAN]** The finite-section obstruction created by logarithmic translation is closed in
`../3-formalized/xi-taylor-finite-translation-logarithmic-haar-edge.md`.

The two diagonal finite edges satisfy the exact reflection identities

```text
E_d^-(x,a;z)=E_d^+(x,a;-z),
partial_z E_d^-(x,a;z)=-partial_z E_d^+(x,a;-z).
```

At the single source-selected depth

```text
k_n=(2 ord_sigma(xi)+1) clog_2(n+1),
a_n=2 k_n log 2,
```

both complete density-integrated finite translation current defects (the two packet--edge mixed
currents plus the edge self-current) and the cofinal Haar row are eventually smaller in absolute
value than

```text
epsilon (n+1) |P_(2D(stage_sigma(n))+3)(z_n)|^2.
```

The Lean capstone is
`eventually_logarithmicHaarTopRow_and_twoPhaseFullDefectCurrents_lt_scaled_normSq` in
`XiCTaylorThetaTailFiniteTranslationDefectCurrent.lean`.  The proof keeps the packet and edge
value--derivative pairs intact and reflects only these bounded finite objects; it does not reflect
the one-sided mesh or change the Taylor denominator.  It uses the canonical density exponential
moments and the local analytic order of Xi, but no Xi divisor data, real-rootedness,
anti-Herglotz positivity, limiting measure, or continued-Cauchy sign.

The remaining open term in this card is the untruncated raw theta-tail/seam mixed current.  The
full core-current theorem remains RH-equivalent.

## Self-consistent weighted Haar current: exact integrated theorem

**[PROVED, LEAN]** The fixed-half-line Fubini calculation for the phase-adapted weighted
polarization is now exact.  This closes the formal bookkeeping left open after `(36)`--`(39)`.
It does not yet close the RH-equivalent raw core-current condition, for the reason stated at the
end of this section.

Put

```text
p_x(z)=exp(ixz),
E(x)=exp(-x/2),
R(z)=integral_(0,infinity) rho(x)p_x(z) dx,
R'(z)=integral_(0,infinity) rho(x) ix p_x(z) dx.
```

The two seam moments are

```text
integral_(0,infinity) E(x)p_x(z) dx=(1/2-iz)^(-1),
integral_(0,infinity) E(x)ixp_x(z) dx=i(1/2-iz)^(-2).    (40)
```

For the second identity, set `c=-1/2+iz`, whose real part is negative in the canonical strip.
The finite primitive

```text
integral_0^b x exp(cx) dx=[(cx-1)exp(cx)/c^2]_0^b
```

passes to `b=infinity` because both `exp(cb)` and `b exp(cb)` tend to zero.  Hence the moment is
`1/c^2`; multiplication by `i` gives `(40)`.  This also proves all four seam integrability
statements used below.

Let

```text
P=A_(m,u;q,r,tau),  u=p_(log 2)(z),
A_(P,N)(x)=sum_j P_j q^j R_(N+j)(x),
```

where `R_k` is the exact one-variable Haar residual.  The endpoint equations `P(q)=1` and
`P(r)=tau` give the pointwise source identity

```text
A_(P,N)(x)
 =a_N sum_j P_j g(x-(N+j)log 2)-rho(x)+c_(N,tau)E(x),
c_(N,tau)=(2^N tau+1)/4.                                (41)
```

The double phase root of `P` cancels the full-line translate vector and its translation drift.
Writing `V_(P,N)` and `D_(P,N)` for the coefficient-weighted returned value and derivative tails,
respectively, integration of `(41)` gives exactly

```text
Ahat_(P,N)(z) =-V_(P,N)(z)-R(z)+c_(N,tau)Ehat(z),
Ahat'_(P,N)(z)= D_(P,N)(z)-R'(z)+c_(N,tau)Ehat'(z).      (42)
```

All exchanges in `(42)` are finite sums; integrability follows from the full-line exponential
bound for the even theta remainder and `(40)`.

The complete coefficient-weighted reflected Haar prefix is the symmetric rank-two tensor

```text
S_(P,N)(x,y)=1/2[A_(P,N)(x)E(y)+E(x)A_(P,N)(y)].         (43)
```

For arbitrary real sources `A,E` and any integrable value--derivative kernel `(V,D)`, Fubini and
one complex-algebra identity give

```text
integral S(x,y) K_(V,D)(x,y) dxdy
 =1/2 Cross((Ahat,Ahat'),(Ehat,Ehat')).                  (44)
```

Keeping both cross terms together and inserting `(42)` into `(44)` identifies the literal
integrated signed Haar-prefix current with one half of
`phaseAdaptedCriticalReturnedSourceCurrent`.

The latter current is affine in `tau`.  Its normalized slope tends to the nonzero seam current

```text
Im(Ehat'(z) conjugate(Ehat(z)))>0.
```

Therefore, at every point `0<Im z<1/2`, some finite depth has nonzero affine denominator.  Choosing
at that depth the exact self-consistent endpoint `tau=tau_(m,N,z)` gives

```text
integral S_(P,N)(x,y) K_z(x,y) dxdy=0.                  (45)
```

Consequently, on every admissible anisotropic schedule and for every positive `epsilon`, the depth
may be selected separately at each mesh point so that the left side of `(45)` is strictly smaller
than

```text
epsilon (n+1) |P_(2D(stage(n))+3)(z_n)|^2.              (46)
```

The Lean implementation is
`XiCTaylorThetaTailPhaseAdaptedProuhetIntegratedHaarCurrent.lean`.  Its capstones are
`canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_eq`,
`exists_canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_eq_zero`, and
`eventually_exists_canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_lt_scaled_normSq`.
Their axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Finite source-arithmetic endpoint: untruncated current discharged

**[PROVED, LEAN]** The endpoint can be made independent of the full transform pair `(R,R')`.
Let

```text
rho_<M(x)=sum_(1<=k<=M) rho_k(x),
R_M(z)=integral_(0,infinity) rho_<M(x) exp(ixz) dx,
R_M'(z)=integral_(0,infinity) rho_<M(x) ix exp(ixz) dx.   (47)
```

Define `tau_M` by the same finite affine endpoint formula as in `(45)`, but with `(R_M,R_M')`
in place of `(R,R')`.  This is a genuinely finite arithmetic coefficient: it uses only the first
`M` exact square-index density atoms and the elementary seam values.  The Haar endpoint slope and
its denominator do not involve `(R,R')`.  Therefore substitution into the *actual* canonical
current cancels the denominator exactly and gives

```text
J_actual(tau_M)=J_0(R,R')-J_0(R_M,R_M').                (48)
```

No division estimate and no current-dependent sign choice remains.  Positivity of the density
atoms gives

```text
0<=rho_<M(x)<=rho(x),
rho_<M(x)->rho(x).
```

On `Im z>=0`, the phase has norm at most one.  Dominated convergence with dominators `rho(x)` and
`x rho(x)` proves

```text
R_M(z)->R(z),  R_M'(z)->R'(z),  J_actual(tau_M)->0.      (49)
```

At each anisotropic mesh point, first choose a finite Haar depth with nonzero elementary affine
denominator and then choose `M` in `(49)`.  The existing local-order lower bound makes the squared
final Taylor value strictly positive eventually.  Hence, for every `epsilon>0`,

```text
integral S_(P_(tau_M),N)(x,y) K_(z_n)(x,y) dxdy
 <epsilon (n+1)|P_(2D(stage(n))+3)(z_n)|^2.             (50)
```

The Lean implementation is
`XiCTaylorThetaTailFiniteArithmeticEndpoint.lean`.  Its capstones are
`phaseAdaptedReturnedSourceCurrent_at_approximantEndpoint_eq`,
`tendsto_canonicalThetaTailFiniteArithmeticUntruncatedCurrent`,
`phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint_eq`, and
`eventually_exists_canonicalThetaTailFiniteArithmeticHaarCurrent_lt_scaled_normSq`.

Equation `(50)` closes the independent upper-sublinear cancellation theorem for the complete
untruncated signed theta-tail/seam Haar current.  It does not close the RH-equivalent raw
core-current predicate.

## Exact finite-arithmetic conservation and no-shortcut equivalence

**[PROVED, LEAN]** The final composition has now been audited exactly.  At the canonical
finite-arithmetic endpoint the raw core current is

```text
J = (1/8) prefix + (1/4) remainder,
remainder = topRow + survivingTranslation
          = 4J - (1/2) prefix.                           (51)
```

The cofinal selector makes `prefix` and `topRow` arbitrarily small.  It cannot make the combined
`remainder` small: at fixed arithmetic cutoff, every change in `topRow` is transferred with the
opposite sign to `survivingTranslation`.  As the finite density cutoff exhausts the source,

```text
remainder -> 4J.                                        (52)
```

Thus the earlier proposed composition double-counted a cancellation.  The exact survivor is a
conserved Haar-refinement current, not an independently decaying error.

The converse logical audit is also formalized.  Under RH, `XiC` is nonzero at the limiting point
of each open left-strip anisotropic fibre.  Superaccuracy then bounds the raw core value and
derivative and bounds the Taylor denominator away from zero, giving the absolute estimate

```text
|J_n| = O(1) = o(n)|P_n(z_n)|^2.                        (53)
```

Together with the cofinal small-prefix selector and `(51)`, this proves the exact equivalences

```text
finiteArithmeticRemainderJointSublinearUpper D
  <-> XiCTaylorThetaTailCoreCurrentSublinearUpper D
  <-> RiemannHypothesis.                                (54)
```

The Lean implementations are
`XiCTaylorThetaTailCoreCurrentCapstone.lean` and
`XiCTaylorThetaTailCoreCurrentRemainderEquivalence.lean`.  The second module proves
`eventually_abs_xiCTaylorThetaTailCoreCurrent_lt_scaled_normSq_of_riemannHypothesis`,
`xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis`, and
`xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_coreCurrentSublinearUpper`.

This retires the finite-arithmetic composition as a source producer.  The card remains open only
at its original target: an unconditional source theorem that orients or dissipates the raw
current `J` itself.  Any proof of the combined remainder bound without new source structure is
already an RH proof by `(54)`.

## Full-density monotone contraction and exact transfer frontier

**[PROVED, NEW SOURCE REDUCTION]** The complete canonical density
`rho=4 thetaCuspTailDerivative 2` is strictly decreasing on `[0,infinity)`.  Put

```text
F(z)=integral rho(t) exp(i t z)dt,
D(z)=integral rho(t) i t exp(i t z)dt,
h(t)=-rho'(t)>0.
```

Two exact integrations by parts give positive completion identities

```text
G_h(z)=-i z F(z),
G_h'(z)=-i(F(z)+zD(z)).                                  (55)
```

For `Im z>0`, `Re G_h(z)>0`; hence `F(z)!=0`.  The pointwise completion contraction gives

```text
|D(z)| <= (2/Im z)|F(z)|,
|D(z)/F(z)| <= 2/Im z,
|Im(D(z)conj(F(z)))| <= (2/Im z)|F(z)|^2.                (56)
```

Exact product-fibre reassembly identifies current in `(56)` with absolutely convergent sum of all
actual Hermitian product-fibre currents.  Thus positive prime-cube faces cancel in full continuous
aggregate.  This is not fibrewise sign and does not use discrete sampling.

Zero-freeness of `F` creates canonical finite transfer

```text
T_d(z)=P_(2d+3)(z)/F(z).
```

Quotient rule and product-current Leibniz identity yield, without assuming `P_d!=0`,

```text
J(P_d)=|T_d|^2 J(F)+|F|^2 J(T_d),
J(P_d)<= (2/Im z)|P_d|^2+|F|^2 J(T_d).                  (57)
```

The `2/Im z` term is `O(1)` on every anisotropic mesh.  Formal forward and reverse transport prove

```text
XiCTaylorFullDensityTransferCurrentSublinearUpper D
  <-> RiemannHypothesis.
```

This is a valid exact gauge localization of `(54)`: all untruncated full-density arithmetic current
is discharged unconditionally and final Taylor denominator is preserved by `P_d=T_dF`.

**[CORRECTED BY HOSTILE WRONSKIAN TEST]** It is not a finite-truncation localization.  Put

```text
W_d=P_d'F-P_dF',
Omega_F=XiC'F-XiC F',
R_d=XiC-P_d.
```

Then exact algebra and Taylor convergence give

```text
W_d=Omega_F-(R_d'F-R_dF'),
W_d(z)->Omega_F(z),
Omega_F(0)!=0.
```

Consequently `T_d->XiC/F`, `T_d'->(XiC/F)'`, and `J(T_d)->J(XiC/F)` pointwise.  Because `F` is
zero-free in the upper half-plane, `XiC/F` has exactly the Xi zeros.  Transfer predicate therefore
retains full divisor rather than isolating truncation.  Pure-remainder route is retired in
`../5-failed/xi-taylor-full-density-transfer-wronskian.md`.

Exact completed reflection identifies surviving background with reflected growing channel:

```text
C_F=2z(F+F(-z))F-(z^2+1/4)(F'(-z)F+F(-z)F')+(1/2)F'
   =8z XiC F+4z^2 Omega_F.
```

Hostile differentiation further corrects that projective frontier.  If `R=E#/E`, its derivative
is generated by

```text
W_E=(E#)'E-E#E',
```

not by `C_F`.  At a Xi zero,

```text
W_E-q C_F=-z^2 XiC',
```

so two connections differ at every noncentral simple collision.  Division-free flow
`V_E=E^2 conjugate(W_E)` satisfies `dR(V_E)=|W_E|^2`; regular no-return is automatic and cannot
exclude one interior antipodal crossing on an unanchored component.

The later transverse Pick cone

```text
Im(z)|F(z)| <= Im(zF(z))
```

proves `E(z)!=0` throughout the upper half-plane.  Hence `R` has no upper poles, and interior
affine-pencil collisions cannot change total zero multiplicity.  Bottom, imaginary, and horizontal
boundaries reduce by existing source orientation and theta-Schwartz decay.  Actual frontier is now
the top-edge acute-angle/nonintersection law for the affine pencil joining `E` to `2z^2 XiC`.
See `xi-completed-density-affine-pencil-top-edge-barrier.md`.

Lean implementation:
`XiCTaylorThetaTailFullDensityMonotoneCurrent.lean` and
`XiCTaylorThetaTailFullDensityWronskianNoGo.lean`, followed by
`XiCTaylorThetaTailCompletedDensityProjectiveCollision.lean` and
`XiCTaylorThetaTailCompletedDensityTransversePick.lean`.
