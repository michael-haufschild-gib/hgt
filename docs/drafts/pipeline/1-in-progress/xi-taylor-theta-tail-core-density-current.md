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

Thus the top row is now eliminated pointwise by a certified double-exponential majorant.  The
remaining top-row task is only the degree-uniform moment estimate needed to pass `(12d.7a)`
through `K_d` when `d` moves with the anisotropic schedule.  The finite Haar sum is not yet
oriented: each parity wavelet has bilateral Mellin factor
`(2^(1-s)-1)zeta(s)` and therefore retains the nontrivial Xi factor.  Dropping the negative Haar
currents would silently assume their sign.  The live theorem is consequently narrower: prove a
joint upper estimate for the signed *finite sum* in `(12d.7)` while sending the explicit top row
to zero; no termwise positivity statement is available.

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
consists of two explicit odd-row/decaying-character cross terms and the favorable negative radial
square `-2^(k-2)exp(-(x+y)/2)`.  This is stronger than the atomwise Lorentz polarization because it
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

It is not yet the current theorem.  Reflecting the parity integral sends the positive quadrant to
the negative quadrant, while the surviving odd row in `(12d.8b)` is translated by `ell_k`.
Transport back to the positive source half-line sweeps a finite interval of length `ell_k`, and
`H_d(z,x+log 2)` is not equal to `H_d(z,x)`: its finite cosine translation mixes the even and odd
Taylor sections.  This identifies the next exact gate without a sign assumption: polarize that
two-component finite translation and prove that its current change is a constant phase multiple
of the squared translated value plus a schedule-superaccurate top defect.

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
- [x] derive the exact mean-zero density-score covariance and rule out pointwise phase ordering
- [x] identify the current with the vertical derivative of the finite squared modulus
- [x] derive and formalize the real-boundary-to-interior complex Laguerre-defect identity
- [x] audit classical theta, orthogonal-polynomial, spectral, and Wigner value relations
- [ ] prove an integrated cancellation bound for the raw moment terms in `(12)`
- [ ] obtain the eventual scaled core-current inequality on every anisotropic fibre
- [ ] complete paper proof and Lean theorem
