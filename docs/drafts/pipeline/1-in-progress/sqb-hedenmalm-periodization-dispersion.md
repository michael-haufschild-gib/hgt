# SQB–Hedenmalm periodization dispersion

- **Stage:** 1-in-progress; exact paper identity, Lean formalization open.
- **Route:** SQB, using the corpus's Hedenmalm exact-spectrum carrier.
- **Claim boundary:** The original scalar periodization has an exact metric loss; a uniquely source-matched complete-row lift preserves the Hedenmalm metric and isolates the fixed forcing. Its fluctuation channel has exact one-dimensional kernel, retained Xi-mode mass, and a one-dimensional multivalued differential defect. One fixed cusp-weighted Hilbert norm detects off-real Xi zeros throughout the physical strip: a source-faithful regularity occurrence, not a self-adjoint spectral occurrence. No RH proof follows.
- **Frontier map:** read-only.

## Chain and hard obstacle

The fixed Hedenmalm compact theta operator already has exact Xi-divisor
occurrence. SQB has a self-adjoint native Maass operator and a critical-line
classifier, but its Xi-conditioned theta modes obey a *forced* equation.
The positive metric can now be transported with every primitive row retained.
The fluctuation quotient removes the forcing and retains nonzero mass, but
its raw differential relation has a one-dimensional multivalued defect and
nonreal eigenpairs at generic free-resolvent parameters. The sharpened
single-weight criterion (15c') recovers the exact Xi selection inside one
positive fluctuation Hilbert space. The hard obstacle is **a closed Green
law on this no-radiation domain that controls the combined moving-projection
leakage and weight-induced dilation current**. A norm comparison that drops
cross-row contribution cannot accomplish that law.

## The common literal mode

Write `Phi = thetaCuspFullSource` and let `alpha = xiSpectralPoint q` for an
actual Xi zero copy. The corpus proves the exact equality

```text
u_alpha(x) = sourceModeU(thetaSource,alpha,x)
           = hedenmalmCausalVolterra(alpha,x).
```

The Hedenmalm source eigenvector is the quantile image of `-alpha*u_alpha`.
The SQB seed is `sqrt(y)*u_alpha(log(y)/2)`. Consequently the two carriers
are made from the same zero-conditioned causal function, though they use
different Hilbert norms and different operators. This is an actual source
identification, not a spectral intertwiner.

## Exact dispersion identity [PAPER-PROVED]

At a modular point `Z`, index the complete primitive rows by `v` and put
`y_v = Im(gamma_v Z)`, `x_v = log(y_v)/2`,

```text
a_v = sqrt(y_v)*Phi(x_v) > 0,
r_v = u_alpha(x_v)/Phi(x_v),
b_v = a_v*r_v.
P(Z) = sum_v a_v,                 W_alpha(Z) = sum_v b_v.
```

The corpus proves these row sums absolute. Its global bound on `r_v`
makes the following quadratic sums absolute as well. Finite weighted
variance, followed by the absolute limit, gives

```text
D_alpha(Z)
  := sum_v |b_v|^2/a_v - |W_alpha(Z)|^2/P(Z)
   = (1/(2*P(Z))) sum_v sum_w a_v*a_w*|r_v-r_w|^2
   >= 0.                                                  (1)
```

No row or reflected cross term has been removed. Integrating (1) over the
original modular quotient and unfolding only the **diagonal** row sum gives

```text
2 integral_R exp(-x)*|u_alpha(x)|^2/Phi(x) dx
   = integral_F |W_alpha(Z)|^2/P(Z) dmu(Z)
     + integral_F D_alpha(Z) dmu(Z).                    (2)
```

Indeed, the strip integral of the diagonal seed is
`integral_0^infinity y^(-3/2)|u_alpha(log(y)/2)|^2/Phi(log(y)/2) dy`;
the substitution `y=exp(2x)` gives the left side. Its integrability follows
from bounded `u_alpha/Phi`, the theta all-rate envelope and the established
positive-source strip unfolding. Equation (2) is a strict data-processing
law for the **actual** modular periodization. The exponential tilt on its
left is forced by the native half-density and must not be replaced by the
untilted Hedenmalm metric.

Equation (2) has a **conservative two-channel form**. On compactly
supported smooth source functions `f`, use the same row weights `a_v` and
put `r_v=f(x_v)/Phi(x_v)`, `R_f(Z)=sum_v a_v*r_v/P(Z)`. Define

```text
T_f(Z)   = sqrt(P(Z))*R_f(Z) = W_f(Z)/sqrt(P(Z)),
S_f(Z,v) = sqrt(a_v)*(r_v-R_f(Z)).
```

The finite weighted-variance identity, absolute passage and source
unfolding prove the exact norm law

```text
||T_f||²_(L²(F)) + ||S_f||²_(L²(F;ell²(rows)))
  = 2 integral_R exp(-x)*|f(x)|²/Phi(x) dx.            (2a)
```

Thus `(T,S)` extends by completion to an isometric embedding from the
tilted source Hilbert space `L²(R,2 exp(-x)/Phi(x) dx)` into a modular
scalar field plus a row-fluctuation fiber. For the actual zero mode,
`||S_u||²=integral_F D_alpha` and its row formulas follow by truncation
and the proved theta envelopes. This is a source-defined *information
preserving lift* of modularization; its first component is the scalar SQB
field divided by `sqrt(P)`. The extra channel is forced by the actual primitive rows,
not chosen from the Xi divisor. Its source norm has the displayed tilt,
so this is not yet an intertwiner from Hedenmalm's untilted operator
domain to the unchanged SQB Maass operator.

The first operator-action calculation is exact on compact source tests.
Write `Q=Phi'/Phi`, `w=2 exp(-x)/Phi(x)` and `D=-i d/dx` in the tilted
source Hilbert space of (2a). Integration by parts gives

```text
D^dagger = D-i*w'/w = D+i*(1+Q),
D_symmetric = (D+D^dagger)/2 = D+(i/2)*(1+Q).          (2b)
```

The actual causal mode obeys `(D+alpha)u_alpha=-Phi`, so

```text
(D_symmetric+alpha)u_alpha
   = -Phi+(i/2)*(1+Q)*u_alpha.                         (2c)
```

Both terms on the right are literal source data. The score `Q` is also
the retained term in SQB's gauged source equation. Equations (2b)–(2c)
show what a two-channel symmetric operator must cancel or carry through
an adjoint coupling; simply transporting the exact-spectrum operator by
the isometry (2a) preserves its non-self-adjoint defect. No cancellation
operator has been constructed here.

## Source-matched modular lift [PAPER-PROVED]

The SQB common-forcing field uses the **reflected pair**, not the single
causal mode in (1). Put `p_alpha = -(u_alpha-u_(-alpha))/(2*alpha)` at an
actual Xi zero. The source equations and reflected parity give

```text
p_alpha(-x) = p_alpha(x),
p_alpha'' + alpha^2*p_alpha = Phi,
u_alpha = -alpha*p_alpha - i*p_alpha'.                (5)
```

Both `p_alpha` and `p_alpha'` decay at both ends by the established
two-ended theta bounds. Since the product of the even `p_alpha` and odd
`p_alpha'` is odd and integrable,

```text
integral_R |u_alpha|^2 dx
  = integral_R (|p_alpha'|^2+|alpha|^2*|p_alpha|^2) dx.
J_alpha = (2*Im(alpha)/m)
  * integral_R (|p_alpha'|^2+|alpha|^2*|p_alpha|^2) dx. (6)
```

There is a canonical change of positive row reference which matches this
**untilted** Hedenmalm Green-energy metric and retains pure-scalar forcing. At each
primitive row set

```text
a_v^* = (1/2)*y_v*Phi(x_v)^2
      = (1/2)*positiveProfile(y_v)^2 > 0,
r_v^f = f(x_v)/Phi(x_v),
P^*(Z) = sum_v a_v^*,       W_f^*(Z) = sum_v a_v^* r_v^f,
T_f^*(Z) = W_f^*(Z)/sqrt(P^*(Z)),
S_f^*(Z,v) = sqrt(a_v^*)*(r_v^f-W_f^*(Z)/P^*(Z)).
```

The positive row sum is finite: `positiveProfile` is bounded and its
complete row sum is finite, so the sum of its squares is finite. For
compactly supported smooth `f`, weighted variance followed by the
original strip unfolding gives

```text
||T_f^*||² + ||S_f^*||²
  = integral_F sum_v a_v^* |r_v^f|² dmu
  = integral_0^infinity (1/(2*y))*|f(log(y)/2)|² dy
  = integral_R |f(x)|² dx.                           (7)
```

Hence `V:f ↦ (T_f^*,S_f^*)` extends to an isometry from the **Green-energy**
source space `L²(R,dx)` into the scalar modular channel plus
complete primitive-row fluctuation channel. The actual `u_alpha`,
`p_alpha` and `p_alpha'` are admitted by the two-ended source envelopes.
Their entire Green current is now represented by positive modular norms:

```text
J_alpha = (2*Im(alpha)/m)
  * (||V p_alpha'||² + |alpha|²*||V p_alpha||²).      (8)
```

There is a sharper **pointwise two-channel law**. Put
`sigma=Re(alpha)`, which the actual divisor support makes nonzero. The
corpus proves the strict source disk
`|1+sigma*u_alpha(x)/Phi(x)|<1` at every `x`. Apply it at `x` and `-x`,
use (5), and average the two squared inequalities. The odd derivative
cross term cancels exactly:

```text
|Phi(x)-sigma*alpha*p_alpha(x)|²
  + sigma²*|p_alpha'(x)|² < Phi(x)².              (8a)
```

Multiplying this by `y_v/2`, summing every primitive row, and using the
orthogonal mean/fluctuation split of (7) gives, at **every** modular point,

```text
|sqrt(P^*)-sigma*alpha*T_(p_alpha)^*|²
  + sigma²*(|alpha|²*||S_(p_alpha)^*||²
              + |T_(p_alpha')^*|² + ||S_(p_alpha')^*||²)
  < P^*.                                           (8b)
```

All terms are finite because `p_alpha/Phi` and `p_alpha'/Phi` are bounded.
This retains the derivative energy and the full primitive-row dispersion
which a scalar disk discards. Integrating (8a), then multiplying
`p_alpha''+alpha²*p_alpha=Phi` by `conj(p_alpha)` and integrating by
parts, yields the strict frequency-dominance law

```text
3*integral_R |p_alpha'|² dx
  < |alpha|²*integral_R |p_alpha|² dx.             (8c)
```

Indeed `integral Phi*conj(p_alpha)=-||p_alpha'||²+alpha²*||p_alpha||²`;
expanding the integrated square in (8a) reduces its strict deficit to
`sigma²*(|alpha|²*||p_alpha||²-3*||p_alpha'||²)`. The inequality is
theta-specific because its input is the corpus's proved strict disk for
the literal theta source, not positivity of an arbitrary even kernel.
It holds for every actual Xi zero, including critical-line ones; it is
not itself a reality criterion.

The fixed source is **purely scalar**: `r_v^Phi=1`, so
`V Phi=(sqrt(P^*),0)`. Moreover, within lifts having rows
`a(x) f(x)/Phi(x)` and scalar source `a(x)`, equation (7) for every compact
test forces `2*exp(-2*x)*a(x)/Phi(x)^2=1` almost everywhere. For continuous
positive row references this uniquely gives `a(x)=exp(2*x)*Phi(x)^2/2`.
Thus (7) does not come from a freely chosen normalization.

Let `D=-i*d/dx` on its standard `H¹(R)` domain. The isometry makes
`A=V D V⁻¹` self-adjoint on the **closed range of V**; this is the
transported free source derivative, not the unchanged native Maass
operator or the compact Hedenmalm exact-spectrum operator. The literal
causal equation becomes

```text
(A+alpha) V u_alpha = -(sqrt(P^*),0).               (9)
```

Equation (9) is a closed, source-derived, parameter-independent forcing
law in an honest positive modular Hilbert space. It removes the metric
tilt and score mismatch of (2b)--(2c), but it is still a *forced*
resolvent equation. For nonreal `alpha`, self-adjointness of `A` supplies
a unique resolvent response rather than excluding `alpha`; no reality
claim follows from (9). A producer must show that the source work
`Im <(sqrt(P^*),T_(u_alpha)^*>` vanishes (or impose a stronger independent
source law) at actual Xi zeros. By the Green identity this vanishing is
equivalent to `Im(alpha)=0`, so it cannot be assumed as a metric or
boundary convention.

This changes the whole-chain target: the correct positive transfer is
available, with its source port isolated, but Xi zeros are nodes of the
analytic theta spectral amplitude rather than eigenvalues of `A`.
The remaining jump is a **theta-specific source-work cancellation** at
those nodes or source-generated unforced occurrence in the unchanged
native Maass carrier.

## Exact native cross-row current [PAPER-PROVED]

The unchanged native SQB Maass equation can now be compared with the
source-matched diagonal pairing without identifying their operators. Let
`P_0(Z)=sum_v sqrt(y_v)*Phi(x_v)` and
`W_p(Z)=sum_v sqrt(y_v)*p_alpha(x_v)`. These are the corpus's original
`positiveSource` and reflected `source`; the latter belongs to the
closed Maass domain and obeys

```text
L W_p = ((5+alpha²)/4)*W_p - P_0/4,
L = the unchanged self-adjoint native energyOperator.
```

The source-matched numerator is
`W_p^*(Z)=sum_v y_v*Phi(x_v)*p_alpha(x_v)/2`. Thus the complete
off-diagonal pairing, defined without conditional rearrangement, is

```text
C_off(Z) = P_0(Z)*conj(W_p(Z)) - 2*conj(W_p^*(Z))
         = sum_(v != w) sqrt(y_v*y_w)
             *Phi(x_v)*conj(p_alpha(x_w)).            (10)
```

At each point both row sums are absolute. The full product is integrable
because `P_0,W_p` are native `L²`; the diagonal is integrable by ordinary
source unfolding and `Phi*p_alpha ∈ L¹`. Therefore the integrated
off-diagonal expression is unambiguous. Pairing the native equation with
`conj(W_p)` and using self-adjointness gives

```text
Im integral_F P_0*conj(W_p) dmu
  = Im(alpha²)*||W_p||² = 2*Re(alpha)*Im(alpha)*||W_p||².
```

The diagonal unfolds to `2*integral_R Phi*conj(p_alpha) dx`;
`p_alpha''+alpha²*p_alpha=Phi` and integration by parts make its
imaginary part `2*Im(alpha²)*||p_alpha||²`. Subtraction proves

```text
Im integral_F C_off dmu
  = Im(alpha²)*(||W_p||²-2*||p_alpha||²).             (11)
```

Equation (11) is the signed, all-row transport law missing from a
diagonal norm argument. It does **not** determine its own sign: the
source-matched ellipse (8b) controls positive diagonal and fluctuation
terms, while (11) depends on native cross-row interference. The
remaining possible producer is a theta-specific signed law for this
off-diagonal interaction, strong enough to force `Im(alpha²)=0` without
assuming a reality or boundary condition at the Xi divisor.

The corpus already computes the horizontal mean `H(y)` of `P_0` and its
arithmetic constant term. Unfolding the *first* row in (10) gives

```text
integral_F C_off dmu
  = 2*integral_R exp(-x)*conj(p_alpha(x))
      *(H(exp(2*x))-positiveProfile(exp(2*x))) dx.
```

Its exact logarithmic source identity is
`H(exp(2*x))-positiveProfile(exp(2*x))
 = 2*exp(x)*SelbergThetaHorizontalTransform.kernel(-2*x)`.
Consequently (11) is equivalently

```text
4*Im integral_R kernel(-2*x)*conj(p_alpha(x)) dx
  = Im(alpha²)*(||W_p||²-2*||p_alpha||²).          (12)
```

The kernel is strictly positive on the real line: it is the horizontal
mean of all **nonparabolic** positive primitive rows divided by
`2*exp(x)`. Yet its transform on the corpus's absolute-convergence
half-plane is `Xi` times a completed-zeta scattering ratio. Thus the
native cross-row current is a one-dimensional pairing against a
source-only arithmetic scattering kernel. This is the conceptual bridge
from SQB's modular Green work to the signed arithmetic/causal questions
in L and PSRC. The broad corpus follow-up found that the continuation
and boundary step **already exists**:
`SelbergThetaNativeScalarBoundary.lean` gives the full scalar response as
a Cauchy transform, `SelbergThetaNativeMeanCancellation.lean` cancels its
mean residue, and `SelbergThetaCommonForcingPacketMass.lean` gives the
nonnegative boundary density `Xi(t)^2*boundaryWeight(t)`. Hence (12)
decomposes an already-closed native Gram interface into its diagonal and
nonparabolic pieces; it supplies no new spectral selection by itself.
The missing step is to produce an **unforced native mode with retained
mass** from source data. The positive Cauchy density proves mass for
each nontrivial finite packet, but the existing corpus does not prove
source-generated forcing cancellation together with a nonvanishing
normalized limiting packet.

There is strict loss at some modular point for every actual zero copy.
If `r(x)=u_alpha(x)/Phi(x)` were even, then `u_alpha` would be even. But its
equation `u'=-i*alpha*u-i*Phi` would have an odd left side and an even right
side; both would vanish, forcing `u` constant and `Phi` constant, contrary
to the positive decaying theta source. Hence some `x>0` has
`r(x) != r(-x)`. At `Z=i*exp(2x)`, the parabolic row and the primitive
inversion row have heights `exp(2x)` and `exp(-2x)`, so their summand in
(1) is strictly positive. Thus the dispersion is not a bookkeeping zero.
Local uniform row convergence gives continuity near this point and strict
positivity of the integrated dispersion in (2). This last continuity step
still needs a Lean proof using the existing source envelopes.

The common mode also gives an **exact reflected balance**, which isolates
the orientation that a positive variance alone cannot carry. Let
`E_alpha = integral_F |W_alpha|²/P`, `Delta_alpha = integral_F D_alpha`, and
`M_±(alpha)=integral_R exp(±x)|u_alpha(x)|²/Phi(x) dx`. At a Xi zero the
two-ended source identity and evenness of `Phi` give
`u_(-alpha)(x)=-u_alpha(-x)`, hence `M_-(−alpha)=M_+(alpha)`.
Subtracting (2) for the two reflected copies yields

```text
[E_alpha-E_(-alpha)] + [Delta_alpha-Delta_(-alpha)]
  = 2[M_-(alpha)-M_+(alpha)]
  = -4 integral_R sinh(x)*|u_alpha(x)|²/Phi(x) dx.       (3)
```

All integrals are absolute by the all-rate source envelope. Equation (3)
is a reflection-odd conservation law for the *complete* modular map. It
identifies the sign-sensitive quantity to compare with the Hedenmalm Green
current; no sign or vanishing assertion for its right side is made.
The corpus's compact-flux and root-energy identities make that comparison
numerically precise: with `m=integral_R Phi(x) dx`, the rank-two current of
the actual quantile eigenvector is

```text
J_alpha = (2*Im(alpha)/m) integral_R |u_alpha(x)|² dx.   (4)
```

Equations (3) and (4) involve different source measures. Any asserted
transport must derive their relation from the literal theta source; the
shared mode alone does not equate them.

## Fluctuation relation and the missing boundary datum [PAPER-PROVED]

The complete-row lift changes the operator question. Its fluctuation part
`S^*` kills the literal forcing, since `S^* Phi = 0`. It does **not** kill the
paired zero response. More precisely, on continuous `L²(R)` source profiles,

```text
ker(S^*) = C*Phi.                                        (13)
```

Here equality means equality as continuous functions, and `S^* f=0` means
zero in the row-fluctuation `L²` space. To prove (13), positivity of every
row weight first gives equality of the ratios `r=f/Phi` for the identity and
inversion rows almost everywhere on the open modular region
`Z=s+i*y`, `|s|<1/2`, `y>1`. Both ratios are continuous, so the equality
holds everywhere there. With `t=(log y)/2>0`, it reads

```text
r(t) = r(t - (1/2)*log(exp(4*t)+s²)).                 (14)
```

At `s=0` this gives `r(t)=r(-t)`. Varying `s` makes `r` constant on a
nonempty interval immediately to the left of `-t`, with value `r(t)`.
These intervals overlap for nearby `t`; hence `r` is locally constant on
`(0,infinity)`, and therefore constant there. Reflection and continuity
extend the constant to all of `R`. The converse in (13) is immediate.
This uses only the two literal primitive rows and the geometry of the
fundamental domain; it is not a positivity assertion about the scalar
periodization.

For the paired response, `p_alpha''+alpha²*p_alpha=Phi` and (13) imply

```text
S^* p_alpha'' + alpha²*S^* p_alpha = 0,
S^* p_alpha != 0.                                    (15)
```

Indeed, if `S^* p_alpha=0`, then `p_alpha=c*Phi`. Fourier transformation of
its differential equation gives
`(c*(alpha²-xi²)-1)*XiC(xi)=0` for every real `xi`. Since `XiC(0)!=0`,
`XiC` is nonzero on a real interval, whereas the displayed quadratic
polynomial cannot vanish on an interval. This is a **source-generated
homogeneous mode with positive retained fluctuation mass** for every actual
Xi zero. It is not yet an eigenvector of the unchanged SQB Maass operator.

The homogeneous relation alone is **not Xi-selective**. If `alpha²` is
nonreal, the self-adjoint free second derivative has the unique `H²`
forced response

```text
p_hat_alpha(xi) = Phi_hat(xi)/(alpha²-xi²).            (15a)
```

This exists for every such `alpha`, whether or not `XiC(alpha)=0`:
the denominator has no real zero and its inverse maps `L²` to `H²`.
The same argument gives `S^* p_alpha != 0`, so `R_fluc` has the
eigenpair `(S^* p_alpha,-alpha²*S^* p_alpha)` at every nonreal
`alpha²`. The raw quotient relation therefore cannot select Xi zeros.

What selects an actual Xi zero is a **no-radiation condition** on this
forced response. The literal theta source has all exponential moments,
and its Fourier transform is `XiC` up to fixed nonzero normalization.
The right side of (15a) is meromorphic in complex frequency with possible
poles at `±alpha`; evenness of `Phi` makes their cancellation equivalent
to `XiC(alpha)=0`. Within the off-real parameter region,

```text
XiC(alpha)=0
  <-> p_alpha has all-rate two-ended decay.               (15b)
```

For the forward implication, the zero of the source transform makes
the left Volterra primitive equal the negative right tail. Each end of
`u_alpha` is therefore bounded by a theta-source tail times a fixed
exponential of rate `|Im(alpha)|`; the corpus's all-shift integrability
of `Phi` gives every further exponential rate. The reflected-pair
formula transfers this to `p_alpha` and its first derivative, and the
differential equation gives the second derivative. This paired response
is the unique `H²` solution of (15a). Conversely, exponential
integrability of `p,p',p''` at every
finite rate permits Fourier--Laplace transformation of
`p''+alpha²*p=Phi` at frequency `alpha`; the left side vanishes and
gives `XiC(alpha)=0`. This is the source boundary condition that plain
positive `L²` geometry loses.

### The fluctuation channel detects no-radiation [PAPER-PROVED]

The modular row geometry restores that boundary datum in a **weighted
scale**, even though the unweighted relation above is nonselective. For
`Im(alpha)>0` and `alpha²` nonreal, let `p_alpha` be the unique `H²`
solution of (15a), and for `s>=0` set

```text
M_s(alpha) = integral_(F, y>1) y^s*
  sum_v |S^*_(p_alpha)(Z,v)|² dmu(Z).
```

Then the following source-faithful modular regularity criterion holds:

```text
XiC(alpha)=0  <->  M_s(alpha)<infinity for every s>=0. (15c)
```

The quantifier over all weights can be replaced by **one fixed Hilbert
weight on the physical Xi strip**. For `0<Im(alpha)<1/2` and
`Re(alpha)!=0`, let `p_alpha` be the unique `H²` free-resolvent solution
used in (15a). Then

```text
XiC(alpha)=0  <->  M_(5/2)(alpha)<infinity.             (15c')
```

The forward implication follows from the all-rate decay in (15b).
For the reverse, if `XiC(alpha)!=0`, the two-row lower bound (15e)
holds on every sufficiently high dyadic cusp band. The contribution
of a band of height `N` to `M_(5/2)` is at least
`c_alpha*N^(1/2-Im(alpha))`. Since `Im(alpha)<1/2`, these positive
contributions cannot sum to a finite value. This is a fixed, positive
Hilbert-space occurrence test for the entire physical strip; no
parameter-dependent intersection of weighted domains is needed.
The same argument gives `M_s(alpha)=infinity` whenever
`s>=2+Im(alpha)` and `XiC(alpha)!=0`. It makes no assertion that the
native Maass action is symmetric in this weighted space.

For the forward direction, (15b) gives for every `N` a bound
`|p_alpha(x)|<=C_N exp(-N*|x|)`. The full row vector in (17) therefore
has identity-row square at most `C_N*y^(1-N)` for `y>1`. A nonparabolic
row `(c,d)`, `c>=1`, has `y_(c,d)<=1/(c²*y)` and contributes at most
`C_N*y_(c,d)^(N+1)`. The elementary shifted-lattice estimate

```text
sum_(d in Z) [y/((c*s+d)²+(c*y)²)]^(N+1)
  <= C'_N*c^(-2*N-1)*y^(-N),  y>=1,
```

is uniform in the horizontal coordinate `s`. Summing `c` bounds
`||U_(p_alpha)(Z)||²` by `C''_N*y^(1-N)`. Pointwise orthogonal
projection gives `||S^*_(p_alpha)||<=||U_(p_alpha)||`, so choose `N`
larger than `s` and integrate against `dmu=ds*dy/y²`.

For the reverse direction, the free Green convolution and the source's
all-rate tails give, uniformly under bounded shifts as `x->+infinity`,

```text
p_alpha(x) = A_alpha*exp(i*alpha*x) + O_A(exp(-A*x)),
A_alpha = Phi_hat(alpha)/(2*i*alpha).                  (15d)
```

The fixed nonzero normalization of `Phi_hat` makes `A_alpha=0` exactly
when `XiC(alpha)=0`. Assume `A_alpha!=0`. On dyadic cusp bands
`N<=y<=2*N`, `|Re Z|<=1/4`, use just the two genuine primitive rows
`(1,N)` and `(1,2*N)`. Their logarithmic heights are
`-log(y)/2-h_1` and `-log(y)/2-h_2`, with `h_2-h_1` bounded below by a
positive absolute constant. The first-atom theta asymptotic therefore
gives `b_2/b_1 -> 0` uniformly, whereas (15d) gives
`U_(p_alpha),2/U_(p_alpha),1` bounded above and away from zero.
The exact two-coordinate least-squares inequality is

```text
sum_v |S^*_(p_alpha)(Z,v)|²
 >= |b_1*U_2-b_2*U_1|²/(|b_1|²+|b_2|²)
 >= c_alpha*N^(-1-Im(alpha))                         (15e)
```

for all sufficiently large dyadic `N`, with `c_alpha>0`. Integrating
one such band contributes at least a constant times
`N^(s-2-Im(alpha))` to `M_s(alpha)`. Choosing `s>2+Im(alpha)` makes
the dyadic-band sum diverge. Hence finiteness at every cusp weight
forces `A_alpha=0`, proving (15c). The projection cannot erase an
exponential radiation tail: two row heights separated on the cusp scale
have vastly different theta reference amplitudes but comparable
resolvent amplitudes.

Equation (15c) is a positive, source-faithful **regularity occurrence**
in the original modular quotient. It does not make `p_alpha` an
eigenvector of a self-adjoint Maass operator. The remaining jump is to
derive a closed operator/Green law on the all-weight fluctuation scale
which forbids a nonreal spectral parameter while retaining (15c).
The uniform first-atom ratio, lattice estimate, row-bundle domain and
weighted norm theorem still need Lean formalization.

The exact operator obstruction is one-dimensional, not an unspecified
failure of forcing cancellation. On the source Sobolev domain `H²(R)` let

```text
R_fluc = { (S^* f, S^* f'') : f in H²(R) }.
```

The theta source belongs to `H²` by its two-ended bounds. Equation (13)
gives the exact vertical fibre

```text
{ g : (0,g) in R_fluc } = C*(S^* Phi'').            (16)
```

It is genuinely one-dimensional: `S^* Phi''=0` would give
`Phi''=c*Phi`, contradicted by Fourier transformation and nonvanishing of
`XiC` near zero. Thus `R_fluc` is a multivalued differential relation,
not a self-adjoint operator merely because its source forcing vanished.
The scalar component `T^*` in (7) records precisely the one free `Phi`
coefficient lost by `S^*`; its remaining values are determined by the
fluctuation data when a source lift exists.

This reframes the hardest SQB step: transport the **source no-radiation
boundary condition** through the complete-row lift and prove that its
native differential relation has a positive self-adjoint selection
admitting exactly those responses. A generic positive source has the
same algebraic quotient and may have nonreal Fourier zeros, so the
selection must use the modular/arithmetic source law rather than
(13)--(16) alone. Lean formalization of (13)--(16) and (15b) remains
open.

There is a more concrete native-operator formulation. Before mean removal,
the complete-row vector simplifies to

```text
U_f(Z,v) = sqrt(y_v/2)*f(x_v),
b(Z) = U_Phi(Z),
Pi(Z) = |b(Z)><b(Z)| / ||b(Z)||²,
S_f^* = (1-Pi) U_f.                                    (17)
```

Thus `Pi` is a source-defined rank-one **moving projection** in the
native primitive-row bundle, and `b` is exactly the forcing row. The
unchanged rowwise Maass action satisfies
`L_row U_(p_alpha) = lambda_alpha*U_(p_alpha)-b/4`, with
`lambda_alpha=(5+alpha²)/4`. On any smooth core where the rowwise action,
projection and integrations by parts are valid, put `Q=1-Pi`. Then

```text
Q L_row Q (S_(p_alpha)^*)
  = lambda_alpha*S_(p_alpha)^* - Q L_row(Pi U_(p_alpha)). (18)
```

This is an exact algebraic identity; its full infinite-row domain
justification is open. It identifies the only coupling that stops the
nonzero homogeneous fluctuation (15) from being a native eigenvector:
the moving source line leaks into its orthogonal complement under the
Maass action. If the compressed operator has a self-adjoint closed
realization, pairing (18) with `S_(p_alpha)^*` gives the targeted signed
law

```text
Im(lambda_alpha)*||S_(p_alpha)^*||²
  = Im <S_(p_alpha)^*, Q L_row(Pi U_(p_alpha))>.      (19)
```

The left mass is strictly positive by (15). Proving that the right side
is real by a theta-specific modular/arithmetic identity would therefore
force `Im(alpha²)=0`, and `Re(alpha)!=0` then forces `Im(alpha)=0`.
Equations (18)--(19) are the next mathematical attack, not a claimed
vanishing: the scalar--fluctuation leakage may carry the entire Green
current. It must be computed with all primitive rows and the actual
domain, then compared with the known scattering kernel in (12).

### One-space Green formulation [formal differential identity; domain and sign open]

The fixed gate (15c') suggests using the single row-bundle space
`H_(5/2)` with measure `y^(5/2)*dmu=y^(1/2)*ds*dy` on the cusp.
There is a precise cost to moving the native Laplacian to that space.
On smooth compactly supported row tests, if the differential part of
the native action is `L=-y²*(partial_s²+partial_y²)` (an unchanged
scalar potential may be added), the weighted symmetric expression is

```text
L_w = L-(5/2)*y*partial_y,
U_w f = y^(5/4)*f,
U_w L_w U_w^(-1) = L+5/16.                         (19a)
```

The first equality is the divergence-form operator for the weighted
measure; the last follows by differentiating `y^(-5/4)g` twice.
The positive weighted geometry therefore supplies a self-adjoint
candidate, but its drift differs from the original source equation.
Writing `S=Q U_(p_alpha)`, `Q=1-Pi`, and `b=U_Phi`, the rowwise equation
in (18) gives the exact compact-core algebra

```text
Q L_w Q S
  = lambda_alpha*S
    - Q L(Pi U_(p_alpha))
    - (5/2)*Q(y*partial_y S).                         (19b)
```

Both terms on the right are forced by the same moving source line:
the first is its off-diagonal Maass leakage, while the second is the
drift required to keep the fixed Xi-selecting Hilbert metric symmetric.
If the compact-core identity extends to a closed symmetric realization
on `H_(5/2)`, an off-real Xi zero can survive only if the imaginary
pairing of their **sum** pays `Im(lambda_alpha)*||S||²_(H_(5/2))`.
The source problem is thus a single signed connection-current identity
in one fixed space. Neither (15c') nor formal symmetry proves that this
current vanishes; deriving its actual theta/prime cancellation is the
remaining RH-scale obstacle. The domain extension and equation (19b)
for the infinite row sum are not yet formalized in Lean.

The first Rellich test can be done exactly at the smooth compact-core
level. For a scalar field `u` satisfying
`Delta u+(a+i*b)*y^(-2)*u=F`, use the real-potential stress
`T_ij=2*Re(partial_i u*conj(partial_j u))
       -delta_ij*(|grad u|²-a*y^(-2)*|u|²)` and the dilation vector
`D=x*partial_x+y*partial_y`. Its trace is `2*a*y^(-2)*|u|²`;
the derivative of the inverse-square potential cancels that trace.
The exact remaining divergence is

```text
div(T D)
  = 2*Re(F*conj(D u))
    + 2*b*y^(-2)*Im(u*conj(D u)).                    (19c)
```

For the actual native scalar response `W_p`, the source equation gives
`a+i*b=lambda_alpha-1` and `F=P_0/(4*y²)`. Hence the two bulk terms
are respectively the **literal theta-source dilation work** and the
imaginary spectral phase current. Cusp no-radiation can remove a top
boundary; it cannot erase either interior term. In particular the
existing real-eigenvalue, unforced conservation theorem in
`SelbergMaassDilationStress` does not extend by simply taking a limit.
The attempted pure-boundary reduction fails. The positive next target
is a source-specific identity for the *combined* bulk work in (19c),
with complete primitive rows and the side/core boundary retained.
`SelbergThetaNativeMeanCancellation` evaluates the zero-derivative
source pairing as a positive Cauchy transform, but does not evaluate
this dilation derivative. The analogous row-bundle identity should be
compared with the leakage-plus-drift expression (19b) before asserting
any sign. Equation (19c) is paper algebra; its infinite-row/global
domain specialization remains open in Lean.

### Finite-row vertical connection law [paper-proved algebra]

The weight-induced drift in (19b) has an explicit primitive-row
coordinate. At `z=x+i*y`, `y>0`, a row with lower matrix entries
`(c,d)` has `h_v=y/|c*z+d|²` and `x_v=log(h_v)/2`. Put

```text
delta_v(z) = y*partial_y log(h_v)
           = 1-2*c²*y²/|c*z+d|²,       -1<=delta_v<=1.  (19d)
```

For a finite row set, let `b_v=sqrt(h_v/2)*Phi(x_v)>0`,
`U_f,v=sqrt(h_v/2)*f(x_v)`, `r_v=f(x_v)/Phi(x_v)`,
`q_v=Phi'(x_v)/Phi(x_v)`, and
`m=(sum_v b_v²*r_v)/(sum_v b_v²)`. The fluctuation is
`S_v=b_v*(r_v-m)`. The chain rule gives the exact source generator

```text
y*partial_y U_f,v
  = delta_v*sqrt(h_v/2)*(f+f')(x_v)/2.              (19e)
```

Differentiate `S=U_f-m*b` and pair with `S`. The `partial_y m`
term vanishes because `sum_v b_v*conj(S_v)=0`. Expanding
`(f+f')/Phi=r'+(1+q)*r` then leaves

```text
Im sum_v (y*partial_y S_v)*conj(S_v)
  = (1/2)*sum_v delta_v*b_v²*
      Im(r'_v*conj(r_v-m)).                          (19f)
```

Every amplitude and theta log-density contribution is real and
therefore disappears from this imaginary current. For the actual
source response `f=p_alpha`, (19f) identifies the weight-induced part
of (19b) as a **signed phase covariance of the literal row ratios**.
The identity row has `delta=1`; all nonidentity rows have
`delta-1=-2*c²*y²/|c*z+d|²<=0`. This does not sign (19f), because
its phase covariance can change sign. Passing (19f) to all rows and
computing the moving-projection leakage in the same coordinates is
the next source-level problem. No RH conclusion or Lean closure is
claimed from this finite-row identity alone.

The other summand of (19b) also has an exact finite-row covariance
normal form. Write `B=sum_v b_v²`, `w_v=b_v²/B`, and let
`xi_(j,v)=partial_j x_v` for `j=x,y`. Set

```text
ell_v = (L b_v)/b_v = (5-Phi''(x_v)/Phi(x_v))/4,
theta_(j,v) = partial_j log(b_v) = (1+q_v)*xi_(j,v),
C_0 = sum_v w_v*ell_v*conj(r_v-m),
C_j = sum_v w_v*theta_(j,v)*conj(r_v-m),
A_j = sum_v w_v*xi_(j,v)*r'_v.                       (19g)
```

The row formula for `ell_v` uses the unchanged native differential
expression `L=1-y²*Delta` and hyperbolic invariance of each primitive
row height. Differentiating the weighted mean gives
`partial_j m=A_j+2*conj(C_j)`. Product differentiation of `L(m*b)`
and orthogonality of `S` to `b` then give

```text
Im sum_v (Q L(Pi U_f))_v*conj(S_v)
  = B*Im[m*C_0-2*y²*(A_x*C_x+A_y*C_y)].           (19h)
```

The apparent quadratic score term is `2*conj(C_j)*C_j`, which is real
and cancels from the imaginary current. Thus (19f) and (19h) express
the **entire finite-row obstruction** in theta curvature, score,
ratio-derivative and modular-height covariances. The geometric
coefficients have the sharp hyperbolic identity

```text
y²*(xi_(x,v)²+xi_(y,v)²)=1/4.                      (19i)
```

For the actual `f=p_alpha`, the missing theorem is a sign or
vanishing law for the sum of (19h) and `(5/2)` times (19f), with
all primitive rows and the weighted spatial integral retained.
Neither covariance is signed separately. These are finite-row paper
identities; all-row differentiation, weighted admission and Lean
formalization remain open.

There is a sharper **edge-current** form of this obstruction. For any
finite row set, the fluctuation mass and every real-coefficient
covariance are complete-graph pair sums:

```text
sum_v |S_v|² = (B/2)*sum_(v,w) w_v*w_w*|r_v-r_w|²,
sum_v w_v*a_v*conj(r_v-m)
  = (1/2)*sum_(v,w) w_v*w_w*(a_v-a_w)*conj(r_v-r_w)   (a_v real). (19j)
```

The second identity also holds for complex `a_v`; reality is needed
only when identifying the theta/geometric coefficients below. Define
`Delta_vw r=r_v-r_w`, and likewise for `ell` and `theta_j`. In the
orientation of (19b), the **combined** leakage-plus-drift imaginary
pairing becomes

```text
J_F = Im sum_v [Q L(Pi U_f)+(5/2)*Q(y*partial_y S)]_v*conj(S_v)
    = (B/2)*Im sum_(v,w) w_v*w_w *
        [m*Delta_vw ell
         -2*y²*sum_(j=x,y) A_j*Delta_vw theta_j
         +(5/4)*(delta_v*r'_v-delta_w*r'_w)]
        *conj(Delta_vw r).                            (19k)
```

This is a finite-row algebraic theorem, obtained by applying (19j)
to (19f) and (19h). It changes the source question from the sign of an
unnamed PDE leakage to the orientation of an explicit **primitive-row
edge current**. The numerator is sensitive to relative phases of
`p_alpha/Phi` at distinct modular heights; pointwise positivity of
`Phi`, strict source log-concavity and the source disk (8a) do not by
themselves orient those phases. A proof producer would have to derive
an all-row cancellation or sign from the literal theta arithmetic in
the bracket of (19k), then justify its weighted spatial integral. The
edge formula alone is a receiver and makes no spectral-reality claim.

The edge set has a canonical **arithmetic grading**. Write each row as
its primitive integer pair `v=(c,d)`, with the sign convention of
`ModularStripUnfolding.gammaSetHalf`, and put
`k(v,w)=|c*d'-d*c'|`. If `k(v,w)=0`, two primitive integer rows are
equal up to sign, hence represent the same row and have
`Delta_vw r=0`. Every nonzero term in (19j)--(19k) therefore has
`k(v,w)>=1`. Common right action by `SL₂(ℤ)` preserves `k`, so the
finite-row edge current decomposes exactly into positive determinant
grades. The unoriented grade-one edges are primitive bases modulo row
sign and form a single orbit under the common modular action; higher
grades carry extra residue data.
This is the rank-two arithmetic content absent from diagonal unfolding.
It suggests a concrete producer test: unfold the complete grade-one
current, then determine whether the remaining grades satisfy a
source-derived cancellation law. Swapping the endpoints of an edge
does **not** cancel its contribution: both the bracket and
`Delta_vw r` change sign. No grade has yet been evaluated or signed.

### Automorphic occurrence metric and directional-variance potential [paper proof]

The polynomial weight in (15c') selects Xi zeros but is not modular
invariant. The corpus already constructs the positive, modular-invariant
height sum `E_s(z)=positiveCuspRows s z=sum_v h_v(z)^s` for `s>1`.
On the standard cusp, the identity row contributes `y^s` and the
nonidentity rows satisfy the same shifted-lattice estimate used in
(15c), now with exponent `s`:

```text
E_s(x+i*y)=y^s+O_s(y^(1-s)) uniformly for |x|<=1/2, y>=1. (19l)
```

Thus `E_(5/2)` is pointwise comparable to `y^(5/2)` there, and the
fixed occurrence criterion has an **automorphic** form:

```text
XiC(alpha)=0  <->
  integral_(F,y>1) E_(5/2)(z)*sum_v |S^*_(p_alpha)(z,v)|² dmu(z)<infinity
```

for `0<Im(alpha)<1/2`, `Re(alpha)!=0`. The equivalence is a paper
consequence of (15c') and (19l); the Lean statement is not yet built.

This weight has a stronger exact Green geometry. Put
`D_v=y*grad(log h_v)`, `pi_v=h_v^s/E_s`, and `d_s=sum_v pi_v*D_v`.
Every `D_v` has Euclidean norm one, `sum_v pi_v=1`, and termwise
differentiation is locally absolute because these first derivatives
are bounded by `s*h_v^s/y`. Write `L_0=-y²*Delta` and retain
`L=1+L_0` for the native expression. Since each height power satisfies
`L_0(h_v^s)=-s*(s-1)*h_v^s`, the weighted symmetric expression and
its square-root conjugate obey

```text
L_E = L-y²*grad(log E_s) dot grad = L-s*y*d_s dot grad,
sqrt(E_s)*L_E*(1/sqrt(E_s)) = L+V_s,
V_s = s*(s-2)/4+(s²/8)*sum_(v,w) pi_v*pi_w*|D_v-D_w|². (19m)
```

The last equality follows from
`1-|d_s|²=(1/2)*sum_(v,w)pi_v*pi_w*|D_v-D_w|²`.
For `s=5/2`, `V_s>=5/16`, strictly at every point because the
identity and `(1,0)` rows have different height directions. In the
cusp, `d_s` tends to the identity-row direction and `V_s` tends to
`5/16`, recovering (19a). Unlike the raw power weight, this
source-compatible metric preserves modular orbit unfolding while
adding a nonnegative **directional variance potential**. It does not
erase the forced source term.

For a finite source-row packet, its drift has an exact phase form
parallel to (19f):

```text
Im sum_v (y²*grad(log E_s) dot grad S_v)*conj(S_v)
  = (s/2)*sum_v b_v²*(d_s dot D_v)*
      Im(r'_v*conj(r_v-m)).                          (19n)
```

The derivatives of `m` drop out by row orthogonality, and the
derivatives of the positive amplitudes contribute only real terms.
Equation (19n) replaces the single identity-row factor `delta_v` in
(19f) by a positive Eisenstein average of *all* row-direction
correlations. The mathematical target is now the signed combination
of (19h) and (19n) in the automorphic `E_(5/2)` space. Whether its
determinant grades cancel or have a useful sign for the actual theta
response remains open; no spectral-reality theorem is inferred.

The choice `E_(5/2)` also has a **source-side interpretation already
proved in Lean**. `SelbergThetaEisensteinProbes.source_eisenstein_pairing`
evaluates the original scalar response against every `E_s`:

```text
integral_F source(alpha,z)*E_s(z) dmu(z)
  = probeMass(s)/(alpha²+(2*s-1)²),  probeMass(s)>0. (19o)
```

At the selecting exponent `s=5/2`, the denominator is `alpha²+16`.
For nonreal `alpha²`, the imaginary part of this literal source
pairing is `-probeMass(5/2)*Im(alpha²)/|alpha²+16|²`, a known
nonzero signed source work. The same `E_s` is thus both the
Xi-occurrence metric and an exactly evaluated arithmetic adjoint
probe. This does **not** evaluate the nonlinear projected edge current
in (19h)--(19n); an identification of that current with (19o), or a
rigorous inequality between them, is the new source-specific test.

There is a stronger ground-state choice. Let `rho=5/4`,
`H=E_rho`, and use the **squared Eisenstein weight** `w=H²`.
Equation (19l) at `rho` gives `w=y^(5/2)*(1+O(y^(-3/2)))`
uniformly on the cusp, so it selects precisely the same Xi-zero
responses as (15c'). It is positive and modular invariant. Unlike
`E_(5/2)`, its square root is itself a Maass eigenfunction:
`L H=(1-rho*(rho-1))*H`. The product rule gives the exact global
ground-state transform

```text
L_w = L-2*y²*grad(log H) dot grad,
H*L_w*(1/H) = L+rho*(rho-1)=L+5/16.             (19p)
```

Thus the Xi-selecting Hilbert geometry has a modular-invariant
completion whose symmetric **differential expression** conjugates to
the unchanged native Maass expression plus a constant, with no
variable potential. The corresponding closed-operator equivalence
still requires a domain proof. The previous positive variance potential (19m)
belongs to the alternative unsquared `E_(5/2)` weight; (19p) is the
preferred carrier for the spectral step. The corpus's
`source_eisenstein_pairing` also evaluates the source against this
same `H`, now as `probeMass(5/4)/(alpha²+9/4)`.

Equivalently, set `g_alpha=H*S^*_(p_alpha)`. Multiplication by `H`
is a unitary map from `L²(H²*dmu;row bundle)` to the original native
row-bundle `L²(dmu)`. Consequently, in the physical strip,

```text
XiC(alpha)=0 <-> g_alpha belongs to native row-bundle L²;  (19r)
```

at an Xi zero `g_alpha` is nonzero by (15). On the smooth core, the
original row equation becomes

```text
Q (L+5/16-lambda_alpha)*g_alpha
  = -H*Q L(Pi U_(p_alpha))
    -2*y²*Q(grad(H) dot grad(S^*_(p_alpha))).     (19s)
```

This is a source-faithful **native Hilbert-space occurrence**, not an
eigenvalue assertion: the right side is the full, explicit residual
in the fluctuation channel that an RH proof must control. The
source-line component of `(L+5/16-lambda_alpha)*g_alpha` is not
asserted to vanish. Its closed-domain interpretation is still open.
Because `H` depends on modular row geometry rather than the theta
coefficients, any RH-producing step must act on this residual through
the literal theta response; the ground-state transform is a carrier
theorem, not the missing source law.

With `pi_u=h_u^rho/H` and `d_rho=sum_u pi_u D_u`, the drift in
(19p) is a complete-row average. For a finite source-row packet,

```text
Im sum_v (2*y²*grad(log H) dot grad S_v)*conj(S_v)
  = rho*sum_v b_v²*(d_rho dot D_v)*
      Im(r'_v*conj(r_v-m)).                          (19q)
```

This has the same cusp limit as `(5/2)` times (19f), since
`d_rho` tends to the identity-row direction. The remaining
paper-level source problem is the signed combination of (19h)
and (19q), now in a globally automorphic space. The closed-domain
intertwining, all-row differentiation and source cancellation are
not yet proved; (19p) alone does not make a forced response an
eigenvector.

## Conjecture loop and whole-chain consequence

**Conjecture 1:** The common source mode makes the two carriers isometric.
**Fail:** (1)–(2) exhibit a strictly positive, complete-row loss. An
unweighted norm match would additionally erase the forced `exp(-x)` tilt.

**Conjecture 2:** The positive dispersion itself is the oriented Hedenmalm
Green boundary current. **Fail:** the latter is signed and equals
`2*Im(mu)` times positive source-metric energy on an eigenmode; (1) is
nonnegative. Reflection reverses the current, while both dispersions stay
nonnegative. A direct equality cannot be the reality mechanism.

**Conjecture 3:** A complete-row reference can simultaneously preserve the
untilted Hedenmalm norm and put the fixed theta forcing in one scalar port.
**Proved:** (7) does both, and its row weight is unique under those two
requirements. The paired-mode current and its derivative are transferred
exactly by (8); the strict source disk becomes the complete modular
kinetic/dispersion ellipse (8b), with the source-specific dominance (8c).

**Conjecture 4:** Self-adjointness of the transported source derivative
then forces `alpha` real. **Fail:** (9) is an inhomogeneous equation; a
self-adjoint operator has forced resolvent responses at nonreal
parameters. The scalar source work remains nonzero exactly when its
Green current does. Thus the new lift closes the metric and port problem
but does not manufacture native spectral occurrence.

**Conjecture 5:** Discarding only the scalar row component makes an
unforced zero response with retained mass. **Proved, with a precise
operator boundary:** (13)--(15) give that response; (16) identifies the
one-dimensional multivalued fibre that prevents a self-adjointness
conclusion. Free-resolvent responses at generic nonreal parameters also
enter this relation, so its unweighted spectrum is not Xi-selective.

**Conjecture 6:** The complete primitive-row variance can detect the
two-ended no-radiation condition even after scalar projection.
**Proved on paper:** (15c)--(15e) give the exact all-cusp-weight criterion.
Two rows with heights separated at the cusp retain every nonzero
exponential radiation tail. This supplies Xi-faithful occurrence as
regularity in a positive modular channel, while (18)--(19) locate the
remaining Maass coupling.

**Conjecture 7:** Xi-selective regularity needs an intersection of all
cusp-weighted spaces. **False, with a positive replacement:** (15c')
shows that the single `y^(5/2)` Hilbert norm selects Xi zeros across
the physical strip. This makes a closed-domain attack concrete.

**Conjecture 8:** Passing to that fixed positive Hilbert metric makes
the native Maass equation symmetric without further source work.
**False on the compact core:** the symmetric weighted expression differs
by the dilation drift in (19a). The surviving source identity (19b)
couples this drift to the moving-projection leakage. Its signed pairing
is the new, single-space mathematical target; no vanishing is known.

**Conjecture 9:** Forced complex-parameter Rellich reduces that pairing
to a cusp/core boundary once the Xi radiation vanishes. **False:** the
exact stress divergence (19c) retains both theta-source dilation work
and imaginary phase current in the interior. The positive replacement
is the finite-row connection law (19d)--(19f): the weighted drift's
imaginary part is exactly a signed phase covariance, with no amplitude
or theta score terms. This makes the remaining arithmetic cancellation
an explicit row-ratio problem rather than an unspecified boundary term.

**Conjecture 10:** The Xi-selecting cusp weight can be made automorphic
without changing its admitted responses. **Proved on paper:**
`E_(5/2)` has the same cusp growth as `y^(5/2)` and produces the
positive directional-variance potential (19m). **Stronger pivot:**
the squared weight `E_(5/4)^2` has the same selecting growth, while
its differential-expression ground-state transform is exactly
`L+5/16` globally, by (19p).
Its drift is the all-row correlation (19q). The graph identity
(19k) and determinant grading expose a rank-two arithmetic object;
none of these statements signs its source current.

**Surviving attack:** Use the automorphic `E_(5/4)^2` space. Extend
(19h) and (19q) to complete rows and the closed weighted domain;
then unfold the determinant-one edge sector and compare its theta
arithmetic with the exact `E_(5/4)` source probe (19o). The decisive
new theorem must orient the full determinant-graded source current
at no-radiation states. If that current is real, positive fluctuation
mass forces `Im(alpha²)=0` and RH. The nonparabolic scattering kernel
(12) may guide its evaluation, but neither it nor the scalar
Eisenstein probe already pays the projected phase current.

## Corpus anchors

- `HedenmalmCompletedDividedEnergy.lean`: exact equality of the causal modes.
- `HedenmalmThetaCompactDivisorEigenmode.lean` and
  `HedenmalmThetaSourceCompressedInverseDeterminant.lean`: source eigenvector
  and exact Xi spectrum.
- `SelbergThetaNativeSource.lean`: complete primitive-row periodizations,
  bounded source ratio, strip unfolding and source envelopes.
- `SelbergThetaNativeEnergy.lean`: native weighted energy and mean-zero
  variance, distinct from the row dispersion (1).
- `SelbergThetaCommonForcingGraph.lean`: the same source has an inhomogeneous
  native Maass equation.
- `SelbergThetaCommonForcingPairing.lean`: absolute primitive-row unfolding of
  native source work to a strictly positive horizontal weight.
- `SelbergThetaHorizontalTransform.lean` and
  `SelbergThetaHorizontalArithmetic.lean`: exact nonparabolic kernel,
  completed-zeta scattering transform and totient/Mobius quadrature laws.
- `SelbergThetaNativeScalarBoundary.lean`,
  `SelbergThetaNativeMeanCancellation.lean`, and
  `SelbergThetaCommonForcingPacketMass.lean`: closed boundary Cauchy
  continuation, mean cancellation and positive finite-packet mass.
- `HedenmalmThetaFredholmEigenmodeGreenIsotropy.lean`: oriented rank-two
  boundary current on the exact-spectrum eigenmode.
- `HedenmalmThetaCompactFluxEnergy.lean` and
  `HedenmalmCompletedDividedEnergy.lean`: normalizations used in (4).
- `HedenmalmThetaAllShiftedTails.lean` and
  `ThetaCuspFirstAtomAllOrderApproximation.lean`: all exponential source
  moments and the first-atom ratio needed for (15b)--(15e).
- `ModularStripUnfolding.lean`: the identity and `(1,d)` primitive rows.
- `ThetaCuspHawkingBMPositiveHeightOperator.lean`: compact-height
  Laplacian-row summability for the proposed closed-domain audit of (18).

Broad hybrid, lexical and mechanism-directed deep corpus searches inspected
candidate lemmas, source arguments and proposed ingredient sets. One deep
result completed but proposed unrelated derivative and D4BM lemmas; another
was partial. A separate Hedenmalm search exposed the existing hyperbolic
mean--dipole boundary form, not a source-work cancellation. Broader
periodization and half-line searches then found the already-formalized
horizontal mean, arithmetic scattering continuation, positive boundary
Cauchy density, and finite-packet mass; (10)--(12) must be read against
those results. The exact source-square lift, paired kinetic ellipse,
fluctuation-kernel classification and all-weight criterion (15c) were
not located as corpus declarations; this is a corpus noncollision
observation, not a literature novelty certificate. No numerical
computation or Lean build was used.
