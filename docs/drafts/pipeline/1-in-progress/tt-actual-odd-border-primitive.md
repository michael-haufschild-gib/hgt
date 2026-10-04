# TT: canonical complete-source off-diagonal primitive

- **ID:** tt-actual-odd-border-primitive
- **Stage:** 1-in-progress
- **Route:** TT, all-rank complete signed theta current
- **Conjecture:** C48, actual odd-four source construction and residual sign

## Current corpus and hard target

`ThetaCuspActualOddHeadVariance` already defines the actual corrected odd
head A(a,r) and cross-column b(a,r). Its local Schur-plus-variance identity
is prior knowledge. The canonical head compensation is positive for r>0;
its full integral is the actual odd-three moment head H(a), positive
definite for 0<a<1/2 by the established six/seven-rank results. The bottom
entry d(a,r) is the actual weighted negative fourteenth reflection jet.

The previous Gaussian scale identity retains every ordered source pair,
but a positive unweighted operator does not sign the physical-weight
pairing. Any locally bounded potential correction still vanishes to
second order with r*sinh(a*r), so it cannot remove the constant negative
Green remainder at the center. This elementary extension will not be
banked as another Lean no-go.

## Concrete construction to test

Let beta=integral b, H=integral A, and m=H^(-1)*beta. Define componentwise

    F_i(r)=integral_0^r [(A(s)*m)_i-b_i(s)] ds.

The actual source is smooth and integrable. Therefore F'=A*m-b,
F(0)=0, and F(infinity)=H*m-beta=0. Correct both symmetric border
positions by F'. This leaves all integrated entries unchanged and makes
the corrected border exactly A*m. For every fixed v the corrected
quadratic form is then

    d-m^T*A*m+(v-m)^T*A*(v-m).

This construction can remove the moving-minimizer variance; it is not
confined to the radius-polynomial class falsified in C45. It is also not
itself an RH proof. A generic conditional Schur receiver would add nothing
and is not the desired output.

## Hard sign test

**C48-S.** For the actual source-selected m and the canonical corrected
odd head, prove d(a,r)-m(a)^T*A(a,r)*m(a)>=0 for every positive r and
0<a<1/2, or find a rigorous source-specific obstruction. Gaussian degree
separation suggests positivity on a far ray; the finite-center sign is
not supplied by that observation. No pointwise sign or rank-eight
positivity is assumed in a proof.

The paper construction above only becomes useful if this residual sign
can be attacked. Test it before spending a turn formalizing generic FTC
plumbing. If the chosen fixed m fails, retain the exact boundary law and
learn which additional diagonal/shape correction is mathematically needed.

## C49: obstruction to the all-rank off-diagonal-only extension

The complete source's signed native center jets take both signs above
every order. Negative jets persist on positive-center intervals. This
has now passed direct Lean checking in `ThetaCuspNativeCenterJetOscillation`;
the proof transfers all-order modular cusp flatness to the actual source
square and excludes either eventual sign by its full Taylor series.

Therefore changing only off-diagonal entries, or repairing only finitely
many diagonal orders, cannot produce pointwise positivity at every rank.
This does not determine J_7(0), does not decide C48-S at rank eight, and
does not disprove the integrated cone. The exact source-selected m above
still needs its residual sign analyzed together with a diagonal flux.
See `../3-formalized/tt-center-jet-sign-oscillation.md` for the proof and audit record.

## C51: differentiated-packet sign attack

The parity-specific mixed derivative term integrates to zero, reducing
the aperture derivative of the packet norm to its signed first spatial
moment. Pointwise reflection pairing is already indefinite for the two
even coefficients 1 and D^2, so that reduction does not supply the needed
nonlocal sign. The literal prime--Gamma--pole operator is retained in the
next attempted proof; its fixed-source diagonal estimate is insufficient.
See `tt-parity-packet-centering.md` for the paper calculations and precise
unproved inequality. C48-S and rank-eight positivity remain open; no new
Lean sign result is claimed from this pass.

## 2026-10-02: test of payment between the compact region and tail

Tested whether C50's positive tail, combined with the moving-minimizer
variance, supplies the missing payment without a compact source inequality.
Use the **native** odd-four block for this test, so no unproved tail
estimate for a corrected block is needed. Fix 0<a<1/2. Write its integral
over (0,R) as [H_c,b_c;b_c^T,d_c], and its remaining integral as
[H_t,b_t;b_t^T,d_t]. For sufficiently large R, the tail block is positive
definite by C50 with N=4,s=1. Also H_c is positive definite: it converges
to the already proved positive odd-three integrated head. All entries
are integrable by `ThetaCuspCenterMixedAllOrderIntegration`.

Put m_i=H_i^(-1)b_i, S_i=d_i-b_i^T*m_i, H=H_c+H_t,
m=H^(-1)(b_c+b_t), and let S denote the complete successor Schur
complement. The exact completion of squares gives

    S = S_c + S_t + V_R,
    V_R = (m-m_c)^T H_c (m-m_c)
        + (m-m_t)^T H_t (m-m_t) >= 0.

This is a matrix-weighted identity; a scalar pairwise-variance formula
cannot be substituted without checking the noncommuting matrices.
Evaluating the complete variational problem at m_c gives

    0 <= S_t + V_R
       <= d_t - 2*m_c^T*b_t + m_c^T*H_t*m_c -> 0.

The limit follows because all tail entries tend to zero and m_c converges
to the finite source-selected m. In particular, it does **not** require
the tail minimizer m_t to stay bounded. Thus the proved cofinal tail and
the positive variance do not provide a nonvanishing payment as R grows.
No lower bound for the actual S_c was obtained. At a finite R the exact
positive tail reserve may still suffice; its comparison with S_c is the
unresolved source inequality, not a consequence of eventual positivity.

This paper diagnostic does not advance the proved rank-eight sign, retire
C48, or falsify RH. No generic variance or conditional Schur theorem was
added to Lean. Further work must prove an actual compact payment, keeping
the mixed terms, rather than infer it from the existence of a positive tail.

## C53: two fixed diagonal fluxes, with the actual neutral test retained

The next concrete signed candidate keeps the canonical odd-three source
correction and adds a separate bottom-diagonal correction. This is a
candidate for rank eight, not an all-rank induction or a proved inequality.
Write J_k(x)=(-1)^k*nativeJet(2k,x), G(x) for the actual center
compensation source, and C_3 for the existing canonical odd-three
coefficient. Set

    A_3(x) = [[J_1,J_2,J_3],
              [J_2,J_3,J_4],
              [J_3,J_4,J_5+C_3*G]],
    b(x) = [J_4,J_5,J_6],
    S_3(x) = J_7(x) - b(x)^T*A_3(x)^(-1)*b(x).

The already proved strict head minors and
`thetaCuspNativeOddCanonicalCompensatedDet_pos_global` make A_3 positive
definite on the nonnegative ray. No sign of S_3 is supplied by this fact.

**C53 (open).** There is a fixed C_4>0, chosen from the actual source,
such that S_3(x)+C_4*G(x)>0 for every x>=0.

Why this specific signed statement matters: the exact aperture flux
obeys F_a'(r)>=w_a(r)*G(r/2). Adding C_3*F_a' and C_4*F_a' to the two
diagonal entries therefore exceeds the matrix in C53 by a positive
semidefinite diagonal matrix, since both coefficients are positive.
Both added derivatives have zero integral. C53 would consequently prove
the actual integrated odd-four block positive, and with the already
proved even-four block would close rank eight. No such implication is
being banked as a new conditional Lean theorem.

The first source-specific test is at the unique tau with G(tau)=0.
`ThetaCuspCompensationNeutralAnchor` proves 5<q(tau)<45/8. At that center
the matrix in C53 is exactly the native odd-four matrix, independent of
both correction coefficients. Its sign there was **not** established in
this pass. The existing order-fourteen Gaussian limit does not classify
this finite center, and the reciprocal-Xi moment theorem in
`XiCenteredOrderFourteenSourcePositivity` concerns a different moment.

Keep the aperture distinction exact. The literal F_a' is strictly
positive at r=2*tau for every a>0, by
`ThetaCuspCenterCompensationTransitionSlack`. After division by w_a,
its extra term is

    Phi(tau)^2 * [2*a*tau*coth(2*a*tau)-1],

which tends to zero as a tends to zero. Thus G(tau)=0 does not give a
zero of the physical correction at any fixed positive aperture. A
negative native direction there would obstruct fixed-coefficient
positivity for all sufficiently small apertures, but no such negative
direction has been proved. Aperture-dependent unbounded coefficients
would require a separate analysis.

Beyond the neutral test, a proof of C53 must separate the actual lower
coefficient requirements -S_3/G where G>0 from the actual upper
requirements S_3/(-G) where G<0, retaining strictness at tau. The modular
source ODE provides all jets but this comparison is unresolved. Its
polynomial sl2 brackets alone do not supply a positive pairing; existing
scalar-contravariant no-go theorems exclude that proposed shortcut.
No numerical or symbolic probe, Lean edit, or new sign theorem resulted
in the initial C53 pass.

## C53 first-contact test

For the actual positive head write u=A_3^(-1)*b and S=S_3. Differentiating
A_3*u=b and using symmetry cancels derivatives of u:

    S' = J_7' - 2*u^T*b' + u^T*A_3'*u.

At a zero of F_C=S+C*G with G nonzero, its derivative is

    F_C' = (G*S'-S*G')/G.

The denominator sign must be retained. Strict upward crossing would
require G*(G*S'-S*G')>0. This sign has not been proved. At G=0 the
separate requirement is S(tau)>0.

Eliminating C from this formula must not eliminate its admissibility
restriction. A coefficient-free upward-crossing theorem for every
positive C is false: fix a point in the negative-G chamber and take C
large. Then F_C is positive at zero and negative at the chosen point,
so a first downward contact exists. The corpus already supplies the
continuous first-zero theorem. This is a check on the proposed argument,
not a new Lean obstruction or a falsification of C53.

## First-atom odd-four certificate on the neutral scale window

**Status:** paper derivation below; one polynomial row inequality checked
in a temporary Lean file. The full source identification and complete
certificate have not been formalized. This is not a sign theorem for
the complete source or a proof of C53.

The finite first-atom central-factorial moments in
`ThetaCuspFirstAtomCentralFactorial` motivated a direct odd generating
kernel. Set B=(2q-3)^2 and

    g_q(t)=exp(-2q*(cosh(2t)-1)).

The exact first-atom reflection function, after its positive scalar
factor 4q^2*exp(x-2q) is removed, is

    (B+6q*partial_q) g_q(t),

where partial_q holds B fixed. No positive representing measure is
assumed. Let L be the finite moment functional defined by these signed
jets through order fourteen. The formal identity

    L(sin(X*s)*sin(X*t)) = (f(s-t)-f(s+t))/2

is read only to degree seven in each variable. Substitute s=asinh(z),
t=asinh(w). For the bare g_q the right side is

    exp(-4q*(z^2+w^2+2z^2*w^2)) *
      sinh(8q*z*w*sqrt(1+z^2)*sqrt(1+w^2)).

Removing the separate factors with nonzero constant term is an
invertible triangular change of the four odd polynomial coordinates.
Put delta=1/(8q), U=8q*z^2, V=8q*w^2. After also removing 8q*z*w and
the two square-root factors, the kernel is

    H(U,V)=exp(-delta*U*V) *
      sum_n ((U+delta*U^2)*(V+delta*V^2))^n/(2n+1)!.

Its coefficient matrix through degree three has H_00=1, H_0j=0 for
j>0, and lower block

    [ 1/6-delta,                  delta/6,                     0;
      delta/6, 1/120-delta/6+2delta^2/3,       delta/60-delta^2/6;
      0,             delta/60-delta^2/6,
                         1/5040-delta/120+7delta^2/60-delta^3/3 ].

The negative terms from exp(-delta*U*V) have been retained. Applying
B+6q*partial_q at fixed z,w gives the exact coefficient rule

    A_ij=(B+6+6(i+j))*H_ij-6delta*partial_delta(H_ij)
           -3*(H_(i-1),j+H_i,(j-1)),

where negative indices mean zero. In particular the derivative must
include the removed q-dependent exponential and the factor 8q.

Set v=1/(2q), h=6/B. Congruence by diag(1,2,10,60), followed by
division by B, gives the symmetric matrix M with entries

    M00 = 1+h; M01=-h; M02=M03=0;
    M11 = 2/3-v+2h*(1-v);
    M12 = 5v/6+h*(5v-5/3);
    M13 = -5v*h/2;
    M22 = (5/6)*(1+5h)*(1-5v)+(25/6)*v^2*(1+3h);
    M23 = 5v/2-25v^2/4+h*(-5/2+25v-75v^2/2);
    M33 = (5/7)*(1+7h)-(15/2)*v*(1+8h)
            +(15/4)*v^2*(7+45h)-(75/4)*v^3*(1+4h).

For q>=5, 0<v<=1/10, 0<h<=6/49 and
h*(1-3v)^2=6v^2. Write r=1-10v, so 0<=r<=1. Then

    4*(1-3v)^2*M23
      = (v/40)*(111+43r+201r^2+45r^3),

so M23>=0. Its h coefficient is nonpositive, and
3/16-(5v/2-25v^2/4)=(1-10v)*(3-10v)/16; hence M23<=3/16.
Also |M12|<=10/49 and |M13|<=3/98. The first three strict row
diagonal-dominance reserves are respectively at least

    1, 22/105, 59/2352.

For the last row put R=M33-5v*h/2-M23. The exact identity is

    112000*(1-3v)^2*R
      = 6083+45941r-13814r^2+26166r^3+14931r^4+693r^5.

The right side is positive since r^2<=r. Thus R>0. Symmetry and
2|ab|<=a^2+b^2 prove M positive definite. Invertibility of the
triangular odd-coordinate change gives the proposed paper conclusion:
the actual first-atom odd-four block is positive definite for q>=5.
The complete literal first-atom conclusion is now formalized in
`RHTower.ThetaCuspOddCentral.firstAtomOddFour_posDef`, in
`ThetaCuspFirstAtomOddFourPositivity.lean`. Its proof checks every row,
the invertible triangular coordinate map, and the exact source jets
through order fourteen. The source identification uses the affine
jet recurrence directly, so it does not depend on an unformalized
generating-kernel argument. Named `--old` build and final direct Lean
audit passed; the compiled theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. See
[formalized certificate](../3-formalized/tt-first-atom-odd-four-positivity.md).
The complete-source C53 sign remains open.

**Remaining hard sign:** the complete source has every ordered pair
(n,m), including n!=m. Their contributions are not positive moment
measures and cannot be discarded. The corpus's fixed-product radial
recurrence supplies all their jets. The previously proved even-four
two-atom error theorem stops at order twelve, and the complete central
error absorption read here requires q>=8. Neither covers the odd-four
neutral test at 5<q(tau)<45/8. No bound absorbing all those terms into
the displayed odd reserves, and no negative full-source direction, has
been established. The next test must retain the signed unequal-pair
core and the full remainder; changing the first-atom constants is not
the research objective.

One exact test direction exposed by these coordinates is the monic odd
polynomial

    P_q(X) = X^7+(56-168q)*X^5+(784-3360q+6720q^2)*X^3
               +(2304-10752q+26880q^2-53760q^3)*X.

Indeed it is -5040 times the z^6 coefficient of
exp(4q*z^2)*sin(X*asinh(z))/(z*sqrt(1+z^2)). This follows by
differentiating cos(X*asinh(z)) and using its central-factorial
coefficients. It is the fourth coordinate above up to a nonzero scale.
At tau, a negative complete-source value of L_tau(P_q^2) would
falsify C53; a positive value alone would not prove the full block
positive. Neither sign has been established. The complete source's
fourteenth jet and every ordered-pair term must remain in this test.

## Complete ordered-pair test for the seventh-degree direction

Let A=56-168q, B=784-3360q+6720q^2 and
C=2304-10752q+26880q^2-53760q^3, so P_q=X^7+A*X^5+B*X^3+C*X.
Write R_k(a,s) for evaluation at s of the corpus polynomial
`thetaPairRadialEvenPolynomial a k`. The exact scalar to sign for one
ordered pair is

    E(a,s;q) = R_7 + 2A*R_6 + (A^2+2B)*R_5
                 + 2(C+A*B)*R_4 + (B^2+2A*C)*R_3
                 + 2B*C*R_2 + C^2*R_1.

For p=n^2*q, r=m^2*q, that pair contributes

    4*p*r*exp(x-p-r)*E(p*r,p+r;q).

This follows directly from
`thetaCuspAtomPairEvenJet_eq_radial`, including cancellation of the
two factors (-1)^k. In particular, the retained two-atom contribution,
after the common positive factor 4q^2*exp(x-2q) is removed, is

    E(q^2,2q;q) + 8*exp(-3q)*E(4q^2,5q;q)
                   + 16*exp(-6q)*E(16q^2,8q;q).

Both unequal pairs are in the coefficient 8. This expression has not
been signed on the neutral window. The infinite omitted source is also
still required. The all-order two-atom source formula is already in the
corpus; the absence of a fourteenth-jet identity is not the obstruction.

A direct attempt to regard the added pair matrices as positive fails
already in their first odd diagonal. If s=p+r, d=p-r and
b=(2p-3)*(2r-3), the recurrence gives

    R_1(p*r,s) = -4*(b*(d^2-s)+6*(2d^2-s)).

For the literal (1,2) pair, p=q, r=4q and q>=5: b>0,
d^2-s=q*(9q-5)>0, and 2d^2-s=q*(18q-5)>0. Its first signed
moment is therefore strictly negative throughout the neutral window.
This elementary paper check is not a new formal no-go, and does not
falsify C53. The complete first odd diagonal is already positive in the
corpus. It shows why the complete signed pair sum must be controlled
together, rather than adjoining positive pair blocks to the first atom.

## Retrieval status

2026-10-02: complete-pair Green search and actual-border primitive search
both returned partial results (decomposed-query / reranking deadlines;
the second also reported a semantic retrieval deadline). Coverage and
refresh metadata were inspected; the background indexer was active and
semantic coverage unmeasured. Source reads checked the actual odd-head
definitions and stronger existing integrated positivity before this
conjecture was recorded. No external literature was used as the frontier.

## Next complete-source sign conjecture

With the first-atom certificate now fully checked, the next C53 subproblem
is: the literal native odd-four matrix

    ((-1)^(i+j+1) * thetaCuspNativeReflectionJet (2*(i+j+1)) x)_(i,j<4)

is positive definite throughout 5<=q<=45/8. This would in particular
settle the uncorrectable neutral-center sign; it would not by itself
prove separation of C53's global coefficient windows or the all-rank
compact correction.

The proposed proof must first sign the exact two-atom matrix through
order fourteen, retaining both unequal pairs, then absorb the complete
n>=3 remainder in the same coordinates. The existing retained odd
profiles/reserves stop at the three-by-three block (jets through ten).
The existing two-atom reflected error theorem stops at twelve. Their
positive signs cannot be applied to the new fourteenth-order entry.
The all-order polynomial/radial identities do supply that entry exactly.
No new positive sign for this two-atom core or the complete matrix has
been proved here.

## 2026-10-02: transverse condensation and native boundary transport

**Status: paper analysis only; no new signed result or Lean theorem.**
The existing eighth-order curvature is a rank-three statement, not the
rank-eight assertion required here. The raw positive-moment determinant
theorems returned by corpus search also concern different matrices.

For a fixed center x put k(t)=Phi(x+t)*Phi(x-t) and
T_n(t)=det(k^(i+j)(t))_(0<=i,j<n). The derivative-Hankel condensation
identity gives

    T_(n+1)*T_(n-1) = T_n*T_n'' - (T_n')^2.

Here primes are transverse t derivatives, not center x derivatives.
Evenness gives T_7'(0)=0. At the neutral center the already positive
native heads imply T_6(0)<0 and T_7(0)<0. Thus the missing odd-four sign
would follow from T_7''(0)>0, equivalently negative second derivative of
log(abs(T_7)) there. More precisely, writing E_j and O_j for the native
even and odd j-by-j blocks, condensation at zero gives

    (log(abs(T_7)))''(0)
      = -det(O_4)*det(E_3)/(det(E_4)*det(O_3)).

Consequently this curvature is minus the native odd successor Schur
coordinate divided by the positive even successor Schur coordinate.
Condensation alone therefore reproduces the missing sign; the proved
lower-order curvature cannot be inserted in its place. No generic Toda
receiver is being added to Lean.

To attack the sign through the actual source rather than determinant
renaming, set V=Phi''/Phi. Positivity and smoothness of the complete Phi
make this a smooth literal source observable. Differentiating the product
directly gives

    partial_x partial_t k_x(t)
      = (V(x+t)-V(x-t))*k_x(t).

For J_k=(-1)^k*partial_t^(2k) k_x(0), k>=1, the resulting triangular
center law is

    J_k' = -2 * sum_(m=0)^(k-1)
      (-1)^m * choose(2k-1,2m+1) * V^(2m+1) * J_(k-m-1).

Every higher potential derivative must be retained. The source-positive
modular ODE supplies their exact jets but does not supply the sign of
this alternating combination. In particular the reflected-fibre
Schrodinger potential in ThetaCuspReflectedSourceOddStationaryCurvature
is a different potential from V; its monotonicity must not be substituted
for a theorem about V'. The existing monotone-potential counterexample
also prevents an argument from generic potential monotonicity alone.

Let L_x(X^(2k))=J_k(x), with odd moments zero. At a hypothetical singular
positive-semidefinite native odd-four block, let P be its monic odd
degree-seven null polynomial, and put Q=P/X. Holding P fixed while
differentiating its energy gives the finite expression

    d_x L_x(P^2) = -2*C_x(P),
    C_x(P) = sum_(m=0)^6 (-1)^m * V^(2m+1)(x)/(2m+1)!
                    * L_x(D_X^(2m+1)(P^2/X)).

This follows coefficientwise from the displayed triangular law, since
P^2/X is polynomial of degree thirteen. Null orthogonality cancels
L_x(P*Q'), so its first coefficient has the exact simplification

    L_x(D_X(P^2/X)) = L_x(Q^2) > 0

when the native even-four block is positive definite. This is positivity
of that coefficient, not a sign of C_x(P) or an assertion that V'>0.
The six remaining alternating terms have not been controlled.

**C54, open source sign attempt.** At every hypothetical native odd-four
singular positive-semidefinite point x>=tau, prove C_x(P)>0 for the
actual source-selected null polynomial. On this ray G<=0, so the proved
positive compensated heads imply positive native even-four and odd-three
heads. C50 supplies a positive native odd-four tail. The conjectured
strict negative derivative at each singular point would exclude a
crossing from nonpositive to positive on the way to that tail, hence
prove native odd-four positivity down to tau. No crossing sign has been
proved, and no conditional crossing theorem is being banked.

Even success here would only settle C53's neutral test and negative-G
native ray. The fixed-coefficient window comparison on both sides of
tau, and the all-rank integrated cone, would still remain. These paper
formulas are a precise record of the next source inequality, not an
audited positive survivor or a claim of RH progress.

## C54: logarithmic null variation and its adverse low-order term

The next source check uses ell=log(Phi), not the reflected-fibre
Schrodinger potential. The corpus already proves ell'''<0 for x>0:
ThetaCuspC5GlobalCurvatureSigns.thetaCuspLogCurvatureJet_pos_of_pos is
exactly this assertion after unfolding the curvature-jet definition.
It follows from the complete source's strict fourth logarithmic sign
and the zero odd jet at the modular center. This is existing knowledge,
not a new result of this attempt.

Differentiate k_x(t) in the center directly:

    partial_x k_x(t) = (ell'(x+t)+ell'(x-t))*k_x(t).

With L_x and J_k as above, the finite coefficient identity is

    J_k' = 2*ell'*J_k + 2*sum_(r=1)^k
        (-1)^r*choose(2k,2r)*ell^(2r+1)*J_(k-r).

Thus for a fixed odd monic polynomial P of degree seven, at a
hypothetical PSD null point L_x(P^2)=0,

    d_x L_x(P^2)
      = 2*sum_(r=1)^7 (-1)^r*ell^(2r+1)/(2r)!
                             *L_x(D_X^(2r)(P^2)).

The scalar mass-growth term vanishes at the null point. Null
orthogonality also gives L_x(P*P'')=0, since P'' is odd of degree five.
Consequently the r=1 summand is

    -2*ell'''*L_x((P')^2) > 0.

The strict inequality uses the native even-four positive head, since
P' is a nonzero even polynomial of degree six. Hence the first known
logarithmic-jet contribution has the OPPOSITE sign to C54's required
negative crossing derivative. This does not disprove C54: the other
six summands can have either sign and cannot be dropped.

Write R_x(P) for the sum of the terms r=2,...,7, with the prefactor 2
retained. The actual burden for this attempted proof is now exactly

    R_x(P) < 2*ell'''(x)*L_x((P')^2) < 0

at every hypothetical native odd-four PSD singular point x>=tau.
For monic P the last summand is -2*ell^(15)(x)*J_0(x). The complete
fifteenth log jet is therefore present with nonzero coefficient; the
lower source curvature signs do not eliminate it.

Also inspected the stronger existing source identities in
ThetaCuspCurvatureDefectSource and ThetaCuspCurvatureProjectiveGlobal:
ell^(5)-4*ell^(3)>0 on x>0, and c''-4*c>0 for c=-ell'' on x>=0,
with a decreasing defect and strict projective curvature. These retain
literal likelihood cumulants, but no estimate of R_x(P) follows from
the inspected statements. An attempted proof using just the first
variation term fails in the required direction. The aggregate higher
log-jet payment remains open; no new conditional receiver, easy
curvature corollary, or generic countermodel is being added to Lean.

These are paper derivations, not a Lean audit of the variation formula.
C54, C53 and the all-rank integrated sign remain unresolved.

## C54: complete variation has only two tail grades

Inspected the actual likelihood-cumulant cooling proof. Its positive
functional uses cumulants two through six, a specific binary spectral
kernel, and bounds on the remaining grades. Its `likelihoodCumulant`
definition is zero outside those six-order entries. This theorem must
not be applied to the fifteenth-order null variation by name alone.
The all-order likelihood moment recurrence supplies derivatives, but
its existence does not supply the required signed quadratic inequality.

There is no need to build a fifteen-order cumulant table merely to
express the current C54 target. Write f=phi_1, h=Phi-f, and, for the
fixed odd polynomial P, write P(X)^2=sum_(k=1)^7 a_k*X^(2k). Define the
paper bilinear expression

    B_x(f,g) = sum_(k=1)^7 a_k*(-1)^k *
        D_t^(2k)[f(x+t)*g(x-t)]_(t=0).

Even differentiation makes B symmetric in f,g. It is separately linear,
and differentiating the center gives

    d_x B_x(f,g) = B_x(f',g)+B_x(f,g').

Thus the COMPLETE source energy and its complete variation are

    E = B(f,f)+2*B(f,h)+B(h,h),
    E' = 2*(B(f',f)+B(f',h)+B(h',f)+B(h',h)).

Only the literal tail h and its derivative occur, at linear and
quadratic degree. The higher cumulant grades in the logarithmic formula
must cancel when that formula is reassembled with its actual source
moment functional. This observation does not discard the fifteenth
source derivative: it remains in the differentiated pair expressions.

The existing exact spectral factorization writes h as f times the
positive higher-likelihood Laplace integral. It therefore identifies
these two grades with literal one-tail and two-tail source terms; it
does not make their signed reflection energies nonnegative. The
all-order native approximation only makes the full correction small
on a cofinal ray and supplies no neutral-center estimate.

At a hypothetical null point on x>=tau, the proved first-atom odd-four
theorem gives B(f,f)>0. The exact null constraint is consequently

    2*B(f,h)+B(h,h) = -B(f,f) < 0.

Neither B(h,h)>=0 nor a Cauchy--Schwarz estimate for the mixed source
form has been established here. C54 still requires the full displayed
E' to be negative under this actual null constraint. The six-order
cooling theorem does not sign it. No extra cumulant machinery, unsigned
receiver or tail-only positivity theorem was banked; the complete mixed
source sign is still the research target. These identities remain paper
analysis, not a new Lean audit or a signed frontier advance.

## C55: test the inherited correction in the full successor block

**Status: complete-source obstruction and sharp positive capacity formalized;
permanent leaf and axiom audits pass.** The global odd-three
theorem permits the canonical coefficient C3 in (10^9,3*10^9). In the
negative-G chamber this correction subtracts from the X^5 diagonal.
Strict positivity of the corrected three-by-three head does not imply
that the same subtraction is admissible after adjoining X^7. Thus the
complete neutral-center sign alone would not settle C53.

Use the exact first-atom central-coordinate polynomial P_q above.
At q=7, its X^5 coefficient is -1120. Put

    x7 = log(7/pi)/2,
    P = P_7/(-1120),
    E7 = L_(x7)(P^2),

where L uses the COMPLETE native source and P has X^5 coefficient 1.
The proposed direct falsification test is

    E7 + C3*G(x7) < 0.                         (C55)

Since G(x7)<0 follows from the established neutral-anchor location,
adding C4*G(x7) times the square of P's nonzero X^7 coefficient would
only decrease this value for C4>0. A proof of C55 would therefore
falsify C53, without assuming a sign of the neutral odd-four block.
The full-source inequality is now proved as detailed below.

The first-atom central identity supplies the exact comparison term

    E7_first/f1(x7)^2 =
      8*7*(43008*7^3/1120)^2 * M33(1/14,6/121).

This is a diagnostic term, not a substitute for E7. Retain the
literal (1,2), (2,1), and (2,2) pair contributions, then bound the
entire n>=3 remainder in this same polynomial direction. For the
compensation term, the positive likelihood Laplace representation
suggests using the exact logarithmic-slope comparison with f1,
rather than an absolute perturbation estimate. Both source transfers
must be proved before any negative conclusion is asserted.

If this specific inherited correction fails, the positive research
target is a coupled head/border flux whose negative-G part respects
the successor's actual Schur reserve. A generic matrix receiver or
another first-atom-only sign certificate is not the intended output.

## C55 proof and positive survivor

At x7, let f=phi_1(x7), z=exp(-21), and
delta=exp(-182/5)/10^6. Exact exponential inequalities give
x7>=2/5, z<=10^-9, delta<=10^-21. Every source term remains present.

The retained two-atom quadratic uses all four ordered pairs. The exact
radial recurrence proves

    20,000,000*f^2 < E_two < 4,000,000,000*f^2.

For the complete n>=3 likelihood remainder D, the corpus's all-order
affine estimate gives |D^(n)|<=125^n*delta through order fourteen.
The Gaussian source recurrence gives |phi_1^(n)|<=2*48^n*f and
|phi_2^(n)|<=2*90^n*phi_2, while phi_2=(212/11)*z*f.
Leibniz then proves, with both cross terms and the tail square retained,

    |nativeJet_n-twoAtomJet_n| <= f^2 *
      (8*221^n*delta+160*z*263^n*delta+4*346^n*delta^2).

Contracting this with the exact witness coefficients bounds the FULL
energy error by 10,000,000*f^2. Thus E7>0 and E7<4,010,000,000*f^2.
The full likelihood derivative is nonpositive, and phi_1'/phi_1=-197/22
at q=7. Consequently Phi'<=-(197/22)*Phi and Phi>=f, giving

    G(x7) <= -(229/55)*f^2 < 0.

Since the canonical C3>10^9, E7+C3*G(x7)<0. The same is true
after adding C4*G(x7)/1120^2 for ANY C4>=0. This falsifies C53's
particular inherited-diagonal extension, not RH and not general matrix
flux positivity.

The positive survivor is an actual-source capacity: B7=E7/(-G(x7)).
It is strictly positive, strictly below C3, and
E7+C*G(x7)>0 exactly when C<B7. The source has a nonempty sharp
admissible correction interval; the canonical load exceeds it after
adjoining the seventh-degree direction. The full source and compensation
signs, matrix obstruction, and exact capacity all have final Lean audits
with only standard axioms. The leaf is wired and indexed. Full proof
and audit status: [closed candidate and positive survivor](../5-failed/tt-inherited-odd-diagonal-extension.md).

## C56: coupled flux in the central polynomial coordinate

New conjecture; no signed conclusion yet. The inherited correction
should be tested in the coordinate z2=c2+(168*q-56)*c3 rather than
c2 alone. This coordinate comes from the proved first-atom central
polynomial decomposition. Let u=(0,0,1,168*q-56), with x-derivative
u'=(0,0,0,336*q). Differentiating the actual center flux multiplied
entrywise by u*u^T gives the source lower matrix

    N4 + C3*(G*u*u^T + x*Phi^2*(u'*u^T+u*u'^T))
       + C4*G*e3*e3^T.

The omitted aperture term is a nonnegative multiple of u*u^T, not
a discarded signed term. At q=7 the C55 witness satisfies u.c=0,
so the entire inherited moving-flux quadratic vanishes in that
direction, including the derivative terms. Its positive native energy
therefore survives for C4=0 at that point.

This cancellation alone does not prove matrix positivity. The hard
next conjecture is existence of a fixed C4>=0 making the displayed
matrix positive definite on the positive half-line. The drift cross
term must be paid in the exact Schur complement; it must not be
silently dropped. The general coupled-flux repair remains open if
this specific moving coordinate fails. No generic receiver will be
counted as its solution. Rank-eight and all-rank integrated sign remain
the Route TT frontier.

### C56 necessary central-direction test

The moving-flux correction vanishes on the native central polynomial
P_q for every q, since c2+(168*q-56)*c3=0. Both the G-square and
the derivative cross term therefore vanish. In the negative-G chamber,
adding C4>=0 only lowers its energy. C56 consequently requires the
complete native P_q energy to be positive throughout that chamber.

Test q=6, which is beyond the proved neutral upper scale 45/8. The
literal retained core is R_(36,12)+8*z*R_(144,30)+16*z^2*R_(576,48),
with z=exp(-18), for the squared central polynomial P_6. The first
proof attempt asks whether this core is strictly negative with enough
margin for the complete n>=3 tail. This is a necessary signed test of
C56, not a first-atom sign surrogate. A negative retained model alone
does not establish an obstruction. No result is claimed before the
entire source and lawful correction are audited.

The proposed negative retained core at q=6 failed for a mathematical
reason: exact radial expansion gives positive constant, linear-z, and
quadratic-z coefficients. Thus that candidate cannot obstruct C56.
No sign of the complete C56 matrix follows from this one direction,
and no isolated retained-model theorem is being banked.

At the neutral center, eliminate the first two native odd coordinates.
Write p>0 for the remaining third pivot, r for its border, and s for
the last diagonal after that elimination. Put a=168*q-56 and
t=C3*x*Phi^2*336*q. The actual coupled Schur numerator is exactly

    p*(s-2*a*r+a^2*p) - (r-a*p+t)^2.

The established head gives p>0. The hard source sign is the displayed
expression, not the uncorrected central direction alone. The drift
term t must remain in the square. The omitted full-source tail needs
a bound that respects high-order reflection cancellations; separate
absolute derivative majorants can consume the compact reserve.
A complex Cauchy estimate for the literal omitted reflected source
is the next proposed analytic ingredient. Its applicability and full
source normalization must be proved, not assumed from holomorphy.

Proposed all-order analytic transfer: for q(x)>=5 and complex |z|<=3/20,
bound the COMPLETE reflected error

    Phi_C(x+z)*Phi_C(x-z)-T2_C(x+z)*T2_C(x-z)

in modulus by f1(x)^2/(5*10^8). The intended proof retains opposite
translations jointly: their exponential polynomial prefactors cancel.
On the disk, Re(exp(2*z))>=exp(-3/10)>=37/50. Each ordered pair
then has a normalized majorant 6*n^4*m^4 times
exp(q*(2-(37/50)*(n^2+m^2))). Geometric bounds for the full m>=1
and n>=3 sums would give 1000*exp(-27)<=1/(5*10^8).
The Cauchy derivative estimate then costs n!*(20/3)^n, rather than
independent real-derivative envelopes. This is a conjectured source
estimate under construction; its normalization and infinite sums are
not yet audited. It is intended to pay the complete fourteen-jet
error in the neutral Schur inequality, not to replace that sign proof.

The all-order analytic transfer is now proved. The saved leaf
`ThetaCuspReflectedCauchyTail` passes direct `lake env lean` without
warnings and a targeted `lake build --old +leaf`. Both the full disk
bound and the real jet transfer have scratch axiom audits with only
propext, Classical.choice, and Quot.sound. The proof includes both
infinite Gaussian sums, all reflected cross terms, analytic restriction,
and Cauchy's theorem. There is no assumed tail derivative estimate.

The next signed argument uses the central basis, with v=1/q and y the
normalized coordinates. Its source coefficient matrix is

    [1, 1-v/6, 5/4-5v/12+v^2/12, 5/4-5v/8+v^2/4-3v^3/56;
     0, -v/24, -5v/48+5v^2/192, -5v/32+5v^2/64-7v^3/384;
     0, 0, v^2/768, v^2/256-v^3/768;
     0, 0, 0, -v^3/43008].

Conjectured tail payment: the complete native-minus-two-atom quadratic
has absolute value at most (8q*f1^2)/10 times sum(y_i^2), for every
q>=5 and every y. A scratch proof contracts the audited all-order
bound with this actual basis. The remaining finite-source obligation
is positivity of the exact two-atom matrix with the actual drift;
the tail payment alone does not settle C56.

This complete central tail payment now passes the scratch Lean audit
with standard axioms only, for every source center with q>=5 and
every coefficient vector. The proof uses finite scalar envelopes and
a weighted double-sum identity; the initial monolithic tactic timeout
was removed without changing heartbeat limits. Its saved-leaf audit
is next. The mixed-pair floor and coupled-source sign remain open.

Concrete neutral-center sign attempt, still open: write the normalized
mixed-pair matrix as

    A12(q)_{ij} = R_{i+j+1}(4q^2,5q)/(8q*(2q-3)^2),
    M12(q) = B(1/q)^T A12(q) B(1/q),

where R is the audited signed radial recurrence and B is the displayed
central coefficient matrix. The normalized two-atom matrix is the
first-atom central matrix plus 8*exp(-3q)*M12(q) plus the nonnegative
second-diagonal-pair matrix. That final pair can be paid by its actual
first-atom positivity at scale 4q, rather than by an absolute error.

The proposed finite-source sign lemma is M12(q)>=-10000*I throughout
5<=q<=45/8. This is a conjecture, not an audited fact. It is enough
because exp(-3q)<=1/3200000 follows from exp(3)>=20: its negative
payment would be at most 1/40*I. No omitted source tail enters this
finite-pair lemma.

For the first-atom matrix with its moving-flux drift, a paper proof
candidate gives a 1/7*I reserve when 4/45<=v<=1/10,
h*(1-3v)^2=6v^2, and 0<=tau<=29/100. Here tau is the ACTUAL
quantity C3*x*Phi^2/(786432*q^5*f1^2), not an independently chosen
parameter. In this first-atom matrix v=1/(2q); the coefficient matrix
B above takes 1/q as its argument. The bound on this exact source quantity now passes its
scratch Lean audit with standard axioms only. The flux-to-matrix
identification is still required. The candidate proof uses weighted cross-term squares with
weight 2 on coordinates 1 and 2 against coordinate 3. Its scalar
obligations are h>=1/12, |c12|<=1/10, 3/25<=c23<=3/20,
d2>=85/144, and d3-5vh/2-c23>=1/10. The last inequality follows
from the existing exact polynomial identity for the final row, with
0<=1-10v<=1/9. These obligations have not yet been Lean audited.

If all these actual-source obligations close, the final reserve is
1/7-1/40-1/10=1/56, proving positivity at the neutral center, where
the G-square corrections vanish. Away from that center their signs
must still be included. This is a concrete attempted Schur payment,
not a claimed conditional endpoint or a solved C56 conjecture.

The complete drift-bound proof uses the corpus's existing one-percent
full-source mass comparison and C3<3*10^9. A tangent estimate gives
10x+107/40<=q, using pi*exp(93/200)>=5. The positive binomial
remainder on q>=5 then gives 1,250,000*x<=93*q^5. These combine
directly to bound the actual tau by 29/100. No new assumed mass or
derivative premise is introduced. Its saved leaf is
`ThetaCuspCoupledOddDrift`; final saved-leaf checks are underway.

Paper certificate for the proposed first-atom drift reserve:
put r=1-10v and D=(1-3v)^2. Then 0<=r<=1/9 and
49/100<=D<=121/225. The existing relation gives
1/12<=h<=6/49, while direct interval inequalities give
|c12|<=1/10, 1/54<=b:=5vh/2<=3/98, d1>=17/30,
and d2>=85/144. The exact c23 certificates are

    4D*(c23-3/25)
      =(423-3716r+3518r^2-3900r^3-1125r^4)/10000,
    4D*(3/20-c23)
      =(33+844r-682r^2+780r^3+225r^4)/2000.

Both are positive: bound r by 1/9 in the negative linear term of
the first, absorb its negative cubic and quartic terms into its
positive quadratic; in the second use r^2<=r/9. The corpus's final
row polynomial identity also gives m:=d3-b-c23>=1/10, since its
numerator is at least 6083 and D<=121/225.

For 0<=tau<=29/100, these imply |c23-tau|<=17/100. Pay the 01
and 12 cross terms with equal-weight squares, and the 13 and 23
cross terms with weights (2,1/2). The four resulting diagonal
reserves are bounded below respectively by

    1, 208/735, 541/3600, 779/5400,

each strictly greater than 1/7. This gives the proposed coercivity
of the explicit central model on paper. Its exact polynomial
identities, source normalization, and Lean proof are still to be
audited; it is not yet a complete-source positivity theorem. The
mixed-pair matrix floor remains the central unsolved signed claim.

Exact source split already available in `ThetaCuspTwoAtomAffineEnergy`:
`thetaCuspTwoAtomSignedEvenJet_eq_affine_add_second` works at every
order, and `thetaCuspSecondPairReflectionJet_eq_shift` identifies the
pure second pair. The odd-four first-atom positivity leaf applies at
the shifted scale 4q. Explicit affine radial polynomial identifications
currently read in `ThetaCuspTwoAtomAffineEvenFour` run through moment
6; this odd-four floor also needs moment 7. Build that exact recurrence
step and its polynomial sign certificate rather than treating the
missing table as a reason to change the conjecture.

Final C56 analytic audit: all three saved leaves pass direct
`lake env lean`, targeted `lake build --old +leaf`, and imported
axiom audits. All four public theorems use only propext,
Classical.choice, and Quot.sound. All leaves are wired once and their
public API rows are indexed. Repository lint still fails on eleven
unrelated unwired modules, with no error in these leaves. Temporary
proofs, search results, and audit logs are removed after recording
these outcomes. No complete C56 sign, rank-eight theorem, or RH
endpoint has been established.

Current mixed-pair sign proof uses a homogeneous version of the exact
radial operator:

    S_(a,b) P = -4*((X^2-4a)*(b^2 P''-2b P'+P)
                    +X*(b^2 P'-b P)),
    R_0(a,b)=4a+9b^2-6bX.

At b=1 this is literally the audited source recurrence. In the last
central quadratic, homogenize its three lower coefficients as

    A=b*(56b-168a),
    B=b^2*(784b^2-3360ab+6720a^2),
    C=b^3*(2304b^3-10752ab^2+26880a^2b-53760a^3),

and evaluate R_k(4a^2,b) at 5a. Substitute a=5u+(45/8)t,
b=u+t with u,t>=0. A positive polynomial certificate here would
cover the entire neutral interval exactly. The first direct proof
attempt hit default tactic limits, with no mathematical counterexample.
Normalization is being split into radial steps and coefficient-ring
maps are being expanded before collecting terms; no limits are raised.

The integer-scaled endpoint substitution is now a=40u+45t,
b=8(u+t), with u,t>=0. The exact denominator is

    K(a,b)=8a(2a-3b)^2(43008a^3)^2 b^7.

The last central diagonal plus 10000*K has a checked positive-
coefficient endpoint certificate (standard axioms only). The earlier
unshifted `positivity` failure retained raw casts and is not a sign
counterexample. The full ten-entry homogeneous mixed matrix has now
been normalized through the seventh radial moment in Lean, at default
limits. No full matrix floor is claimed yet.

For the full matrix, use all four leading principal minors of E+10000*K*I.
Their exact square decomposition is the corpus's four-dimensional
symmetric quadratic identity. The first three minor normalizations
elaborate; the single fourth-determinant normalization hits default
heartbeats. Splitting its six quadratic cofactors and seven determinant
terms is the current proof construction. No limit is raised, and no
source cross term is discarded.

The monolithic homogeneous determinant has unnecessary coordinate powers.
In the exact homogeneous central basis T, column j contains
D_j=(a*b)^(3-j). Write T=U*diag(D), with

    U=[43008, b(43008a-7168b), b^2(53760a^2-17920ab+3584b^2),
         b^3(53760a^3-26880a^2b+10752ab^2-2304b^3);
       0,-1792,b(-4480a+1120b),b^2(-6720a^2+3360ab-784b^2);
       0,0,56,b(168a-56b);
       0,0,0,-1].

Then E_ij=D_i*D_j*F_ij, where F uses U in the same literal radial
quadratic. The required diagonal allowance factors exactly as

    10000*K = D_i^2 * [10000*8*43008^2*(ab)^(1+2i)*(2a-3b)^2].

Thus the same matrix floor follows by diagonal congruence from F with
this graded diagonal allowance; no division or source term is lost.
Its leading minors have degrees 4,12,24,40 instead of 16,32,48,64.
This factorization is proved on paper and its Lean audit is prepared.
The attempted degree-48 sign still has only tactic-budget failures,
not a mathematical counterexample. Scalar radial value certificates
are now separated before assembling the reduced matrix.

### C56 unequal-pair floor: retain the actual exponential weight

The constant raw-matrix conjecture M12(q) >= -10000 I failed at
q=45/8: the fourth determinant of the shifted matrix is negative
there, while the first three leading minors are strictly positive.
The first three interval signs are kernel-checked. The exact fourth
endpoint negative certificate also passes Lean, using only propext,
Classical.choice, and Quot.sound. This
obstructs that uniform auxiliary floor, not C56 or RH.

The discarded correlation is the unequal pair's literal weight
8*exp(-3q). Keep the same intended energy payment and conjecture
instead

    M12(q) >= -10000*(3q-14) I,    5 <= q <= 45/8.

This is a source-weighted matrix sign test, not an increase of the
final payment. From exp(3)>=20 and exp(t)>=1+t,

    exp(3q) >= 20^5*(3q-14),
    8*exp(-3q)*10000*(3q-14) <= 1/40.

The exact homogeneous diagonal allowance becomes

    S_i(a,b) = 10000*8*43008^2*a^(1+2i)*b^(2i)
                 *(2a-3b)^2*(3a-14b).

Its degree is unchanged. The previous diagonal congruence gives
D_i^2*S_i=10000*8a*(2a-3b)^2*(43008a^3)^2*b^6*(3a-14b).
At a=40u+45t,b=8(u+t), the new linear factor is 8u+23t.
Every scalar radial entry remains unchanged; only this source-derived
allowance changes. Prove its four leading-minor signs, then transfer
to the actual exponential-weighted pair. The proposed complete-source
neutral reserve remains 1/56 after the audited 1/10 tail payment and
the still-to-be-audited first-atom drift coercivity 1/7.

The weighted fourth minor now passes its direct Lean audit, with only
propext, Classical.choice, and Quot.sound. All four leading-minor signs
are established. The source congruence and exponential payment also
elaborate; final quadratic glue currently has a finite-index/conditional
simplification repair, not a source-sign failure. No full floor theorem
or neutral positivity is claimed until this final audit succeeds.

The complete source-weighted mixed-pair floor now passes the direct
Lean scratch audit: mixedPairOddFour_exponential_floor has only
propext, Classical.choice, Quot.sound. The actual radial source
congruence, all four principal-minor signs, quadratic decomposition,
and literal exponential payment are included. Production leaf
ThetaCuspMixedPairOddFourFloor.lean is created and awaits its own
full leaf audit. The actual canonical-drift coercivity audit is next;
neutral-source positivity and global/all-rank closure remain open.

Actual canonical drift coercivity now passes Lean: substituting the
literal q(x), h(x), and normalizedCanonicalDrift(x), the complete
first-atom central quadratic including the derivative cross term is
at least (sum y_i^2)/7 on 5<=q<=45/8. Both the scalar coercivity and
actual-source substitution print only propext, Classical.choice,
Quot.sound. No free drift bound is assumed by the source theorem.
The remaining neutral step is exact source-energy assembly with the
mixed 1/40 and native-tail 1/10 payments; predicted reserve is 1/56.
The new mixed-pair production leaf is wired and its targeted --old
build is running. No umbrella or full build is used.

Production axiom audit now exits 0 and prints exactly propext,
Classical.choice, Quot.sound for mixedPairOddFour_exponential_floor.
The temporary API-name probe was also fixed by explicit universe
levels and passes. Seventeen superseded TTC56 scratch .olean artifacts
were removed after the production replacement was fully audited.
The complete source/neutral-anchor assembly is now being audited in
/tmp/TTNeutralAssembly.lean, with one owned foreground Lean process.

Global source reduction to retain after the neutral audit: eliminating
the first two native odd coordinates gives p,r,s. Put a=168q-56,
t=C3*x*Phi^2*a', P=p+C3*G. The actual coupled determinant numerator is

    P*(s-2*a*r+a^2*p+C4*G) - (r-a*p+t)^2.

The C3*G cross terms cancel exactly in this moving coordinate. In
central coordinates, they contribute only sigma*y2^2, where
sigma=C3*G/(4718592*q^5*f1^2); the C4 term contributes
C4*G/(8*43008^2*q^7*f1^2)*y3^2. These are paper identities pending
formal assembly, not a new positivity assumption. The literal G
changes sign once, so a single fixed C4 must satisfy both sides.
Corpus search found exact full-source lower/upper slope and mass
lemmas, and G/(f1^2*q^5)->0; these support later source estimates.
The active mathematical work remains the full neutral source audit
and then the global coupled source sign, not an asymptotic-only closure.

The COMPLETE neutral source theorem now passes its direct Lean scratch
audit. native_canonical_drift_coercive proves the literal native energy
plus actual canonical moving-coordinate drift >=(8*q*f1^2)/56*sum y_i^2
on 5<=q<=45/8. exists_neutral_coupledOddFour_positive then proves an
actual x>0 with G(x)=0 where the coupled form is strictly positive for
every nonzero native coefficient vector and every real C4. Both
print only propext, Classical.choice, Quot.sound. Full reflected tail,
both unequal pairs, pure second pair, inverse coordinate transfer,
actual C3 and actual neutral-anchor existence are included.

This resolves C56's neutral source-sign obstruction. It does not
produce a single global C4 or an all-rank/integrated sign. Production
leaf ThetaCuspCoupledOddNeutral.lean is created from the audited proof;
its own audit remains pending. The supporting first-atom energy
identity is added to ThetaCuspFirstAtomOddFourPositivity.lean, whose
targeted --old build is running. No full or umbrella build is run.

### C57: source-selected fourth coefficient (open conjecture)

Use the actual coupled matrix with C4=0. Let D4 be its determinant at
x=0, and let D3>0 be the canonical corrected odd-three determinant at
x=0. Both are literal source quantities, not free data. Consider

    C4* = 1 + max(0, -D4/(D3*Phi(0)^2)).

Conjecture: the actual coupled odd-four source matrix at C4* is positive
definite for every x>=0. This is a concrete stronger candidate for the
remaining C56 existence claim, not an established theorem. At zero,
the determinant becomes D4+3*C4*D3*Phi(0)^2>0; the three-row head has
the corpus's strict canonical margin. The new neutral theorem already
handles the actual zero of G. The hard obligation is the same fixed
source-defined coefficient on both sides of G, especially the compact
negative-G region. A failure of this particular coefficient would not
retire C56 or imply a falsification of RH.

Grounding: the current corpus gives all-order literal seam derivatives
via thetaCuspFullSource_seamJet_eq_formalJet; canonical odd-three
positivity; actual neutral positivity; native odd-four cofinal
positivity; and G/(f1^2*q^5)->0. Deep search for global odd-four coupled
compensation returned the new neutral theorem and no applicable global
producer among its hits; coverage was partial, generation 1189177,
background refresh pending. The search's suggested ingredient set is
unverified and only restates neutral positivity, not global closure.
No new C57 Lean code or source-coefficient bound has been claimed.

First hard C57 sub-obligation: establish the literal coupled source
form with C4=0 throughout G<0. This is necessary for every admissible
C4>=0, because adding C4*G*c3^2 can only decrease each source energy
there. A negative actual-source direction anywhere in that region
would rule out all such C4 for this moving u, not merely the proposed
seam coefficient. The neutral theorem supplies the endpoint margin;
no whole negative-G-ray sign is yet asserted.

FINAL AUDIT CHECKPOINT: both new production leaves and the modified
first-atom source leaf passed targeted --old builds and direct
`lake env lean <leaf>` audits. Public theorem statement checks confirm
no supplied neutral point or analytic source-sign hypothesis. Axiom
prints for firstAtomOddFour_energy_eq, native_canonical_drift_coercive,
exists_neutral_coupledOddFour_positive, and mixedPairOddFour_exponential_floor
contain only propext, Classical.choice, Quot.sound. Umbrellas and
index are updated; global lint has fourteen unrelated unwired-module
errors and none for these changes. Superseded owned proof probes and
caches were removed; production source is canonical. Audit logs and
research queries remain in /tmp, and minimal axiom probes import only
production modules. No owned Lean process remains live.

Route TT goal remains ACTIVE. Neutral source positivity is resolved.
C57/global fixed C4, integrated closure, all-rank repair, and RH remain
open. First next mathematical obligation is the unloaded coupled
source sign throughout G<0; any failure there rules out all C4>=0
for this particular moving direction.

### C58: global literal unequal-pair sign (open conjecture)

For q>=5 define E7(q)=sum_{k=0}^7 (3*(q-5))^k/k!. Conjecture:

    M12(q) + 10000*E7(q)*I is positive semidefinite for every q>=5.

The existing exact radial certificate gives maximal numerator degree16
and denominator degree9 in the last reduced mixed entry. Degree7
therefore matches its actual normalized growth. The source exponential
obeys exp(3q)>=20^5*E7(q), so the actual weighted energy payment stays
1/40. This conjecture extends the current compact-interval matrix sign
to the entire scale-five ray; it does not assume a mixed sign or use
external numerical experimentation. Test four polynomial leading
minors after q=5+u, u>=0, with the existing exact radial entries.
This is an ingredient for the hard coupled C4=0 sign on G<0, not a
replacement for global C56/C57 or all-rank closure.

### C59: source-correlated unloaded coupled positivity (open)

Conjecture: the actual coupled form at C4=0 is positive definite on
q>=5, with the canonical coefficient C3 retained. This implies the
necessary unloaded sign on G<0 in that ray. The remaining q<5 source
problem, global fixed C4, and all-rank problem remain separate.

Paper strategy from current source bounds: in central coordinates set
sigma=C3*G/(4718592*q^5*f1^2),
tau=C3*x*Phi^2/(786432*q^5*f1^2).
The first-atom matrix is the exact centralMatrix(1/(2q),6/(2q-3)^2),
with sigma added to (2,2) and -tau added to (2,3) and (3,2).
Test this matrix >= (1/7)I at both drift endpoints tau=0,tau=T(q)
and the lower compensation endpoint sigma=S(q). Convexity in tau
and monotonicity in sigma then give the entire source box, rather
than discarding q-dependence in unrelated uniform bounds.

For 5<=q<=8 use existing quadratic compensation lower bound and the
proved tangent 10x+107/40<=q:
 S(q)=3000000000*(101/100)^2*(1+9q/5-2q^2/5)/(4718592*q^5),
 T(q)=3000000000*(101/100)^2*(q-107/40)/(7864320*q^5).
For q>=8 retain the positive 3*Phi^2 term in the existing scale-seven
mass/slope argument and use 16x<=q:
 S(q)=3000000000*(3-13q^2/50)/(4718592*q^5),
 T(q)=3000000000*(101/100)^2/(12582912*q^4).
These are proof candidates, not established matrix signs or source
inequalities. Both S are nonpositive on their stated domains. The
actual source coefficients, slope, mass, and tangent estimates are
already corpus theorems; their combination and the two endpoint
matrix signs need Lean proofs. If C58 supplies global mixed cost1/40,
existing complete tail cost1/10 leaves source reserve1/56.

C58 source proof checkpoint: all four global principal-minor signs,
source diagonal congruence, exact radial identification, and actual
exponential payment have passed direct scratch Lean audits. The
result is exactly the existing mixedCentralMatrix source on every
q>=5, with cost1/40. Axiom audit uses only the standard three axioms.
Production now replaces the compact-only proof with this global
proof; the old compact theorem is a corollary, with no duplicated
certificate chain. Production target/direct audit are still pending.
Index refreshed; formal lint reports twelve unrelated umbrella
omissions and no error in this leaf. C59 model normalizations compile;
source endpoint identification is running, endpoint sign tests pending.

C59 scope refinement from literal source: the full statement of
exists_thetaCuspCompensationNeutralAnchor already includes the unique
sign transition and q(tau)>5. Therefore for x>=0, G(x)<0 forces x>tau
and q(x)>5. A proof of C59 on the scale-five ray covers the ENTIRE
negative-G region, not only its far subset. The positive-G small-scale
region still matters for global fixed-C4 positivity. The combined C59
entry identity exceeded the default heartbeat limit; it is now split
into four row proofs, without changing the conjecture or raising limits.

C58 COMPLETE: production --old target build, final direct leaf audit,
and production public-statement/axiom audit all exit0. Both public
floor theorems depend only on propext, Classical.choice, Quot.sound.
Global theorem assumes only q>=5 and takes an arbitrary Fin4 vector;
no source-sign or approximation hypothesis was introduced. Existing
umbrella import retained; index refreshed; lint has twelve unrelated
umbrella omissions and no error for this module. Superseded owned
C58 prototypes and four compiled caches removed. Frontier map now
records the global literal unequal-pair sign. C59 remains OPEN; its
row-by-row exact source identity is now under audit.

C59 mathematical sign checkpoint: all eight minor theorems in the
scratch model passed direct Lean audit (exit0), covering both drift
endpoints on the middle interval and the entire far ray. Axiom prints
are standard3 only. Thus the four endpoint polynomial matrices have
the proposed 1/7 reserve. Native-source positivity is NOT yet claimed:
source identity still needs the last denominator normalization, actual
source bounds are prepared but unverified, and matrix/source assembly
is pending. The positive scalar-minor certificates are genuine progress
on the coupled sign problem; no sign failure or route retirement occurred.

C59 exact-model checkpoint: source_endpoint_identify passed standard3
axioms, identifying every homogeneous entry with the exact first-atom
matrix and endpoint corrections. Quadratic-form assembly now also
passes: centralEnergy_middle and centralEnergy_far have standard3
axioms. A rank-one coordinate-mask decomposition avoids full finite
expansion and stays within default recursion/heartbeat limits. Actual
source-bound audit is running. Native capstone proofs, reusing the
complete pair/tail identities, are prepared but not yet checked.

### C60: a common loaded coefficient on the complete adverse region

C59 source bounds, full native assembly, and both nonzero-vector
capstones have passed scratch audits with standard3 axioms. Production
--old leaf build also passed; final direct audits remain in progress.

Next conjecture, grounded in the actual C59 reserve and existing full
compensation-source bounds: every fixed 0<=C4<=10^13 preserves strict
coupled positivity on q>=5. The mathematical target is a nontrivial
COMMON admissible coefficient interval on the entire adverse region,
not a new asymptotic result or numerical fit. In central coordinates
its last diagonal debit is C4*G/(8*43008^2*q^7*f1^2). Prove that this
is at least -1/112, leaving half of C59's 1/56 reserve. On 5<=q<=8,
use the complete-source quadratic lower bound and prove the polynomial
8*43008^2*q^7/112+10^13*(101/100)^2*(1+9q/5-2q^2/5)>0.
For q>=8 use the existing scale-seven normalized compensation bound.

The remaining global candidate is C4=10^13 on pi<=q<=5. No small-scale
sign or adequacy of this coefficient at the actual seam is assumed.
C57's source-defined coefficient also remains open. Corpus deep search
for odd-four seam/coupled inertia was partial, generation1190203,
pending refresh; its relevant hits provide actual energy, cofinal
positivity and seam-jet interfaces, not a global coefficient producer.
Lexical search with Hawking excluded likewise found no applicable
small-scale coupled-four theorem among the returned hits.

C59 COMPLETE production checkpoint: targeted --old build and BOTH
final direct `lake env lean` leaf audits exit0 without new diagnostics.
The production statement/axiom probe confirms source_central_coercive,
native_coupled_coercive, coupledOddFourEnergy_zero_pos_of_scale_five,
and coupledOddFourEnergy_zero_pos_of_compensation_neg depend only on
propext, Classical.choice, Quot.sound. The source first-atom reserve
is 1/7; the actual native reserve after both complete payments is1/56.
Thus no unloaded negative-G sign obligation remains. New RayModel is
wired into the umbrella, existing Neutral import retained. Frontier
map updated; index refresh and lint checkpoint follow. C60 source
budget and fixed-coefficient ray proof are under scratch audit.
Global positive coefficient, small-scale sign, integrated closure,
all-rank repair and RH remain OPEN.

C59 closure hygiene: index refresh completed. Lint reports thirteen
unrelated unwired modules; no C59 error, no prohibited declaration.
All seven owned TTC59 prototypes and matching compiled caches removed;
production leaves are canonical. Audit logs and the minimal production
axiom probe remain. C60's exact middle-budget and far-budget signs
passed on the first audit; assembly needed let-unfolding and negative
inequality proof repairs, not a change to the mathematical conjecture.

### C61: fixed coefficient on the small-scale source (open)

Conjecture: the actual coupled form at C4=10^13 is positive definite
for x>=0 with q(x)<=5. Together with C60 this would prove C56. First
attack the actual seam and its derivative-fourteen entry: current
source interfaces identify all orders, and explicit exact scalar
polynomials reach order12. Derive order14 by applying the existing
mass-normalized modular Lie derivative twice to the proved order12
polynomial. At S=W=0 only its transverse two-jet contributes:
if A is the seam modular gap, s=3-3A/4 and w=2+A/2, then

  L^2 Q = s^2 Q_SS + sw(Q_SW+Q_WS) + w^2 Q_WW
          -2Aw Q_A - (s/6)Q

at the seam. This is an exact structural derivative identity, not an
asymptotic approximation. It permits the missing source14 entry without
expanding the entire general-state fourteenth polynomial. Next use the
literal source coefficient C3 and the seven existing seam moments to
prove or refute the C61 seam sign, retaining its actual pi-dependent
moving direction. No sign at the seam or on the compact region is
claimed yet. Search tt_c61_fourteenth_source_search.json is partial,
snapshot generation1190258 (current1190266), background refresh pending;
it returns exact SourceJet12 and all-order/seam interfaces, but no
fourteenth seam producer among the hits. Exhaustive source-text search
also found no SourceJet13/14 or ReflectedScalar14 declaration.

C60 COMPLETE: ThetaCuspCoupledOddLoaded.lean passed production --old
leaf build, final direct `lake env lean` audit, and exact public-type/
axiom probe. All three public theorems use only standard3 axioms.
Every fixed 0<=C4<=10^13 retains reserve1/112 on q>=5 and is strictly
positive for every nonzero native vector throughout the whole negative-G
region. No analytic sign premise has been inserted. Umbrella wired;
index updated; lint retains unrelated umbrella omissions only. Owned
C60 scratch sources removed; production canonical. Frontier map updated.
C61 seam transverse two-jet proof is now under direct scratch audit.
The small-scale sign, global C56/C57/C61, integrated closure, all-rank
repair and RH remain OPEN.

C61 exact fourteen-jet checkpoint: scratch source_fourteen now passes
with only propext, Classical.choice, Quot.sound. It identifies the
literal derivative14 of the complete source at zero with the factored
modular polynomial. The generic transverse two-jet identity and all six
polynomial evaluations passed without raised limits. One redundant
`dsimp` was removed; an output-cache root mismatch was corrected using
the documented Lean --root option. No mathematical sign failure yet.
The actual seam determinant still needs its sign proof. At the seam
C3's correction is positive rank one, so test C3=10^9 first, then use
its proved lower bound. Native third cofactor is negative there; the
rank-one determinant formula is concave in the moving direction, so
its two pi-enclosure endpoints suffice after exact identity proof.
Only the order14 source identity is currently established, not this
proposed determinant sign or compact propagation.

C61 canonical coefficient refinement (paper identity, not yet Lean-audited):
write normalized seam native head minors H2>0 and D3<0, native D4,
and cofactors A=cof22, B=cof23. The literal canonical coefficient gives
C3*G0=-3*D3/H2 exactly, since G0=3*Phi0^2. Thus the normalized coupled
determinant at direction t=168*pi-56 obeys

  H2*Dcoupled = H2*D4 - 3*D3*(A+2*t*B+t^2*D3)
               -2*C4*G0*D3*H2.

Here G0 is normalized by the common squared theta mass. This retains
the exact source-selected C3 if the stronger C3=10^9 endpoint test is
too conservative; it requires no improved numerical C3 enclosure.
Jacobi's identity also gives H2*D4=D3*A-B^2. Any failure of the
lower-C3 auxiliary test must not be called a failure of C61 before
checking this exact canonical identity and sign.

C61 order14 subproblem COMPLETE in production: ThetaCuspOddSeamFourteen
passed targeted --old build, final direct leaf audit, and four public
axiom checks (standard3 only). Its literal source_fourteen and
native_fourteen have no source-sign or approximation premise. Umbrella
wired; index refreshed. Superseded seam-jet/source/nonhomogeneous-model
scratch files and source-jet cache removed. The production identity is
canonical. C61 compact sign remains OPEN. Separate cofactor and Jacobi
identities also pass scratch kernel audit, standard axioms only. The
homogeneous endpoint sign still needs its normalization decomposition;
failed combined proofs were default-limit/elaboration failures, never
negative determinant witnesses. No proof limit was raised.

C61 compact drift target (paper identity, awaiting Lean): for native
moments m0..m6 at a center, let H2, D3, D4 be their leading minors,
A=cof22, B=cof23, t=168q-56, s=C3*G,
r=C3*x*Phi^2*(336q), L=C4*G. The actual lower-block correction is
[[s,s*t+r],[s*t+r,s*t^2+2*t*r+L]]. Its exact determinant should be

  D4+s*(A+2*t*B+t^2*D3)+2*r*(B+t*D3)
    +L*(D3+s*H2)-r^2*H2.

This exposes the precise compact obligation, including the adverse
quadratic drift term. Existing global odd-three positivity supplies
D3+s*H2>0; it does not supply this four-row sign. Search
/tmp/tt_c61_compact_source_search.json completed (partial=false;
source snapshot generation1190854/current1190858; many compiler
records pending/stale). Candidate lemmas recover the compact odd-three
polynomial proof and our q>=5 coupled source theorem, not the missing
compact coupled-four producer. No new sign claim. Strict four-variable
square completion passed scratch audit with standard3 axioms. Current
endpoint normalization uses direct rewrites after recursive simp
exceeded default limits; no heartbeat limit raised.

C61 lower-C3 surrogate failed: after correcting Fin numeral projections,
both homogeneous endpoint polynomials for C3=10^9,C4=10^13 have strictly
negative coefficients. Exact negative endpoint audit is running. This
refutes the proposed whole-box positive surrogate, not the actual
canonical source and not RH. The canonical coefficient must be retained.
Its cleared determinant model is now prepared without bounding C3.

Positive survivor from the source correlation and Jacobi (paper proof):
with actual seam H2>0,D3<0,D4, cofactor B, G=3*Phi0^2 and canonical C3,

  H2*Dcanonical(t,C4) =
    -2*H2*(D4+C4*G*D3) - 3*(D3*t+B)^2.

Proof: substitute C3*G*H2=-3*D3 into the exact coupled cofactor formula,
then substitute H2*D4=D3*A-B^2 and complete the square. This is an exact
source-selected direction penalty: optimal seam direction is t=-B/D3;
for any other t the loss is precisely 3*(D3*t+B)^2/H2. It supplies a
sharp replacement criterion, not a reason to discard the coupled route.
Source-specific Lean binding remains to be formalized. Canonical
C4=10^13 sign test takes precedence; no global failure inferred from
failure of the lower-C3 surrogate.

C61 literal obstruction CLOSED IN SCRATCH: actual_seam_determinant_neg
passed with standard3 axioms (/tmp/tt_c61_actual_seam_negative_closed.audit.log).
It uses the complete theta source, actual pi, exact canonical C3, and
C4=10^13 at direction168*pi-56. The optimized-direction homogeneous
reserve also passed, standard3 (/tmp/tt_c61_optimal_seam_sign.audit.log).
Thus C61's original direction is wrong at the seam, while the same load
admits a positive optimal-direction determinant. Literal optimized
bridge and full PosDef conclusion are prepared for production audit;
no global-direction positivity is claimed. Four production leaves
Direction/Model/Signs/Obstruction are now prepared and wired, but their
production builds/final audits/index/lint remain pending.

C62 NEXT HARD CONJECTURE: a smooth direction eta(x), equal to the
original168*q(x)-56 on q>=5 and equal to -B(0)/D3(0) at zero, makes the
literal coupled source strictly positive with the SAME C4=10^13.
The actual correction for u=c2+eta*c3 is
C3*(G*u^2+2*x*Phi^2*u*eta'*c3)+C4*G*c3^2.
This is grounded in the audited original flux form and source-specific
optimal-direction identity, not a new assumed source inequality.

C62 paper mechanism (NOT YET LEAN): at each center let H2>0,D3,D4,A,B
be the actual native head/cofactors, s=C3*G, rho=C3*x*Phi^2*eta', and
R=H2*rho-D3*eta-B. Exact Schur algebra gives

  H2*Dcoupled = (D3+s*H2)*(A+C4*G*H2+D3*eta^2+2*B*eta)-R^2.

Choosing C3*x*Phi^2*H2*eta'=D3*eta+B cancels R. The canonical source
coefficient makes this a regular-singular equation x*eta'+p(x)*eta=f(x)
with p(0)=1 and f(0)=-B(0)/D3(0), so its regular initial direction is
forced to be the proved optimal direction. Hard remaining obligations:
construct the actual regular solution/control through the compact
region; prove the scalar Schur gap A+C4*G*H2+D3*eta^2+2*B*eta positive;
join the already proved q>=5 direction while retaining a controlled
residual and the exact flux identity. None is assumed or claimed.
Searches tt_c62_schur_direction_transport_search.json (partial snapshot
1191448/current1191449) and tt_c62_direction_source_search.json
(partial=false snapshot1191474) recover the literal coupled energy,
canonical drift bounds and related modular drift equations, not this
source-direction producer. Candidate/source-argument hits inspected;
no training-data or external numerical conjecture used.

2026-10-03 C62 transport producer: prepared the actual global continuous
regular solution (not merely an existence receiver). Set
K=C3*Phi^2*H2>0, p=-D3/K, f=B/K. The exact canonical coefficient gives
p(0)=1 and f(0)=t_opt. Since the complete reflected jets are differentiable,
k=dslope p 0 is continuous and x*k(x)=p(x)-1. Let

  mu(x)=exp(integral_0^x k),
  y(x)=mu(x)^(-1)*integral_0^x(mu*f),
  eta(x)=dslope y 0 x.

Then eta is continuous, eta(0)=t_opt, differentiable off zero, and
x*eta'+p*eta=f at every x (the x=0 equation uses the literal endpoint).
Thus K*x*eta'-D3*eta-B=0 with no source premise. At the latest scratch
checkpoint p/f endpoint values, coefficient differentiability and
continuous removable k are audited; integral/direction assembly is
being repaired for two Lean elaboration/no-goal issues. No limit raised.
Do not call the full direction theorem proved until its audit passes.

The full actual determinant identity is separately prepared in
TTC62SchurTransport. It retains the exact residual square and reduces
the constructed direction's determinant sign to its actual Schur gap.
The initial gap is strictly positive by the C61 optimal source repair.
The next substantive inequality is positivity of this gap across the
compact region; local continuity alone does not close that problem.
C62 must also retain a controlled transition to the established
adverse-ray direction: no inherited C60 bound applies automatically
when eta differs from168*q-56.

C62 source construction scratch audit COMPLETE: the explicit direction,
its continuity, optimal seam value and exact residual cancellation all
passed with standard3 axioms (tt_c62_source_transport_complete.audit.log).
The continuous removable coefficient requires only differentiability of
the actual source moments and the exact canonical coefficient identity.
The general solution is differentiable away from zero; smoothness at zero
is not claimed. The corrected flux needs that punctured derivative and
continuous zero-boundary value. A production source-transport leaf is
prepared/wired; its build and direct audits are still pending.

C63 proposed gap attack (sign conjecture, NOT PROVED): normalize the
actual gap by Phi^6. Write a=A/Phi^6, b=B/Phi^6, d=D3/Phi^6,
l=C4*G*H2/Phi^6. Along the residual-free direction on x>0,

  (gap/Phi^6)' = a'+l'+d'*eta^2+2*b'*eta
      +2*(D3*eta+B)^2/(x*(C3*Phi^2*H2)*Phi^6).

The last term is nonnegative. A source-native nonnegative quadratic
[a'+l',b';b',d'] on the compact interval would propagate the proved
initial gap. This is a substantive new source-sign conjecture, not an
assumed inequality. If that uniform quadratic is false, the exact
identity still exposes the needed inequality along the constructed
trajectory; its negative component must be paid by the retained square.
Search tt_c63_gap_derivative_search.json is in progress. Do not claim
any derivative sign or interval propagation before kernel proof.

C62 exact Schur scratch audit COMPLETE: determinant_residual_square,
determinant_direction, determinant_direction_pos_iff, schurGap_zero_pos,
and eventually_schurGap_pos all pass, standard3 axioms only.
The Schur identity retains the actual derivative and all native moments;
the determinant sign equivalence uses the already proved global canonical
third-minor positivity. No global fourth-gap sign is asserted. Prepared
and wired ThetaCuspCoupledOddTransportSchur for production audit.
C63 derivative search was partial (snapshot1215642/current1215643);
candidate/source-argument hits give generic quadratic algebra, not the
actual normalized source-sign theorem. Compact source coordinates and
all-order literal Lyapunov jet incidence are available and being used.

C63 source test: write P_j for exact source seam derivatives of order 2j,
and m_k for signed reflected derivatives of order 2(k+1). Native second
center variations (all odd source jets vanish at the seam) are

  v0=-(2P0P2-2P1^2),
  v1=2P0P3-2P1P2,
  v2=-(2P0P4+8P1P3-10P2^2),
  v3=2P0P5+26P1P4-28P2P3,
  v4=-(2P0P6+52P1P5+30P2P4-84P3^2).

The candidate curvature of D3/Phi^6 has cleared numerator
P0*(gradient detThree(m) dot v)-6P1*detThree(m).
All ingredients are the existing exact source polynomials through twelve.
This is a symbolic source-sign conjecture, not a numerical experiment.
First audit failed at positivity (goal-shape diagnostic); no sign verdict
has been inferred. Exact all-order native first/second variations and
literal normalized-gap derivative are prepared as separate scratch proofs.
Compact-coordinate search partial snapshot1215680 recovers the all-order
literal Lyapunov polynomial incidence but no needed quadratic sign law.

Potential sharper C63 continuation if uniform quadratic positivity fails:
for D3<0 let r=-B/D3 and Smax=A+C4*G*H2-B^2/D3. Then gap equals
Smax+D3*(eta-r)^2 exactly. The actual regular solution obeys
eta'=(p/x)*(r-eta), p=-D3/K>0, so it is a weighted running average
of the moving optimal direction, with (x*mu)'=mu*p. A source-derived
bound on tracking error could retain the positive chamber even when
an arbitrary-direction quadratic derivative is indefinite. Neither a
tracking bound nor Smax positivity beyond the seam is yet proved.

C61/C62 production checkpoint: all four C61 leaf --old builds and final
direct audits passed. C62 DirectionTransport and TransportSchur each
passed direct lake env lean -o audits against the current source.
All current production capstone axiom reports are standard3 only in
/tmp/tt_c63_gap_derivative.audit.log. That combined scratch run exited1
only because C63's function-valued derivative expression needed an
explicit eta expansion before rewriting; its sorryAx is confined to
that failed scratch theorem, not any production declaration. Fix made,
rerun pending. Index passed. All owned superseded TTC61 and TTC62
scratch sources/caches were removed; retained audit logs as evidence.

C63 auxiliary homogeneous seam-curvature certificate passed (exit0,
/tmp/tt_c63_seam_curvature_hom.audit.log): degree17 cleared candidate
curvature is strictly positive on the full proved seam-scale interval,
via positive homogeneous coordinates. This only checks the algebraic
necessary entry; actual second-derivative incidence is not yet audited,
and full quadratic PSD or compact gap monotonicity is NOT established.
To test the other entries, the normalized A-cofactor curvature requires
the order16 source jet. Corpus search tt_c63_source_sixteen_search.json
running. Existing exact source14 proof retains transverse two-jet of
source12; order16 needs its transverse four-jet or an equivalent exact
Lie iteration. Missing source algebra must be constructed, not assumed.
Current lint has13 unrelated umbrella omissions (including a newly
listed ThetaTailPositiveBalancePrimitive); no C61/C62 module errors.

2026-10-04 C63 order16 source construction (paper proof, Lean scratch prepared):
source-sixteen search completed, partial=false, generation1215863;
no applicable source16 jet was found in candidate/source-argument hits.
For the exact corpus vector field S'=3-S^2/3-3A/4,
A'=-2AW, W'=2+A/2+2S^2/9-2SW/3 and mass'/mass=-S/6,
put s=3-3a/4, w=2+a/2, a2=-2aw,
s3=-2s^2/3+3aw/2, w3=-aw+4s^2/9-4sw/3,
a4=12aw^2-2aw3. At the seam v=(s,0,w), acceleration=(0,a2,0),
third variation=(s3,0,w3), fourth=(0,a4,0). Thus

  (mass*Q)''''/mass = D4Q[v,v,v,v]+6a2*D3Q[A,v,v]
    +3a2^2*Q_AA+4D2Q[(s3,0,w3),v]+a4*Q_A
    -s*(D2Q[v,v]+a2*Q_A)+(-s3/6+s^2/12)*Q.

Applying this to the existing exact source12 polynomial uses only its
transverse terms through degree4. Prepared TTC63FourthSeamLie with the
generic identity and coefficient-level partial-derivative commutation;
prepared TTC63SourceSixteen with copied existing monomial text, fourteen
exact partial-jet identities, and literal source16 assembly. NOT audited.
No external coefficient evaluation, source truncation estimate, limit
increase or source hypothesis is used by this proposed construction.
C63 normalized-gap derivative second audit failed only on function-power
eta expansion; fixed Pi.pow_apply, third audit running. Native moment
variation scratch had the same function-product issue plus one missing
parenthesis; patched, rerun pending. No mathematical sign failure claimed.

C63 normalized-gap derivative scratch audit COMPLETE (exit0, standard3,
tt_c63_gap_derivative.audit3.log). Both exact derivative and unconditional
nonnegative squared-gain lower bound on x>0 passed. Promoted/wired
ThetaCuspCoupledOddGapDerivative; final production audit pending.
This proves the new actual-source differential identity, NOT positivity
of the remaining source quadratic or of the compact gap. Now auditing
the fourth covariant seam identity needed for source16 and the full
seam quadratic-variation sign test.

C63 planned full seam quadratic test, grounded in exact source16 construction:
Let P_j be source derivative2j divided by literal seam mass, and m_r be
signed reflected derivative2r divided by its squared mass. Exact proposed
second center variation (r>=1) is

  v_r = 2*(-1)^r * sum_(j=0)^r
    (choose(2r,2j)-choose(2r,2j+1))*P_(j+1)*P_(r-j).

This follows by pairing the two even-index terms in the finite Leibniz
second variation; odd-index terms contribute the negative cross term.
It gives all seven needed variations using P0..P8, where P7 is existing
source14 and P8 is the pending source16. The actual polynomial incidence
must be audited; do not infer it from the displayed formula alone.

For actual cofactor values A,B,D and their native second variations A2,B2,D2,
let H=m0*m2-m1^2 and H2=v0*m2+m0*v2-2*m1*v1 (here m0 is signed order2).
At the seam G=3Phi^2, G''=10Phi*Phi'', and all first variations vanish.
The normalized quadratic derivative's first nonzero candidate matrix,
after multiplying by the positive P0^7, has entries

  Na=P0*A2-6*P1*A+C4*(3*P0^3*H2-8*P0^2*P1*H),
  Nb=P0*B2-6*P1*B,
  Nd=P0*D2-6*P1*D.

The auxiliary Nd polynomial positivity already passed on the actual seam
scale interval. Na*Nd-Nb^2 is the next decisive test for the proposed
uniform quadratic sign. Its homogeneous degree is36 after inserting the
fixed C4 load with its proper degree. No sign is yet known or assumed.
If this uniform test fails, the actual-direction survivor is instead
D^2*Na-2*B*D*Nb+B^2*Nd at eta(0)=-B/D; do not retire the route without
attacking the actual trajectory and retaining the nonnegative gain.

Fourth seam formula diagnostic: the reduced residual consists entirely
of pderiv_S(2) and pderiv_W(2) factors. Thus no mathematical formula
correction is indicated. Added the explicit derivative-of-constant fact
from pderiv_C to the simplifier; third audit running. Partial-derivative
commutation itself passed. C63 GapDerivative production direct audit
passed; exact production axiom probe and refreshed lint pending.

C63 fourth covariant seam identity AUDITED: TTC63FourthSeamLie exit0,
standard3 axioms (tt_c63_fourth_seam_lie.audit4.log). The displayed
paper fourth-variation formula is now a kernel-checked generic theorem;
the only repair was explicitly reducing pderiv of the numeral2 via
2=1+1, additivity and pderiv_one. No formula change or limit increase.
TTC63SourceSixteen literal-source assembly is now under audit using
this valid scratch module cache. C63 GapDerivative refreshed index
passed; latest lint12 unrelated umbrella omissions, no owned errors.
