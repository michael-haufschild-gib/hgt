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
endpoint negative certificate is under final scratch audit. This
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
