# TT: all-rank center-flux induction

- **ID:** tt-all-rank-center-flux-induction
- **Stage:** 1-in-progress
- **Type:** OPEN CONJECTURE; all-rank current sign unproved
- **Route:** TT, complete signed theta current

## Corpus basis and target

`ThetaCuspCenterMixedAllOrderIntegration` identifies every actual signed
Hankel form with its complete physical center integral. Its all-order
nonnegativity is equivalent to RH. The current source contains
`thetaCuspCenterMixedSignedHankel_seven_posDef` in
`ThetaCuspCenterMixedSeventhRankStrict`; the older successor-source comment
calling rank seven open is stale. No bound at every rank follows from that
finite theorem. These existing declarations were read, not newly audited here.

Let Phi be the actual complete theta source, w_a(r)=r*sinh(a*r), and
J_N(r) the native Fourier-signed reflection-jet matrix at r/2. The corpus
already supplies the exact zero-boundary flux

    F_a(r)=r^2*sinh(a*r)*Phi(r/2)^2.

Every polynomial multiple of F_a has integrable derivative and zero
half-line derivative integral. The proved ranks use such compensation to
repair native negative directions without changing the integrated moments.

**C45.** For every N and 0<a<1/2, construct a symmetric matrix polynomial
P_(N,a)(r), directly from the Gaussian integer source, for which

    w_a(r)*J_N(r) + d/dr [F_a(r)*P_(N,a)(r)]

is positive semidefinite for every r>0. This would prove the existing
all-order integrated cone and hence RH. The requirement is a construction
and a sign proof, not a new premise admitted into Lean. No such general
construction has been proved.

## First induction test

Adding only a last-diagonal flux does not follow from positivity of the
integrated head. Even when a corrected pointwise head A(r) is positive
definite, a border b(r),c(r) requires the added derivative to dominate

    d(r)=b(r)^T A(r)^(-1) b(r)-c(r).

Its integral must therefore be nonpositive. Put H=integral A,
q=integral b, and m=H^(-1)q, with all displayed integrals finite. Expanding
the square and using H*m=q gives the exact paper identity

    integral [b^T A^(-1)b]
      = q^T H^(-1)q
        + integral [(b-A*m)^T A^(-1)(b-A*m)].

Thus a last-diagonal correction must pay an additional nonnegative
variation term beyond the integrated successor Schur requirement. Ignoring
this term is not a valid induction. This calculation neither falsifies C45
nor signs the actual successor. It motivates retaining off-diagonal fluxes
and their exact boundary values in the next construction. No generic
conditional Schur wrapper was added to Lean.

## Outstanding hard work

Construct the matrix flux using the actual integer Gaussian source, retaining
all cross terms, and prove its sign at every rank and every center. Existing
fixed-rank estimates, Gaussian tail limits, and zero-flux identities do not
establish the uniform induction. No numerical experiments are planned.

C49 now proves that the actual native signed center jets have both signs
above every order, with negative jets on positive-center intervals
(`ThetaCuspNativeCenterJetOscillation`). Thus C45 must repair diagonal
orders without a finite cutoff; off-diagonal transport alone cannot close
it. This all-order necessity follows from the complete source's flat
imaginary odd cusp. It supplies no integrated sign or successor Schur
payment. The rank-eight residual in `tt-actual-odd-border-primitive.md`
remains a concrete next sign test.

C50 now closes the outer native source region at every finite rank and
every nonnegative integer moment shift. The exact first-atom profile has
a jointly smooth inverse-square-root-scale extension; the all-order full
source remainder transfers each Gaussian jet limit. Every limiting shifted
matrix is a positive diagonal congruence of a positive-shape Gamma moment
matrix. `RHTower.ThetaCuspGaussianLimit.nativeShiftedMatrix_posDef_eventually`
in `ThetaCuspAllRankNativeTail` is unconditional and audited;
certificate: `../3-formalized/tt-all-rank-native-tail.md`. Each rank still
has a compact region requiring actual diagonal and mixed correction, with
zero integrated flux. No uniform rank threshold or integrated sign follows.

## Search and status

2026-10-02: three corpus queries inspected candidates and source arguments,
including the complete pair current and the successor source. The broad
Gaussian-pair query was partial (decomposition deadline); the constrained
Wigner and center-mixed queries completed. Refresh was incomplete because
the background indexer was running; semantic coverage was unmeasured.
Direct source reads checked the relevant definitions and the stronger
rank-seven declaration. No external-literature frontier was substituted.

The preceding pass produced the audited timelike bilinear flattening theorem
recorded in `../5-failed/tt-timelike-bilinear-flattening.md`. The current pass
also audits the exact border-degree invariant below. C45 remains open;
neither result supplies the RH-strength current bound.

## 2026-10-02: test of exact off-diagonal flattening

Fresh corpus search also located `ThetaCuspSchurMovingMinimizerVariance`:
the moving-minimizer square is prior formal knowledge, not a new result of
this card. Its integrated form still correctly identifies the payment.

The proposed next construction set the corrected border equal to A(r)*m
for a fixed vector m, removing that variation. This can be effected by
a zero-endpoint primitive of A*m-b when their integrals agree. However,
the primitive need not be a polynomial multiple of F_a.

There is a source-specific degree test. Write x=r/2,
q=pi*exp(2x), f=thetaCuspSourceTerm(x,1), and
J_k=(-1)^k*thetaCuspNativeReflectionJet(2k,x). The current corpus gives
J_k/(f^2*q^k) tending to its positive Gaussian moment through k=6.
The final odd-four border contains J_6, while the existing odd-three
head contains only J_1,...,J_5 and its center-flux correction.

For every polynomial P in the physical radius, the derivative of P*F_a,
divided by w_a*f^2*q^6, tends to zero: polynomial radius growth loses to
each positive power of q. Consequently no fixed linear combination of
the lower J_k and such a flux derivative can equal J_6 on the full ray.
The positive survivor is the unchanged, strictly positive sixth Gaussian
moment in that residual. The paper proof and all four public Lean theorems
are now audited in `ThetaCuspPolynomialFluxBorderDegree.lean`; full
certificate: `../5-failed/tt-radius-polynomial-border-flattening.md`.

This test does not falsify C45, which does not demand exact border
flattening. It excludes this particular construction inside its radius-
polynomial class. A source-based continuation should test polynomials in
the Gaussian scale q (or genuine source primitives), retaining their
signed tail payment, rather than increase the degree of a radius polynomial.

### C46: a Gaussian-scale flux with the correct center boundary order

The degree obstruction suggests a concrete new family. For k>=2 put

    Q_k(q)=q^(k-2)*(q-pi),
    G_(a,k)(r)=w_a(r)*Phi(r/2)^2*Q_k(q(r/2)).

The factor q-pi vanishes at r=0. Since w_a(r)=O(r^2), this gives
G_(a,k)(r)=O(r^3) and G'_(a,k)(r)=O(r^2), matching the native weighted
source order. The version with Q=q^(k-1) lacked this order: its derivative
started at order r and could create an artificial leading seam matrix.

The proposed exact asymptotic is

    G'_(a,k)(2x)/(w_a(2x)*f(x)^2*q(x)^k) -> -2.

Indeed, with L=log Phi and r=2x, the quotient before normalization is

    G'/[w_a*Phi^2]
      = [1/r+a*coth(a*r)+L'(r/2)]*Q_k(q) + q*Q'_k(q).

The corpus gives Phi/f->1 and Phi'/(f*q)->-2. Also Q_k/q^(k-1)->1,
q*Q'_k/q^k->0, and the remaining radius/aperture factor divided by q
tends to zero. Thus the displayed limit follows on paper. At k=6 the
candidate correction +(2724986880/2)*G'_(a,6)/w_a cancels the retained
leading sixth Gaussian moment. It does not sign the remainder.

Next proof obligations: verify this candidate against prior corpus work;
formalize its exact zero-boundary and integrability laws and leading
source cancellation; then control the complete corrected matrix rather
than infer positivity from the vanished leading term. The calculation
is a candidate construction, not an audited current estimate or an RH proof.

A second focused corpus search completed without errors. It returned the
existing flux log-rate limits, first-atom scale profile, and Gaussian jet
limits, plus the newly indexed radius-polynomial leaf; it did not establish
the proposed Gaussian-scale flux family or its global sign. Candidates,
source arguments, proof ideas, and recipes were inspected. Refresh remained
incomplete while the background indexer ran, and semantic coverage was
unmeasured, so no exhaustive novelty claim is made.

### C46 full-matrix test: the next term cannot be discarded

The current corpus's exact first-atom affine profile gives, on writing
H(q,t)=exp(-2*q*(cosh(2*t)-1)),

    m_k(q)=(-1)^k*d_t^(2k) H(q,0),
    m_(k+1)=8*q*m_k+(16*q^2-4*q)*m_k'-4*q^2*m_k''.

Consequently its two leading coefficients are G_k and
-G_k*k*(k-1)/12, where G_0=1 and G_(k+1)=8*(2*k+1)*G_k.
The affine first-atom factor changes only terms of degree at most k-2
after division by the squared first atom. The complete-source all-order
relative-error theorem makes its error smaller than every fixed inverse
power of q. These give the paper expansion

    J_k/f^2 = G_k*q^k-G_k*k*(k-1)*q^(k-1)/12+O(q^(k-2)).

For the proposed G_(a,k) flux, cancellation by G_k/2 leaves the normalized
next coefficient

    G_k*[pi+7/4+a/2+(7*k-k^2)/12].

It is negative for all sufficiently large k, including even k (diagonal
matrix entries). Thus simultaneous cancellation of every leading Gaussian
moment does not give a positive matrix. This is a paper calculation,
not yet an audited all-order Lean no-go; C46's selective off-diagonal
construction and C45 remain open. No finite-rank source sign is inferred.

### C47: preserve the scale operator and its physical boundary form

Rather than erase the positive leading Gaussian matrix, retain the exact
operator generating all its jets. With U=exp(-2*q)*P(q), conjugation of
the displayed recurrence gives

    A U = -4*q^2*U''-4*q*U'+16*q^2*U.

Its unweighted Green identity is

    U*A U/q + (4*q*U*U')' = 4*q*(U')^2+16*q*U^2.

The first atom is connected exactly, not by a tail approximation:
its reflected product is 4*q^2*exp(x-2*q) times
[(2*q-3)^2*H+6*q*partial_q H]. This suggests using the operator and its
boundary flux to obtain a Gram representation of the complete signed
matrix. The hard obligation is to retain the actual center weight and
all ordered atom pairs in that representation.

There is a specific warning to resolve, not an admissible omitted term.
For a physical weight V the exact Green form instead contains

    V*U*A U/q + (4*q*V*U*U'-2*q*V'*U^2)'
      = 4*q*V*(U')^2 + [16*q*V-2*(q*V')']*U^2.

For V(q)=log(q/pi)*sinh(a*log(q/pi)), the second potential is negative
near q=pi: V has a double zero there, while (q*V')' is positive there.
The unweighted positive operator therefore supplies no automatic sign
for the required physical form. C47 must pay this exact remainder using
the actual source; arbitrary polynomial tests cannot be silently restricted.
The exact operator/source identities and the strict sign defect on a whole
positive-radius interval are now checked in `ThetaCuspGaussianScaleOperator`.
The first-pair operator tested on Phi is not its native reflection-jet
operator: ordered-pair potentials differ. Thus this is an obstruction to
the proposed pointwise Green construction, not a negative TT current.
The all-rank sign remains unproved. Exact positive survivor, paper proof
and audit record: `../5-failed/tt-gaussian-scale-pointwise-green.md`.

The retained all-pair equation strengthens the single-atom starting point.
For K_(p,s)(r,t)=exp[-exp(r)*(p*exp(2*t)+s*exp(-2*t))],

    -partial_t^2 K = -4*partial_r^2 K+16*p*s*exp(2*r)*K.

For the actual p=scale(n,x), s=scale(m,x), the atom pair equals
4*p*s*exp(x)*[(4*p*s+9)*K(0,t)+6*partial_r K(0,t)]. Both indices
and the scale derivative are kept. Next construction must work with
these differing potentials and the complete physical weight remainder;
an unweighted positive operator alone does not sign the source pairing.
