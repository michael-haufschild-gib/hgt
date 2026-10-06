# TT — Complete sixth surplus coefficient: source orientation

- Stage: coefficient obstruction and positive absorbed survivor formalized; full-value research in progress.
- Parent: `tt-surplus-top-coefficient.md` and `tt-third-slope-nonlinear-cone.md`.
- Target: determine the sign of full Q6, not a truncated native expression.
- Constraint: all mathematics hand-derived from the current native source field;
  no sampling, external coefficient arithmetic, added source hypotheses or axioms.

## Current finding

Actual-source Q6 is eventually strictly negative, now kernel-audited in
ThetaCuspRatioTerminalActualCoefficient. Eighth-to-seventh absorption leaves
this coefficient unchanged for every mass, so the proposed ordinary
nonnegative-coefficient certificate fails on the actual source itself.
This is NOT a counterexample to the full surplus value, third slope, or RH.
The stronger positive survivor for the same absorption and all52 imported
capstones passed. Certificate retired with its exact positive survivor in
`../5-failed/tt-ordinary-absorbed-surplus-coefficients.md`. Historical
paper/draft checkpoints below are superseded by this current finding.

## Exact all-order terminal source

Set U=3, Y=3K+1, T=J-Y-1. Direct substitution into the complete source field gives

    L/12 = δ = Y*(Y+T+1)*∂Y + T*∂T,
    integerStep/12 = δ + 5/4-Y,
    seed = 2Y-3.

Let P_n be the pulled-back native integerJet n divided by 12^n. Define B_n^a(T)
by B_0^a=1 and B_(n+1)^a=T*(B_n^a)' + (T+a)*B_n^a. The exact identity is

    T*P_n = 2Y*T*B_n^(9/4) + 3Y*B_n^(5/4)
      - 3*(T+Y)*(5/4)^n.

No division by T is required. Proof: multiplication by T conjugates the jet
operator to δ+1/4-Y. This operator acts on Y*T*f(T), Y*f(T), and T+Y as

    Y*T*[T*f'+(T+9/4)f],
    Y*[T*f'+(T+5/4)f],
    (5/4)*(T+Y),

respectively. The initial identity is T*(2Y-3). Thus induction identifies every
literal native jet on this plane, including its complete constant seed.

The same recurrence gives the formal generating function

    f(s)=exp(5s/4)*[Y*(2exp(s)+3/T)*exp(T*(exp(s)-1))
      -3*(1+Y/T)].

This is only a convenient derivation of the next polynomial identity; the
cleared recurrence above is the intended source formalization.

## Complete reflected moments and principal determinant

Let R_n be integerReflection n on this plane divided by 12^n. For even n>0,
let B_n=B_n^0, and G_n be the nth formal derivative at zero of
exp(2T*(cosh(s)-1)). Multiplication of the ENTIRE source function gives

    T² R_n = Y²*((2T+3)²*G_n+6T*G_n')
      -6Y*(T+Y)*(2B_(n+1)+3B_n).

The top two coefficients of B_n are 1 and n(n-1)/2. G_n has degree n/2 and
leading coefficient (n-1)!!*2^(n/2). Consequently the degree n+1 and n
homogeneous parts of the ACTUAL R_n are

    R_n[top] = -12Y*(T+Y)*T^(n-1) + 1_(n=2)*8Y²*T,
    R_n[next] = -6Y*(T+Y)*T^(n-2)*(n(n+1)+3)
      +1_(n=2)*24Y² +1_(n=4)*48Y²*T².

Both exceptional reflections are retained. Lower terms have total degree at
most n-1. This is needed only for n=2,4,6,8,10; it can also be checked against
the finite source recurrence without any analytic generating function.

Put A=-12Y*(T+Y)*T and B=8Y²*T. After extracting T^(2i) and T^(2j) from the
three-by-three moment matrix, the leading matrix is A*ones+B*E00. It has rank
two, with kernel (0,1,-1). Its adjugate is A*B times the outer product of that
kernel. The next reflected coefficient has index polynomial

    q(r)=(2r+2)(2r+3)+3=4r²+10r+9.

Thus its kernel pairing is A/(2T)*(q(2)+q(4)-2q(3))=4A/T. The exceptional
next terms occur only at r=0,1 and do not enter this pairing. Restoring the row
and column factors gives the determinant's degree20 part

    4*A²*B*T^11 = 4608Y⁴*(T+Y)²*T^14.

The signed third minor is the negative determinant. With κ=12^18,

    M20 = -4608κ Y⁴*(T+Y)²*T^14.

The full determinant has degree at most20: degree21 vanishes by the rank-two
leading matrix. The full source slope has degree at most22. Its degree22 part
comes only from 24Y²*(T+Y)*∂Y M20-144Y*(T+Y)*M20, namely

    S22 = 221184κ Y⁵*(T+Y)²*T^15.

Returning to the ORIGINAL J (T=J-Y-1), the principal factor is therefore

    S22(Y,J)=221184κ Y⁵*J²*(J-Y)^15.

Independent hand checks: J^17, J^16 and J^15 coefficients are respectively
221184κY⁵, -3317760κY⁶, 23224320κY⁷, matching the three complete native heads
already present in the C78 corpus at U=3. This is not a Lean audit.

## Independent source proof of the two reflected heads

This is a second hand derivation of the actual native principal terms. It
uses the literal terminal recurrence and finite binomial cancellation; no
formal exponential identity is needed for these two heads. Lean audit pending.

Write a=5/4. The COMPLETE terminal jets have the exact affine form

    P_n(Y,T)=Y*A_n(T)-3*a^n,
    A_0=2,
    A_(n+1)=T*A_n' +(T+9/4)*A_n+3*a^n.

This follows by substituting the affine form into the audited terminal step:
the Y² terms cancel, including the full constant seed. A_n has degree n and
leading coefficient2. For n>=1 its next coefficient is

    c_n=n²+(7/2)*n+3.

For n>=2 its third coefficient is

    d_n=6*choose(n,4)+(31/2)*choose(n,3)
      +(105/8)*choose(n,2)+(15/4)*n.

The scalar recurrences are
`c_(n+1)-c_n=2n+9/2` and `d_(n+1)-d_n=(n+5/4)*c_n`.
The initial constant forcing supplies the endpoint values, so these formulas
retain the seed rather than silently applying a high-degree recurrence at zero.
The polynomial continuations c_0=3 and d_1=15/4 are NOT actual coefficients:
A_0=2 and A_1=2T+15/2 must be retained separately. Also d_0=0.

For even n>0, define

    H_n=sum_i (-1)^i*choose(n,i)*A_i*A_(n-i),
    K_n=sum_i (-1)^i*choose(n,i)*A_i*a^(n-i).

The entire reflected source is exactly

    R_n=Y²*H_n-6Y*K_n.

The constant term vanishes by the binomial identity. K_n has top terms
`2T^n+q_n*T^(n-1)`, with `q_n=n(n+1)+3`; specifically
`c_n-2*a*n=q_n`.

H_n has degree at most n-1 because its degree-n coefficient is the
alternating binomial sum of the constant4. Its next coefficient is

    [T^(n-1)]H_n = -12+8*1_(n=2).

Indeed it is four times the alternating binomial sum of c_i, omitting i=0.
The full quadratic sum vanishes for n>2, while its n=2 difference is2;
omitting c_0=3 supplies the -12.

For the next coefficient the full expression is

    4*sum_i (-1)^i*choose(n,i)*d_i
      +sum_i (-1)^i*choose(n,i)*c_i*c_(n-i)
      +15*n-6*c_n.

The correction15*n restores the missing d_1, and -6*c_n removes both
spurious c_0 endpoint products. The two full sums are fourth-degree
polynomial differences. They vanish for even n>=6. At n=4 their total is
24+24=48; at n=2 it is105/2-57/2=24. Thus

    [T^(n-2)]H_n=-6*q_n+24*1_(n=2)+48*1_(n=4).

These identities recover exactly the two homogeneous reflected rows above,
including both exceptional moments. Lower terms have total degree at most
n-1. Together with the audited rank-two determinant pairing, they isolate
the remaining native principal-component proof into three explicit obligations:
affine jet incidence, the first three A_n coefficients, and polynomial
binomial cancellation. No extra positivity premise or unproved asymptotic
substitution is used in this alternative derivation.

## Consequence for full Q6 and its velocity derivative

At V=9 the reduced source is p(z)=S(3,K,3z)/3. At the flat mass,
aFlat=(Y-4)/27, b=(7-Y)/9. Insert the six ENTIRE coefficient heads into the
exact Q6 formula. Its Y-degree is at most10 at fixed bounded z. Terms involving
aFlat or z have lower Y-degree; the top weights are 1,6b,21b²,56b³,126b⁴,252b⁵.
Every resulting top contribution is negative. Keeping the positive sum explicit,

    [Y^10] Q6(9,(Y-1)/3,z,aFlat)
      = -73728κ*[3003+2*1365+(7/3)*455+(56/27)*105
        +(14/9)*15+28/27]
      = -(8192/3)*189994*κ < 0.

The velocity derivative has degree at most9, with positive leading coefficient

    [Y^9] ∂z Q6 = 221184κ*[1365+(7/3)*455+(28/9)*105
      +(28/9)*15+70/27]
      = 8192*75670*κ > 0.

Therefore the proposed velocity sign can hold in the tail while the full
flat-mass value is negative. Monotonicity alone cannot establish its positivity.

## Positive survivor: the complete principal value in a different basis

The obstruction has a positive replacement. Normalize w=-9z/Y and e=36E/Y².
At principal order the quadratic relation is w²=w-e/4 and the reduced source
is -8192κY²²*w²*(1+w/3)^15. Let w±=(1±d)/2, d²=1-e. Its constant affine
component is the positive divided difference

    8192κY²²*(e/4)*[f(w+)-f(w-)]/(w+-w-),
    f(w)=w*(1+w/3)^15.

Clearing d removes the apparent diagonal singularity. The exact odd-part
identity gives this component as

    (2048κY²²/6^15)*e*P(1-e),
    P(x)=sum_(j=0)^7 c_j*x^j,
    c_j=choose(15,2j+1)*7^(14-2j)+choose(15,2j)*7^(15-2j) > 0.

It is strictly positive on 0<e≤1, including the double-root endpoint. Its
ordinary sixth coefficient is nevertheless -54718272 times the positive
prefactor. As an independent hand check, c5=53748786, c6=161210, c7=106 and
c5+6c6+21c7=54718272; the conversion back to E reproduces the full negative
Q6 principal coefficient above. No numerical sampling is involved.

This suggests testing the full source after extracting its constant term and
expanding the remaining quotient in the deficit Emax-E:

    Q(E)=Q(0)+E*R(Emax-E).

The principal model has positive coefficients in this basis. That fact is NOT
a sign theorem for the complete source: Q(0), the entire R, its physical-domain
incidence and every lower homogeneous source term must still be retained and
proved. The former all-nonnegative ordinary-power certificate and this proposed
replacement are mathematically different claims.

## Source handoff and next required audits

The existing complete-source flatness theorems give all-order decay of
9-u² and 1-3J/u against powers of k. Actual a-aFlat is a polynomial multiple
of 9-u². Since Q6 is a fixed polynomial source observable, its normalized
actual value has the same leading coefficient as the U=3, z=1/3, flat-mass
specialization. Hence the paper prediction is eventual actual Q6<0.
Use normalization by `(3*k+1)^10`; normalization by `k^10` instead changes
the limiting coefficient by the factor3^10. This last polynomial/normalization
incidence must be formalized explicitly;
do not cite compact-coordinate flatness without clearing the coordinate change.

Positive survivor: the all-order exact terminal jet formula, complete reflected
moment law, principal minor/slope factorization, and opposite asymptotic signs
of Q6 and its velocity derivative. Formalize these exact source statements and
the eventual actual sign before moving a no-go card to failed/retired.

Next viable target remains positivity of the FULL absorbed surplus value on
the physical interval. Negative ordinary power coefficients do not decide that
question. Any replacement must retain Q6 and the other complete coefficients,
not add their nonnegativity as premises. No value certificate is asserted here.

## Validation

Paper derivation from current production integerField/integerStep/
integerReflection/integerThirdMinor/integerThirdSlope and C78 coefficient laws.
C77 cell227 finished; the global boundary core and physical-source boundary sign
both passed, with standard axioms. Production promotion of its 627-module
dependency closure is staged and still requires serial audits.

Source98 passed scratch audit5: complete field pullback, all-order native
scaling and cleared Bell-jet identity, all four capstones standard3. Promoted
`ThetaCuspRatioTerminalKineticJets.lean` passed its direct production audit.
Source99's determinant response, principal derivative, positive deficit basis
and negative sixth coefficient passed scratch audit1; its evaluation lemma
was repaired. Promoted `ThetaCuspRatioTerminalPrincipalAlgebra.lean` then passed
its direct audit. All three terminal leaves are wired into RHTower. The imported axiom audit
passed for all11 capstones, using only propext, Classical.choice, Quot.sound. No raised limits or extra mathematical axioms.

The principal polynomials have NOT yet been identified with actual homogeneous
source components. That identification and actual-tail transfer remain required.
Source100 passed scratch audit2 and its production audit as
`ThetaCuspRatioTerminalReflections.lean`. Its exact all-order native reflection
scaling and cleared Cauchy identity retain every reflected pair; this is not
yet the explicit central-moment law.


### Current formal handoff

Prepared `/tmp/TTC78TerminalAffineJets.lean` (uncompiled) gives the exact
all-order affine-Y native jet identity, retaining the complete constant seed
and the T=0 plane. The next formal steps are the coefficient recurrence above,
then the two reflected heads and native homogeneous minor/slope identities.
The corpus supplies the required alternating-power sum zero/factorial laws
in `HTGeometry/MicroSpectrumMomentCollapse.lean`; source bodies inspected.
No external coefficient calculation or numerical sampling was used.

Update: the affine identity passed scratch audit3 and its renamed direct
production audit as `ThetaCuspRatioTerminalAffineJets.lean`. The complete
univariate realization, coefficient recurrence, degree bound, and first
three coefficients at EVERY order passed scratch audit2; the renamed
`ThetaCuspRatioTerminalAmplitudePolynomial.lean` production audit passed
without warnings. Nine scratch capstones use only standard3. Both modules
are wired. No principal native determinant identity is claimed yet.

The complete product extraction now passes scratch audit4 in
`TTC78TerminalAmplitudeReverse`: the first three coefficients of EVERY
product A_i*A_j retain both low-order corrections. `TTC78TerminalReflectedLeading`
passes scratch audit2: [T^n]H_n=0 for n>0 and [T^(n-1)]H_n=-12 for even
n>2. `TTC78TerminalReflectedSecond` passes scratch audit3: the EXACT next
coefficient is `-6*(n*(n+1)+3)+24*1_(n=2)+48*1_(n=4)` for every even n≥2.
All nine audited capstones use only standard3; no raised limits. Renamed
production leaves for these three modules are staged; their direct audits
and umbrella wiring remain pending. `TTC78TerminalReflectedAffine` is now
auditing the full native identity `R_n=Y²*H_n-6Y*K_n`, not a truncation.
Update: its scratch audit2 passed; both native capstones use standard3.
The full affine reflected identity is now kernel-checked for EVERY positive
even order. Source108 `TTC78TerminalCrossHeads` is auditing the two remaining
cross coefficients and the complete degree bounds/exceptional H_2 head.

### Remaining native grading step (explicit source construction)

Next prove the cross-polynomial K_n has degree n, leading coefficient2,
and next coefficient `q_n=n*(n+1)+3`. Only i=n and i=n-1 survive in its
defining binomial sum; the exact next coefficient is `c_n-2*(5/4)*n=q_n`.
Also finish the exceptional H_2 next coefficient -4. The already audited
H coefficients then give every complete reflected top/next row on paper.

For formal grading without uncontrolled full-source expansion, use an
auxiliary polynomial clock H. For a polynomial P(T), define its degree-d
homogenization by reversing to degree d after substituting T*X. Then

    Rstar_n(H;Y,T)=Y²*hom_(n-1)(H_n)-6Y*hom_n(K_n)
      = H^(n+1)*R_n(Y/H,T/H)

at nonzero H. Its constant and linear coefficients are exactly the two
reflected homogeneous rows. The signed three-by-three Hankel determinant
of Rstar_2,...,Rstar_10 equals H^21 times the entire native minor (with its
known 12^18 factor). Its constant coefficient vanishes by the audited
rank-two row, and its linear coefficient is the audited determinant
pairing. This identifies the degree20 minor while controlling every lower
term. The exact terminal source field then gives the degree22 slope.
Polynomial homogenization/identity and source grading still need Lean;
these are concrete next proof obligations, not extra source assumptions.


### Exact original-coordinate flat transfer (paper proof, draft102)

The corpus supplies `sourcePolynomial_regularization`: for any full source
polynomial P there are m,Q with
`h^m*P(sourcePoint(h,r,t))=Q(h,r,t)` whenever h is nonzero. Apply it at the
actual compact coordinates and at r=t=0. At h=1/k the corresponding source
points are exactly `(u²,k,J/u)` and `(9,k,1/3)`.

Subtract the two identities. For each n,

    k^n*(P(actualSquarePoint)-P(9,k,1/3))
      = k^(n+m)*(Q(actualBase)-Q(axisBase)).

The right side tends to zero by the production theorem
`actual_axis_polynomial_flat Q (n+m)`. This proves all-order flatness for
EVERY polynomial observable in the original, unbounded source coordinates;
no boundedness assertion about k and no extra source premise is needed.
Draft `/tmp/TTC78TerminalFlatTransfer.lean` formalizes this exact argument,
UNCOMPILED while the serial boundary production audit is active. It imports
production only. The full Q6 polynomial must still be identified explicitly,
and its terminal leading coefficient must still be proved, before this
transfer gives actual-tail negativity.

## Deficit basis: exact mass transport (new paper result)

Keep the complete literal source polynomial and the quadratic normal form
`z²=a+b*z-E/9`. Put `M=9*(a+b²/4)` and `D=M-E`. There is a polynomial F,
independent of a, such that `Q_a(E)=F(a-E/9)`. Consequently

    G(D)=Q_a(M-D)=F(-b²/4+D/9)

is independent of a. Define the polynomial divided difference R_M by

    G(D)-G(M)=(M-D)*R_M(D).

Then `Q_a(E)=Q_a(0)+E*R_M(M-E)`, exactly, with every source term retained.
For `M=M0+δ`, polynomial subtraction gives the all-order transport identity

    R_M(D)=R_M0(D)+δ*secant(R_M0;M,D),
    (M-D)*secant(f;M,D)=f(M)-f(D).

The secant of a polynomial with nonnegative coefficients has nonnegative
coefficients in D whenever M≥0: each monomial contributes
`sum_(i<n) M^(n-1-i)*D^i`. Hence all coefficient signs of the COMPLETE R_M
reduce to their zero-mass values `M0=9*b²/4`, whenever a≥0. This is a
structural reduction, not an assumed positivity theorem for the actual R.
Its zero-mass coefficients and the full value cancellation remain open.

### First two complete replacement coefficients (paper, not kernel-audited)

If q_j are the ordinary coefficients of the full degree-eight Q, then

    [D^7]R=-q8,
    [D^6]R=q7+7*M*q8.

The first is positive by the complete-source q8 sign argument. Writing
c=-1/9, the second is exactly

    c^7*[p14+(z+7b)*p15+(a+8bz+105b²/4)*p16
      +((a+137b²/4)*z+8ab+70b³)*p17].

Here p14,...,p17 are the ENTIRE native source coefficients, including their
lower homogeneous terms. Its a-derivative is `-9*q8>0`. Its z-derivative is
c^7 times `p15+8b*p16+(a+137b²/4)*p17`; the latter is positive on the same
source domain. Relative to the earlier absorbed seventh-coefficient proof,
its last velocity factor changes from H2 to `H2-(3/2)b²*C17`.
With Y=3k+1, x=Y-4≥0, C17=24576Y²(Y+3), and b=(7-Y)/9, use
`(Y-7)²≤Y²`. The exact lower polynomial for 27 times this new factor is

    9797632x^5+171689472x^4+1151144448x^3
      +3770128000x²+5841541632x+2809712256 > 0.

At a=0,z=1/3 the neutral source factors are N0 (unchanged),
`N1new=N1old-(3/2)b²*D0`, and
`N2new=N2old-(3/2)b²*Bupper`. The old exact negative-factor certificates are
in TTC78KineticMinorThirteenMiddle/Last and the complete source incidence in
TTC78SurplusResidualNeutralFace. No native coefficients are discarded.
For N1 the additional positive polynomial to subtract from -3N1old is at
most `Y²*(4096Y^4+36352Y³+81408Y²+11520Y+8640)`; its x-coefficients are
4096,134656,1791488,12373248,46955968,93158912,75717632 (descending).
Each is strictly smaller than its old certificate coefficient.
For N2 the subtraction from -243N2old is at most
`Y²*(614400Y^4+164352Y³+3877632Y)`; its x-coefficients are
614400,14909952,150743040,816605952,2511012864,4171370496,2933047296.
Again each is strictly smaller than the corresponding old certificate.
Thus the neutral factor is negative; multiplication by c^7 makes the full
replacement coefficient positive. Mass monotonicity and velocity
antitonicity extend this to the physical domain. All displayed arithmetic
is hand-derived and still needs exact Lean verification.

The next coefficient is `-(q6+6*M*q7+21*M²*q8)`. At zero mass this equals
-c^6 times

    p12+(z+6b)*p13+((39/2)b²+7bz)*p14
      +((91/2)b³+(53/2)b²z)*p15
      +((1365/16)b^4+72b³z)*p16
      +((273/2)b^5+(2517/16)b^4z)*p17.

Its complete-source sign is OPEN. The lower R coefficients and Q(0) are
also OPEN. In particular positive R coefficients alone do not settle the
original value; a potentially negative Q(0) must be retained.

### Constant term: a new cancellation obstruction (paper proof)

The stronger proposal `Q(0)≥0` throughout the nonlinear cone is false on
paper. This is a separate obstruction from the negative ordinary Q6 and
does not refute the deficit-basis coefficient signs or the full source value.
Its source-normal-form incidence and limit still require a Lean audit.

Use the EXACT polynomial boundary parametrization from the audited corpus:
`b(h)=1/12-7h/72`, `r(h)=1-h²*b(h)`, `t_boundary=b(h)`. Move strictly inward
by setting `t=b(h)+d`, for fixed `0<d<1/12`, and
`z=(1-h*t)/3=nonlinearBoundaryZ(h,1)-h*d/3`. Then

    E=t-h²t²-r*b=d-h²*(2*b*d+d²)>0

for all sufficiently small positive h. The strict coarse-cone forcing tends
to `1/2-6d>0`; all other strict cone conditions follow from the same
parametrization and their strict limiting margins (z<1/3 follows from t>0).
The entire source value is positive on this family by the existing uniform
nonlinear-cone tail theorem.

Let `m=6^24*24^9`. The actual affine remainder at E=0 has the exact scaling

    h^22*Q(0)/m=A75(h,r)+h*z*B75(h,r).

The audited boundary regularization gives
`A75(h,r(h))+h*nonlinearBoundaryZ(h,1)*B75(h,r(h))=h^6*G(h,1)`.
Subtract the inward displacement, without a root approximation:

    h^20*Q(0)/m=h^4*G(h,1)-(d/3)*B75(h,r(h)).

The right side tends to `-(d/3)*(268435456/2187)<0`, since the complete
polynomial B75 has that positive constant value. Thus Q(0) is eventually
strictly negative INSIDE the nonlinear cone, while the full source is
positive. The positive survivor is the exact cancellation law above and the
complete-source compensation: the negative order-h^-20 constant term must
cancel the order-h^-20 surplus contribution, leaving the positive order-h^-19
full value. The already audited scaled-source limit is
`Qcompact(0,1,1/12+d)=7776*principalMass*d>0`.

Consequence for the next conjecture: prove the compensated VALUE, retaining
both Q(0) and E*R. Separate nonnegativity of these two terms cannot be the
full-cone certificate. This is not an effort-driven change of target and is
not a retirement: the exact source obstruction and positive cancellation
survivor remain queued for formalization.

### Audit scheduling checkpoint

The renamed boundary production audit passed indices0..31 (32/627), then
ProductValues8 (index32) was deliberately interrupted, exit130, to release
the sole foreground Lean slot for new frontier proofs. Cell1036 is terminal.
This is an audit checkpoint, not a mathematical failure or a goal pause.
Resume from index32 using `/tmp/tt_c77_production_manifest.json` and the
journal `/tmp/tt_c77_production_audits/status.jsonl`. Original scratch closure
remains audited. Affine-jet draft101 is now under its first direct Lean audit.

### Native determinant identified; differentiated source next

Scratch110 pass3 is terminal0. All four capstones use standard3. The exact
polynomial N(Y,T;h) satisfies N(h)=h^21 M(Y/h,T/h), N_0=0 and
N_1=-4608*12^18 Y^4(T+Y)^2T^14 for M=pull(integerThirdMinor).
Both reflected heads and native determinant incidence are now proved.
Production109 is under direct audit; production110 is staged/wired.

Next dependency-closed paper step: differentiate the full affine reflected
source R_n=Y²H_n(T)-6Y K_n(T). Define inverse-clock polynomials for R_Y
and R_T with scale h^n. Their determinant first variations give
N_Y=h^20 M_Y and N_T=h^20 M_T. The constant coefficients vanish because
the leading determinant vanishes identically. The linear coefficient of N_Y
is the exact Y derivative of N_1. With the complete kinetic field retained,

    h^23 S(Y/h,T/h) =12*((2Y-3h)*
      (Y*(Y+T+h)*N_Y+h*T*N_T)-12*Y*(Y+T+h)*N).

Its constant coefficient vanishes; its linear coefficient is precisely
221184*12^18 Y^5(T+Y)^2 T^15. This is the next source theorem, not an
assumed leading-term identification. It remains paper until audited.
Search generation1251122 had66693 inventoried/indexed files, partial search
and many pending compiler records. No applicable complete slope incidence
was returned. Generic homogenization/derivation ingredients were inspected.

Derivative bridge scratch111/112 passed (passes2/3 respectively), with
seven/five printed capstones using standard3 and no warnings. Complete
coordinate-derivative scaling identities retain all source terms. Exact
N_Y,0=N_T,0=0 and N_Y,1=-9216*12^18 Y³(T+Y)(2T+3Y)T^14
are audited. Mixed first-variation symmetry reduces the coefficient proof
to the previous rank-two pairing, with default Lean limits. Production
111/112 are staged/wired; their direct audits remain pending.
Scratch113 now audits the complete slope regularization and its leading
coefficient; it does not assume a homogeneous-source incidence.

The full-value curvature search (generation1251416,66698 indexed files,
partial with compiler records pending) returned the existing cubic normal
form and plane derivative, not global kinetic concavity. A concavity-based
full-value proof would also require positivity on the complete F=0 lower
physical endpoint, not just the already proved J=F=0 corner. Neither new
sign is claimed or used as a premise.

### Principal normal-form survivor: exact quadratic derivation (paper)

The native slope bridge also exposes the precise link to the already
audited positive principal model. Set h=1/Y, W=h*J_native, e=E/Y².
At h=0 the complete native degree22 source is
221184*kappa*W²*(W-1)^15, kappa=12^18. The square-chart reduced source
is one third of the native source at U=3 (integerSlope_shear_factor),
so its principal coefficient is73728*kappa. The scaled quadratic law is
W²=-W/3-e; its normal-form evaluation point 3*z*h tends to0.

For ANY e, the exact constant remainder of W²*(W-1)^15 modulo
W²+W/3+e is

    e/6^15 * deficitShape(1-36e).

Hand proof retaining both conjugate branches: Wbar=-1/3-W, D=6W+1,
D²=1-36e, W*Wbar=e. For F=W²*(W-1)^15 and its conjugate Fbar,
(W-Wbar)*re(F)=W*Fbar-Wbar*F. The right side equals
e*(Wbar*(Wbar-1)^15-W*(W-1)^15)
=e*2D*deficitShape(D²)/6^16 by the audited principal_odd_part identity.
Since W-Wbar=D/3, compare the coefficient of W on both sides to cancel
the factor2; no division by D or exclusion of the double-root value.

Consequently the source principal surplus polynomial is
(73728*kappa/6^15)*e*deficitShape(1-36e). Its sixth coefficient is
(256/27)*kappa*(-54718272)=-(8192/3)*189994*kappa. It is strictly
positive for0<e≤1/36 by the existing principalSurplusShape positivity.
This derives BOTH the negative ordinary coefficient and its positive
value survivor from the same complete principal source. Formal quadratic
identity, graded coefficient transport, and actual-tail transfer remain
required; no actual Q6 sign is claimed yet. No external arithmetic/CAS
was used.

The exact quadratic-remainder identity and its positive-value/negative-sixth
coefficient survivor PASSED scratch114 audit4, no warnings. All five printed
capstones use subsets of standard3 (the generic conjugate-selection identity
uses only propext/Quot.sound). Production TerminalQuadraticPrincipal is
staged/wired; direct audit remains. Original-coordinate flat transfer102 is
now under its first audit. No actual Q6 sign or full interior sign follows
before the graded source-coefficient transport is checked.

Next exact transport mechanism: set h=1/Y, W=h*J_native. The complete
regularized source is R(h;1,W-1-h); its h=0 value is
221184*kappa*W²*(W-1)^15. For flat mass, the scaled quadratic parameters
are a_h=(h-4h²)/3, b_h=(7h-1)/3 and the normal-form reading is W=3zh.
All are polynomial in h. Build the finite polynomial family from the
audited complete homogenized H/K rows and their derivatives, divide its
forced clock factor, then apply the exact quadratic reduction. Coefficient
continuity at h=0 now gives the displayed sixth leading coefficient;
all lower native terms remain in the family. This avoids assuming a
kinetic degree17 bound or relying on the older97 unaudited drafts. Exact
reduced-source /3 incidence and this family transport remain to formalize.

The /3 normalization bridge is itself an exact paper identity for every
complex Y,T: reducedSlope(9,(Y-1)/3,(T+Y+1)/3)
=eval_terminal(Y,T)(pull integerThirdSlope)/3. Apply the production
integerSlope_shear_factor at U=3, then the exact shear/square evaluations
and terminal pullback. It has no positivity, nonzero drift or source
premise. Combined with slopeRegularized_eval it gives a finite polynomial
regularization of the literal reduced source. This is the next small
incidence proof needed before graded quadratic coefficient transport.

Finite-family implementation refinement (not yet code/proof): work in
Polynomial(Polynomial ℂ), outer variable clock h, inner variable terminal T.
Lift the exact homogenized H/K rows by mapping their complex coefficients
into the inner ring; coefficientwise map/reflect and map/divX identities
transport the already-audited scalar theorems. Extract the clock factor
before substituting T=W-1-h. At h=0 this substitution is T=W-1, so the
regularized slope constant is exactly221184*kappa*W²(W-1)^15.
Quadratic base-change can be defined explicitly by mapping the re/im
coordinates, with a,b mapped too; its ring laws follow from the actual
QuadraticAlgebra multiplication. Apply it to the h=0 specialization to
transport the complete quadratic remainder and coefficient6. No
discriminant inverse, degree17 assumption, or finite-source truncation is
needed. Lexical map_reflect search returned no applicable polynomial
lemma; direct checks of Polynomial Reverse/Inductions and QuadraticAlgebra
Basic/Defs found no map_reflect/map_divX/base-change definition. Build the
needed identities coefficientwise rather than assume remembered APIs.

### Complete finite family and quadratic base change: audited progress

Scratch116 pass3 and production TerminalGradedFamily passed, warning-free.
It explicitly retains every reflected row and both coordinate derivatives
over C[T][h]. Specialization in T recovers the complete scalar source
regularization, and the h0 coefficient is221184*12^18*(T+1)^2*T^15.
Scratch117 quadraticChange passed with only propext/Quot.sound; production
is auditing. The homomorphism maps both normal-form coordinates and both
quadratic parameters, hence commutes with arbitrary polynomial operations.

Next118 uses this on W²=(h-4h²)/3-e+(7h-1)W/3 and T=W-1-h. The full
normal-form reading is re+3zh*im; its h0 specialization forgets the velocity
reading because its multiplier contains h, not because terms are discarded.
It should equal3 times the audited reduced principal polynomial. This
would close finite-family coefficient transport at the exceptional fiber.
The remaining exact bridge to unscaled Q6 is E=e/h², source factorh22:
[h0][e6] corresponds to the leadingY10 coefficient of ordinaryQ6.

The full unscaled quadratic is z²=(k-1)/9+(2-k)z/3-E/9 atv9. For
h=1/(3k+1), W=3hz, multiplying by9h² gives the graded quadratic above.
Ring-hom transport z↦W/(3h), E↦e/h² proves the entire polynomial identity;
it requires h≠0 only for coordinate inversion, no source sign premise.
Do not import the older97 degree17 draft chain to assert this incidence.

### Lossless graded coefficient identity: dependency-closed paper mechanism

Write P_k(Z)=reducedSlope(9,k,Z), k=(1/h-1)/3, and let Q_k,z(E) be
its exact affine quadratic remainder read at z under
Z²=(k-1)/9+(2-k)Z/3-E/9. No degree bound on P_k is required.
Let G_z(h,e) be one third of the entire graded remainder, read at3zh.
Then for every nonzero complex h,

    G_z(h,e) = h^22 Q_k,z(e/h²).

Proof: the complete source regularization gives a polynomial identity in W,
R(h,1,W-1-h)/3=h^22 P_k(W/(3h)); polynomial extensionality follows from
the existing scalar identity for every complex W. Apply the ring hom into
the graded quadratic W²=(h-4h²)/3-e+(7h-1)W/3. The map from the original
quadratic sends coefficients by E↦e/h² and generator Z↦W/(3h).
Its defining relation holds because c²a'=a-E/(9h²), cb'=b for c=1/(3h).
Read re+3zh im; the generator factor cancels, yielding re+z im on the
original side. Therefore

    [e^6]G_z(h,e) = h^10 [E^6]Q_k,z(E).

The left side is a POLYNOMIAL in h, not an asymptotic truncation. At h0 its
value is the exact negative sixth coefficient of the principal polynomial.
This gives the flat-terminal Q6 asymptotic without the older degree17
proof chain. To transfer to the actual source, realize [E6]Q as a fixed
source polynomial in(v,k,z) by doing quadratic reduction over Poly[E]
with a=(k-1-k(6k-7)(9-v)/72)/9 and b=(2-k)/3; its coefficients are
polynomials. Then apply actual_terminal_polynomial_flat to that exact
source coefficient. Both final incidence constructions remain to audit.

### Positive survivor after the same eighth-coefficient absorption (paper)

The actual no-go should cover the proposed absorbed polynomial, not merely
unabsorbed Q. Absorb(P,M)=P-q8*E8+q8*M*E7 leaves q6 unchanged for EVERY M.
The principal absorbed model itself still has a positive mixed E/deficit
certificate. Put t=36e, D=1-t, d_j=deficitCoeff j, and
p(t)=t*sum_(j=0..7) d_j D^j. Its top coefficient is -d7. Absorb at M=1:

  Absorb(p,1)/t = d0+(d1-d7)*D+sum_(j=2..7) d_j*D^j
                   +d7*D²*sum_(i=0..5) t^i.

Exact identity follows from 1-t6=D*(1+t+...+t5). All terms are nonnegative
on0<=t<=1, with d0>0 and d1>=d7 (direct defining binomial integers).
Thus the absorbed principal model remains strictly positive on0<t<=1,
although its sixth ordinary coefficient is negative. Rescaling t=36e
and multiplying by73728*12^18/(36*6^15) gives the SAME conclusion for
Absorb(principalReducedSurplusPolynomial,1/36). This is a stronger positive
survivor of the exact absorbed-certificate obstruction. PAPER ONLY so far;
formalize after actual-source transfer126, without claiming full interior
source positivity. The mixed basis suggests preserving E/deficit coupling
when attacking the complete compensated value, rather than asserting all
ordinary coefficients nonnegative.

The flat-terminal maximum mass also scales polynomially and exactly:
9*(a+b²/4)=k²/4 atv9, so h²*M=(1-h)²/36 for k=(1/h-1)/3.
Thus the complete graded absorbed family uses mass(1-h)²/36; its h0
specialization is precisely Absorb(principalReducedSurplusPolynomial,1/36).
This links the proposed positive absorbed survivor to the actual graded
construction, rather than choosing an unrelated positive model.
