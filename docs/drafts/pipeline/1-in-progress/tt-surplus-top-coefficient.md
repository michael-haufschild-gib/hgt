# Complete-source test of the surplus power certificate

- **ID:** TT-C78-SURPLUS-HEAD
- **Route:** TT, full finite-clock third-slope positivity.
- **Stage:** In progress. Symbolic paper derivation below; source identities and sign still require independent algebra audit and Lean verification.
- **Parent:** `tt-third-slope-nonlinear-cone.md`.
- **Question:** Does canonical reduction in the nonlinear surplus have nonnegative affine coefficients throughout the physical kinetic interval? This is a proposed certificate for C78, not an assumed source property.
- **Constraints:** Complete source recurrence; retain exceptional first/second jets and second/fourth reflections. No sampling, external coefficient arithmetic, omitted remainder, second Lean process, or raised limits.

## Why this test is needed

The preceding displacement obstruction excludes all-nonnegative powers of downward kinetic displacement. It does not exclude a certificate in the nonlinear surplus. The latter uses a monic quadratic relation and has a different highest coefficient. Its sign requires the next full-source slope coefficient, not merely the already-derived degree-seventeen head.

## Derivation to audit

Write `u=U`, `Y=3K+1`, `j=J`, and `P_n=integerJet n`. The complete source field in these coordinates is

    L_source = 2(Y-1)(9-u²) partial_u + 12Y*j partial_Y
      + [6Y²-24Y-6 -(2/3)(Y-1)²*u² +4(Y+1)u*j] partial_j,
    P_(n+1)=L_source P_n+u(5-4Y)P_n.

The existing top-two derivation gives, for n>=1,

    [j^n]P_n=2*12^n*Y,
    [j^(n-1)]P_n=u*12^(n-1)*f_n,
    f_n=-8nY²+(4n²+6n+12)Y-15*delta_(n,1).

For n>=2, the proposed exact third coefficient is

    [j^(n-2)]P_n=12^(n-2)*(p_n+u²*q_n+(270-105u²)*delta_(n,2)),
    p_n=(-72n²+180n-108)Y²-(24n³+90n²+102n+54)Y,
    q_n=16n(n-1)Y³+(-16n³-44n+60)Y²
      +(4n⁴+4n³+11n²+17n+54)Y.

Here is a complete recurrence check to formalize. Away from the exceptional n=1 jet, the source equation gives

    p_(n+1)=Y partial_Y p_n+18(Y-1)f_n+144nY(Y²-4Y-1),
    q_(n+1)=Y partial_Y q_n+[(4n-10)Y+4n+3]f_n-16nY(Y-1)².

At n=2 the full initial constant coefficient is

    -36Y²-810Y+270+u²*(32Y³-156Y²+228Y-105).

The extra term `270-105u²` is killed by the kinetic commutator, whose only derivatives are in K and J. Consequently it does not propagate to the next third coefficient. Substitution of the displayed p_n,q_n verifies each polynomial recurrence without any source truncation. The exact native derivative proof can use

    f(n)=-8nY²+(4n²+6n+12)Y,
    L(n)=24nY*j+u*f(n),
    H(n)=144n(n-1)Y*j²+12(n-1)u*f(n)*j+p_n+u²*q_n,
    12*integerStep L(n)+kineticCommutator78 H(n)=12*H(n+1).

The existing full commutator identity then inducts on the literal jets. It yields

    partial_j^m P_(m+2)=m!*12^m*H(m+2)
      +(270-105u²)*delta_(m,0).

This identity, including the exceptional second jet, is the next formal target.

### Third reflected coefficient

Set `G_n=12^(2-n)*[j^(n-2)]integerReflection n`. For even n>=6, endpoint-corrected binomial cancellation gives the candidate

    G_n=432Y³+432(n²-5n+2)Y²
      +(144n³+1080n²+72n+324)Y
      +u²*[(-96n²+288n-240)Y³
        +(96n³-336n²+720n-864)Y²
        +(-24n⁴+96n³-336n²+408n-324)Y].

For n=4 add `768u²Y²`. For n=2 use the exact full expression

    G_2=-144Y³-3024Y²+5940Y-1620
      +u²*(-112Y³+400Y²-468Y+180).

The binomial audit must retain these terms explicitly. Extend the jet heads to indices zero and one by setting the missing coefficients to zero. The corrections to the polynomial p_n+u²q_n are

    e0=108Y²+54Y-u²*(60Y²+54Y),
    e1=270Y-90u²Y,
    e2=270-105u².

For even n>=6, the C*A plus A*C part contributes
`-6*(p_n+u²q_n)+4Y*(e0-n*e1+n(n-1)*e2/2)`.
The B*B endpoint correction is
`-24u²Y*f(n)+30n*u²*f(n-1)`.
The unrestricted polynomial binomial sum vanishes because its degree is four. At n=4 its leading coefficient contributes `768u²Y²`. The n=2 formula follows directly from `R_2=2P_0P_2-2P_1²`. These are exact coefficient arguments, not approximations to the full source value.

### Next minor and slope coefficients

For the normalized complete reversed reflections `Q_n`, write

    Q_n=-12Y+epsilon*F_n+epsilon²*T_n+...,
    T_n=G_n/144.

This notation is only for coefficient extraction. The already-prepared exact quadratic-plus-cubic determinant identity retains the entire remainder. Its next coefficient is

    -12Y*(F'11*T'22+T'11*F'22-2*F'12*T'12)+HankelCubic(F2,F4,F6,F8,F10).

Using `F'ab=(8/3)uY²-16uYab`, the cross term reduces to

    u*((8/3)Y²*S-16Y*W),
    S=T10-2T8+T6,
    W=T10-4T8+6T6-4T4+T2.

This reduction retains both exceptional reflections. The resulting candidate native coefficient is

    [j^15]integerThirdMinor=12^18*u*Y²*(A(Y)+u²*B(Y)),
    A(Y)=1536Y³+9792Y²+2160,
    B(Y)=(6656/3)Y³-(15296/3)Y²+8192Y-240.

Applying the complete source slope operator, together with the previous exact degree-sixteen minor head, gives the candidate

    [j^16]integerThirdSlope=12^18*u*Y²*(D0(Y)+u²*D1(Y)),
    D0(Y)=-73728Y⁴-654336Y³-1465344Y²-207360Y-155520,
    D1(Y)=-114688Y⁴-132096Y³+248832Y²-861696Y+17280.

Shear/square transfer should therefore give

    p16=[z^16]reducedSlope(v,k,z)=12^18*v^8*Y²*(D0(Y)+v*D1(Y)),
    p17=[z^17]reducedSlope(v,k,z)=24576*12^18*v^9*Y⁴*(Y+3).

All these next-coefficient formulas are unaudited. In particular they are not premises available to a Lean proof yet.

### Surplus coefficient and proposed obstruction

Let `a=boundaryA(v,k)`, `b=boundaryB(k)=(2-k)/3=(7-Y)/9`, and

    E=9*(a+b*z-z²).

This is the compact nonlinear surplus `t-h²*t²-r*b(h)` after the source substitution. Canonical reduction by `z²=b*z+a-E/9` expresses the complete polynomial uniquely as an affine expression in z with polynomial coefficients in E. Its highest E^8 coefficient is

    9^(-8)*(p16+(z+8b)*p17).

For 0<=z<=1/3 and Y>19/4, the proposed formulas make this strictly negative whenever v>0. Indeed D0 has all coefficients negative, and

    D1(Y)+24576Y²(Y+3)*(z+8b)
      <= -(409600/3)Y⁴-(109568/3)Y³+732160Y²-861696Y+17280
      = -(409600/3)Y²*(Y²-9)-(109568/3)Y³
        -496640Y²-861696*(Y-1)-844416 < 0.

If the coefficient audit succeeds, this refutes the all-nonnegative canonical surplus coefficient certificate. It does not refute full C78 positivity, permit removing the physical interval, or supply an RH counterexample. The strongest positive survivor must include the all-order third jet/reflection coefficients, both exceptional terms, and the exact next native minor/slope coefficient laws. Do not retire this candidate before those laws and the canonical reduction are Lean-audited.

## Validation and next actions

- [x] Literal source recurrence, existing top-two chain, quadratic definitions inspected.
- [x] Derive the third-jet coefficient recurrence with the exceptional second jet retained.
- [ ] Formalize and audit the full native third-head identity.
- [ ] Audit the reflected endpoint sums and both exceptional reflections.
- [ ] Audit the next minor and slope coefficients and square transfer.
- [ ] Formalize canonical quadratic reduction and decide the proposed coefficient sign.
- [ ] Extract/integrate the survivor before any no-go retirement.

The sole live Lean pipeline remains C77 cell227. Twenty-seven scratch sources are prepared after the original sixteen kinetic modules, in dependency order (the general response module imports only the original chain):

1. `/tmp/TTC78KineticThirdJetHead.lean`
2. `/tmp/TTC78KineticThirdReflectionHead.lean`
3. `/tmp/TTC78KineticThirdReflectionFive.lean`
4. `/tmp/TTC78KineticMinorNext.lean`
5. `/tmp/TTC78KineticMinorAffine.lean`
6. `/tmp/TTC78KineticSlopeNext.lean`
7. `/tmp/TTC78KineticSquareNext.lean`
8. `/tmp/TTC78SurplusPowerHeads.lean`
9. `/tmp/TTC78SurplusHeadSign.lean`
10. `/tmp/TTC78SurplusNormalHead.lean`
11. `/tmp/TTC78SurplusSource.lean`
12. `/tmp/TTC78SurplusSquareResidual.lean`
13. `/tmp/TTC78ShiftedKineticSource.lean`
14. `/tmp/TTC78KineticFourthJetHead.lean`
15. `/tmp/TTC78KineticFourthReflectionHead.lean`
16. `/tmp/TTC78KineticFourthReflectionFive.lean`
17. `/tmp/TTC78KineticMinorFourteen.lean`
18. `/tmp/TTC78KineticMinorQuadratic.lean`
19. `/tmp/TTC78KineticSlopeFifteen.lean`
20. `/tmp/TTC78KineticCoefficientTransfer.lean`
21. `/tmp/TTC78KineticMinorEvenParts.lean`
22. `/tmp/TTC78KineticSlopeFifteenEven.lean`
23. `/tmp/TTC78KineticCoefficientResponse.lean`
24. `/tmp/TTC78KineticFifthJetHead.lean`
25. `/tmp/TTC78KineticFifthReflectionHead.lean`
26. `/tmp/TTC78KineticMinorThirteen.lean`
27. `/tmp/TTC78KineticSlopeFourteen.lean`

All forty-three kinetic/surplus sources remain UNCOMPILED, with no axiom audits. The chain now also targets the complete minor coefficients fourteen/thirteen, native slope coefficients fifteen/fourteen and square transfer, the general coefficient response of the source operator, and the all-order fifth jet/reflection construction. No source-coordinate division is used. The generic even-reflection third/fourth-head closed formulas still need proofs beyond the five actual moments. No certificate is retired or promoted until direct serial `lake --old env lean` audits and survivor integration succeed.

### Exact quadratic power mechanism

For the free quadratic algebra over `C[E]` with `omega²=a+b*omega+c*E`, write `omega^n=A_n(E)+omega*B_n(E)`. Simultaneous induction gives

    deg A_(2m+1), deg B_(2m+1) <= m,
    [E^m]A_(2m+1)=m*b*c^m, [E^m]B_(2m+1)=c^m,
    deg A_(2m+2)<=m+1, deg B_(2m+2)<=m,
    [E^(m+1)]A_(2m+2)=c^(m+1), [E^m]B_(2m+2)=(m+1)*b*c^m.

The induction uses the complete recurrence `A_(n+1)=(a+cE)B_n`, `B_(n+1)=A_n+bB_n`. Therefore all source powers below sixteen contribute zero to `[E^8]`; the complete degree-seventeen polynomial gives exactly `c^8*(p16+(z+8b)*p17)`. The prepared source-evaluation ring hom sends `E` to `9*(a+bz-z²)` and `omega` to `z`, discharging the quadratic relation identically. The no-go target concerns this canonical polynomial, not positivity of its value at the physical surplus.

### Next conjecture: retain the compensating square

The negative eighth coefficient suggests a positive remainder, rather than a reason to abandon the interior problem. Put `Ebar=9*(a+b²/4)` and let `q8(z)` be the exact eighth coefficient above. Define

    P7(E)=P(E)-q8(z)*E^8+q8(z)*Ebar*E^7.

Then, identically on the quadratic source relation,

    P(E)=P7(E)+(-9*q8(z))*E^7*(z-b/2)^2,
    Ebar-E=9*(z-b/2)^2.

On the physical range, `E>0` and the proposed audited head law would give `q8(z)<0`, so the removed term is nonnegative. The new frontier conjecture is `P7(E)>=0` on the **full physical cone**, retaining both the speed and kinetic constraints. This is unproved; the negative head alone does not imply it. Its next source coefficient and the remaining full polynomial must be analyzed. A generic algebraic identity alone is not a proof of the conjecture. No numerical sampling or bound tuning is proposed.

This is also an exact source-degree descent: after substituting `E=9*(a+bz-z²)`, `P7` has kinetic degree at most fifteen. The compensating square removes both degree-seventeen and degree-sixteen source coefficients, with their correct values forced by `q8(z)=9^(-8)*(p16+(z+8b)*p17)`. Thus the negative canonical head can expose a positive square and a strictly smaller complete residual. Proving the residual sign, rather than only recording the negative certificate, is the proposed frontier attack. The residual's next head depends on native coefficients fifteen and fourteen; neither is presently established by the prepared top-two slope chain.

### Full source coordinate reduction for the remaining heads

The literal integer field yields a useful cancellation, without discarding lower terms. Put

    W=J-U*K+(2/3)*U, Y=3*K+1.

Then

    L W=4*U*W-(8/3)*(U²+9),
    L U=2*(Y-1)*(9-U²),
    L Y=12*Y*W+4*U*Y*(Y-3),
    integerStep(Y*P)=Y*(L P+(12*W-7*U)*P).

In particular, the W component of the complete field is independent of K/Y. Define `A_0=B_0=1`, `A_(n+1)=L A_n+(12W-7U)A_n`, and `B_(n+1)=integerStep B_n`. The full source recurrence then gives `integerJet n=2Y*A_n-3B_n` at every order. Both seed components remain: dropping `-3B_n` would repeat an endpoint error. This reduction is intended to derive the two missing residual heads; it supplies no residual sign by itself. The identity and source recurrence still require Lean audits.

### Fourth native jet head: next source ingredient

The complete field, applied to the preceding three heads, gives for `n>=3`

    [J^(n-3)]P_n=12^(n-3)*(U*r_n(Y)+U³*s_n(Y)
      +(5130U-945U³)*delta_(n,3)),

with the following proposed closed polynomials, derived coefficient by coefficient from the full recurrence:

    r_n=144(n-1)(2n-3)(n-2)Y³
      +(-48n⁴+600n³-492n²+696n-3456)Y²
      +(-48n⁵-60n⁴+54n³-318n²-546n-432)Y,
    s_n=-(64/3)n(n-1)(n-2)Y⁴
      +(32n⁴-80n³+160n²-400n+288)Y³
      +(-16n⁵+32n⁴-60n³+40n²-224n+768)Y²
      +[(8n⁶+2n⁴+59n³+191n²+202n)/3-4n⁵+240]Y.

The exact recurrence used is

    r_(n+1)=Y*r_n'+36(Y-1)*q_n+[(4n-12)Y+4n-3]*p_n
      +72(n-1)(Y²-4Y-1)*f_n,
    s_(n+1)=Y*s_n'+[(4n-16)Y+4n+1]*q_n
      -8(n-1)(Y-1)²*f_n.

The Y^4 terms in the first recurrence cancel identically; the remaining third-jet endpoint correction supplies `5130U-4860UY+U³(840Y-945)` at n=3. The Y terms are incorporated into r_3,s_3; the constant correction is killed by the kinetic commutator at the next order. The complete native derivative packet is

    K4(n)=576n(n-1)(n-2)YJ³+72(n-1)(n-2)U*f_n*J²
      +12(n-2)*(p_n+U²q_n)*J+U*r_n+U³*s_n,
    12*integerStep H(n)+kineticCommutator K4(n)=12*K4(n+1).

This all-order polynomial identity and the exact initial jet3, not isolated coefficient evaluations, are the proposed Lean proof. The formulas remain unaudited. They target the missing source data for the degree-15 residual; they do not establish its sign.

The prepared fourth reflected coefficient retains the complete Cauchy sum. Let `D_n=0` for n<3 and otherwise `D_n=U*r_n+U³*s_n+(5130U-945U³)*delta_(n,3)`. Then the target identity is

    1728*[epsilon³]reverse(P_n)=12^n*D_n,
    1728*[epsilon³]reverse(R_n)
      =12^n*sum_i (-1)^(n-i)*choose(n,i)
        *(A_i*D_(n-i)+B_i*C_(n-i)+C_i*B_(n-i)+D_i*A_(n-i)).

Here A,B,C are the preceding three exact reverse heads. The next task is to carry this coefficient through the five actual moments and the **full** quadratic-plus-cubic minor remainder, obtaining native minor coefficient fourteen and then slope coefficient fifteen. Native slope coefficient fourteen additionally needs the fifth jet head; it is still missing. Do not replace either missing coefficient with a sign assumption.

For the all-order reflected survivor, let `Cpoly_n=p_n+U²*q_n`, `Dpoly_n=U*r_n+U³*s_n`, and use the three C-head endpoint corrections `e0,e1,e2` above. Put `d_j=-Dpoly_j` for j=0,1,2 and `d3=5130U-945U³`. For even n>=8, polynomial binomial cancellation of degree six reduces the full fourth reflected head to

    -6*Dpoly_n+4Y*(d0-n*d1+choose(n,2)*d2-choose(n,3)*d3)
      -24U*Y*Cpoly_n+30n*U*Cpoly_(n-1)
      +2U*(f_n*e0-n*f_(n-1)*e1+choose(n,2)*f_(n-2)*e2).

This expression includes every endpoint correction. The unrestricted summand has degree at most six in the binomial index. At n=6 its degree-six coefficient is `(128/3)*U³*Y²`, so the additional term is `6!*(128/3)*U³*Y²`. The n=4 unrestricted sum still needs its exact finite treatment; n=2 has zero fourth reverse coefficient by degree. These are paper deductions pending a separate binomial and Lean audit, not additional established source lemmas.

### Complete next minor coefficient

The order-four unrestricted fourth-head sum has now been derived symbolically. Its A*D+D*A part is

    U*(-4608Y³-51840Y²)+U³*(3072Y⁴-12288Y³+12864Y²),

and its B*C+C*B part is

    U*(-23040Y³-19584Y²)+U³*(-3072Y⁴+9216Y³-1344Y²).

Their sum is `768*U*Y²*(-3*(12Y+31)+U²*(15-4Y))`; the fourth powers of Y cancel. This is the extra order-four correction to the endpoint formula above. Order six adds `30720*U³*Y²`. Both corrections must survive the five-moment minor reconstruction. The zero fourth coefficient at order two is imposed by the full source degree, not by extending the general formula.

Write the complete normalized reflection remainder as `F_n+epsilon*T_n+epsilon²*D_n+...`; here T is the third reflection head divided by 144 and D is the fourth reflection head divided by 1728. Let M denote the exact quadratic residual and H the exact cubic Hankel polynomial. The next complete minor coefficient is

    [J^14]minor=-12^18*((-12Y)*(cross_M(F,D)+M(T))+directional_H(F,T)).

Every entry is now an explicit polynomial from the preceding jet heads. `cross_M` is the quadratic cross term; `directional_H` is the coefficient linear in the second argument. In particular, the U-independent part comes entirely from `M(T|U=0)`, since each F contains U. Direct residual-row differences give

    M(T|U=0)=-3Y*(32Y⁴+408Y³+756Y²+858Y+945),
    ([J^14]minor)|U=0
      =-36*12^18*Y²*(32Y⁴+408Y³+756Y²+858Y+945).

This identifies one component of the full coefficient, not a replacement for it. The U² and U⁴ components, and their full slope transport, must also be retained. All formulas in this section await Lean audit.

### Even decomposition and complete slope response

The explicit five reflection heads have the exact forms

    F=U*f, T=t0+U²*t2, D=U*d1+U³*d3.

Retaining the entire minor gives `M14=12^18*(e0+U²*e2+U⁴*e4)`, with

    e0=12Y*M(t0),
    e2=12Y*(cross_M(f,d1)+cross_M(t0,t2))-directional_H(f,t0),
    e4=12Y*(cross_M(f,d3)+M(t2))-directional_H(f,t2).

These are explicit polynomials in Y, defined through the already-displayed five reflection formulas; no missing source coefficient is hidden in the definitions. Put `c=-512Y⁴`, `d=Y²*A(Y)`, `f3=Y²*B(Y)`, so that `M16=12^18*U²*c` and `M15=12^18*(U*d+U³*f3)`. The complete response gives `S15=12^18*(s0+U²*s2+U⁴*s4)`, where the derivatives below are in K and Y=3K+1:

    s0=(2Y-3)*(4Y*partial_K(e0)+18(Y-1)*d)-144Y*e0,
    s2=(2Y-3)*(4Y*partial_K(e2)+54(Y-1)*f3+(58Y+62)*d
      +96(Y²-4Y-1)*c)-144Y*e2,
    s4=(2Y-3)*(4Y*partial_K(e4)+(54Y+66)*f3
      -(32/3)(Y-1)²*c)-144Y*e4.

The all-order shear identity, followed by constant-coefficient extraction of kinetic derivatives, yields

    U^n*[J^n]integerThirdSlope=U*square([J^n]reducedSlope).

Factorials and U cancel in the polynomial ring, without a nonzero source-coordinate premise. Hence the complete reduced coefficient is

    [J^15]reducedSlope=12^18*V^7*(s0+V*s2+V²*s4).

The prepared proof establishes square-invariance of the actual components; parity is not assumed. This is still an unaudited identity, not a positivity theorem. In particular, retaining only s0 would not decide the residual conjecture.

The same source calculation exposes a reusable identity. Write `m_j=[J^j]integerThirdMinor`, `A=6K(9-U²)`, `B=6K²(9-U²)-36K-24`, `D=(12K+8)U`. For every j>=1,

    [J^j]integerThirdSlope=(2Y-3)*
      (4Y*partial_K(m_(j-1))+A*partial_U(m_j)+j*D*m_j+(j+1)*B*m_(j+1))
      -144Y*m_(j-1).

It follows directly by commuting transverse derivatives with polynomial coefficient extraction and retaining all three field components. The prepared general theorem avoids constructing a new high-derivative packet for each slope coefficient. For j=14, the remaining missing source ingredient is m13, which needs the fifth reflected head.

### Fifth-head recurrence to attack next

The full field gives a three-term recurrence for normalized kinetic deficit coefficients `t_(n,d)=12^(d-n)*[J^(n-d)]P_n`, away from the low-index endpoint cases:

    t_(n+1,d)=Y*partial_Y(t_(n,d))
      +2(Y-1)(9-U²)*partial_U(t_(n,d-1))
      +U*((4n-4d)Y+4n+9-4d)*t_(n,d-1)
      +12(n+2-d)*(6Y²-24Y-6-(2/3)(Y-1)²*U²)*t_(n,d-2).

For d=4 write `t_(n,4)=g0_n+U²*g2_n+U⁴*g4_n`. Start all three g's at zero at n=3 (the full third jet has degree three). Let `R_n=r_n+5130*delta_(n,3)` and `S_n=s_n-945*delta_(n,3)` retain the exact fourth-head endpoint. Then for n>=3:

    g0_(n+1)=Y*g0_n'+18(Y-1)*R_n+72(n-2)(Y²-4Y-1)*p_n,
    g2_(n+1)=Y*g2_n'+54(Y-1)*S_n+((4n-18)Y+4n-5)*R_n
      +72(n-2)(Y²-4Y-1)*q_n-8(n-2)(Y-1)²*p_n,
    g4_(n+1)=Y*g4_n'+((4n-22)Y+4n-1)*S_n-8(n-2)(Y-1)²*q_n.

Primes here denote Y derivatives. This gives an exact symbolic recursive construction from known source polynomials, with no guessed sign or dropped initial seed. The next target is a full all-order fifth derivative packet and its five actual reflection moments. If the reflection remainder is `F+epsilon*T+epsilon²*D+epsilon³*E+...`, the complete next minor coefficient must be

    m13=-12^18*((-12Y)*(cross_M(F,E)+cross_M(T,D))
      +directional_H(F,D)+directional_H(T,F)).

The two directional cubic terms are both required. Prepared source40 constructs the fifth head recursively as one polynomial G_m (n=m+3), directly from the known third/fourth heads and the full transverse operator. It starts at G_0=0, retains the exceptional third jet, and targets the exact packet

    K5(n)=1728*n(n-1)(n-2)(n-3)*Y*J⁴
      +288*(n-1)(n-2)(n-3)*U*f_n*J³
      +72*(n-2)(n-3)*(p_n+U²*q_n)*J²
      +12*(n-3)*(U*R_n+U³*S_n)*J+G_(n-3),
    partial_J^m P_(m+4)=m!*12^m*K5(m+4).

The recurrence is checked through `12*integerStep(K4_actual)+commutator(K5)=12*K5_next`, including the exact n=3 endpoint. Source41 retains all five reflected Cauchy pairs `A*E+B*D+C*C+D*B+E*A`. Source42 carries them through the full minor to m13; source43 uses the general response to obtain native S14 and `square(p14)=U^13*S14`. These remain unaudited preparations. They supply the companion coefficient required for the residual's next canonical coefficient; residual positivity itself remains open.

### Next canonical coefficient of the full residual

Let p_j denote the complete reduced native slope coefficients, and a,b the actual quadratic coefficients. Polynomial square absorption gives the complete kinetic residual

    r(z)=p(z)+(p16+(z+8b)*p17)*(a+bz-z²)^7*(z-b/2)².

Its top two remaining native coefficients are

    r15=p15+8b*p16+(7a+143b²/4)*p17,
    r14=p14+(7a-113b²/4)*p16+(7ab-673b³/4)*p17.

Thus the next affine surplus coefficient is

    q7(z)=(-1/9)^7*(p14+(z+7b)*p15
      +(7a+8bz+111b²/4)*p16
      +((7a+143b²/4)*z+56ab+82b³)*p17).

This can also be derived directly from the second heads of powers in the free quadratic algebra, with omega²=a+b*omega+c*E. For M>=1:

    [E^(M-1)]Re(omega^(2M))=(M*a+M(M-1)*b²/2)*c^(M-1),
    [E^(M-1)]Re(omega^(2M+1))=(M²*a*b+(M-1)*M*(M+1)*b³/6)*c^(M-1),
    [E^(M-1)]Im(omega^(2M+1))=(M*a+M*(M+1)*b²/2)*c^(M-1).

The factor M² in the odd real component includes the extra factor (a+cE); omitting it would corrupt q7. A paired induction using the existing exact real/imaginary recurrence proves the displayed candidate formulas on paper. The two independent symbolic derivations agree. The next task is to formalize this all-order identity and connect q7 to the actual source coefficients just prepared, then settle its sign on the full physical cone. No sign is asserted here.

## Log

- 2026-10-05 — Derived symbolically during C77 row51. Corpus `full_quotient_attack` exited0, partial index1242423/coverage1242430 with complete65835-file inventory, compiler mostly pending/stale and background refresh incomplete. `third_jet_head_api` exited0, partial index1242505 with coverage pending and deadline/refresh limitations. All candidate/source/idea/ingredient sections inspected. The supplied results contain source recurrence/incidence and fixed reflection identities, not the required all-order third coefficient. No exhaustive novelty claim. No numerical sampling or external coefficient arithmetic. The next-coefficient expressions above need independent algebra and Lean audits before they are treated as established.
- 2026-10-05 — Second hand-algebra pass rederived the third-jet recurrence, reflected endpoint corrections, determinant cross term, native slope coefficient and final surplus sign completion. It agrees with the displayed formulas; this is not a Lean audit. Prepared the four sources listed above. The native recurrence retains the entire `integerStep` operator and the exceptional `270-105u²`; reflected coefficient reconstruction retains all Cauchy terms; the five-moment proof targets literal complete source coefficients; the next-minor proof uses the full quadratic-plus-cubic remainder. No sign premise is introduced. Static forbidden-declaration/raised-limit scans empty. C77 row51 completed all five stages, with all37 strict signs and the universal Fin37 capstone using only standard foundational axioms; sole cell227 continues row52. No second Lean, production promotion, or no-go retirement.
- 2026-10-05 — Prepared the seven additional sources above, including a full source-to-canonical-polynomial-to-source evaluation chain. Rechecked the displayed native slope D0/D1 by differentiating the complete minor head and retaining the transverse U term. The all-order quadratic power induction supplies the exact canonical highest coefficient independently of finite source truncation. Static forbidden-declaration/raised-limit scans empty; all new files still unaudited. Corpus `next_slope_affine_api` exited0, partial1242829/coverage1242833, complete65844-file inventory; `surplus_quadratic_api` exited0, partial1242929, complete65846-file inventory. Compiler metadata mostly pending/stale; refresh incomplete; all result categories inspected. C77 row52 closed all37 signs plus its universal capstone with standard3; row53 normalization stages subsequently passed. The square-absorption conjecture above is the next proposed attack, not an established positivity result.
- 2026-10-05 — Added four prepared modules: the complete source square comparison and degree-fifteen residual; exact W-field/gauged source decomposition; all-order fourth native jet head with its exceptional third jet; and full fourth reflected Cauchy coefficient. Extended `TTC78SurplusNormalHead` with component degree bounds. A second symbolic pass checked every fourth-head coefficient recurrence and its initial correction; this is not a Lean audit. Residual sign and next minor/slope coefficients remain open. Current frontier map still lists the global interior gap. Corpus `residual_square_structure` exited0 partial1243141/coverage1243147, complete65845-file inventory; `shifted_kinetic_invariant` exited0 partial1243268 with coverage pending/deadline; lexical `integerLie integerJet --any` returned actual integer source declarations. All result categories inspected, no exhaustive novelty claim. C77 row54 closed all37 signs plus its universal capstone with standard3; row55 Columns passed, remaining stages live. No second Lean, raised limits, numerical sampling, external coefficient arithmetic, production promotion, or no-go retirement.
