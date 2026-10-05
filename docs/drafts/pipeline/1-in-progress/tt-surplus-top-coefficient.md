# Complete-source test of the surplus power certificate

- **ID:** TT-C78-SURPLUS-HEAD
- **Route:** TT, full finite-clock third-slope positivity.
- **Stage:** In progress. Symbolic paper derivation below; source identities and sign still require independent algebra audit and Lean verification.
- **Parent:** `tt-third-slope-nonlinear-cone.md`.
- **Question:** Does canonical reduction in the nonlinear surplus have nonnegative affine coefficients throughout the physical kinetic interval? This is a proposed certificate for C78, not an assumed source property.
- **Constraints:** Complete source recurrence; retain exceptional first/second jets and second/fourth reflections. No sampling, external coefficient arithmetic, omitted remainder, second Lean process, or raised limits.

## Why this test is needed

Latest paper frontier: complete sixth native head, complete seventh U=0 component, and the highest coefficients of its remaining even components are derived. Full seventh U²/U⁴/U⁶ components, complete Q6 endpoint signs, and the full residual sign remain open. All eighty scratch sources require Lean audit.

### 2026-10-05 — Sixth coefficient: exact mass concavity and a factorable endpoint

#### Next native coefficient: complete U=0 component of M12 and S13

The full reversed remainder has coefficients `F,T,D,E,...`, with F,D odd in U. On U=0 its zeroth and second coefficients vanish. Therefore the COMPLETE quadratic determinant coefficient4 is `cross(T0,E0)`, and the COMPLETE cubic coefficient3 is `H(T0)`. Unknown sixth reflection heads vanish from this projection; they are not omitted from the transverse problem. This gives

    M12|_(U=0)=12^18*[12Y*cross(T0,E0)-H(T0)].

Hand finite differences of the full E0, including both exceptional reflections, give

    S(E0)=E10-2E8+E6
      =-6Y⁴-522Y³-(14367/2)Y²-(69279/2)Y,
    T(E0)=E8-3E6+3E4-E2
      =(129/4)Y⁴+(111/4)Y³-(31341/16)Y²-(150381/16)Y+2295/16,
    W(E0)=E10-4E8+6E6-4E4+E2
      =-(177/4)Y⁴-(1559/4)Y³-(47847/16)Y²-(205203/16)Y-765/4.

Independent substitution in `(8/3)Y²*S-16Y*W` reproduces the previously derived complete `cross(f,E0)` exactly. Using the corrected identity `e*S+(24Y²+156Y)*W-96Y*T`, with `e=-4Y³-9Y²-45/4`, now gives

    cross(T0,E0)=24Y⁷+1080Y⁶+14079Y⁵+(136083/2)Y⁴
      -(1074555/4)Y³-(8177751/8)Y²+(2768715/8)Y,
    H(T0)=-288Y⁸+5688Y⁷+148104Y⁶+601812Y⁵-78894Y⁴
      -(2549313/2)Y³+(2998215/2)Y².

The cubic was derived independently by writing `T0_r` as its complete cubic polynomial in r plus the exceptional r=0 term e. The regular cubic determinant is `-p0*d3²+2*d1*d2*d3-d2³`; its exceptional correction is `e*(T6*T10-T8²)`. Thus

    M12|_(U=0)=12^18*Y²*L12(Y),
    L12=576Y⁶+7272Y⁵+20844Y⁴+214686Y³-3144771Y²-10991970Y+2653965.

The exact full source response at kinetic degree13 retains the transverse U derivative of M13:

    S13|_(U=0)=12^18*Y²*T13(Y),
    T13=(2Y-3)*[24L12+12Y*L12'+18(Y-1)*L1+84*(Y²-4Y-1)*E0_minor]
      -144Y*L12
      =-27648Y⁷-176256Y⁶+1620864Y⁵+6856704Y⁴+207826128Y³
        +945579096Y²+1123829316Y-235394100.

Here L1 is the corrected full M13 U coefficient and E0_minor the full M14 constant component already derived above. This determines the first V component of actual p13, but not its other components or the full Q6 sign. All displayed new identities are PAPER deductions awaiting serial Lean audit. Sources64/65 will connect these statements to literal complete source coefficients; no native coefficient is replaced by an independent premise.

#### Complete first U component of the sixth native head

For n>=5 write the normalized sixth jet head as `U*f1(n,Y)+U³*f3(n,Y)+U⁵*f5(n,Y)`, plus its exceptional n=5 scalar term. The exact native recurrence determines

    f1(n+1)=Y*partial_Y f1(n)+36(Y-1)*g2(n)
      +[(4n-20)Y+4n-11]*g0(n)+72(n-3)*(Y²-4Y-1)*r(n),

where g0,g2 are the complete regular fifth-head components and r is the regular fourth-head U coefficient. Solving each literal Y-coefficient gives `f1=A6*Y⁴+B6*Y³+C6*Y²+D6*Y`, with

    A6=-1296(n-2)(n-3)(n-4)(4n²-8n+19),
    B6=-108(n-3)(n-4)(8n⁴+68n³-398n²-347n-1266),
    C6=(36/5)(n-4)*(160n⁶-852n⁵-1325n⁴+2115n³-7070n²-13413n-11340),
    D6=(9/5)n(n-1)*(160n⁶-736n⁵-182n⁴+5465n³-1925n²-1534n-5928).

The apparent Y⁵ forcing cancels exactly. The four coefficient equations are `a(n+1)-j*a(n)=forcing_j(n)`; independent seed checks give `f1(4,Y)=3499200Y`. The complete fifth scalar correction `-92340+86940U²-10395U⁴` contributes `3499200Y-3591540` to the next first-U coefficient. Hence the literal normalized sixth first-U component is `f1(n,Y)-3591540*delta_(n,5)`, after subtracting the regular n=4 linear seed in the zero-seeded recurrence. This is a paper formula pending source-identification and kernel audit, not yet an audited native identity.

It also supplies the next required seventh-head constant component h0 through

    h0(n+1)=Y*partial_Y h0(n)+18(Y-1)*f1(n)
      +72(n-4)*(Y²-4Y-1)*g0(n).

Its apparent Y⁵ forcing cancels because `A6=-4(n-4)*A0_fifth`. Solving this complete recurrence, retaining its exceptional n=5/6 terms, is the next mathematical task needed for the p12 first component. The transverse f3/f5 and remaining seventh components are still open and remain necessary for the full Q6 sign.

#### Remaining sixth transverse components: full forcing and leading solutions

The full fifth-head split gives the following exact remaining sixth recurrences, with `D=Y²-4Y-1`, g2/g4 the known fifth components and r/s the fourth U/U³ components:

    f3(n+1)=Y*partial_Y f3(n)+72(Y-1)*g4(n)
      +[(4n-24)Y+4n-7]*g2(n)+72(n-3)*D*s(n)-8(n-3)*(Y-1)²*r(n),
    f5(n+1)=Y*partial_Y f5(n)
      +[(4n-28)Y+4n-3]*g4(n)-8(n-3)*(Y-1)²*s(n).

The apparent Y⁶ forcing of f3 cancels exactly. Its Y⁵ coefficient a3 and the Y⁶ coefficient a5 of f5 obey

    a3(n+1)-5*a3(n)=-768*(n-1)*(n-2)*(n-3)*(4n²-27n+30),
    a5(n+1)-6*a5(n)=(256/3)*n*(n-1)*(n-2)*(n-3)*(n-5),
    a3(4)=a5(4)=0.

Hand factorization supplies the closed solutions

    a3(n)=384*(n-1)*(n-2)*(n-3)*(n-4)*(2n-3),
    a5(n)=-(256/15)*n*(n-1)*(n-2)*(n-3)*(n-4).

These satisfy both polynomial recurrences and the seeds, so their homogeneous 5^n/6^n corrections vanish. This assertion concerns only these highest transverse coefficients; it does not discard possible geometric corrections in the remaining equations. Source76 prepares the full forcing split, both highest forcing identities, the two polynomial recurrence/seed checks, and the exact scalar corrections. Literal all-order identification of the full f3/f5 remains open.

Applying the complete native constant-coordinate operator to the fifth exceptional scalar gives

    SixthInitialLinear=Y*(3499200U-1443960U³+124740U⁵),
    SixthInitialConstant=-3591540U+1530900U³-135135U⁵.

Applying it to this SixthInitialConstant gives the full seventh correction

    SeventhInitialLinear=Y*(-64647720+104217840U²-27471150U⁴+1891890U⁶),
    SeventhInitialConstant=64647720-107809380U²+29002050U⁴-2027025U⁶.

Thus the previously retained seventh constant 64647720 is only one part of its full scalar seed. The other terms are necessary for the remaining even components. The complete regular seventh U²/U⁴/U⁶ recurrences to solve next are

    h2(n+1)=Y*partial_Y h2(n)+54(Y-1)*f3(n)
      +[(4n-26)Y+4n-13]*f1(n)+72(n-4)*D*g2(n)-8(n-4)*(Y-1)²*g0(n),
    h4(n+1)=Y*partial_Y h4(n)+90(Y-1)*f5(n)
      +[(4n-30)Y+4n-9]*f3(n)+72(n-4)*D*g4(n)-8(n-4)*(Y-1)²*g2(n),
    h6(n+1)=Y*partial_Y h6(n)
      +[(4n-34)Y+4n-5]*f5(n)-8(n-4)*(Y-1)²*g4(n).

All are paper deductions from the complete source field, with no source-sign premise. Remaining lower Y coefficients and their seeds are unsolved; the full p12/p13/Q6 signs remain open.

#### Complete sixth U³ component

The remaining four Y coefficients of f3 have now been solved by exact polynomial coefficient comparison, with their full source forcings retained. Write

    f3(n,Y)=A3(n)Y⁵+B3(n)Y⁴+C3(n)Y³+D3(n)Y²+E3(n)Y,
    A3=384(n-1)(n-2)(n-3)(n-4)(2n-3),
    B3=32(n-2)(n-3)(n-4)*(-28n³+102n²-11n+567),
    C3=24(n-3)(n-4)*(8n⁵-88n⁴+64n³-635n²-576n-3138),
    D3=6(n-4)*(16n⁷-40n⁶-48n⁵+1014n⁴-109n³+3973n²+4950n+14544),
    E3=-32n⁹+312n⁸-924n⁷-398n⁶+5433n⁵-8048n⁴-1486n³-6887n²-4386n-13824.

The four difference equations, extracted from the COMPLETE forcing displayed above, are

    B3(n+1)-4B3(n)=96(n-2)(n-3)*(28n⁴-270n³+589n²-641n+2814),
    C3(n+1)-3C3(n)=24(n-3)*(-16n⁶+296n⁵-1360n⁴+2198n³-6076n²+2069n-28926),
    D3(n+1)-2D3(n)=6*(-16n⁸+232n⁷-392n⁶-1822n⁵+9355n⁴-9513n³
      +11183n²-13959n+43452),
    E3(n+1)-E3(n)=3*(-96n⁸+448n⁷-140n⁶-2784n⁵+2221n⁴-1126n³
      -5402n²-9969n-5472).

The first four components vanish at n=4. Exact Horner evaluation of E3 gives E3(4)=-1443960, matching the full scalar-source correction already derived. Independent substitution at n=3 gives D3 forcing1662120 and E3 forcing-1089450 from the original g4/g2 forcing as well. Thus no extra 4^n,3^n or2^n mode is required for this component. The final integration constant in E3 is fixed by the source seed, not a free hypothesis.

The literal zero-seeded closed expression is

    SixthThreeClosed(m)=f3(m+4,Y)+1443960Y*delta_(m,0)+1530900*delta_(m,1).

The complete m=0 forcing correction is -1443960Y+1530900, coming from the fifth-head scalar terms 86940U²-10395U⁴. Source77 prepares every component recurrence, the FULL forcing identity, the seed, and the corrected closed recurrence. This is PAPER progress only; the literal third-transverse native identification and Lean audit are next. Full f5 and the seventh higher components remain open.

#### Complete sixth U⁵ component and full native identification

The last sixth-head component is now solved on paper. Writing

    f5(n,Y)=A5(n)Y⁶+B5(n)Y⁵+C5(n)Y⁴+D5(n)Y³+E5(n)Y²+F5(n)Y,
    A5=-(256/15)*n*(n-1)*(n-2)*(n-3)*(n-4),
    B5=(64/3)*(n-1)*(n-2)*(n-3)*(n-4)*(2n²-n+12),
    C5=(16/3)*(n-2)*(n-3)*(n-4)*(-8n⁴+16n³-58n²-28n-417),
    D5=(4/3)*(n-3)*(n-4)*(16n⁶-72n⁵+148n⁴+94n³+1042n²+845n+6162),
    E5=(1/3)*(n-4)*(-16n⁸+128n⁷-328n⁶-80n⁵+103n⁴-780n³
      -8165n²-7242n-35280),
    F5=(1/60)*(32n¹⁰-400n⁹+1680n⁸-1480n⁷-5854n⁶+12791n⁵
      +10830n⁴-10635n³+71072n²+77484n+276480).

Exact coefficient comparison verifies each equation `P(n+1)-jP(n)=forcing_Yj(n)` from the complete f5 forcing. All coefficients above Y vanish at n=4 and F5(4)=124740. Independent substitution at n=3 in the original source forcing gives E5 forcing-151200 and F5 forcing85050, agreeing with the derived equations. Hence every homogeneous geometric correction vanishes once the final constant is chosen by the exact source seed. This statement applies to the sixth head; the seventh zero head still requires its known 4^n term.

The zero-seeded fifth-U component is

    SixthFiveClosed(m)=f5(m+4,Y)-124740Y*delta_(m,0)-135135*delta_(m,1).

Together with the complete first/third components, define

    SixthClosedCore(n)=U*f1(n,Y)+U³*f3(n,Y)+U⁵*f5(n,Y),
    SixthClosedHead(m)=SixthClosedCore(m+4)
      -SixthInitialLinear*delta_(m,0)+SixthInitialConstant*delta_(m,1).

The full source recurrence is

    SixthClosedHead(m+1)=Y*partial_Y SixthClosedHead(m)
      +AU*partial_U FifthHead(m+1)
      +U*[(4(m+4)-20)Y+4(m+4)-11]*FifthHead(m+1)
      +12(m+1)*B0*FourthRegular(m+4).

No transverse term is omitted. Source80 identifies the resulting full coefficient target

    [J^m]integerJet(m+5)=12^m*SixthClosedHead(m+1).

Its base uses the full fourth jet, then the existing complete fifth/fourth coefficients drive induction through the literal integerStep coefficient formula. Source78 separately prepares the third-transverse bridge via normalized third/fourth U derivatives; source79 carries the complete f5 equations, forcing identity and scalar seed; source80 assembles the whole sixth head. ALL80 sources remain UNCOMPILED, with no axiom audits. These are paper derivations and proof scripts, not verified Lean results.

Next mathematical target: use the full sixth reflected coefficient to reconstruct the complete M12 and S13, hence p13; solve the remaining seventh U²/U⁴/U⁶ recurrences for the full p12. Both Q6 endpoint signs and the complete residual sign remain open.

#### Highest coefficients of the remaining seventh components

With all sixth components now available, the full seventh recurrences give further cancellations. The apparent Y⁶ forcing in h2 vanishes because `54*A3+72(n-4)*g2_A=0`. The apparent Y⁷ forcing in h4 vanishes because `90*A5+72(n-4)*g4_A=0`. Their highest surviving coefficients and the Y⁷ coefficient of h6 have zero seeds at n=5. Denote them by H2,H4,H6. Exact coefficient extraction gives

    H2(n+1)-5H2(n)=10368(n-2)(n-3)(n-4)*(-4n³+34n²-70n+115),
    H4(n+1)-6H4(n)=384(n-1)(n-2)(n-3)(n-4)*(10n²-77n+90),
    H6(n+1)-7H6(n)=-(1024/15)n(n-1)(n-2)(n-3)(n-4)*(n-6).

The corresponding closed solutions are

    H2(n)=2592(n-2)(n-3)(n-4)(n-5)*(4n²-8n+19),
    H4(n)=-384(n-1)(n-2)(n-3)(n-4)(n-5)*(2n-3),
    H6(n)=(512/45)n(n-1)(n-2)(n-3)(n-4)(n-5).

Substituting these factored polynomials verifies both the three recurrences and their zero seeds. Thus these particular highest coefficients need no extra 5^n/6^n/7^n channel. The lower Y coefficients of h2/h4/h6 remain unsolved and may require geometric corrections; the known h0 4^n term is retained. These newest three identities are PAPER only and not yet included in a separate Lean source.

#### Seventh zero component: the seed forces a geometric channel

The Y⁴ coefficient a7 of the seventh-head zero component obeys the exact recurrence

    a7(n+1)-4*a7(n)=5832*(n-3)*(n-4)*
      (8n⁴-68n³+230n²-439n+794),
    a7(5)=0.

The purely polynomial ansatz with vanishing seed fails. The unique polynomial particular solution is `1944*F(n)`, where

    F(n)=-8n⁶+108n⁵-662n⁴+2289n³-5342n²+8835n-7788,
    F(5)=-12288.

Thus the exact zero-seeded solution for n>=5 is

    a7(n)=1944*F(n)+23887872*4^(n-5).

Independent direct substitution of the full previously derived A6,B6,A0_fifth,B0_fifth at n=5 gives forcing9902736, agreeing with this recurrence at n=6. No numerical sampling or external coefficient arithmetic was used; these are symbolic source and seed identities. A polynomial solution of the homogeneous shift equation `R(n+1)=4R(n)` must vanish, by comparing its highest coefficient. Hence there is no alternative polynomial particular solution that fixes the seed. This is a paper classification of this recurrence, pending the full literal-source bridge and Lean audit, not a claim that all seventh-head components are already known.

Positive survivor: retain the forced geometric channel exactly. Future reflected binomial sums cannot discard it by a polynomial-degree cutoff; its binomial transform need not vanish at large order. This is a new structural issue in the complete next-head derivation, not evidence against RH or the finite physical-interval source sign. Source67 prepares the exact scalar forcing, recurrence, zero seed, and geometric solution. The lower Y components, their seeds, full U³/U⁵ components and p12/p13 endpoint signs remain open.

#### Complete seventh-head U=0 component

The remaining three coefficient recurrences have now been solved on paper. For n=m+5 define

    h0(n,Y)=a7(n)*Y⁴+b7(n)*Y³+c7(n)*Y²+d7(n)*Y,
    a7(n)=1944*F(n)+23887872*4^(n-5),
    b7(n)=972*(-16n⁷+180n⁶-556n⁵-465n⁴+4646n³-2460n²-8889n-9180),
    c7(n)=(162/5)*(-160n⁸+1536n⁷-2298n⁶-10095n⁵+15705n⁴
      +39n³+7813n²-12540n),
    d7(n)=-(9/35)*n*(n-1)*(2240n⁷-16912n⁶+24932n⁵+79805n⁴
      -236350n³+155132n²-98667n+188550).

The Y³/Y²/Y forcing equations are, respectively,

    b7(n+1)-3*b7(n)=18*(C6-B6)+72*(n-4)*(C0_fifth-4B0_fifth-A0_fifth),
    c7(n+1)-2*c7(n)=18*(D6-C6)+72*(n-4)*(-4C0_fifth-B0_fifth),
    d7(n+1)-d7(n)=-18D6-72*(n-4)*C0_fifth.

Independent exact seed checks give b7(5)=c7(5)=0 and d7(5)=-64647720. Thus only a7 requires a geometric mode; no 3^n or 2^n correction is needed. The complete zero-seeded head is

    G7(m)=h0(m+5,Y)+64647720*Y*delta_(m,0)+64647720*delta_(m,1),
    G7(0)=0,
    G7(m+1)=Y*partial_Y G7(m)+18(Y-1)*SixthOneClosed(m+1)
      +72(m+1)*(Y²-4Y-1)*g0(m+5).

The exceptional scalar at native order six is forced by the full preceding scalar jet, not introduced to fit the formula. The literal native target is

    UZero([J^m]integerJet(m+6))=12^m*G7(m+1).

Its paper proof uses the full constant/positive coefficient response of integerStep, the previous literal sixth first-U and fifth zero projections, and the base P6=integerStep(P5). This retains the transverse U derivative. Prepared sources69/70 carry the closed recurrence and literal-source proof. All are UNCOMPILED; the projected reflection and determinant continuation below is also pending kernel audit. Full p12/p13 and both Q6 endpoint signs remain open.

#### Complete projected reflections and the first component of S12

The full Cauchy products now determine the two further reflection components needed here. Let A,B,C,D,E be the first five normalized reversed native heads already derived, F1 the sixth first-U head, and G0 the seventh zero head. All heads are zero below their source degree and retain their exceptional endpoint corrections. In particular

    F1(n)=0                         if n<5,
    F1(n)=SixthOneCore(n)-3591540*delta_(n,5) otherwise,
    G0(n)=0                         if n<6,
    G0(n)=SeventhZeroClosed(n-5)     otherwise.

Write B1=UOne(B), C0=UZero(C), D1=UOne(D), E0=UZero(E). The proven-form targets for the complete reflected source are the binomial sums

    12^5*UOne([X^5]normalizedReflection(n))
      =sum_i binom(n,i)*(-1)^(n-i)*
        [A(i)F1(n-i)+B1(i)E0(n-i)+C0(i)D1(n-i)
          +D1(i)C0(n-i)+E0(i)B1(n-i)+F1(i)A(n-i)],
    12^6*UZero([X^6]normalizedReflection(n))
      =sum_i binom(n,i)*(-1)^(n-i)*
        [A(i)G0(n-i)+C0(i)E0(n-i)+E0(i)C0(n-i)+G0(i)A(n-i)].

The second identity retains all seven Cauchy pairs before using B0=D0=0. It does not assume that the unknown sixth zero projection vanishes. The first identity uses A1=C1=E1=0 and B0=D0=0; it does not assume a value for the sixth zero projection either. The geometric 4^n component of G0 remains in the exact sum. No polynomial-degree cutoff is applied to it.

For the five actual moments n=2,4,6,8,10, call the resulting normalized projections H1 and I0 respectively. Let f,T0,T2,d,E0,E2 be the previously derived full first/zero/second projections of the remainder's coefficients F,T,D,E. Let `mix(F,T,E)=Hdir(F+T,E)-Hdir(F,E)-Hdir(T,E)`; this is the existing full trilinear polarization. Hand coefficient extraction from the COMPLETE quadratic-plus-cubic determinant gives

    M11_one/12^18 = L11
      =12Y*[cross(f,I0)+cross(T0,H1)+cross(d,E0)]
        -mix(f,T0,E0)-Hdir(T0,d),
    M12_two/12^18 = L12two
      =12Y*[cross(f,H1)+cross(T2,E0)+cross(T0,E2)+Residual(d)]
        -Hdir(f,E0)-mix(f,T0,d)-Hdir(T0,T2).

Here `M12_two` means the U² coefficient, equivalently one half of the second U derivative at zero. Its derivation needs no unknown higher transverse native component: F is exactly linear, T has zero first derivative, and D vanishes at zero. These vanishing statements are used only after the full coefficient product rules are written.

Consequently the complete first-U component of the native coefficient S12 is

    S12_one/12^18 = R12
      =(2Y-3)*[4Y*partial_K L11+36(Y-1)*L12two
        +48(Y+1)*Y²*L12(Y)+78(Y²-4Y-1)*L1_full]
        -144Y*L11,

where `L1_full=Y²*(3840Y⁵+43440Y⁴-24336Y³+129036Y²+3116268Y-661770)` is the corrected M13 first-U shape. Thus the term with the second U derivative of M12 is retained, rather than replaced by a zero-face restriction. Sources71..75 prepare the reversed-head identification, exact projected Cauchy sums, M11_one, M12_two, and the literal full S12_one response. ALL80 sources remain UNCOMPILED; these are paper identities with proof scripts, not checked Lean theorems.

The source square-transfer identity shows why these components matter: the coefficient of V⁶ in complete Q6, at fixed Y,z,a, is

    (-1/9)^6*12^18*[R12+(z+6b)*Y²*T13(Y)],  b=(7-Y)/9.

It is independent of the auxiliary mass a; contributions from p14..p17 begin at higher V order. This identifies the next exact sign expression to settle without discarding those higher components from the full Q6 problem. Neither its full sign nor either complete Q6 endpoint sign is claimed. Remaining tasks include expanding/analysing these five-moment expressions, deriving the other transverse components of p12/p13, and proving the full residual sign.

Current hard target remains positivity of the COMPLETE degree-seven absorbed residual. The previous complete q7 sign is a paper result, not a sign for the remaining polynomial. A kinetic-antitonicity conjecture has not been proved or refuted; the corpus searches below did not supply it. No monotonicity premise is admitted.

For a fixed complete native polynomial p of degree at most17, let Qj(a) denote coefficient j of its canonical affine normal form at fixed b,z, with c=-1/9. Absorption of Q8 changes Q7 only, so the sixth coefficient is exactly Q6. Hand expansion using the quadratic power recurrence gives

    Q6=c^6*[p12+(z+6b)p13+(7a+21b²+7bz)p14
      +(49ab+56b³+(7a+28b²)z)p15
      +(28a²+196ab²+126b⁴+(56ab+84b³)z)p16
      +(224a²b+588ab³+252b⁵+(28a²+252ab²+210b⁴)z)p17].

This is the entire coefficient, including p12 and p13; these last two native coefficients are NOT yet derived. No truncated expression is used for its sign.

The exact quadratic coefficient in auxiliary a is `2268*Q8`, where Q8 is independent of a. Consequently, for a=(1-t)a0+t*a1,

    Q6(a)=(1-t)Q6(a0)+t*Q6(a1)
      -2268*Q8*t*(1-t)*(a1-a0)².

Since the actual source has Q8<0, this gives strict mass concavity, with a positive interior chord reserve. Equivalently its second mass derivative is 4536*Q8. The exact increment, writing q7 for the absorbed coefficient and Emax(a)=9(a+b²/4), is

    Q6(a+d)-Q6(a)=-63*d*q7(a)
      +63*d*Emax(a)*Q8+2268*d²*Q8.

Thus positive q7 does not propagate positivity to Q6: it makes Q6 decrease with mass when a>=0. This closes that attempted shortcut and supplies the stronger positive survivor, a full endpoint reduction with an explicit reserve.

For the physical source, `0<a<aFlat=(k-1)/9`, because

    aFlat-a=k*(6k-7)*(9-v)/648>0.

The upper endpoint factors exactly:

    z²-((2-k)/3)z-aFlat=(z-1/3)*(z+(k-1)/3).

New conjecture to attack: the complete Q6 values at a=0 and a=aFlat are positive for the physical v,k,z. If true, the chord identity proves the actual Q6 sign. Neither endpoint sign is established. In particular the native p12/p13 contributions must be derived from the full recurrence, including its exceptional low jets. This is a proposed removal of the mixed mass variable from the next hard sign problem, not a bound optimization or a completed full-residual certificate.

Prepared sources62/63 below target the all-order third quadratic heads, the exact complete Q6 formula, and the mass chord/source interval identities. Sources64/65 target the literal M12/S13 zero components; source66 gives the closed sixth first-U recurrence with its seed correction; source67 retains the forced geometric channel of the seventh zero component. They remain UNCOMPILED while sole foreground cell227 audits C77. No second Lean process or numerical/CAS experiment was started. Current checkpoint: rows0..69 and96 closed, all37 strict signs and universal Fin37 capstones using only standard3; final68/69 logs read. Sole cell227 continues70Columns, last OS lake70231/Lean70285 live at03:37. All68 kinetic/surplus sources remain uncompiled; static forbidden/raised-limit scans64..67 empty. These identities are paper deductions awaiting kernel audit, and no endpoint sign or full-residual positivity has been claimed. Source68 now prepares literal native identification of the sixth first-U recurrence, including order five. It remains UNCOMPILED. Literal seventh-head identification is still a separate required step.

Corpus searches `full_residual_comparison` (partial, semantic timeout; complete65920-file inventory), `quadratic_derivative_normal` (not partial; complete65922 files), and `sixth_mass` (not partial; complete65929 files), all terminalexit0. All declaration/candidate/source/idea/ingredient sections inspected. Their compiler metadata is mostly pending/stale/source-only and refresh incomplete; no exhaustive novelty claim. Relevant source evidence was checked directly: full canonical evaluation, exact absorbed coefficient, all-order quadratic power recurrence, and native squared source flow.

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

The sole live Lean pipeline remains C77 cell227. Sixty-four scratch sources are prepared after the original sixteen kinetic modules, in dependency order (the general response module imports only the original chain):

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
28. `/tmp/TTC78SurplusNextHeads.lean`
29. `/tmp/TTC78SurplusAbsorbedHead.lean`
30. `/tmp/TTC78KineticFifthZeroHead.lean`
31. `/tmp/TTC78KineticFifthClosedHead.lean`
32. `/tmp/TTC78KineticFifthReflectionFive.lean`
33. `/tmp/TTC78KineticMinorFourteenExpanded.lean`
34. `/tmp/TTC78KineticSlopeFifteenExpanded.lean`
35. `/tmp/TTC78SurplusResidualDerivativeSign.lean`
36. `/tmp/TTC78SurplusResidualMonotone.lean`
37. `/tmp/TTC78SurplusResidualNeutralFace.lean`
38. `/tmp/TTC78KineticFifthZeroReflection.lean`
39. `/tmp/TTC78KineticSlopeFourteenFirstPart.lean`
40. `/tmp/TTC78KineticFifthTwoReflection.lean`
41. `/tmp/TTC78KineticMinorThirteenMiddle.lean`
42. `/tmp/TTC78KineticFifthFourReflection.lean`
43. `/tmp/TTC78KineticMinorThirteenLast.lean`
44. `/tmp/TTC78KineticSlopeFourteenExpanded.lean`
45. `/tmp/TTC78SurplusResidualHeadPositive.lean`
46. `/tmp/TTC78SurplusSixHeads.lean`
47. `/tmp/TTC78SurplusSixMass.lean`
48. `/tmp/TTC78KineticMinorTwelveZero.lean`
49. `/tmp/TTC78KineticSlopeThirteenZero.lean`
50. `/tmp/TTC78KineticSixthOneHead.lean`
51. `/tmp/TTC78KineticSeventhZeroTop.lean`
52. `/tmp/TTC78KineticSixthOneSource.lean`
53. `/tmp/TTC78KineticSeventhZeroClosed.lean`
54. `/tmp/TTC78KineticSeventhZeroSource.lean`
55. `/tmp/TTC78KineticProjectedReverseHeads.lean`
56. `/tmp/TTC78KineticProjectedReflectionHeads.lean`
57. `/tmp/TTC78KineticMinorElevenOne.lean`
58. `/tmp/TTC78KineticMinorTwelveTwo.lean`
59. `/tmp/TTC78KineticSlopeTwelveOne.lean`
60. `/tmp/TTC78KineticSixthTransverseForcing.lean`
61. `/tmp/TTC78KineticSixthThreeHead.lean`
62. `/tmp/TTC78KineticSixthThreeSource.lean`
63. `/tmp/TTC78KineticSixthFiveHead.lean`
64. `/tmp/TTC78KineticSixthClosedHead.lean`

All eighty kinetic/surplus sources remain UNCOMPILED, with no axiom audits. The chain now targets the complete minor coefficients fourteen/thirteen, native slope coefficients fifteen/fourteen and square transfer, the general coefficient response of the source operator, the all-order fifth jet/reflection construction, the residual's actual next canonical coefficient, and its complete kinetic monotonicity and quadratic-mass reserve. Sources58..60 supply the complete fifth even split, full odd M13 and native S14, then actual p14. Source61 prepares the resulting strict positivity of the complete absorbed q7 on StrictCoarseCone. Sources62/63 prepare the full Q6 coefficient and exact auxiliary-mass concavity; its endpoint signs remain open. Sources64/65 retain complete M12/S13 zero components;66..70 prepare the complete sixth first-U and seventh zero native recurrences and source identification, including their seed corrections and the required geometric term. Sources71..75 supply projected reflections, full M11_one/M12_two and the first-U response of actual S12. Source76 supplies the complete sixth transverse forcing, its two highest polynomial solutions and full sixth/seventh scalar corrections. Sources77/78 supply the entire sixth U³ closed recurrence, its exceptional seed and literal third-transverse source identity. Sources79/80 supply the complete sixth U⁵ component and full all-order native sixth head. These hand derivations still require Lean audit. Positivity of all lower residual terms and of the full interior source remains OPEN. No source-coordinate division is used. The generic even-reflection third/fourth-head closed formulas still need proofs beyond the five actual moments. No certificate is retired or promoted until direct serial `lake --old env lean` audits and survivor integration succeed.

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

The factor M² in the odd real component includes the extra factor (a+cE); omitting it would corrupt q7. A paired induction using the existing exact real/imaginary recurrence proves the displayed candidate formulas on paper. The two independent symbolic derivations agree. Source44 now prepares the all-order second-head induction and complete canonical coefficient seven for degree-seventeen polynomials. Source45 connects the absorbed coefficient to the actual source, with no extra sign premise: for every real u,k,z, its native expression is

    q7(u²,k,z)=(-1/9)^7*u^13*(S14
      +(z+7b)*u*S15+(7a+8bz+111b²/4)*u²*S16
      +((7a+143b²/4)*z+56ab+82b³)*u³*S17),

where a=boundaryA(u²,k), b=boundaryB(k), and each S_j is the complete explicit native coefficient evaluated at (U,K,J)=(u,k,0). The all-order source transfer is `p_(n+1)(u²,k)=u^n*S_(n+1)(u,k)`, including u=0. Every source degree premise is discharged by the existing prepared degree theorem. All these sources remain UNCOMPILED; the next hard problem is the sign of this entire expression and then of the full residual on the physical cone. No sign is asserted here.

There is a further symbolic cancellation to use in that sign analysis. In the g0 fifth-head recurrence, the apparent Y⁴ forcing coefficient is

    18*144*(n-1)(2n-3)(n-2)
      +72*(n-2)*(-72n²+180n-108)=0.

Thus g0 has Y-degree at most three at every order, starting from zero; the n=3 endpoint correction has only Y-degree one. This is a paper invariant, not yet a Lean theorem. The highest Y⁵ coefficient of g4 is compatible with `(64/3)*n(n-1)(n-2)(n-3)`, whose Euler recurrence also checks symbolically. These cancellations target the full q7 source expression; they do not justify retaining only its U=0 part or omitting either physical constraint.

## Log

- Current checkpoint: C77 rows63,64,65 closed all37 strict coefficient signs and universal Fin37 capstones, standard3. Rows0..65 and96 closed; sole cell227 continues66Columns. Sources56..61 prepared and sources54/55 repaired for the finite-difference error documented below. All61 C78 kinetic/surplus sources remain UNCOMPILED; static scans and final row65 log verification are recorded in the parent working log. No full build, second Lean process, raised limits, numerical sampling, CAS, external coefficient arithmetic, production promotion or no-go retirement. Corpus `fifth_mixed_sign` terminalexit0, partial=false, index1245119/coverage1245125, complete65904-file inventory; mostly pending/stale/source-only compiler metadata, background refresh incomplete, semantic coverage unmeasured. Every candidate/source/idea/ingredient section inspected. Reflection symmetry or an RH-assuming Gram representation does not discharge the actual source sign. No exhaustive novelty claim.

### 2026-10-05 — Complete final fifth-reflection component

Hand derivation, awaiting Lean audit. The U⁴ component of the normalized fifth reflection has regular part `e4(n)`:

    [Y⁵]e4=(-n⁴+10n³-38n²+65n-42)/162,
    [Y⁴]e4=(4n⁵-46n⁴+230n³-653n²+1101n-897)/324,
    [Y³]e4=(-2n⁶+26n⁵-158n⁴+578n³-1302n²+1675n-1236)/216,
    [Y²]e4=(4n⁷-58n⁶+418n⁵-1932n⁴+5784n³-10199n²+8353n-3819)/1296,
    [Y]e4=(-n⁸+16n⁷-136n⁶+786n⁵-3129n⁴+7736n³-10381n²+5541n-792)/2592.

The five actual moments add ALL four corrections:

    delta_n2*((25/108)Y⁴+(49/36)Y³+(791/432)Y²+(65/144)Y),
    delta_n4*((4/27)Y⁴+(2/27)Y³+(491/108)Y²+35/48),
    delta_n6*(-(80/9)Y³+(260/9)Y²),
    delta_n8*((2240/27)Y²).

At n=4, the independent full source expression has U⁴ coefficient

    -768Y⁵+9408Y⁴-36096Y³+62160Y²-49824Y+15120

before division by20736. Its apparent Y⁶ cancels exactly. It agrees with the stated regular part and correction. This completes the hand expressions needed for every even part of the fifth reflection.

Continuing with ALL five actual moments gives

    S(e4)=-(248/27)Y⁵+(5426/27)Y⁴-(42286/27)Y³
           +(273163/54)Y²-(704443/108)Y,
    W(e4)=-(64/27)Y⁵+(9433/108)Y⁴-(101261/108)Y³
           +(475213/144)Y²-(2081405/432)Y-35/12,
    cross(f,e4)=-(1984/81)Y⁷+(46480/81)Y⁶-(451484/81)Y⁵
                 +(2307784/81)Y⁴-(5685803/81)Y³+(2081405/27)Y²+(140/3)Y,
    cross(t2,d3)=-(128/27)Y⁷-(8512/81)Y⁶+(260260/81)Y⁵
                  -(1404784/81)Y⁴+(2815660/81)Y³-(272164/9)Y²-(110365/36)Y,
    Hdir(f,d3)=Y²*((256/3)Y⁶-(83008/27)Y⁵+(563008/27)Y⁴
                   -(517472/9)Y³+(1010048/27)Y²+(125588/9)Y),
    Hdir(t2,f)=-(11776/27)Y⁸+(83840/27)Y⁷-10640Y⁶
                +(221296/9)Y⁵-(23936/3)Y⁴-8916Y³-6285Y².

Again the apparent Y⁸ term cancels only after both cubic contributions are retained. The resulting COMPLETE last minor component is

    L5=Y²*((151040/27)Y⁵-(1040624/27)Y⁴+(1500176/9)Y³
            -(4091732/9)Y²+(1671436/3)Y-89830/3).

The full source response gives

    27R4=-9185280Y⁶+24171264Y⁵-48849024Y⁴-7580736Y³
          +929795328Y²-2067587856Y+79062480.

For the final neutral-face bracket, `b=(7-Y)/9` gives

    8b/3+111b²/4=(37Y²-550Y+2037)/108,
    143b²/12+82b³=(Y-7)²*(2725-328Y)/2916.

Substitution into the complete N2 yields

    243N2=-140238848Y⁶+747549696Y⁵-1087319424Y⁴-1662850624Y³
           +16966444128Y²-39850337232Y+1267896240.

With x=Y-4, its negative completion is

    -243N2=140238848x⁶+2618182656x⁵+19793649024x⁴+78957735488x³
            +167455798944x²+167053257936x+80373991824.

All coefficients are positive. Thus N2<0 for Y>=4 on paper. Together with the corrected N0 and complete N1, `Neutral=(-1/9)^7*12^18*V^7*Y²*(N0+V*N1+V²*N2)>0` for V>0,Y>=4. The previously derived two positive reserves then give the COMPLETE absorbed q7>0 on StrictCoarseCone. This is a dependency-complete HAND derivation, NOT a Lean result: all source identities, native even/odd incidence and exact arithmetic need kernel audit. No sign premise was added. The positivity of the full residual, including every lower coefficient, remains OPEN.

### 2026-10-05 — Remaining fifth reflection: complete middle component

New hand derivation, UNVERIFIED in Lean. The U² component of the normalized fifth reflection has regular part `e2(n)` with coefficients

    [Y⁵]e2=(n²-5n+6)/6,
    [Y⁴]e2=(n⁴-13n³+54n²-98n+83)/6,
    [Y³]e2=(-8n⁵+155n⁴-902n³+2440n²-3179n+2250)/72,
    [Y²]e2=(-n⁶-31n⁵+377n⁴-1660n³+3239n²-2326n+999)/72,
    [Y]e2=(4n⁷-18n⁶-110n⁵+1233n⁴-4148n³+6147n²-2964n+216)/288.

The actual five moments add all three corrections:

    delta_n2*(-(5/2)Y⁴-(55/6)Y³-(111/8)Y²-(35/8)Y),
    delta_n4*((8/3)Y⁴-(124/9)Y³-(523/18)Y²-95/8),
    delta_n6*(-80Y³-(700/3)Y²).

The independent n=4 source expression `2*A0*E4-8*B1*D3+6*C2²` has U² coefficient

    6912Y⁵-17280Y⁴+386496Y³-1192608Y²+1156032Y-246240

before division by20736; it agrees with the regular part and stated correction.

**Correction learned during the full mixed calculation:** for `S(d)=d10-2d8+d6`, `W(d)=d10-4d8+6d6-4d4+d2`, `T(d)=d8-3d6+3d4-d2`, the actual identity is

    cross(t0,d)=e*S(d)+(24Y²+156Y)*W(d)-96Y*T(d),
    e=-4Y³-9Y²-45/4.

The previous first-component derivation incorrectly used `e*W(d)`. Its old cross(t0,d1), L1, R0 and N0 values were INVALID, and have been corrected below and in sources54/55. The corrected N0 remains negative for Y>=1. An independent substitution of the actual t2 finite differences recovers the earlier source49 `cross(t0,t2)` exactly, so this error does not alter e2/e4, S15, r15 or the kinetic monotonicity/mass-reserve identities. Everything remains unaudited in Lean.

The complete five-moment middle calculation now gives

    S(e2)=(4/3)Y⁵+(520/3)Y⁴-(676/3)Y³-13489Y²+(185743/4)Y,
    W(e2)=(305/6)Y⁴-(15973/18)Y³-(520823/72)Y²+(228797/8)Y+95/2,
    cross(f,e2)=(32/9)Y⁷+(4160/9)Y⁶-(12728/9)Y⁵-(195952/9)Y⁴
                +(2156104/9)Y³-457594Y²-760Y,
    cross(t0,d3)=-(128/3)Y⁷+(6896/9)Y⁶-(13436/3)Y⁵+(116048/9)Y⁴
                 +50640Y³-(444397/3)Y²+(110365/4)Y,
    cross(t2,d1)=-(2336/9)Y⁶+(84956/9)Y⁵-(101308/9)Y⁴
                 -(632006/3)Y³+338761Y²+(37635/4)Y,
    Hdir(f,d1)=(256/3)Y⁸-(20416/3)Y⁷+28352Y⁶+(83744/3)Y⁵
                -314112Y⁴+245100Y³,
    mix(t0,t2;f)=-(1664/3)Y⁸+(21248/3)Y⁷-(31712/3)Y⁶
                 -(213008/3)Y⁵-(127328/3)Y⁴-103356Y³+91860Y².

Both cubic contributions are essential: together they cancel the apparent Y⁸ term of the quadratic contribution. The resulting COMPLETE middle minor component is

    L3=Y²*((34048/3)Y⁵+(74336/3)Y⁴-198528Y³+1311016Y²-3345328Y+343020).

Applying the full source response gives

    R2=-643072Y⁶-3986944Y⁵+1262336Y⁴-26730624Y³
        +8651520Y²+404298720Y-32832000.

Consequently the middle neutral-face bracket satisfies

    3N1=-2750464Y⁶-11581696Y⁵+44312064Y⁴-65694208Y³
         -35985504Y²+1707705504Y-165252960.

With x=Y-4, its exact negative completion is

    -3N1=2750464x⁶+77592832x⁵+847433216x⁴+4730366464x³
          +14544425056x²+22113033824x+9896297184.

Thus the full middle bracket is negative for Y>=4 on paper. These hand identities require Lean audit. The last V² bracket N2 remains OPEN, and the full residual does not follow from q7 alone. No numerical sampling, CAS or external coefficient arithmetic was used.

### 2026-10-05 — Two exact reserves and the remaining face

The next head also increases with the quadratic mass. Holding the full source polynomial p and b fixed, its exact mass difference is

    q7(a,z)-q7(0,z)=-63*a*q8(z).

Thus, with `N(v,k)=q7(0,1/3)`, the complete source identity is

    q7(a,z)-N(v,k)=(1/9)^7*(1/3-z)*r15-63*a*q8(1/3).

Both terms are strictly positive on `StrictCoarseCone`. This is a paper deduction; source53 prepares this exact identity and actual-cone strict comparison. It does not assume or assert the still-missing sign of N.

For the remaining face, the full U-independent normalized fifth reflection has regular part `e0(n)`:

    [Y⁴]e0=-(3/4)*(n²-5n+11),
    [Y³]e0=(-3n⁴+34n³-174n²+290n-126)/8,
    [Y²]e0=(-4n⁵+6n⁴+204n³-471n²+139n-99)/16,
    [Y]e0=-n⁶/24-7n⁵/20+41n⁴/96+27n³/8-383n²/48+731n/160.

The five actual moments retain the corrections

    delta_n2*((15/4)Y⁴+(9/4)Y³+(105/16)Y²+(45/16)Y),
    delta_n4*(12Y⁴+62Y³+(261/4)Y²+765/16).

The n=4 expression agrees independently with `2*A0*E4+6*C2²` at U=0. From the complete five moments, hand finite-difference algebra gives

    cross(f,e0)=-16Y⁶-684Y⁵-12920Y⁴-44525Y³+205203Y²+3060Y,
    cross(t0,d1)=496Y⁶+4084Y⁵-3316Y⁴+39454Y³+109434Y²-(338715/4)Y,
    Hdir(t0,f)=1920Y⁷-2640Y⁶-170496Y⁵-189888Y⁴+659376Y³-317655Y².

Consequently, writing `M13=12^18*(U*L1+U³*L3+U⁵*L5)`, the full first component is

    L1=Y²*(3840Y⁵+43440Y⁴-24336Y³+129036Y²+3116268Y-661770).

Source54 prepares the exact fifth-reflection projection and these three component identities. Its identification with the U-linear coefficient of M13 is currently a PAPER consequence of the complete source42 formula; no partial projection is substituted for the full source sign.

The exact source response then gives the U-linear native S14 component `12^18*U*Y²*R0`, where

    R0=-202752Y⁶-3085056Y⁵-9523584Y⁴-29234880Y³
       -176656896Y²-302469552Y+58300560.

With `M13` as above and `e0,e2,d` the complete components already recorded, its derivation is

    Y²*R0=(2Y-3)*(12Y*d_Y(L1)+36(Y-1)e2+56(Y+1)e0
                   +90(Y²-4Y-1)d)-144Y*L1.

After the neutral upper-face substitution, the constant-in-V bracket becomes

    R0+(52-7Y)*G0/9=
      -245760Y⁶-3399936Y⁵-7262592Y⁴-16273728Y³
      -142642944Y²-267444720Y+73126800.

It is negative for Y>=1: write its last two terms as `-267444720*(Y-1)-194317920`. This is still unaudited hand algebra. These displayed coefficients include the subsequent correction of the second/fourth finite-difference mix-up in `cross(t0,d1)`; the earlier values are invalid. The complete normalized neutral bracket has TWO further components, multiplying V and V²; they require L3 and L5 from the full fifth reflection and both cubic directional terms. Deriving and signing those complete components is the next hard target. Only then can the neutral-face sign imply q7 positivity; the lower residual coefficients and full interior sign remain open.

Source55 prepares the exact source identifications `UZero(partial_U M13)=12^18*L1` and `UZero(partial_U S14)=12^18*Y²*R0`, retaining all terms before projection, and the negative first neutral component. No Lean audit has run. For continuing the complete calculation, define `mix(t0,t2;f)=Hdir(t0+t2,f)-Hdir(t0,f)-Hdir(t2,f)`. Then the two remaining minor components are exactly

    L3=12Y*(cross(f,E2)+cross(t0,d3)+cross(t2,d1))
         -Hdir(f,d1)-mix(t0,t2;f),
    L5=12Y*(cross(f,E4)+cross(t2,d3))-Hdir(f,d3)-Hdir(t2,f).

Here E2,E4 are the remaining even components of the COMPLETE normalized fifth reflection, not the earlier M14 components. If `L3=Y²*l3` and `L5=Y²*l5`, the source response gives

    R2=(2Y-3)*(24l3+12Y*l3'+72(Y-1)*E4_minor+(52Y+60)*E2_minor
               +90(Y²-4Y-1)*B-10(Y-1)²*A)-144Y*l3,
    R4=(2Y-3)*(24l5+12Y*l5'+(48Y+64)*E4_minor-10(Y-1)²*B)-144Y*l5.

With b=(7-Y)/9, the two remaining neutral-face brackets are

    N1=R2+(52-7Y)*G2/9+(8b/3+111b²/4)*D0,
    N2=R4+(52-7Y)*G4/9+(8b/3+111b²/4)*D1+(143b²/12+82b³)*C17.

Target their full signs for Y>=19/4 and V>0; a stronger componentwise sign for Y>=4 is only a conjecture. No omitted component is presumed negative.

- Checkpoint: C77 rows59,60,61,62 completed all five audit stages, all37 strict signs plus universal Fin37 capstones, standard3. Rows0..62 and96 closed; cell227 remains live at63Columns. Sources46..55 are UNCOMPILED; static forbidden-declaration/raised-limit scans46..54 empty (source55 scan follows in the working log). No production edits or promotion. Corpus `boundary_mass_positive` completed at generation1244603, partial=false but compiler metadata mostly pending/stale/source-only, coverage snapshot older generation and refresh incomplete; every result category inspected. Its category/filter boundary suggestions have no connection to the actual mass. Corpus `upper_face_sign` partial=true, generation1244745/coverage1244745 with complete65894-file inventory and refresh incomplete; every result category inspected. Positive unrelated Hankel sources do not identify the complete reflected source here. No exhaustive novelty claim.

### 2026-10-05 — Complete derivative of the next residual head

PAPER DEDUCTIONS ONLY; sources46..48 and the following identities have not yet been audited. The complete five reflected source moments give `e_i=Y²*E_i` for the coefficient `M14=12^18*(e0+U²e2+U⁴e4)`:

    E0=-36*(32Y⁴+408Y³+756Y²+858Y+945),
    E2=-6144Y⁴-26176Y³+77376Y²-289104Y+40320,
    E4=-4480Y⁴+(185248/9)Y³-(186448/3)Y²+102136Y-4060.

Here the exact component identities against source37 are

    cross(f,d1)=-(992/3)Y⁵-(5936/3)Y⁴+(49496/3)Y³-33100Y²,
    cross(t0,t2)=(64/3)Y⁶-400Y⁵+(272/3)Y⁴-5040Y³+1104Y²+4905Y,
    Hdir(f,t0)=Y²*(256Y⁵-2624Y⁴+3520Y³+60128Y²-94848Y+18540),
    M(t2)=(64/27)Y⁶+(1360/27)Y⁵-(59864/27)Y⁴+(32420/3)Y³-(31846/3)Y²-510Y,
    cross(f,d3)=(256/9)Y⁶-(15520/27)Y⁵+(36464/9)Y⁴-(414664/27)Y³+(57796/3)Y²,
    Hdir(f,t2)=Y²*((3328/9)Y⁵-(5440/3)Y⁴+(4288/3)Y³+(67808/9)Y²+1664Y-2060).

The complete native slope response then yields `s_i=Y²*G_i`:

    G0=55296Y⁵+815616Y⁴+3151872Y³+6749568Y²+6407424Y+2566080,
    G2=319488Y⁵+2405376Y⁴+2351616Y³+4891392Y²+28636416Y-3343680,
    G4=(751616/3)Y⁵-181760Y⁴-(239104/3)Y³+2317184Y²-12255744Y+339840.

Thus `p15=12^18*V⁷*Y²*(G0+V*G2+V²*G4)`, including every source term. With `b=(7-Y)/9`, `C17=24576Y²(Y+3)` and the already prepared complete D0,D1,

    r15/(12^18*V⁷*Y²)=G0+V*H1+V²*(H2+7a*C17),
    H1=G2+8b*D0,
    H2=G4+8b*D1+(143/4)b²*C17.

Hand algebra gives the positive decompositions, for `x=Y-4`:

    H1=385024Y³*(Y²-16)+2528256Y²*(Y²-16)
       +5743104Y³+36410112Y²+27484416*(Y-1)+23173056,
    27H2=9809920x⁵+171972096x⁴+1153700352x³
         +3781531264x²+5866707456x+2831732352.

Consequently the complete `r15` is strictly positive for `V>0,Y>=4,a>=0`, and the complete `q7` is strictly decreasing in z since its affine slope is `(-1/9)^7*r15`. These sign deductions still require Lean audit and actual-source transfer. No source-sign premise is being added: the current `StrictCoarseCone` supplies `k>5/4`, `v>0`, and `r=k²(9-v)<361/25`. Direct expansion gives

    648*k*a=72*(k-5/4)²+(108-6r)*(k-5/4)+(45-r)/2.

Every right-hand term is nonnegative and the last is positive, so `a>0` follows from the existing cone itself. This reduces the next residual coefficient sign to its upper face `q7(v,k,1/3)`, whose sign is STILL OPEN. Positivity of q7 alone would not prove positivity of the full residual.

The full fifth head has also been prepared in source47 (`TTC78KineticFifthClosedHead`) and all five reflected instances in source48 (`TTC78KineticFifthReflectionFive`). The fifth reflection regular baseline is `46080U²Y²*(-3*(12Y+35)+U²*(13-4Y))` at n=6 and `1720320U⁴Y²` at n=8; n=4 retains the entire exceptional endpoint. These supply p14 for the upper-face problem. No sampling, CAS, or external coefficient arithmetic was used. C77 rows0..60 and96 now closed; sole foreground cell227 continues row61. All new C78 sources remain UNCOMPILED.

### 2026-10-05 — Closed fifth head for the residual sign problem

The complete fifth-head recurrence has now been solved symbolically in all three even powers of U. These formulas are paper deductions pending Lean audit. Write the regular core as `G(n)=g0(n)+U²*g2(n)+U⁴*g4(n)`. For n>=4 the literal normalized fifth coefficient is `G(n)+delta_(n,4)*(-92340+86940U²-10395U⁴)`. The recursive seed at n=3 is zero; its regular core is `Y*(92340-81810U²+9450U⁴)` and must be subtracted at that seed.

The U-independent core is `g0=A0*Y³+B0*Y²+C0*Y`, with

    A0=324(n-3)(n-2)(4n²-8n+19),
    B0=108(n-3)(8n⁴+2n³-71n²-101n-63),
    C0=(9/5)n(n-1)(80n⁴+152n³-143n²-173n-228).

The middle core is `g2=A2*Y⁴+B2*Y³+C2*Y²+D2*Y`, with

    A2=-288(n-1)(n-2)(n-3)(2n-3),
    B2=24(n-3)(n-2)(16n³-66n²-28n-327),
    C2=6(n-3)(8n⁵+84n⁴-22n³+627n²+815n+2268),
    D2=3(-16n⁷+52n⁶+20n⁵-377n⁴+62n³-368n²-669n-864).

The final core is `g4=A4*Y⁵+B4*Y⁴+C4*Y³+D4*Y²+E4*Y`, with

    A4=(64/3)n(n-1)(n-2)(n-3),
    B4=-(32/3)(n-1)(n-2)(n-3)(4n²+21),
    C4=4(n-3)(n-2)(8n⁴-8n³+42n²+38n+295),
    D4=-(2/3)(n-3)(16n⁶-48n⁵+64n⁴+136n³+655n²+653n+3294),
    E4=(16n⁸-96n⁷+136n⁶+304n⁵-191n⁴+194n³+3591n²+3534n+12672)/12.

Each Y-coefficient solves the exact scalar recurrence `a(n+1)-j*a(n)=forcing_j(n)`, where j is its Y-degree. The apparent Y⁴ term in g0 and Y⁵ term in g2 both cancel. The Y-linear equations include the source endpoint correction: core values at n=3 are respectively `92340Y`, `-81810Y`, and `9450Y`. The resulting actual n=4 components are

    g0_actual(4)=33048Y³+61884Y²+583200Y-92340,
    g2_actual(4)=-8640Y⁴-22608Y³+263088Y²-391932Y+86940,
    g4_actual(4)=512Y⁵-5440Y⁴+21240Y³-38572Y²+32654Y-10395.

These match an independent application of the full constant-coordinate source operator to the complete third jet on paper. Source46, `/tmp/TTC78KineticFifthZeroHead.lean`, prepares the exact U=0 projection and its closed all-order formula. Full three-component source closure is the next prepared proof target. The mathematical task remains the sign of the resulting complete q7 on the physical cone, not the sign of an isolated component. No numerical samples or external coefficient calculations were used.

- 2026-10-05 — Rows56,57,58 completed all five foreground audit stages; each has all37 strict signs and a universal Fin37 capstone using only standard3. Final row57/58 logs read. Sole cell227 continues59Columns; global/source integration remains pending. Prepared sources32..45, all UNCOMPILED: complete fourth reflection/minor14/slope15 transfer; even decomposition; generic coefficient response; exact recursive fifth head with exceptional third jet; all five reflected Cauchy pairs; full minor13/slope14; all-order second quadratic heads; actual absorbed q7 coefficient. No source sign added. Static forbidden-declaration/raised-limit scans empty. Made existing helper lemmas public in sources22,24,26 for reuse; no production edits, umbrella build, or no-go retirement. Corpus queries `minor_fourteen_api`, `native_constant_response_api`, `even_minor_source_search`, `transverse_coeff_response_search`, `quadratic_next_heads_search` all terminalexit0 and every candidate/source/idea/ingredient section inspected. All partial, compiler metadata mostly pending/stale/source-only, background refresh incomplete; respective index generations1243502,1243625,1243733,1243817,1243952. Complete inventories reported where available; no exhaustive novelty claim. New next-head formulas rechecked through two symbolic derivations. Full residual/physical-cone sign, source quadratic, fourthgap/join, all-rank closure and RH remain open.

- 2026-10-05 — Derived symbolically during C77 row51. Corpus `full_quotient_attack` exited0, partial index1242423/coverage1242430 with complete65835-file inventory, compiler mostly pending/stale and background refresh incomplete. `third_jet_head_api` exited0, partial index1242505 with coverage pending and deadline/refresh limitations. All candidate/source/idea/ingredient sections inspected. The supplied results contain source recurrence/incidence and fixed reflection identities, not the required all-order third coefficient. No exhaustive novelty claim. No numerical sampling or external coefficient arithmetic. The next-coefficient expressions above need independent algebra and Lean audits before they are treated as established.
- 2026-10-05 — Second hand-algebra pass rederived the third-jet recurrence, reflected endpoint corrections, determinant cross term, native slope coefficient and final surplus sign completion. It agrees with the displayed formulas; this is not a Lean audit. Prepared the four sources listed above. The native recurrence retains the entire `integerStep` operator and the exceptional `270-105u²`; reflected coefficient reconstruction retains all Cauchy terms; the five-moment proof targets literal complete source coefficients; the next-minor proof uses the full quadratic-plus-cubic remainder. No sign premise is introduced. Static forbidden-declaration/raised-limit scans empty. C77 row51 completed all five stages, with all37 strict signs and the universal Fin37 capstone using only standard foundational axioms; sole cell227 continues row52. No second Lean, production promotion, or no-go retirement.
- 2026-10-05 — Prepared the seven additional sources above, including a full source-to-canonical-polynomial-to-source evaluation chain. Rechecked the displayed native slope D0/D1 by differentiating the complete minor head and retaining the transverse U term. The all-order quadratic power induction supplies the exact canonical highest coefficient independently of finite source truncation. Static forbidden-declaration/raised-limit scans empty; all new files still unaudited. Corpus `next_slope_affine_api` exited0, partial1242829/coverage1242833, complete65844-file inventory; `surplus_quadratic_api` exited0, partial1242929, complete65846-file inventory. Compiler metadata mostly pending/stale; refresh incomplete; all result categories inspected. C77 row52 closed all37 signs plus its universal capstone with standard3; row53 normalization stages subsequently passed. The square-absorption conjecture above is the next proposed attack, not an established positivity result.
- 2026-10-05 — Added four prepared modules: the complete source square comparison and degree-fifteen residual; exact W-field/gauged source decomposition; all-order fourth native jet head with its exceptional third jet; and full fourth reflected Cauchy coefficient. Extended `TTC78SurplusNormalHead` with component degree bounds. A second symbolic pass checked every fourth-head coefficient recurrence and its initial correction; this is not a Lean audit. Residual sign and next minor/slope coefficients remain open. Current frontier map still lists the global interior gap. Corpus `residual_square_structure` exited0 partial1243141/coverage1243147, complete65845-file inventory; `shifted_kinetic_invariant` exited0 partial1243268 with coverage pending/deadline; lexical `integerLie integerJet --any` returned actual integer source declarations. All result categories inspected, no exhaustive novelty claim. C77 row54 closed all37 signs plus its universal capstone with standard3; row55 Columns passed, remaining stages live. No second Lean, raised limits, numerical sampling, external coefficient arithmetic, production promotion, or no-go retirement.
