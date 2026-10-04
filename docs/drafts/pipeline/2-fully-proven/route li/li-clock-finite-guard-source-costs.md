# Actual finite guarded-clock source costs

- **ID:** li-clock-finite-guard-source-costs
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** li-clock-integrated-source-sign; literal single-Xi theta source.
- **Statement:** Complete matched-dilation positivity, sharp all-positive-clock quarter-age kernel boundary, exact signed-history cost localization, and strict finite guarded-clock upper envelope.

## Goal and status

[PROVED HERE] Positive survivors F3–F11 below have dependency-closed paper proofs and two complete mathematical reviews. They isolate the actual early negative costs. The relative finite-clock source inequality OPEN-FINITE in F12 remains OPEN, as do M15, guarded-zero exclusion and RH. No guarded-zero witness, effective cutoff or branch selection is supplied.

- [x] 0 → 1: literal source and complete signed contracts fixed.
- [x] 1 → 2: full421 paper/root review plus full283 independent source/corpus audit PASS.
- [ ] 2 → 3: exact348-line formal design has dual complete PASS: all26 contracts,24 private groups and22 paper mappings. New survivor Lean formalization remains pending its primitive/correlation prerequisites.
- [ ] 3 → 4: publication packet pending.

## Scope and dependencies

Retain same R0, full source moment rows, both factorials and full-copy P/D. Quarter-age sharpness concerns ALL positive clocks, not an optimal threshold restricted to guarded clocks after20. Lower early boundary cancels only in the exact full decomposition. Previous terminal-history, score-reserve and primitive-family proofs are dependencies on paper; their uninstalled planned Lean APIs are not imports. ScoreMeasure14, SourceEnvelope21, Profile18 and TerminalAnalytic10 are now locally FINAL. StageA still waits full Primitive18 and its transitive Correlation12 gate; StageB also waits StageA FINAL.

This is positive progress, not retirement of the finite-clock route. Strongest new insight is the exact split into nonnegative early costs and a strictly positive favorable cost; absolute cost envelopes do not establish the relative budget.

## Frozen evidence and reviews

Paper421 SHA `fd18aa2dcc4e8b729c5d173e157d68a9fce84b09ac2c6122ce06cbf6457f85c9`; evidence JSON SHA `f4e690419c3ade5c94ba78d83bb24dfa849c4ed8923e882f3645c59e4ecf9e13`. Independent audit283 SHA `888e5133d0118704e295773d139b913502944f21817472623ea6e8df1c80ac2c`; metadata3310 SHA `4be1b42a36da051df45ecb5b8ef8ebcdc1e01639564aafc7049432dbdacf3d33`. Full raw research records123 reviewed by author and independent reviewer, reconstructed against both saved captures; deep query partial, compiler metadata source-only. No exhaustive novelty claim. Root full paper/independent certificate and all artifact/source pin checks accepted; root does not claim a new manual read of every nested raw field.

2026-10-01 — Dual full paper acceptance; paper-only exact formal design assigned. No tree Lean changes or RH conclusion.

2026-10-01 — Exact formal plan348 `417fa6b5e3ff9e38a186895121c6fb42d526e8fa88cc48305296c187c91b1959` and metadata931 `0d1be115d9dabf2e9d430ecbc18a0b984302663f7affc5cd3eaa0fbab551d1f7` have dual full design PASS. Independent Pole150 `ecc01e3dfe43204f898d044c36d752e86afa918c58d6fa16797855c0deb583fc` and metadata1541 `a55abea369c01fceae6b1271d55f6b63b85c7fe0e83257d68706993472e069b6`; root read every certificate line and verified every contract/group/mapping/pin/span. Audit A08 table typo `C1(un*t)` means `C1(u*t)`, as in its exact contracts and complete following derivation; no mathematical change. No finiteguard implementation release or relative-budget proof follows.

## Frozen complete paper421

# Literal finite guarded-zero source attack: reciprocal-lag transfer and early signed cost

**PAPER-ONLY outcome: actual M15 remains OPEN.** The complete literal source gives a positive matched-dilation history, a sharp quarter-age sign boundary for its positive primitive discrepancy, and an exact finite-clock positive/negative cost decomposition. None supplies the remaining adaptive upper comparison. No guarded zero, effective cutoff, RH branch or Lean theorem is asserted.

Chosen mechanism, after corpus-first searches: exploit the exact variable-weight primitive `g(r)=rT(r)=B_2(r)/r`, rather than the already-excluded nonnegative constant primitive mixture. Match its integral-of-dilations representation to the ACTUAL factor-one Volterra law, retain the mismatch, then use every positive coefficient of the complete actual discrepancy to localize its negative history cost. No paired-eta model, artificial positive source, finite moment truncation, inverse positivity or hypothetical all-log-moment sign is substituted.

## Frozen inputs, provenance and source admission

The complete prior paper proofs are reused only at these exact hashes. Their supplied full independent certificates are part of the dependency ledger; new proofs below are written independently.

|Input|Lines|SHA256 / review|
|---|---:|---|
|Literal terminal-history paper|295|`b19ac9e238d86ce07a3c805c21b6dcaccd9ed612437509f03fe25dcadfe9bae3`|
|Own complete terminal audit|132|`57f550cb0a9dba97d506d6a46a82903d383f12238152cc34750227f6ccf938cb`|
|Literal score-correlation paper|373|`7454b4a27be838bc10eb4608872d2eda9cd471c90fd4956f24bfe5e3d8157d3d`|
|Own complete score audit|169|`2d8bc7203919872897fb49a33c23e07428435d1abbb43f1487b5d1cabfe9f22f`|
|Literal score-budget paper|273|`9b6cac0c746eae68e5c60496bc88339f89928c57779935be6540b4553a1a0e87`|
|Pole complete B1–B11/source/corpus audit|182|`756964f2e29967ddf5262618a4349aa1dcd0674fc2e26258f73e830b69764c6a`|
|Own complete causal-history paper|608|`815457a785a910206e21ad479fad5c09c1834506f6e11ac2e77967dea374c9fc`|
|Approved Score plan, PROSPECTIVE beyond finalized measure|817|`6da9fb115733ce2872f2ba5fb36e379a6eb49d4a0f3559eafa0935a7ee8c7d6b`|
|Approved Terminal plan, PROSPECTIVE|432|`e634d7e2a53068ccafb3e88999e123c5b1b6d7dddb934b2c0c5ce0c4c3a0d77e`|

Paths, complete source hashes and inspected ranges are in the accompanying evidence JSON. `rh-current-frontier-map.md` relevant Li block and `STATUS.md` relevant current Li entries retain actual RH/M15 as OPEN. Root's concurrent card reconciliation changes headers/locations only: frozen295+132,373+169,273 and608 mathematical inputs above remain unchanged. No changed whole-card hash is silently treated as an unchanged mathematical source.

F1. Literal objects and whole-source regularity. Write

    R_j = 2 integral_(0,infinity) x^(2j) thetaCuspFullSource(x) dx,
    nu_j = R_j/R_0, b_j = nu_j/((2j)!)^2,
    B(t) = sum_(j>=0) b_j t^(2j), K=B',
    P(t) = liEvenCrossActualClockPrimitive(t),
    D(t) = integral_0^t P(s)/s ds, with value0 at s=0.

ONE positive `R_0` normalizes every row: `nu_0=1`, all `nu_j>0`. Spectral absolute mass `A=xiShiftAbsoluteMass 0>0` is distinct from `R_0`. The actual all-order Ward bound is `nu_j<=(32/303)^j j!`, hence `b_j<=(32/303)^j/j!`. On each compact radius R, every complete B row is bounded by `((32/303)R^2)^j/j!`. Polynomial degree factors are summable as well: shift factorial indices, or enlarge radius to `max(1,R+1)` and absorb each fixed degree power into a geometric factor. Consequently all finite-order derivatives, the primitive series and all compact parameter integrals below have uniform absolute majorants BEFORE interchange. No totalized divergent integral is evaluated.

The full-copy cosine primitive is entire and even, with P(0)=P'(0)=0. Its all-copy compact bound is

    |P(s)| <= A s^2 exp(s/300)/2, s>=0.                 (F1a)

The apparent origin division in P(z)/z is removable; it is an entire odd function with leading coefficient `nu_1 z/2`. Its entire primitive D is even, `D(z)=nu_1 z^2/4+O(z^4)`, so it is nonzero. The single-Xi identity `nu_1=M_0>0` has already been fully source-audited; raw and logarithmic normalizers are not doubled. In particular D cannot vanish identically on any nonempty real open interval. Canonical installed D is the same genuine oriented integral, with continuous quotient and real FTC at every clock. Thus `P(s)=sD'(s)` for s>0, with the continuous equality filled at0.

Relevant direct primary body checks: BorelSource17–276 (positive rows, complete factorial envelope, uniform convergence, genuine first derivative); Primitive163–235 (FTC/smoothness/full-copy mass bound and conditional-only RH sign); PrimitiveVolterra27–119 (full source compact IBP and factor ONE); BorelFlattening106–178 (all-order derivative admission, reused complete589 review); HistoryBarrier32–92/251–421 (canonical D/FTC, complete reserve/receiver guards). The nonzero entire-D extension and exact full-copy germ are reused from the unchanged, fully audited terminal295 T1–T3; no merely C-infinity zero-isolation argument is substituted.

For every t>=0 the source identity is

    P(t)+(P*K)(t)=tK(t),                               (F1b)

where `(f*h)(t)=integral_0^t f(s)h(t-s)ds`. This is installed `liEvenCrossActualClockPrimitive_volterra`, factor ONE. The factor-two paired-eta laws returned by corpus searches have a different normalized source and are inapplicable.

## Exact positive family and variable primitive

F2. Let B_0=B and B_(m+1)(t)=integral_0^t B_m(r)dr for natural m. On nonnegative clocks,

    B_m(t)=sum_j b_j (2j)! t^(2j+m)/(2j+m)!,
    C_m(t):=(P*B_m)(t)=tB_m(t)-(m+1)B_(m+1)(t)
      =sum_(j>=1) 2j b_j (2j)! t^(2j+m+1)/(2j+m+1)!
      >=nu_1 t^(m+3)/(m+3)!.                           (F2)

These are reused, source-pure Budget B4a/B4b. For completeness: integrate F1b and use compact signed triangle Fubini to obtain `P*B=tB-B_1`; integrate repeatedly, with `integral_0^t rB_m(r)dr=tB_(m+1)-(B_(m+2))`, to induct. Every compact primitive row has bound `R^m/m!` times the complete B majorant, because `(2j)!/(2j+m)!<=1/m!`. All `C_m(t)>0` for t>0, but this is convolution positivity, not pointwise P positivity.

F3. Define the SAME full score profile and reciprocal-lag kernel

    T(r)=sum_j nu_j r^(2j)/[(2j+2)!(2j)!],
    g(r)=rT(r), g(0)=0.

For r>0, and continuously through r=0,

    g(r)=B_2(r)/r = integral_0^1 B_1(ur)du,
    T(r)=integral_0^1 (1-u)B(ur)du.                    (F3)

Integrate the full absolutely uniform B/B1 series on u in[0,1]. Both identities keep j0; `T(0)=1/2`, `g'(0)=1/2`. The quotient B2/r has a genuine smooth origin filling from its series, not an undefined endpoint. Every g coefficient is positive; `g,g'>=0` on the positive ray.

F4. A matched-dilation positive history. For u>0, substituting v=us in a genuine compact integral gives

    integral_0^t P(us)B_1(u(t-s))ds
      =C_1(ut)/u
      =tB_1(ut)-2B_2(ut)/u
      >=nu_1 u^3 t^4/24.                              (F4a)

At u=0 the original continuous integrand is identically0; the right side has the same continuous limit. The complete two-parameter integrand is continuous on `[0,1]x[0,t]`, hence absolutely L1 before Fubini. Averaging over u yields the unconditional actual-source survivor

    A_dil(t):=integral_0^1 integral_0^t
                    P(us)B_1(u(t-s))ds du
      =sum_(j>=1) 2j b_j t^(2j+2)/[(2j+1)(2j+2)^2]
      >=nu_1 t^4/96>0, t>0.                           (F4b)

This uses the entire actual source, not a proxy. Compact factorial majorants authorize the sum/parameter exchange; there is no improper `1/u` integral without its numerator cancellation.

F5. The literal target is different. F3 and genuine compact Fubini give exactly

    (P*g)(t)=A_dil(t)+C_dil(t),
    C_dil(t)=integral_0^1 integral_0^t
             [P(s)-P(us)]B_1(u(t-s))ds du.             (F5a)

Using `P(us)=s(d/ds)D(us)`, compact IBP at each u, with B1(0)=0 at the upper endpoint, gives

    C_dil(t)=integral_0^1 integral_0^t [D(s)-D(us)]
                     [su B(u(t-s))-B_1(u(t-s))]ds du.  (F5b)

This is regular also at u0. Nonnegative D on its WHOLE preceding history proves neither `D(s)>=D(us)` nor `P(s)>=P(us)`; the remaining kernel is also signed. No such order is an admitted theta-source law. Therefore the positive A_dil is not a sign or upper estimate for literal P*g. Moreover M15 requires an upper budget, not merely positivity of this convolution. The concrete source-correlation mismatch is retained as an unresolved quantity, not renamed as a positivity premise.

F6. The reciprocal weight has an independent exact commutator. For t>0, multiply the literal convolution by t and use t=(t-s)+s:

    (P*g)(t)=C_2(t)/t+(1/t)integral_0^t sP(s)g(t-s)ds,
    integral_0^t sP(s)g(t-s)ds
        =integral_0^t D(s)[s^2g'(t-s)-2sg(t-s)]ds.     (F6)

Both boundaries in the second identity vanish: s^2 at0 and g(0)=0 at t. The positive C2 is source-proved, but the exact correction has no uniform sign from D>=0. Because `rg'(r)>=g(r)`, its kernel is nonnegative for s>=2t/3; this alone does not orient its early part. Thus direct transfer through B2/r fails at a literal signed correction, rather than through an omitted source or convergence admission.

## Full discrepancy and sharp quarter-age localization

F7. Keep the entire positive discrepancy already exposed by Budget B6:

    G(r):=B_1(r)/2-g(r)
      =sum_(j>=1) b_j*j*r^(2j+1)/[(2j+1)(2j+2)].       (F7a)

Every row is positive; `G(0)=G'(0)=0`, and `G(r)>0` for r>0. Its leading term is `nu_1 r^3/48`. Compact derivative majorants from F1 admit termwise differentiation. Hence

    rG'(r)>=3G(r) for r>=0,
    rG'(r)>3G(r) for r>0,                             (F7b)

where strictness uses the retained j2 row (`nu_2>0`), not a discarded-tail assumption. Also

    (P*g)(t)=C_1(t)/2-(P*G)(t).                        (F7c)

The source-specific constant nonnegative primitive-mixture shortcut was already excluded, even for a genuinely convergent countable mixture: g0 forces a0=0, the full O(r^2) mixture tail forces a1=1/2, then the mixture>=B1/2>g. This is reused overlap, not a new retirement or novelty claim. The fractional-depth lead was considered but is not used or asserted as a proved mixture theorem here; no unnecessary Beta/Gamma extension is needed for F3–F12.

F8. Put `H_G(t,s)=sG'(t-s)-G(t-s)`. All clocks below are nonnegative. For `t/4<=s<t`, let r=t-s>0. Then r<=3s and F7b gives

    H_G(t,s)>0;
    H_G(t,t)=0.                                       (F8a)

This includes s=t/4: the cubic row cancels there, but the complete higher rows make the inequality strict. The exact row expansion is

    H_G(t,s)=sum_(j>=1) [b_j*j/((2j+1)(2j+2))]
                          (t-s)^(2j)[(2j+1)s-(t-s)].  (F8b)

No row is omitted. In contrast H_G(t,0)=-G(t)<0 for t>0. The quarter-age constant is sharp for a uniform statement over ALL positive clocks: for each fixed c in[0,1/4),

    H_G(t,ct)/t^3 -> (nu_1/48)(1-c)^2(4c-1)<0
                  as t decreases to0.                (F8c)

This follows from the admitted cubic leading row and derivative remainder O(t^5). It makes no optimal-cutoff assertion restricted to t>20; actual guarded clocks lie there, and a sharper source-specific cutoff on that restricted region remains possible.

F9. Genuine signed-cost decomposition at a guarded history. More generally suppose t>0 and D(s)>=0 for every s in[0,t]. Since P=sD' and G0=0, genuine compact IBP gives

    (P*G)(t)=integral_0^t D(s)H_G(t,s)ds.              (F9a)

The condition D(t)=0 is unnecessary for this identity; no boundary term is hidden. Let `[x]_+=max(x,0)` and define finite nonnegative costs

    N_G(t)=integral_0^(t/4) D(s)[-H_G(t,s)]_+ ds,
    A_G(t)=integral_0^t D(s)[H_G(t,s)]_+ ds.

Every density is continuous on a finite compact, including its positive part, so genuinely L1. F8 shows the COMPLETE negative part is supported in s<t/4; it is not merely bounded by a truncated row. Therefore

    (P*G)(t)=A_G(t)-N_G(t),
    A_G(t)>0, hence (P*G)(t)>-N_G(t).                  (F9b)

Proof of strict positive A_G: D is a nonzero real restriction of an entire function. It cannot vanish throughout the open interval(t/4,t). Under D>=0 it has a strictly positive value there, and continuity gives a smaller positive open interval. F8 is strictly positive there. Their product has strictly positive integral. No effective witness, actual guarded-zero existence or global P sign is required. This strengthens mere positive-profile information to a precise literal-history localization.

F10. Complete norm admissions and quantitative early envelopes. From F1a,

    |D(s)| <= A s^2 exp(s/300)/4, s>=0.                (F10a)

For s>0, bound `|P(u)/u|<=A u exp(u/300)/2` on0<u<=s and integrate; origin0 is continuous, so there is no log divergence. At a nonnegative history, `[-H_G]_+<=G(t-s)<=G(t)` gives

    0<=N_G(t)<=A G(t)t^3 exp(t/1200)/768.              (F10b)

Likewise for any0<=ell<=t put

    L_g(t,ell)=integral_0^ell D(s)[g(t-s)-sg'(t-s)]_+ds,
    A_g(t,ell)=integral_0^ell D(s)[sg'(t-s)-g(t-s)]_+ds.

Then both are genuinely finite and nonnegative, and

    integral_0^ell P(s)g(t-s)ds
       =ell D(ell)g(t-ell)+A_g(t,ell)-L_g(t,ell),
    0<=L_g(t,ell)<=integral_0^ell D(s)g(t-s)ds
       <=A g(t)ell^3 exp(ell/300)/12.                 (F10c)

The endpoint ell may exceed20. Its signed P integral was not assigned the early-source sign; all its boundaries and two positive parts remain exact.

## Complete finite-clock cost bound and missing arithmetic comparison

F11. At a literal guarded clock

    Z(t): t>20, D(t)=0, D(s)>=0 for EVERY s in[0,t],
    ell=K(t)/(4K'(t)), 0<ell<t/4,
    I_U=integral_ell^t sD(s)U(t-s)ds,
    I_K=integral_ell^t D(s)K(t-s)ds,
    V=tK(t)+(K(t)/2)integral_0^ell D(s)ds,
    U(r)=17T(r)+16rT'(r).

All guards follow from literal source curvature, NOT from a free kernel class. Exact Budget B8/Score S12 is

    I_U=16ell D(ell)g(t-ell)+W(t)+8C_1(t)
                   -16(P*G)(t)-16integral_0^ellP(s)g(t-s)ds,
    W(t)=integral_ell^t D(s)(16t-15s)T(t-s)ds>=0.

Substitute F9/F10. The complete lower-boundary term cancels exactly, yielding

    I_U=W(t)+8C_1(t)+16[N_G(t)+L_g(t,ell)]
                          -16[A_G(t)+A_g(t,ell)].     (F11a)

Every displayed component is nonnegative under the literal guard; A_G>0 and C1>0. Thus the ACTUAL finite-clock upper bound is

    I_U < W(t)+8C_1(t)+16[N_G(t)+L_g(t,ell)]            (F11b)
        <=W(t)+8C_1(t)
          +(A/48)G(t)t^3 exp(t/1200)
          +(4A/3)g(t)ell^3 exp(ell/300).               (F11c)

The coefficients16/768=1/48 and16/12=4/3 retain the single-Xi normalization. This is a positive survivor with a complete exact decomposition, not a P or RH claim. One can further bound W by the explicit finite source integral

    W <= (A/4)integral_ell^t s^2 exp(s/300)
                                  (16t-15s)T(t-s)ds,

but this discards source correlation and has not yielded the required relative estimate. No class of all norm majorants is claimed impossible.

F12. The attempted budget transfer stops at an exact unproved inequality. Complete score373 has one actual coefficientwise theta in(0,1) with

    Rscore(r)>= (1-theta)U(r),
    303K'(r)+Rscore(r)=U(r),
    Etheta:=I_R-(1-theta)I_U>=0.

Literal source IBP at Z gives

    theta I_U-303(I_K+V)
       =303[Anear-P(t)]+Etheta >=303zeta_t>0,          (F12a)
    zeta_t=q A K(t) min(ell/2,20)^3/48>0,
    q=1051/2184.

This is a conditional necessary crossing defect, NOT a counterexample asserting Z exists. The missing source producer is M15 `Cout<=V`, equivalently the exact normalized score-history comparison; stronger `theta I_U<=303(I_K+V)` would suffice. For the present mechanism a sufficient NEW line would be

    theta[W+8C_1+16(N_G+L_g)] <=303(I_K+V) at EVERY Z. (OPEN-FINITE)

No source Ward law, full primitive-family balance, score square slack or returned corpus item proves that line. F11 has isolated the costs but has not bounded their relative size against V and I_K. F12a proves that any actual such producer would exclude Z; it does not permit replacing it by an assumed sign/receiver. The exact residual without the sufficient overestimate is

    theta[W+8C_1+16(N_G+L_g)-16(A_G+A_g)]
                                               <=303(I_K+V).

This is still a source-correlation burden, not a solution by re-expression. Guarded zeros are finite by terminal295; no cofinal guarded sequence exists, so a large-clock tail comparison would be vacuous. An effective finite cutoff or actual zero witness has not been supplied. Unguarded N/V growth and the whole causal signed-history family remain separate true results.

## Exhaustive claim self-audit and exact scope

|Claim|Verdict / retained admission|
|---|---|
|F1|Actual full source, SAME R0, genuine compact whole sums/derivatives, P double zero, D entire nonzero and factor ONE; absolute mass A distinct. Existing exact papers/source establish admission before the new algebra.|
|F2|Reused positive full primitive family, every natural m and j0 cancellation; compact signed triangle Fubini and whole factorial majorant. No inferred inverse sign.|
|F3|Literal g=B2/r and parameter integrals, regular0 including T0=1/2/g'0=1/2; complete rows and two factorials.|
|F4|Genuine double compact L1, u0 removable, scaling P(us) not P(s), full series/floor nu1t^4/96. Unconditional positive theorem.|
|F5|Exact full mismatch, all endpoints and parameter0, no order for D(s)-D(us); no positivity leap.|
|F6|Exact weighted commutator, s^2/g0 boundaries, signed early kernel; source C2 stays positive but cannot absorb an unestimated correction.|
|F7|Full discrepancy/strict derivative inequality uses all rows and nu2>0. Countable constant-cone no-go reused only at exact certified bytes. No fractional-mixture assertion.|
|F8|Closed t/4 endpoint strict via j2, t endpoint0, negative at0; sharpness proof is all-clock small-origin statement only, not optimality for Z>20.|
|F9|Full signed L1 positive-part split; complete negative support s<t/4; A_G>0 uses actual entire nonzero D + nonnegative history, not existence of Z.|
|F10|Actual full-copy norm bounds, continuous origin division, precise768/12 constants, arbitrary ell includingell>20.|
|F11|Full signed S12, SAME source every term, boundary cancellation, exact four nonnegative costs and strict upper bound; every compact integral truly L1.|
|F12|Actual theta reserve and strict conditional defect; missing relative finite budget remains explicit. No ineffective tail used on finite Z and no RH branch selected.|

Strongest proved additions proposed for independent paper review: complete matched-dilation positivity and sharp floor F4; full-source sharp quarter-age kernel boundary F8; exact literal nonnegative-history cost localization and strict survivor F9; finite-clock unsigned cost decomposition and upper bound F11 with source-certified envelopes F10. Their Lean status is OPEN. They neither refute M15 nor prove it. No route/card retirement or formal implementation is performed here.

## Corpus-first commands and lifecycle

Both commands were run directly, without help or search-implementation preparation:

    python3 scripts/formal_tools.py research 'actual theta signed history first zero D integral P over t score measure adaptive terminal mass upper bound Cout budget finite clock factor one Volterra' --mode deep --budget-seconds 180 --no-refresh --json
    python3 scripts/formal_tools.py research 'actual Borel primitive beta integral parameter varying primitive depth positive convolution theta signed clock history' --mode deep --budget-seconds 120 --no-refresh --json

Owned sessions61193/54920 observed terminal exit0 before replacement; raw JSONs are distinctly prefixed and fully retained in the evidence. No compiler or numerical job was run. All returned records were read: query1 ALL61=20C+20S+10P+10T+1I; query2 ALL62=20C+20S+10P+10T+1proofidea+1I. Empty declarations/exploration/markers are recorded as empty. Every source proof excerpt, non-null method, ingredient/proof-idea obligation, prose/passage text and provenance/runtime/coverage field was inspected. Initially truncated displays were recovered in bounded outputs, including Q1 C7's complete dependency inventory; no unseen record is called reviewed.

Query1 SHA `2b1114523b4f685bef1748cebbe0b350733d6ac5a00c46e6ad6398127b6db45a`, elapsed140.861421375s, partial=true; unfinished `query:P over t Volterra terminal` and reranking, local-runtime deadline error. Retrieval index1176282; coverage generation1176293/current1176294. Inventory63957/63957 complete, pending0; Lean53646/prose10311; declarations829911/documents2399760/vectors2248036. Compiler43snapshot/2error/10311not-applicable/48248pending/2660stale/38stale-snapshot/1umbrella-source-only/2654unavailable. Methods46failed/400106ready/184543stale; invalidationfalse, errors[].

Query2 SHA `56957fe52eb0cbad71b840d3d6f41a58fa7511e62c0e14f927a3662ada8adb74`, elapsed90.821883458s, partial=false, unfinished/errors[]; retrieval index1176367, coverage1176374/current1176375. Inventory63959/63959 complete, pending0; Lean53648/prose10311; declarations829940/documents2399806/vectors2247946. Compiler43snapshot/2error/10311not-applicable/48250pending/2660stale/38stale-snapshot/1umbrella-source-only/2654unavailable; method invalidationfalse/enrichment counts pendingtrue. Both semantic-coverage complete=null/not-measured/reporting_budget and warn older coverage snapshot/semantic unavailable.

Every ranked Lean record is source-only/not-checked, with null compiled statement/axioms/compiler metadata. Returned source/declaration hashes are distinct from full-file hashes. Query2's Primrec let-type record is an incomplete indexed declaration snippet, irrelevant to the source question; its entirety as RETURNED was inspected, never asserted to be a full proved contract. Generated “sufficient sources” assessments are rejected as proof. The full runtime/model fingerprints, all timing fields and relaxed-query traces are retained in evidence, not silently converted to semantic/compiler freshness. No absence, world novelty, comprehensive prior exhaustion or RH conclusion follows from retrieval.

## Complete returned-record applicability ledger

Zero-based C/S/P/T indices match each raw array exactly. Every table row disposes of the FULL returned record, including its metadata and nested methods. Applicable source fragments were followed in primary files; unrelated source snippets were not silently promoted to actual theta identities.

### Query 1 — deep

|Record|Returned source/name|Complete disposition|
|---|---|---|
|C0|RHTower.integrable_thetaRateBound|Supplied rate-Laplace bound; unrelated theta measure, no history sign.|
|C1|RHTower.integral_abs_thetaError_div_le|Prime-Chebyshev theta error, different literal theta; cannot identify P or D.|
|C2|RHTower.lintegral_comap_thetaSeedRate_le|Generic pullback lintegral upper measure; no signed budget.|
|C3|RHTower.exists_bound_thetaRenewalIncrement|Compact renewal bound for another clock, no actual history correlation.|
|C4|RHTower.integral_thetaSquareL1Majorant|Square L1 admission only; no orientation.|
|C5|RHTower.HedenmalmThetaSource.norm_thetaSourceDerivativeHistoryQuotientProjection_le|Hilbert quotient projection bound, different history observable.|
|C6|RHTower.ThetaSourceWard.exists_bound_laplaceIntegrand_one|Generic ThetaSource Laplace norm admission; source identification missing.|
|C7|RHTower.thetaWeightedRealTranslationHistory_le_derivativeHistory|Closed Hilbert translation-history inclusion, not scalar D age order.|
|C8|RHTower.primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_diagonal_eq_thetaFlux|Prime-Hodge nuclear defect diagonal/flux identity, different carrier.|
|C9|RHTower.deterministicClockLaw_toMeasure|Deterministic clock law definition, wrong actual law.|
|C10|RHTower.integrable_bounded_mul_thetaL1|Bounded-times-theta L1 admission only.|
|C11|RHTower.liClockCriticalCutoffMeasure|Gaussian paired-eta cutoff measure, different source.|
|C12|RHTower.ccmFirstClockCounterMeasure|CCM first-clock counter definition, not actual D.|
|C13|RHTower.ccmFirstClockContinuousBaseMeasure|CCM first-clock base-measure definition, not actual D.|
|C14|RHTower.XiShiftedCanonicalAdmission.resetCounter_clock_step|Synthetic reset-counter packet, not source log history.|
|C15|RHTower.measurable_clockOrient|Mertens clock measurability, not scalar primitive sign.|
|C16|RHTower.thetaLocalizationWeight_le_four|Weil quadratic localization bound, wrong actual observable.|
|C17|RHTower.thetaLocalizationChainWeight_le_four|Weil quadratic localization bound, wrong actual observable.|
|C18|RHTower.ccmFirstClockLandauMeasure|CCM Landau cutoff measure, no literal P or budget.|
|C19|RHTower.clockRate|Prolate clock-rate definition only.|
|S0|RHTower.l2Amplification_primeCoordinate_actualThetaPacket|Actual prime-coordinate theta L2 amplification, wrong observable.|
|S1|GaloisForLFunctions.HTGeometry.gomesQubitOrbitDerivative|Qubit orbit derivative identity, unrelated carrier.|
|S2|RHTower.quantumStratonovichCayleyTransition_theta_eq|Quantum Stratonovich/Cayley transition, unrelated source.|
|S3|RHTower.HedenmalmThetaSource.thetaSourceSignedStageCorrection|Hedenmalm signed finite-stage correction, no actual history orientation.|
|S4|GaloisForLFunctions.HTGeometry.gomesQubitOrbitBias|Qubit source bias identity, wrong source.|
|S5|RHTower.thetaCuspComplexSource|Actual theta complex cast/source admission, no signed primitive order.|
|S6|RHTower.thetaCuspFullLogJetEight|Fixed full-log-jet order eight only, no all-clock budget.|
|S7|RHTower.thetaCuspFullLogJetSix|Fixed full-log-jet order six only, no all-clock budget.|
|S8|RHTower.HedenmalmThetaSource.thetaSourceSignedStageFinMatrix|Signed finite-stage matrix representation, no D order.|
|S9|GaloisForLFunctions.HTGeometry.gomesSSHCarrier|SSH carrier calculation, unrelated source.|
|S10|RHTower.HedenmalmThetaSource.thetaSourceSignedStageMatrix|Signed finite-stage matrix representation, no D order.|
|S11|GaloisForLFunctions.HTGeometry.gomesFockPhase_vector_moments|Fock phase moment gauge invariance, different Hilbert observable.|
|S12|GaloisForLFunctions.HTGeometry.gomesFockZeroPhase_vector_moments|Fock zero-phase moment gauge invariance, different Hilbert observable.|
|S13|RHTower.thetaBilateralLaplace|Theta bilateral-Laplace definition, no inverse sign.|
|S14|RHTower.liEvenCrossActualClockBorelCoefficient|Literal actual b_j=nu_j/((2j)!)^2; applicable full source normalization.|
|S15|GaloisForLFunctions.HTGeometry.egbFixedCharge_enthalpy_jump|Gauss-Bonnet enthalpy identity, unrelated source.|
|S16|RHTower.continuous_thetaCuspSourceTerm_one|Actual first-atom continuity; genuine admission, not sign producer.|
|S17|RHTower.thetaCuspSchwartzReal_apply|Actual Schwartz representative admission, no history comparison.|
|S18|RHTower.ccmLocalPotentialLocalizationDefect_eq|Full returned ready IMS-localization method read; needs another Weil quadratic test/cost, not M15.|
|S19|RHTower.ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular|Finite order-eight modular reflection identity only.|
|P0|docs/drafts/pipeline/3-formalized/theta/theta-compact-inverse-zero-jordan-history.md|Historical compact-theta inverse/Jordan history report; different operator and no M15 producer.|
|P1|docs/drafts/pipeline/2-fully-proven/li-clock-cutoff-marking-boundary.md|Prior signed cutoff/marking boundary; retains unsmoothed source gap.|
|P2|docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md|Recursive compact division/support proof ledger, not budget producer.|
|P3|docs/drafts/pipeline/3-formalized/theta/theta-compact-inverse-zero-jordan-history.md|Compact Hilbert-history certificate, different inverse/observable.|
|P4|docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md|Recursive source admission ledger, no scalar history comparison.|
|P5|docs/drafts/pipeline/3-formalized/theta/theta-compact-inverse-zero-jordan-history.md|Original Schwartz-core report, not source sign.|
|P6|docs/drafts/pipeline/2-fully-proven/li-clock-source-correlation-envelope.md|Prior source-envelope record dispositions, no new budget proof; card relocated during root reconciliation.|
|P7|docs/drafts/pipeline/2-fully-proven/li-clock-source-correlation-envelope.md|Prior source-envelope source/no-M15 boundary, card relocated during root reconciliation.|
|P8|docs/drafts/pipeline/2-fully-proven/li-clock-score-correlation-reserve.md|Prior score-correlation hit ledger, not a new source proof.|
|P9|docs/drafts/pipeline/3-formalized/li-clock-history-correlation-boundary.md|Formalized barrier prior hit ledger; receiver remains conditional.|
|T0|formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean|Full returned Fock-qubit gauge block, unrelated source.|
|T1|formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualFiniteDivisorRigidity.lean|Full72 finite-divisor supplied branch/dichotomy; source branch not selected.|
|T2|formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean|Full returned Fock-qubit gauge block, unrelated source.|
|T3|formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitTransport.lean|Qubit orbit transport block, not P or D.|
|T4|formal/GaloisForLFunctions/RHTower/CCMThetaArithmeticLocalization.lean|Weil quadratic IMS localization identity, wrong cost.|
|T5|formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean|Genuine actual ScoreMeasure finite/L1/moments/strict square slack; applicable admission, no M15 sign.|
|T6|formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean|Literal actual raw R0 and score measures; applicable source normalization.|
|T7|formal/GaloisForLFunctions/HTGeometry/GreedyBumpCovarianceApplications.lean|Supplied positive-definite covariance model, not actual history.|
|T8|formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean|Actual all-degree score strict gap and nonnegative test domination; applicable reserve only.|
|T9|formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean|Actual probability/support/null-singleton/row-Ward admission; no source correlation.|
|I0|Theta error integral bounded by rel mass|Unverified Chebyshev theta-error plus renewal compact-bound proposal: neither source is literal P/D; rejected.|

### Query 2 — primitive

|Record|Returned source/name|Complete disposition|
|---|---|---|
|C0|RHTower.D4BMJointSource.positive_convolution|Private BM positive-half-line convolution equality; positive means domain, not a sign theorem.|
|C1|MeasureTheory.posConvolution|Mathlib positive convolution definition; no integrand sign.|
|C2|Finset.convolution_pos|Finite combinatorial convolution positivity, different space.|
|C3|RHTower.positiveMellinConvolution|Positive Mellin convolution means positive integration domain; no actual P sign.|
|C4|RHTower.mellin_positiveMellinConvolution|Mellin product formula, different transform/source.|
|C5|Nat.Primrec|Computability primitive recursion, irrelevant.|
|C6|Nat.Primrec'.of_prim|Computability primitive recursion, irrelevant.|
|C7|Nat.Partrec.Code.primrec_recOn|Computability primitive recursion; indexed let-type snippet incomplete, irrelevant.|
|C8|RHTower.D4BMJointSource.weighted_primitive_convolution|Private BM weighted-primitive convolution of supplied vector, wrong source.|
|C9|RHTower.ExtendedSelbergClass.hasSum_shiftLatticeExpansion|Selberg cusp expansion, wrong source.|
|C10|RHTower.ExtendedSelbergClass.hasSum_cuspExpansion|Selberg lattice cusp expansion, wrong source.|
|C11|GaloisForLFunctions.HTGeometry.coeffTheta|Dirichlet theta coefficient, not actual normalized clock.|
|C12|GaloisForLFunctions.HTGeometry.PositiveMeixnerConvolutionTime|Positive Meixner convolution-time supplied class, not actual theta law.|
|C13|RHTower.ccmL1Convolution|CCM L1-convolution definition, no source sign.|
|C14|GaloisForLFunctions.RHTower.HalfWeight.theta_one_div_p_A|Quadratic Gauss theta reciprocal parameter identity, unrelated.|
|C15|Nat.Primrec.prec1|Computability primitive recursion, irrelevant.|
|C16|RHTower.compactFourierBorel|Compact Fourier-Borel functional, wrong target.|
|C17|RHTower.measurable_positiveMellinConvolution|Mellin-convolution measurability admission, no sign.|
|C18|VectorFourier.fourierIntegral|Vector Fourier integral definition, unrelated carrier.|
|C19|GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_eq_fourierIntegral|Lp Fourier representative identity, no history order.|
|S0|RHTower.summableLocallyUniformlyOn_liClockPairedEtaInfinitePartitionBorelTermComplex|Paired-eta infinite Borel locally uniform full series, wrong symmetric source; admission pattern only.|
|S1|RHTower.liEvenCrossActualClockBorelCoefficient|Literal actual b_j, same normalization; exact overlap with query1 S14.|
|S2|RHTower.liEvenCrossActualClockBorelTerm|Literal actual Borel term with both factorials; applicable whole series.|
|S3|RHTower.infiniteBorel_halfLine_coefficient_bound|Paired-eta half-line coefficient bound, not actual theta.|
|S4|RHTower.pv_kernel_continuous|Private actual K continuity body source-read; genuine admission only.|
|S5|RHTower.schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_deningerReflectGauge_comm|PW partner imbalance receiver, wrong observable.|
|S6|GaloisForLFunctions.HTGeometry.scaledGammaAlienChargeZero_commonUnitScale_iff_orbitCharge_zero|Scaled-Gamma orbit-charge algebraic classification, unrelated carrier.|
|S7|GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_orbitCharge|Scaled-Gamma differential-algebraic classification, unrelated carrier.|
|S8|RHTower.d4BMPeierlsMetricSquareNumerator|Peierls bare metric square numerator, no D sign.|
|S9|RHTower.gm_damped_measurable|Private actual Gamma-mixture damped measurability, admission only.|
|S10|RHTower.compactCarrierLambert_zero_on_ray|Full returned ready Lambert zero-on-ray transfer needs supplied sector/cofinite annihilation; no actual budget.|
|S11|GaloisForLFunctions.HTGeometry.FokasLenells.continuous_globalSmall_contourReflection|Fokas-Lenells scattering continuity, unrelated.|
|S12|RHTower.compactPrimeEulerUnitTangent_apply|Full returned ready prime-Euler tangent application, unrelated actual clock.|
|S13|RHTower.integral_responseKernelBlock|Actual full response-kernel-block integral with beta/factorial normalization; applicable factor-one admission.|
|S14|GaloisForLFunctions.RHTower.MaassSmooth.weightLift_section_rotation_diagonal|Maass weight-lift section derivative, unrelated.|
|S15|RHTower.exists_uniformSectorCarrierPositive|Full returned uniform-sector-positive method uses compact complex wedge and supplied guards; not history M15.|
|S16|RHTower.riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight|Wold subhalf residual RH receiver assumes critical-energy summability; no producer.|
|S17|RHTower.liEvenCrossActualClockBorelKernel_ge_spatialExp|Actual Borel spatial exponential growth, source admission without P sign.|
|S18|I₁|Aesop test declaration/full strategy method, irrelevant.|
|S19|Bottcher.hDisc_productCover_loop_and_deckMaps_of_commonPullback|Bottcher deck-map tower, different geometry.|
|P0|docs/drafts/pipeline/1-in-progress/li-complex-orientation-conjecture-loop-2026-09-29.md|Historical Li orientation-loop report, no new producer.|
|P1|docs/drafts/pipeline/3-formalized/li-clock-infinite-partition-density-tail-boundary.md|Final paired-eta density-tail certificate, different source.|
|P2|docs/drafts/pipeline/3-formalized/li-clock-positive-borel-ratio-transfer.md|Positive-series ratio transfer, applicable proof pattern but not source history sign.|
|P3|docs/drafts/pipeline/1-in-progress/li-clock-finite-eta-orientation-window.md|Finite-eta orientation boundary, distinct arithmetic source.|
|P4|docs/drafts/pipeline/3-formalized/li-actual-clock-volterra-positive-mass.md|Banked actual Volterra positive-mass/source identities; exact overlap retained.|
|P5|docs/drafts/pipeline/5-failed/pw-b-forced-scalar-contact-borel-transmutation.md|PW forced-scalar failed route, different source.|
|P6|docs/drafts/pipeline/3-formalized/li-clock-positive-borel-ratio-transfer.md|Positive-series ratio transfer continuation, no M15 producer.|
|P7|docs/reports/STATUS.md|Historical STATUS paired-eta entry, no actual theta-history proof.|
|P8|docs/drafts/pipeline/3-formalized/li-clock-infinite-partition-supercritical-window.md|Final supercritical paired-eta source window, different source/normalizers.|
|P9|docs/drafts/pipeline/5-failed/pw-b-peierls-bare-metric-borel-edge.md|PW Peierls bare-metric failed route, different observable.|
|T0|formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelSource.lean|Actual BorelSource1–112: source rows/nu positivity/R0/factorial envelope; applicable, primary followed.|
|T1|formal/GaloisForLFunctions/RHTower/LiClockPairedEtaInfinitePartitionBorel.lean|Paired-eta complete Borel convergence block, distinct source.|
|T2|formal/GaloisForLFunctions/RHTower/RealSL2Haar.lean|Real-SL2 Haar normalization, unrelated.|
|T3|formal/GaloisForLFunctions/HTGeometry/FokasLenellsScatteringContinuity.lean|Fokas-Lenells scattering continuity, unrelated.|
|T4|formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekForcedContactScalarTransmutationNoGo.lean|PW scalar-transmutation no-go, different divisor/operator.|
|T5|formal/GaloisForLFunctions/RHTower/DepthUpdate.lean|Synthetic depth quadratic update model, not actual D.|
|T6|formal/GaloisForLFunctions/RHTower/RoutePPrimitiveJointDepthGammaJuliaScalarIntertwinerNoGo.lean|Prime Hilbert joint-depth intertwiner, wrong observable.|
|T7|formal/.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean|Mathlib gcongr tactic implementation, not mathematics of source sign.|
|T8|formal/GaloisForLFunctions/RHTower/XiGuinandWeilVerticalCauchyScaled.lean|Xi vertical-Cauchy scaled contour admission, different weight.|
|T9|formal/GaloisForLFunctions/RHTower/XiMassPolynomialVerticalResolvent.lean|Xi mass-polynomial vertical resolvent, different source weight.|
|I0|Borel convolution with positive kernel|Unverified BM half-line convolution plus Mellin product: domain positivity is not inverse/source positivity; rejected.|
|Idea0|RHTower.pv_kernel_continuous|Actual private K-continuity source; proposed transfer explicitly still requires Volterra identity. Identity is separately banked, but neither it nor continuity proves M15.|

## Final source/evidence verification and boundary

Every returned ranked statement/source statement, every full returned source proof excerpt, and all20+20 prose/source-passage texts occur literally in the pinned live source after resolving query1P6/P7's documentary move from Stage2 to Stage3. This verifies returned-content correspondence, not compiled applicability or completeness of surrounding declarations. All raw-record arrays reconstruct exactly from the retained captures, all123 indices have dispositions, and all mathematical input/source hashes were rechecked unchanged at freeze. Current source-only/provenance fields remain separately recorded.

The primary exact germ check was refreshed: `PrimeArchThetaCumulantMinor.lean435–463`, specifically `normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment`; literal response-series78–105 in `LiEvenCrossActualClockVolterra.lean` gives F(t)=nu1*t+O(t^3), hence P/D leading terms as stated. Full-copy P cosine trace151–161 and primitive norm193–211 were read directly; neither a half-copy nor factor-two source enters any new floor/cost.

Evidence JSON: `/tmp/li_producer_theta_finite_guard_source_evidence.json`, SHA256 `f4e690419c3ade5c94ba78d83bb24dfa849c4ed8923e882f3645c59e4ecf9e13`. It retains every raw returned field, method, proof idea/ingredient, coverage/runtime fingerprint, source/input/documentary pin and all123 dispositions. No compiler, Lean source, cards or numerical experiments were touched.

**Final result:** F4/F8/F9/F10/F11 are dependency-closed positive paper survivors submitted for independent review. Literal actual M15, actual guarded-zero exclusion and unconditional RH remain OPEN. Exact relative finite-clock source comparison in F12 is the missing producer; neither matched dilation nor the early-cost envelopes establish it. No route retirement is claimed.

## Frozen complete independent audit283

# Independent complete finite guarded-source paper and corpus audit

Verdict: **PAPER/SOURCE/CORPUS PASS**, with no mathematical correction required. Actual M15, actual guarded-zero existence, effective finite cutoff, unconditional D/P sign and RH remain OPEN. This audit proves no new Lean result and claims no fresh compiler validity.

## Frozen scope and exhaustive coverage

- Author paper: `/tmp/li_producer_theta_finite_guard_source_attack.md`, ALL421 lines, SHA256 `fd18aa2dcc4e8b729c5d173e157d68a9fce84b09ac2c6122ce06cbf6457f85c9`.
- Evidence: `/tmp/li_producer_theta_finite_guard_source_evidence.json`, ALL19197 lines/1155734 bytes, SHA256 `f4e690419c3ade5c94ba78d83bb24dfa849c4ed8923e882f3645c59e4ecf9e13`.
- Every F1–F12 statement, proof, admission, self-audit, scope limitation and corpus disposition was read. Originally truncated displays were recovered, including paper252–274.
- ALL123 distinct returned records were read with every supplied statement, proof excerpt, dependency list, nonnull generated method, nested obligations/evidence, prose/source text, source hash, provenance, score, runtime/model/timing/query-trace and coverage field. ALL61 deep and ALL62 primitive records have separate source-order dispositions below. No sampling.
- The evidence's duplicated `queries.raw` objects are exactly equal to their separately retained complete JSON captures; each `record_dispositions.raw_record` equals its indexed original record. All section/index slots match uniquely, with no missing/extra record. Duplicate content was read once and mechanically matched, never assumed equal.
- For all80 ranked Lean records, `source_statement=statement`; shared null compiled_statement/axioms/compiler_metadata, empty binders and source_only/indexed/not_checked fields were checked mechanically and read once. Every distinct field and all generated methods were read individually. The extra proof-idea is separately checked.
- All11 frozen mathematical input pins and all10 primary source pins match exact bytes and line counts. The two changing frontier/STATUS documentary whole hashes are explicitly qualified below.
- Every returned statement/source_statement/proof_excerpt/text occurs literally in its current resolved primary file. Every record's current path/hash/range and exact correspondence is retained in the independent metadata; moved Stage2 documentary paths are resolved explicitly.
- Read-only task: no Lean/probe/compiler, numerical experiment, tree/card/source edit, new agent or new research query. Only this certificate and matching metadata were written.

## Literal source and admissions

The actual coefficient is `b_j=nu_j/((2j)!)^2`, `nu_j=R_j/R_0`, with `R_j=2 integral_Ioi0 x^(2j)*thetaCuspFullSource(x)`. The same positive SINGLE-Xi `R_0` remains in every row; nu0=1 and every nu_j>0. Spectral absolute mass `A=xiShiftAbsoluteMass 0` is distinct from this normalizer. Neither a paired-eta law nor a positive proxy replaces the source.

Fresh primary BorelSource ALL1–276 supplies `nu_j<=(32/303)^j*j!`, complete compact norm convergence and genuine first derivative. Each fixed-order differentiated series has a polynomial-in-j multiplier absorbed by an enlarged-radius factorial envelope. This admits all entire series, every derivative used, and every compact parameter integral before exchanging sums/integrals. Fresh Flattening106–178 and exact prior full589 review independently pin the all-order real ladder.

Fresh Primitive ALL1–235 retains EVERY XiZeroCopy, complete square-frequency norm mass, compact complex normal convergence, true complex reality and sharp `|P(s)|<=A*s^2*exp(s/300)/2` for s>=0. The same primitive's double origin zero makes P(z)/z entire with its zero filling. Frozen Terminal295's fully audited double-copy Taylor construction proves the entire literal D, rather than inferring analyticity from C-infinity. Fresh Terminal1–132 and CumulantMinor435–463 verify `D(z)=nu1*z^2/4+O(z^4)`, with nu1=M0>0. Thus D is nonzero and cannot vanish on a real open interval.

Fresh Barrier1–145 verifies canonical `D=integral_0^t(P(s)/s)ds`, continuous zero filling and real FTC: P=sD' including the filled origin. Fresh PrimitiveVolterra ALL119 proves `P+P*K=tK` for t>=0 with factor ONE, genuine compact signed L1 and correct IBP orientation. No all-real Volterra law or P/D monotonicity is used.

The full Score373 and Budget273 arguments remain at exact audited pins. Returned ScoreMeasure passages were all read against the exact prior full497 review: raw probability has density `(2/R_0)*thetaCuspFullSource`; positive score carrier retains all positive theta rows, j0 and exact Ward factor2*pi. It is finite, has all natural-power L1, strict gaps in every degree and square-weighted raw domination. It supplies reserve only, never a signed D-test orientation. Score profiles/history still use their proved paper contracts; prospective plan817 is not treated as an installed API.

Every integral in F3–F12 is a continuous signed or nonnegative function on an explicitly finite compact carrier before linear operations. At u=0 no division is used to secure admission; the original integrand and its continuous extension are used. At lag0 and at s=0 all stated origin terms are retained. Positive-part operations preserve continuity and true compact L1. No totalized divergent integral is evaluated.

## Exhaustive F1–F12 mathematical dispositions

|Claim|Disposition|
|---|---|
|F1|PASS: literal single-R0 source, full-copy P, entire nonzero D, sharp norm envelope, true compact all-order admission and factor-one Volterra law.|
|F2|PASS: every natural primitive depth, m0 included; full factorial series, genuine triangle Fubini and exact positive j1 floor.|
|F3|PASS: exact `g=rT=B2/r`, both parameter identities and origin filling, all rows and both factorials.|
|F4|PASS: full matched-dilation positivity and explicit displayed j1 floor; u0 admitted before substitution.|
|F5|PASS: complete undilated mismatch/IBP; no assumed order for D(s)-D(us).|
|F6|PASS: exact reciprocal commutator, signed history kernel, correct late interval and surviving correction.|
|F7|PASS: complete discrepancy series, strict elasticity via retained j2, exact signed transfer; prior constant-cone obstruction reused only at pin.|
|F8|PASS: complete negative support confined before quarter-age, strict t/4 endpoint via higher rows, exact allclock small-origin sharpness and terminal0.|
|F9|PASS: genuine signed-cost split and strictly positive A_G from actual entire nonzero D under explicit nonnegative history. No zero witness.|
|F10|PASS: actual norm admission and exact1/768,1/12 constants, arbitrary ell, both positive parts and full early boundary.|
|F11|PASS: exact SAME-source boundary cancellation, four admitted nonnegative costs, strict finite-clock upper bound and both envelope constants.|
|F12|PASS: strict conditional first-zero defect, exact missing sufficient/equivalent inequalities and finite-guard logical boundary. No sign producer.|

F1: Re-normalization or doubling would break the germ; neither occurs. Full moment identity M0=nu1 establishes the positive quadratic D germ. Entire nonzero is essential for F9. Spectral mass A is used only for the absolute P/D envelopes and actual early reserve.

F2: Genuine integration of `P+P*K=tK` gives P*B=tB-B1. Repeated compact triangle Fubini gives `C_m=P*B_m=tB_m-(m+1)B_(m+1)`. The full row is `2j*b_j*(2j)!*t^(2j+m+1)/(2j+m+1)!`; j0 cancels, every j>=1 is nonnegative. Its j1 coefficient is `2*b1*2!=nu1`, hence `C_m>=nu1*t^(m+3)/(m+3)!>0` for t>0. The compact bound `R^m/m!` times the B-majorant admits all rows first. Positivity of these convolutions is not positivity of signed P.

F3: The literal adjacent factorials give `T(r)=sum nu_j*r^(2j)/[(2j+2)!(2j)!]`. Integrating B1(ur) over u divides by 2j+2, giving g=B2/r for r nonzero and the same continuous filling at0. Integrating `(1-u)B(ur)` gives the same T because `integral_0^1(1-u)u^(2j)=1/[(2j+1)(2j+2)]`. Therefore T0=g'0=1/2, g0=0. Complete compact uniform convergence licenses both exchanges also for oriented negative r; positivity is invoked only at nonnegative clocks.

F4: For u>0, x=us changes `integral_0^t P(us)B1(u(t-s))ds` to C1(ut)/u. Its original continuous double-compact integrand is zero at u0, so the quotient formula is applied only after admission. Integrating the full u^(2j+1) row gives
`A_dil=sum_(j>=1) 2j*b_j*t^(2j+2)/[(2j+1)(2j+2)^2]`.
The j1 row is nu1*t^4/96. This is a genuine unconditional SAME-source positive survivor for t>0.

F5: Add/subtract P(us) to get P*g=A_dil+C_dil. Since `P(us)=s*d_s D(us)` even at u0 via filling, IBP of `[D(s)-D(us)]*sB1(u(t-s))` gives exactly the stated mismatch kernel `s*u*B(u(t-s))-B1(u(t-s))`. Both endpoints vanish. Nonnegative D does not order D(s)-D(us), and the kernel is signed; no unproved mixed-history positivity enters.

F6: Pointwise t=(t-s)+s and `(t-s)g(t-s)=B2(t-s)` give P*g=C2/t+(1/t) integral sP(s)g(t-s). IBP with P=sD' gives `integral D[s^2*g'(t-s)-2s*g(t-s)]`; s0 and g0 kill both boundaries. Full positive coefficients imply rg'>=g for r>=0. This makes the latter kernel nonnegative only when s>=2t/3, with endpoint handled directly. The early signed term remains unestimated.

F7: `G=B1/2-g=sum_(j>=1) b_j*j*r^(2j+1)/[(2j+1)(2j+2)]`, whose first row is nu1*r^3/48. Differentiation is already admitted: `rG'-3G` has zero j1 row and positive every j>=2 row, so strictness holds for r>0 from actual nu2>0. The exact transfer P*g=C1/2-P*G follows genuine signed linearity. The prior finite/countable NONNEGATIVE CONSTANT primitive-cone exclusion does not exclude time-dependent or fractional representations; none is asserted here.

F8: With r=t-s, s>=t/4 gives r<=3s. For r>0 the strict `rG'>3G` yields sG'-G>0, including s=t/4. At s=t both G0 and G'0 vanish, giving0; at s0 the value is -G(t)<0. Every row of H_G is retained. For each fixed c in[0,1/4), the genuine cubic-plus-higher remainder gives
`H_G(t,ct)/t^3 -> (nu1/48)*(1-c)^2*(4c-1)<0`.
This proves sharpness over ALL t>0; it supplies no optimality claim restricted to guarded t>20.

F9: On a nonnegative history with t>0, IBP gives P*G=integral D*H_G without any D(t)=0 premise because G0=0. Whole negative part vanishes on[t/4,t], so the exact split is A_G-N_G with N_G on[0,t/4] and A_G on[0,t]. D cannot vanish throughout(t/4,t) because its entire continuation is nonzero. Under D>=0 some point there is positive; continuity and strict H_G give a positive open interval of product, so A_G>0. No effective point, actual first zero or global P sign is inferred.

F10: Integrating `|P(u)/u|<=A*u*exp(u/300)/2` with continuous origin yields `|D(s)|<=A*s^2*exp(s/300)/4`. Since g,G,g',G' have nonnegative full coefficients on nonnegative clocks, `[-H_G]_+<=G(t-s)<=G(t)`, and the integral of s^2 on[0,t/4] gives A*G(t)*t^3*exp(t/1200)/768. For ANY0<=ell<=t, the exact truncated IBP is `ell D(ell)g(t-ell)+A_g-L_g`; the same bound gives `L_g<=A*g(t)*ell^3*exp(ell/300)/12`. Neither D/P monotonicity nor ell<=20 is assumed.

F11: Actual geometry gives0<ell<t/4 at t>0. Full signed ScoreS12 is `I_U=16ell D(ell)g(t-ell)+W+8C1-16P*G-16 integral_0^ell P(s)g(t-s)ds`. Substitute F9/F10: the COMPLETE signed early boundary cancels exactly, leaving
`I_U=W+8C1+16(N_G+L_g)-16(A_G+A_g)`.
All four costs, W and C1 are nonnegative under the explicit history guard; A_G>0 supplies strict upper comparison. Factors16/768=1/48 and16/12=4/3 are correct. W's optional envelope follows the same D bound and16t-15s>=t>0. These are finite-clock upper bounds, never the needed denominator comparison with I_K+V.

F12: Source gaps and their tail give one actual theta in(0,1), preserving every degree and same R0. Etheta=I_R-(1-theta)I_U>=0. Source303Cout=I_U-I_R-303I_K and factor-one history identity give
`theta I_U-303(I_K+V)=303(Anear-P(t))+Etheta`.
At a hypothetical Z, left derivative D'(t)<=0 and P(t)=tD'(t)<=0. Full near-kernel lower bound plus actual early floor gives `Anear>=zeta_t=q*A*K(t)*min(ell/2,20)^3/48>0`, q1051/2184; fresh Barrier251–421 retains that precise min and the exact factor. Therefore the strengthened budget has a strictly positive CONDITIONAL defect. A producer proving the opposite at every Z would exclude Z; this is not a counterexample asserting a Z exists. Exact finiteZ classification is prior paper overlap, not an effective verification algorithm. Eventual guarded comparisons are vacuous and cannot replace all-clock finite-guard control.

## Strongest nontrivial survivors and remaining premise

1. F4: exact matched-dilation source positivity, complete series and explicit nu1*t^4/96 floor.
2. F8: full quarter-age negative-support boundary, strict quarter endpoint and sharp all-positive-clock cutoff law.
3. F9: exact localized signed history cost with a strictly positive A_G at every explicit nonnegative history; no D(t)=0 needed.
4. F10–F11: quantitative finite-clock early-cost envelopes and the exact lower-boundary-free four-cost decomposition, including strict upper inequality.
5. F12: actual first-zero strengthened-budget defect with explicit positive reserve; this is a conditional crossing criterion, not a producer or M15 failure.

Original arithmetic task remains `Cout<=V` at EVERY literal Z(t), equivalently `I_R+303I_K>=I_U-303V`. The stronger sufficient line isolated by this mechanism is
`theta*(W+8C1+16(N_G+L_g))<=303(I_K+V)` at EVERY Z.
Neither proof nor a counterexample is supplied. Keeping the exact negative reserves gives the equivalent source-correlation burden with `-16(A_G+A_g)`. Raw positivity, unweighted Q retention, signed primitive-family identities and fixed-lag tail limits do not establish that relative finite-clock inequality. No finite/cofinal guarded clock witness, RH branch, unconditional inverse positivity, effective cutoff, growing-clock limit interchange or new Lean certification follows.

## Complete corpus metadata and applicability qualifications

Both direct documented commands and their terminal0 owner handles61193/54920 are retained in the author evidence. No help/search-source preparation is reported. This reviewer did not rerun research or operate any runtime/indexer/compiler.

Deep raw capture: `/tmp/li_producer_theta_finite_guard_search_deep.json`, SHA256 `2b1114523b4f685bef1748cebbe0b350733d6ac5a00c46e6ad6398127b6db45a`;61 records=20C+20S+10P+10T+1I. partial=true, unfinished query:P over t Volterra terminal/reranking, local-runtime deadline, elapsed140.861421375s. Retrieval index1176282 differs from coverage1176293/current1176294. Inventory63957/63957 complete is file inventory only; semantic coverage complete=null/not_measured/reporting_budget. Compiler43snapshot/2error/10311not-applicable/48248pending/2660stale/38stale-snapshot/1umbrella-source-only/2654unavailable. Model-suggests-sufficient-sources is not an applicability proof.

Primitive raw capture: `/tmp/li_producer_theta_finite_guard_search_primitive.json`, SHA256 `56957fe52eb0cbad71b840d3d6f41a58fa7511e62c0e14f927a3662ada8adb74`;62 records=20C+20S+10P+10T+1I+1idea. partial=false, unfinished/errors empty, elapsed90.821883458s. Retrieval1176367 differs from coverage1176374/current1176375; inventory63959/63959 complete, semantic coverage still unavailable/not measured. Compiler counts as above except10311not-applicable/48250pending; enrichment counts pending. Both coverage-snapshot-older and semantic-coverage-unavailable warnings are retained.

Every query relaxation, round, timing, reported refresh/index/method coverage, runtime device/model configuration, fingerprint/revision/license/protocol and provenance field was read and is retained in the immutable evidence and independent nonrecord metadata copy. Both use cached/no-refresh research; source-only records cannot establish compiler validity. Declaration/exploration arrays and markers are empty; this is not a corpus-absence theorem. Source/declaration and content hashes are distinct from whole-file source hashes. The incomplete Primrec let snippet was reviewed only in its returned scope, never promoted to a complete proved contract.

Generated deep ingredient I0 combines Chebyshev prime-theta error with renewal compact bound: wrong theta observable and no literal D/history bridge. Primitive ingredient I0 combines positive-HALFLINE-domain convolution with a Mellin product: no positivity-of-values or inverse sign follows. Fresh primary BM1–46 and Mellin168–end confirm those domain/analytic identities and supplied convergence premises. The primitive continuity proof idea has an explicit still-required Volterra-law obligation; actual factor-one law is separately banked, but continuity plus the law supplies no M15 bound. Generated methods labelled ready are still only source arguments with their listed assumptions, not actual mixed-history estimates.

## ALL123 individual record dispositions

Indexes below are zero-based exact raw-array indexes. Complete names, source/provenance hashes, raw-record digests, live resolved path/range/hash and every exact-match check are in the independent metadata. The concise disposition is independently accepted after full record read; no item is omitted.

### deep — every source-order section/index

|Record|Exact returned name/path|Independent disposition|
|---|---|---|
|candidate_lemmas[0]|`RHTower.integrable_thetaRateBound`|Supplied rate-Laplace bound; unrelated theta measure, no history sign.|
|candidate_lemmas[1]|`RHTower.integral_abs_thetaError_div_le`|Prime-Chebyshev theta error, different literal theta; cannot identify P or D.|
|candidate_lemmas[2]|`RHTower.lintegral_comap_thetaSeedRate_le`|Generic pullback lintegral upper measure; no signed budget.|
|candidate_lemmas[3]|`RHTower.exists_bound_thetaRenewalIncrement`|Compact renewal bound for another clock, no actual history correlation.|
|candidate_lemmas[4]|`RHTower.integral_thetaSquareL1Majorant`|Square L1 admission only; no orientation.|
|candidate_lemmas[5]|`RHTower.HedenmalmThetaSource.norm_thetaSourceDerivativeHistoryQuotientProjection_le`|Hilbert quotient projection bound, different history observable.|
|candidate_lemmas[6]|`RHTower.ThetaSourceWard.exists_bound_laplaceIntegrand_one`|Generic ThetaSource Laplace norm admission; source identification missing.|
|candidate_lemmas[7]|`RHTower.thetaWeightedRealTranslationHistory_le_derivativeHistory`|Closed Hilbert translation-history inclusion, not scalar D age order.|
|candidate_lemmas[8]|`RHTower.primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_diagonal_eq_thetaFlux`|Prime-Hodge nuclear defect diagonal/flux identity, different carrier.|
|candidate_lemmas[9]|`RHTower.deterministicClockLaw_toMeasure`|Deterministic clock law definition, wrong actual law.|
|candidate_lemmas[10]|`RHTower.integrable_bounded_mul_thetaL1`|Bounded-times-theta L1 admission only.|
|candidate_lemmas[11]|`RHTower.liClockCriticalCutoffMeasure`|Gaussian paired-eta cutoff measure, different source.|
|candidate_lemmas[12]|`RHTower.ccmFirstClockCounterMeasure`|CCM first-clock counter definition, not actual D.|
|candidate_lemmas[13]|`RHTower.ccmFirstClockContinuousBaseMeasure`|CCM first-clock base-measure definition, not actual D.|
|candidate_lemmas[14]|`RHTower.XiShiftedCanonicalAdmission.resetCounter_clock_step`|Synthetic reset-counter packet, not source log history.|
|candidate_lemmas[15]|`RHTower.measurable_clockOrient`|Mertens clock measurability, not scalar primitive sign.|
|candidate_lemmas[16]|`RHTower.thetaLocalizationWeight_le_four`|Weil quadratic localization bound, wrong actual observable.|
|candidate_lemmas[17]|`RHTower.thetaLocalizationChainWeight_le_four`|Weil quadratic localization bound, wrong actual observable.|
|candidate_lemmas[18]|`RHTower.ccmFirstClockLandauMeasure`|CCM Landau cutoff measure, no literal P or budget.|
|candidate_lemmas[19]|`RHTower.clockRate`|Prolate clock-rate definition only.|
|source_arguments[0]|`RHTower.l2Amplification_primeCoordinate_actualThetaPacket`|Actual prime-coordinate theta L2 amplification, wrong observable.|
|source_arguments[1]|`GaloisForLFunctions.HTGeometry.gomesQubitOrbitDerivative`|Qubit orbit derivative identity, unrelated carrier.|
|source_arguments[2]|`RHTower.quantumStratonovichCayleyTransition_theta_eq`|Quantum Stratonovich/Cayley transition, unrelated source.|
|source_arguments[3]|`RHTower.HedenmalmThetaSource.thetaSourceSignedStageCorrection`|Hedenmalm signed finite-stage correction, no actual history orientation.|
|source_arguments[4]|`GaloisForLFunctions.HTGeometry.gomesQubitOrbitBias`|Qubit source bias identity, wrong source.|
|source_arguments[5]|`RHTower.thetaCuspComplexSource`|Actual theta complex cast/source admission, no signed primitive order.|
|source_arguments[6]|`RHTower.thetaCuspFullLogJetEight`|Fixed full-log-jet order eight only, no all-clock budget.|
|source_arguments[7]|`RHTower.thetaCuspFullLogJetSix`|Fixed full-log-jet order six only, no all-clock budget.|
|source_arguments[8]|`RHTower.HedenmalmThetaSource.thetaSourceSignedStageFinMatrix`|Signed finite-stage matrix representation, no D order.|
|source_arguments[9]|`GaloisForLFunctions.HTGeometry.gomesSSHCarrier`|SSH carrier calculation, unrelated source.|
|source_arguments[10]|`RHTower.HedenmalmThetaSource.thetaSourceSignedStageMatrix`|Signed finite-stage matrix representation, no D order.|
|source_arguments[11]|`GaloisForLFunctions.HTGeometry.gomesFockPhase_vector_moments`|Fock phase moment gauge invariance, different Hilbert observable.|
|source_arguments[12]|`GaloisForLFunctions.HTGeometry.gomesFockZeroPhase_vector_moments`|Fock zero-phase moment gauge invariance, different Hilbert observable.|
|source_arguments[13]|`RHTower.thetaBilateralLaplace`|Theta bilateral-Laplace definition, no inverse sign.|
|source_arguments[14]|`RHTower.liEvenCrossActualClockBorelCoefficient`|Literal actual b_j=nu_j/((2j)!)^2; applicable full source normalization.|
|source_arguments[15]|`GaloisForLFunctions.HTGeometry.egbFixedCharge_enthalpy_jump`|Gauss-Bonnet enthalpy identity, unrelated source.|
|source_arguments[16]|`RHTower.continuous_thetaCuspSourceTerm_one`|Actual first-atom continuity; genuine admission, not sign producer.|
|source_arguments[17]|`RHTower.thetaCuspSchwartzReal_apply`|Actual Schwartz representative admission, no history comparison.|
|source_arguments[18]|`RHTower.ccmLocalPotentialLocalizationDefect_eq`|Full returned ready IMS-localization method read; needs another Weil quadratic test/cost, not M15.|
|source_arguments[19]|`RHTower.ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular`|Finite order-eight modular reflection identity only.|
|prose[0]|`docs/drafts/pipeline/3-formalized/theta/theta-compact-inverse-zero-jordan-history.md`|Historical compact-theta inverse/Jordan history report; different operator and no M15 producer.|
|prose[1]|`docs/drafts/pipeline/2-fully-proven/li-clock-cutoff-marking-boundary.md`|Prior signed cutoff/marking boundary; retains unsmoothed source gap.|
|prose[2]|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md`|Recursive compact division/support proof ledger, not budget producer.|
|prose[3]|`docs/drafts/pipeline/3-formalized/theta/theta-compact-inverse-zero-jordan-history.md`|Compact Hilbert-history certificate, different inverse/observable.|
|prose[4]|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md`|Recursive source admission ledger, no scalar history comparison.|
|prose[5]|`docs/drafts/pipeline/3-formalized/theta/theta-compact-inverse-zero-jordan-history.md`|Original Schwartz-core report, not source sign.|
|prose[6]|`docs/drafts/pipeline/2-fully-proven/li-clock-source-correlation-envelope.md`|Prior source-envelope record dispositions, no new budget proof; card relocated during root reconciliation.|
|prose[7]|`docs/drafts/pipeline/2-fully-proven/li-clock-source-correlation-envelope.md`|Prior source-envelope source/no-M15 boundary, card relocated during root reconciliation.|
|prose[8]|`docs/drafts/pipeline/2-fully-proven/li-clock-score-correlation-reserve.md`|Prior score-correlation hit ledger, not a new source proof.|
|prose[9]|`docs/drafts/pipeline/3-formalized/li-clock-history-correlation-boundary.md`|Formalized barrier prior hit ledger; receiver remains conditional.|
|source_passages[0]|`formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean`|Full returned Fock-qubit gauge block, unrelated source.|
|source_passages[1]|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualFiniteDivisorRigidity.lean`|Full72 finite-divisor supplied branch/dichotomy; source branch not selected.|
|source_passages[2]|`formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean`|Full returned Fock-qubit gauge block, unrelated source.|
|source_passages[3]|`formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitTransport.lean`|Qubit orbit transport block, not P or D.|
|source_passages[4]|`formal/GaloisForLFunctions/RHTower/CCMThetaArithmeticLocalization.lean`|Weil quadratic IMS localization identity, wrong cost.|
|source_passages[5]|`formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean`|Genuine actual ScoreMeasure finite/L1/moments/strict square slack; applicable admission, no M15 sign.|
|source_passages[6]|`formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean`|Literal actual raw R0 and score measures; applicable source normalization.|
|source_passages[7]|`formal/GaloisForLFunctions/HTGeometry/GreedyBumpCovarianceApplications.lean`|Supplied positive-definite covariance model, not actual history.|
|source_passages[8]|`formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean`|Actual all-degree score strict gap and nonnegative test domination; applicable reserve only.|
|source_passages[9]|`formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean`|Actual probability/support/null-singleton/row-Ward admission; no source correlation.|
|ingredient_sets[0]|`Theta error integral bounded by rel mass`|Unverified Chebyshev theta-error plus renewal compact-bound proposal: neither source is literal P/D; rejected.|

### primitive — every source-order section/index

|Record|Exact returned name/path|Independent disposition|
|---|---|---|
|candidate_lemmas[0]|`RHTower.D4BMJointSource.positive_convolution`|Private BM positive-half-line convolution equality; positive means domain, not a sign theorem.|
|candidate_lemmas[1]|`MeasureTheory.posConvolution`|Mathlib positive convolution definition; no integrand sign.|
|candidate_lemmas[2]|`Finset.convolution_pos`|Finite combinatorial convolution positivity, different space.|
|candidate_lemmas[3]|`RHTower.positiveMellinConvolution`|Positive Mellin convolution means positive integration domain; no actual P sign.|
|candidate_lemmas[4]|`RHTower.mellin_positiveMellinConvolution`|Mellin product formula, different transform/source.|
|candidate_lemmas[5]|`Nat.Primrec`|Computability primitive recursion, irrelevant.|
|candidate_lemmas[6]|`Nat.Primrec'.of_prim`|Computability primitive recursion, irrelevant.|
|candidate_lemmas[7]|`Nat.Partrec.Code.primrec_recOn`|Computability primitive recursion; indexed let-type snippet incomplete, irrelevant.|
|candidate_lemmas[8]|`RHTower.D4BMJointSource.weighted_primitive_convolution`|Private BM weighted-primitive convolution of supplied vector, wrong source.|
|candidate_lemmas[9]|`RHTower.ExtendedSelbergClass.hasSum_shiftLatticeExpansion`|Selberg cusp expansion, wrong source.|
|candidate_lemmas[10]|`RHTower.ExtendedSelbergClass.hasSum_cuspExpansion`|Selberg lattice cusp expansion, wrong source.|
|candidate_lemmas[11]|`GaloisForLFunctions.HTGeometry.coeffTheta`|Dirichlet theta coefficient, not actual normalized clock.|
|candidate_lemmas[12]|`GaloisForLFunctions.HTGeometry.PositiveMeixnerConvolutionTime`|Positive Meixner convolution-time supplied class, not actual theta law.|
|candidate_lemmas[13]|`RHTower.ccmL1Convolution`|CCM L1-convolution definition, no source sign.|
|candidate_lemmas[14]|`GaloisForLFunctions.RHTower.HalfWeight.theta_one_div_p_A`|Quadratic Gauss theta reciprocal parameter identity, unrelated.|
|candidate_lemmas[15]|`Nat.Primrec.prec1`|Computability primitive recursion, irrelevant.|
|candidate_lemmas[16]|`RHTower.compactFourierBorel`|Compact Fourier-Borel functional, wrong target.|
|candidate_lemmas[17]|`RHTower.measurable_positiveMellinConvolution`|Mellin-convolution measurability admission, no sign.|
|candidate_lemmas[18]|`VectorFourier.fourierIntegral`|Vector Fourier integral definition, unrelated carrier.|
|candidate_lemmas[19]|`GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_eq_fourierIntegral`|Lp Fourier representative identity, no history order.|
|source_arguments[0]|`RHTower.summableLocallyUniformlyOn_liClockPairedEtaInfinitePartitionBorelTermComplex`|Paired-eta infinite Borel locally uniform full series, wrong symmetric source; admission pattern only.|
|source_arguments[1]|`RHTower.liEvenCrossActualClockBorelCoefficient`|Literal actual b_j, same normalization; exact overlap with query1 S14.|
|source_arguments[2]|`RHTower.liEvenCrossActualClockBorelTerm`|Literal actual Borel term with both factorials; applicable whole series.|
|source_arguments[3]|`RHTower.infiniteBorel_halfLine_coefficient_bound`|Paired-eta half-line coefficient bound, not actual theta.|
|source_arguments[4]|`RHTower.pv_kernel_continuous`|Private actual K continuity body source-read; genuine admission only.|
|source_arguments[5]|`RHTower.schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_deningerReflectGauge_comm`|PW partner imbalance receiver, wrong observable.|
|source_arguments[6]|`GaloisForLFunctions.HTGeometry.scaledGammaAlienChargeZero_commonUnitScale_iff_orbitCharge_zero`|Scaled-Gamma orbit-charge algebraic classification, unrelated carrier.|
|source_arguments[7]|`GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_orbitCharge`|Scaled-Gamma differential-algebraic classification, unrelated carrier.|
|source_arguments[8]|`RHTower.d4BMPeierlsMetricSquareNumerator`|Peierls bare metric square numerator, no D sign.|
|source_arguments[9]|`RHTower.gm_damped_measurable`|Private actual Gamma-mixture damped measurability, admission only.|
|source_arguments[10]|`RHTower.compactCarrierLambert_zero_on_ray`|Full returned ready Lambert zero-on-ray transfer needs supplied sector/cofinite annihilation; no actual budget.|
|source_arguments[11]|`GaloisForLFunctions.HTGeometry.FokasLenells.continuous_globalSmall_contourReflection`|Fokas-Lenells scattering continuity, unrelated.|
|source_arguments[12]|`RHTower.compactPrimeEulerUnitTangent_apply`|Full returned ready prime-Euler tangent application, unrelated actual clock.|
|source_arguments[13]|`RHTower.integral_responseKernelBlock`|Actual full response-kernel-block integral with beta/factorial normalization; applicable factor-one admission.|
|source_arguments[14]|`GaloisForLFunctions.RHTower.MaassSmooth.weightLift_section_rotation_diagonal`|Maass weight-lift section derivative, unrelated.|
|source_arguments[15]|`RHTower.exists_uniformSectorCarrierPositive`|Full returned uniform-sector-positive method uses compact complex wedge and supplied guards; not history M15.|
|source_arguments[16]|`RHTower.riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight`|Wold subhalf residual RH receiver assumes critical-energy summability; no producer.|
|source_arguments[17]|`RHTower.liEvenCrossActualClockBorelKernel_ge_spatialExp`|Actual Borel spatial exponential growth, source admission without P sign.|
|source_arguments[18]|`I₁`|Aesop test declaration/full strategy method, irrelevant.|
|source_arguments[19]|`Bottcher.hDisc_productCover_loop_and_deckMaps_of_commonPullback`|Bottcher deck-map tower, different geometry.|
|prose[0]|`docs/drafts/pipeline/1-in-progress/li-complex-orientation-conjecture-loop-2026-09-29.md`|Historical Li orientation-loop report, no new producer.|
|prose[1]|`docs/drafts/pipeline/3-formalized/li-clock-infinite-partition-density-tail-boundary.md`|Final paired-eta density-tail certificate, different source.|
|prose[2]|`docs/drafts/pipeline/3-formalized/li-clock-positive-borel-ratio-transfer.md`|Positive-series ratio transfer, applicable proof pattern but not source history sign.|
|prose[3]|`docs/drafts/pipeline/1-in-progress/li-clock-finite-eta-orientation-window.md`|Finite-eta orientation boundary, distinct arithmetic source.|
|prose[4]|`docs/drafts/pipeline/3-formalized/li-actual-clock-volterra-positive-mass.md`|Banked actual Volterra positive-mass/source identities; exact overlap retained.|
|prose[5]|`docs/drafts/pipeline/5-failed/pw-b-forced-scalar-contact-borel-transmutation.md`|PW forced-scalar failed route, different source.|
|prose[6]|`docs/drafts/pipeline/3-formalized/li-clock-positive-borel-ratio-transfer.md`|Positive-series ratio transfer continuation, no M15 producer.|
|prose[7]|`docs/reports/STATUS.md`|Historical STATUS paired-eta entry, no actual theta-history proof.|
|prose[8]|`docs/drafts/pipeline/3-formalized/li-clock-infinite-partition-supercritical-window.md`|Final supercritical paired-eta source window, different source/normalizers.|
|prose[9]|`docs/drafts/pipeline/5-failed/pw-b-peierls-bare-metric-borel-edge.md`|PW Peierls bare-metric failed route, different observable.|
|source_passages[0]|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelSource.lean`|Actual BorelSource1–112: source rows/nu positivity/R0/factorial envelope; applicable, primary followed.|
|source_passages[1]|`formal/GaloisForLFunctions/RHTower/LiClockPairedEtaInfinitePartitionBorel.lean`|Paired-eta complete Borel convergence block, distinct source.|
|source_passages[2]|`formal/GaloisForLFunctions/RHTower/RealSL2Haar.lean`|Real-SL2 Haar normalization, unrelated.|
|source_passages[3]|`formal/GaloisForLFunctions/HTGeometry/FokasLenellsScatteringContinuity.lean`|Fokas-Lenells scattering continuity, unrelated.|
|source_passages[4]|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekForcedContactScalarTransmutationNoGo.lean`|PW scalar-transmutation no-go, different divisor/operator.|
|source_passages[5]|`formal/GaloisForLFunctions/RHTower/DepthUpdate.lean`|Synthetic depth quadratic update model, not actual D.|
|source_passages[6]|`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveJointDepthGammaJuliaScalarIntertwinerNoGo.lean`|Prime Hilbert joint-depth intertwiner, wrong observable.|
|source_passages[7]|`formal/.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean`|Mathlib gcongr tactic implementation, not mathematics of source sign.|
|source_passages[8]|`formal/GaloisForLFunctions/RHTower/XiGuinandWeilVerticalCauchyScaled.lean`|Xi vertical-Cauchy scaled contour admission, different weight.|
|source_passages[9]|`formal/GaloisForLFunctions/RHTower/XiMassPolynomialVerticalResolvent.lean`|Xi mass-polynomial vertical resolvent, different source weight.|
|ingredient_sets[0]|`Borel convolution with positive kernel`|Unverified BM half-line convolution plus Mellin product: domain positivity is not inverse/source positivity; rejected.|
|proof_ideas[0]|`RHTower.pv_kernel_continuous`|Actual private K-continuity source; proposed transfer explicitly still requires Volterra identity. Identity is separately banked, but neither it nor continuity proves M15.|

## Exact pinned mathematical dependencies

### Frozen paper/evidence/approved plans

|Path|Lines|SHA256|Scope / status|
|---|---:|---|---|
|`/tmp/li_current_theta_m15_terminal_history_attack.md`|295|`b19ac9e238d86ce07a3c805c21b6dcaccd9ed612437509f03fe25dcadfe9bae3`|FULL295 prior audited proof, exact byte reuse; entireD/nonzero/finiteZ and no effective cutoff|
|`/tmp/li_producer_theta_m15_terminal_history_audit.md`|132|`57f550cb0a9dba97d506d6a46a82903d383f12238152cc34750227f6ccf938cb`|FULL132 own prior source/corpus certificate reuse|
|`/tmp/li_current_theta_m15_terminal_history_evidence.json`|9137|`1277d98d36b4d08930864d492429d83e5b5b04965e1036397e8f6f162e559192`|prior evidence9137; exact hash only, prior FULL corpus audit reused|
|`/tmp/li_current_theta_m15_score_correlation_attack.md`|373|`7454b4a27be838bc10eb4608872d2eda9cd471c90fd4956f24bfe5e3d8157d3d`|FULL373 prior audit, exactS12/new paper uses canonical score source|
|`/tmp/li_producer_theta_m15_score_correlation_audit.md`|169|`2d8bc7203919872897fb49a33c23e07428435d1abbb43f1487b5d1cabfe9f22f`|FULL169 own prior certificate reuse|
|`/tmp/li_current_theta_m15_score_budget_attack.md`|273|`9b6cac0c746eae68e5c60496bc88339f89928c57779935be6540b4553a1a0e87`|FULL273 prior Pole certificate; fresh main45–192 complete body check|
|`/tmp/li_pole_theta_m15_score_budget_audit.md`|182|`756964f2e29967ddf5262618a4349aa1dcd0674fc2e26258f73e830b69764c6a`|FULL182 prior audit reuse; fresh1–39 coverage/hash/admission check, remaining claim/body source maps returned and read|
|`/tmp/li_current_theta_m15_score_budget_evidence.json`|5504|`2cf093f793452e01f841e843af7e161ac5325db1e759b36601468d3b5267e24c`|prior evidence5504 exact hash only; prior FULL corpus audit reused|
|`/tmp/li_producer_theta_undamped_cutoff_attack.md`|608|`815457a785a910206e21ad479fad5c09c1834506f6e11ac2e77967dea374c9fc`|FULL608 own previously full paper admission reuse|
|`/tmp/li_producer_theta_score_correlation_formal_plan.md`|817|`6da9fb115733ce2872f2ba5fb36e379a6eb49d4a0f3559eafa0935a7ee8c7d6b`|FULL817 own plan; pending consumers not installed assumption|
|`/tmp/li_producer_theta_terminal_history_formal_plan.md`|432|`e634d7e2a53068ccafb3e88999e123c5b1b6d7dddb934b2c0c5ce0c4c3a0d77e`|FULL432 own plan; no code/API existence assumption|
### Actual primary sources

|Path|Lines|SHA256|Scope / status|
|---|---:|---|---|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelSource.lean`|276|`1eb4512abdbfc56ad3aa07ff3be0b10c157d58d81a92a03ccb26add83665420f`|fresh ALL17–276 bodies; same-nu/factorials/compactL1/termderivative; prior full276 review|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitive.lean`|235|`19432a2d8b80329be82c8d500b1aeca07cb7f34afaf81f6a747d39275e3a8590`|fresh163–235 exact FTC/smoothness/whole mass/norm/conditionalRH; prior complete235 review|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitiveVolterra.lean`|119|`50d3f834eea44fca75ac77820a912f7d6edb9f9b57e9f359d809e1b8889a3787`|fresh27–119 full factorONE proof, true compactL1/IBP|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelFlattening.lean`|589|`ccdf4a14032fbc30aa427f40afe611691639a696fb6d613ab4bb083521eb6445`|fresh106–178 full derivative-ladder/smooth source blocks; prior ALL589 review|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockHistoryRetention.lean`|2003|`5b4ed65207f355b8761d353d23e9401967805968f5ba74088f11a9fa85e1d4fd`|fresh1540–1678 complete canonical scale/geometry/hinge/source blocks; exact pin; no fresh whole2003 read claim|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockHistoryBarrier.lean`|485|`ee2c229e7dbe6ce339e9879521ab7e2ce732f057c3950cc8f836587d68c10e35`|fresh1–145/222–246/251–421 full relied D/FTC/scale guards/strict reserve/receiver blocks; prior ALL485 peer/root gates|
|`formal/GaloisForLFunctions/RHTower/LiClockThetaScoreMeasure.lean`|497|`10929c6023cd170428d4f1f603c0d92c8711daa7ad46b084d64a11daba6be650`|fresh all returned1–113/107–214/300–407/400–EOF497 proofs; actual finite score admission only|
|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`|799|`aa6f9e7531322c7723180d4cfde4c94c73276b91027850b74d506c1d11f62040`|fresh435–463 complete normalizedM0=nu1 proof; prior whole799 review; sameR0/factorONE source|
|`formal/GaloisForLFunctions/RHTower/LiClockThetaCompactGammaMarking.lean`|335|`02539934ef19beef3b97680ded36a8b9c0c10cc85881600f82b411c354e8608a`|exactfull335 prior own complete audit, unused representation/contrast only|
|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockVolterra.lean`|246|`2a67745d549660291119c7030ff617aebf0fe1c119a1a25528e8040717a6a192`|fresh78–105 literal full response/moment series, exact germ normalization; prior full246 review|

All above bytes remain exact. Prior full mathematical audits are reused only at these verified pins. Fresh primary full/range reads and their source hashes are individually recorded in matching metadata; no fresh whole2003/799 read is asserted. The entire-D and Score/Budget paper dependencies remain paper-level where their complete formalization is pending. The Gamma-marking source is an unused representation contrast, not a hidden inference premise.

Documentary qualification: frontier/STATUS changed concurrently, so their historical whole-file pins do NOT match current bytes. At this audit snapshot frontier has438 lines/current SHA `b0b8fdd3dfade6022e966b33dcef1be83e0e37b54b11d2f5f2281c382edae410`; STATUS has2089/current SHA `c02c7a63dbbb450d4789e9f61c768648b88aca4717a7ff052573e1b8c12494c8`. Current relevant history/score/retention/barrier/envelope and OPEN entries were read. Returned primitive prose7 STATUS1637–1648 remains byte-exact at its supplied span. Root's full57 documentary migration metadata was read; moved deep prose6/7 resolve to Stage3 source-envelope with exact returned text. These documentation changes do not alter any frozen proof or primary source pin; no unchanged whole-doc claim is made.

Retrieval disposition: no returned record supplies the actual M15 mixed D-weighted finite budget. Applicable records support source normalization, L1, smoothness, strict raw score reserve, complete Volterra coefficients or generic analytic mechanisms. Others concern different probability/quantum/Weil/prime/paired-eta sources, a supplied RH receiver, or historical source-only metadata. This is an applicability statement about these123 returned records, not exhaustion, novelty or a proof that no future source producer exists.

## Final independent disposition

All F1–F12 paper proofs, complete123 corpus records, reused dependency correspondence, live primary source identities and scope/nonclaim boundaries PASS. No correction to frozen421 is requested. Strong positive survivors are dependency-closed on paper and their new Lean status is OPEN. The missing finite relative source budget, actual guarded-zero exclusion and RH remain OPEN.

Independent metadata: `/tmp/li_current_theta_finite_guard_source_audit_metadata.json`, 3310 lines, SHA256 `4be1b42a36da051df45ecb5b8ef8ebcdc1e01639564aafc7049432dbdacf3d33`. Full123 reconstruction and current primary correspondence verified without a compiler.
