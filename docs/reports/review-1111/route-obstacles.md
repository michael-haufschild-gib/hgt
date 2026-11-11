# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `65731ede04` with its working tree (2026-11-11). Fact log: `logs/review-1111-status-quo-facts.md` (cited as "log §n"). Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. Formulations are not independent mechanisms: HJ is PA; the BSY criterion of FEL belongs to CTF; PCS, DR, PW-B are retired labels. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.**
- `[L*]` Lean statement read at the declaration for this report; the declaration is listed in log §3 under the identifier given in parentheses.
- `[N]` declaration located through the corpus search index, index docstring read, statement not read (log §3.12).
- `[F]` stated by the frontier map at the checkpoint; `[KR]` stated by the scoped-obstruction ledger at the checkpoint. Read for this report, Lean not re-read. `[S]` marks a module that the frontier map grades unfinished or unintegrated.
- `[D]` deduction made in this report from `[L*]` statements; not a Lean theorem. `[C]` classical mathematics quoted from memory, not in the corpus. `[A]` assessment.
- `[P]` proved on a pipeline card at stage 2 (paper proof, Lean formalization in progress), taken as correct here: `docs/drafts/pipeline/2-fully-proven/shortest-generic-twist-family.md` (log §3.21).
- `[X]` one external source cached in the repository, outside the native import graph and not checked here: a zero-free half-plane `Re s>7/8` for ζ, Dirichlet `L`-functions and Hecke `L`-functions over `ℚ(√−3)`. The frontier map states that the native graph has no unconditional `7/8` theorem [F]. Every row that uses `[X]` carries the tag and states the native form beside it.

**Strength.** RH; ≥qRH (a zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); ≥B56 (implies `Θ<1 ⇒ Θ=½`); sub (below quasi-RH and below AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md). `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1 ⇒ Θ=½`. `S(u)` the lag structure of the cubic spline `B`, `2Re S(log p)` the prime trace; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I**: ¬AAL, a finite isolated top layer at `β<1`. **World II**: AAL ∧ ¬ZAL. The **edge world**: `Θ=Θ∞=1`. The **depth** of a zero is `|Re ρ−½|`. A **tangent datum** is a depth `0<b≤½`, a finite set of positive ordinates and a multiplicity for each; the **normalized trace** at depth `b` is `2Re S(u)e^{−bu}`. **Comb pairing** of a real divisor `D=Σc_nγ_n`: off the diagonal `½(1/|m−n|+1/(m+n))+Λ(n/m)` (jets plus contacts), on the diagonal `−log(n/2π)`; `d₁=Σc_n/n`, `d₂=Σc_n`; **comb form** `2d₁d₂−D·D`. A **window of ratio `Q`** is `(N,QN]`, its **aperture** `½log Q`. A **system** is a weight system `w` with a **mass** `m` (log conductor, or log height of a modulated packet); `w` is **dominated** if `|w|≤Λ`; the **rung** of an aperture `a` is `κ=a/log m`; the **trivial aperture** is the supremum of the apertures at which every dominated system is feasible. The **Liouville twist** is `w(p^k)=(−1)^k log p`. `JasDressedPSD σ`: positive semidefiniteness of the `σ`-dressed lag aggregate. The **signal** of a kernel `G` is `(1/2π)∫G(2+it)Z^{2+it}dt`; the zeta kernel is `exp((s−c)²)/((s−1)ζ(s))`. A **step packet** is `σ_je^{u/2}` on the windows `(log(R+j),log(R+j+1)]`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `∃K`: `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside at most `Ce^{δT}` primes per window (`δ<1`); ⇔ the upper bound alone on undeleted windows; ⇔ `ℕ`-counts on the surviving prime rays with quadratic limit the plane defect; ⇔ one growth exponent for all even local moments; ⇔ the absolute value | [L*] (S1–S6) | sign, prime count and count door are one number per prime on sparse windows |
| A tempered configuration with `\|Im ρ\|≥4`, logarithmic local counts, `\|N_Z(T)−N_ζ(T)\|≤εT log T` and unattained top `½+Θ` has floors `K` on windows of a radius `R→∞`, `R=o(log T)` | [L*] (S8, S9) | below the logarithmic radius no receiver at the level of configurations decides RH |
| ζ with a finite nonempty top layer of at most `k` positive ordinates has, on every late window of length `(k+1)π/67`, a point below every floor; `n` modes of frequency `≥Γ` keep one sign on a length `≤nπ/Γ`; floors with constants depending on `k` give AAL | [L*] (S10–S12) | world I is seen on bounded windows |
| At `b_*=Θ−½` the normalized trace is in exactly one of four sectors: RH (Bohr almost periodic); top line empty (trace `→0`); top line finite nonempty (trace approaches a nonzero trigonometric polynomial); top line infinite (no trigonometric polynomial limit). Excluding the third gives AAL | [L*,S] (N1, N2) | AAL is the absence of one asymptotic shape |
| AAL ⇔ for every line `Re s=½+h` the number of zeros to its right is at most one or infinite | [L*] (FFA5) | AAL is a unit gap |
| A one-sided floor on late windows of one fixed length `L` has a finite-stratum model (an isolated pair at ordinate `2π/(3L)`); two-sided smallness of the normalized trace on windows of one length leaves the top line of ζ empty or infinite | [L*] (FFA8, FFA16) | the two forms of non-attainment differ |
| Every tangent datum is the top layer of a finite tempered symmetric configuration; of a nonnegative density with a simple pole (any `Θ<1`); of an Euler product over natural norms with natural coefficients, linear counting and continuation to `Re s>½`, with the prescribed multiplicities; of an Euler product over rational primes with repetition for `17/30<Θ<1` | [L*] (FFA12–FFA15, N3) | the explicit formula, positivity, Euler products over integer norms and counting put no condition on a finite top layer |
| AAL, or `Θ<1` and for every `β∈(Θ,1)` a meromorphic function with an Euler product over the rational primes, multiplicative coefficients `0≤a(n)≤C_εn^ε`, polynomial bounds for itself and its inverse, exactly one pair of zeros right of `Θ`, and a pole in the left strip. The property "the right zeros are the divisor of an Euler product over natural norms" has floor `½` | [L*] (M1, M2) | the Euler product with bounded coefficients, without the functional equation, does not give the abscissa law; a producer has to use the Euler product on the function, not on its zeros |
| `Θ<1 ⇔ Θ∞<1`; failure of quasi-RH is `Θ=Θ∞=1` with AAL; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the supremal negative index on real packets is `0` or `∞` | [L*] (S13, S16); [F] | a failure of RH is world I or world II; three atoms |
| An entire function with the Riemann functional equation, Gamma factor, residue one, order `≤1` and the zero count of ξ within one has all zeros simple, off the line, approaching it; two-scale Euler products over natural norms realize `(Θ,Θ₂,Θ∞)=(β,θ₂,θ)`, `½<θ≤θ₂<β<2/3`, and refute every graded repulsion bound | [L*] (C6, S15) | Landing and DH follow from neither structure alone |
| For `η>0` and large `q`: every dominated system has the floor `½(1−e^{−η/2})log q∫\|F\|²` at `a≤log log q−η`; at `a≥log log q+η` the Liouville twist and `−Λ` fail on the odd polar packet and `Λ` without pole plane on the even one; the trivial aperture is `log log q+o(1)` | [L*] (L1–L3) | sizes prove the sign to rung `1−o(1)` in the conductor aspect and nothing beyond |
| At height `t`: floor `½(1−e^{−η/2})log\|t\|∫f²−5∫f′²` at `a≤log log\|t\|−η`; a dominated system fails at `log log t+log(π/2)+η` | [L*] (L4, L5, SA6) | the same in the height aspect, with additive gap `log(π/2)` |
| One theorem: cancellation `(C,γ)` with `2γκ<1` pays the sign on bounded shapes to `a≤κ log log q`; positivity on tests of aperture `κ log(A log\|γ\|)` forces a second off-line zero near a zero of depth `δ>1/(2κ)`; a bounded dyadic Möbius moment at length `T^θ`, `θ>1`, confines high zeros to depth `<1/(2θ)+ε`; quasi-RH is seven equivalent power savings | [L*] (SA1) | one exchange rate `γ=δ=1/(2κ)=1/(2θ)` |
| At aperture `κ log log T` the paired sign on bounded shapes fails only on a set of heights in `[T,2T]` of measure `≤T^{1−1/(2κ)+ε}` | [L*] (SA2) | the sizes fail at aligned heights only |
| For every `a>0`, `0<δ≤½`: a tempered configuration with `N_Z=N_ζ+O(T)`, logarithmic local counts, positive on `[−a,a]`, with zeros of depth `δ` at unbounded heights | [L*] (SA5) | the sign at a fixed aperture is not a strip at the level of configurations |
| RH ⇔ `JasDressedPSD 1` ⇔ positivity at level one on all large primes; a level `σ≥1` on large primes gives `\|Re ρ−½\|≤σ−1`; for `½≤b<1`: `Θ≤b` ⇔ the signal of the zeta kernel is `O(Z^{b′})` for every `b′>b`; the signal is `Σμ(n)·signal(poleKernel)(Z/n)` | [L*] (J1, FCT2, F1) | levels, half-planes and the exponent of one smoothed Möbius sum are one scale |
| Over `ℚ(ζ₃)`: if zero-freeness of the Hecke family in `Re s>β` gives every ray class character a sum with a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with its corrected signal, `a₁,a₂<β` common, for every `β>σ₀`, then `Θ≤σ₀` | [L*] (N5) | the half-plane route is one implication whose premises are two estimates |
| Exponent budget of the published probe: boundary in `(7/8−1/4000,7/8]` with its row count; RH-quality bounds for every nonprincipal row summed trivially do not go below `13/15`; at twist order `n` the balanced floor is `1−4/(5n)`, the conductor corner `8/9`, `25/28`, `49/54` for `(2,6)`, `(3,4)`, `(4,3)`; two or more row variables give `≥1`; evaluating the reflected rows through the same twists returns the zero | [L*] (FCT11–FCT17) | the room inside the Gauss-sum probe is `[13/15,7/8]`; in positive form the boundary is `½+(1−1/n)θ/2` [L*] (M3), and a generic mean square over the principal `n`-th-power twists at the exponent `θ` is equivalent to that half-plane: the least `θ` is `(n/(n−1))(2Θ−1)` [P] (SG1); in the twist exponent the class of reflection, slots and large sieves has the floors `1`, `9/10`, `(5n−8)/(5(n−1))`, `(n−2)/(n−1)` [L*] (TB1–TB8) |
| `CombBezoutShift c ⇔ c≤0 ∧ RH`; one contact changed by `t` at `n₀`: Bézout ⇔ RH ∧ `2\|t\|/√n₀≤c`; tree of `p` at length `ℓ`: Bézout ⇔ RH ∧ `ℓ=log p`; along the price path of any `n₀` Bézout on all packets is RH at every parameter | [L*] (G1–G3, AGZ3) | constant, contacts and tree lengths are forced; a path transports no sign |
| RH ⇔ exactly one positive square of the intersection Gram on packets; the negative index counts the distinct right zeros for ζ with Dirichlet characters, for every primitive ray class character of every number field, for a Dedekind zeta function, and for the class characters together | [L*] (G4, G5, AGZ6–AGZ8) | the Hodge index is the exact count of the right zeros |
| RH ⇔ `𝔚_{3K+1}≥0` on step packets of `3KR` blocks for all `K,R` (finite matrices with elementary entries) ⇔ eventual exact nonnegativity of the comb form on every fixed ratio window ⇔ a positive coefficient-mass floor `γ(Q)` on each ratio window; `r≤#`right zeros ⇔ eventually `r≤` the robust comb index | [L*] (AGZ1, AGZ2, HFP1–HFP3) | the inequality at finite scale is an equivalence in four forms |
| RH ⇔ some feasible weight system at every aperture; feasible systems converge to `Λ` in every coordinate; feasibility at an aperture ⇔ spectral kernels positive definite on node intervals; the pencils `ξ(s+h)+ξ(s−h)` and the cleared Eisenstein constant term over their dominant halves are no Dirichlet series | [N]; [L*] (FFA21–FFA23, FFA27, N4) | the existence half of the sign carries no freedom in the limit |
| The clock regulator lies below Weil's form at every cutoff; `Λ(s)/Λ(s+N)` has at most one right zero ⇔ RH; the heat flow has the nonreal count of its limit; a form with one negative square in which the right zeros are a symmetric spectrum gives RH | [L*] (FFA20, FFA24–FFA26) | no regulator of the corpus supplies a unit gap before the limit |
| A bounded holomorphic Dirichlet series on `Re s>x` (any `x`) whose zeros are zeros of ξ has no zero; a Wiener expansion on a strip with an interior zero has nonsummable residues and admits no `ℓ^p` transport of its zeros to zeros of ζ | [L*] (CTZ1–CTZ4) | ξ has no bounded or Wiener constituent with a zero |
| `R_polar=R_halfline`; RH, or `R_polar<W`, or `R_polar=W` finite with every critical half-line ground state orthogonal to the polar source | [L*] (C1–C3) | the critical curve has one undecided case (B104) |
| RH through height 67; RH through `windowHeight(a)` gives the sign on `[−a,a]`; `log log log windowHeight(a)=c·a^{4/3}+log 138+o(1)` for the construction | [L*] (J2, J3); [F] | each window is a finite-height statement at triple-exponential cost |
| Displaced twisted second moment of `ζ·`(real polynomial of length `T^θ`), `θ<½`, bounded by its main terms plus a power saving; simple critical zeros `≥(0.67250071−ε)N(T)`; positivity cost of a pair-correlation certificate `≥1+3/π²` at every bandwidth | [L*] (J5, C4); [KR] (TT1) | the mean-value ladder is proved below the square root; positivity alone does not certify 70% |
| Universal horocycle exponent `sup=1−Θ/2`; with a nonzero Euler polynomial filter `sup=1−Θ∞/2`, never above `3/4` | [L*,S] (N8) | on the horizon AAL is: no finite filter accelerates the relaxation |
| `[X]`: `Θ≤7/8`. Natively: the cube of the normalized composite cubic Gauss sum is the ideal Möbius value times a phase; `g(χ)^n=−card F+z(μ−1)²` for odd order `n>2` | [X]; [L*] (W5, F3) | one producer, external; its source identity and its frame are native |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a` follows from verification to `windowHeight(a)` |
| M2 Calibration | window cones, feasible sets, margins | feasible sets nonempty at every aperture ⇔ RH; they shrink to `Λ`; margins decay doubly exponentially [KR] |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | RH ⇔ `Ψ` locally bounded on precontact intervals [N] |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | sharp receivers; horocycle exponents are `1−Θ/2` and `1−Θ∞/2` |
| M5 Square-root cancellation | smoothed prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH [L*] (C8); the flow has the count of its limit |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros visible at their rung; clusters hide [KR] |
| M8 Finite-layer receiver | damping filters, centred Vaughan currents, half-period deletion, non-attainment | complete in world I; four-sector classification of the trace |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level [F]; at one prime `p^{11/12}` [F] |
| M10 Count | nonnegative count with quadratic Tate limit | hyperelliptic curves [L*] (C11); over ℤ the count of sections in boxes has no quadratic term [L*] (AGZ10) |
| M11 Orbit at finite time | prime phases, returns, resonators | depth by Baker; breadth to VK; resonator means to `κ<2σ−1` [F] |
| M12 Critical compactness | thresholds, pole channel, half-line ground states | three-way classification [L*] |
| M13 Topology of the prime complex | nerve, persistence, orientation cover | centred count `M(N)` [L*] (C12); weight `½` ⇔ RH [F] |
| M14 Infinite-rank elimination | towers, thick sets, attained tops | with an attained top a thick crude count is RH [N] |
| M15 Prime-degree sampling | logarithmic windows, exceptions, upper side, counts, moments | complete receiver [L*] |
| M16 Intersection on half-products | adelic carrier, Green kernels | invariant glued diagonal refuted [KR]; critical adelic inverse unbounded [L*] (H3) |
| M17 Absolute geometry | square, contacts, carries, rings, paths | forced data; exact index for every Hecke character; paths transport no sign |
| M18 FE rigidity | Hamburger, defects, prime measures | countable systems with an `L²` defect are the rational primes [L*] (C13); continuous prime measures keep every zero [L*] (W1) |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing; all open for ζ |
| M20 Families and monodromy | gauge torus, covers, towers, class characters | fixed-part laws; the base has weight `1/d`, `1/h` [L*] (G10, AGZ8) |
| M21 Index and limits | index law, unit gaps, sizes on a circle | RH ⇔ limit of index-one functions [L*] (C5); unit gaps pass to limits; no approximant with a gap |
| M22 Separation | ordinate injectivity, digit calculus | receiver [N]; optimal ⇔ greedy [L*] (J8) |
| M23 Hodge lattice at finite scale | comb pairing, block averages, step packets | RH in four finite-scale forms; robust index = right zeros |
| M24 Arithmetic constituents | recurrence against density, jump law, prime contraction | none with a zero in the bounded and the Wiener class |
| M25 The ladder | mass, aperture, rung | sizes to rung `1−o(1)`; one exchange rate |
| M26 Family continuation | signal of a reciprocal kernel; two estimates; reciprocity | frame for every ray class character; budget room `[13/15,7/8]`; `[X]` |
| M27 Dressed positivity | lag aggregate at a level | level one ⇔ RH; level `σ` ⇔ half-plane `σ−½` |
| M28 Floor-free receivers | homogeneous, unit gap, certificate, amplification | each kind has its receiver and its kill (block S13) |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators | amplify or reshape a certificate, produce none [KR] |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT.

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH [F]; `R_polar=R_halfline`, the charged-ground-state separation and the three-way classification [L*] (C1–C3).
- Complete tilted-spline matrix positive definite at every fixed overlap eventually, and at `c≤2K₁(log N)^{1/8}` [L*] (W11); no countable square-bounded family of holomorphic multipliers dominates the depleted kernel [KR].

| | Obstacle | Strength |
|---|---|---|
| A9 | explicit constants of the eighth-root horizon and the Beurling schedule | — |
| A13 | near-gcd charges and periods beyond the admissible scale (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | whether a critical half-line ground state at finite `W` can be polar-orthogonal | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow and the aperture–height exchange
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL, SA, ACCE.

Established:
- RH ⇔ `W≥0` on every window [N]; RH ⇔ `Ψ` bounded on every bounded precontact interval [N].
- `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]`; RH through height 67 [L*] (J2, J3); the height of the construction is triple exponential in `a^{4/3}` [F].
- RH ⇔ every aperture admits a real weight system with nonnegative Weil form; ¬RH ⇔ some aperture admits none [N]. First contact: for `2a<log 2` feasibility does not depend on the weights; above it `|w(n)|≤√n(log(1+1/r)+C)` with the pole plane; a neighbourhood of `log 2` is feasible for `w(2)` up to `a=181/500` [L*] (L10, L14, G11).
- Certificates: for every `n≥2`, `ε>0` there is an aperture beyond which every feasible system has `|λ(n)−Λ(n)|≤ε` [L*] (FFA21). Margins: best margin of a window `≤K exp(11c/2−πe^{2(c−2)})` [KR]; proved floors `(1/20000)/2^k` through `a_k`, `a_∞<0.3621` [F]/[KR].
- Index in the aperture: immediately right of an aperture the index is the negative index plus the nullity; resonant apertures are finite below every bound [F] (ACCE1).
- Positivity at a camera aperture forces `|depth|<exp(−c log³(T/2π))` at height `T` [L*] (W12); a configuration with ζ's local counts hides a zero of depth `δ` at height `T` to aperture `(log T)/36` [KR].
- The ladder (block S12).

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A132 | the order of the verification height: sizes pay all frequencies above `exp(c·e^a)` [D]; a lower bound for the margin of the verified part would give a double-exponential `windowHeight` (unverified) | — |
| A117 | end points of the feasible interval of `w(2)` on the first selective window | — |
| B1, B2, B4, B5 | sign on every window; bounded oscillation of `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |
| B176 | whether RH through `exp(C·e^{2a})` gives the sign on `[−a,a]`: a lower bound for the margin of the verified part | sub / method |
| B179 | a symplectic structure in which the index in the aperture is a Maslov index | producer |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo, FFA.

Established:
- The five forms of the minimal face on logarithmic windows [L*] (S1–S6); power-thin exceptional sets [L*] (S7); width `≤σ` ⇔ the same with `Kp^σ` [F].
- `r√T` windows; two fixed primes on such windows [F].
- Half-period law; finite top layers on windows of length `(k+1)π/67`; length-dependent floors give AAL [L*] (S10–S12).
- Counter-configurations below the logarithmic radius, also density-matched and at prime samples [L*] (S8, S9); one-sided floors on windows of one length have finite-stratum models [L*] (FFA8).
- A global floor `−K` bounds the weighted absolute mass with sharp coefficient two [KR].

| | Obstacle | Strength |
|---|---|---|
| A78, A89 | cluster form of the separated-window theorem; a prescribed radius in the sub-logarithmic model (unverified) | — |
| A58, A59 | effective gap iteration; residue-class primes [C] | — |
| B130 | the bound itself on any decisive sample | RH (≥qRH at `p^σ`, `σ<½`) |
| B144 | separation of the deep off-line ordinates of ζ | sub |

### S4. Continuation, nodal geometry, index and constituents
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidates: W1C. Programmes: NGF, FFP, ADO, AES, IRP, CTZ.

Established:
- RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*] (C8); `N_d≤300√(d log d)` for `log d≥6.1·10⁶` [L*] (C9); RH ⇔ infinitely many Jensen degrees real-rooted [N]; `N(t)≤1` on times accumulating at `0` gives RH, and with finitely many nonreal zeros `N(t)` is their number for small `t` [L*] (FFA25).
- RH ⇔ ξ is a locally uniform limit of conjugation-real entire functions with at most one right-half zero [L*] (C5); a splitting of ξ with sizes on one circle bounds its zeros in the disc by the degree of the factored half [L*] (K1); a unit gap of analytic approximants passes to the limit [L*] (FFA26).
- RH ⇔ the prime lag function is positive definite on `ℝ` [N].
- Constituents: none with a zero in the bounded class (any abscissa) and in the Wiener class of a strip; one zero forces infinitely many unmatched zeros; a Wiener expansion with an interior zero has nonsummable residues with no purity premise and admits no `ℓ^p` transport of its zeros; every box has a Dirichlet polynomial with exactly the zeros of ξ and no fixed length works at all heights [L*] (CTZ1–CTZ4, K3, K4). The jump law on strips with countably many poles of summable residues [L*] (K2).
- The alternating series `(1−2^{1−s})ζ(s)` converges on `Re s>0` and has on the open strip exactly the zeros of ζ [C]: the class of convergent, unbounded Dirichlet series contains a constituent with every zero [D].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B24, B25 | collisions at small time, all heights; frequency below one | RH |
| B22, B23 | outer roots of the Jensen polynomials; `N_d` bounded | RH; ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ; a splitting of ξ with certified defect | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |

### S5. Near-line geometry, long moments and the census
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation.

Established:
- RH ⇔ cofinal polynomial boundedness of the long Möbius second moment with one exponent [N]; dyadic boundedness at length `T^θ`, `θ>½`, leaves finitely many zeros beyond depth `1/(2θ)+ε` [L*] (J6).
- For `0≤θ<½`: the displaced twisted second moment with its main terms and an arbitrary power saving [L*] (J5); errors of orders 0, 1, 2 keep the saving [F]; the `(ζ+λζ′)Ψ` detector is three moments plus jets and two taper terms, and for the linear mollifier its integral is an explicit main expression plus `O(T^{7/8})` [F] ([S] for the remainder).
- Census: simple critical zeros `≥0.67250071` [L*] (C4); five consecutive simple critical ordinates at `≥N(T)/5000` starts [F]; every continuous integrable `g≥0` with Fourier transform `≤0` outside the unit band has positivity cost `≥1+3/π²>13/10`; a pair-density deficit `0≤g≤1` supports diagonal mass `<13/10` only [KR] (TT1, TT3).
- Finite symmetric relocation of zeros is invisible to quadratic tests of length `o(T²)` on fixed lines right of `½` [KR] (APD1).

| | Obstacle | Strength |
|---|---|---|
| A134 | the main expression of the linear Levinson detector below the square root: a proportion of critical zeros from the native moments (unverified) | — |
| A18, A21 | twisted moments past the square root [C]; census items | — |
| B57 | depth density `o(T)` | sub |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)`: arithmetic upper control beyond frequency one | sub |

### S6. Production, precision and the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established:
- `c₁/(√K(1+log K))≤rate` for every producer of alphabet `≤K` [L*] (W2); rates `K^{−a}` for all `a<½` give RH [F]; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [N]; RH ⇔ Robin's inequality at `lcm(1,…,n)` for large `n` [N].
- Orientation cover: centred count `=M(x)` [L*] (C12); weight `½` ⇔ RH [F]. AAL, or `|M(x)|≤Cx^β` with `β<1` [L*] (C7).
- Every bilinear statement is invariant under the Liouville twist [L*] (W3).
- Stepanov at one prime: `|Σ_{n≤p}e(an^p/p²)|≤5p^{11/12}` [F].

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients; singular indices past the cubic cutoff | — |
| B48, B49, B50, B53, B54 | deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | past Vinogradov–Korobov | sub |
| B56 | `Θ<1 ⇒ Θ=½` | ≥B56 |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers and the modular horizon
Routes: PM, HAT-C. Candidate: W1C. Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT.

Established:
- RH ⇔ every compact pulse rings down at the quarter rate ⇔ positivity of the reflection Krein forms [N]; ⇔ horocycle error `O(y^{¾−ε})` of one cuspidal function; one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero [F].
- Horocycle exponents: unfiltered supremum `1−Θ/2`; with a nonzero Euler polynomial filter `1−Θ∞/2`; no filter passes `3/4`; ZAL ⇔ filtered rates approach `3/4`; AAL ⇔ no filter accelerates past the unfiltered optimum [L*,S] (N8).
- Regulators: the clock lies below Weil's form at every cutoff, and a floor `−C‖f‖²` at one cutoff per large aperture gives RH [L*] (FFA24); the tower of height `N` is the logarithmic derivative of `Λ(s)/Λ(s+N)` plus Robin and polar terms [L*] (H2); for every `N`, RH ⇔ the corrected energy is at least minus the jump tail ⇔ the raw energy is at least minus its full defect [L*] (H1); the tower quotient has a unit gap ⇔ RH [L*] (FFA26).
- No bounded critical inverse of the adelic adjacency; the critical spherical operator integral is not integrable [L*] (H3).
- No Maass cusp eigenvalue `0<λ<3/16` for groups containing `Γ(N)` [L*] (J7).
- RH ⇔ an `ℕ`-valued count with Tate limit the integer probes [N]; on a hyperelliptic curve the defect of an integral class is a natural number, quadratic on rays [L*] (C11).

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents | — |
| B68 | independent reflection Krein positivity, Krein flux, dispersion bound | RH |
| B71 | universal decay `e^{−t/4}`; horocycle, Farey, Narain or cavity rate `y^{¾−ε}` | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one eigenform | indep. |
| B114, B117, B171 | a realization of the partner involution outside the excluded classes; a regulator with a unit gap before the limit; a form of signature `(1,∞)` in which the right zeros are a symmetric spectrum | producer |
| B178 | a relaxation lower bound for a horizon with a cusp: a resonance-free strip from a principle that fails under deformation of the group | ≥qRH (producer) |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling branch), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, IRP, APD, AAD, TAPO, FFA.

Established:
- `Θ<1 ⇔ Θ∞<1`; ¬quasi-RH ⇔ `Θ=Θ∞=1` ∧ AAL [L*] (S13). RH ⇔ ZAL ∧ B13 ∧ Landing; Landing is local below no height [F]/[L*] (S14).
- One-structure calibrations: the functional equation with ζ's Gamma factor and count does not force landing [L*] (C6); Euler products over natural norms refute every graded repulsion [L*] (S15) and realize every finite divisor right of the line [L*] (FFA12, N3); rational primes with repetition for `Θ>17/30` [L*] (FFA13); a continuous Beurling system with integer count `N(x)−ρx−C→0` has a one-off pair [N] (X1, X2). Count `n+o(log n)` forces the rational primes [KR] (X3).
- The integer count of the models: a discrete system with integer norms and count remainder `o(log n)` is the rational primes, and every other one has remainder `≥c·log n` at arbitrarily large `n`; the odd primes with extra labels of norms `3` and `4` have remainder `O(log²x)` and exactly the zeros of ζ on `Re s>0`; a multiplicative sequence with values in `{0,1,4}` has `−3≤N(x)−x≤0` and a zero in `½<Re s<1`; the Euler products over natural norms with a prescribed divisor have a count known in the mean only [L*] (LF1–LF4, LF7).
- World I receivers: non-attainment on windows, for `ψ(x)−x`, at the primes; the unit gap; the quantum of a multiplicity; one growth exponent for all even window moments; the four-sector classification [L*] (FFA4–FFA7, FFA9, FFA16, FFA17, N1, N2). A moment of one order `2k` with exponent `A` reaches depths `≥A/2k` only; bounds of all orders with one exponent are sup bounds [L*] (FFA10, FFA11).
- World I instruments: prime filters recover the top residues; the growing-order current reduces to centred type-II cofactors `≤3t⁷¹`; the unweighted near-diagonal row is summable [F] (ELT1).
- Replication: under a finite nonempty right layer every locally uniform limit of normalized translates along a phase return vanishes [L*] (FFA19).
- B13 ⇔ the supremal negative index on real packets is `0` or `∞`; that index is the number of distinct right zeros [L*] (S16).
- Level one on large primes gives AAL, B56 and `Θ=½` [L*] (L13).

| | Obstacle | Strength |
|---|---|---|
| A47 | constants of the one-quartet world (unverified) | — |
| A120 | a finite nonempty stratum with both structures in Lean: Selberg zeta functions of surfaces with a small eigenvalue [C] | — |
| B13, B138 | finite stratum; landing for ζ | sub |
| B141 | Deuring–Heilbronn for ζ: `¬AAL ⇒ ZAL` | sub |
| B83, B170 | AAL; non-attainment for ζ in any of its receiver forms | sub / AAL |
| B89, B112, B128 | a bounded aligned return at each right zero; FE into vertical transport; replication by a mechanism other than normal families | sub |
| B145 | the signed, prime-weighted centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; a bound on a sampling set; positive-measure lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method |
| B182 | the least remainder of the integer count of a discrete system with integer norms that has a zero right of the line which ζ lacks: `N(x)=Ax+O(x^β)` with `β<1`; with `β<½` | method (a construction); the negative side is of GRH type |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT, every route at all heights. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, SPAL, ALST.

Established:
- Near-total `p^{−1/2}`-mass returns of the primes `≤y` need `log t>(log y)^{3/2−ε}` [F]; a strip of depth `h` excludes heavy identity returns up to `exp(ηT)` [F]; under `Θ≤b` heavy returns need `log t≥c·y^{1−b}` [L*] (SA4).
- The return transfer gives `Θ<1 ⇒ RH`, and under `Θ<1` it is equivalent to RH; RH gives it without its premise [L*] (J12, FCT4).
- For `½<σ<1`, `κ<2σ−1`: the dyadic mean of `|Rζ|²` is the convolution diagonal [L*] (W8) / [F].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| B46 | proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97, B137 | constant-precision first return past the VK rung; a collective depth floor uniform in `π(y)` | sub |
| B148 | the transfer of candidate S3 | RH under a strip |
| B121 | freezing control beyond the precision cap | sub |

### S10. The diagonal, counts and absolute geometry
Routes: ACS, HF, HAT-C, PM (count branch), LI. Programmes: SOSZ, HAT, AGZ, HFP, AE, RIAC, HHAC, CTH, LST, KPA.

Established ([L*] with log identifiers):
- Forced data (G1–G3); the price path at every `n₀≥2`: the functional is the zero sum plus a square, monotone along each ray, with a threshold on packets of length `L` that is `0` iff ℤ satisfies Bézout at `L`; on all packets the inequality along the path is RH at every parameter; the tree-length path exists at `2` only (AGZ3–AGZ5).
- Index: one positive square ⇔ RH (G4); exact count of right zeros for ζ with Dirichlet characters (G5), for every primitive ray class character of every number field (AGZ6), for a Dedekind zeta function through the ideals (AGZ7), for the class characters together with pole-plane weight `1/h` (AGZ8). Below the first contact a large discriminant gives the inequality with margin `∫f²/5000` (AGZ9, G6).
- Sections and counts: planar restriction is an equality of ideals (G7); the count on two graphs is quadratic on rays and fails the parallelogram law (G8); the sections of the first `N` graphs in aligned boxes number the volume over `N!`, with no quadratic term (AGZ10); the system of the squares fails on its own comb (G9); cyclotomic towers (G10).
- Finite scale: RH ⇔ the sign of `𝔚_{3K+1}` on step packets ⇔ eventual floors `−ηΣc²` on every ratio window ⇔ eventual exact nonnegativity ⇔ a positive mass floor on each ratio window (AGZ1, AGZ2, HFP1, HFP2); floors on block-constant divisors give RH (J11); the robust index counts the right zeros (HFP3); the unshifted index lies between the aperture index and index plus nullity [S] (HFP4).
- Tails: Weil's form on the comb is a quadratic form in the increments with rows the remainder of the prime number theorem (AGZ11); the forms of logarithmic tails per degree point tend to `k!l!Re Σ_ρρ^{−k−1}(1−ρ)^{−l−1}`; the Laguerre tails tend to the paired Li coefficients, with and without damping (HFP5, N6 [S], N7).
- Carrier: no adelic-invariant glued kernel has Weil's diagonal [KR].

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests at verified scales | — |
| A133 | Artin characters of non-abelian extensions: the index law per character; the Dedekind index of the non-abelian ring of the cube roots of two is a theorem [L*] (M4) (unverified) | — |
| A135 | the step-packet matrices at window ratios 4 and 7 as certified finite statements (unverified) | — |
| B87 | a count on the rays `Γ_1+Γ_p`, defined without `Q` | RH |
| B88 | the sign of the comb finite part | RH |
| B149, B169 | Bézout for the comb pairing from a property of the object; a group with a doubling on which the defect is a canonical height | RH (producer) |
| B152 | the sign on step packets, in any of its four finite-scale forms | RH |

### S11. Families, rigidity and exactness
Routes: ACS (tensor branch), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established:
- Fixed-part laws; sublinear tensor growth with the trace of ζ retained ⇔ RH [N]; pole-preserving gauge deformations are isozeric [KR].
- Countable Beurling systems with an `L²` functional-equation defect are the rational primes [L*] (C13); positive continuous prime measures are not rigid and keep every zero [L*] (W1).
- Carlitz–Goss: optimal ⇔ greedy [L*] (J8).
- `ξ(s+a)ξ(s−a)` keeps a functional equation and an Euler product and moves every abscissa by `a`; strip self-improvement for the family holds iff `Θ=1` [KR].

| | Obstacle | Strength |
|---|---|---|
| A115 | the Newton polygon of the Carlitz–Goss zeta function from the greedy optimum [C] | — |
| B86 | positivity of the endpoint character at unbounded rank | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The ladder, the level and the signal
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, RHTower `QuasiRH*`, CDG.

Established ([L*] with log identifiers):
- Sizes and fakes (L1–L5, SA6); feasible sets between an `ℓ¹` ball and a box, convex, decreasing, finitely determined (L3, L10); bounded shapes do not decide feasibility (L11).
- Exchange (L6–L9, SA1); the first conductor rung forces primes with both signs below `e^{2η}log²q` (SA3); exceptional heights of measure `≤T^{1−1/(2κ)+ε}` (SA2); the mean square of the contact polynomial (L12).
- Given `Θ≤b`: the rung `(2b−1)κ<1` for the centred contacts, positivity on large primes above the level `b+½`, return-free windows (SA4).
- Level and signal (J1, L13, FCT1–FCT3, F1); family frame for all ray class characters, with holomorphic corrections, over `ℚ` and `ℚ(ζ₃)` (FCT5, FCT6, N5).
- Source: the cube identity (W5); the sign law at odd and even order (F3); one Jacobi sum carries the sign (FCT9); no cancellation over the exceptional frequencies of a coprime column pair (F4).
- Budget (J10, FCT11–FCT17); positive form: the target occurs among its twists, boundary `½+(1−1/n)θ/2` (M3).
- The budget in the twist exponent `θ=(2n/(n−1))(σ₀−½)`: floors `10/9` (optimal sextic multiplicative large sieve on the reflected rows), `1` (additive planar sieve without slots; the dual diagonal), `n/(n−1)` (two or more row variables), `9/10` (published geometry, binding bin), `(5n−8)/(5(n−1))` (floor bin summed trivially, every order, both Gram regimes), `(n−2)/(n−1)` (rows of nonnegative rescaled length without the dual-length term); reflected rows through the order-`n` twists return `(n/(n−1))(2β−1)` (TB1–TB8).
- The law of a twist family [P] (SG1–SG3): the principal `n`-th-power subfamily has a generic mean square of the Möbius sums exactly for `θ≥(n/(n−1))(2Θ−1)`, attained, zero iff RH; the full Jacobi family is generic at every `θ` iff RH and GRH for the quadratic twists of odd squarefree modulus hold; positive squarefree weights are not generic below `n/(n−1)`. B177 is answered by these statements.

| | Obstacle | Strength |
|---|---|---|
| A118 | `[X]` in the native graph: removal of the cube sum in the source comparison; the properties of the corrections `H_η`; the direct and the comparison saving uniformly in the character; reflection of the completed theta row; quadratic and sextic large sieves over `ℤ[ω]`; the zero detector | — (given `[X]`) |
| B159 | a rung `κ>1`: a power saving of the contacts on the integers between `m` and `m^{2κ}`, uniform in the height, that fails for the Liouville twist | ≥qRH |
| B156 | clusters on a rung for ζ: arithmetic cluster exclusion | method |
| B160 | `JasDressedPSD 1` | RH |
| B161 | the signal bound `O(Z^b)`, `b<1`, natively | ≥qRH |
| B174 | the density of sextic twists with a zero near real part `0.69`: the room `[13/15,7/8]` of the probe | sub (given `[X]`) |
| B175 | a bound for the nonprincipal rows of a twist family with cancellation across the rows, not passing through the twists: a twist exponent below the floor bin `(5n−8)/(5(n−1))` | producer (below `13/15`); of the strength of its half-plane [P] |
| B180 | the reflection of the completed theta row without Eisenstein series | method |
| B181 | the comparison estimate at `7/8`: removal of the cube indices, the corrections, uniformity in the character | producer lemma |

### S13. Floor-free receivers and their kills
Routes: every route (as a filter on proposed estimates). Programme: FFA.

Established ([L*] with log identifiers):
- Floors: what holds for every tempered symmetric configuration has floor `½`; a floor of exponent `σ` has floor exactly `σ`; a mechanism that reads only ordinate counts has floor `½` (FFA1–FFA3); so has everything a zero configuration can carry at once, the Euler product over natural norms included (M2).
- Homogeneous kind: a floor of the clock regulator at one cutoff per aperture gives RH; the regulator lies below its limit (FFA24).
- Unit-gap kind: AAL ⇔ at most one or infinitely many zeros right of every line (FFA5); the quantum of a multiplicity (FFA17); unit gaps pass to limits; the tower and the heat flow have the count of their limit (FFA25, FFA26); an index-one realization gives RH (FFA20).
- Certificate kind: feasible systems converge to `Λ` (FFA21); feasibility is positive definiteness on intervals and tapered kernels are transforms of positive measures (FFA22, FFA23); the pure objects with ζ's Gamma factor are no Dirichlet series over their dominant half (FFA27, N4).
- Amplification kind: one exponent for all even window moments gives AAL; one order reaches depth `A/2k`; all orders are sup bounds (FFA9–FFA11).
- Symmetrization: no convergent linear statistic is monotone under projection to the line; additive functionals of the depths are functions of the inner masses (FFA28, FFA29).

| | Obstacle | Strength |
|---|---|---|
| B170 | non-attainment for ζ | AAL |
| B171 | a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) |
| B172 | a nonlinear functional that decreases under projection to the line | producer |
| B173 | a two-sided subexponential bound of the trace on late windows of one length | AAL (RH on those windows) |

## 3. Live routes

Receiver statements are `[N]` (log §3.12) unless marked; open estimates are as stated by the frontier map [F].

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or positive definiteness of the prime lag, or an attained top with an `O(√X)` prime deviation on a thick set of scales → RH.
- **Established:** endpoint energy bounded ⇔ RH; RH ⇔ the prime lag is positive definite on `ℝ`; RH ⇔ attained top ∧ thick `O(√X)` deviation.
- **(a)** A30.
- **(b)** bounded endpoint energy (B49); deciding input (B48); attainment with the thick estimate (B110); the sign of the lag Gram matrices from prime counts (B1).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH; equivalently some feasible weight system at every aperture.
- **Established:** RH ⇔ `Ψ` locally bounded on precontact intervals; RH ⇔ feasible weights at every aperture; feasible systems converge to `Λ` [L*] (FFA21); verified-height rung [L*]; block S2.
- **(a)** A1–A3, A16, A117, A132.
- **(b)** B1, B2, B4, B18. The existence quantifier of B18 carries no freedom in the limit.

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established:** a one-sided subpower bound of the square-root Abel moment, also on a power-gap sampling set ⇔ RH.
- **(a)** none. **(b)** complete-history bounds across advancing clocks (B42).

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on a tail → RH.
- **Established:** exact tail criterion [F].
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH.
- **Established:** exact linear-floor criterion; sublinear floors impossible [KR].
- **(a)** none. **(b)** high-LCM pairs, moving core and singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma response sign → RH.
- **Established:** response sign at positive frequencies above an admissible radius ⇔ RH; calibrated Hausdorff-row sign above an explicit radius [F].
- **(a)** A1. **(b)** signs below the explicit shift, uniformly in the degree (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** Möbius Hilbert form subpolynomial ⇔ RH; cofinal admission of the damped Möbius energy ⇔ RH; centred orientation count `=M(x)` [L*]; AAL or a Mertens power saving [L*] (C7); the signal of the zeta kernel is a smoothed Möbius sum and its exponent is the zero abscissa [L*] (F1, FCT2); the cube identity [L*] (W5).
- **(a)** A21, A33, A46, A118.
- **(b)** B48, B50, B15; a bounded-index correspondence (B106); the signal bound (B161).

### SQF — Weighted squarefree count
- **Path:** a one-sided `O(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH.
- **Established:** RH ⇔ the upper law ⇔ the lower law.
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH.
- **Established:** RH ⇔ a bound `C_t` for every `0<t<½`.
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted; `N_d≤300√(d log d)` [L*]; at each fixed degree only finitely many shifts fail real-rootedness, and excluding the nonempty finite exceptions at every degree gives RH [F].
- **(a)** A20, A1.
- **(b)** outer roots (B22); bounded `N_d` gives finite support only (B23, then B13, B138); heat budgets (B124).

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** collision exclusion ⇔ RH [L*]; ordinate injectivity ⇔ RH; blocks S3, S4, S8, S13; the four-sector classification of the normalized trace [L*,S].
- **(a)** A19, A47.
- **(b)** B24, B25, B47, B27, B124; B130; B83 through non-attainment (B170), transport (B89, B112, B128) or the signed current (B145); B13, B138, B141.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established:** RH ⇔ every strict-right rectangle has an anchor with trace norm below one; explicit Gaussian central-gap inequality ⇔ RH.
- **(a)** none. **(b)** trace norm below one on every formation rectangle, or the Gaussian passage (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; one positive square ⇔ RH and the exact index for every Hecke character [L*]; three-way classification [L*].
- **(a)** A9, A13, A133, A135.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152.

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → the energy floor → `W≥0` on packets ⇔ RH.
- **Established:** the clock lies below Weil's form at every cutoff; a floor at one cutoff per large aperture gives RH [L*] (FFA24); for every fixed `N`, RH ⇔ the corrected-energy floor ⇔ the raw-energy floor with its full defect [L*] (H1); the tower is the completed-zeta quotient [L*] (H2).
- **(a)** none.
- **(b)** the floor at one fixed height on all apertures: this is `W≥0` (B1). Negative Weil directions are negative at every cutoff.

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH.
- **Established:** RH ⇔ the prime wave is bounded; RH ⇔ the odd resolvent is `≤½`.
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** signed jet hierarchy ⇔ RH; ranks `≤14` for `0<a≤½`; rank `N` from verified height `41+6(N+2)log(N+2)`; the adaptive critical Dirichlet sum is `ζ(½+ib)` up to `O(|b|^{−½})` [F].
- **(a)** A4, A5, A24, A42.
- **(b)** signed adaptive head near cancellation (B102); amplitude oscillation (B20); all ranks (B21).

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH.
- **Established:** RH ⇔ the theta-ground energy comparison.
- **(a)** none. **(b)** joint-node exclusion or the comparison (B36).

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ cofinal polynomial boundedness with one exponent; the twisted moment below the square root [L*]; block S5.
- **(a)** A18, A134.
- **(b)** B62, B57–B61, B63: the cofinal criterion needs unbounded `θ`, the proved range stops at `θ<½`.

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ the ladder sign on primitive vectors; RH ⇔ a subexponential lower bound of the clock response; `λ_n≥0` for `n≤314` [F]; every paired Li coefficient is the limit per degree point of the comb form of a Laguerre tail [L*] (HFP5, N6 [S]).
- **(a)** A1. **(b)** the lower bound or the sign (B43): neither representation gives a sign uniform in `n`.

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH.
- **Established:** completed Abel source bounded ⇔ RH; `|A_N|≤C√N e^{−c·vkScale N}` [F].
- **(a)** none. **(b)** bounded completed residual (B37, B1).

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity-energy rate, or a count → RH.
- **Established:** block S7.
- **(a)** A26.
- **(b)** B68, B71, B87; B147; B114, B117, B171. Polynomial filters erase finite exceptions; their sharp rate gives ZAL and leaves AAL.

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ every real zero of `cos(hD)Ξ` is simple for `0<h<½`; ZAL gives finite nonreal defects at every positive shift [F].
- **(a)** none. **(b)** the sign below the VK boundary (B29); a prime-faithful lossless stack (B69). Bounded and Wiener pieces sharing zeros with ξ are excluded [L*].

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower control on finite power windows of square shells → RH.
- **Established:** RH ⇔ `JasDressedPSD 1` ⇔ positivity at level one on all large primes ⇔ positivity at infinity at every level above one [L*] (J1); a signal bound `O(Z^b)` ⇔ the half-plane `b` and gives the level `b+½+ε` on large primes [L*] (FCT2, FCT3, SA4).
- **(a)** A118.
- **(b)** `JasDressedPSD 1` (B160); the signal bound (B161; `[X]` states `b=7/8` outside the native graph); the moving `k`-window control (B51). A bound at `7/8` is a strip and gives no level-one positivity.

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass → RH.
- **Established:** RH ⇔ unit-bounded rows reach every tolerance; RH ⇔ the log-integral vanishes; RH ⇔ the mollified ratio approaches one.
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH.
- **Established:** two-grid criterion at fixed offsets.
- **(a)** A1. **(b)** nonnegativity at every degree (B30).

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH.
- **Established:** coverage and source-margin criteria.
- **(a)** none. **(b)** the cover (B32).

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence ⇔ RH; fewer than `T^c` separated returns to a zero disc, `c>(30/13)(1−σ)`, in the form: power-many returns exclude the zero [L*] (C10); under a finite right layer normalized returns have only the zero limit [L*] (FFA19); the resonator mean controls ζ in mean square [L*].
- **(a)** none.
- **(b)** uniform target mass (B72); transport (B83, B89); breadth past VK (B97, B137); B145.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH.
- **Established:** RH ⇔ prime-blind positivity on the even cone; attained blind minimum `≥1/20` for `a≤(log 2+1/50)/2` [F].
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH.
- **Established:** RH ⇔ uniform decay of the positive quartic charge.
- **(a)** none. **(b)** charge below `ε` at arbitrarily late stages (B33).

### OWU — Odd sector
- **Path:** archimedean-minus-prime positivity on odd tests → RH.
- **Established:** RH ⇔ positivity on odd tests; unit-window floors [F].
- **(a)** A1–A3, A6. **(b)** B4, B17, B44.

### PBM — Regularized abscissa
- **Path:** convergence of the pole-regularized series right of `½` → RH.
- **Established:** exact convergence equivalence.
- **(a)** none. **(b)** the partial-sum bound (B53).

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH.
- **Established:** eventual criteria at colossally abundant numbers and at `lcm(1,…,n)`.
- **(a)** none. **(b)** the inequality (B54).

### SRT — Lag localization
- **Path:** the prime two-bump sign on a decisive sample → RH.
- **Established:** block S3 [L*]; a verified height covers every prime below its rung [L*] (J4).
- **(a)** A9.
- **(b)** B130; B6, B101.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH.
- **Established:** RH ⇔ the variation inequality at any single shift; outward kicks of `{2,3,4}` cost `<991/1000` of the Lévy energy below `2c<log 5` [F].
- **(a)** A7. **(b)** one shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** global incidence allocation → RH.
- **Established:** RH ⇔ the global incidence allocation; VK signed cost [F].
- **(a)** A9, A13. **(b)** signed cost `C_σe^{2σr}` (B45); polar payment (B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling, or glued index `≤1` → RH.
- **Established:** bounded Gaussian cone coupling ⇔ RH; glued index `=κ_ζ+1`; undamped coupling on a two-prime cone gives AAL [F].
- **(a)** none. **(b)** the damped bound; sublinear tensor loss (B39); ZAL for the undamped branch.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** the comb floor → step and smooth packet positivity → RH; or the prime-window floor.
- **Established:** block S10. The analytic transfer between combs, step packets and smooth packets is closed in both directions [L*].
- **(a)** A28, A41, A48, A59, A133, A135.
- **(b)** B152, B149, B169, B88, B87; B130; B28; or force the packet index to be `0` or `∞` (B13).

### ECP — Endpoint character positivity
- **Path:** endpoint jets → coherent symmetric-group class functions → PSD character Grams at every rank ⇔ RH.
- **Established:** column projections nonnegative; Toeplitz minors through order 200; four mixed shapes [F].
- **(a)** none. **(b)** positivity at arbitrary rank (B86).

## 4. Candidates

Each needs its source-to-receiver step first (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF. Established facts are [F] unless marked.

| Candidate | Established | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| S3 | a strip of depth `h` excludes heavy identity returns up to `exp(ηT)`; the transfer gives `Θ<1 ⇒ RH`; RH gives the transfer; under `Θ<1` the transfer ⇔ RH [L*] | none | an arithmetic proof of the transfer that uses its premise (B148, RH under a strip); natively also `Θ<1` |
| SEC | Fock boundedness at every divisor point ⇔ `Re s=½` | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` | none | arithmetic descent on actual zero fibres |
| APF | prime/grade trace reconstruction on real labels | none | full-divisor exhaustion and RH landing |
| EGC | zero-pair contour; count error `≤32ε²log T/T` | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on the blind plane | none | faithful endpoint admission |
| FEL | KL accounting | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion | none | RH-sufficient orientation law |
| W1C | Laguerre–Pólya approximants on one interval give RH; index-one limits give RH [L*]; an index-one realization of the right zeros gives RH [L*] (FFA20) | none | an independent index-one family or realization (B146, B171) |
| WBF | Gram recovers magnitudes and phase class | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| FFA (floor-free arithmetic) | floors of mechanisms; non-attainment receivers; tangent datum, quantum, four sectors; every finite datum realized under one structure; unit gaps and their kills; certificates converge to `Λ`; projection statistics [L*] (FFA1–FFA30, N1–N4) | — | B170–B173 |
| SOSZ ScaleLocality | logarithmic, `log²` and `√T` windows; exceptions; upper side; counts; local moments; half-period law; finite top layers; counter-configurations [L*] | A78, A89 | B130, B144 |
| SA (selective arithmetic) | trivial aperture in both aspects; feasible sets; fakes; the cancellation and depth ladder; exceptional heights with power saving; first conductor rung; three rungs under a half-plane; deep zeros at ζ density with positivity at a fixed aperture [L*] | A117 | B159, B156 |
| FCT (family continuation) | frame for every ray class character with corrections; the two-estimate implication for ζ; signal as Möbius and log-normal sums; signal exponent = abscissa = level; one Jacobi sum; budget with vertex, floor, orders, designs, conductors, circularity, and its floors in the twist exponent [L*]; the law of a twist family as a level of the scale [P] | A118 | B161, B174, B175 |
| MMD | cubic Gauss arithmetic, the cube identity, the cubic residue with Gauss coefficients and Fourier/Bessel formulas [L*]/[F] | A33, A118 | B94 |
| CTZ (constituents) | none with a zero in the bounded and the Wiener class; nonsummable residues; no `ℓ^p` transport; jump law; boxes; sizes on a circle [L*] | — | — (the classes with a first step are closed) |
| HFP (Hodge theory of a fixed part) | exact eventual comb positivity; mass floors; robust index; unshifted index; Li tails [L*] | A135 | B152, B149 |
| AGZ | forced data; price paths; step packets; exact index for every Hecke character and Dedekind zeta function; class characters; discriminant below first contact; sections in boxes; tails and rows [L*] | A133 | B149, B169, B88, B87 |
| ELT | atoms; filters; growing-order reduction; near-diagonal row [F] | A47 | B141, B145, B138, B13 |
| ZCG AbscissaLaws, Recurrence | split, atoms, tail law [L*]; graded recurrence [L*]; boundary trace without isolation [F] | — | B13, B83, B138 |
| IRW / EFT / APD | the paired ξ model [L*]; continuous prime measures [L*]; Beurling rigidity [L*]; the critical-line firewall and one-offs [N]; relocation invisible to growing quadratic tests [KR] | — | B112 |
| IRP | index law; flow criterion; index-one limits [L*]/[N] | — | B146 |
| AWT | fixed-part laws; cover-family tensor criterion [N] | — | B86 |
| SignFreePurityMechanisms | height separation ⇔ bounded prime traces [F]; greedy optimality [L*]; the return transfer [L*] | A115 | B148 |
| HAT | clock; tower as a completed-zeta quotient; fixed-height floors ⇔ RH; unbounded critical inverse [L*] | A54 | B88, B117 |
| AHMH / BHR / ASH / CTH | cavity receivers, reflection Krein forms, halving descent, ringdown, count door [N]/[F]; horocycle exponents with Euler filters [L*,S] | A26, A41 | B68, B71, B87, B147 |
| TTPO / CDGeo / PTT / TAPO | depth law, VK breadth, strip breadth, collective counts; resonator means [F]/[L*] | A24 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates [L*]; cut kernel; parity blindness [L*] | A30 | B48, B55, B67 |
| AHD / CACT | threshold identities, pole channel, ground states, classification [L*]; positivity to the eighth root [L*] | A9, A13 | B104, B123 |
| MZF / CDG | twisted moments below the square root with derivatives; detector identity; mollifier trap [L*]/[F] | A18, A134 | B62, B57 |
| Census (IGP, TTPC) | `0.67250071` [L*]; positivity cost `≥1+3/π²` [KR] | — | B150, B57 |
| VHR / TCS | verified-height rungs; height 67; window, prime two-bump, rank and degree entries [L*]/[F] | A1–A5, A132 | — |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: `P(p)≤A(p)+K` on the primes of logarithmic windows off power-thin exceptions | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count), every window route through the prime two-bumps |
| Σ: the sign on every window, equivalently every rung, verification at every height, one positive square, the sign on step packets, feasible weights at every aperture | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: continuation at small time and the theta head at the critical zeros | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision and long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| One scale: level one of the dressed aggregate (RH); a level above one = a half-plane = the exponent of the signal (`[X]` outside the native graph) | JAS; MC (signal); S3 |
| Γ: reflection and count | PM, ECP |
| The exceptional coordinate: world I (B13, Landing, DH; non-attainment) and world II (ZAL) | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length, Dirichlet polynomials longer than the height | every route at all heights; BAG; TH certificates; WD; the centred type-II current of ELT; the rungs above one in the height aspect |
| Missing source landing | the twelve candidates |
