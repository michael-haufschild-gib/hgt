# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `1cec78e529` with its working tree (2026-11-10). Working log: `logs/review-1011-status-quo-facts.md`. Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question, the programme for the case that every route is a receiver), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. Formulations are not independent mechanisms: HJ is PA; the BSY criterion of FEL belongs to CTF; PCS is a retired label. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.**
- `[L*]` Lean statement read for this report (source at the declaration, or the statement returned by the corpus search tool); listed in the working log §5.
- `[L]`, `[K]`, `[S]` as graded by the frontier map and the scoped-obstruction ledger at the checkpoint: integrated Lean; Lean with transitive axiom audit; source present, unfinished or unintegrated. Statement not re-read here.
- `[D]` deduction made in this report from `[L*]` statements (working log §7); not a Lean theorem. `[C]` classical mathematics quoted from memory, not in the corpus. `[A]` assessment.
- `[X]` one external source cached in the repository, outside the native import graph and not checked here: a zero-free half-plane `Re s>7/8` for ζ, Dirichlet `L`-functions and Hecke `L`-functions over `ℚ(√−3)` (described in [fable.md](fable.md)). No statement of the native graph depends on it. Every row that uses it carries the tag and states the native form beside it.

**Strength.** RH; ≥qRH (a zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); ≥B56 (implies `Θ<1 ⇒ Θ=½`); sub (below quasi-RH and below AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md). `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1 ⇒ Θ=½`. `B` the cubic spline, `c_B(u)` the real part of its lag structure, `c_p=c_B(log p)`; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I**: ¬AAL, a finite isolated top layer at `β<1`; **I-a** with the remainder on the line, **I-b** with an off-line tail. **World II**: AAL ∧ ¬ZAL. The **edge world**: `Θ=Θ∞=1`. The **depth** of a zero is `|Re ρ−½|`. **Comb pairing** of a real divisor `D=Σc_nγ_n`: `Γ_m·Γ_n=½(1/|m−n|+1/(m+n))+Λ(n/m)` off the diagonal (jets plus contacts), `Γ_n·Γ_n=−log(n/2π)`, `d₁=Σc_n/n`, `d₂=Σc_n`; **comb form** `2d₁d₂−D·D`. A **window of ratio `Q`** is `(N,QN]`, its **aperture** `½log Q`. A **system** is a weight system `w` (its contacts) with a **mass** `m`: the log conductor `log q` of a comb of density `q`, or the log height `log|t|` of a packet modulated to the height `t`. `w` is **dominated** if `|w|≤Λ`. The **rung** of an aperture `a` is `κ=a/log m`. The **trivial aperture** is the supremum of the apertures at which every dominated system is feasible. The **Liouville twist** is `w(p^k)=(−1)^k log p`. `JasDressedPSD σ`: positive semidefiniteness of the `σ`-dressed lag aggregate on finite families of rational characters. The **signal** of the zeta kernel is `f(Z)=(1/2π)∫G(2+it)Z^{2+it}dt`, `G(s)=exp((s−c)²)/((s−1)ζ(s))`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `∃K`: `2c_p≥−K` at the primes of arbitrarily late logarithmic windows outside at most `Ce^{δT}` primes per window (`δ<1`) | [L*] | Σ (Weil's sign), Π (a prime count) and the count door are one inequality per prime, local in scale, tolerant of power-thin exceptions |
| The same criterion holds with the upper bound alone on undeleted windows, with `ℕ`-counts on the surviving rays `Γ_1+Γ_p`, with even moments of the traces under one exponent for all orders, and with the absolute value | [L*]/[K] | the minimal face has a one-sided, a two-sided, a counting and a moment form |
| A density-matched tempered configuration with logarithmic local counts, `\|Im ρ\|≥4`, `N(T)−N_ζ(T)=o(T log T)` and unattained top `½+Θ` passes every floor on windows of a radius `R→∞`, `R=o(log T)` | [L*] | below the logarithmic radius no receiver at the level of configurations decides RH |
| ζ with an attained positive top of at most `k` positive ordinates fails every fixed floor on every sufficiently late continuous window of length `(k+1)π/67`; `n` modes of frequency `≥Γ` keep one sign on a length `≤nπ/Γ` | [L*] | world I is seen on windows of bounded length; floors on such windows, with constants depending on `k`, give AAL |
| `Θ<1 ⇔ Θ∞<1`; RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH | [L*] | a failure of RH is world I or world II; three atoms on the RH path |
| An entire function with the Riemann functional equation, the Riemann Gamma factor, residue one at `1`, order `≤1` and the zero count of ξ within one has all its zeros simple, off the line, approaching it; positive integer-norm Euler products with linear counting realize `(Θ,Θ₂,Θ∞)=(β,θ₂,θ)` for `½<θ≤θ₂<β<2/3` | [L*] | Landing and DH follow from neither structure alone; a Dirichlet series with ζ's functional equation is a multiple of ζ [L] |
| For every `η>0` and large `q`: every dominated system has the floor `½(1−e^{−η/2})log q∫f²` at apertures `a≤log log q−η`; at `a≥log log q+η` the Liouville twist and `−Λ` are negative on the odd polar packet and `Λ` without pole plane on the even one; the trivial aperture is `log log q+o(1)` | [L*] | sizes prove the sign up to rung `1−o(1)` in the conductor aspect and nothing beyond: no gap |
| At height `t`: every dominated system with pole plane has the floor `½(1−e^{−η/2})log\|t\|∫f²−5∫f′²` at `a≤log log\|t\|−η`; at `a=log log t+log 2+η` some dominated system built with the height fails | [L*] | the same in the height aspect, on packets of bounded shape, up to an additive `log 2` |
| Partial sums of the contacts `≤Cn^{½+γ}` give the sign up to `a≤κ log log q`, `2γκ<1`, with floor `½log q(∫f²−∫f′²)`; cancellation of the twisted contacts at every frequency inside the archimedean budget gives all packets; the sign on the two polar packets bounds the Riesz mean of the contacts at `e^{2a}` by `log q(e^a+2a)+C(1+a)³e^a` | [L*] | prime side of the exchange rate, both directions: saving `γ` ⇔ rung `1/(2γ)` |
| A lattice of density `x/2` with one pair of depth `δ` is nonnegative at `a≤κ log x` if `2δκ<1` and has a negative direction at `κ log x≤a≤x/4` if `2δκ>1`; for ζ and for primitive Dirichlet characters, the sign on the tests of aperture `κ log m` forces a second off-line zero within `m^κ` of every zero of depth `δ>1/(2κ)` | [L*] | zero side of the exchange rate: depth `δ` shows at rung `1/(2δ)`; a rung excludes isolated zeros, not clusters |
| RH ⇔ `JasDressedPSD 1` ∧ a half-plane bound `Re ρ≤½+α`, `α<½`; positivity on the characters of large primes at a level `σ≥1` gives `\|Re ρ−½\|≤σ−1` for every zero or `sup\|Re ρ−½\|=½`, and at level one `Θ=½` with no exception; a bound `O(Z^b)`, `b<1`, of the signal gives `Re ρ≤b`; the signal is `Σ_nμ(n)W_c(Z/n)` | [L*] | level one on large primes is RH; a higher level and the exponent of the signal are half-planes |
| A family with kernels `G_η=E_η/L_η`: if zero-freeness in `Re s>β` gives each member a sum `J` with `\|J\|≤KZ^{a₁}` and `\|J−signal\|≤KZ^{a₂}`, `a₁,a₂<β` common to the family, no member has a zero right of `σ₀` | [L*] | the continuation step is a theorem with both estimates as hypotheses |
| `[X]`: `Θ≤7/8`. Natively: over `ℤ[ω]` the cube of the normalized composite cubic Gauss sum is the ideal Möbius value times a phase; on a finite field `g(χ)^n≡−card F mod (μ−1)²` for every odd order `n>2` and `≡χ(−1)card F` for even order; the exponent budget of the detector has the boundary `7/8` at every redistribution of its two scales and `29/36` with the unit term alone | [X]; [L*] | one producer, external; its arithmetic source and its budget are in the native graph; between `7/8` and `½` no producer |
| `CombBezout w ⇔ RH ∧ w=Λ`; with the counterterm `log(n/2π)−c`: `⇔ c≤0 ∧ RH`; with contacts `(1+ε)Λ+δ`, `Σ\|δ(n)\|/√n<∞`: `⇔ ε=0 ∧ RH ∧ c≥sup P_δ`; with the tree of `p` glued at edge length `ℓ`: `⇔ RH ∧ ℓ=log p` | [L*]/[L] | weights, constant, scale and tree lengths are forced; the sign has no margin |
| RH ⇔ at every aperture some real weight system is Weil-positive; if RH fails, one aperture admits none | [L*] | the existence half of the sign needs no compatibility between apertures |
| RH ⇔ the intersection form on the two rulings and every finite family of packets has exactly one positive square; for ζ and finitely many primitive Dirichlet `L`-functions the defect has `n` negative squares on some family iff they have together at least `n` distinct zeros right of the line; the counterterm of an abelian ring obeys `2g_K(n)−2=d(2g(n)−2)+nR` with `g(n)=1+(n/2)log(n/2π)` | [L*] | the Hodge index is the exact count of the right zeros; a cover bounds its base; conductors are ramification |
| If for all `K,R,η` there are arbitrarily large block sizes `B` with comb form `≥−ηΣσ²` on the divisors constant on the `3KR` blocks of `(RB,(3K+1)RB]`, RH holds; replacing a divisor by its block means costs `εΣc_n²` | [L*] | the inequality at finite scale lives on a space whose dimension does not depend on the scale |
| On the planar square the values on `Γ_m` of the sections vanishing on a finite set `S` are exactly the ideal `Π_{n∈S}J(m,n)`; the count of a section on two graphs is `\|x_mx_n\|`; the system of the squares fails Bézout on its own comb; in a tower `Z_ζ` has weight `1/d` | [L*] | every structure of the square found so far returns an identity or loses ζ |
| A nonzero Dirichlet series absolutely convergent at `x`, or an expansion over positive real scales absolutely convergent on a closed strip about the line, whose zeros there are zeros of ξ, has no zero there; one zero forces infinitely many that are not zeros of ξ; a bounded Dirichlet series on `Re s>x` with support exponent `δ`, `x+δ<½`, likewise | [L*] | ξ has no constituent with a zero in the Wiener class; the open case is the bounded class with `0≤x<½` |
| `ξ=E+E^♯` on a disc with `E=Π_{w∈W}(z−w)E₁`, `E₁` zero-free, `‖E^♯‖≤‖E‖` on the circle: ξ has at most `card W` zeros in the disc | [L*] | the defect of a splitting is certified by sizes on one circle |
| Twisted second moments of `ζ·`(a real polynomial of length `T^θ`), `θ<½`, with both gcd main terms; the dyadic mean of `\|Rζ\|²` at `σ∈(½,1)` equals the convolution diagonal for every resonator of length `T^κ`, `κ<2σ−1`; RH ⇔ `∫_1^T\|M_{T^θ}(½+it)\|²dt≤C_θT^{K₀}` for cofinal `θ` with one `K₀` | [L*] | the mean-value ladder is proved below the square root; its conversion to every zero needs length past the height |
| Simple critical zeros `≥(0.67250071−ε)N(T)`; for every `θ` either `N₀≥θN` or the simple off-line zeros number `≥(1+HD(1)−2θ−ε)N` | [L*] | the census is in law; `70%` is open |
| `R_polar=R_halfline≤W`; RH, or ¬RH with `R_polar<W`, or ¬RH with `R_polar=W` finite and every critical half-line ground state orthogonal to the polar source | [L*] | the critical curve has one undecided case (B104) |
| RH is verified through height 67; verification through `windowHeight(a)` gives the sign on `[−a,a]`; through `T` it gives the two-bump sign at every prime `p≤primePacketRung(T)` | [L*] | each window, and each prime of the minimal face, is a finite-height statement |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a` follows from verification to `windowHeight(a)` |
| M2 Calibration | window cones, feasible sets, margins | feasible sets nonempty at every aperture ⇔ RH; all-aperture cone pinned to Λ; first selective window bounded |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | complete and sharp receivers; rates and signs open |
| M5 Square-root cancellation | smoothed prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH; purity thresholds are the width |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros at rate 2; [fixed-deficit sector clusters are visible or have a deep exterior companion](../../drafts/pipeline/3-formalized/box-convolutions-pay-a-fixed-cluster-depth-deficit.md), with uniform prime and remainder costs; [original `ClusterAt` forces deep isolation](../../drafts/pipeline/3-formalized/cluster-mass-control-forces-deep-isolation.md); [fixed-centre exterior mass has an exact boundary-depth limit](../../drafts/pipeline/3-formalized/the-camera-retains-exactly-its-boundary-exterior-mass.md); uniform general-cluster control and depth density `o(T)` open |
| M8 Finite-layer receiver | damping filters, centred Vaughan currents, half-period deletion | complete in world I; a top of `k` quartets is seen on windows of length `(k+1)π/67` |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level; exact count = Chebyshev; cost `m·θ(S)` |
| M10 Count | nonnegative count with quadratic Tate limit | every hyperelliptic curve; over ℤ: RH ⇔ counts on the surviving prime rays; the object's own count is the split norm |
| M11 Orbit at finite time | prime phases, returns, resonators | depth by Baker; breadth to VK; resonator means to `κ<2σ−1` |
| M12 Critical compactness | thresholds, pole channel, half-line ground states | threshold identities; three-way classification; actual full-domain zero energy and weak equation; no positive real Laplace zero and uniqueness up to sign, without polar-threshold equality [L] |
| M13 Topology of the prime complex | nerve, persistence, orientation cover | centred count `M(N)`; weight `½` ⇔ RH |
| M14 Infinite-rank elimination | towers, thick sets, Turán, resolvent of a tower | elimination proved; with an attained top a thick crude count is RH |
| M15 Prime-degree sampling | logarithmic windows, exceptions, upper side, counts, moments | complete receiver; resolution logarithmic at the level of configurations |
| M16 Intersection on half-products | zonotope, `ℍ³` and tree fibres, adelic carrier | off-diagonal Green formula; invariant glued diagonal refuted; critical adelic inverse unbounded |
| M17 Absolute geometry | Λ-square, contacts, carries, tower of lines, paying ring, planar square | the square is a curve; unit masses with paid contacts exist; restriction is an equality of ideals |
| M18 FE rigidity | Hamburger, defect isolation, gauge deformations | identifies ζ among countable systems; positive continuous prime measures are not rigid and keep every zero |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing; all open for ζ; no model with both structures among Dirichlet series over the integers |
| M20 Families and monodromy | gauge torus, vertical family, covers, towers | fixed-part laws; in a tower ζ has weight `1/d`; no producer by averaging |
| M21 Index and limits | index law, Hermite–Biehler defect, sizes on a circle | RH ⇔ limit of index-one objects; exact index = number of right zeros |
| M22 Separation | ordinate injectivity, Newton polygons, digit calculus | receiver; greedy carry-free compositions are the optimal ones in the Carlitz–Goss calculus |
| M23 Hodge lattice at finite scale | comb pairing, block Schur test, block averages | short windows coercive and blind to the contacts; finite index; decided on block-constant divisors |
| M24 Arithmetic constituents | recurrence against density, the jump law, the carry | none in the Wiener class; bounded class open |
| M25 The ladder | mass, aperture, rung; dominated box; fakes | sizes to rung `1−o(1)`; both one-structure fakes fail at `1+o(1)`; one exchange rate on the prime and the zero side |
| M26 Family continuation | signal of a reciprocal kernel; two estimates for one sum; reciprocity identity | principle and receiver in Lean; `[X]` at `7/8`; local sign law at every odd order |
| M27 Dressed positivity | lag aggregate at a level `σ` | level one on large primes ⇒ `Θ=½`; a level `σ>1` gives `Θ≤σ−½` or the edge world; level 2 holds, `3/2` on large primes |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators | amplify or reshape a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH [L]; `R_polar=R_halfline` and the three-way classification [L*].
- A critical half-line ground state with nonzero polar pairing forces `R_polar<W` [L*].
- Every actual critical half-line state has full Gamma/logarithmic energy, causal coordinates, zero full energy and a weak equation against every finite-energy half-line test, without polar-threshold equality [L]. [Proof](../../drafts/pipeline/3-formalized/critical-half-line-states-have-causal-logarithmic-coordinates.md). The polar pairing remains undecided (B104).
- Every actual critical state has nonzero Laplace value at every positive real argument, without positivity or polar-threshold equality [L]. A positive Laplace zero would permit an admissible reflection preserving Gamma, prime and pole energy while strictly reducing exponential mass. [Proof](../../drafts/pipeline/3-formalized/critical-half-line-states-have-no-positive-laplace-zero.md).
- Actual normalized critical states are unique up to sign almost everywhere. At every `s>0`, `F=(L_F(s)/L_G(s))G`; the weak equation and Laplace-zero exclusion force this relation [L]. [Proof](../../drafts/pipeline/3-formalized/critical-half-line-ground-states-are-unique-up-to-sign.md).
- Complete tilted-spline matrix positive for every subcritical exponent `<1/8` [L], and at `c≤2K₀(log N)^{1/8}` [K]; no countable square-bounded family of holomorphic multipliers dominates the depleted kernel [L].

| | Obstacle | Strength |
|---|---|---|
| A9 | explicit constants of the eighth-root horizon and the Beurling schedule | — |
| A13 | near-gcd charges and periods beyond the admissible scale (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | whether the unique critical-state line at finite `W` can be polar-orthogonal | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow and the aperture–height exchange
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL, SA.

Established:
- RH ⇔ `W≥0` on every window; RH ⇔ `Ψ` bounded on every bounded precontact interval [L].
- `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]`; RH through height 67 [L*].
- RH ⇔ every positive aperture admits a real weight system with nonnegative Weil form; ¬RH ⇔ some aperture admits none [L*]. Bézout at an aperture ⇔ membership in the window cone; at `a=181/500` every `w(2)` within `√2/10000` of `log 2` occurs [L*].
- First contact [L*]: for `2a<log 2` feasibility does not depend on the weights; a system feasible with ζ's pole plane at `a≥½log n+r`, `0<r≤1/(4n)`, has `|w(n)|≤√n(log(1+1/r)+C)`; for `a≤181/500` every system with `√2|w(2)−log 2|≤1/5000` is feasible.
- Positivity at aperture `a` (the level-`a` Hodge index) forces `δa<12((4n_δ+2)log(10⁶/δ)+log(A₀log(|γ|+3))+18)` for a zero of depth `δ` at `|γ|≥103`, `n_δ` the number of zeros of depth `≥δ/8` within `±100` [L*]; a tempered configuration with ζ's local counts hides a zero of depth `δ` at `T≥e³⁶⁰` to aperture `(log T)/36` [L].
- Best margin of a window `≤K exp(11c/2−πe^{2(c−2)})` [L]; floors `(1/20000)/2^k` through `a_k`; margin `∫f²/5000` at `a=181/500` [L].
- The ladder (block S12).

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A79, A81, A93 | constants in the aperture–height exchange; the order of `windowHeight(a)` against the visibility laws (unverified) | — |
| A117 | end points of the feasible interval of `w(2)` on the first selective window (a finite computation) | — |
| B1, B2, B4, B5 | sign on every window; bounded oscillation of `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |
| B18 | a construction of feasible weights at every aperture | RH |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo.

Established:
- RH ⇔ the floor on the primes of arbitrarily late logarithmic windows off `Ce^{δT}` primes [L*]; width `≤σ` ⇔ the floor `−Kp^σ` there [L]; absolute form, also on `log²` windows with omissions [K]/[L*].
- RH ⇔ the upper bound `2c_p≤K` at every prime of arbitrarily late logarithmic windows [L*].
- RH ⇔ `ℕ`-counts `K_p(m)` with `K_p(m)/m²→planeDefect p (1,1)` on the surviving rays of such windows [L*].
- RH ⇔ `∃A ∀k≥1`: the `2k`-th local moment of the prime traces on arbitrarily late windows is `≤C_ke^{AT}` [L*].
- RH ⇔ a floor on the scale limits of the comb form on two-bump packets at `log p`, same windows and exceptions [L].
- `r√T` windows decide every tempered configuration without real zeros; two fixed primes suffice on such windows [L].
- Half-period law: `n` modes with frequencies `≥Γ` and nonnegative real part on a length `L` have `ΓL≤nπ` or vanish identically [L*]. A finite top layer of ζ with at most `k` positive ordinates breaks every floor on every late window of length `(k+1)π/67` [L*]. A floor on integer runs `[x,e^Lx]` for every `L` gives AAL [L*]. Floors on arbitrarily late windows of length `(k+1)π/67`, with a constant depending on `k`, also at the prime logarithms, give AAL; a floor of any exponent below the top depth fails on such windows [L*].
- The sub-logarithmic counter-configuration has `N(T)=o(T log T)` [L*]; the density-matched model keeps the unattained top and the floors [L*]. The projection of ζ's divisor to the line keeps every ordinate count and is tempered [L*].
- A global floor `−K` bounds the weighted absolute mass by `2K∫w` plus Fourier leakage; the coefficient two is sharp [K].
- A verified height `T` gives both signs of the two-bump at every prime `p≤primePacketRung(T)`, a rung tending to infinity [L*].

| | Obstacle | Strength |
|---|---|---|
| A78, A89 | cluster form of the separated-window theorem; a prescribed radius in the sub-logarithmic model (unverified) | — |
| A58, A59 | effective gap iteration; residue-class primes [C] | — |
| B130 | the bound itself on any decisive sample | RH (≥qRH at `p^σ`, `σ<½`) |
| B144 | separation of the deep off-line ordinates of ζ | sub |

### S4. Continuation, nodal geometry, index and constituents
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidates: W1C. Programmes: NGF, FFP, ADO, AES, IRP, CTZ.

Established:
- RH ⇔ every zero of every `H_t`, `t>0`, is simple [L]; RH ⇐ infinitely many Jensen degrees real-rooted; `N_d≤300√(d log d)` [L]; the finite-stratum law on shifted Jensen polynomials gives RH, on the cosine family RH ⇔ ZAL [L].
- Index law: a Hermite–Biehler splitting covering the right zeros bounds the negative index by its defect; RH ⇔ ξ is a locally uniform limit of conjugation-real entire functions with at most one right-half zero [L]. Sizes on one circle bound the zeros of ξ in the disc by the zeros of the dominant half [L*].
- Flow: Castelnuovo–Severi on every divisor of Frobenius graphs ⇔ pure and effective; RH ⇔ the prime lag function is positive definite on `ℝ` [L*].
- Constituents [L*]: no absolutely convergent Dirichlet series and no absolutely convergent expansion on a strip about the line has a zero there with its zeros among those of ξ; one zero forces infinitely many unmatched zeros; exponential polynomials with real frequencies are covered; for every length `N` a height `H₀` beyond which a Dirichlet polynomial of length `≤N` with a zero near the line has an unmatched zero below `H₀`; approximants sharing zeros in growing boxes and converging in the absolute norm lose their zeros; every box has a Dirichlet polynomial with exactly the zeros of ξ, of unbounded length.
- The jump law on every strip: two absolutely convergent expansions of `−sΦ/ζ` on the two sides of the line over the same scales are equal, also with finitely many simple poles on the line [L*] and with countably many of summable residues [L*] (graded [S]); it is the law of the carry [L*].
- A bounded constituent with a zero lives on `Re s>x`, `0≤x<½`, converges absolutely nowhere left of the line, has support exponent `≥1−2x` and infinitely many primes in its support [L*].
- An exponential polynomial of `N` terms that vanishes at `N` consecutive points of a vertical progression vanishes on the whole progression [L].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B153 (bounded class) | a bounded Dirichlet series on `Re s>x`, `0≤x<½`, with a zero and all its zeros among those of ξ | method |
| B24, B25 | collisions at small time, all heights; frequency below one | RH |
| B22, B23 | outer roots of the Jensen polynomials; `N_d` bounded | RH; ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ; a splitting of ξ with `‖E^♯‖≤‖E‖` on circles and a defect counted without the zeros | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |

### S5. Near-line geometry, long moments and the census
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation.

Established:
- RH ⇔ cofinal polynomial boundedness of the long Möbius second moment with one exponent [L*]; dyadic boundedness with prefix-cancellation mollifiers of length between `T^{θ₁}` and `T^θ` leaves finitely many zeros beyond depth `1/(2θ₁)+ε` [L]; near-unit moments need length `exp(c log²T)` [L].
- For `0≤θ<½`: the displaced second moment of `ζ` times a real polynomial of length `T^θ` is bounded by its two gcd main terms plus an arbitrary power saving [L*].
- Census: simple critical zeros `≥0.67250071`; alternatives at every proposed proportion [L*]; five consecutive simple critical ordinates at `≥N(T)/5000` starts [L]; a form factor `≤4` on `(1,10/9)` or a trans-threshold integral `≤7/45` at bandwidth `4/3` certifies `70%`; positivity alone does not reach `75%` [L].
- BSY: RH ⇔ the log-integral vanishes; RH ⇔ unit-bounded chronological rows reach every tolerance [L].

| | Obstacle | Strength |
|---|---|---|
| A18, A21 | twisted moments past the square root [C]; census items | — |
| A111 | a proportion of critical zeros by Levinson's gate with the twisted moment below the square root (unverified) | — |
| A112 | the positivity ceiling of the certificate at the threshold `7/45` (a linear programme) | — |
| B57 | depth density `o(T)` | sub |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)` | sub |

### S6. Production, precision and the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established:
- `c/(√K(1+log K))≤bestRate K≤exp(−(log K)^α)`, `α<3/5`; rates `K^{−a}` for all `a<½` give RH [L]; RH ⇔ `log N(A_N)≤N+C√N log²N` for the fixed-point auxiliary [L]; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [L]; RH ⇔ Robin's inequality at `lcm(1,…,n)` for large `n` [L].
- Orientation cover over ℤ: centred count `M(N)=Ω±(√N)`; weight `½` ⇔ RH; in world I `M(x)=O(x^β)`, `β<1` [L].
- Every bilinear statement is invariant under the Liouville twist [L*]; Type I and Type II norms are parity-blind [L].
- Stepanov at one prime: `|Σ_{n≤p}e(an^p/p²)|≤5p^{11/12}` [L].
- Cubic branch: the residue of the cubic Eisenstein family at `4/3` is nonzero, with cubic automorphy and continuation of its Fourier coefficients [L]; the cube of the composite cubic Gauss sum is Möbius times a phase [L*].

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients [C]; singular indices past the cubic cutoff | — |
| B48, B49, B50, B53, B54 | deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | past Vinogradov–Korobov | sub |
| B56 | `Θ<1 ⇒ Θ=½` | ≥B56 |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers and the modular horizon
Routes: PM, HAT-C. Candidate: W1C. Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT.

Established:
- RH ⇔ every compact pulse rings down at the quarter rate ⇔ full reflection positivity of the reflection-paired cavity forms ⇔ the horocycle error `O(y^{¾−ε})` of one cuspidal function built from Hecke forms [L]; for one Hecke eigenform RH ⇔ sharp rate ∧ no nonhalving Shimura zero [L].
- RH ⇔ an `ℕ`-valued count with Tate limit the integer probes; on a hyperelliptic curve the defect of an integral class is a natural number [L].
- Regulators: `E_r↑W` with error `(1−r²)‖f′‖²/2`; the scattering tower of height `N` is the logarithmic derivative of `Λ(s)/Λ(s+N)` plus Robin and polar terms [L*]; for every fixed `N`, RH ⇔ the raw energy at height `N+1` is at least minus its full arithmetic defect on every aperture and form-domain state [L*]; corrected energy plus a nonnegative jump tail is the closed Weil form [L*].
- The critical adelic Green inverse is unbounded; the critical spherical integral is entrywise finite and not Bochner integrable [L*].
- No Maass cusp eigenvalue `0<λ<3/16` for groups containing `Γ(N)` [L] (statement returned by the search tool, not re-read).

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents | — |
| B68 | independent reflection Krein positivity, Krein flux, dispersion bound | RH |
| B71 | universal decay `e^{−t/4}`; horocycle, Farey, Narain or cavity rate `y^{¾−ε}` | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one eigenform | indep. |
| B114, B117 | a realization of the partner involution outside the excluded classes; a regulated horizon that is unitary at every cutoff and has ξ as its limit | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling branch), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, IRP, APD, AAD, TAPO.

Established:
- `Θ<1 ⇔ Θ∞<1` [L*]; ¬AAL ⇒ `Θ<1`; failure of quasi-RH forces `Θ=Θ∞=1` and AAL [L].
- `AbscissaLaw ⇔ B13 ∧ Landing ∧ DH`; pure ⇔ ZAL ∧ B13 ∧ Landing; the atoms are pairwise exclusive in failure; Landing is a tail law that no finite height decides [L*].
- Landing calibration: the Riemann Gamma factor, residue one, the functional equation, reality, order `≤1` and the zero count within one do not force landing [L*]. DH calibration: integer-norm two-scale Euler products realize every `(β,θ₂,θ)` with `½<θ≤θ₂<β<2/3`, and every graded repulsion bound is refuted there [L*]. Classical Deuring–Heilbronn on the twisted comb: for a real zero `β` of a real primitive `L(s,χ)` with `C(1−β)log(q(R+3))<(q(R+3))^{−C/2}`, every other zero below height `R` is on the line, the odd packets isolate the exceptional square, and the sign at an aperture gives an unconditional lower bound for `1−β` [L*].
- World I: prime filters recover the top residues; the prime error is a finite oscillation at the top plus a smaller remainder [L]; the centred Vaughan reduction at growing moment order and the rapid decay of separated unweighted cofactor pairs [K]; every late window of length `(k+1)π/67` contains a point below every floor [L*].
- Level-one dressed positivity on large primes gives AAL, B56 and `Θ=½` [L*]; B13 ⇔ the supremal negative index of the comb defect on real packets is `0` or infinite, and that index is the number of right zeros [L*]; level-one constant-vector positivity on infinitely many dyadic prime shells gives AAL [L].
- Continuous prime measures: for every `δ>0` a positive continuous perturbation of the Riemann prime measure has zeta function `ζ(s)exp(ε/(s+1)²)`, the zeros of ζ, and a functional-equation defect `≤δ/(1+t²)` in `L¹∩L²` [L*].

| | Obstacle | Strength |
|---|---|---|
| A47, A86 | constants of the one-quartet world; the near-diagonal cofactor pairs and the transfer through the growing-order filter (unverified) | — |
| A109 | the trichotomy of the normalized prime error [D] | — |
| A120 | a finite nonempty stratum in an Euler product with a functional equation over a discrete system of real norms [C] | — |
| B13, B138 | finite stratum; landing for ζ | sub |
| B141 | Deuring–Heilbronn for ζ: `¬AAL ⇒ ZAL` | sub |
| B83, B89, B112, B128 | AAL; a bounded aligned return at each right zero; FE into vertical transport; replication | sub |
| B145 | the signed centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; a bound on a sampling set; positive-measure lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum, and which gap mechanism has a counterpart for ζ | method |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT, every route at all heights. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, SPAL, ALST.

Established:
- Near-total `p^{−1/2}`-mass returns of the primes `≤y` need `log t>(log y)^{3/2−ε}` [L]; a strip of depth `h` excludes heavy identity returns up to `exp(ηT)` at prime cutoff `⌊T^{2/(½−h)}⌋` [K].
- A transfer from these return-free intervals to bounded absolute prime traces on `log²` windows gives `Θ<1 ⇒ Θ=½` [L*].
- For `½<σ<1`, `0≤κ<2σ−1`: the dyadic mean of `|Rζ|²` is the full convolution diagonal up to `ηΣ|r_m|²`, uniformly in the resonator [L*].
- In the height aspect the sign at rung `κ>1` for the fixed system `Λ` is the exclusion of an alignment of a proportion `(log t)^{1−κ}` of the `p^{−1/2}`-mass of the primes `≤(log t)^{2κ}` [D].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| A104 | the measure of the heights at which the sizes fail on rung `κ`: `O(Ta³/log²T)` from the mean square [L*]/[D]; `T^{1−1/(2κ)+o(1)}` from moments of order `log T/log Y` [D] (unverified) | — |
| B46 | proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97, B137 | constant-precision first return past the VK rung; a collective depth floor uniform in `π(y)` | sub |
| B148 | the transfer of candidate S3 | ≥B56 |
| B121 | freezing control beyond the precision cap | sub |

### S10. The diagonal, counts and absolute geometry
Routes: ACS, HF, HAT-C, PM (count branch). Programmes: SOSZ, HAT, AGZ, HFP, AE, RIAC, HHAC, CTH, LST, KPA.

Established ([L*] unless marked):
- Forced data: `CombBezout w ⇔ RH ∧ w=Λ`; constant `c≤0` with the counterterm `log(n/2π)−c`; exchange law `c≥sup P_δ` for summable corrections, one contact changed by `t` costs `2|t|/√n`; a common factor on the contacts fails for every constant; the tree of `p` has edge length `log p` [L*]/[L].
- The tree of 2: on packets of length `≤log 4` Bézout holds exactly for edge lengths `ℓ≥ℓ*(L)`; `ℓ*(L)≤log 2−1/10000` for `L≤181/250`; for odd `p` every long tree fails on packets longer than `log p`.
- Index: one positive square ⇔ RH; exact count of the right zeros for ζ with finitely many primitive Dirichlet `L`-functions; `riemannHypothesis_of_ringDefect`: index zero of the ring defect on all families gives RH.
- Genus and Riemann–Hurwitz: `combForm{n}=(2e²/n)(1+(n/2)log(n/2π))`, negative exactly at `n=2,3`; abelian ring: contacts `Λ(n)(1+ΣRe χ_i(n))`, `2g_K(n)−2=d(2g(n)−2)+nΣlog q_i`; cyclotomic ring of prime conductor: contacts `(p−1)Λ(n)` on `n≡1 mod p`; on packets shorter than `log 2` the margin `∫f²/5000` for odd conductors `≥4π`, even `≥128π`.
- Towers: `Z_K(f)/d` differs from the mean of the twisted parts by `Z_ζ(f)/d`; for cyclotomic rings of prime conductor beyond the window `Z_K(f)≥(p−1)(½log p∫f²−C_f)`.
- Sections: the paying ring generated by `y_p=Σ_{j≥1}e_{p^j}` is a polynomial ring with unit masses in which every contact is paid; the planar square has the contacts of the square; planar values on `Γ_m` of sections vanishing on `S` are the ideal `ΠJ(m,n)`, attained; in the full square `p−e_p` violates this.
- Counts: on two graphs the functions are the pairs congruent modulo `J(m,n)`; the count is `|x_mx_n|`, quadratic on rays, not a form.
- Own comb: the system of the squares (`ζ(2s)`) exceeds `2d₁d₂` on a packet, without hypothesis.
- Finite scale: short windows coercive and blind to the contacts; finite index on every window; block means cost `εΣc_n²`; RH from floors on block-constant divisors; contacts of flat packets are overlap lengths; jets are the even multipoles of the Newtonian kernel on an axis, the two rulings the origin and infinity; the contact form of `p` is `log p·(Σ_chains(Σ_chain c_n)²−Σc_n²)`.
- Carrier: no adelic-invariant glued kernel has Weil's diagonal [L]; the weighted Green kernel descends to the rational torus with a Robin diagonal [L].

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests at verified scales | — |
| A80, A94 | A80 proved: RH iff every fixed ratio window eventually has a uniform positive coefficient-mass floor [L*]. Robust index counts distinct right zeros [L*]. The right-hand aperture index jump equals nullity; resonant apertures below any fixed bound are finite [L*]. A94: at every integer ratio `Q≥2`, eventual unshifted index lies between native rank and rank plus nullity at `log Q/2`; equality holds at nonresonant apertures [L*]. Resonant splitting remains | [exact positivity](../../drafts/pipeline/3-formalized/exact-eventual-positivity-of-fixed-comb-windows.md); [robust index](../../drafts/pipeline/3-formalized/robust-finite-comb-index-counts-right-zeros.md); [nullity growth](../../drafts/pipeline/3-formalized/weil-null-modes-force-strict-aperture-index-growth.md); [fixed-ratio index](../../drafts/pipeline/3-formalized/unshifted-comb-index-at-nonresonant-ratios.md) |
| A82 | Li/Laguerre tails formalized. Power tails have exact convergence radius `1/2-zetaZeroWidth`; every convergent subcritical tail has its reflected zero-pairing limit. Convergence excludes boundary zeros, so an attained positive width makes the endpoint diverge. RH iff every positive subcritical tail converges [L*]. The critical tail `a=1/2` never converges, but its strict growth thresholds are exactly `σ≥zetaZeroWidth`; subpolynomial critical growth iff RH [L]. For `0<a<1/2`, all positive absolute logarithmic Abel integrals exist iff `a+zetaZeroWidth≤1/2`, and their normalized mean has the canonical zero-pairing limit throughout this closed range [L]. At `a=1/2`, every positive absolute Abel integral exists iff RH, and the mean then tends to the explicit finite part `E−2B′(0)` [L]. Ordinary subcritical convergence holds exactly when every zeta zero has `Reρ<1−a`; an unattained endpoint therefore converges, without a common gap [L] | [power tails](../../drafts/pipeline/3-formalized/power-comb-tails-detect-the-zero-width.md); [boundary zeros and limits](../../drafts/pipeline/3-formalized/convergent-power-combs-exclude-boundary-zeros.md); [critical divergence and exact growth](../../drafts/pipeline/3-formalized/the-critical-power-comb-does-not-converge.md); [closed-boundary Abel classification](../../drafts/pipeline/3-formalized/power-combs-have-an-abel-limit-at-the-zero-width-boundary.md); [critical Abel endpoint](../../drafts/pipeline/3-formalized/critical-power-comb-abel-integrability-detects-rh.md); [exact pointwise boundary](../../drafts/pipeline/3-formalized/unattained-power-comb-boundaries-from-zero-density.md) |
| A114 | the limit matrices of the block-constant form with both pole moments: RH ⇔ nonnegativity on step packets (unverified) | — |
| A116 | Hecke characters and non-abelian rings: ideals as degree points, the index law per Artin character (unverified) | — |
| B87 | a count on the rays `Γ_1+Γ_p`, defined without `Q` | RH |
| B88 | the sign of the comb finite part | RH |
| B149 | Bézout for the comb pairing from a property of the object | RH (producer) |
| B152 | the comb form on block-constant divisors: `≥−ηΣσ²` at arbitrarily large block sizes, all `K,R,η` | RH |

### S11. Families, rigidity and exactness
Routes: ACS (tensor branch), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established:
- Fixed-part laws for the canonical arithmetic families; sublinear tensor growth with the trace of ζ retained ⇔ RH [L]; pole-preserving gauge deformations are isozeric; analytic prime smoothings have a moving branch; residue-class mixtures have no joint endpoint germ [L]/[K].
- Countable Beurling systems with an `L¹` or `L²` functional-equation defect are the rational primes [L]; positive continuous prime measures are not rigid [L*].
- Frobenius at one prime; cost `m·θ(S)`; `ℤ` has only the identity endomorphism [L].
- Carlitz–Goss: a digit composition is optimal iff it is greedy, for every base, residue degree and number of parts [L] (returned by the search tool; the Newton polygon of the zeta function is not assembled).

| | Obstacle | Strength |
|---|---|---|
| A115 | the Newton polygon of the Carlitz–Goss zeta function from the greedy optimum [C] | — |
| B86 | positivity of the endpoint character at unbounded rank, mixed Young shapes | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The ladder, the level and the signal
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, RHTower `QuasiRH*`, CDG.

Established:
- Sizes [L*]: floors below the trivial aperture in the conductor and the height aspect; the feasible set of a conductor lies between an `ℓ¹` ball `A₀+2Σ_{n≤e^{2a}}|w(n)|/√n≤log q` and the box `|w(n)|≤√n(log q+log(1+1/r)+C)`; a floor `−K∫|F|²` at `q` is feasibility at `qe^K`; feasible sets are convex, decreasing in the aperture, determined by `w(n)`, `n≤e^{2a}`.
- Fakes [L*]: the Liouville twist, `−Λ`, and `Λ` without pole plane fail at `log log q+η`, on the polar packets; the Liouville twist violates every floor there; in the height aspect `Λ(n)cos(t log n)` fails at `log log t+log 2+η`; a lattice with one pair of depth `δ` changes sign at the rung `1/(2δ)`; at `log log q+log 2+η` a dominated system has the bounded-shape floor on every packet and is not feasible.
- Mean over the heights [L*] (graded [S]): for the contact polynomial `D_a(t)=Σ_{2≤n≤e^{2a}}Λ(n)n^{−1/2}cos(t log n)`, the mean square over `[T,2T]` is `≤2a(2+2a)²+1` when `4e^{4a}(2+2a)⁴≤T`, against the mass `log T`; a height exists at which it is small on a grid, with Lipschitz interpolation. So the sizes are attained at aligned heights only, and at apertures up to about `¼log T` the sign on bounded shapes fails at most on a set of heights of measure `O(Ta³/log²T)` [D].
- Exchange [L*]: cancellation `(C,γ)` buys `a≤κ log log q`, `2γκ<1`; the sign on the polar packets is square-root cancellation of the Riesz mean; the height transfer `𝔚_{w,q}(e^{−itu}f)=𝔚_{w_t,q}(f)+(log(2+|t|)+O(1))∫f²` up to the shape.
- The first rung past the trivial aperture in the conductor aspect: the sign at `a=log log q+η` for a real character forces a prime `p≤e^{2η}log²q` with `χ(p)≠1` and one with `χ(p)≠−1` [D].
- Level and signal [L*]: positivity at level one on the characters of all large primes gives `Θ=½`; RH ⇔ `JasDressedPSD 1` ∧ a half-plane; `JasDressedPSD 2`; positivity on large primes at every `σ≥3/2`; the dichotomy at a level; signal `O(Z^b)` ⇒ `Re ρ≤b`; signal = smoothed Möbius sum; family continuation from two estimates.
- Source [L*]: cube of the composite cubic Gauss sum = Möbius × phase; odd-order sign law; planar large sieve. Exceptional frequencies of one coprime column pair add without cancellation.
- Budget [L*]: `lowGramExponent x (5/6−x)−principalShift x (1/6)=7/8` for every `x`; the retuned boundary is `≥7/8` with equality only at slot `1/6`; unit Gram term alone `≥29/36`; a Gram profile reaches `5/6` iff `ν≤1/15 ∧ κ+4ν≤4/3`; with its row-count law the detector has no boundary below `7/8−1/4000` [L].
- Quasi-RH is seven equivalent power savings across five programmes [L*].

| | Obstacle | Strength |
|---|---|---|
| A102 | the additive `log 2` of the height aspect (unverified) | — |
| A103 | one statement for the rate `δ=1/(2κ)=1/(2θ)` from the cancellation margin, the companion law, the mollifier trap and the seven-way list [D] | — |
| A105 | a density-matched configuration that is positive on a rung and has deep zeros at arbitrarily large heights (unverified) | — |
| A108 | the least non-residue and the least split prime on the ladder [D] | — |
| A113 | the corollaries of a half-plane premise: the rung `1/(2b−1)`, large-prime positivity above the level `½+b`, return-free windows [D] | — |
| A118 | `[X]` in the native graph: theta coefficients of the cubic residue, removal of cube indices, the mean square with uniform transfer, the detector | — (given `[X]`) |
| B159 | a rung `κ>1`: a power saving of the contacts on the integers between `m` and `m^{2κ}`, uniform in the height, that fails for the Liouville twist and for the lattice with a pair | ≥qRH |
| B156 | whether the sign on one rung `κ>1` at all large heights gives a zero-free strip for ζ (clusters) | method |
| B160 | `JasDressedPSD 1` on the characters of all large primes | RH |
| B161 | the signal bound `O(Z^b)`, `b<1`, in the native graph | ≥qRH |
| B158 | a second completed sum: a global object whose coefficients are Gauss sums of an odd order `n≥5`, or another identity that gives Möbius a functional equation | producer |

## 3. Live routes

Receiver statements are `[L]` unless marked.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or positive definiteness of the prime lag, or an attained top with an `O(√X)` prime deviation on a thick set of scales → RH.
- **Established:** endpoint energy bounded ⇔ RH; RH ⇔ `primeLag` positive definite on `ℝ` [L*]; RH ⇔ attained top ∧ thick `O(√X)` deviation; on a bounded full lag progression accessibility of an isolated right mode replaces attainment.
- **(a)** A30.
- **(b)** bounded endpoint energy (B49); deciding input (B48); attainment with the thick estimate (B110); the sign of the lag Gram matrices from prime counts (B1).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH; equivalently some feasible weight system at every aperture.
- **Established:** RH ⇔ `Ψ` locally bounded on precontact intervals; RH ⇔ feasible weights at every aperture [L*]; all-aperture weights pinned to Λ; verified-height rung; block S2.
- **(a)** A1–A3, A16, A79, A117.
- **(b)** B1, B2, B4, B18.

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established:** either one-sided bound on `A(j^m)/j^m` ⇔ RH; one controlled sample per backward window suffices.
- **(a)** none. **(b)** complete-history bounds across advancing clocks (B42).

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on a tail → RH.
- **Established:** exact tail criterion; ¬RH forces unboundedness below on every tail.
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH.
- **Established:** exact linear-floor criterion; sublinear floors impossible.
- **(a)** none. **(b)** high-LCM pairs, moving core and singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma response sign → RH.
- **Established:** calibrated Hausdorff-row sign above an explicit radius; the remaining entries ⇔ RH.
- **(a)** A1. **(b)** signs below the explicit shift, uniformly in the degree (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** bounded damped Möbius energy for arbitrarily small damping ⇔ RH; Möbius-polynomial zeros accumulate on `Re s=Θ`; orientation-cover weight `½` ⇔ RH; in world I `M(x)=O(x^β)`; the Möbius fibre mean square is small at every length `h→∞`, `h≤√x`; the cubic Eisenstein residue is nonzero; the signal of the zeta kernel is a smoothed Möbius sum whose power saving is a half-plane [L*].
- **(a)** A21, A33, A46.
- **(b)** B48, B50, B15; cubic theta identification and rational descent (B94); a bounded-index correspondence (B106); the signal bound (B161).

### SQF — Weighted squarefree count
- **Path:** a one-sided `O(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH.
- **Established:** RH ⇔ the upper law ⇔ the lower law; `Ω±(t^{−¼})`.
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH.
- **Established:** RH ⇔ a bound `C_t` for every `0<t<½`; uniform bound on a shrinking band.
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted; the finite-stratum law on shifted Jensen polynomials gives RH; `N_d≤300√(d log d)`.
- **(a)** A20, A1.
- **(b)** outer roots (B22); bounded `N_d` gives finite support only (B23, then B13, B138); heat budgets (B124).

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** collision exclusion ⇔ RH; blocks S3, S4, S8; ordinate injectivity ⇔ RH; a finite attained top breaks every continuous floor on bounded windows [L*].
- **(a)** A19, A47, A86, A109.
- **(b)** B24, B25, B47, B27, B124; B130; B83 through transport or a contradiction in world I (B89, B112, B128, B145); B13, B138, B141.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established:** exact integer trace; endpoint and Gaussian central-gap receivers.
- **(a)** none. **(b)** trace norm below one on every formation rectangle, or the Gaussian passage (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; cofinal source-work `≤2` ⇔ RH; three-way classification [L*]; one positive square ⇔ RH and the exact index [L*]; Riemann–Hurwitz for the counterterm [L*].
- **(a)** A9, A13, A80, A114, A116.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152.

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → the energy floor → `W≥0` on packets ⇔ RH.
- **Established:** `E_r↑W` with error `(1−r²)‖f′‖²/2`; for every fixed `N`, RH ⇔ the raw energy floor with its full arithmetic defect [L*]; the tower is the completed-zeta quotient [L*].
- **(a)** none.
- **(b)** at one fixed height the corrected energy bounded below by minus the jump tail on all apertures; this is `W≥0` (B1). The sign of the tail alone does not bound the energy.

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH.
- **Established:** wave and Doob receivers; normalized decay of (prime−pole)/√Y.
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** ranks `≤14` for `0<a≤½`; rank `N` from verified height `41+6(N+2)log(N+2)`; the adaptive critical Dirichlet sum is `ζ(½+ib)` up to `O(|b|^{−½})`.
- **(a)** A4, A5, A24, A42.
- **(b)** signed adaptive head near cancellation (B102); amplitude oscillation (B20); all ranks (B21).

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH.
- **Established:** complete Weil sign ⇔ Gamma/polar jump energy ≤ prime jump energy in theta ground coordinates.
- **(a)** none. **(b)** joint-node exclusion or the comparison (B36).

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ cofinal polynomial boundedness with one exponent [L*]; width slope `2w`; the displaced twisted moment below the square root with both gcd main terms [L*]; block S5.
- **(a)** A18.
- **(b)** B62, B57–B61, B63: the cofinal criterion needs unbounded `θ`, the proved range stops at `θ<½`.

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ the ladder sign on primitive vectors; `λ_n≥0` for `n≤314`; the comb form of the flat tail per degree point tends to `2+γ−log 4π`.
- **(a)** A1, A82. **(b)** the lower bound or the sign (B43).

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH.
- **Established:** completed Abel source bounded ⇔ RH; `|A_N|≤C√N e^{−c·vkScale N}`.
- **(a)** none. **(b)** bounded completed residual (B37, B1).

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity-energy rate, or a count → RH.
- **Established:** block S7.
- **(a)** A26.
- **(b)** B68, B71, B87; B147; B114, B117.

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ the Laguerre sign at every `0<h<½`; ZAL gives finite nonreal defects at every positive shift.
- **(a)** none. **(b)** the sign below the VK boundary (B29); a prime-faithful lossless stack (B69). Exact arithmetic pieces sharing zeros with ξ are excluded in the Wiener class [L*].

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower control on finite power windows of square shells → RH.
- **Established:** positivity at level one on the characters of all large primes ⇒ RH, with no half-plane [L*]; RH ⇔ `JasDressedPSD 1` ∧ a half-plane bound [L*]; signal `O(Z^b)` ⇒ that half-plane [L*]; level two holds, `3/2` on large primes [L*]; positivity on large primes at a level `σ` gives `|Re ρ−½|≤σ−1` or the edge world [L*]; constant-vector positivity on dyadic prime shells gives AAL.
- **(a)** A113.
- **(b)** `JasDressedPSD 1` (B160); the signal bound (B161; `[X]` supplies `b=7/8` outside the native graph); the moving `k`-window control (B51).

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass → RH.
- **Established:** RH ⇔ unit-bounded rows reach every tolerance; BSY sign ⇔ RH; mollifier infimum `exp(2I(1))`.
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH.
- **Established:** two-grid criterion at fixed offsets; detector degree explicit.
- **(a)** A1. **(b)** nonnegativity at every degree (B30).

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH.
- **Established:** coverage and closed-margin criteria.
- **(a)** none. **(b)** the cover (B32).

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence ⇔ RH; AAL ⇔ arbitrarily high all-cut zero transport; graded recurrence with exponent `(30/13)(1−σ)`; zero discs of strip-almost-periodic functions recur relatively densely; the resonator mean controls ζ in mean square [L*].
- **(a)** none.
- **(b)** uniform target mass (B72); transport (B83, B89); breadth past VK (B97, B137); B145. Mean square alone gives no lower bound for the mass of returns.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH.
- **Established:** attained blind minimum `≥1/20` for `a≤(log 2+1/50)/2`; sign-gauge balance iff `c≤log ρ`.
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH.
- **Established:** full-mode compactness ⇔ RH; cofinal arbitrarily small charge suffices.
- **(a)** none. **(b)** charge below `ε` at arbitrarily late stages (B33).

### OWU — Odd sector
- **Path:** archimedean-minus-prime positivity on odd tests → RH.
- **Established:** odd RH criterion; unit-window floors [K].
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
- **Established:** block S3; the upper side alone on undeleted windows [L*]; counts and moments [L*]; a verified height covers every prime below its rung [L*].
- **(a)** A9.
- **(b)** B130; B6, B101.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH.
- **Established:** single-shift receiver; outward kicks of `{2,3,4}` cost `<991/1000` of the Lévy energy below `2c<log 5`.
- **(a)** A7. **(b)** one shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** global incidence allocation → RH.
- **Established:** exact allocation; VK signed cost; subcritical orthogonal error control.
- **(a)** A9, A13. **(b)** signed cost `C_σe^{2σr}` (B45); polar payment (B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling, or glued index `≤1` → RH.
- **Established:** glued index `=κ_ζ+1`; damped coupling bounded ⇔ RH; undamped coupling on a two-prime cone gives AAL.
- **(a)** none. **(b)** the damped bound; sublinear tensor loss (B39); ZAL for the undamped branch.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** a floor on block-constant divisors → a floor on all divisors → packet positivity → RH; or the prime-window floor.
- **Established:** block S10; block means cost `εΣc_n²`; RH from floors on block-constant divisors [L*]; forced weights, constant, scale and tree lengths [L*]/[L]; exact index for ζ with Dirichlet `L`-functions [L*]; the planar square, the split norm, the own comb, the tower [L*].
- **(a)** A28, A41, A48, A59, A80, A82, A94, A108, A114, A116.
- **(b)** B152, B149, B88, B87; B130; B28.

### ECP — Endpoint character positivity
- **Path:** endpoint jets → coherent symmetric-group class functions → PSD character Grams at every rank ⇔ RH.
- **Established:** column projections nonnegative; Toeplitz minors through order 200; four mixed shapes.
- **(a)** none. **(b)** positivity at arbitrary rank (B86).

## 4. Candidates

Each needs its source-to-receiver step first (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF.

| Candidate | Established | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| S3 | weighted identity-return bounds [L]; a strip of depth `h` excludes heavy identity returns up to `exp(ηT)` [K]; the transfer gives `Θ<1 ⇒ Θ=½` [L*] | A113 | the transfer (B148, ≥B56); natively also a half-plane |
| SEC | Fock boundedness at every divisor point ⇔ `Re s=½` [L] | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` [L] | none | arithmetic descent on actual zero fibres |
| APF | prime/grade trace reconstruction on real labels [L] | none | full-divisor exhaustion and RH landing |
| EGC | zero-pair contour; count error `≤32ε²log T/T` [L] | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on the blind plane [L] | none | faithful endpoint admission |
| FEL | KL accounting [L] | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution [L] | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport [L] | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion [L] | none | RH-sufficient orientation law |
| W1C | Laguerre–Pólya approximants on one interval give RH; index-one limits give RH [L] | none | an independent index-one family (B146); exact constituents with a zero are excluded in the Wiener class [L*]; stable polynomials in the prime fields have linear zero counts [L] |
| WBF | Gram recovers magnitudes and phase class [L] | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| SOSZ ScaleLocality | logarithmic, `log²` and `√T` windows; exceptions; upper side; counts; local moments; half-period law; finite top layers; floors depending on the length give AAL; weighted floors with sharp coefficient two; the density of the counter-configuration [L*]/[K] | A78, A89 | B130, B144 |
| SA (selective arithmetic) | trivial aperture in the conductor and the height aspect; feasible sets; box and `ℓ¹` laws; fakes; exchange rate on the prime and the zero side; first selective window; Dirichlet `L`-functions on the ladder [L*]; the contacts cancel in the mean over the heights; level one and the abscissa laws; bounded shapes do not decide feasibility [L*] | A102, A103, A105, A108, A117 | B159, B156 |
| FCT (family continuation) | continuation from a common signal; a signal bound with level one gives RH; the signal as a Möbius sum; columns correlate through one residue; odd-order sign law; planar large sieve [L*]; the sieve over the Eisenstein integers; the lattice sum `6ζ(s)L(s,χ₋₃)`; the geometry of the detector as a vertex [L] | A113, A118 | B158, B161 |
| MMD | cubic Gauss arithmetic, reciprocity, the cubic Eisenstein residue and its transport [L] | A33, A118 | B94; the identification of the arithmetic coefficients with the reciprocal signal and both bounds below `β` uniformly in the family |
| CTZ (constituents) | the jump law on strips, with poles; Wiener's lemma on a strip; no constituent with a zero in the Wiener class; boxes; the Bohr strip; sizes on a circle; progressions [L*] | none | B153 (bounded class) |
| HFP (Hodge theory of a fixed part) | normal form; short windows; finite index; block averages; flat packets; multipoles; chain squares; one inequality per prime on the comb [L*]/[L] | A80, A82, A94, A114 | B152, B149 |
| AGZ | square, contacts, carries, tower, one ring; forced weights, constant, scale, tree lengths; exact index of rings; Riemann–Hurwitz; cyclotomic combs; towers; paying ring and planar square; split norm; own comb; the trivial aperture and Deuring–Heilbronn on the twisted comb; the zero side of an explicit formula from two vertical lines, without functional equation [L*]/[L] | A108, A116 | B149, B88, B87 |
| ELT | atoms and landing forms; filters at every speed; centred Vaughan currents at growing order; separated cofactor pairs [L]/[K] | A47, A86 | B141, B145, B138, B13 |
| ZCG AbscissaLaws, Recurrence | split, atoms, sectors, quasi-RH as a tail law, graded recurrence [L*]/[L]; projection to the line; density-matched model [L*] | A109 | B13, B83, B138 |
| IRW / EFT | the paired ξ model: an entire function with ζ's Gamma factor and count that does not land [L*]; continuous prime measures [L*] | none | B112 |
| IRP | index law; flow criterion; prime lag [L*]; exponential polynomials are no factors [L*] | none | B146 |
| AWT | fixed-part laws; cover-family tensor criterion; gauge deformations [L]/[K] | none | B86 |
| SignFreePurityMechanisms | height separation ⇔ bounded prime traces; prices of Frobenius lifts; digit compositions and greedy optimality [L]; the return transfer collapses strips [L*] | A115 | B148 |
| HAT | Green formula; weighted covariance; clock; scattering tower as a completed-zeta quotient; jump-tail floor ⇔ RH; unbounded critical inverse [L*]/[L] | A54 | B88, B117 |
| AHMH / BHR / ASH / CTH | cavity receivers, reflection Krein forms, halving descent, ringdown, count door [L] | A26, A41 | B68, B71, B87, B147 |
| TTPO / CDGeo / PTT / TAPO | depth law, VK breadth, strip breadth, collective counts; resonator means [L]/[L*] | A24, A104 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates; cut kernel; parity blindness of bilinear statements [L]/[L*] | A30 | B48, B55, B67 |
| AHD / CACT | threshold identities, pole channel, ground states, classification [L*]/[L] | A9, A13 | B104, B123 |
| MZF / CDG | hyperbolic density; twisted moments below the square root; mollifier trap; pure Möbius criterion [L*]/[L] | A18, A111 | B62, B57 |
| Census (IGP, TTPC) | `0.67250071`; alternatives; exchange rates; positivity does not reach `75%` [L*]/[L] | A112 | B150, B57 |
| VHR / TCS | verified-height rungs; height 67; window and prime two-bump entries [L*] | A1–A5 | — |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: `P(p)≤A(p)+K` on the primes of logarithmic windows off power-thin exceptions; slack `p^{o(1)}` | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count), every window route through the prime two-bumps |
| Σ: the sign on every window, equivalently every rung of the ladder, verification at every height, one positive square of the comb pairing, feasible weights at every aperture | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: continuation at small time and the theta head at the critical zeros | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision and long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Level-one dressed positivity on large primes (RH); the signal bound (a half-plane; `[X]` outside the native graph) | JAS; MC (signal), S3 |
| Γ: reflection and count | PM, ECP |
| The exceptional coordinate: world I (B13, Landing, DH) and world II (ZAL) | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length, Dirichlet polynomials longer than the height | every route at all heights; BAG; TH certificates; WD; the centred type-II current of ELT; the rungs above one in the height aspect |
| Missing source landing | the twelve candidates |
