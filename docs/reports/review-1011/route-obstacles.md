# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `d0cfbbc75f` with its working tree (2026-11-10). Working log: `logs/review-1011-frontier-facts.md`. Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, the census of mechanisms, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. Formulations are not independent mechanisms: HJ is PA; the BSY criterion of FEL belongs to CTF; SEC and CDC/BSH are candidates; PCS is a retired label. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.**
- `[L*]` Lean statement read for this report, in source or through the corpus search tool.
- `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/`; statement not re-read here.
- `[S]` Lean source present, graded unfinished or unintegrated by the frontier map, or untracked in the working tree; statement read. `[K]` Lean with transitive axiom audit, as recorded.
- `[D]` deduction made in this report from `[L*]`/`[S]` statements; not a Lean theorem. `[C]` classical literature, not in the corpus. `[A]` assessment.

**Strength.** RH; ≥qRH (a zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); sub (below quasi-RH and below AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md). `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1 ⇒ Θ=½`. `B` the cubic spline, `S` its lag structure, `c_B(u)=Re S(u)`, `c_p=c_B(log p)`; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I**: ¬AAL, a finite isolated top layer at `β<1` over a remainder. **World II**: AAL ∧ ¬ZAL, `Θ=Θ∞>½`. **Class `𝒵(γ_min,C)`**: tempered reflection-symmetric zero configurations without real zeros, lowest ordinate `≥γ_min`, `N(t,t+1)≤C log(|t|+3)`. The **depth** of a zero is `|Re ρ−½|`. **World I-a**: world I with the remainder on the line; **world I-b**: world I with an off-line tail. A **window of ratio `Q`** is `(N,QN]`, its **aperture** `½log Q`. The **twisted part** of the square of a quadratic ring of conductor `q`: jets, counterterm `log(qn/2π)`, contacts `Λχ`, no pole plane. `W` Weil's form; `a*(ζ)` onset aperture; `Ψ=½log H₁`; `R=c⁸/log N`; `R_c`, `R_polar`, `R_halfline` whole-space, polar-payment and half-line thresholds; `W₀=⨅_A windowThreshold(A)`. `E_r` the arithmetic-clock Green energy. `𝒢=W(ℤ)` the arithmetic square in ghost coordinates, `Γ_n` its graphs. **Comb pairing**: for a real divisor `D=Σc_nγ_n` on a finite set of degree points, `Γ_m·Γ_n=½(1/|m−n|+1/(m+n))+Λ(n/m)` off the diagonal, `Γ_n·Γ_n=−log(n/2π)`, `d₁=Σc_n/n`, `d₂=Σc_n`; **comb form** `2d₁d₂−D·D`. A **heavy return** is a `δ`-return (`δ≤1/20`) at height `t` of a subset of the primes `≤y` omitting at most `1/1000` of the `p^{−1/2}`-mass.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `∃K`: `2c_p≥−K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ Weil positivity of `B+τ_{log p}B` at every prime | [L*] | Σ (Weil's sign), Π (a prime count) and the count door are one inequality per prime |
| RH ⇔ the same on the primes of arbitrarily late logarithmic windows, outside at most `Ce^{δT}` primes per window (`δ<1`); the absolute form `\|2c_p\|≤K` is equivalent; the exponent `p^α` reads the width exactly; a power saving `p^α`, `α<½`, on such windows is quasi-RH | [L*] | the minimal face is local in scale at radius `32 log(T+2)` and tolerant of power-thin exceptions |
| In the class `𝒵(γ_min,C)` no bounded window length and not every unbounded radius decides: one configuration with an unattained top `½+Θ` beats every floor on windows of every fixed length, and on windows of a radius `R(T)→∞`, `R=o(log T)` | [L*] | below the logarithmic radius no receiver at the level of `𝒵` exists; a floor on unbounded windows excludes world I [L*] |
| That configuration has at least `8(k+1)Γ_k` zeros of real part `½+x_k` with ordinate in `[Γ_k,2Γ_k+1]`; ζ has `o(V)` zeros of depth `≥d₀` below `V` for every `d₀>0`, and at most `T^{(30/13)(1−σ)+ε}` right of `σ∈[½,5/6]` | [D]; [L*] | the counter-configuration uses a positive density of deep zeros; on the aperture side the resolution law counts the deep neighbours of a zero [L*]; its transport to the prime side is open (B151, A92) |
| `Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; `Θ<1 ∨ AAL` | [L*] | a failure of RH lies in world I or world II; world I has a zero-free strip for free [D] |
| World I: `M(x)=O(x^β)`, `β<1`; heavy returns need `log t≥c·y^{1−β′}` with `β′<Θ`; prime-only filters read each top residue at every damping speed; the top has two distinct positive ordinates or the corrected current diverges at every supercritical speed; the Vinogradov–Korobov bound decays only above `a(1−σ)/2` | [L*] | the finite-layer receiver is complete; the gap `a(1−β)/2` is the exclusion itself [D] |
| RH ⇔ ZAL ∧ B13 ∧ Landing; no two of B13, Landing, DH fail together; FE-only and Euler-only models violate landing | [L*] | three atoms on the RH path; each needs the FE and the Euler product jointly |
| The zero motive of ζ is the fixed part of the canonical arithmetic families: moments bound the atom at the trivial fibre only by the trivial bound; product positivity couples one way; with the trace of ζ retained, sublinear tensor growth is RH | [L*] | Deligne's family step has no producer among these families |
| Pole-preserving gauge deformations of ζ are isozeric; analytic prime smoothings from `1` to `−1` keep every multiplicity right of `max(½,1−mt)` and have a moving branch; a Dirichlet series with ζ's FE is a multiple of ζ | [L*]/[L] | ζ has no moduli; no fake keeps both structures [D] |
| A bounded holomorphic Dirichlet series on a half-plane whose zeros there are zeros of ξ has only critical-line zeros; every Dirichlet polynomial with at least two terms has a zero that is not a zero of ξ, by the agreement of the constant terms on the two sides of the line | [L*] | the off-line zeros are the zeros of no bounded Dirichlet series; ξ has no Dirichlet-polynomial constituent; bounded series with zeros on the line are open (B153) |
| `x↦xⁿ` is a Frobenius at one prime only; order `m` of the `p`-derivations at every prime of `S` costs `m·θ(S)`; Riemann–Roch on the tower of lines has the gluing index `K!` as second term and Bézout returns `n≤\|x_n\|`; a section of the square pays the contacts below a degree point and one contact per prime above | [L*] | Stepanov's inequality over ℤ is the product formula; sections do not certify prime powers above or jets |
| The arithmetic square `𝒢=W(ℤ)` carries the prime part of every off-diagonal intersection number as contacts; no object of finite type carries the contacts; the pairing of the degree points has the limit `2d₁d₂−Z(f)` on packets; RH ⇔ the intersection form on `H,V` and every finite family of packets has exactly one positive square; the defect has at most as many negative squares as ζ has zeros right of the line, and at most the defect of a Hermite–Biehler splitting that covers the right zeros | [L*] | the count door and the sign door are the Hodge index of one pairing |
| The comb form is one matrix on the integers with no scale in it; on windows of ratio `≤19/18` it is `≥(1/50)Σc_n²` at every scale; on windows of ratio `≤Q` it is nonnegative on a subspace of codimension below `2QR(Q)` at every scale; on windows of ratio `≤2` it is the same for every system of contact weights; on `{2}` it is negative; a lower bound `−ηΣc_n²` at arbitrarily large scales at every ratio gives RH | [L*] | the Hodge index is a statement on real vectors at finite scale with finite index; short windows are not selective |
| Comb Bézout with contact weights `w` ⇔ RH ∧ `w=Λ`; a weight differing from `Λ` at one integer fails on some packet without hypothesis; unit masses on the integers force `w=Λ`; with the counterterm `log(n/2π)−c` the inequality holds ⇔ `c≤0` ∧ RH | [L*]; [S] | the sign is carried by the contacts; no positive margin, no other weight, no larger constant; a uniform floor `−C∫f²` over all packets is RH |
| On the comb `q^ℤ` of a curve the comb form is the Toeplitz form of the Frobenius eigenvalues, without jets and counterterm; on the comb of norms of a quadratic ring the contacts are `Λ(1+χ)`, the counterterm `log(qn²/(2π)²)`, the limit `2d₁d₂−Z_ζ−Z_χ`, and the twisted part has no pole plane | [S] | one matrix for ζ, a curve and a quadratic ring; the conductor is a density; the class group does not enter |
| The jets are `Σ_j min^{2j}/max^{2j+1}`, each weight a positive semidefinite kernel with diagonal `1/n` | [L*] | the archimedean part is a sum of Hardy squares minus diagonals; the even multipoles of the Newtonian kernel on an axis [D] |
| Every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal and drifts to `−∞` against Weil's off-diagonal; the weighted adelic Green kernel descends to the rational torus with a leafwise Robin diagonal; the critical spherical average recovers it | [L*] | Weil's diagonal is not one glued carrier object; the quotient Robin diagonal is not Weil's degree diagonal |
| `E_r(f)≤W(f)`, `0≤W−E_r≤(1−r²)‖f′‖²/2`; the damped form has a finite limit exactly on the closed Weil form domain | [L*] | the clock is an ordered approximation of Weil's form; its sign is Weil's sign [D] |
| The scattering tower of height `N` has the jump density `(1−e^{−Nt})·archLevyDensity` and contacts weighted `1−n^{−N}`; its energies extend continuously to `L²` and tend to the closed Weil form; the second-height defect tends to `½∫\|u′\|²` | [K]/[L] | the tower is the explicit formula of `Λ(s)/Λ(s+N)` and approaches Weil's form from below by a positive jump tail [D] |
| Positivity at aperture `a` forces `δa<12((4n_δ+2)log(10⁶/δ)+log(A₀log(\|γ\|+3))+18)` for a zero of depth `δ` with `n_δ` deep neighbours within `±100`; a configuration with ζ's local counts hides a deep zero at height `T` to aperture `(log T)/36` | [L*]/[L] | aperture and height exchange at a rate set by the number of deep neighbours |
| RH ⇔ ξ is a locally uniform limit of conjugation-real entire functions with at most one right-half zero each; the Eisenstein constant term is pure off the real axis for `Y≥1`; the same line law holds over impure fixed parts | [L*] | the index is semicontinuous; a family does not prove the purity of its fixed part |
| On the flow, Castelnuovo–Severi for every divisor of Frobenius graphs ⇔ the module is pure and effective; for the zero motive with weights `1/(ρ(1−ρ))` ⇔ RH | [L*] | RH ⇔ the central trace of the zeros is a positive definite function on `ℝ` [D] |
| RH ⇔ the ordinate is injective on the zeros ⇔ `\|c_p\|≤K` at every prime | [L*] | separation by the height is a receiver |
| One cuspidal cavity function of Hecke forms: RH ⇔ energy rate `y^{¾−ε}`; one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero | [L*] | the horizon has complete and sharp receivers |
| Unconditional savings: Vinogradov–Korobov pointwise; Guth–Maynard density `30/13`; deep zeros `o(V)`; Matomäki–Radziwiłł for μ; simple critical zeros `≥0.67250071` | [L*]/[L] | everything past VK is in law [D] |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | format exact on every window; a window at aperture `a` follows from verification to `windowHeight(a)` |
| M2 Calibration | window cones, blind positivity, margin | cone pinned to Λ; sign open |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | complete and sharp receivers; rates and signs open |
| M5 Square-root cancellation | smoothed prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH; purity thresholds are the width |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros at rate 2; clusters and depth density `o(T)` open |
| M8 Finite-layer receiver | damping filters, boundary rotation, centred Vaughan currents of every moment order | complete in world I; arithmetic bound in the growth range is the exclusion |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level; exact count = Chebyshev; cost `m·θ(S)`; Stepanov at one prime bounds Heilbronn sums |
| M10 Count | nonnegative count with quadratic Tate limit | every hyperelliptic curve; over ℤ no count known |
| M11 Orbit at finite time | prime phases, returns, linear forms in logarithms | depth by Baker; breadth to VK; in a strip to `exp(c·y^{1−Θ∞})` |
| M12 Critical compactness | thresholds, pole channel, half-line ground states | `R_c=R_polar=R_halfline≤W₀`; three-way classification |
| M13 Topology of the prime complex | nerve, persistence, orientation cover | centred count `M(N)`; weight `½` ⇔ RH |
| M14 Infinite-rank elimination | towers, thick sets, Turán, resolvent of a tower | elimination proved; with an attained top a thick crude count is RH |
| M15 Prime-degree sampling | bounds at decisive samples, logarithmic windows, exceptional sets, two-bump comb packets | RH from one side or sign-free; resolution logarithmic in `𝒵`; slack `p^{o(1)}`; estimate open |
| M16 Intersection on half-products | zonotope, `ℍ³` and tree fibres, adelic carrier | off-diagonal Green formula; invariant glued diagonal refuted |
| M17 Absolute geometry | Λ-square, contacts, carries, tower of lines, archimedean fibre, one ring of sequences | square is a curve; no finite-type carrier; carry class nonzero |
| M18 FE rigidity | Hamburger, defect isolation, gauge deformations, analytic smoothings | identifies ζ; moves no zero |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing; all open for ζ |
| M20 Families and monodromy | gauge torus, vertical family, covers | fixed-part laws: no producer |
| M21 Index and limits | index law, Hermite–Biehler defect, index-one limits, flow | RH ⇔ limit of index-one objects; no independent family |
| M22 Separation | ordinate injectivity, Newton polygons, coefficient gaps | receiver; separation by absolute value excluded for ζ |
| M23 Hodge lattice at finite scale | comb pairing, Zariski's lemma, block Schur test, gauge of the flat tail, jets by weights, combs of curves and of quadratic rings | short windows coercive and blind to the contacts; finite index; one positive square ⇔ RH; no positive margin; any uniform floor is RH |
| M24 Arithmetic constituents | Dirichlet-series factors, recurrence against the density theorem, two-sided constant terms | bounded factors are pure; no Dirichlet polynomial is a factor |
| M25 Conductor ladder | twisted part of the square of a quadratic ring, trivial aperture, exceptional square | negative semidefinite to aperture `log log q−log 4` [D]; one square open at `log log q+C` |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators | amplify or reshape a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- `R_c=R_c^{PSD}=R_polar=R_halfline`; the thresholds `=⊤` ⇔ `a*(ζ)=⊤` ⇔ RH [L*]; `0<R_c≤R_nonneg≤R_polar≤R_high=W₀` [L*].
- The complete matrix at ratio `R` is positive ⇔ the primitive hyperplane is ∧ the pole channel is; below `W₀` the pole channel decides; `R_c=W₀` ⇔ the pole channel is eventually positive at every `R<W₀` [L*].
- RH, or ¬RH with `R_polar<W₀`, or ¬RH with `R_polar=W₀` finite, a critical half-line ground state and every such state orthogonal to the polar source [L*].
- Complete tilted-spline matrix PD with floor `κ/(2c⁷)` for `1≤c≤(log N)^α`, every `α<1/8` [L*], and at one critical multiple [K]; no countable square-bounded family of holomorphic multipliers dominates the depleted kernel [L].

| | Obstacle | Strength |
|---|---|---|
| A9 | explicit constants of the eighth-root horizon and the Beurling schedule | — |
| A13 | near-gcd charges and periods beyond the admissible scale (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; low-packet payment at every ratio | RH |
| B104 | whether a critical half-line ground state at finite `W₀` can be polar-orthogonal; pole-channel positivity at every `R<W₀` | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow and the aperture–height exchange
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL.

Established:
- RH ⇔ `W≥0` on every window [L]; RH ⇔ `Ψ` bounded on every bounded precontact interval ⇔ `L=artanh r` bounded there; off RH the angle is unbounded above every base [L*].
- `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]`; RH is verified through height 67 [L*].
- Window positivity at `a` forces `k·pairEnergy(δ,a)≤(K/2)ℓe^{2(2π/ℓ+σ)a}` for an off-line site of depth `δ` in a sea of depth `≤σ` with at most `K` zeros per cell [L*]; for ζ, `δa<12((4n_δ+2)log(10⁶/δ)+log(A₀log(|γ|+3))+18)` with `n_δ` the number of zeros of depth `≥δ/8` within `±100` [L*]; positivity at aperture `λ·½log(T/2π)`, `λ>1`, bounds the depth at height `T` by `exp(−c log³(T/2π))` [L*]; model configurations hide an off-line zero at height `T` up to aperture `(log T)/36` [L].
- A window blind to a set of lower density `D` has aperture `≥πD`; a cancelling cluster at aperture `a` has upper uniform density `≥2a/π` at any depth; finite clusters never cancel [L*]/[L].
- The best margin of the window `[−c,c]` is `≤K exp(11c/2−πe^{2(c−2)})`; prime-blind positivity at level `A+1` gives a weight system that is Weil-positive to level `A`; positivity at aperture `A` depends on the weights with `log n≤2A` [L*]. RH ⇔ at every aperture some weight system is Weil-positive [D].
- Floors `(1/20000)/2^k` through `a_k<0.3621`; margin `∫f²/5000` at `a=181/500`, `∫f²/8000` at the enlarged aperture `<½` [L*]/[L]; cone pinning; finite templates exactly below spread `27/5` [L].

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A79, A81, A93 | matching constants in the aperture–height exchange; the block constant `R(Q)` against the resolution law; the exchange atlas of the receivers (unverified) | — |
| B1, B2, B4, B5 | sign on every window; bounded oscillation of `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo.

Established:
- RH ⇔ lower bound at every prime ⇔ on the primes of arbitrarily late logarithmic windows ⇔ the same off `Ce^{δT}` primes per window (`δ<1`); width form at exponent `p^σ`; Stepanov form `P(p)≤A(p)+Kp^σ`; a power saving on such windows ⇔ quasi-RH; absolute form on log-square windows by signed deletion; under ¬RH every late window keeps a violator outside every such exceptional set [L*].
- `r√T` windows decide every tempered configuration without real zeros; two primes suffice on such windows [L*].
- Every `L>0` has an impure tempered configuration bounded below on arbitrarily late windows of length `L`; with `δ`-separated deep ordinates length `80/δ+1` decides from below and from above [L*].
- In `𝒵(γ_min,C)`: one configuration of simple zeros with unattained top `½+Θ` (any `0<Θ≤½`) is bounded below beyond every bound on windows of every fixed length and on windows `|u−T|≤R(T)` with `R` monotone, `R→∞`, `R=o(log T)`, also at the prime logarithms; `R` is built with the configuration [L*].
- Sets with arbitrarily long intervals are Bohr-dense; a floor on a Bohr-dense set puts an attained top on the line [L*]/[L]: a floor on windows of any unbounded radius excludes world I [D].
- Exceptions `O(X^α)`, `α<1`, keep the criterion; off a relative-density-zero set of primes RH ⇔ ZAL ∧ the Stepanov bound [L*].
- The block tower of the counter-configuration uses, at level `k`, the ordinates `d/(4(k+1))`, `4(k+1)Γ_k≤d≤8(k+1)Γ_k`, each split into two simple zeros, at one depth [L*]; the pairs synthesize signed amplitudes [D]; ζ's zeros of depth `≥d₀` number `o(V)` [L*].
- RH ⇔ a floor on the scale limits of the comb form on two-bump packets at `log p`, for the primes of arbitrarily late logarithmic windows off `Ce^{δT}` exceptions [L*].
- A sum of `n` modes with frequencies `≥Γ` whose real part is nonnegative on an interval of length `L` has `ΓL≤(2n+1)π`; a floor `−K` forces `‖Re Q‖_{L¹(w)}≤K‖w‖₁+Σ|a_j||ŵ(γ_j)|` for every smooth weight on the window [D].

| | Obstacle | Strength |
|---|---|---|
| A72 | count door on logarithmic windows with exceptional sets [D] | — |
| A73, A76 | one-sided upper side on logarithmic windows; exceptional sets in the absolute and signed criteria (unverified) | — |
| A78, A92, A95 | cluster form of the separated-window theorem; the resolution law on the prime side with the count of deep neighbours; a layer of `k` quartets seen on windows of a length depending on `k` (unverified) | — |
| A83, A89 | density-matched form of the counter-configuration [D]; prescribed radius and the constant in `32 log(T+2)` (unverified) | — |
| A58, A59 | effective gap iteration; residue-class primes [C] | — |
| B130 | the bound itself on any decisive sample | RH (≥qRH at `p^σ`, `σ<½`) |
| B151 | the prime-side resolution law in ζ's class: the radius that decides configurations with ζ's local counts and deep zeros of density zero | method |
| B144 | separation of the off-line ordinates of ζ | sub |

### S4. Continuation, nodal geometry and index
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Programmes: NGF, FFP, ADO, AES, IRP.

Established:
- RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*]; heat finiteness does not pass to `t=0` [L*]; linear AAL along the heat flow is RH [L].
- RH ⇐ every Jensen polynomial of Ξ real-rooted [L*]; infinitely many degrees suffice; `N_d≤300√(d log d)`, `sup_d N_d` = off-line multiplicity [L]; at each degree finitely many shifted Jensen polynomials fail real-rootedness and a law excluding finite nonempty exceptional strata gives RH [L*]; the same law on the cosine family gives RH ⇔ ZAL [L].
- RH ⇔ every real zero of `A_h=(Ξ(·+ih)+Ξ(·−ih))/2`, `0<h<½`, is simple [L*].
- Index law: a Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points, attained by `cosh` models; the bound passes to locally uniform limits; RH ⇔ ξ is a limit of index-one objects; `ξ(s+½)±ξ(s−½)` is pure; the cleared Eisenstein constant term has a right-half zero exactly for `Y>4πe^{−γ}` [L*].
- Flow: for summable, locally finite modules in a vertical strip the trace on `x≥1` determines the module; Castelnuovo–Severi on every divisor of graphs ⇔ pure and effective ⇔ positive definite central trace; for the zero motive ⇔ RH [L*].
- Factors: a bounded holomorphic Dirichlet-series factor of ξ is pure; a Dirichlet polynomial with a constant term and its zeros on the line has a functional equation; every Dirichlet polynomial with at least two terms has a zero that is not a zero of ξ; a zero-free exponential polynomial is bounded below on closed half-planes and its inverse expands over the monoid of its frequencies [L*].
- A Hermite–Biehler splitting that covers the right zeros of ζ with a defect of `κ` points bounds the negative index of Weil's form by `κ`; the cleared constant term gives index at most one for `Y≥1` and zero for `1≤Y≤4πe^{−γ}` [L*].
- Approximants that are Lee–Yang or half-plane stable polynomials in the prime fields have linear zero counts [L]; `H_{−τ}` has infinitely many non-real zeros for every `τ>0` [L]. If `−Gζ/s` is holomorphic in the strip and bounded near the line, with `G=Σb_ia_i^s`, `0<a_i≤1`, right of the line and `G=Σc_jq_j^s`, `q_j≥1`, left of it, the constant terms agree: `Σ_{q_j=1}c_j=Σ_{a_i=1}b_i` [L*].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon at the exponent `(3/2+ε)/t` with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| A90 | the flow criterion in prime form [D] | — |
| B153 | a bounded Dirichlet series on a half-plane containing the line with a zero and all its zeros among those of ξ | method |
| B24, B25 | collisions at small time, all heights; frequency below one | RH |
| B22, B23 | outer roots of the Jensen polynomials; `N_d` bounded | RH; ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |

### S5. Near-line geometry, long moments and the census
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation.

Established:
- RH ⇔ cofinal polynomial boundedness of long Möbius-mollified second moments; a strict slope saving gives RH [L]. BSY: RH ⇔ `∫log|ζ(½+it)|dt/(¼+t²)=0`; `tanh(I/2)≤d` for every Báez-Duarte residual [L*]; RH ⇔ unit-bounded chronological rows reach every tolerance, and otherwise no budget `exp(ε^{−θ})`, `θ≤2`, does [L*].
- Census: critical-line density `≥0.67250071` gives the covariance ceiling `4π(1−0.67250071)` [L*]; failure of `θN`, `θ∈{7/10,3/4,4/5}`, forces `(1+HD(1)−2θ−1/A−ε)N` simple off-line zeros within `A/log T` [L*]; `7/10≤certOpt(B)` ⇔ `B≤4` [L].
- The off-line second moment is `o(V)`; zeros of depth `≥d₀` number `o(V)` [L*]; Guth–Maynard exponent `(30/13)(1−σ)` [L*]; Matomäki–Radziwiłł for μ in fibre form [L].
- The prime polynomial of a window at a height is the contact weights of the square at that height; contacts plus the off-line correction minus the smoothed increments of `S` tend to `0` [L*].
- Necessary mollifier length `exp(c log²T)`; long mean values are collision counts of order `X²` [L].

| | Obstacle | Strength |
|---|---|---|
| A18, A21 | twisted moments past `21/50` [C]; census items | — |
| B57 | depth density `o(T)` (all but `o(N)` zeros within `o(1/log T)` of the line) | sub |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | bounded form factor `F≤4` on `(1,10/9)` (70%) | sub |

### S6. Production, precision and the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established:
- `c₁/(√K(1+log K))≤bestRate K≤exp(−(log K)^α)`, `α<3/5`; rates `K^{−a}` for all `a<½` give RH; a rate `K^{−a}` forces `Re ρ≤1−a` [L*]; RH ⇔ `log N(A_N)≤N+C√N log²N` for the fixed-point auxiliary, and for the squarefree auxiliary [L*]; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [L*]; RH ⇔ the pole-regularized prime series converges right of `½` [L*]; RH ⇔ Robin's inequality at `lcm(1,…,n)` for large `n` [L*].
- Orientation cover over ℤ: `D(N)=Ω±(√N)`; weight `½` ⇔ RH [L*]; in world I `M(x)=O(x^β)`, `β<1` [L*].
- Stepanov at one prime: every fibre of the truncated logarithm over `𝔽_p` has at most `100p^{2/3}` points; pair collisions of the Teichmüller image in `ℤ/p²` are these fibres; `|Σ_{n=1}^p e(an^p/p²)|≤5p^{11/12}` for `p∤a` [L*].
- Producer rate = Mertens level; parity exponent = zero abscissa; Farey discrepancy ⇔ RH; Möbius over `ℤ[ω]` a cubic Gauss coefficient [L].

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients [C]; singular indices past the cubic cutoff | — |
| B48, B49, B50, B53, B54 | deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | past Vinogradov–Korobov | sub |
| B56 | `Θ<1 ⇒ Θ=½` | sub (implies AAL [D]) |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers and the modular horizon
Routes: PM; W1C (candidate). Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT.

Established:
- RH ⇔ every compact pulse rings down at `e^{−(¼−ε)τ}`; a zero-free strip of width `2δ` ⇔ the rate `e^{−(δ−ε)τ}` [L*]; RH ⇔ every tent reflection Krein form has negative index 0 [L*]; one cavity function of Hecke forms is a complete and sharp receiver, and a zero-free strip ⇔ a rate `y^α`, `α>½` [L*].
- One Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero [L*]; any halving pair forces `Θ≥2/3` [L].
- RH ⇔ an `ℕ`-valued count with Tate limit the integer probes exists; quadratic growth of an `ℕ`-count ⇔ `Q≥0`; on a hyperelliptic curve the defect of an integral class is a natural number [L*].
- The cleared Eisenstein constant term has all zeros on the line for `1≤Y≤4πe^{−γ}` and one real exceptional pair above [L*].
- Weil's functional on `C²_c` packets is the limit of Robin-normalized Maass–Selberg diagonals, independent of the centre of the packet [L*]; the Green damping has a finite limit exactly on the closed Weil form domain and its coercively shifted inverses converge strongly to the restricted Weil covariance [L*].
- The scattering tower of height `N`: exact jump kernel `(1−e^{−Nt})·archLevyDensity`, contacts weighted `1−n^{−N}`; continuous `L²` extension; limit the closed Weil form on its domain and `+∞` outside [K]; the mass-corrected second-height defect tends to `½∫|u′|²` on smooth interior packets [L].

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| B68 | independent reflection Krein positivity, Krein flux, dispersion bound | RH |
| B71 | universal decay `e^{−t/4}`; horocycle, Farey, Narain or cavity rate `y^{¾−ε}` | RH |
| B87 | a count with Tate limit `Q` | RH |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one eigenform | indep. |
| A99 | the tower as the explicit formula of `Λ(s)/Λ(s+N)`; RH ⇔ regulated energy ≥ minus its jump-tail defect [D] | — |
| B114, B117 | a realization of the partner involution outside the excluded classes; a regulated horizon that is unitary at every cutoff and has ξ as its limit | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling branch), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRP, APD, AAD, TAPO.

Established [L*] unless marked:
- `Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; failure of quasi-RH forces `Θ=Θ∞=1` and AAL.
- RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; a failure of the abscissa law fails exactly one atom; B13 is the emptiness of world I-a and DH of world I-b [D]; finitely many non-real zeros ⇔ a bounded nonreal count of the heat flow as `t↓0` [L*]; landing is a tail law, undecided below every height; a zero at depth `δ` is lost by the exponential current at every speed `a<π/(2δ)`.
- Classical Deuring–Heilbronn for a real zero of a primitive quadratic `L(s,χ)` with a uniform constant; graded repulsion is refuted on integer-norm Euler products with linear counting.
- World I: a top layer with a dominant ordinate makes the corrected current diverge at every `a` with `a(β−σ)>π/2`; a top with one positive ordinate does; AAL, or top zeros supply prime filters with a fixed positive critical modulus at the polynomial observation boundary.
- RH ⇔ attained top ∧ thick bounded lag ⇔ attained top ∧ thick `O(√X)` prime deviation.
- Centred Vaughan currents: for every moment order `r≥1` the Gaussian prime moment minus its pole is the centred current up to `O_r((1+1/η)/t)` on admissible cutoffs; the filtered cofactor reduction error is `O(h^{k}/t)`; truncating cofactors changes the current by exactly the complementary convolution with both continuum terms kept [L*]. At `σ=½`, `X=e^{at}`, moment order `⌊κt/log t⌋`: the unfiltered prime-minus-pole current equals the centred type-II current on cofactors `≤⌈2t^{J+3}⌉` up to `O(e^{−at/4})`, uniformly in the admissible Gaussian sector [K]. Complete unweighted lattice pairs of cofactors `m≥2k` are `≤2/t^b` for every fixed `b`, eventually, uniformly up to polynomial cutoffs in the rotating sector; the lattice pair equals its Gaussian main term up to the relative error `(2048r³Re(ε)t²W²)^r` [S]. The even-mask prime cross form under Gaussian localization is eventually positive, uniformly in the moment order [K].
- Graded recurrence: for `½≤σ≤5/6` and `c>(30/13)(1−σ)`, `T^c` one-separated returns to every small disc at `ρ` at arbitrarily large `T` exclude a zero `ρ` right of `σ`.
- No vertical progression `ρ+ikT` consists of zeros of ξ; `Σ_n|ζ(ρ+inT)/(ρ+inT)|` diverges on each half progression; no sequence of zeros is eventually within an `ℓ²` perturbation of a half progression; the periodicity dichotomy for ζ is RH.

| | Obstacle | Strength |
|---|---|---|
| A47, A68, A86 | constants of the one-quartet world; a landing calibration with ζ's Gamma factor; the transfer of the growing-order reduction through the top-mode filter and the near-diagonal cofactor pairs (unverified) | — |
| A101 | classical Deuring–Heilbronn as a margin on the twisted comb [C] | — |
| B13, B138 | finite stratum; landing for ζ | sub |
| B141 | Deuring–Heilbronn for ζ: `¬AAL ⇒ ZAL` (world I-b empty) | sub |
| B83, B89, B112, B128 | AAL; a bounded aligned return at each right zero; FE into vertical transport; replication | sub |
| B145 | the signed centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; a bound on a sampling set; positive-measure lag recurrence | AAL |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT, every route at all heights. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, SPAL, ALST.

Established:
- No heavy return while `log t≤(log y)^{3/2−ε}` [L*]; every heavy return has `√y≤K(y^{½−w(2t)}log t+log(2+t))`; a strip of depth `h` above some height gives `log t≥c·y^{½−h}` [L].
- Two-prime depth law (Baker); collective return counts beyond the depth floor; rational orbit preservers are Laurent Adams maps [L]; a route from return bounds to ZAL uniform over a class containing `ζ(s−h)` refutes the return conjecture [L*].
- The transfer of candidate S3 implies B56 [D].

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | certified scans; growing resonators (unverified) | — |
| A75 | Lean form of "transfer ⇒ strip self-improvement" [D] | — |
| B46 | proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97, B137 | constant-precision first return past the VK rung; a collective depth floor uniform in `π(y)` | sub |
| B148 | the transfer of candidate S3 | ≥B56 [D] |
| B121 | freezing control beyond the precision cap | sub |

### S10. The diagonal, counts and absolute geometry
Routes: ACS, HF, HAT-C, PM (count branch). Programmes: SOSZ, HAT, AGZ, HTFP, AE, RIAC, HHAC, CTH, LST, KPA.

Established [L*] unless marked:
- Sections: a section vanishing on the graphs of the proper divisors of `m` and not on `Γ_m` pays all those contacts; upward it pays one contact per distinct prime; `p−e_p` vanishes on every `Γ_{p^j}` and has the value `p` on `Γ_1`.
- Selectivity: on a window of ratio `≤2` the comb form is the same for every system of contact weights and the floor `(1/50)Σc_n²` holds for all of them; `combForm {2} c=c²(1−log π)<0`.
- Jets: `½(1/|m−n|+1/(m+n))=Σ_j min^{2j}/max^{2j+1}`; each weight with the diagonal `1/n` is positive semidefinite; the truncations to `J` weights increase to the comb form with remainder `≤(1−1/N)^{2J}` times half the Dirichlet form of the jets.
- One inequality per prime: RH ⇔ a floor on the limits of the comb form on two-bump packets at `log p` on logarithmic windows off exceptions.
- Curves [S]: the comb form on `q^ℤ` is the Toeplitz form of the normalized Frobenius eigenvalues; nonnegative on every finite set ⇔ purity; `2g·e_k²` on one graph; the golden datum violates it. Purity of a curve datum is decided on the window of `#spectrum` points [L*].
- Quadratic rings [S]: contacts `Λ(n)(1+χ(n))` on the comb of norms; counterterm `log(qn²/(2π)²)`; limit `2d₁d₂−Z_ζ−Z_χ`; the twisted part has no pole plane and the counterterm `log(qn/2π)`; the class group does not enter; with the conductor `qe^{−c}`, `c>0`, a packet of degree zero has a positive pairing; the index law holds on the square of the ring; on packets shorter than `log 2` and for conductors `≥4π` (odd) or `≥128π` (even) the twisted part is nonpositive, with the margin `∫f²/5000` on the square of the ring.
- The constant [S]: Bézout with the counterterm `log(n/2π)−c` ⇔ `c≤0` ∧ RH; for every `c>0` a packet with both degrees zero has `Z(g)<c∫g²`.
- Off-diagonal: `Γ_m·Γ_n=Σ_{j≥0}m^{1+2j}n^{−2j}+g·log#(ℤ/J(a,b))`, jets plus contacts; `log#(ℤ/J(1,n))=Λ(n)`; a perfect square keeps no contact; a finite fibre forces contacts that are not Weil's; no Witt Verschiebung carries the off-diagonal; over a Dedekind domain the necklace coordinate at `𝔡` is the ideal `𝔡` and an orbit exists iff `𝔡` is principal.
- Refutation of the invariant glued carrier; the weighted mixed Green kernel descends to the rational torus, symmetric, with stabilizers `±1` and a leafwise Robin diagonal; its critical spherical average is the minimal Green kernel of the all-prime weighted adjacency.
- Pairing of the degree points: limit `2d₁d₂−Z(f)` on packets; twice the contacts tend to the pole and archimedean part minus `Z(f)`; `Z(f)≥−D(f)`, RH ⇔ `D≡0`; margin `∫f²/5000` on packets of width `≤181/250` of any sign; with the weight `−log 2` at `k=2` some packet violates the inequality.
- Hodge index: on every finite family of packets the defect has at most `#{ρ: Re ρ>½}` negative squares; RH ⇔ the intersection form on `H,V` and the packets has exactly one positive square.
- Comb Bézout with weights `w` ⇔ RH ∧ `w=Λ`; `Λ(k)/√k` is the contact number of the diagonal and `Γ_k` on the orbit ring with a base.
- Normal form: the comb pairing at every finite scale; `D·D=Σc_n²V(n)−½Σ_{m≠n}(c_m−c_n)²Γ_m·Γ_n`; on `S⊆(N,N+M]`, `18M≤N`: `D·D≤−(1/40)Σc_n²` and comb form `≥(1/50)Σc_n²`; for every `Q` there is `R` with the comb form `≥0` on real divisors of `(N,QN]`, `N≥R`, with vanishing sums over blocks of `⌊N/R⌋` points; a lower bound `−ηΣc_n²` for the comb form on every real divisor of the window, at arbitrarily large scales, for every ratio and every `η>0`, gives RH; under ¬RH some ratio has at every large scale a real divisor with `Σc_n²≤C` and comb form `≤−ε`.
- Gauge of the flat tail: potential `ρ(n)=N/n−ψ(N/n)+H_N−½(H_{N−n}+H_{N+n})+3/(4n)−log 2π`; `Σ_{n≤N}ψ(N/n)=log N!`; the form of the flat tail per degree point tends to `2+γ−log 4π`; for weights differing from `Λ` at finitely many integers the limit is lowered by `2Σ(w(k)−Λ(k))/k`, and doubling the contact at 2 makes the flat tail violate the inequality.
- Diagonal: the comb's own density is the counterterm; the ambient point counterterm on the multiples of `g` shifts the limit by `−log g·∫f²`; on the comb of squares the counterterm is `log(n/4π)`, the density `n/2` over `2π`, and the packets on the squares carry minus the archimedean form without the pole of the rescaled packet `s↦g(s/2)`, with no prime contacts. A uniformly separated set of positive reals stable under every multiplication `x↦kx` lies in one orbit `δℕ`, and is that orbit if it contains `δ`.
- One ring: the real algebra generated by the orbit ring with a base, `χ_1` and `τ` is stable under every shift, contains the tower of lines, the pole plane and the jets, with exact counts on every weight line. Pointwise, the shifts of the point count span every finite set of degrees; tested against packets at a scale the contacts have the weights `±½`, the jets and `ρ−½`.
- Tower: a nonzero section vanishing on `Γ_1,…,Γ_K` exists once `Π_{n≤K}(⌊2B_n/n⌋+1)<(A+1)^{bτ(M)}`; its first nonvanishing graph has `n>K` and `n≤|x_n|`.
- Carries: the carry defect plus the window-count defect plus `½log N` tends to `−½log π`; the digit carry and the Witt carry are cocycles that are not coboundaries.
- Gluing: index `N!`; `|log N!−N(2πN)|≤C log N`; `G(T)−N(T)+S(T)→½log 2π−7/8`; `G(T)−N(T)` leaves every bounded neighbourhood of that constant.
- Clock: `E_r↑W` with Sobolev error; capacity `∼4√N`; horizon sharp at `κ=4` [L].

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests at verified scales | — |
| A54 | cusp expansion for Bianchi resolvents | — |
| A80, A81, A94 | the converse at finite scale (RH ⇒ the comb form is nonnegative on every real divisor of `(N,QN]` for large `N`); the constants; the index at finite scale as the window index (unverified) | — |
| A82, A91 | the Li ladder as comb forms of tails; the Hodge index on the square of a number ring of higher degree (unverified) | — |
| A96, A97, A98, A100 | the first selective window; the multipole form of the jets; RH ⇔ feasible weights at every aperture; the trivial aperture of a conductor [D] | — |
| B87 | a count on the rays `Γ_1+Γ_p`, defined without `Q` | RH |
| B88 | the sign of the Gram defect / of the comb finite part | RH |
| B149 | Bézout for the comb pairing on effective classes, from a property of the object | RH (producer) |
| B152 | the comb form on a full window: nonzero block sums and their cross terms, at every ratio | RH |
| B154 | the exceptional square: the sign of the twisted part of the square of a quadratic ring at aperture `log log q+C` | Landau–Siegel |

### S11. Families, rigidity and exactness
Routes: ACS (tensor branch), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established [L*] unless marked: fixed-part laws for the gauge torus, Dirichlet characters, the vertical line, Weyl cuspidal eigenforms and number fields under a counting measure; RH ⇔ sublinear tensor exponents of a cover family with the trace of ζ retained; local residue classification and isozeric continuation [L]; for every analytic profile `Φ` unimodular on `[0,1]` with `Φ(0)=1`, `Φ(1)=−1`: multiplicities of ζ kept on `Re s>max(½,1−mt)`, no joint analytic regularization at `(0,1)`, a zero-free non-polynomial scaling limit `ζ(2)exp(−Σc_{n+1}log(w+n+1))`, and entire scaling forces `Re Φ′(1)≤−2`; the `χ₄`-selected pair of profiles has a zero of order four at `1−2t`, a double pole at `1−4t` and the scaling limit `ζ(2)(w+2)⁴/(w+4)²`; every finite residue-class mixture has the scaling profile of its principal average and admits no joint holomorphic endpoint germ [S]; Frobenius at one prime; cost `m·Σ_{p∈S}log p`; `ℤ` has no ring endomorphism but the identity; the Teichmüller element `[p]` has vanishing positive jets and value `p` [L]; no finitely generated lattice stable under three prime Frobenii [L]; coefficient gaps do not occur at three explicit critical ordinates [L]. Carlitz–Goss: `p^s−1∣N` ⇔ the digit-content vector of `N` is `Ea` with `a≥1` integral; a digit collection splits into `k` divisible parts and one further part ⇔ every coordinate of `E⁻¹u` exceeds `k`; the criterion holds for the actual base-`p` digits of every `N`; optimality and greediness survive the deletion of digits from the last part; the highest digit block carries more than half the value [S].

| | Obstacle | Strength |
|---|---|---|
| A84 | optimality of the greedy carry-free composition and the Newton polygon of the Carlitz–Goss zeta [C] | — |
| B86 | positivity of the endpoint character at unbounded rank, mixed Young shapes | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

## 3. Live routes

Receiver statements are `[L*]` unless marked.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or a one-sided integer lag, or an attained top with an `O(√X)` prime deviation on a thick set of scales → RH.
- **Established:** RH ⇔ the integer lags at the primes are bounded below; RH ⇔ attained top ∧ thick bounded lag ⇔ attained top ∧ thick `O(√X)` prime deviation; a lag bounded on a thick set leaves RH or an unattained top; RH ⇔ the central trace of the zeros with weights `1/(ρ(1−ρ))` is positive definite on `ℝ` [D]; gauge exponents `[Θ,1]` [L/K].
- **(a)** A30, A90.
- **(b)** bounded endpoint energy (B49); deciding input (B48); attainment of the top together with the thick estimate (B110, ZAL or attainment); past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** RH ⇔ `Ψ` locally bounded on precontact intervals; block S2; verified-height rung.
- **(a)** A1–A3, A16, A79.
- **(b)** B1, B2, B4, B18.

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established:** RH ⇔ `A(M)/M≤C_εM^ε` for every `ε>0` ⇔ `−C_εM^ε≤A(M)/M` for every `ε>0`, `A` the Möbius-divisor square-root Abel moment; samples at powers `j^m` suffice [L].
- **(a)** none. **(b)** complete-history cross-clock bound (B42).

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on a tail → RH.
- **Established:** RH ⇒ the source is eventually bounded below; ¬RH ⇒ it is unbounded below on every tail.
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH.
- **Established:** RH ⇔ floor `−B(K+2)`; sublinear floors impossible [L].
- **(a)** none. **(b)** high-LCM pairs, moving core and singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma response sign → RH.
- **Established:** calibrated Hausdorff-row sign above an explicit radius; the remaining entries ⇔ RH [L].
- **(a)** A1. **(b)** signs below the explicit shift (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** `Σ_{m,n≤N}μ(m)μ(n)/(m+n)=O_ε(N^ε)` ⇔ RH, and the form is unbounded; residue energies bounded or equidistributed [L]; orientation-cover weight `½` ⇔ RH; in world I `M(x)=O(x^β)`.
- **(a)** A21, A33, A46.
- **(b)** B48, B50, B15; cubic theta identification (B94); bounded-index correspondence (B106).

### SQF — Weighted squarefree count
- **Path:** `e(t)=Σμ(n)²e^{−nt}−6/(π²t)`; a one-sided `O(t^{−¼−ε})` bound on `(0,1]` → RH.
- **Established:** RH ⇔ the upper law ⇔ the lower law; a one-sided bound `t^{−α}` gives a zero-free band; `Ω±(t^{−¼})` [L].
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH.
- **Established:** RH ⇔ for every `0<t<½` a bound `C_t` for `D_t(N)+Q_t(N)/2`; VK saving of the residual [L].
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇐ infinitely many Jensen degrees real-rooted [L]; the finite-stratum law on shifted Jensen polynomials gives RH; block S4.
- **(a)** A20, A1.
- **(b)** outer roots (B22); bounded `N_d` gives finite support only (B23, then B13, B138); heat budgets (B124).

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** RH ⇔ every positive-time zero simple; blocks S3, S4, S8; ordinate injectivity ⇔ RH; centred Vaughan reductions at every moment order.
- **(a)** A19, A47, A68, A86.
- **(b)** B24, B25, B47, B27, B124; B130; B83 through transport or a contradiction in world I (B89, B112, B128, B145); B13, B138, B141.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established:** RH ⇔ every formation rectangle has an anchor with trace norm `<1`; RH ⇔ `Σ Λ(n)n^{−1/2}e^{−yn²}−∫₁^∞u^{−1/2}e^{−yu²}du≤−1/10+32√y` for `0<y≤1`.
- **(a)** none. **(b)** trace norm below one on every rectangle, or the Gaussian inequality (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; cofinal source-work `≤2` ⇔ RH [L]; ground-state dichotomy and three-way classification; RH ⇔ one positive square of the intersection form on packets [L*].
- **(a)** A9, A13, A80, A100.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152; B154 on the twisted part.

### HAT-C — Arithmetic-clock Green energy
- **Path:** prime capacities fill one clock → `E_r(f)↑W(f)` → `W≥0` on packets ⇔ RH.
- **Established:** `0≤W−E_r≤(1−r²)‖f′‖²/2` uniformly on a support window; the finite-limit domain is the closed Weil form domain; coercively shifted damped inverses converge strongly to the restricted Weil covariance; the scattering tower of height `N` with its exact jump kernel and the second-height defect `½∫|u′|²` [K]/[L].
- **(a)** A99.
- **(b)** the unshifted `E_r(f)≥−ε` arbitrarily near `r=1`, or the raw scattering energy `≥−ε` at arbitrarily large integer heights; this is `W(f)≥0` (B1) [D].

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH.
- **Established:** RH ⇔ the prime wave is bounded; a primitive bound state above `½` gives an odd one.
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** signed jet cone ⇔ RH; rank 14 at `0<a≤½`; the adaptive partial sum is `ζ(½+ib)` up to `O(|b|^{−½})` [L].
- **(a)** A4, A5, A24, A42.
- **(b)** signed adaptive head near critical zeros (B102); amplitude oscillation (B20); all ranks (B21).

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH.
- **Established:** ¬RH ⇔ some theta ground profile has prime energy below its Gamma/polar energy.
- **(a)** none. **(b)** joint-node exclusion or the comparison (B36).

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ cofinal polynomial boundedness; strict slope saving ⇒ RH; block S5 [L].
- **(a)** A18.
- **(b)** B62, B57–B61, B63.

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** a curve datum is unitary ⇔ its Cayley ladders are NSD on primitive vectors; RH ⇒ the Cayley ladder of ξ is Lorentzian; RH ⇔ the ladder sign [L]; `λ_n≥0` for `n≤314`; the comb form of the flat tail per degree point tends to `2+γ−log 4π`, twice the first Li coefficient [L*]/[D].
- **(a)** A1, A82. **(b)** the lower bound or the sign (B43).

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH.
- **Established:** ¬RH ⇒ the defect is not eventually bounded below for any nonnegative source energy; `|A_N|≤C√N e^{−c·vkScale N}` [L].
- **(a)** none. **(b)** bounded completed residual (B37, B1).

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity-energy rate, or a count → RH.
- **Established:** block S7.
- **(a)** A26.
- **(b)** B68, B71, B87; B147; B114, B117.

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ every real zero of `A_h`, `0<h<½`, is simple; under RH every `A_h` is Laguerre–Pólya [L].
- **(a)** none. **(b)** the sign below the VK boundary (B29); a prime-faithful lossless stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on finite power windows of square shells → RH.
- **Established:** RH ⇔ `‖jasShellRieszSum(m²,k)‖≤m^{εk}` on `m<k≤m+m/log(m+1)` for infinitely many `m`, every `ε`.
- **(a)** none. **(b)** the control (B51); the shell alternative needs ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass → RH.
- **Established:** RH ⇔ unit-bounded chronological rows reach every tolerance; RH ⇔ the BSY integral vanishes.
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH.
- **Established:** the residual criterion ⇔ nonnegativity on the grids of `log 2` and `log 3` at arbitrary offsets; RH ⇒ every grid is nonnegative.
- **(a)** A1. **(b)** nonnegativity at every degree (B30).

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH.
- **Established:** RH ⇔ every zero lies in a disc centred on the line with nonnegative margin.
- **(a)** none. **(b)** the cover (B32).

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence on a disc ⇔ head-target heights of density uniform in the head length; uniform density on every right-strip disc ⇒ RH; block S9; in world I heavy returns are later than `exp(c·y^{1−β′})`; graded recurrence; no half progression of zeros.
- **(a)** A37, A47.
- **(b)** uniform target mass (B72); transport (B83, B89); breadth past VK (B97, B137); B145.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH.
- **Established:** RH ⇔ the blind minimum is nonnegative at every aperture; a minimizer exists at every aperture; `≥1/20` on the first window [L].
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH.
- **Established:** RH ⇒ the charge is eventually below every `ε`; a non-real zero keeps it above a positive constant.
- **(a)** none. **(b)** charge below `ε` at arbitrarily late stages (B33).

### OWU — Odd sector
- **Path:** archimedean-minus-prime positivity on odd tests → RH.
- **Established:** RH ⇔ the pole-free functional is nonnegative on odd real `C²_c` tests.
- **(a)** A1–A3, A6. **(b)** B4, B17, B44.

### PBM — Regularized abscissa
- **Path:** convergence of the pole-regularized series right of `½` → RH.
- **Established:** width `≤α` ⇔ convergence right of `½+α`, for the prime and the log-ζ coefficients.
- **(a)** none. **(b)** the partial-sum bound (B53).

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH.
- **Established:** RH ⇔ Robin's inequality at `lcm(1,…,n)` for all large `n`.
- **(a)** none. **(b)** the inequality (B54).

### SRT — Lag localization
- **Path:** the prime two-bump sign on a decisive sample → RH.
- **Established:** RH ⇔ Weil positivity of every prime two-bump, even or odd ⇔ these values bounded below; RH ⇔ a lower bound on the two-prime difference lags of arbitrarily late `√T` windows; block S3.
- **(a)** A9, A72, A73, A56, A92, A95.
- **(b)** B130; B151; B6, B101.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH.
- **Established:** RH ⇔ the remainder dominates the defect for every even `C²_c` profile at any single shift `a>0`.
- **(a)** A7. **(b)** one shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** global incidence allocation → RH.
- **Established:** exact allocation and an explicit ledger floor for the full zero form on odd tests [L*]; RH ⇔ the allocation condition [L].
- **(a)** A9, A13. **(b)** signed cost `C_σe^{2σr}` (B45); polar payment (B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling on one two-prime cone → RH.
- **Established:** RH ⇔ bounded damped cone coupling for any two primes; under AAL the finite-stratum receivers collapse to RH [L].
- **(a)** none. **(b)** the coupling bound; sublinear tensor loss (B39); ZAL for the undamped branch.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** degree-point pairing → `D·D≤2d₁d₂` on every packet → Weil positivity → RH; or `P(p)≤A(p)+K` on logarithmic windows off power-thin exceptions.
- **Established:** the packet deficit `2d₁d₂−D·D` tends to the zero sum; the all-packet bound for weights `w` ⇔ RH ∧ `w=Λ`; margins on packets of width `≤181/250`; RH ⇔ exactly one positive square on the pole plane and every finite packet family, with the index law; the comb form at finite scale is coercive on windows of ratio `≤19/18` for every weight system and nonnegative off fewer than `2QR(Q)` block sums on windows of ratio `≤Q`, and its lower bound `−ηΣc_n²` at arbitrarily large scales gives RH; one inequality per prime on two-bump comb packets; the potential in the gauge of the flat tail is the remainder `N/n−ψ(N/n)` of the prime number theorem; unit comb masses determine `Λ`; the constant `2π` is forced [S]; sections pay one contact per prime above; the combs of a curve and of a quadratic ring [S]; blocks S3, S10.
- **(a)** A28, A41, A48, A59, A72, A80, A81, A82, A94, A96, A97, A98, A100.
- **(b)** B152, B149, B88, B87; B130; B28; B154 on the twisted part.

### ECP — Endpoint character positivity
- **Path:** endpoint jets → coherent symmetric-group class functions → PSD character Grams at every rank ⇔ RH.
- **Established:** the arithmetic character is PSD on every finite family of permutations ⇔ RH; column projections nonnegative; Toeplitz minors through order 200; four mixed shapes [L].
- **(a)** none. **(b)** positivity at arbitrary rank (B86).

## 4. Candidates

Each needs its source-to-receiver step first (B81).

| Candidate | Established | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| S3 | weighted return bounds [L]; floor on logarithmic windows off exceptions ⇔ RH [L*]; two-prime windows are a receiver, not the transfer | A75 | the transfer has at least the strength of B56 [D] (B148) |
| SEC | Fock boundedness at every divisor point ⇔ `Re s=½` [L] | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` [L] | none | arithmetic descent on actual zero fibres |
| APF | prime/grade trace reconstruction on real labels [L] | none | full-divisor exhaustion and RH landing |
| EGC | zero-pair contour; count error `≤32ε²log T/T` [L] | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on the blind plane [L] | none | faithful endpoint admission |
| FEL | KL accounting [L] | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution [L] | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport [L] | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion [L] | none | RH-sufficient orientation law |
| W1C | real-rooted or Laguerre–Pólya approximants on one interval give RH [L]; index-one limits give RH [L*]; a ferromagnetic chain on the Γ sites is real-rooted and has the Riemann–Siegel cosine sum with frozen phase as its first-order wall expansion [L*] | none | an independent index-one family (B146); no Dirichlet polynomial is an exact factor [L*]; stable polynomials in the prime fields have linear zero counts [L]; bounded series with zeros on the line are open (B153) |
| WBF | Gram recovers magnitudes and phase class [L] | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| SOSZ ScaleLocality | `√T`, log-square and logarithmic windows; exceptional sets; signed deletion; separated windows; other side on windows; two-prime windows [L*]; sub-logarithmic and bounded windows miss the class `𝒵` [L*] | A72, A73, A76, A78, A83, A89, A92, A95 | B130, B151, B144 |
| HTFP (Hodge theory of a fixed part) | normal form of the pairing; Zariski's lemma on a comb; coercivity on short windows at every scale; finite index at every scale; gauge of the flat tail; the comb of unit masses fixes the contacts; a separated comb is one orbit of the Frobenius monoid; Riemann–Roch on the tower with the gluing index; what the sections certify; the inequality at finite scale decides the limit; one inequality per prime on the comb; short windows do not see the contacts; the jets as Hardy squares; the index of the pairing ≤ the defect of a splitting [L*]; the comb of a curve [S] | A80, A81, A82, A94, A96, A97 | B152, B149 |
| AGZ | ghost ring, cofreeness, contacts, carries, gluing index, comb finite parts, archimedean fibre, tower of lines, one ring of sequences, the pairing as a weighing of the zeros, the sign carried by the contacts, the density as counterterm, carry cocycle, Dedekind squares, Hodge index on packets, contacts at a height, packets on the comb of squares [L*]; the square of a quadratic ring with its conductor; Bézout determines the constant of the counterterm; the Hodge index of the square of a quadratic ring [S] | A91, A100 | B149, B88, B154 |
| ELT | atoms and landing forms; Deuring–Heilbronn calibration; filters at every speed; polynomial observation boundary; centred Vaughan currents at every moment order; cofactor localization; top-ordinate dichotomy [L*]; growing moment order at exponential scales with cofactor localization; the Gaussian prime cross form [K]; separated cofactor pairs; lattice correlation bounds [S] | A47, A68, A86 | B141, B145, B138, B13 |
| ZCG AbscissaLaws, Recurrence | split, atoms, sectors, quasi-RH as a tail law, heat-, cosine- and Jensen-family laws, graded recurrence [L*] | none | B13, B83, B138 |
| IRP | index law; semicontinuity; Eisenstein line law and its blindness; exceptional parameter at `4πe^{−γ}`; Kronecker at infinite rank; attained top on thick sets; no class or half class of one Frobenius among the zeros; a factor with a Dirichlet series is pure; no Dirichlet polynomial is a factor; the constant terms on the two sides of the line agree, also with finitely many poles on the line; inverse expansions of zero-free exponential polynomials; Castelnuovo–Severi on the flow [L*] | A90 | B146, B153 |
| AWT | fixed-part laws; cover-family tensor criterion; gauge deformations; analytic smoothings and their scaling limits; edge divisors; Künneth; character prime logarithms; arithmetic phase mixtures [L*]; residue-class mixtures: principal-average scaling, no joint endpoint germ [S] | none | B86 |
| SignFreePurityMechanisms | height separation ⇔ bounded prime traces; Frobenius at one prime; `m·θ(S)`; primorial; Newton polygons; coefficient gaps; Carlitz–Goss digit contents and content partitions [L*]; content bounds, last-block operations, top digits [S] | A84 | — |
| HAT | adelic Green formula; full degree carrier; weighted Green covariance; torus descent, Robin diagonal, critical spherical average; refutation of the glued carrier; arithmetic clock; Green damping detects the Weil form domain and resolves the Weil operator [L*]; the finite scattering tower with its exact jump kernel; the tower detects the Weil form domain; the second height jet is Dirichlet energy [K]; sharp spectral edges of the prime walk and of the weighted adelic adjacency [S] | A54, A99 | B88, B117 |
| AHMH / BHR / ASH / CTH | cavity receivers, reflection Krein forms, halving descent, ringdown, count door, sharp shells [L*] | A26, A41 | B68, B71, B87, B147 |
| TTPO / CDGeo / PTT / TAPO | depth law, VK breadth, strip breadth, collective counts, label statements [L*]/[L] | A24, A37, A75 | B97, B137, B148 |
| ALST / AAD / RAC | Stepanov degrees; orbit rigidity; producer rates; Heilbronn sums by Stepanov on the truncated logarithm [L*] | A30 | B48, B55, B67 |
| AHD / CACT | threshold identities, hierarchy, pole channel, ground states, classification [L*] | A9, A13 | B104, B123 |
| Census (IGP, P) | density `0.67250071`, covariance ceiling, alternatives, exchange rate, deep zeros `o(V)` [L*]/[L] | none | B150, B57 |
| VHR / TCS | verified-height rungs; height 67 [L*] | A1–A5 | — |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: `P(p)≤A(p)+K` on the primes of logarithmic windows off power-thin exceptions; resolution logarithmic in `𝒵`; slack `p^{o(1)}` | ACS, SRT, WL, HF, ZCG, HAT-C, and every window route through the prime two-bumps |
| Σ sign on every window (`a*(ζ)=⊤`), equivalently verification at every height, equivalently one positive square of the comb pairing at every ratio | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ continuation at small time and the theta head at the critical zeros | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and count | PM, ECP |
| The exceptional coordinate: world I (B13, Landing, DH sectors) and world II (ZAL) | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range | every route at all heights; BAG; TH certificates; WD near-unit moments; the centred type-II current of ELT |
| Missing source landing | the twelve candidates |
| The exceptional square on the conductor ladder (B154) | the twisted part of every sign route: ACS, HF, HAT-C, PM, SRT |
