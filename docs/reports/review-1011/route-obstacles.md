# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `68b0e1200f` with its working tree (2026-11-10). Working log: `logs/review-1011-statusquo-research.md`. Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. Formulations are not independent mechanisms: HJ is PA; the BSY criterion of FEL belongs to CTF; SEC and CDC/BSH are candidates; PCS is a retired label. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.**
- `[L*]` Lean statement read for this report, in source or through the corpus search tool.
- `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/` returned by the corpus search tool; statement not re-read here.
- `[S]` Lean source present in the working tree, not committed at the checkpoint; statement read. `[K]` Lean with transitive axiom audit, as recorded.
- `[D]` deduction made in this report from `[L*]` statements; not a Lean theorem. `[C]` classical literature, not in the corpus. `[A]` assessment.

**Strength.** RH; ≥qRH (a zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); sub (below quasi-RH and below AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md). `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1 ⇒ Θ=½`. `B` the cubic spline, `S` its lag structure, `c_B(u)=Re S(u)`, `c_p=c_B(log p)`; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`, in the original variable `[x(log x)^{−32}, x(log x)^{32}]`. **World I**: ¬AAL, a finite isolated top layer at `β<1` over a remainder. **World II**: AAL ∧ ¬ZAL, `Θ=Θ∞>½`. `W` Weil's form; `a*(ζ)` onset aperture; `Ψ=½log H₁`; `R=c⁸/log N`; `R_c`, `R_polar`, `R_halfline` whole-space, polar-payment and half-line thresholds; `W₀=⨅_A windowThreshold(A)`. `E_r` the arithmetic-clock Green energy. `𝒢=W(ℤ)` the arithmetic square in ghost coordinates, `Γ_n` its graphs. A **heavy return** is a `δ`-return (`δ≤1/20`) at height `t` of a subset of the primes `≤y` omitting at most `1/1000` of the `p^{−1/2}`-mass.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `∃K`: `2c_p≥−K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ Weil positivity of `B+τ_{log p}B` at every prime | [L*] | Σ (Weil's sign), Π (a prime count) and the count door are one inequality per prime |
| RH ⇔ the same on the primes of arbitrarily late logarithmic windows; the absolute form `\|2c_p\|≤K` is equivalent; the exponent `p^α` reads the width exactly | [L*] | the minimal face is local in scale at radius `32 log(T+2)` |
| RH ⇔ the bound on those windows outside a finite set of at most `Ce^{δT}` primes per window, any fixed `δ<1`, chosen freely per window; if RH fails every late window keeps a violator outside every such set | [L*] | the face tolerates power-thin exceptions; violators are either absent or of size `x^{1−o(1)}` in every late window [D] |
| No fixed window length decides every tempered configuration; with `δ`-separated deep ordinates windows of length `80/δ+1` decide, from either side, also in count form | [L*] | the residual resolution question is the radius between "unbounded" and `32 log T` (B143) |
| `Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; `Θ<1 ∨ AAL` | [L*] | a failure of RH lies in world I or world II; world I has a zero-free strip for free [D] |
| World I: `M(x)=O(x^β)`, `β<1`; heavy returns need `log t≥c·y^{1−β′}` with `β′<Θ`; prime-only filters read each top residue at every damping speed and every contraction rate below `a(β−σ)/2`; the Vinogradov–Korobov bound decays only above `a(1−σ)/2` | [L*] | the finite-layer receiver is complete; the gap `a(1−β)/2` is the exclusion itself [D] |
| RH ⇔ ZAL ∧ B13 ∧ Landing; no two of B13, Landing, DH fail together; landing has equivalent forms (Hadamard threshold, Krein–Langer index, heat counts, …); FE-only and Euler-only models violate it | [L*] | three atoms on the RH path; each needs the FE and the Euler product jointly |
| The zero motive of ζ is the fixed part of every arithmetic family: moments bound the atom at the trivial fibre only by the trivial bound; product positivity couples one way; with the trace of ζ retained, sublinear tensor growth is RH | [L*] | Deligne's family step has no producer over ℤ |
| Pole-preserving gauge deformations of ζ are isozeric; a Dirichlet series with ζ's FE is a multiple of ζ; Beurling systems with `L¹`/`L²` FE defect are the rational primes | [L*]/[L] | ζ has no moduli; no fake keeps both structures [D] |
| `x↦xⁿ` is a Frobenius at one prime only; order `m` of the `p`-derivations at every prime of `S` costs `m·θ(S)`; simultaneous inseparability costs the primorial | [L*] | Stepanov's inequality over ℤ is the product formula: no slack |
| The arithmetic square `𝒢=W(ℤ)` carries the prime part of every off-diagonal intersection number as contacts; the conormal classes of its diagonal are torsion; no object of finite type carries the contacts; a section count with Riemann–Roch and Bézout exists iff the Hodge index holds | [L*] | the count door and the sign door need the same missing object |
| Every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal and drifts to `−∞` against Weil's off-diagonal | [L*] | Weil's diagonal is not one glued carrier object |
| Weil's archimedean form is the finite part of the jets on invariant combs; the counterterm `log(density/2π)` belongs to the comb, not to the degree point | [L*] | the diagonal is a comb-dependent finite part, not a self-intersection number |
| `E_r(f)≤W(f)`, `0≤W−E_r≤(1−r²)‖f′‖²/2` once the clock covers the capacity of the support | [L*] | the clock is an ordered approximation of Weil's form; its sign is Weil's sign [D] |
| RH ⇔ ξ is a locally uniform limit of conjugation-real entire functions with at most one right-half zero each; the Eisenstein constant term is pure off the real axis for every `Y≥1`; the same line law holds over impure fixed parts | [L*] | the index is semicontinuous; a family does not prove the purity of its fixed part |
| RH ⇔ the ordinate is injective on the zeros ⇔ `\|c_p\|≤K` at every prime | [L*] | separation by the height is a receiver |
| One cuspidal cavity function of Hecke forms: RH ⇔ energy rate `y^{¾−ε}`; one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero | [L*] | the horizon has complete and sharp receivers; the halving condition is void |
| Unconditional savings: Vinogradov–Korobov pointwise; Guth–Maynard density `30/13`; Matomäki–Radziwiłł for μ at every length; simple critical zeros `≥0.67250071` | [L*]/[L] | everything past VK is in law [D] |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | format exact on every window; a window at aperture `a` follows from verification to `windowHeight(a)` |
| M2 Calibration | window cones, blind positivity, margin | cone pinned to Λ; sign open |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies, standard forms | complete and sharp receivers; rates and signs open |
| M5 Square-root cancellation | smoothed prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH; purity thresholds are the width |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros at rate 2; clusters and depth density `o(T)` open |
| M8 Finite-layer receiver | damping filters, boundary rotation, polynomial damping, centred Vaughan current | complete in world I; arithmetic bound in the growth range is the exclusion |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level; exact count = Chebyshev; cost `m·θ(S)` |
| M10 Count | nonnegative count with quadratic Tate limit | every hyperelliptic curve; over ℤ one ray per prime of sparse windows; no count known |
| M11 Orbit at finite time | prime phases, returns, linear forms in logarithms | depth by Baker; breadth to VK; in a strip to `exp(c·y^{1−Θ∞})` |
| M12 Critical compactness | thresholds, pole channel, half-line ground states | `R_c=R_polar=R_halfline≤W₀`; three-way classification |
| M13 Topology of the prime complex | nerve, persistence, orientation cover | centred count `M(N)`; weight `½` ⇔ RH |
| M14 Infinite-rank elimination | towers, thick sets, Turán, resolvent of a tower | elimination proved; with an attained top a thick crude count is RH |
| M15 Prime-degree sampling | bounds at decisive samples, logarithmic windows, exceptional sets | RH from one side or sign-free; estimate open |
| M16 Intersection on half-products | zonotope, torsion on `ℙ¹_ℤ`, `ℍ³` and tree fibres, adelic carrier | off-diagonal Green formula; invariant glued diagonal refuted |
| M17 Absolute geometry | Λ-square, contacts, carries, tower of lines, archimedean fibre | square is a curve; no finite-type carrier of the contacts |
| M18 FE rigidity | Hamburger, defect isolation, Gaussian surgery, gauge deformations | identifies ζ; moves no zero |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing; all open for ζ |
| M20 Families and monodromy | gauge torus, vertical family, covers | fixed-part theorem: no producer |
| M21 Index and limits | index law, Hermite–Biehler defect, index-one limits | RH ⇔ limit of index-one objects; no independent family |
| M22 Separation | ordinate injectivity, Newton polygons, coefficient gaps | receiver; separation by absolute value excluded for ζ |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators, positive translation repair | amplify or reshape a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- `R_c=R_c^{PSD}=R_polar=R_halfline` [L*]; `R_polar=W₀` ⇔ half-line polar positivity at every `R<W₀` [L*]; pole-orthogonal positivity below `W₀` [L*].
- RH, or a finite `W₀>0` with a unit critical half-line ground state [L*]; three-way classification: RH, or ¬RH with `R_polar<W₀`, or ¬RH with `R_polar=W₀` and every ground state polar-orthogonal [L*].
- Full tilted-spline matrix PD below exponent `1/8` and at one critical multiple; charged compactness; no universal holomorphic multiplier dominates the depleted kernel [L].

| | Obstacle | Strength |
|---|---|---|
| A9 | explicit constants of the eighth-root horizon and the Beurling schedule | — |
| A13 | near-gcd charges and periods beyond the admissible scale (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; low-packet payment at every ratio | RH |
| B104 | whether a critical half-line ground state at finite `W₀` can be polar-orthogonal; polar payment at every `R<W₀` | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow and the aperture–height exchange
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL.

Established:
- RH ⇔ `W≥0` on every window [L*]; RH ⇔ `Ψ` bounded on every bounded precontact interval ⇔ `L=artanh r` bounded there; off RH the angle is unbounded above every base [L*].
- `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]` [L*]; RH is verified through height 67 [L*].
- Window positivity at aperture `a` forces near-line zeros up to height `≈2πe^{a}`; model configurations hide an off-line zero at height `T` up to aperture `(log T)/36` [L].
- Floors `(1/20000)/2^k` through `a_k<0.3621`; cone pinning; `{2,3,4}` band below `log 5`; finite templates exactly below spread `27/5` [L].

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A79 | matching constants in the aperture–height exchange: the necessary height (scale `e^{a}`) against the sufficient `windowHeight(a)` (unverified) | — |
| B1, B2, B4, B5 | sign on every window; bounded oscillation of `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo.

Established [L*]:
- RH ⇔ lower bound at every prime ⇔ on the primes of arbitrarily late logarithmic windows ⇔ the same off `Ce^{δT}` primes per window (`δ<1`); width form at exponent `p^σ`; Stepanov form `P(p)≤A(p)+Kp^σ`; absolute form; signed-deletion proof of the absolute form on log-square windows.
- `√T` windows decide every tempered configuration; no fixed length decides every configuration (off-line pair of ordinate `δ/2`); under `δ`-separation of the deep ordinates length `80/δ+1` decides from below and from above.
- Bohr-dense sets (sets with arbitrarily long intervals) put an attained top on the line, from either side.
- Exceptions `O(X^α)`, `α<1`, keep the criterion; density-zero exceptions need ZAL.
- Two primes suffice on `√T` windows: for distinct primes `p,q` and every `r>0`, RH ⇔ the lag correlation is bounded below on the difference lags of the monoid of `p,q` inside `|ℓ−T|≤r√T` for arbitrarily late `T`.

| | Obstacle | Strength |
|---|---|---|
| A72 | count door on logarithmic windows with exceptional sets [D] | — |
| A73, A76 | one-sided upper side on logarithmic windows; exceptional sets in the absolute and signed criteria (unverified) | — |
| A78 | cluster form of the separated-window theorem (unverified) | — |
| A58, A59 | effective gap iteration; residue-class primes [C] | — |
| B130 | the bound itself on any decisive sample | RH (≥qRH at `p^σ`, `σ<½`) |
| B143 | decisive radius of ζ's class below `32 log T` | method |
| B144 | separation of the off-line ordinates of ζ | sub |

### S4. Continuation, nodal geometry and index
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Programmes: NGF, FFP, ADO, AES, IRP.

Established:
- RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*]; each `H_t` has finitely many non-real zeros [L*]; heat finiteness does not pass to `t=0` [L*]; linear AAL along the heat flow is RH [L*].
- RH ⇔ infinitely many Jensen polynomials of Ξ real-rooted [L*]; `N_d≤300√(d log d)`, `sup_d N_d` = off-line multiplicity [L]; `RHVerifiedThrough T` gives real-rooted degrees `d` with `2·10⁷d⁴≤T log T` [L*].
- Zeros of `H_t`, `0<t≤⅛`, with `|Re z|≥2π·exp(40/t)` are real [L*].
- Finite-stratum laws: at each degree only finitely many shifted Jensen polynomials fail real-rootedness, and a law that excludes finite nonempty exceptional strata gives RH; the same law on the cosine family gives RH ⇔ ZAL, the finiteness of the cosine defects being the tail condition [L*].
- Index law: a Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points; the index bound passes to locally uniform limits; RH ⇔ ξ is a limit of index-one objects; zeros of `ξ(s+½)∓ξ(s−½)` lie on the line [L*].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon at the exponent `(3/2+ε)/t` with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B24, B25 | collisions at small time, all heights; frequency below one | RH |
| B22, B23 | outer roots of `R_d(Ξ)`; `N_d` bounded | RH; ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |

### S5. Near-line geometry, long moments and the census
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation.

Established:
- RH ⇔ cofinal polynomial boundedness of long Möbius-mollified second moments; a strict slope saving gives RH [L*]. BSY: RH ⇔ `∫log|ζ(½+it)|dt/(¼+t²)=0` [L*].
- Census: critical-line density `≥0.67250071` [L*]; ceiling `4π(1−a)` of the source covariance ⇔ density `≥a` [L*]; for every `θ`, `N₀≥θN` or at least `(1+HD(1)−2θ−1/A−ε)N` simple off-line zeros within `A/log T` [L*]; `7/10≤certOpt(B)` ⇔ `B≤4` [L*].
- Matomäki–Radziwiłł for μ at every length `h→∞`, `h≤√x`, in fibre form [L*]; Guth–Maynard density exponent `≤(30/13)(1−σ)` [L*].
- Necessary mollifier length `exp(c log²T)`; long mean values are collision counts of order `X²` [L].

| | Obstacle | Strength |
|---|---|---|
| A18, A21 | twisted moments past `21/50` [C]; census items | — |
| B57 | depth density `o(T)` (all but `o(N)` zeros within `o(1/log T)` of the line) | sub |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | bounded form factor `F≤4` on `(1,10/9)` (70%) | sub |

### S6. Production, precision and the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC.

Established:
- Rates `K^{−a}` for all `a<½` give RH [L*]; RH ⇔ `log N(A_N)≤N+C√N log²N` for the fixed-point auxiliary [L*]; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [L*]; RH ⇔ pole-regularized prime series converges right of `½` [L*].
- Orientation cover over ℤ: weight `½` ⇔ RH [L*]; in world I `M(x)=O(x^β)`, `β<1` [L*].
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
Routes: PM; W1C (candidate). Programmes: RIT, BHR, ASH, AHMH, CTH, IRP.

Established:
- RH ⇔ every compact pulse rings down at `e^{−(¼−ε)τ}` [L*]; RH ⇔ every tent reflection Krein form has negative index 0 [L*]; one cavity function of Hecke forms is a complete and sharp receiver, and a zero-free strip ⇔ a rate `y^α`, `α>½` [L*].
- One Hecke eigenform: a halving pair blinds it; RH ⇔ sharp rate ∧ no nonhalving Shimura zero; a sharp rate under ¬RH forces a Shimura zero at `ρ/4+¼`, real part in `(3/8,½)` [L*].
- Any `ℕ`-valued count within a bounded distance of the integer probes gives RH; under RH a count within distance one exists [L*]. Sharp horoball rate ⇔ RH ∧ Möbius × circle remainder [L*].
- Lagarias–Suzuki: `Λ(2s)Y^s+Λ(2s−1)Y^{1−s}` has no non-real zero off the line, `Y≥1`; a real exceptional zero exists exactly above `Y=4πe^{−γ}` [L*].
- Weil's functional on `C²_c` packets is the limit of energies built from truncated Maass–Selberg diagonals with one scalar counterterm [L*].

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| B68 | independent reflection Krein positivity, Krein flux, dispersion bound | RH |
| B71 | universal decay `e^{−t/4}`; horocycle, Farey, Narain or cavity rate `y^{¾−ε}` | RH |
| B87 | a count with Tate limit `Q` | RH |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one eigenform | indep. |
| B114, B117 | a realization of the partner involution outside the excluded classes; a confined companion | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling branch), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRP, APD, AAD, TAPO.

Established [L*]:
- `Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; failure of quasi-RH forces `Θ=Θ∞=1` and AAL.
- RH ⇔ ZAL ∧ B13 ∧ Landing; a failure of the abscissa law fails exactly one atom; landing is a tail law, undecided below every height; FE models with approaching quartets and approaching integer-norm Euler products violate it.
- Classical Deuring–Heilbronn for a real zero of a quadratic `L(s,χ)` with a uniform constant; ζ has no Siegel regime; graded repulsion is refuted on integer-norm Euler products.
- World I: a top layer with a dominant ordinate (its Gamma mass exceeds the mass of all other ordinates of the layer) makes the corrected current diverge at every damping `a` with `a(β−σ)>π/2`; filters read the divisor at every damping speed; VK bound `C h^d t^N exp(a(1−σ)t/2−a t·vk/4)`.
- RH ⇔ attained top ∧ thick bounded lag ⇔ attained top ∧ thick `O(√X)` prime deviation; a thick lag bound at every exponent gives AAL; under AAL the finite-stratum receivers and ZAL are equivalent to RH.
- Graded recurrence: for `½≤σ≤5/6`, `c>(30/13)(1−σ)` and a zero `ρ` with `Re ρ>σ`, the one-separated returns of ζ to a small disc at `ρ` up to height `T` number fewer than `T^c` for large `T`; `T^c` such returns at arbitrarily large `T` on every small disc exclude the zero.
- The zeros contain no conjugacy class of one Frobenius: no vertical progression `ρ+ikT` consists of zeros of ξ, at any real part; `Σ_n|ζ(ρ+inT)/(ρ+inT)|` diverges in the strip and the sum of squares converges; no two-sided sequence of zeros lies within an `ℓ²` perturbation of a progression in the open strip. The periodicity dichotomy for ζ is RH.

| | Obstacle | Strength |
|---|---|---|
| A47, A68 | constants of the one-quartet world; a landing calibration with ζ's Gamma factor (unverified) | — |
| A77 | power-sized cutoffs for the filtered centred Vaughan error: source present [S] | — |
| B13, B138 | finite stratum; landing for ζ | sub |
| B141 | Deuring–Heilbronn for ζ: `¬AAL ⇒ ZAL` | sub |
| B83, B89, B112, B128 | AAL; a bounded aligned return at each right zero; FE into vertical transport; replication | sub |
| B145 | the filtered centred Vaughan current in the growth range | AAL [D] |
| B110, B126, B127 | thick crude count; a bound on a sampling set; positive-measure lag recurrence | AAL |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT, every route at all heights. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, SPAL, ALST.

Established:
- No heavy return while `log t≤(log y)^{3/2−ε}`; every heavy return has `√y≤K(y^{½−w(2t)}log t+log(2+t))`; a strip of depth `h` above some height gives `log t≥c·y^{½−h}` [L*].
- Two-prime depth law (Baker) [L*]; integer combinations of `log(−1)`, `log p`, `log q` are polynomially separated from zero [L*]; collective return counts beyond the depth floor; rational orbit preservers are Laurent Adams maps [L*]; return bounds are label statements shared by `ζ(s−h)` [L*].
- The transfer of candidate S3 implies B56 [D]: in every world with `½<Θ∞<1` its hypothesis holds for large exponents `A` and its conclusion on all late windows is RH.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | certified scans; growing resonators (unverified) | — |
| A75 | Lean form of "transfer ⇒ strip self-improvement" [D] | — |
| B46 | proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97, B137 | constant-precision first return past the VK rung; a collective depth floor uniform in `π(y)` | sub |
| B148 | the transfer of candidate S3 | ≥B56 [D] |
| B121 | freezing control beyond the precision cap | sub |

### S10. The diagonal, counts and absolute geometry
Routes: ACS, HF, HAT-C, PM (count branch). Programmes: SOSZ, HAT, AGZ, AE, RIAC, HHAC, CTH, LST, KPA.

Established [L*]:
- Off-diagonal: `archKernel(m,n)=2π√(mn)·G_{1/2}(|log n−log m|)` on `ℍ³`; `weilPrimeKernel(m,mp^k)=log p·((p−1)/√p)·G^{T_p}_{1/2}(k)`.
- `frobeniusIntersection(ga,gb)=g·a/(1−(a/b)²)+g·log#(ℤ/J(a,b))`: jets plus contacts; a perfect square keeps no contact; a finite fibre forces contacts that are not Weil's; no Witt Verschiebung carries the off-diagonal.
- Refutation of the invariant glued carrier; weighted adelic Green kernel is a positive covariance, invariant, and does not sign Weil's form.
- The mixed hyperbolic Green kernel of the weighted adelic adjacency is the limit of its finite Dirichlet sections; between distinct finite vertices it and its Robin finite part lie between `0` and a strictly tempered product barrier of exponent above `½`, uniformly as the archimedean distance tends to `0`.
- Diagonal: finite part of the jets on invariant combs; the counterterm belongs to the comb; on the carrier Weil's form is a density at every frequency.
- Archimedean fibre: weight lines of the same Frobenius, transposition `z↦1−z`, trace `1+1/(n²−1)` on the jets, pole plane at weights `0,1`.
- Count: RH ⇔ every effective prime class carries an `ℕ`-count with Tate limit `δ_p(1,1)`; the same on power-saving gap sets; section count with Riemann–Roch and Bézout ⇔ Hodge index, over ℤ ⇔ RH.
- Carries: `log C(2N,N)` = carry term + prime count of `(N,2N]`, carry term `∼(2log 2−1)N`. Gluing index of the first `N` graphs is `N!`, within `O(log N)` of the zero count at height `2πN`.
- Clock: `E_r↑W` with Sobolev error; capacity `∼4√N`; clock horizon sharp at `κ=4`.

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests at verified scales | — |
| A54, A70 | cusp expansion for Bianchi resolvents; torus-periodized local Green functions | — |
| A77 | adelic symmetry of the mixed hyperbolic Green kernel: source present [S] | — |
| B87 | a count on the rays `Γ_1+Γ_p`, defined without `Q` | RH |
| B88 | the sign of the Gram defect / of the comb finite part | RH |
| B149 | a section count with Riemann–Roch and Bézout on an infinite-type object carrying contacts and jets | RH (producer) |

### S11. Families, rigidity and exactness
Routes: ACS (tensor branch), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established [L*]: fixed-part theorem (five parts); RH ⇔ sublinear tensor exponents of a cover family with the trace of ζ retained; local residue classification and isozeric continuation; quadratic gauge rigidity; Liouville continuation `exp(J)/ζ`; along the exponentially damped Liouville phases the residue at `1` vanishes to second order in the damping `t`, the fibre rescaled at `s=1+tw` converges to a non-polynomial profile with a branch point of exponent `iπ` at `w=−1`, and no joint analytic regularization exists at the endpoint `(0,1)`; residue Hessian positive with kernel the zero phase speeds; Frobenius at one prime; cost `m·Σ_{p∈S}log p`; primorial divisibility; coefficient gaps separate roots and no such polynomial vanishes at three explicit critical ordinates; no finitely generated lattice stable under three prime Frobenii; integral traces in the open strip force zero amplitudes.

| | Obstacle | Strength |
|---|---|---|
| B86 | positivity of the endpoint character at unbounded rank, mixed Young shapes | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

## 3. Live routes

Receiver statements are `[L*]` unless marked; further established facts are `[L]`.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or a one-sided integer lag, or an attained top with an `O(√X)` prime deviation on a thick set of scales → RH.
- **Established:** RH ⇔ the real lag is bounded below ⇔ the integer lags are bounded below ⇔ bounded above; RH ⇔ attained top ∧ thick bounded lag; a thick lag bound at every exponent ⇒ AAL; `Ω±(√n)`; gauge exponents `[Θ,1]` [L/K].
- **(a)** A30.
- **(b)** bounded endpoint energy (B49); deciding input (B48); attainment of the top together with the thick estimate (B110, ZAL or attainment); past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** RH ⇔ `Ψ` locally bounded on precontact intervals; block S2; verified-height rung.
- **(a)** A1–A3, A16, A79.
- **(b)** B1, B2, B4, B18.

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established:** RH ⇔ `mobiusDivisorSquareRootAbelMoment(M)/M` bounded above, also eventually.
- **(a)** none. **(b)** complete-history cross-clock bound (B42).

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on a tail → RH.
- **Established:** tail lower-bound completeness and its converse.
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH.
- **Established:** RH ⇔ eventual linear floor `−B(K+2)`; sublinear floors impossible [L].
- **(a)** none. **(b)** high-LCM pairs, moving core and singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma response sign → RH.
- **Established:** RH ⇔ response sign at positive frequencies above an admissible radius; RH ⇔ the sharp initial segment of every Hausdorff row is nonnegative.
- **(a)** A1. **(b)** signs below the explicit shift (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** Möbius Hilbert form subpower ⇔ RH; RH ⇔ cofinal admission of the damped Möbius energy; residue energies bounded or equidistributed; orientation-cover weight `½` ⇔ RH; in world I `M(x)=O(x^β)`.
- **(a)** A21, A33, A46.
- **(b)** B48, B50, B15; cubic theta identification (B94); bounded-index correspondence (B106).

### SQF — Weighted squarefree count
- **Path:** `e(t)=Σμ(n)²e^{−nt}−6/(π²t)`; a one-sided `O(t^{−¼−ε})` bound on `(0,1]` → RH.
- **Established:** RH ⇔ the upper law ⇔ the lower law; `Ω±(t^{−¼})`; the `k`-free ladder reads the strip `Re s>1−1/k` [L].
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH.
- **Established:** RH ⇔ `D_t+Q_t/2≤C_t` for every `0<t<½`; VK saving of the residual [L].
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted; block S4.
- **(a)** A20, A1.
- **(b)** outer roots (B22); bounded `N_d` gives finite support only (B23, then B13, B138); heat budgets (B124).

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** RH ⇔ every positive-time zero simple; blocks S3, S4, S8; ordinate injectivity ⇔ RH; the centred Vaughan first-moment reduction is unconditional for `X≥t⁸`.
- **(a)** A19, A47, A68.
- **(b)** B24, B25, B47, B27, B124; B130; B83 through transport or a contradiction in world I (B89, B112, B128, B145); B13, B138, B141.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established:** RH ⇔ every rectangle has an anchor with trace norm `<1`; RH ⇔ an explicit Gaussian central-gap inequality for `0<y≤1`.
- **(a)** none. **(b)** trace norm below one on every rectangle, or the Gaussian inequality (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; cofinal source-work `≤2` ⇔ RH; ground-state dichotomy and three-way classification.
- **(a)** A9, A13, A70.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149.

### HAT-C — Arithmetic-clock Green energy
- **Path:** prime capacities fill one clock → `E_r(f)↑W(f)` → `W≥0` on packets ⇔ RH.
- **Established:** `0≤W−E_r≤(1−r²)‖f′‖²/2`; uniform Sobolev convergence; growing windows `log N/2` at clock `κ√N`, `κ>4`.
- **(a)** none.
- **(b)** `E_r(f)≥−ε` arbitrarily near `r=1`; this is `W(f)≥0` (B1) [D].

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH.
- **Established:** RH ⇔ the Klein–Gordon prime wave is bounded; RH ⇔ the resolvent is at most `½` on the odd sector.
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** signed jet cone ⇔ RH; rank 14 at `0<a≤½`; the adaptive partial sum is `ζ(½+ib)` up to `O(|b|^{−½})`.
- **(a)** A4, A5, A24, A42.
- **(b)** signed adaptive head near critical zeros (B102); amplitude oscillation (B20); all ranks (B21).

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH.
- **Established:** RH ⇔ Gamma/polar energy `≤` prime energy on theta ground profiles; a strict violation is a falsification witness.
- **(a)** none. **(b)** joint-node exclusion or the comparison (B36).

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ cofinal polynomial boundedness; strict slope saving ⇒ RH; five-way unit-window equivalence; block S5.
- **(a)** A18.
- **(b)** B62, B57–B61, B63.

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ `R(t)≥−C e^{r′t}` eventually for every `r′>0`; RH ⇔ Cayley ladders NSD on primitive vectors.
- **(a)** A1. **(b)** the lower bound or the sign (B43).

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH.
- **Established:** the Hilbert-source criterion; `|A_N|≤C√N e^{−c·vkScale N}` [L].
- **(a)** none. **(b)** bounded completed residual (B37, B1).

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity-energy rate, or a count → RH.
- **Established:** block S7.
- **(a)** A26, A70.
- **(b)** B68, B71, B87; B147; B114, B117.

### PTR — Cosine source
- **Path:** strict Laguerre sign of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ strict Laguerre at every `0<h<½` ⇔ `(Im ξ′)²+Re ξ·Re ξ″>0` on `½<Re s<1` ⇔ no exceptional point.
- **(a)** none. **(b)** the sign below the VK boundary (B29); a prime-faithful lossless stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on finite power windows of square shells → RH.
- **Established:** RH ⇔ subpower growth on `m<k≤m+m/log(m+1)` for infinitely many `m`.
- **(a)** none. **(b)** the control (B51); the shell alternative needs ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass → RH.
- **Established:** RH ⇔ unit-bounded chronological rows reach every tolerance; RH ⇔ the BSY integral vanishes.
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH.
- **Established:** RH ⇔ nonnegativity on the grids of `log 2` and `log 3`, after any finite prefixes.
- **(a)** A1. **(b)** nonnegativity at every degree (B30).

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH.
- **Established:** RH ⇔ disc self-maps ⇔ source margin.
- **(a)** none. **(b)** the cover (B32).

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** RH ⇒ strong recurrence on compacts of the strip; uniform head-target density on every right-strip disc ⇒ RH; block S9; in world I heavy returns are later than `exp(c·y^{1−β′})`; one-separated returns to a small disc at a zero right of `σ` number fewer than `T^c`, `c>(30/13)(1−σ)` [L*].
- **(a)** A37, A47.
- **(b)** uniform target mass (B72); transport (B83, B89); breadth past VK (B97, B137); B145.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH.
- **Established:** RH ⇔ the blind minimum is nonnegative at every aperture; `≥1/20` on the first window [L].
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH.
- **Established:** the all-stage quartic source law gives RH; RH gives uniform decay.
- **(a)** none. **(b)** charge below `ε` at arbitrarily late stages (B33).

### OWU — Odd sector
- **Path:** archimedean-minus-prime positivity on odd tests → RH.
- **Established:** RH ⇔ the form is nonnegative on odd compact `C²` tests.
- **(a)** A1–A3, A6. **(b)** B4, B17, B44.

### PBM — Regularized abscissa
- **Path:** convergence of the pole-regularized series right of `½` → RH.
- **Established:** exact equivalence for the prime and the log-ζ coefficients.
- **(a)** none. **(b)** the partial-sum bound (B53).

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH.
- **Established:** Robin's inequality at `lcm(1,…,n)` for large `n` gives RH; remainder criterion.
- **(a)** none. **(b)** the inequality (B54).

### SRT — Lag localization
- **Path:** the prime two-bump sign on a decisive sample → RH.
- **Established:** RH ⇔ Weil positivity of every prime two-bump ⇔ these values bounded below; RH ⇔ a lower bound on the two-prime difference lags of arbitrarily late `√T` windows [L*]; block S3.
- **(a)** A9, A72, A73.
- **(b)** B130; B143; B6, B101.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH.
- **Established:** RH ⇔ the variation inequality at any single shift `a>0`.
- **(a)** A7. **(b)** one shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** global incidence allocation → RH.
- **Established:** RH ⇔ the allocation condition for every odd compact test ⇔ the full zero form is nonnegative on odd tests.
- **(a)** A9, A13. **(b)** signed cost `C_σe^{2σr}` (B45); polar payment (B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling on one two-prime cone → RH.
- **Established:** RH ⇔ bounded damped cone coupling for any two primes and any `τ>0`; under AAL the finite-stratum receivers collapse to RH.
- **(a)** none. **(b)** the coupling bound; sublinear tensor loss (B39); ZAL for the undamped branch.

### ACS — Castelnuovo–Severi at the prime degrees
- **Path:** all-aperture Bézout of the source cone → RH; or `P(p)≤A(p)+K` on logarithmic windows off power-thin exceptions.
- **Established:** RH ⇔ all-aperture Bézout ⇔ all-aperture ampleness of the exact source cone; blocks S3, S10; the pairing of the degree points (jets + twice the contacts) tends to pole − Weil on packets [L*].
- **(a)** A28, A41, A48, A59, A72.
- **(b)** B40, B130; B87, B88, B149; B28.

### ECP — Endpoint character positivity
- **Path:** endpoint jets → coherent symmetric-group class functions → PSD character Grams at every rank ⇔ RH.
- **Established:** column projections nonnegative; Toeplitz minors through order 200; mixed shapes `(2,1)`, `(3,1)`, `(2,2)`, `(2,1,1)` [L].
- **(a)** none. **(b)** positivity at arbitrary rank (B86).

## 4. Candidates

Each needs its source-to-receiver step first (B81).

| Candidate | Established | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| S3 | weighted return bounds [L]; floor on logarithmic windows off exceptions ⇔ RH [L*] | A75 | the transfer has at least the strength of B56 and fails in every world with `½<Θ∞<1` [D]; its hypothesis is implied by quasi-RH [D] (B148) |
| SEC | Fock boundedness at every divisor point ⇔ RH [L*] | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` [L] | none | arithmetic descent on actual zero fibres |
| APF | prime/grade trace reconstruction on real labels [L] | none | full-divisor exhaustion and RH landing |
| EGC | zero-pair contour; count error `≤32ε²log T/T` [L] | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on the blind plane [L] | none | faithful endpoint admission |
| FEL | KL accounting [L] | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution [L] | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport [L] | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion [L] | none | RH-sufficient orientation law |
| W1C | real-rooted or Laguerre–Pólya approximants on one interval give RH [L*]; index-one limits give RH [L*] | none | a finite ferromagnetic producer, or an independent index-one family (B146) |
| WBF | Gram recovers magnitudes and phase class [L] | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| SOSZ ScaleLocality | `√T`, log-square and logarithmic windows; exceptional sets; signed deletion; separated windows; short windows miss; other side on windows; counts on one sequence of windows [L*] | A72, A73, A76, A78 | B130, B143, B144 |
| ELT | atoms and landing forms; Deuring–Heilbronn calibration; filters at every speed; boundary rotation; polynomial damping; VK bounds; centred Vaughan current; dominant-ordinate divergence; arithmetic bounds in world I [L*]; power-sized Vaughan cutoffs [S] | A47, A68, A77 | B141, B145, B138 |
| ZCG AbscissaLaws, Recurrence | split, atoms, sectors, quasi-RH as a tail law, heat-, cosine- and Jensen-family laws, graded recurrence [L*] | none | B13, B83, B138 |
| IRP | index law; semicontinuity; Eisenstein line law and its blindness; exceptional parameter at `4πe^{−γ}`; Kronecker at infinite rank; attained top replaces ZAL on thick sets; Lefschetz numbers are not traces; no class of one Frobenius among the zeros, nor an `ℓ²` perturbation of one [L*] | none | B146 |
| AWT | fixed-part theorem; cover-family tensor criterion; gauge deformations; moving branch and quadratic residue collapse of damped Liouville phases; edge divisors; Künneth [L*] | none | B86 |
| SignFreePurityMechanisms | height separation ⇔ bounded prime traces; Frobenius at one prime; `m·θ(S)`; primorial; Newton polygons; coefficient gaps [L*] | none | — |
| AGZ | ghost ring, cofreeness, contacts, torsion conormal, carries, gluing index, comb finite parts, archimedean fibre, toric surface of a base, tower of lines [L*] | none | B149, B88 |
| HAT | adelic Green formula; full degree carrier; prime operators; weighted Green covariance; mixed hyperbolic Green kernel from finite Dirichlet sections with strictly tempered barriers and uniform adelic decay; refutation of the glued carrier; scattering tower; arithmetic clock [L*]; adelic symmetry of the mixed kernel [S] | A54, A70, A77 | B88 |
| AHMH / BHR / ASH / CTH | cavity receivers, reflection Krein forms, halving descent, ringdown, count door, sharp shells [L*] | A26, A41 | B68, B71, B87, B147 |
| TTPO / CDGeo / PTT / TAPO | depth law, VK breadth, strip breadth, collective counts, label statements [L*] | A24, A37, A75 | B97, B137, B148 |
| ALST / AAD / RAC | Stepanov degrees; orbit rigidity; producer rates [L*] | A30 | B48, B55, B67 |
| AHD / CACT | threshold identities, ground states, classification [L*] | A9, A13 | B104, B123 |
| Census (IGP, P) | density `0.67250071`, covariance equivalence, alternatives, exchange rate [L*] | none | B150, B57 |
| HTGeometry | positive translation repair of Laplace-positive functions, keeping a prescribed mode [L*] | none | — |
| VHR / TCS | verified-height rungs; height 67 [L*] | A1–A5 | — |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: `P(p)≤A(p)+K` on the primes of logarithmic windows off power-thin exceptions | ACS, SRT, WL, HF, ZCG, HAT-C, and every window route through the prime two-bumps |
| Σ sign on every window (`a*(ζ)=⊤`), equivalently verification at every height | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C |
| Σ continuation at small time and the theta head at the critical zeros | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and count | PM, ECP |
| The exceptional coordinate: world I (B13, Landing, DH sectors) and world II (ZAL) | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range | every route at all heights; BAG; TH certificates; WD near-unit moments |
| Missing source landing | the twelve candidates |
