# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `1cec78e529` with its working tree (2026-11-10). Working log: `logs/review-1011-status-quo-facts.md`.

**Evidence.** `[L*]` Lean statement read for this report (working log §5); `[L]`, `[K]`, `[S]` as graded by the frontier map and the scoped-obstruction ledger at the checkpoint, not re-read; `[D]` deduction made here from `[L*]` statements (working log §7); `[C]` classical mathematics quoted from memory, not in the corpus, to be checked before use; `[A]` assessment; `[X]` one external source cached in the repository, outside the native import graph and not checked here: a zero-free half-plane `Re s>7/8` for ζ, Dirichlet `L`-functions and Hecke `L`-functions over `ℚ(√−3)` (see [fable.md](fable.md)). Sections 2.3–2.14, 3 and 4 are interpretation and ideation: every untagged statement there is a proposal, not a result.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS is a retired label.

**Notation.** As in [route-obstacles.md](route-obstacles.md): `Θ`, `Θ∞`, ZAL, AAL, B13, Landing, DH, B56; world I (I-a, I-b), world II, the edge world `Θ=Θ∞=1`; `c_B`, `c_p`, `P(d)`, `A(d)`; logarithmic windows; the comb pairing and the comb form; system, mass `m`, dominated, rung `κ=a/log m`, trivial aperture, Liouville twist; `JasDressedPSD σ`; the signal of the zeta kernel. A statement is **selective** if it fails for some system that shares all of ζ's structures but one.

## 1. Big picture

### 1.1 One object, two exact forms
- **One inequality per prime.** RH ⇔ `2c_p≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window [L*]. Equivalent forms on the same windows: the upper bound `2c_p≤K` alone, without omissions [L*]; `ℕ`-counts on the surviving rays `Γ_1+Γ_p` with quadratic limit the plane defect [L*]; local even moments of the traces with one growth exponent for all orders [L*]; the absolute value [K]; a floor on two-bump comb packets [L]. The exponent of the floor is the width; a power saving is quasi-RH [L].
- **One matrix on the integers.** The comb pairing has the limit `2d₁d₂−Z(f)` on packets; RH ⇔ exactly one positive square on the two rulings and every finite family of packets [L*]; the negative index of the defect is the exact number of distinct right zeros, for ζ and for ζ with finitely many primitive Dirichlet `L`-functions [L*].

### 1.2 The sign has no margin and its data are forced
`CombBezout w ⇔ RH ∧ w=Λ`; with the counterterm `log(n/2π)−c`: `⇔ c≤0 ∧ RH` [L*]. With contacts `(1+ε)Λ+δ`: `⇔ ε=0 ∧ RH ∧ c≥sup P_δ`; one contact changed by `t` costs `2|t|/√n` [L*]/[L]. With the tree of `p` glued at edge length `ℓ`: `⇔ RH ∧ ℓ=log p` [L*]. A uniform floor `−C∫f²` over all packets is RH; the best margin of a window decays doubly exponentially [L]. RH ⇔ at every aperture some real weight system is Weil-positive, with no compatibility between apertures; if RH fails, one aperture admits none [L*].

### 1.3 Two worlds, three atoms, one edge
`Θ<1 ⇔ Θ∞<1` [L*]. A failure of RH is world I (a finite isolated top layer at `β<1`, with a free strip and a Mertens power saving) or world II (a tail approaching `Re s=Θ∞>½`) [L]. RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH [L*].

| Structure kept | Model | What fails | Evidence |
|---|---|---|---|
| Euler product, integer norms, linear counting | two-scale products with `(Θ,Θ₂,Θ∞)=(β,θ₂,θ)`, `½<θ≤θ₂<β<2/3` | DH and every graded repulsion bound | [L*] |
| functional equation, Riemann Gamma factor, residue one, order `≤1`, count within one | the paired ξ model: all zeros simple, off the line, approaching it | Landing | [L*] |
| both, up to an integrable defect, with a positive continuous prime measure | `ζ(s)exp(ε/(s+1)²)` | nothing: the zeros are those of ζ | [L*] |
| both, among Dirichlet series over the integers | ζ alone (Hamburger; rigidity of countable systems) | — | [L] |
| both, over a discrete system of real norms, order two | Selberg zeta functions of surfaces with small eigenvalues: finitely many real zeros in `(½,1)` | B13 | [C] |

So the atoms have no model with both structures among Dirichlet series over the integers; outside that class B13 fails in a classical family (§2.5).

### 1.4 The finite layer is seen on bounded windows
An attained positive top of ζ with at most `k` positive ordinates breaks every fixed floor on every sufficiently late continuous window of length `(k+1)π/67` [L*]; `n` modes of frequency `≥Γ` keep one sign on a length `≤nπ/Γ`, with no separation [L*]. A floor on integer runs `[x,e^Lx]` for every `L` gives AAL; so do floors on arbitrarily late windows of length `(k+1)π/67` with a constant depending on `k`, also at the prime logarithms, and a floor of any exponent below the top depth fails on such windows [L*]. A density-matched configuration with unattained top passes every floor on windows of a radius `o(log T)` [L*].

Statements that exclude world I, and the world each leaves open [L*]/[D]:

| Statement | Implied by RH | Gives | World left open |
|---|---|---|---|
| floors on windows of every bounded length at arbitrarily late scales, constants depending on the length | yes | AAL [L*] | unattained tops (world II, edge) |
| level-one dressed positivity on large primes | yes | RH: `Θ=½`, with no half-plane [L*] | none |
| attained top ∧ thick `O(√X)` prime deviation | yes | RH [L] | none |

### 1.5 The ladder: what is proved is sizes
A system has a mass `m` (log conductor; log height) and a packet an aperture `a`; the rung is `κ=a/log m`.

| Fact | Evidence |
|---|---|
| Below rung one every dominated system is positive with margin: `½(1−e^{−η/2})log q∫f²` at `a≤log log q−η`; at height `t`, `½(1−e^{−η/2})log\|t\|∫f²−5∫f′²` at `a≤log log\|t\|−η` | [L*] |
| At `log log q+η` the Liouville twist and `−Λ` fail on the odd polar packet, `Λ` without pole plane on the even one; the Liouville twist violates every floor; the trivial aperture is `log log q+o(1)` | [L*] |
| At `log log t+log 2+η` a dominated system built with the height fails | [L*] |
| Prime side: partial sums `≤Cn^{½+γ}` buy the rung `κ<1/(2γ)` on bounded shapes; twisted cancellation at every frequency inside the archimedean budget buys all packets; the sign on the polar packets is square-root cancellation of the Riesz mean | [L*] |
| At `log log q+log 2+η` a dominated system has the floor `½log q(∫f²−∫f′²)` on every packet and is not feasible: bounded shapes do not decide the sign on all tests | [L*] |
| Zero side: a pair of depth `δ` shows at rung `1/(2δ)`; for ζ and Dirichlet characters the sign on a rung `κ` forces a second off-line zero within `m^κ` of every zero of depth `>1/(2κ)` | [L*] |
| A real character with the sign at `log log q+η` has a prime `p≤e^{2η}log²q` with `χ(p)≠1` and one with `χ(p)≠−1` | [D] |
| In the height aspect the sign at rung `κ>1` for the fixed system `Λ` excludes an alignment of a proportion `(log t)^{1−κ}` of the `p^{−1/2}`-mass of the primes `≤(log t)^{2κ}`: the dark range below the Vinogradov length | [D] |
| In the mean over the heights `[T,2T]` the contact polynomial of aperture `a` has mean square `≤2a(2+2a)²+1` when `4e^{4a}(2+2a)⁴≤T`: the sizes are attained at aligned heights only | [L*] (graded [S]) |
| The same rate on the mean-value ladder: mollifiers of length `T^{θ}`, depth `1/(2θ)`; proved range `θ<½` with both gcd main terms | [L]/[L*] |

Natively no rung above one is proved in any aspect, and the first step by sizes is a classical problem in each (least non-residue at the scale `log²q`; the region `1−c/log log t`). `[X]` gives the rung `4/3` in the height and the conductor aspect.

### 1.6 A level and a half-plane
Positivity of the dressed lag aggregate at level one on the characters of all large primes gives `Θ=½`: RH, with no half-plane and no edge exception [L*]. A level `σ>1` on large primes gives `|Re ρ−½|≤σ−1` or the edge world; level two holds, `3/2` on large primes [L*]. A half-plane has a second receiver: a bound `O(Z^b)`, `b<1`, of the signal of the zeta kernel, a smoothed Möbius sum, gives `Re ρ≤b` [L*]; the family form continues the reciprocals of a whole family from two estimates for one sum [L*]. `[X]` is this receiver at `7/8`. Its source is one identity, in the native graph: the cube of the composite cubic Gauss sum is the ideal Möbius value times a phase [L*]. On a finite field `g(χ)^n≡−card F mod (μ−1)²` for every odd order `n>2` and `≡χ(−1)card F` for even order [L*]: order three is the least order with the Möbius sign. The budget of the detector has the boundary `7/8` at every redistribution of its two scales, `29/36` with the unit term alone [L*], and with its row-count law no boundary below `7/8−1/4000` [L]; the exceptional frequencies of one coprime column pair add without cancellation [L*].

### 1.7 Constituents
No absolutely convergent Dirichlet series, and no absolutely convergent expansion over positive real scales on a strip about the line, has a zero there with its zeros there among those of ξ; one zero forces infinitely many unmatched ones [L*]. Mechanism: recurrence of a zero against the density zero of the deep zeros, then the jump law: two absolutely convergent expansions of `−sΦ/ζ` on the two sides of the line are equal, also with countably many poles of summable residues on the line [L*]. A bounded constituent with a zero lives on `Re s>x`, `0≤x<½`, has support exponent `≥1−2x` and infinitely many primes [L*]. Every box has a Dirichlet polynomial with exactly the zeros of ξ, of unbounded length; for bounded length a fixed height refutes [L*]. Sizes on one circle bound the zeros of ξ in the disc by the zeros of the dominant half of a splitting [L*].

### 1.8 The square returns identities
| Structure | What it returns | Evidence |
|---|---|---|
| Sections with Riemann–Roch and Bézout on the tower of lines | the product formula | [L] |
| Restriction on the planar square (unit masses, every contact paid) | an equality of ideals: the values on `Γ_m` are exactly `Π_{n∈S}J(m,n)` | [L*] |
| The count of a section on two graphs | the split norm `\|x_mx_n\|`, quadratic on rays, not a form | [L*] |
| The own comb of an integer-norm system (squares) | Bézout fails without hypothesis | [L*] |
| A tower of rings | the base has weight `1/d`; the per-degree limit does not see ζ | [L*] |
| The tree of a prime with a free edge length | `ℓ=log p` forced; at `p=2` on packets `≤log 4` a monotone path with threshold `ℓ*(L)` | [L*] |
| Gluing along the comb with a free scale or constant | scale one and `c≥sup P_δ` forced | [L*]/[L] |
| An adelic-invariant glued carrier | constant diagonal; refuted | [L] |
| Jets and contacts | even Newtonian multipoles on an axis; chain squares minus the diagonal | [L*] |
| The counterterm of an abelian ring | Riemann–Hurwitz with the conductors as ramification; genus `1+(n/2)log(n/2π)` | [L*] |

### 1.9 Finite scale
Short windows are coercive and blind to the contacts; every window has finite index [L]; a real divisor may be replaced by its block means at the cost `εΣc_n²`, and floors `−ηΣσ²` on block-constant divisors at arbitrarily large block sizes give RH [L*]; the prime entries of the limiting matrix on flat packets are overlap lengths [L*]. Each window follows from verification to `windowHeight(a)`; RH is verified through 67; a verified height `T` gives the two-bump sign at every prime below a rung tending to infinity [L*].

### 1.10 Regulators and the horizon
`E_r↑W` with error `(1−r²)‖f′‖²/2` [L]. The scattering tower of height `N` is the logarithmic derivative of `Λ(s)/Λ(s+N)` plus Robin and polar terms; corrected energy plus a nonnegative jump tail is the closed Weil form; for every fixed `N`, RH ⇔ the raw energy is at least minus its full arithmetic defect [L*]. The critical adelic Green inverse is unbounded [L*]. Ringdown at the quarter rate, reflection positivity of the cavity forms, the horocycle rate `y^{¾−ε}` and an `ℕ`-count with Tate limit the integer probes are equivalent to RH [L].

### 1.11 Law and point
Past the Vinogradov–Korobov region every unconditional native theorem about the location of the zeros of ξ is in law: density exponent `30/13`, deep zeros `o(V)`, twisted moments below the square root, resonator means, Matomäki–Radziwiłł for μ, `67.25%` of simple critical zeros [L*]/[L]. The pointwise theorems act on constituents (§1.7), on finite layers (§1.4) and on fakes (§1.5). `[X]` is pointwise for every zero right of `7/8`.

### 1.12 Receivers are complete; producers
For each mechanism that proves a statement of the type of RH elsewhere the corpus fixes its price over ℤ.

| Mechanism | What the corpus proves | Evidence |
|---|---|---|
| Surface, sections, Riemann–Roch (Weil) | §1.8: identities | [L*]/[L] |
| A bounded-below naive height and Tate's limit | RH ⇔ such a height on every window; ⇔ counts on the surviving prime rays; the object's own count is the split norm | [L]/[L*] |
| A family with monodromy (Deligne) | fixed-part laws; tower weight `1/d`; a cover bounds its base | [L]/[L*] |
| A Frobenius with zero derivative (Stepanov) | cost `m·θ(S)`; one prime: `p^{11/12}` | [L] |
| Ferromagnetic stability (Lee–Yang) | linear zero counts; no stable prime polynomial converges to Ξ | [L] |
| A dominant half (Hermite–Biehler) | index law; sizes on a circle; no splitting with certified defect | [L]/[L*] |
| Newton polygons (Sheats) | greedy carry-free compositions are the optimal ones; the carry is a nonzero class; the jump law is the law of the carry | [L]/[L*] |
| Recurrence (Bagchi) | RH ⇔ strong recurrence; recurrence against density empties the Wiener class of constituents | [L]/[L*] |
| Existence of weights (duality) | RH ⇔ feasible weights at every aperture | [L*] |
| Sizes of the contacts | the trivial aperture `log log(mass)`; nothing beyond | [L*] |
| Mean values | below the square root in Lean; conversion to a point needs length past the height | [L*]/[L] |
| Power sums (Turán), half-period deletion | finite layers on bounded windows | [L*] |
| Continuation of the reciprocals of a family with a reciprocity identity | the principle, the receiver and the local sign law; the half-plane is `[X]` | [L*]; [X] |

Consequence [D]: natively every route is a receiver. The one producer is `[X]`, outside the native graph.

### 1.13 Where a statement has slack
| Form of RH | Slack | Evidence |
|---|---|---|
| the sign over all packets | none upward; any uniform floor `−C∫f²` downward | [L*]/[L] |
| a floor at the primes for one fixed bump | `p^{o(1)}` | [L] |
| the long Möbius moment | any fixed power of `T`, uniform in `θ` | [L*] |
| the signal of the zeta kernel | any exponent below one gives a half-plane | [L*] |
| the level of the dressed aggregate | `σ−1` in the depth | [L*] |
| the index of an approximant | one unit | [L] |
| returns | a power `T^c`, `c>(30/13)(1−σ)` | [L] |

Receivers with power slack accept an estimate with any power margin; the sign routes do not [D].

### 1.14 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Sizes of the contacts beyond the trivial aperture, in the conductor or the height aspect | the dominated box fails at rung `1+o(1)` | [L*] |
| An exceptional square with a bounded gap | no gap: the first rung past the trivial aperture is the least non-residue at the scale `log²q` | [L*]/[D] |
| A receiver below the logarithmic radius at the level of configurations, also with ζ's density | density-matched model with unattained top | [L*] |
| An exact arithmetic constituent of ξ with a zero in the Wiener class; a Dirichlet polynomial of bounded length sharing zeros at all heights | none; a fixed height refutes | [L*] |
| Sections of the square, of the tower or of the planar square as a source of a sign | identities | [L]/[L*] |
| The count of sections on two graphs as the pairing | split norm | [L*] |
| A free contact weight, constant, scale or tree length | forced | [L*]/[L] |
| A per-degree limit in a tower; an own comb | loses ζ; fails | [L*] |
| Landing from the functional equation, Gamma factor and count; repulsion from Euler products | models | [L*] |
| Rigidity of positive prime measures under finite functional-equation defects | continuous perturbations | [L*] |
| Cancellation over the exceptional frequencies of one coprime column pair | the terms add | [L*] |
| A family as a source of purity by averaging; one glued invariant carrier; finite-type objects; stable prime polynomials; positive ground states for the polar charge | as recorded | [L] |
| Bilinear statements as parity-sensitive information | invariant under the Liouville twist | [L*] |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads, positive Laplace mixtures; Schur, `C*`, KMS, internal modular conjugation; bounded-height Diophantine certificates against returns | refuted or bounded | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A103 | The ladder as one statement: saving `γ` ⇒ sign to `κ<1/(2γ)`; the sign on a rung ⇒ no isolated zero of depth `>1/(2κ)`; a bounded dyadic moment at `θ>1` ⇒ depth `<1/(2θ)+ε` eventually; the seven power savings of quasi-RH [D] | RW, WD, SRT | `exists_cancellation_margin`, `zeta_companion_of_rung`, `finite_offLineZeros_beyond_of_dyadic_long_mollifier`, `quasiRH_crossRoute_seven_way_tfae` |
| A108 | The first rung in the conductor aspect: the sign at `log log q+η` forces a non-residue and a split prime below `e^{2η}log²q` [D] | ACS, HF | `feasible_congr`, `exists_systemForm_polar_neg` |
| A109 | The trichotomy of the normalized prime error: RH, a nonzero finite trigonometric limit (world I), or limit zero [D] | ZCG | `exists_primeErrorFiniteOscillation_of_lt_gap`, the half-period law |
| A113 | The map under a half-plane premise `Θ≤b`: the rung `1/(2b−1)` on bounded shapes, large-prime positivity above the level `½+b`, return-free windows of the prime orbit [D] | JAS, SA, S3 | `exists_cancellation_margin`, the level dichotomy, the strip theorem for returns |
| A114 | The limit matrices of the block-constant form with both pole moments: RH ⇔ Weil's form is nonnegative on step packets of `3KR` blocks, for all `K,R` (unverified) | ACS, HF | `riemannHypothesis_of_frequently_blockFunction_combForm_ge`, `tendsto_flatContactPoints_self_autocorr` |
| A104 | Exceptional heights on the ladder: the sizes fail at aperture `a` at most on a set of heights in `[T,2T]` of measure `O(Ta³/log²T)`, from the mean square of the contact polynomial [D]; `T^{1−1/(2κ)+o(1)}` on rung `κ` from moments of order `log T/log Y` [D] (unverified) | RW, BAG | `integral_contactPoly_window_sq_le`, `exists_height_margin`, `measureReal_large_primePoly_le` |
| A105 | A density-matched configuration that is positive on a rung and has deep zeros at arbitrarily large heights: the sign on a rung is not a strip at the level of configurations (unverified) | SA | the hiding configuration at aperture `(log T)/36` [L]; the projection of ζ's divisor |
| A102 | The additive `log 2` between the two bounds of the height aspect (unverified) | SA | `exists_height_margin`, `exists_dominated_height_neg` |
| A80, A94 | The converse at finite scale; the index at finite scale as the window index (unverified) | ACS, HF | the block decomposition; `exists_windows_le_weilNegIndex` |
| A82 | The Li ladder as comb forms of tails (unverified) | LI, ACS | `tendsto_combForm_flatTail_div` |
| A79, A81, A93 | Constants of the aperture–height exchange; the order of `windowHeight(a)` (unverified) | RW, ACS | `windowPositiveAt_of_rhVerifiedThrough`, the resolution law, `exists_height_margin` |
| A78, A89 | Cluster form of the separated-window theorem; a prescribed radius in the sub-logarithmic model (unverified) | SRT | the finite-mode theorem; the block tower |
| A86, A47 | The near-diagonal cofactor pairs and the transfer through the growing-order filter; constants of the one-quartet world (unverified) | ZCG, BAG | the growing-order reduction [K] |
| A111 | A proportion of critical zeros by Levinson's gate from the twisted moment below the square root (unverified) | WD | `exists_interval_twistedMoment_le`; the Levinson detector coefficients |
| A116 | Ideals as degree points; Hecke characters; the index law per Artin character for a non-abelian ring (unverified) | ACS | the abelian index theorem; Riemann–Hurwitz; `hasSum_zeros_two_lines` (the zero side of an explicit formula without functional equation) |
| A119 | The depth sum `Σ_{β>½}(β−½)≤cT` with a constant from the mollified moment (unverified) | WD, AIF | the moments below the square root |

### Finite verification and explicit constants
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Certified `RHVerifiedThrough T` past 67 | all rungs | `rhVerifiedThrough_sixtySeven` |
| A2, A3 | Numeric values of the explicit heights; membership on the first windows | window routes, TH, LA, HCF | explicit definitions |
| A4, A5 | Theta rank 15 and beyond; certificate of the center-tail failure (unverified) | TH | height 67 |
| A6, A7 | Cone widths; certificates on the anti-diagonals (unverified) | CHT, ACT | convex programs |
| A9, A13 | Constants at the eighth-root horizon; near-gcd charges (unverified) | HF, AIP | proved limits |
| A117 | End points of the feasible interval of `w(2)` on the first selective window | RW, ACS | `exists_abs_weight_le_of_poleFeasible`, `poleFeasible_of_abs_sub_le` |
| A112 | The positivity ceiling of the census certificate at the threshold `7/45`: a linear programme | census | `positivity_does_not_reach_three_quarters`; the exchange rates |
| A48, A58 | Hasse–Weil tests at verified scales; effective gap iteration (unverified) | ACS | window rungs |

### Classical inputs to formalize
| # | Task | Routes | Basis |
|---|---|---|---|
| A118 | `[X]` in the native graph: the Fourier coefficients of the cubic residue as cubic Gauss sums; removal of cube indices; the mean square with uniform transfer bounds; the detector and the continuation to `11/12` and `7/8` | JAS, MC, S3 | MMD; FCT; the cached external sources |
| A18, A21 | Twisted second moments past the square root; logarithmic two-point Chowla [C] | WD, MC | `θ<½` in Lean |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM | order `N(Λ)≍Λ` |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics [C] | ACS, PM | hyperelliptic law |
| A59 | Short-interval primes in a residue class [C] | ACS, SRT | gap sets |
| A115 | The Newton polygon of the Carlitz–Goss zeta function from the greedy optimum [C] | sign-free calibration | `isOptimal_iff_isGreedy` |
| A120 | A finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C]; at finite rank the impure curve data of the corpus | BAG, ZCG | `selbergSmallEigenvalue_offCritical`; the golden datum [L] |

### Further items
A16 numerical `r,m,q`; A19 an explicit height for the heat horizon; A20 a Jensen rung toward the saddle scale; A24 certified scans; A28 reciprocal-quadric traces; A30 best stencil exponent under RH; A42 Gamma-weighted transport to the adaptive head; A46 singular indices; A54 cusp expansion for Bianchi resolvents (all unverified).

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K`, or `2c_p≤K`, on the primes of arbitrarily late logarithmic windows; any growth `Kp^σ`, `σ<½`, is a zero-free strip. Known natively: the VK saving | RH (≥qRH) | ACS, SRT, WL, HF, ZCG, HAT-C |
| B159 | A rung above one: a power saving of ζ's contacts on the integers between `m` and `m^{2κ}`, uniform in the height, that fails for the Liouville twist and for the lattice with a pair. In the height aspect: no partial alignment of the primes `≤(log t)^{2κ}` [D] | ≥qRH | every sign route; BAG |
| B144 | Separation of the deep off-line ordinates of ζ | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window; equivalently the fixed-height energy floors | RH | all sign routes, HAT-C |
| B152 | The comb form on block-constant divisors: `≥−ηΣσ²` at arbitrarily large block sizes, every `K,R,η` | RH | ACS, HF |
| B160 | `JasDressedPSD 1` on the characters of all large primes: it gives `Θ=½` with no half-plane [L*] | RH | JAS |
| B18 | A construction of feasible weights at every aperture | RH | RW |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact; outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | **Polar orthogonality** at the critical curve (§2.4) | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B156 | Clusters on a rung: whether the sign on one rung `κ>1` at all large heights gives a zero-free strip for ζ | method | SA, RW |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
| B19–B21, B102 | Torus law for `S*`; amplitude oscillation; all theta ranks; the signed adaptive head | RH | TH |
| B22, B24, B25 | Outer roots of the Jensen polynomials; collisions at small time; frequency below one | RH | LA, ZCG |
| B27, B28, B47 | Runs of simple critical zeros; local positivity at fixed `λ` on density-one heights; multiplicity by a non-size input | sub | ZCG, RW |
| B29–B45 | The single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | Finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146 | An independent family of bounded index converging to ξ; a splitting of ξ with sizes on circles and a defect counted without the zeros | RH (producer) | W1C, PTR, IRP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B161 | The signal bound `O(Z^b)`, `b<1`, in the native graph: a power saving of one smoothed Möbius sum. `[X]`: `b=7/8` | ≥qRH | JAS, MC |
| B158 | **A second source**: a completed sum with two exact representations whose dual side contains the reciprocal of the target, from Gauss sums of an odd order `n≥5` or another identity; the boundary `b(n)` of its budget (§3) | producer | JAS, MC |
| B48–B54 | Deciding input at square-root precision; endpoint energy; trivial-gauge half power; moving power windows; rows and BSY; regularized partial sums; extremal inequality | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | Polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½`; implied by the transfer of S3 [L*] | ≥B56 | whole programme |
| B57 | Depth density `o(T)` | sub | WD, CTF, MC, RW, PM |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub | WD, MC |
| B62, B63, B66 | Cofinal long moment; collision charge; near-unit holomorphic budgets | RH | WD, CTF, AIF |
| B91, B94 | Cut-kernel mass; cubic theta identification and rational descent | RH; past VK | RAC, MMD |
| B46, B96, B97, B100, B121, B137 | Proportional saving at length `(log X)^{2K}` at all heights; tail law at the Kronecker scale; first return past the VK rung; savings on moving blocks; freezing beyond the cap; collective depth floor | sub | BAG, PTT, TAPO, TTPO, CDGeo |
| B106 | A correspondence on the orientation cover with bounded local indices | RH | MC, HAT |
| B110, B126, B127 | Thick crude count; a one-sided bound on a sampling set; positive-measure lag recurrence | AAL | WL, ZCG, ACS, IWT |
| B145 | The signed centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] | ZCG, BAG, ELT |
| B148 | The transfer of candidate S3 | ≥B56 | S3, BAG |
| B150 | A form factor bounded by `4` on `(1,10/9)` | sub | census |
| B64, B65, B98, B113 | Signed pair information beyond bandwidth one; genus upper law; count distance against a finite top layer; Möbius × quarter-disc remainder | sub / method / beyond RH | census, ACS, RAC, PM |

### Γ — selection, reflection, transport, count
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13 | Finitely many off-line zeros ⇒ none | sub | whole programme |
| B138 | Landing for ζ | sub | ZCG, LA, ELT, HF |
| B141 | Deuring–Heilbronn for ζ: `¬AAL⇒ZAL` | sub | BAG, ZCG, ELT |
| B83 | AAL = B13 ∧ Landing ∧ DH | sub | BAG, JAS, SC, ZCG, WL |
| B157 | **What excludes a finite stratum when both structures are present** (§2.5) | method | BAG, ZCG, ELT |
| B89, B112, B128 | A bounded aligned return at each right zero; the functional equation into vertical transport; replication | sub | BAG, ZCG, EFT |
| B153 (bounded class) | A bounded Dirichlet series on `Re s>x`, `0≤x<½`, with a zero and all its zeros among those of ξ (§2.6) | method | IRP, W1C, PTR, PM |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates | RH | PM |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a regulated horizon unitary at every cutoff with ξ as its limit (§2.7) | producer | PM |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one Hecke eigenform | indep. | PM |
| B149, B169 | Bézout for the comb pairing from a property of the object; a height or a Lefschetz path for the comb (§2.8) | RH (producer) | ACS, HF, AGZ |
| B69, B70, B77–B79, B82, B92, B93, B111, B116 | A positive physical or graph carrier; Hecke dispersion from it; `0∉E`; Rosati positivity of the window reflection; band holomorphy of `Λ(s)/Λ(s+1)`; inner-field decay; rotated relations; `ZAL⇒RH`; linear AAL at one slope | as recorded | PM, W1C, PTR, ZCG, LA, HF, ACS, BAG, CTF, WL |
| — | ZAL | ≥qRH | whole programme |

### Settled method questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B154 | The exceptional square on the conductor ladder | no gap: the trivial aperture is `log log q+o(1)`; beyond it the Liouville twist fails; the sign there is the least non-residue at the scale `log²q` | [L*]/[D] |
| B153 (Wiener class) | Almost periodic constituents | none with a zero, in a half-plane or a strip; open in the bounded class | [L*] |
| B143, B151, A92, A95 | The resolution of the minimal face | logarithmic radius; a density-matched model below it; `ΓL≤nπ`; a finite top layer needs no separation | [L*] |
| B148 (as a method question) | The strength of the transfer of S3 | it gives `Θ<1⇒Θ=½` | [L*] |
| B155 | The edge alternative of the level dichotomy at level one | does not occur: level-one positivity on large primes gives `Θ=½` | [L*] |
| A106, A107, A110 | Floors depending on the length, also at the prime logarithms; level one and the abscissa laws; B13 as an index dichotomy | AAL; AAL, B56 and RH; B13 ⇔ the supremal negative index of the comb defect on real packets is `0` or infinite, that index being the number of right zeros | [L*] |
| — | Whether the bounded-shape floor decides the sign on all tests | no: an aligned dominated system at `log log q+log 2+η` | [L*] |
| A68 | Landing with ζ's Gamma factor and count | not forced | [L*] |
| A55 | Functional-equation rigidity for prime measures | holds for countable systems; fails for positive continuous measures, which keep every zero | [L]/[L*] |
| A72, A73, A76, A71 | Counts, the upper side, absolute and signed forms with exceptions, local tensor moments on logarithmic windows | equivalences with RH | [L*]/[K] |
| A83 | A counter-configuration with ζ's density | exists | [L*] |
| A56 | Prime two-bump signs from a verified height | every prime below a rung tending to infinity | [L*] |
| A90, A98, A99 | The flow criterion in prime form; feasible weights at every aperture; the tower as a completed-zeta quotient with its floor | theorems | [L*] |
| A97, A100, A101 | Multipoles and chain squares; the trivial aperture with a uniform constant; Deuring–Heilbronn on the twisted comb | theorems | [L*] |
| A96 | The first selective window | every ratio above `2` is selective for `w(2)`; the feasible interval is bounded and contains a neighbourhood of `log 2`; its end points are A117 | [L*] |
| A91 | The square of a number ring | abelian rings: exact index, Riemann–Hurwitz, cyclotomic combs; non-abelian rings are A116 | [L*] |
| A84 | Greedy carry-free compositions | optimal ⇔ greedy; the Newton polygon is A115 | [L] |
| A37 | Growing resonators | the mean keeps the full diagonal for `κ<2σ−1` | [L*] |
| Q20 | An object with unit masses and paid contacts | the paying ring and the planar square; restriction there is an equality of ideals | [L*] |
| — | The Möbius signs at the exceptional frequencies of one column pair | no cancellation | [L*] |
| — | Which orders of Gauss sums carry the Möbius sign locally | every odd order; no even order | [L*] |
| B140, B139, B138 (method), B85, B142, B133, A85, A87, A88, B125, A50, A65, A67, A74, (S1), (S2) | as recorded in the scoped-obstruction ledger | answered | [L] |

## 2.3 Frankenstein routes

**No assembly closes RH in the native graph.** Every assembly has an open input of RH, ≥B56, AAL or ≥qRH strength. With `[X]` one assembly has a single open input of RH strength (F23).

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F23 | **Level and signal.** JAS dressed positivity; the signal of the zeta kernel; family continuation; `[X]` | RH ⇔ level one on large primes [L*]; a half-plane ⇐ signal `O(Z^b)`, `b<1` [L*]; `[X]`: `b=7/8` | B160 for RH; B161 natively for a half-plane | one positivity statement at one level is RH with no premise; the signal receiver has power slack |
| F24 | **Escape worlds.** Bounded-window floors; levels; logarithmic windows; a half-plane | a level `σ>1` leaves the edge world; bounded-window floors leave unattained tops; a half-plane removes the edge world; level one and a floor on logarithmic windows remove all [L*]/[D] | one of them | a map of which input kills which world |
| F25 | **The ladder.** Sizes, fakes, exchange rates on both sides, the mean over the heights | the sign on a rung from a saving; isolated deep zeros excluded by the sign; the sizes fail only at aligned heights, a set of small measure [L*]/[D] | B159; clusters (B156) | one scale for every sign statement; the dark range and the rungs are one problem |
| F2 | **One inequality per prime**, with the upper side, counts and moments | Σ, Π and count readings are one number per prime on sparse windows [L*] | B130 on one sequence of windows | one target with slack `p^{o(1)}` |
| F8 | **Finite-layer world.** Free strip, Mertens saving, filters, centred currents, half-period deletion, bounded windows | a complete receiver; level one or the S3 transfer excludes world I [L*] | B145, or B160, or B148 | world I is excluded by any input that turns a strip into the line |
| F17 | **The comb at finite scale.** Normal form, block averages, flat packets, forced data, exact index | RH ⇔ nonnegativity of an explicit family of finite matrices on step packets (A114) [L*]/[D] | B152 | the statement lives in finite rank, uniformly in the scale |
| F26 | **Covers.** Exact index of a ring; a cover bounds its base; towers | the index of one abelian ring gives RH; per degree ζ is lost [L*] | the index of a ring | support, not a route |
| F11 | **Construct, then identify.** Index semicontinuity, rigidity, sizes on a circle | a splitting with `‖E^♯‖≤‖E‖` on circles and a zero-free dominant half gives purity in the window [L*] | B146 | constituents with a zero are excluded as pieces in the Wiener class |
| F27 | **Sign-free skeleton.** Signed deletion, ordinate injectivity, recurrence against density, the jump law, half-period deletion, Turán, the digit calculus | pointwise theorems on constituents and finite layers [L*] | a sign-free source that acts on ξ | under the constraint of §2.6 the receiver is complete |
| F6 | **Regulators.** Cusp cutoff, clock, scattering tower | RH ⇔ the energy floor at one fixed height [L*] | B88, B117 | one fixed finite height suffices |
| F28 | **Source and budget.** The local sign law at odd order, the cubic identity, the planar large sieve, the budget of the detector, the continuation principle | every native brick of the half-plane receiver except the global object and the two estimates [L*] | A118; B158 | the boundary of a probe is a theorem about exponents before any estimate |
| F1, F3–F5, F7, F9, F10, F12–F16, F18–F22 | as recorded: two-world skeleton, Deligne skeleton, critical curve, horizon, rigidity, exactness, count skeleton, graded recurrence, sign-free receivers, dark range, theta wall, census, flow, remainder, existence half, resolution atlas, conductor ladder | F20 and F22 are theorems (feasible weights; the trivial aperture); the others keep their missing inputs | B104, B71, B97, B102, B150, … | — |

**Closest to the open core: F23, F25, F2, F17, F8.**

### What a contradiction search may assume in world I
`Θ<1`; isolated top `β`, attained; `M(x)=O(x^{β′})`; the prime error is a finite oscillation at the top plus a smaller remainder; every late window of length `(k+1)π/67` holds a point below every floor [L*]; filters read each top residue; centred type-II currents on polynomially many cofactors [K]; fewer than `T^c` separated returns to a small disc at a zero right of `σ`; in world I-a the negative index of the pairing is finite, even and equal to the number of right zeros [L*]; level-one dressed positivity fails [L*]. No contradiction comes from exact identities alone, from positivity, Euler products, integrality or counting alone, from the functional equation with ζ's Gamma factor and count, or from any statement in law [L*]/[L].

## Validation tests for 2.4–2.8 and 3

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH; for §2.5 and §3 also not implying AAL; or a method question implied by nothing about ζ's zeros |
| T2 | Answered by proving or refuting a stated inequality, identity or implication |
| T3 | A named consequence for either answer |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake, or calibrated on the fakes |
| T6 | Names an input not refuted in Lean |
| T7 | Moves a wall; not a shape already answered |
| T8 | Not a named long-standing problem in disguise; a first step in corpus objects with one named obstacle |

**No statement about the zeros of ζ below RH, quasi-RH and AAL passes all tests as a door.** Pointwise statements below rung one are sizes; at rung `1+o(1)` both one-structure fakes fail; mean values below the height are stable under relocation of finitely many zeros; the structural questions about receivers are answered in Lean (§2.2, settled); the atoms have no model among Dirichlet series over the integers. The questions below are method questions and producer questions; each states its failed tests.

## 2.4 Breakthrough question below RH and quasi-RH: does the pole channel see every failure first?

**Question (B104).** *If RH fails, is every critical half-line ground state charged?* At the critical curve exactly one of three cases holds: RH; ¬RH with `R_polar<W`; ¬RH with `R_polar=W` finite, a critical half-line ground state at `W` and every such state orthogonal to the polar source [L*]. Is the third case empty?

**What is proved [L*]/[L].** `R_polar=R_halfline`; a ground state with nonzero polar pairing forces `R_polar<W`; `R_PD=R_PSD=R_polar≤W=R_prim=R_high`; no countable square-bounded family of holomorphic multipliers dominates the depleted kernel.

**What either answer gives.**
| Answer | Effect |
|---|---|
| The third case is empty | ¬RH ⇒ the complete matrix fails strictly before the windows; RH ⇔ `R_polar=W`; the five routes that meet at the critical curve (HF, SRT, AIP, ACS, SC) have one inequality with a rank-one payment [D] |
| A polar-orthogonal ground state is consistent | a failure mode that the pole channel does not see; at such a threshold the complete matrix carries no information beyond the windows |

**First step and obstacle.** The lattice with one pair of depth `δ` of the ladder has an explicit sign change at the rung `1/(2δ)` and an explicit critical direction of the shape `sinh(δu)e^{iγu}` [L*]/[D]; its polar pairing is a closed integral. If it vanishes for no depth and ordinate, the third case is empty on that class, and the statement to prove is that a critical ground state of a configuration with ζ's pole is a limit of such directions. Named obstacle: the Euler–Lagrange equation of the truncated form at `W` contains the full zero side; positivity of a ground state gives nothing, because the pole moments are not of jump type [D].

**Tests.** T1: vacuous under RH; implies no width. T2–T4: pass. T5: calibrated on the isolated-pair lattice. T6, T7: pass (Σ135, Σ139). T8: not a named problem.

**Limit.** Confined to the critical curve; it produces no sign.

## 2.5 Breakthrough question below AAL: what excludes a finite stratum when both structures are present?

**Position.** AAL ⇔ B13 ∧ Landing ∧ DH [L*]. Each calibration in the corpus drops a structure (§1.3), and among Dirichlet series over the integers the two structures leave ζ alone [L]. So no mechanism for an atom can be tested inside the corpus. One classical family has both structures and a finite stratum.

**The calibration [C].** The Selberg zeta function of a finite-area hyperbolic surface is an Euler product over the primitive closed geodesics, with norms `e^{ℓ}`, and has a functional equation. Its nontrivial zeros are `s=½±ir_n` for the eigenvalues `λ_n=¼+r_n²` of the Laplacian: on the line, except the finitely many eigenvalues `λ_n<¼`, which give real zeros in `(½,1)`. Surfaces with such eigenvalues exist in every genus. In this family ZAL and Landing hold, and B13 fails. For congruence groups the stratum is empty below `3/16`: a theorem of the corpus [L] (`selberg_three_sixteenths_congruence`), with Weil's bound for Kloosterman sums as its arithmetic input; the conjectured emptiness is Selberg's eigenvalue conjecture.

**Question (B157).** *Which hypothesis on an object with an Euler product and a functional equation excludes a finite nonempty stratum, and does the mechanism that proves it act on a finite top layer of ζ?* Three mechanisms empty a stratum, fully or partly, where both structures are present [C]: square-root cancellation over finite fields fed through a sum formula (Kloosterman sums; `3/16`); an archimedean parameter common to a family of twists against non-vanishing on average over the family; expansion in the finite quotients.

**What is proved in the corpus.** A finite top layer of ζ is a finite datum read by prime filters, seen on bounded windows, with a finite even index [L*]/[L]; the Deuring–Heilbronn phenomenon on the twisted comb: a real zero near `1` clears the strip below a height and is isolated on odd packets [L*]; graded repulsion is refuted for Euler products without functional equation [L*]; Landing is refuted for the functional equation without Euler product [L*].

**What either answer gives.**
| Answer | Effect |
|---|---|
| A hypothesis satisfied by ζ and violated by the Selberg family is identified (integer norms with unit gaps, order one, a Hecke symmetry), with a proof scheme | the first mechanism for an atom that can be run on a family where it must fail and on one where it is a theorem; B13 becomes a statement of the type of a spectral gap, with `3/16` as its calibrated instance |
| Every scheme that proves B13 for ζ is shown to prove it for the Selberg family | the scheme is refuted before it is attempted; the instrumentation of world I (ELT) is confirmed to be a receiver |

**First step and obstacle.** State the calibration in Lean at the level the corpus uses: a discrete multiplicative system of real norms, an Euler product, a functional equation with a meromorphic factor, zeros on the line except a finite real set (A120); at finite rank the corpus has it (impure curve data with integral counts and a functional equation [L]). Then run each world-I instrument on it: the filters, the bounded-window theorem and the index count apply verbatim to a real stratum of one zero. Named obstacle: the zeros of ζ are resonances of the modular surface at `Re s=β/2<½`, not eigenvalues; the family is a calibration by analogy of structure, not a transport.

**Tests.** T1: a method question. T2: passes for the calibration and for each scheme; the question as a whole is a research direction, not one inequality. T3, T4: pass. T5: built on a fake that keeps both structures. T6: not refuted. T7: moves Γ184, Γ219. T8: the emptiness of the stratum for congruence groups is Selberg's conjecture; the question does not ask for it.

**Limit.** It decides what a proof of an atom may use; it proves no atom. The sector off the RH path remains B141 (`¬AAL⇒ZAL`); it has no first step.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form, automorphic spectral theory included; "positivity" includes nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, continuation, power sums, integrality, recurrence, the argument principle.

**What survives [L*]/[L].**
- *Receivers.* RH ⇔ `|c_p|≤K` on windows, by complex deletion filters; RH ⇔ the ordinate is injective on the zeros; the upper side alone on logarithmic windows is a bound, not a sign of a form.
- *Conversions from a law to a point.* Recurrence against density (constituents); budget overflow (long mollifiers); winding and sign changes (the index law; half-period deletion; sizes on a circle); the rightmost zero of a family against a mean square over its twists (`[X]`).
- *The additive identity.* The jump of the fractional part: the jump law on strips, with summable poles, and its form as the law of the carry.
- *Priced producers.* Frobenius at one prime; integrality; exponential sums; the digit calculus of the Carlitz–Goss zeta function with its greedy optimum.
- *The local sign law.* `g(χ)^n≡−card F` for odd `n`: an identity in a cyclotomic ring, with no sign of a form and no operator.

`[X]` under the constraint [A]: its estimates are large sieves used as bounds and its identity is algebraic, but its global object, the cubic theta function, is a residue of an Eisenstein family on a cover. The strict reading removes it.

**Verdict.** Under the constraint no statement about ξ below quasi-RH passes the tests. Two questions remain, one with a first step and one that would restore a source of half-planes.

**Question with a first step (B153, bounded class).** *Can a bounded Dirichlet series on `Re s>x`, `0≤x<½`, have a zero and all its zeros there among those of ξ?* Proved: none in the Wiener class; a bounded constituent has support exponent `≥1−2x`, infinitely many primes, and no absolute convergence left of the line [L*]. First step: the jump law for a left expansion that is square summable and not absolutely summable; poles with summable residues are covered [L*]. Named obstacle: Bohr's inequality gives absolute convergence only on `Re s>x+½`. Either answer: No — the zero set of ξ contains the zero set of no bounded almost periodic function, and every exact arithmetic piece is excluded; Yes — an infinite set of zeros of ξ is on the line by recurrence against density, with no sign in the proof.

**Question that restores a source (B158, non-spectral form).** *Is there a summation formula, proved by Poisson summation and reciprocity alone, whose two sides carry Gauss sums of an odd order?* Order two is elementary and carries the parity of the character; order three is the least order with the Möbius sign [L*], and its theta function is not elementary [D]/[C]. A formula of this kind is a completed sum with two representations and would give the half-plane receiver a source inside the constraint.

**Tests.** B153: T1 method; T2–T4 pass; T5 calibrated on curve zeta functions, which are their own constituents; T7 moves Γ215; T8 passes. B158: T1 producer; T2 passes; T8: the summation formulas for cubic Gauss sums are classical through automorphy [C]; a proof without it is not known to exist.

**Limit.** B153 decides what can share zeros with ξ, not where the zeros are.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L]/[L*].** The resonances of the modular horizon are the zeros of `ξ(2s)`. RH ⇔ every pulse rings down at the quarter rate ⇔ reflection positivity of the cavity forms ⇔ one cavity energy decays at `y^{¾−ε}`. Three regulators: the cusp cutoff (index at most one, limit `(s−1)ξ(2s)`); the clock (`E_r↑W`); the scattering tower, the completed-zeta quotient `Λ(s)/Λ(s+N)`. At every fixed height: corrected energy plus a nonnegative jump tail is the closed Weil form, and RH ⇔ the raw energy is at least minus its full arithmetic defect [L*]. The sign of the tail does not bound the energy [L]. No bounded critical inverse of the adelic adjacency exists [L*]. The stratum of exceptional eigenvalues of congruence quotients is empty below `3/16` [L].

**Readings [D].**
- *World I is ordinary ringdown.* A finite isolated top layer is a finite set of least-damped modes that dominates the late signal: the prime error is a finite oscillation times `x^{β}` [L]. AAL says that the least-damped modes of this horizon are not isolated.
- *RH is equal damping.* All resonances have one decay rate. Where this holds for a horizon in three-dimensional gravity it is forced by a symmetry that makes the fundamental modes of all momenta one highest-weight line, and the momenta form a lattice [C]; here the heights have no period [L].
- *RH is a saturated bound.* The zeros of `ξ(2s)` are symmetric about `Re s=¼`, so the ringdown rate is at most `¼` without hypothesis; RH says the bound is attained. A proof needs a lower bound for the relaxation rate: no slow mode.
- *The mass is a monotone parameter.* Feasibility increases with the conductor, and a floor `−K∫|F|²` is feasibility at the conductor `qe^{K}` [L*]: a mass term stabilizes every dominated system up to the trivial aperture and no further.

**The question (B117).** *Is there a regulator of the modular horizon that is unitary at every cutoff and has ξ as its limit?* A family of self-adjoint boundary conditions whose secular functions are conjugation-real, have at most one right-half zero, and converge locally uniformly to ξ gives RH [L]. The three regulators miss in two ways: a unitary one with the limit at a shifted argument; two with the right limit whose defect is a jump tail of one sign. In the form of a floor: *at one fixed height, is the full arithmetic defect the energy radiated through the horizon, so that the floor is conservation of a nonnegative total energy?* By the fixed-height theorem this is RH; the question is whether the defect, which is explicit (jump tail, Robin drift, omitted contacts), is a norm in a representation built from the places.

**Why it opens the path.** It replaces the sign of a form by unitarity at each cutoff and continuity of the limit; the identification of the limit is free by rigidity [L]. Internal modular conjugation, vacuum-fixing partners, half-sided inclusions and the invariant glued bulk are excluded [L].

**Tests.** T1: fails — a producer of RH strength. T2: passes. T5: graph black holes with `t²>4q` are impure at every size [L]; a principle uniform in the sector must stabilize the Liouville twist at rung one, which is false [L*], so it has to use the conductor or the pole. T8: not a named problem; no first step beyond the three regulators.

**Limit.** A regulator whose secular function is built from the zeros is a restatement.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*]/[L].** The arithmetic square is a curve whose graphs meet in the primes; no object of finite type carries the contacts. The pairing of the degree points has a Hodge index theorem equivalent to RH, with exact index the number of right zeros, also for abelian number rings; the counterterm obeys Riemann–Hurwitz and defines a genus `1+(n/2)log(n/2π)` at the degree point `n`, negative at `2` and `3`. Every datum of the pairing is forced. The jets are the even multipoles of the Newtonian kernel of `ℝ³` on an axis, with the two rulings at the origin and at infinity; the contacts of a prime are chain squares; the tree of `p` is glued with length `log p`. At finite scale the inequality is decided on block-constant divisors. The structures of the square return identities (§1.8).

**Readings [D].**
- *The fibre at infinity has three dimensions.* The archimedean kernel is Newtonian, not logarithmic: the object is not an arithmetic surface with a Green function of a Riemann surface, and the Hodge index theorem of arithmetic surfaces [C] does not apply to it as it stands.
- *Where that theorem gets its sign.* On an arithmetic surface the index is minus a canonical height on a Jacobian: a group, a quadratic functoriality, and a naive height bounded below by integrality. The corpus has the receiver (RH ⇔ a bounded-below naive height on every window; ⇔ `ℕ`-counts on the prime rays [L]/[L*]) and the object's own count, which is the split norm: the hyperbolic plane of the two rulings, not the defect [L*].
- *A Lefschetz path exists at one prime.* On packets of length `≤log 4` Bézout is monotone in the edge length of the tree of `2`, holds for all long trees without hypothesis, and holds for ℤ iff the threshold is `≤log 2` [L*]. For odd primes the long trees fail. Along the mass the inequality is monotone at every aperture and holds at large mass for every dominated system [L*].

**Geometric question at finite rank (B152).** *For all `K,R` and `η>0`, are there arbitrarily large block sizes at which the comb form is `≥−ηΣσ²` on the divisors constant on the `3KR` blocks of `(RB,(3K+1)RB]`?* This gives RH [L*]. The entries of the limit matrices are explicit: jump forms of flat packets, overlap lengths with the weights of the primes below `3K+1`, the two pole moments (A114). Each matrix is a finite-height statement.

**Geometric question on the source (B169).** *Is there a group with a doubling on which the defect of the comb pairing is a canonical height, or a one-parameter family of squares through that of ℤ along which the index is constant and which ends at a square where the inequality is known?* Known end points: large mass; long trees of `2` at width `≤log 4`; short windows; curves, where the form is Toeplitz and purity is its sign. Known rigidity: weights, constant, scale and the lengths of the odd trees admit no deformation [L*].

**Topological question (B106).** *Is there a correspondence on the orientation cover over ℤ with bounded local indices and Lefschetz number the number of points of the cover?* It bounds the centred count `|M(N)|` by the dimension of the middle cohomology times `N^{½}` [L]; the signed localization `Σ_p index=1−M(N)` is known [K].

**Tests.** B152: T1 fails (RH at all `K,R`); T4 fails rung by rung. B169: T1 fails (producer); T5: must fail for the Liouville twist at rung one and for a wrong constant; T8: no first step beyond the path at the prime `2`. B106: T1 fails (RH).

**Limit.** No geometric question below RH is known that the corpus has not answered with an identity.

## 2.9 New field for RH: reciprocity sources

**Does RH need a new field?** Not a further language. The languages exist as programmes: the square and its lattice (AGZ, HFP), purity at infinite rank (IRP, IRW), prices and ladders (SA), constituents (CTZ), isolated layers (ELT), families and weights (AWT), the mollified field (MZF), the horizon (HAT, AHMH). Each ends at one statement, a rung above one. What no native programme contains is a source. The one source in the repository is external: `[X]`, the continuation of the reciprocals of a family across its rightmost zeros, fed by an identity that turns Möbius coefficients into coefficients with a functional equation. Its analytic step, its receiver and the local form of its identity are in the native graph (FCT, MMD). A theory of such sources does not exist.

| Aspect | Content |
|---|---|
| What it is about | Identities that give a parity-carrying coefficient (`μ`, `λ`, `Λχ`) a functional equation, and the continuation of reciprocal families that they feed. A **source** is a completed sum with two exact representations: one bounded directly, one whose principal row is the reciprocal of the target |
| What it is like | A theory of budgets before estimates: for each source the boundary of the half-plane as a function of the exponents of its large sieves, proved as a theorem about exponents; then the estimates. Its calibration objects are the two fakes of the ladder |
| Established | The continuation principle for a family and for ζ; the signal as a Möbius sum; the cube identity over `ℤ[ω]`; the local sign law: every odd order, no even order; the nonzero cubic Eisenstein residue with its transport; the planar large sieve; the budget of one detector: `7/8` at every redistribution, `29/36` with the unit term alone, `5/6` iff `ν≤1/15 ∧ κ+4ν≤4/3`; no cancellation over the exceptional frequencies of one column pair [L*]/[L] |
| Criteria for a source | P1 it fails for the Liouville twist and for the lattice with a pair at the same rung. P2 it uses the functional equation and the Euler product jointly, through a family closed under the twists that its summation formula produces; a strip of one function does not improve itself [L]. P3 uniform in the conductor, it removes exceptional zeros; else it uses the pole or the identity of the prime torus. P4 its direct bound holds for the actual coefficients, not for every array of norm one, wherever the budget needs a saving. P5 its boundary is a theorem about exponents. P6 it is pointwise in the zeros. P7 over `𝔽_q[T]` it reproduces square-root cancellation with Weil's bound in the place of the large sieve |
| Questions it must answer | Which odd orders, ranks and base fields have a global object whose coefficients are the Gauss sums of the local law (B158)? What is the boundary `b(n)` of the order-`n` probe, and is its infimum `½` (§3)? Where the mean square is followed by Cauchy–Schwarz the boundary stays above `½`: which sources have cancellation inside the mean square? Is there a source for ζ alone that uses the pole? |
| Tools it develops | Summation formulas for Gauss sums of higher order; large sieves over rings of integers with residue symbols; budget calculus; the continuation principle with explicit margins; the ladder as the measuring instrument |
| Objects | Sources, completed sums, rows and columns, exceptional frequencies, budgets, boundaries, families closed under twists |
| Language | source, probe, boundary, budget, slot, exceptional frequency, signal, leg |
| Mechanisms | Built on: FCT, MMD, SA, the budget modules. To discover: a second source, or a proof that the class of Gauss-sum sources has an infimum boundary above `½` |

**Main conjecture.** For every `σ₀>½` there is a source with boundary below `σ₀`. **Milestones.** M1 `[X]` in the native graph (A118). M2 the boundary of the order-`n` probe as a function of `n` (§3). M3 a second source. M4 a boundary below `3/4`. M5 every boundary.

**Status [A].** The field has one theorem, external and unchecked here, and native bricks. If `[X]` fails, the field has no theorem and the native statement of §1.12 stands: every route is a receiver.

## 2.10 New field for AAL: gap theory of finite strata

**Does AAL need a new field?** Yes. The instrumentation of world I exists (ELT, ZCG, SOSZ): filters at every speed, centred currents at growing order, the bounded-window theorem, the exact index. Its residual is the exclusion itself (B145). What does not exist is a theory of when an object with both structures has a finite stratum and of what removes it.

| Aspect | Content |
|---|---|
| What it is about | Finite strata of zeros off the line in zeta functions with an Euler product and a functional equation: where they occur (Selberg zeta functions of surfaces with small eigenvalues [C]; impure curve data [L]), where they are excluded by a theorem (congruence quotients below `3/16` [L]), and what the exclusion uses |
| What it is like | The theory of exceptional eigenvalues, read as a theory of B13: a stratum is a finite datum; it is excluded by arithmetic, never by the two structures alone; partial exclusion is a gap |
| Established | The sector theorem; the three calibrations of the atoms with one structure; the bounded-window theorem; the exact, even index of world I-a; Deuring–Heilbronn on the twisted comb for a real stratum of one zero; `3/16`; a level-one positivity or a strip transfer excludes world I [L*]/[L]/[D] |
| Criteria | Fail on Selberg zeta functions with a small eigenvalue. Reproduce `3/16` on congruence quotients. Fail on integer-norm Euler products and on the paired ξ model. Treat a quartet as two squares and a real zero as one. Not be a statement in law. Use an arithmetic input beyond the two structures and name it |
| Questions it must answer | Which hypothesis excludes a finite stratum (B157)? Is world I-b empty (B141)? In world I-a, does a finite even index force a relation among the top residues? Is there a sum formula in which a top layer of ζ appears with a sign, as an exceptional eigenvalue appears in the Kloosterman side? What bounds the near-diagonal cofactor pairs (A86, B145)? |
| Tools it develops | Finite-layer filters; half-period deletion; the twisted comb; calibrations with both structures; sum formulas with a finite-field input |
| Objects | Strata, layers, tails, gaps, exceptional squares, calibrating families |
| Language | stratum, gap, layer, sector, exceptional, calibrated |
| Mechanisms | Built on: the instrumentation, the sector theorem, the gap theorem for congruence quotients. To discover: an arithmetic input that acts on a non-real layer of ζ |

**Main conjecture.** An object with integer norms, order one, an Euler product and a functional equation has no finite nonempty stratum. **Milestones.** M1 the calibration with both structures in Lean (A120). M2 the instruments run on it. M3 the hypothesis that separates ζ from it. M4 B13. M5 AAL.

## 2.11 New field for RH without positivity: conversion theory with non-spectral sources

**Does a positivity-free RH need a new field?** Yes. The corpus proves much in law and RH is a statement at every zero of one rigid object. The sign-free mechanisms that turn a law into a point exist in five programmes (CTZ, IRP, CDG, SOSZ, SFPM) and no programme owns them as a subject.

| Aspect | Content |
|---|---|
| What it is about | Conversions: an amplification of one exception and a law that the amplified exception violates. Their exponents, their domains, their prices; and sources that need no spectral construction |
| The conversions | recurrence against density (a zero of an almost periodic object recurs; deep zeros have density zero); budget overflow (one off-line zero costs `Y^{2δ}` against a budget `T`); winding and sign changes (index; half-period deletion; sizes on a circle); the rightmost zero of a family against a mean square over its twists (`[X]`, by the narrow reading) |
| Established | No constituent with a zero in the Wiener class; the jump law with summable poles; the law of the carry; the long-mollifier trap; the half-period law; finite layers on bounded windows; RH ⇔ `\|c_p\|≤K` on windows; ordinate injectivity; the greedy optimum of the digit calculus; the local sign law at odd order [L*]/[L] |
| Criteria | No sign of a form and no operator. Reprove the conversions as one scheme with exponents. Over `𝔽_q` reduce to periodicity of the zeros in height. Fail on integer-norm one-offs (finite exceptions do not recur) and on `ζ(s−h)`. State the exchange with length: which conversions stay below the height |
| Questions it must answer | Is there an amplification of one zero that is unconditional below the height? Does recurrence against density extend to the bounded class (B153)? Which splittings of ξ have sizes on circles and an arithmetic count of the zeros of the dominant half (B146)? Is there a summation formula for Gauss sums of odd order without automorphic input (B158, non-spectral form)? What replaces the carry-free calculus when the carry is a nonzero class? |
| Tools it develops | Recurrence against density on strips; the jump law; half-period deletion; Turán's power sums; budgets for long polynomials; reciprocity in cyclotomic rings |
| Objects | Exceptions, amplifications, budgets, constituents, defects, carries, sources |
| Language | law, point, exception, amplification, budget, overflow, constituent, carry |
| Mechanisms | Built on: the conversions above. To discover: a conversion that reaches ξ below the height, or a proof that none exists in the class of quadratic mean values, from relocation invariance |

**Main conjecture.** Every sign-free conversion of a law about the zeros of ζ into a statement at every zero has an input of the strength of the rung that it produces, or acts on a family through a reciprocity identity. **Milestones.** M1 the conversions in one scheme. M2 the bounded class. M3 a no-go below the height for quadratic mean values. M4 a non-spectral source.

## 2.12 New field for RH as AdS physics: relaxation theory of arithmetic horizons

**Does it need a new field?** Yes. The receivers and the regulators exist (BHR, ASH, AHMH, CTH, HAT). A cutoff either keeps unitarity and moves the limit, or keeps the limit and loses the sign by a jump tail; at every fixed height the floor is RH [L*]. What physics would have to supply is a lower bound for the relaxation rate.

| Aspect | Content |
|---|---|
| What it is about | Horizons whose resonances have a reflection symmetry, so that the relaxation rate is bounded above by a symmetric value, and the question when the bound is attained: no slow mode. Sectors labelled by a conductor, in which the conductor is a mass |
| What it is like | A stability theory at a bound with no margin: instability, if any, appears at an aperture, as a finite set of least-damped modes (world I) or as modes approaching the bound (world II) |
| Established | Ringdown, cavity and Krein receivers; three regulators; the tower as a completed-zeta quotient; the fixed-height floor; the mass stabilizes every dominated system to the trivial aperture and no further; the gap `3/16` for the bound states of congruence quotients [L*]/[L] |
| Criteria | Built from the places and the horizon, never from the zeros. Unitary at every cutoff with ξ as limit, or a stability argument on the limit. Impure for graph horizons with `t²>4q`. False for the Liouville twist at rung one: so it uses the pole or the conductor. No margin |
| Questions it must answer | Which regulator is unitary at every cutoff with ξ as its limit (B117)? Is the full defect at a fixed height a radiated energy? What symmetry would make the resonances one highest-weight line when the heights have no period? Is there a horizon of this family with a finite set of least-damped modes, as a calibration of world I? What selects the Shimura nonvanishing for one eigenform (B147)? |
| Tools it develops | Maass–Selberg calculus at general cutoff; the scattering tower; Green damping; the index law; the ladder with mass |
| Objects | Horizons, cutoffs, towers, defects, sectors, masses, least-damped modes |
| Language | regulator, defect, relaxation rate, slow mode, sector, mass |
| Mechanisms | Built on: the regulators and receivers. To discover: a no-slow-mode principle for a jump form with a pole |

**Main conjecture.** The relaxation rate of the modular horizon attains the bound set by its reflection symmetry. **Milestones.** M1 the regulators and the fixed-height floor. M2 a calibrating horizon with isolated least-damped modes. M3 the defect as an energy. M4 a universal positive rate. M5 the bound.

## 2.13 New field for RH as topology or geometry: Lefschetz paths and heights in infinite type

**Does it need a new field?** The lattice and index theory exists (AGZ, HFP), with the genus, Riemann–Hurwitz, the exact index and the finite-rank reduction; a Kähler package without a variety exists except at the top coprime stratum (HWV) [L]. No theorem obtains the Hodge index of the square from its geometry at unbounded scale, and every structure tested returns an identity (§1.8). The two mechanisms that produce a Hodge index without a classical surface are not built.

| Aspect | Content |
|---|---|
| What it is about | Two sources of an index theorem in infinite type. A **height**: a group, a doubling and a naive height bounded below by integrality, with the defect as its canonical limit. A **Lefschetz path**: a one-parameter family of squares along which the index is constant, ending where the inequality is known |
| What it is like | Arithmetic surfaces get the index from a height; combinatorial Hodge theory gets it from a path along which no zero mode appears [C]. Over ℤ the first has a receiver and a hyperbolic count, the second has a path at one prime |
| Established | RH ⇔ a bounded-below naive height on every window ⇔ counts on the prime rays; the split norm; the tree of `2` as a monotone path below `log 4` with threshold `ℓ*(L)`; monotonicity in the mass; rigidity of weights, constant, scale and odd tree lengths; the three-dimensional fibre at infinity; finite rank on block-constant divisors; the forced genus [L*]/[L] |
| Criteria | Reproduce curves: no jets, no counterterm, a window of `2g+1` points. Fail for an integer-norm system on its own comb, for the Liouville twist at rung one, for a wrong constant. Not a section count. Selective only where a contact enters. On a number ring give the index of each character |
| Questions it must answer | Which group carries the height (B169)? Is there a path for an odd prime, where long trees fail? Does a zero mode along the mass path have a geometric meaning? Is the block-constant lattice the lattice of an object for which an index theorem is known? What is the three-dimensional object whose leafwise pairing is jets plus contacts with the density as counterterm, given that no invariant glued kernel exists? |
| Tools it develops | Canonical limits of counts; monotone parameters; block lattices; trees with lengths; Newtonian multipoles; local-to-global arguments at the top stratum |
| Objects | Combs, block lattices, trees, masses, heights, paths, zero modes |
| Language | height, doubling, path, threshold length, zero mode, block lattice |
| Mechanisms | Built on: the comb lattice, the tree of `2`, the mass. To discover: one property of the square that is an inequality |

**Main conjecture.** The square of ℤ lies on a path of squares with constant index whose other end is a square with Bézout. **Milestones.** M1 the paths at `2` and along the mass. M2 the limit matrices on step packets (A114). M3 a path at an odd prime or a proof that none exists. M4 a height. M5 Bézout.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a product with itself and the inequality of Castelnuovo and Severi on that product is a theorem. The programme is `AbsoluteGeometryOfSpecZ` with `HodgeTheoryOfAFixedPart`; `SelectiveArithmetic` is its test bench.

**What the corpus fixes.**
| Item | Theorem | Evidence |
|---|---|---|
| The square | `𝒢=W(ℤ)`: Frobenius graphs glued along the primes; a curve; gluing index `N!`; no finite type | [L] |
| Paid contacts with unit masses | the paying ring (graphs are lattice points with coordinates `p+…+p^{v_p(n)}`) and the planar square; forced values `ΠJ(m,n)`, attained | [L*] |
| The pairing | jets + contacts − counterterm `→2d₁d₂−Z(f)`; Bézout ⇔ RH; index = number of right zeros | [L*] |
| Forced data | `Λ`, the constant `2π`, scale one, tree lengths `log p`, the exchange law `c≥sup P_δ` | [L*]/[L] |
| The fibre at infinity | even Newtonian multipoles on an axis of `ℝ³`; the rulings at the origin and infinity | [L*] |
| The finite fibres | chain squares minus the diagonal at each prime | [L*] |
| Frobenius | a power map is a Frobenius at one prime; order `m` on `S` costs `m·θ(S)` | [L] |
| Carries | a cocycle that is not a coboundary; the jump law on a strip is the law of the carry | [L]/[L*] |
| Sections | the product formula on the tower; an equality of ideals on the planar square | [L]/[L*] |
| Counts | on two graphs the split norm | [L*] |
| Number rings | contacts `Λ(1+ΣRe χ_i)`; Riemann–Hurwitz; exact index; a cover bounds its base; in a tower the base has weight `1/d` | [L*] |
| Integer-norm systems | on its own comb the system of the squares fails Bézout | [L*] |
| Curves | the comb `q^ℤ`: Toeplitz form, decided on `2g+1` points | [L] |
| Twisted parts | positive below the trivial aperture for every dominated system; no information on the character there | [L*] |

**What it would be like [D].** Spec ℤ over `𝔽₁` is a curve of infinite genus with a genus function. Its Frobenius is a monoid at the finite places and a flow at infinity; no map is a Frobenius at two primes. Its square is of infinite type; the prime part of an intersection number is a contact order, the archimedean part a multipole in three dimensions, the diagonal a density. Passing from `𝔽_p[T]` to ℤ is a deformation by the carry, which `𝔽₁` does not remove. Extensions of the base are covers with ramification, and ζ is the fixed part of every family of covers.

**State of the constructions.**
| Construction | Deliverable | State |
|---|---|---|
| I. A Lefschetz operator or path on the comb lattice | Hodge–Riemann at a base point and a transport that is not RH | dilation, overlap flow and coupling Laplacian: hard Lefschetz ⇔ RH [L]; the tree of `2` is a monotone path below `log 4` [L*]; odd trees fail [L*] |
| II. The archimedean fibre glued to the trees | the comb form as a glued form | invariant gluings refuted [L]; along the comb every free parameter is forced [L*] |
| III. Stepanov on the planar square | a small section vanishing on a window | closed: the forced value is the product of the contact ideals and is attained [L*] |
| IV. Squares of towers | the index law per degree | closed: the base has weight `1/d` [L*] |
| V. The own comb | Bézout for an integer-norm system on its comb | closed: fails for the squares [L*] |
| VI. A count | natural numbers on the rays `Γ_1+Γ_p` with quadratic Tate limit | the object's count is the split norm [L*]; counts on surviving prime rays ⇔ RH [L*]; no definition without the form |

**Criteria.** C1 reproduces Weil and Stepanov for curves. C2 counts alone are not enough (the golden datum). C3 uses the functional equation: integer-norm one-offs fail, the Liouville twist fails at rung one. C4 uses the Euler product: `cosh` models, the heat family, the lattice with a pair fail. C5 sees the exact normalization. C6 infinite type. C7 the diagonal is the density of a comb. C8 positivity is derived, and not from a section count. C9 selective only where a contact enters; no margin. C10 on a number ring it gives the index of each character, or uses the pole plane. C11 below the trivial aperture it proves nothing that the dominated box does not have. C12 at finite scale it is a statement on block-constant divisors.

**Questions the programme must answer.**
1. Bézout from a property of the object (B149); a height or a path (B169).
2. The block-constant form at every `K,R` (B152); its limit matrices (A114); the converse (A80).
3. Hecke characters, ideals as degree points, one non-abelian ring (A116).
4. A count with the pairing as its limit (B87).
5. The Li ladder as comb forms of tails (A82).
6. A path at an odd prime, or its impossibility.

**Tools.** Witt vectors and Λ-structures; necklace coordinates; comb finite parts and the normal form; Hardy squares, chain squares, multipoles; the index law; combs of norms; the ladder.

**Order of work [A].** A114; a path at an odd prime; A116; a count. **Decisive test.** A construction whose Bézout holds for an integer-norm system with an off-line pair, for the Liouville twist at rung one, or for a wrong constant, is wrong [L*].

## 3. The one big question: what is the boundary of the order-`n` probe?

**Why not a question about ζ.** No statement about the zeros of ζ below AAL and quasi-RH passes the tests (§2.2 settled; the verdict before §2.4). The native corpus has every receiver and no producer. The repository holds one producer, `[X]`, external and unchecked here; its boundary `7/8` is a floor of its probe: the exponent budget is a theorem [L*], and the Möbius signs at the exceptional frequencies of one column pair carry no cancellation [L*]. A lower boundary needs another probe.

**The source in the native graph.** The algebraic part of the source is a sign law at every order [L*]: for a character of odd order `n>2` on a finite field, `g(χ)^n≡−card F mod (μ−1)²`; for even order the sign is the parity of the character. So for every odd `n` the `n`-th power of the `n`-th order Gauss sum of a squarefree modulus is Möbius times a multiplicative factor, and order three is only the least instance.

**Question (B158, budget form).** For an odd order `n≥3`, let a **probe of order `n`** be a completed sum over a ring containing the `n`-th roots of unity, averaged against residue symbols of order `2n` and the target, with two exact representations: the reflection of the coefficients of a theta function of order `n`, and Poisson summation in the averaging variable, whose principal row is the reciprocal of the target.
1. *For which odd `n` does a global object exist whose coefficients are the Gauss sums of the local law?*
2. *What is the boundary `b(n)` of the half-plane that the probe gives, as a theorem about the exponents of its large sieves?*
3. *Is `inf_n b(n)=½`, or is it bounded away from `½`?*

**What is known.**
- `n=3`: the object is the cubic theta function, the residue at `4/3` of the cubic Eisenstein family; the residue is nonzero and its transport is in Lean [L]; its coefficients as Gauss sums are an open item of the native graph (A118). `b(3)=7/8` by `[X]`, a floor of the probe [L*], with no boundary below `7/8−1/4000` under its row-count law [L]; `29/36` if the exceptional term is absent; `5/6` needs a Gram profile with `ν≤1/15` [L*].
- `n≥5` [C], to be checked: on the `n`-fold cover of `GL₂` the coefficients of the theta function are not determined by Gauss sums for `n≥4`; uniqueness of Whittaker models, which gives Gauss-sum coefficients, holds for theta functions on the `n`-fold cover of `GL_{n−1}` and `GL_n`. A probe of order `n` then lives in rank `n−1`, with summation formulas and large sieves of that rank.
- The pole of the order-`n` Eisenstein family is at `1+1/n` in the normalization in which the cubic one is at `4/3` [C]; the exponents `4/3`, `5/6`, `11/12`, `7/8` of the cubic budget are functions of this number [A].
- The continuation principle, the receiver for ζ, the planar large sieve and the lattice sum of the base ring do not depend on the mechanism of one order [L*]/[L].

**What either answer gives.**
| Answer | Effect |
|---|---|
| `b(n)→½` | RH by half-planes in the limit of the orders, each order with its own estimates; level one is not needed; the programme of sources has a definite ladder, and the first target is the order with the first boundary below `3/4` |
| `inf b(n)>½` | half-planes through Gauss-sum probes stop above the line by a theorem about exponents; RH needs level one (`JasDressedPSD 1` on large primes) or a source of another kind; the routes that wait for a half-plane premise (S3, JAS, WL, MC) receive at best that infimum |
| no global object for `n≥5` | the cubic identity is isolated; `7/8` is the end of this mechanism unless the mean square of the cubic probe is replaced |

**Why this question.** It is the only place in the repository where a producer exists, and the question asks for its extent before any estimate: a classification and a budget. It is below RH, AAL and quasi-RH in kind: items 1 and 2 are statements about objects and exponents, proved or refuted without any information on zeros. Its answer decides whether the half-plane route can reach the line, which is the premise of four routes.

**First step and obstacle.** Write the budget of the cubic detector with the order as a parameter: slot length, Gram exponent, principal shift, the count of exceptional frequencies (`n`-th and `2n`-th powers in place of cubes and sixth powers), keeping the shape of `fixed_slot_boundary` and `retunedBoundary_sharp_minimum` [L*]; this gives `b(n)` conditional on the existence of the object and on large sieves of the same strength. Named obstacle: the global object for `n≥5` lives in higher rank [C], where the summation formula and the planar sieve are not the ones in the corpus.

**Tests.** T1: a method and producer question, implied by nothing about ζ's zeros; item 3 with the answer `½`, together with all the estimates, is RH. T2: passes for items 1–3 as statements about objects and exponents. T3, T4: pass. T5: every probe must fail for the Liouville twist and for the lattice with a pair; a family closed under twists is forced. T6: the cubic case is `[X]`; nothing is refuted. T7: moves Π158, Π159. T8: not a named problem; its inputs from the theory of theta functions on covers are classical and unchecked here.

**Dependence.** The question rests on `[X]`. If the native formalization (A118) fails, no producer exists, and the question to ask is the first failing estimate with its exponent.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| Polar orthogonality (B104, §2.4) | the critical curve becomes one inequality | native; passes; produces no sign |
| What excludes a finite stratum (B157, §2.5) | a calibration with both structures for the atoms | native; a method question; proves no atom |
| Constituents in the bounded class (B153, §2.6) | every exact arithmetic piece excluded, or an infinite pure subset | native; passes; decides constituents, not zeros |
| Clusters on a rung (B156) | whether the sign on a rung is a strip | No at the level of configurations is expected (A105); for ζ it needs both structures |
| `JasDressedPSD 1` (B160); the comb form on block-constant divisors (B152); a regulator unitary at every cutoff (B117); a height or a path (B169) | RH | producers of RH strength |
| Deuring–Heilbronn for ζ (B141); B13; Landing | atoms | no first step |
| `Θ<1⇒Θ=½` (B56); the transfer of S3 (B148); the signed centred current (B145) | AAL and more | fail T1 |
| Depth density `o(T)` (B57); a bounded form factor (B150) | first near-line inputs past the diagonal | census problems |

## 4. If every route is a receiver: a research programme

**Assumption.** Every one of the 38 formulations is an equivalence with an open input, and no producer exists. `[X]` does not change this section: its mechanism has a floor (§4.1), so even as a theorem it reaches neither AAL nor the line.

**Guidance adopted for the programme.** A mechanism for the asymptotic abscissa law has to work for every `Θ=½+δ` with `δ>0` arbitrarily small. This excludes every method whose conclusion stops at a boundary, large-sieve methods among them. What is needed is an inequality without a floor, by a mechanism of another kind than `[X]`.

### 4.1 The floor of a mechanism

The **floor** of a mechanism is the least depth `δ=Re ρ−½` at which it can exclude a zero. A mechanism with a positive floor cannot prove AAL, B13 or RH, whatever its constants.

| Mechanism | Floor in the depth | Evidence |
|---|---|---|
| Sizes of the contacts (the dominated box) | `½`: rung one; both one-structure fakes fail at `1+o(1)` | [L*] |
| Positivity of Dirichlet coefficients (the pole against a zero; `3+4cos+cos2`) | `½`: every nonnegative combination of logarithms of shifts of ζ contains the unshifted one with a positive coefficient and has the pole at its abscissa | [D] |
| Exponential sums (Vinogradov–Korobov) | `½−o(1)` | [L] |
| Density theorems as exclusion (graded recurrence with exponent `(30/13)(1−σ)`) | `1/15`: the exponent is `≥1` for `σ≤17/30` | [L] |
| Mean square over a family followed by Cauchy–Schwarz (the detector of `[X]`) | `3/8`; `11/36` with the unit term alone; exact in its budget, and with its row-count law not below `3/8−1/4000` | [L*]/[L] |
| A dominant half made of a shifted ξ (pencils `ξ(s+h)±ξ(s−h)`, cosine producers) | `h=½`: it transports the trivial zero-free region | [L] |
| Bilinear statements (Type I, Type II norms) | none reached: invariant under the Liouville twist | [L*] |
| Mean values of length below the height | none reached: stable under relocation of finitely many zeros | [L] (ledger) |
| Verification | no floor in the depth; a floor in the height | [L*] |
| The sign of Weil's form; the level-one sign of the dressed aggregate on large primes; an exact count; the parity of an index | no floor | [L*]/[L] |

Consequence [D]: every estimate that is a size, a mean value, a coefficient positivity or a large-sieve budget is out, for a structural reason and not for lack of strength. What remains has no floor because it is exact.

### 4.2 Inequalities without a floor

RH is in every formulation the missing direction of a one-sided inequality whose other direction is a theorem: `Θ≥½`; the inner mass `I≥0`; the ringdown rate `≤¼` [D]; the negative index `≥0`; the de Bruijn–Newman constant `≥0` [C]. An estimate with a floor proves the missing direction above its floor only. Four kinds of inequality have no floor [D]/[C].

| Kind | Why it has no floor | Where it proves a theorem [C] | Receivers of the corpus that accept it |
|---|---|---|---|
| (a) **Homogeneous**: some constant suffices | scaling turns any bound into the sharp one | Tate's limit for heights | a uniform floor `W(f)≥−C∫f²` over all packets, any `C` [L*]; floors on windows of every bounded length, any `K(L)` ⇒ AAL [L*]; the cofinal Möbius moment with one power [L*]; a floor `−Kp^{ε}` for every `ε` on logarithmic windows [L] |
| (b) **Unit gap**: an integer below one is zero | discreteness | Stepanov; verification; the argument principle | `ℕ`-counts on prime rays [L*]; index at most one for approximants [L]; at most one zero right of a line gives none, the zeros of the strip being non-real [D]; the sub-unit gate of TG [L] |
| (c) **Equality case**: a certificate for an extremal problem | a feasible point proves the optimum exactly | linear programming bounds with a magic function | some feasible weight system at each aperture, not `Λ` [L*]; a mollifier with budget below `1+ε` (Szegő infimum `exp(2I)`) [L]; Jensen's equality (BSY) [L] |
| (d) **Amplification**: the depth is multiplied, the loss is not | a parameter `k→∞` with a loss independent of `k` | the tensor-power argument of Rankin and Deligne | one growth exponent for all even moments of the prime traces [L*]; sublinear tensor growth with the trace of ζ retained [L]; tensor series of a configuration converge right of `1+m·depth` [L] |

The programme works only on these receivers. Every other route waits.

### 4.3 Requirements for a producer

| # | Requirement | Source |
|---|---|---|
| R1 | No floor: it acts at every depth `δ>0` | §4.1 |
| R2 | Its inequality is of kind (a), (b), (c) or (d) | §4.2 |
| R3 | It uses the functional equation and the Euler product jointly: it fails for the Liouville twist, for the lattice with a pair, for the paired ξ model and for integer-norm one-offs | [L*] |
| R4 | It is pointwise in the zeros; a statement in law never excludes | [L] |
| R5 | It is not a mean square over a family of twists and uses no large sieve | guidance; §4.1 |
| R6 | It proves no margin and no wrong constant, weight or scale | [L*] |
| R7 | It does not follow from the explicit formula alone: every filtered current is the filtered zero sum | [L] |
| R8 | For AAL it acts on a finite datum, the top layer, and on quantities normalized by the top exponent | §4.4 |

### 4.4 AAL as non-attainment

In world I the smoothed prime error is `e^{(Θ−½)u}(P(u)+o(1))` with `P` a nonzero real trigonometric polynomial with finitely many frequencies [L]. The world is uniformly bad [D]: for every `L>0` there is `c(L)>0` with `sup_{[T,T+L]}|c_B|≥(c(L)−o(1))e^{(Θ−½)T}` for all large `T`, because the translates of `P` form a compact family of nonzero analytic functions. So each of the following gives AAL, at every depth, with no exponent claimed.

| # | Statement | Evidence |
|---|---|---|
| N1 | For one `L>0`: `liminf_T e^{−(Θ−½)T}·sup_{[T,T+L]}\|c_B\|=0`: on some late windows of one fixed length the error is of smaller order than its own maximal rate | [D] |
| N2 | For each `k`: a floor `−K_k`, or a floor of any exponent below the top depth, on arbitrarily late windows of length `(k+1)π/67`, also at the prime logarithms | [L*] |
| N3 | One growth exponent for all even moments of the prime traces on arbitrarily late windows of one fixed length | [D] |
| N4 | At most one zero right of some line `Re s=σ`, `Θ₂<σ<Θ` | [D] |
| N5 | `JasDressedPSD 1` on large primes; it gives `Θ=½` | [L*] |

N1 is the form the guidance asks for: it compares the error with its own rate, so it is the same statement at `δ=10^{−9}` and at `δ=¼`. In prime terms: the prime number theorem with exponent `Θ` is never attained uniformly; there are scales at which the error falls below every multiple of `x^Θ` on a whole window of bounded ratio.

What a proof of N1 cannot be [D]. Normalization by `e^{(Θ−½)u}` removes every main term, so positivity of `Λ` is lost: it bites only at `δ=½`, which is the classical zero-free region. Every linear identity of the explicit formula passes to the limit as a homogeneous convolution equation whose solutions are exactly the trigonometric polynomials with frequencies at zeros on `Re s=Θ`: a tautology. What can survive the normalization is nonlinear or discrete: multiplicativity, integrality of multiplicities, the parity of the top layer, replication of a zero.

### 4.5 Tracks

Ranked by fit to R1–R8 and by the existence of a first step. Each track ends at a stated theorem or at a stated kill.

**Track 1 — Non-attainment (AAL).**
- *Aim.* N1–N4 for ζ.
- *First theorems.* A121: N1 and N3 in Lean, with the compactness of the hull of the top trace. A125: N4, with the parity of the top layer. A127: the **tangent datum** of world I — top exponent, ordinates, multiplicities, and the residues that govern the top traces of `Λ`, `μ`, `λ` and of twisted multiplicative functions — with the theorem that every linear identity of the corpus is a tautology on it.
- *Then, three mechanisms to test on the tangent datum.* (i) Replication: a zero at the top forces another at the same real part. It follows from recurrence of ζ to itself on a small disc at the top zero, and in world I the only obstruction to Hurwitz's argument is that the translates are not a normal family on `Re s>Θ₂`; decide which normalization of the translates is normal there (B128, B89). (ii) Multiplicativity: the tangent data of `f`, `g` and `f·g` for bounded multiplicative `f,g` are linked by nonlinear relations; decide whether a bounded multiplicative function exists whose top trace would exceed the trivial bound. (iii) Integrality: the prime filters recover the multiplicities as limits; decide whether any filter has an a priori bound below one.
- *Kill.* If the tangent datum of every bounded multiplicative function is consistent (Selberg–Delange asymptotics at a pole of order the multiplicity) and no normalization of the translates is normal, the track has shown that non-attainment needs an input that the top layer does not see; record the consistent tangent datum as a theorem.

**Track 2 — Certificates for the equality cases.**
- *Aim.* RH ⇔ at every aperture some real weight system is feasible, and one aperture admits none if RH fails [L*]. A producer may use a different, non-arithmetic system at each aperture. A feasible system at aperture `a` is a positive measure on the line whose Fourier transform on `(−2a,2a)` is the archimedean-plus-pole background minus atoms at `±log n` [D]: a pure object that imitates the place at infinity of ζ up to the resolution `a`, with any real weights at the integers.
- *First theorems.* A128: the description of the feasible set as a set of positive measures (the extension theorem for positive definite functions on an interval), and its extreme points. A117: the feasible interval of `w(2)` on the first selective window. A129: for the objects of the corpus with all zeros on the line and ζ's Gamma factor (the cleared Eisenstein constant term for `1≤Y≤4πe^{−γ}`, the pencils at `h≥½`, symmetric completions of zero-free Dirichlet polynomials), the distance of their prime side from an atomic measure on `log ℕ` on a window.
- *Kill.* If no pure object with the Gamma factor of ζ has an atomic prime side on any window beyond first contact except through its own zeros, the existence half carries no more freedom than the sign for `Λ`; record the rigidity as a theorem.

**Track 3 — Unit gaps.**
- *Aim.* Bound an integer by one: the number of zeros right of a line (N4), the index of an approximant, the trace norm at a formation rectangle (TG).
- *First theorems.* A126: for each regulator of the horizon, the function whose zeros are its resonances at finite cutoff and the number of its right-half zeros: one for the cusp cutoff [L*]; unknown for the clock and the tower. Both convergent regulators approach Weil's form from below, so a sign at finite cutoff is at least as hard as the limit [D]; a regulator from above, or a secular function with at most one right-half zero and limit ξ, is what the index law can use (B117). B171: a source of "at most one" built from the single pole: a form of signature `(1,∞)` given by the prime side with one positive square by construction, in which the zeros are the spectrum of a symmetric operator.
- *Kill.* Every regulator with limit ξ has an unbounded number of right-half zeros before the limit, or no secular function.

**Track 4 — Symmetrization.**
- *Aim.* A functional `Φ` on zero configurations with `Φ(Z^{sym})<Φ(Z)` whenever `Z` has an off-line pair, at every depth, where `Z^{sym}` is the projection to the line, which keeps every ordinate count and is tempered [L*]; and a reason why ζ is `Φ`-minimal in a class closed under projection of finitely many pairs. For AAL finitely many pairs suffice.
- *What is known.* Weil's form is not such a functional: the difference of the on-line and the off-line pair term has no sign [D]. The inner mass is one, decreases strictly, and is the logarithm of a Szegő infimum over mollifiers [L]; projection by a Blaschke factor leaves `|ζ|` on the line unchanged, so its minimality is Jensen's equality, the receiver of Track 2.
- *First theorem.* A130: the prime side of the projected divisor: primes plus an explicit smooth signed density `−2Σm cos(γu)(cosh(δu)−1)` [D]; which functionals of the prime side are monotone under adding it.
- *Kill.* Every functional that decreases under projection is a function of the inner mass.

**Track 5 — Amplification.**
- *Aim.* A bound for the `m`-th tensor object with a loss independent of `m`.
- *What is known.* Tensor series of a configuration converge right of `1+m·depth`; sublinear tensor growth with the trace of ζ retained is RH; ζ is the fixed part of the canonical families, so no family supplies the bound [L]. On the prime side the `2k`-th moment of the prime traces on a window is a `2k`-fold correlation of primes.
- *First theorem.* A131: the a priori statement in prime terms: which correlation bound, uniform in `k`, is N3, and whether it is implied by a bound at `k=1` together with a structure of the integers.
- *Kill.* The uniform bound is equivalent to the prime-tuple asymptotics with power saving at every order; then the track waits for a geometric source of the bound.

**Track 6 — The floor census as theorems (runs beside the others).**
- A123: the infimum over all slot and scale parameters of the boundary of a probe whose direct bound is a mean square followed by Cauchy–Schwarz is above `½`, as a theorem about exponents; the detector budget is the model. A124: the positivity floor of §4.1 in Lean. A floor is computed for every proposed estimate before work starts.

### 4.6 Tests for a proposed mechanism

1. Its floor (§4.1). A positive floor ends the proposal for AAL and RH.
2. Its kind (§4.2) and the receiver that takes it.
3. The fakes: the Liouville twist and the lattice with a pair at rung one; the paired ξ model; integer-norm two-scale products; the density-matched model with unattained top; a Selberg zeta function with a small eigenvalue (§2.5). It has to fail on each for a stated reason.
4. The limit `δ→0`: the statement and its constants at depth `δ` must not degenerate.
5. Independence of `[X]`: no mean square over twists, no large sieve, no family average.
6. Its tangent form (§4.4): what remains of it after normalization by the top exponent.

### 4.7 What stops, and the order of work

Stops [A]: further receivers and equivalences; further one-structure calibrations of the atoms; rungs by verification; any estimate with a positive floor; averages over families.

Order [A]: Track 6 at once, as the filter. Track 1 first theorems (A121, A125, A127), because they are decidable and fix what a proof of AAL may use. Track 2 (A128, A129), the only place where the existence quantifier gives freedom. Tracks 3–5 at their first theorems, each to its kill or its survivor.

| # | Item | Kind |
|---|---|---|
| A121 | N1 and N3 in Lean (two-sided windows of any fixed length; moments on fixed windows) | assembly [D] |
| A123, A124 | the floor of mean-square probes; the positivity floor | assembly [D] |
| A125 | N4 with the parity of the top layer | assembly [D] |
| A126 | resonance functions of the regulators at finite cutoff and their right-half zero counts | (unverified) |
| A127 | the tangent datum of world I and the tautology theorem for linear identities | (unverified) |
| A128, A129 | the feasible set as positive measures; the prime side of the pure objects with ζ's Gamma factor | (unverified) |
| A130, A131 | the prime side of the projected divisor; the prime form of a tensor-uniform bound | (unverified) |
| B170 | Non-attainment: N1 for ζ | AAL |
| B171 | A form of signature `(1,∞)` from the prime side in which the zeros are a symmetric spectrum | RH (producer) |
| B172 | A functional that decreases under projection to the line and is not a function of the inner mass | producer |
| B173 | A bound for all tensor orders with a loss independent of the order | RH |

**Limit of this section.** It is a programme for a search, not a route. It contains no producer; under its assumption none is known. Its deliverables are theorems that decide which kinds of producer can exist, and five decidable first steps.
