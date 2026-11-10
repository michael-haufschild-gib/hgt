# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `68b0e1200f` with its working tree (2026-11-10). Working log: `logs/review-1011-statusquo-research.md`.

**Evidence.** `[L*]` Lean statement read for this report (source or corpus search tool); `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/` returned by the corpus search tool, not re-read; `[S]` Lean source present in the working tree, not committed at the checkpoint, statement read; `[K]` Lean with transitive axiom audit as recorded; `[D]` deduction made here from `[L*]` statements; `[C]` classical, not in the corpus; `[A]` assessment. Sections 2.3–2.14 and 3 are interpretation and ideation: every untagged statement there is a proposal, not a result.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS is a retired label.

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1⇒Θ=½`. `c_B` the orbit correlation of the cubic spline, `c_p=c_B(log p)`, `c_B(log d)=A(d)−P(d)` with `P(d)` the smoothed von Mangoldt count in the window of `d` and `A(d)` its archimedean-plus-pole prediction. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I** ¬AAL; **world II** AAL ∧ ¬ZAL. `𝒢=W(ℤ)` the arithmetic square, `Γ_n` its graphs, `J(m,n)` the ideal of `Γ_m∩Γ_n`. `E_r` the arithmetic-clock Green energy. A **heavy return**: a `δ`-return, `δ≤1/20`, of a subset of the primes `≤y` omitting at most `1/1000` of the `p^{−1/2}`-mass.

## 1. Big picture

### 1.1 One inequality per prime, on logarithmic windows, off power-thin exceptions
RH ⇔ `∃K`: `2c_p≥−K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ Weil positivity of the two-bump `B+τ_{log p}B` at every prime ⇔ every effective prime class `Γ_1+Γ_p` carries an `ℕ`-count with Tate limit `δ_p(1,1)` [L*]. The face is local in scale and robust:

| Sample of primes | A one-sided bound gives | Evidence |
|---|---|---|
| all primes; any power-saving gap set | RH | [L*] |
| primes of arbitrarily late `√T` windows | RH, for every tempered configuration | [L*] |
| primes of arbitrarily late logarithmic windows `\|log p−T\|≤32 log(T+2)` | RH; width `≤α` from the floor `−Kp^α`; absolute form equivalent | [L*] |
| the same windows, outside at most `Ce^{δT}` primes per window, `δ<1`, chosen freely per window | RH; width form; Stepanov form `P(p)≤A(p)+Kp^σ` | [L*] |
| windows `T≤log p≤T+80/δ+1`, if the deep ordinates of ζ are `δ`-separated | RH, from below or from above; count form | [L*] (conditional on the separation) |
| windows of any fixed length | nothing uniformly: an off-line pair of ordinate `<π/L` is bounded below on windows of length `L` beyond every bound | [L*] |
| Bohr-dense sets (arbitrarily long intervals, sampling weights) | an attained top lies on the line: AAL; with ZAL RH | [L*] |
| primes off a density-zero set; very smooth degrees; finitely many Frobenii | nothing without attainment | [L] |

If RH fails, every sufficiently late logarithmic window holds a violator of every floor outside every set of `Ce^{δT}` primes [L*]. The number of violators in a late window is therefore `0` or at least `x^{1−o(1)}` [D]. Unconditionally the error has the Vinogradov–Korobov saving [L]. The decisive radius below `32 log T` for ζ's class is open (B143).

### 1.2 Two worlds, three atoms
`Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; failure of quasi-RH forces `Θ=Θ∞=1` and AAL [L*]. A failure of RH therefore lies in exactly one of two worlds [D]:

| World | Description | Proved inside it |
|---|---|---|
| I: ¬AAL | a finite isolated top layer at `β<1` over a remainder `≤Θ∞<β`; contains every ZAL ∧ ¬RH world (finite stratum; remainders approaching the line) and the DH-violating worlds `½<Θ∞<Θ<1` | zero-free strip; `M(x)=O(x^{β′})`, `β′<1`; heavy returns later than `exp(c·y^{1−β″})`, `β″<Θ`; a complete finite-layer receiver [L*] |
| II: AAL ∧ ¬ZAL | `Θ=Θ∞>½`: the top is approached by infinitely many zeros; contains `Θ=1` | the receivers only |

RH ⇔ ZAL ∧ B13 ∧ Landing; a failure of the abscissa law fails exactly one of B13, Landing, DH [L*]. Landing is a tail law, undecided below every height [L*]; an FE model of exponential type with approaching quartets and a positive integer-norm Euler product with approaching remainders both violate it [L*]. Classical Deuring–Heilbronn holds for a real zero of a quadratic `L(s,χ)` with a constant uniform in conductor, height and zeros; ζ has no Siegel regime [L*].

To prove AAL one may assume quasi-RH: AAL ⇔ (`Θ<1` ⇒ AAL) [D]. B56 implies AAL [D].

### 1.3 The finite-layer receiver is complete; the gap is the exclusion
In world I, for every top zero `ρ` at `β` and every observation line `σ<β`:
- prime-only damping filters divided by the Gaussian kernel tend to minus the multiplicity times a nonzero divisor constant; with boundary rotation the fixed Gamma loss is absent and every damping speed `a>0` reads [L*];
- at contraction `h=e^{−κt}` the filter norm tends to infinity when `dκ<a(β−σ)/2`, `d` = one plus the number of other layer points [L*];
- the Vinogradov–Korobov bound is `C h^d t^N exp(a(1−σ)t/2−a t·vk(t³+1)/4)` [L*]; the same holds at polynomial damping with prime cutoff polynomial in the height [L*];
- above `X≥t⁸` the first Gaussian prime moment minus its pole is the centred Vaughan current up to `O(1/t)` [L*]; with cutoffs `U,V` the filtered centred error is at most a constant times `h^k/t` once `(UV)²t^{k+3}≤X^{1+σ−η}`, `k` the filter degree [S];
- a top layer with a dominant ordinate — its Gamma mass exceeds the mass of all other ordinates of the layer — makes the corrected current diverge at every damping `a` with `a(β−σ)>π/2` [L*];
- for `½≤σ≤5/6` and `c>(30/13)(1−σ)` the one-separated returns of ζ to a small disc at a zero right of `σ` number fewer than `T^c` up to height `T` [L*].

The growth range `dκ<a(β−σ)/2` and the decay range `dκ>a(1−σ)/2−o(1)` are separated by `a(1−β)/2`. An arithmetic upper bound in the growth range beats the trivial bound of a prime sum of length `e^{at/2}` at height `t` by the power `1−β`: it is the exclusion of the layer (B145) [D].

### 1.4 Rigidity: ζ has no moduli, and a family sees only its variable part
- A Dirichlet series with ζ's FE is a multiple of ζ; a Borel prime measure on `(1,∞)` whose integer measure has ζ's completed FE is the rational prime measure; a countable Beurling system with an `L¹` or `L²` FE defect is the rational primes; count distance `o(log n)` forces the rational primes [L*]/[L].
- A gauge fibre with a nonzero analytic residue at `1` is `ζ·exp(H)` on a half-plane left of `1`, with the same zeros; quadratic rigidity holds under continuation; a fibre summably close to `−1` continues to `exp(J)/ζ` [L*]. Along the exponentially damped Liouville phases the residue at `1` vanishes to second order in the damping `t` with a nonzero coefficient, the fibre rescaled at `s=1+tw` converges locally uniformly on `Re w>−1` to a non-polynomial profile with a branch point of exponent `iπ` at `w=−1`, and no function analytic at `(t,s)=(0,1)` regularizes the family [L*].
- Fixed part: for every finite measure on the gauge torus and every continuous amplifier the moment is at least the atom at the trivial fibre times the trivial bound; amplification beats it strictly at a nontrivial torsion fibre; product positivity passes from base to product and not back, for every exponent `a<½`; the trivial fibre has mass zero or tending to zero in the five family classes; with the trace of ζ retained, sublinear tensor growth of a cover family ⇔ RH [L*].
- The Eisenstein line law holds over every symmetric fixed part in the closed strip: the purity of all members of a family is the closed strip of its fixed part, never its line [L*].

Consequences [D]: Deligne's family step has no producer over ℤ; no fake keeps Euler product, FE and coefficient size and moves a zero, so statements that use the structures jointly cannot be calibrated on models.

### 1.5 Exactness over ℤ has an exact price
`x↦xⁿ` is additive in characteristic `q` exactly when `n` is a power of `q`, at most one prime for `n≥2`; `N(n)=Λ(n)+1+1/(n²−1)` lies in `(1,2)` off the prime powers [L*]. A monic polynomial whose derivative vanishes modulo every prime of `S` has degree divisible by the primorial of `S`; order `m` of the Fermat-quotient derivations at every prime of `S` costs `log|a|≥m·Σ_{p∈S}log p` [L*]. The minimal fixed-point auxiliary has log length `ψ(N)`, and RH ⇔ `ψ(N)≤N+C√N log²N` [L*]. Rational self-maps preserving the prime orbit are Laurent Adams maps [L*]. No finitely generated lattice is stable under three prime Frobenii; eventually integral traces of a summable family of modes in the open strip force zero amplitudes [L*]; `Λ`, the Mertens function and the glued Lefschetz count are not traces of any order [L]. On the diagonal Stepanov's inequality is the product formula.

### 1.6 The square of Spec ℤ is a curve; the diagonal is a comb finite part
- **Contacts and jets.** In `𝒢=W(ℤ)`, cofree among rings with commuting Frobenius lifts, `frobeniusIntersection(ga,gb)=g·a/(1−(a/b)²)+g·log#(ℤ/J(a,b))`: Weil's off-diagonal is the archimedean jets plus the contacts of the graphs [L*].
- **No normal direction.** The conormal classes of the diagonal are torsion; the gluing index of the first `N` graphs is `N!`, within `O(log N)` of the zero count at height `2πN`; graph by graph the square counts the zeros up to the increments of the remainder `S(T)` [L*].
- **No finite type.** The fibre of the square over `p` has infinitely many points; a ring with Frobenius lifts, a ℤ-point and a finite fibre over `p` has two graphs with a contact that is not Weil's; a perfect square keeps no contact [L*].
- **Archimedean fibre.** On real sequences the same Frobenius has the weight lines `χ_z`; transposition is `z↦1−z`; the jets give `1+1/(n²−1)` and `m/(1−(m/n)²)`; the pole plane is the weights `0,1`; no Witt Verschiebung carries Weil's off-diagonal [L*]. No duality exchanges contacts and jets.
- **Diagonal.** Weil's archimedean form of a packet is the limit of the jets on invariant combs minus the mass times `log(density/2π)`; no function of the degree point is the counterterm on two combs [L*].
- **Counts.** A section count with Riemann–Roch and Bézout exists iff the Hodge index holds; over ℤ the pair is RH [L*]. On the toric surface of a base the diagonal has a normal direction and the count of sections is bilinear; a tower of lines carries the contacts with an exact count [L*].
- **Carries.** `log C(2N,N)` is the carry term plus the prime count of `(N,2N]`; the carry term is `∼(2 log 2−1)N` [L*].

### 1.7 The adelic carrier: a Green pairing off the diagonal, no glued diagonal
Off the diagonal Weil's kernel is the pole minus `2πG_{1/2}` on the degree geodesic of `ℍ³` and the tree Green functions at the Ramanujan point on the `p`-ladders [L*]. Every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal and its dyadic pairing with Weil's off-diagonal tends to `−∞`; the unweighted critical product erases the prime contacts and diverges over the torus; bounded words in the prime operators vanish where Weil's off-diagonal is positive; no scalar normalization removes the jump `−2‖g‖²log p` between `p` and `p³` [L*]. The summably weighted adelic Green kernel is an invariant positive covariance and does not sign Weil's form [L*]. The mixed hyperbolic Green kernel of the weighted adelic adjacency is the limit of its finite Dirichlet sections; between distinct finite vertices it and its Robin finite part are nonnegative and bounded by a strictly tempered product barrier of exponent above `½`, uniformly as the archimedean distance tends to `0` [L*]; the kernel is symmetric and invariant under adelic isometries [S]. Weil's functional on packets is the limit of Robin-normalized Maass–Selberg diagonals of the scattering tower [L*]. The arithmetic clock gives `E_r≤W`, `E_r↑W` with error `≤(1−r²)‖f′‖²/2` [L*]; its sign is Weil's sign [D].

### 1.8 The window sign is verification height; the critical curve has one undecided case
RH ⇔ `W≥0` on every window ⇔ `Ψ` locally bounded on precontact intervals [L*]. `RHVerifiedThrough(windowHeight a)` gives the sign on `[−a,a]` [L*]; window positivity at `a` forces near-line zeros to a height of scale `e^{a}`, and models hide an off-line zero at height `T` to aperture `(log T)/36` [L]. Each of the fourteen window formulations at aperture `a` is a finite-height statement in both directions up to constants.

At the critical curve `R_c=R_polar=R_halfline≤W₀` [L*]. Exactly one of: RH; ¬RH and `R_polar<W₀`; ¬RH and `R_polar=W₀` finite with every critical half-line ground state polar-orthogonal [L*]. The third case is undecided (B104).

### 1.9 Index, limits and separation
A Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points; the bound passes to locally uniform limits; RH ⇔ ξ is a limit of conjugation-real entire functions with at most one right-half zero each [L*]. The Eisenstein constant term `Λ(2s)Y^s+Λ(2s−1)Y^{1−s}` is pure off the real axis for `Y≥1`, with one real exceptional zero exactly above `Y=4πe^{−γ}` [L*]. `ξ(s+a)+ξ(s−a)` is pure at `a=½` and each heat deformation `H_t`, `t>0`, has finitely many non-real zeros [L*]; for these natural deformations the purity threshold moves with the width [D]. RH ⇔ the ordinate is injective on the zeros ⇔ `|c_p|≤K` at every prime; separation by absolute value is excluded for ζ [L*]. The zeros contain no conjugacy class of one Frobenius: no vertical progression `ρ+ikT` consists of zeros, at any real part; `Σ_n|ζ(ρ+inT)/(ρ+inT)|` diverges in the strip while the squares are summable; no two-sided sequence of zeros lies within an `ℓ²` perturbation of a progression in the open strip; the periodicity dichotomy for ζ is RH [L*].

### 1.10 The horizon has complete and sharp receivers
RH ⇔ every compact pulse rings down at `e^{−(¼−ε)τ}` ⇔ every tent reflection Krein form has negative index `0` ⇔ one cavity energy of Hecke forms decays at `y^{¾−ε}` [L*]. For one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero; any halving pair forces `Θ≥2/3` [L*]/[L]. A count within bounded distance of the integer probes gives RH [L*].

### 1.11 The dark range and the returns of the prime orbit
Heavy returns do not occur while `log t≤(log y)^{3/2−ε}`; a strip of depth `h` above some height gives `log t≥c·y^{½−h}`; two-prime returns obey Baker's depth law, also with `log(−1)` adjoined; return bounds are statements about the labels and are shared by `ζ(s−h)` [L*]. Candidate S3 asks for a transfer from "no heavy return of the primes `≤(log x)^A` below `x^η`" to the floor on the logarithmic window at `x`. In every world with `½<Θ∞<1` the hypothesis holds for `A(1−Θ∞)>1` while the conclusion on all late windows is RH: the transfer implies B56, hence AAL, and its hypothesis is implied by quasi-RH [D].

### 1.12 Law and point
Past the Vinogradov–Korobov region every unconditional theorem of the corpus about the zeros is in law: density exponent `30/13`, Matomäki–Radziwiłł for μ, critical-line density `0.67250071`, the form-factor identities, typical-height signs [L*]/[L]. On the prime side a zero is visible at every scale, so power-thin exceptional sets of primes are harmless (§1.1); on the height side a zero is one point and every in-law statement is blind to it [D]. Census receivers: ceiling `4π(1−a)` of the source covariance ⇔ density `≥a`; the exchange-rate certificate reaches `70%` exactly when its form-factor bound is at most `4` on `(1,10/9)`; failure of `θN` forces `(1+HD(1)−2θ−1/A−ε)N` simple off-line zeros within `A/log T` [L*].

### 1.13 The Mertens level in several geometries
Producer rates, Farey discrepancy, the nerve, the prime-vertex indices, the gluing quotient and the centred count of the orientation cover over ℤ read `M(N)`; cover weight `½` ⇔ RH; rates `K^{−a}` for all `a<½` give RH; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [L*]/[L].

### 1.14 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| A family (gauge twists, characters, vertical shifts, Hecke forms, covers, Euler deformations) as a source of purity for ζ | fixed-part theorem; isozeric deformations | [L*] |
| One glued adelic-invariant carrier object with Weil's diagonal | constant diagonal; drift `−∞`; discriminant jump | [L*] |
| A finite-type object with Frobenius lifts carrying the contacts | fibres infinite; forced wrong contacts | [L*] |
| A Frobenius for a window; cheap simultaneous vanishing over ℤ | one prime per power map; cost `m·θ(S)`; primorial | [L*] |
| A duality exchanging contacts and jets; a Verschiebung carrying the off-diagonal | transposition preserves both parts; vanishes at `(2,3)` | [L*] |
| A diagonal entry attached to a degree point | the counterterm belongs to the comb | [L*] |
| Integral or trace-class Frobenius modules for the zeros | Tate twists only; the Lefschetz numbers are not traces | [L*] |
| Purity of a fixed part from the line law of its family | holds over impure fixed parts | [L*] |
| Separation of the zeros by absolute value (coefficient gaps) | three critical ordinates in a dyadic range | [L*] |
| The transfer of candidate S3 as a method question | implies B56 | [D] |
| The clock energy `E_r` as an independent producer | `E_r≤W`, `E_r↑W` | [L*]/[D] |
| A fixed window length uniform over configurations; density-zero exceptions without ZAL | off-line low pair; unattained tops | [L*]/[L] |
| Landing from the FE alone or the Euler product alone; graded repulsion from Euler products; the classical Deuring–Heilbronn mechanism for ζ | models; no Siegel regime | [L*] |
| Heat finiteness at `t>0` as landing; family-uniform finite-stratum laws | collision mass diverges; RH-strength | [L*] |
| Euler-region or VK bounds for filters as exclusion of a finite layer | ranges separated by `a(1−β)/2` | [L*] |
| One Hecke eigenform as a complete receiver without side condition | halving pairs; Shimura zeros | [L*] |
| Markov, Perron, size-only payment, floor tower, universal holomorphic multipliers, fixed theta heads, positive Laplace mixtures | refuted or bounded | [L] |
| Positivity, Euler products, integrality, linear counting, continuation, reflection, positive Hecke and two-prime polynomials as any atom | one-offs and annihilators | [L*]/[L] |
| Schur, `C*`, KMS, internal modular conjugation, half-sided inclusions as zero locators | blind or excluded | [L] |
| Hyperbolic 3-manifold carriers of the finite places; metrics on `ℙ¹_ℤ`; locked atomic dampings | excluded; discriminant diagonal | [L] |
| Bounded-height Diophantine certificates against returns; return bounds as uniform routes to ZAL | Kronecker-scale cap; label statements | [L*]/[L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A72 | Count door on logarithmic windows with exceptional sets: RH ⇔ counts with Tate limit `δ_p(1,1)` at the primes of arbitrarily late logarithmic windows off `Ce^{δT}` primes | ACS, HF, PM, SRT | `riemannHypothesis_iff_prime_logarithmic_windows_off_finset`; the count gives the floor `K=2c_B(0)` |
| A73 | One-sided upper side (`2c_p≤K`) on logarithmic windows (unverified) | SRT, ACS | positive deletion acts on either sign; `TheOtherSideOnWindows` |
| A75 | Lean form of "the transfer of S3 implies `Θ<1⇒Θ=½`" | BAG, S3 | `log_ge_of_heavy_return_of_strip`; logarithmic-window criterion |
| A76 | Exceptional sets in the absolute and signed window criteria (unverified) | SRT, ACS, CDGeo | `SignedPrimeLogSquareWindows`; `ExceptionalLogarithmicWindows` |
| A71 | Local tensor moments: uniform-in-`k` moments of `c_B` over the primes of late windows ⇔ RH [D] | ACS, AWT | window criteria; Chebyshev's inequality with the exceptional-set form |
| A56 | Explicit rung: `RHVerifiedThrough T` ⇒ the two-bump sign for all `p≤P(T)` (unverified) | SRT, ACS | supports of the two-bump tests |
| A77 | Power-sized cutoffs for the filtered centred Vaughan error with its cofactor tail; adelic symmetry of the mixed hyperbolic Green kernel | ELT, HAT | source present [S] |
| A78 | Cluster form of the separated-window theorem: clusters of deep ordinates with at most `C log γ` members, by a Turán-type inequality (unverified) | SRT, ACS | `SeparatedOrdinatesAreSeenInEveryWindow`; first step of B143 |
| A79 | Matching constants in the aperture–height exchange (unverified) | RW and the window routes | `windowPositiveAt_of_rhVerifiedThrough`; visibility laws |

### Finite verification and explicit constants
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Certified `RHVerifiedThrough T` past 67 | all rungs | `rhVerifiedThrough_sixtySeven` |
| A2, A3 | Numeric values of the explicit heights; two-weight membership on the first windows | window routes, TH, LA, HCF | explicit definitions |
| A4, A5 | Theta rank 15 and beyond; certificate of the center-tail failure (unverified) | TH | height 67 |
| A6, A7 | Cone widths; certificates on the anti-diagonals (unverified) | CHT, ACT | convex programs |
| A9, A13 | Explicit constants at the eighth-root horizon; near-gcd charges (unverified) | HF, AIP | proved limits |
| A47, A58 | Constants of the one-quartet world; effective gap iteration (unverified) | ELT, ACS | envelope and gap theorems |
| A48 | Hasse–Weil tests of smoothed Frobenius pairs at verified scales | ACS, HF | window rungs |

### Classical inputs to formalize
| # | Task | Routes | Basis |
|---|---|---|---|
| A18, A21 | Twisted second moments past `21/50`; logarithmic two-point Chowla [C] | WD, MC | classical |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM, BHR | order `N(Λ)≍Λ` |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics [C] | ACS, PM | crude-bound self-improvement |
| A59 | Short-interval primes in a residue class [C] | ACS, SRT | gap sets |

### Further items
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` (unverified) | RW | Galerkin |
| A19 | Heat horizon: an explicit height for the exponent `(3/2+ε)/t` (unverified) | ZCG | zeros of `H_t`, `0<t≤⅛`, beyond `2π·exp(40/t)` are real; beyond `2π·exp((3/2+ε)/t)` past an inexplicit height |
| A20 | Jensen rung toward the saddle scale (unverified) | LA | `RHVerifiedThrough T` gives real-rooted Jensen degrees `d` with `2·10⁷d⁴≤T log T` |
| A24, A37 | Certified scans; resonators below the Kronecker scale (unverified) | TH, BAG | column calculus |
| A28, A30, A42, A46 | Reciprocal-quadric traces; best stencil exponent under RH; Gamma-weighted transport to the adaptive head; singular indices (unverified) | ACS, WL, TH, MC | stated bases |
| A54, A70 | Cusp expansion for Bianchi resolvents; torus-periodized local Green functions | HAT | carrier theorems; barrier bound of the mixed Green kernel |
| A55, A68 | FE rigidity with an `L¹` or `L²` defect for Beurling prime measures; a landing calibration with ζ's Gamma factor (unverified) | BAG, ELT | the exact FE forces the rational primes for every Borel prime measure; approaching models |

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K` on a decisive sample: every prime, or the primes of arbitrarily late logarithmic windows off `Ce^{δT}` exceptions; any growth `Kp^σ`, `σ<½`, is a zero-free strip. Known: the VK saving | RH (≥qRH) | ACS, SRT, WL, HF, ZCG, HAT-C |
| B143 | **Decisive radius**: do prime windows of unbounded sub-logarithmic radius, or of bounded ratio given ζ's lowest ordinate and local zero count, decide RH (§3) | method | ACS, SRT, WL, HF, SOSZ |
| B144 | Separation of the off-line ordinates of ζ (vacuous under RH); gives bounded windows by `[L*]` | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window; equivalently `E_r(f)≥−ε` near `r=1` on every packet | RH | all sign routes, HAT-C |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact; outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | **Polar orthogonality**: can a critical half-line ground state at finite `W₀` be polar-orthogonal (§2.4) | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
| B18 | Prime-blind positivity on nonnegative blind mixtures | RH | RW |
| B19–B21, B102 | Torus law for `S*`; amplitude oscillation; all theta ranks; sign of the adaptive head near critical zeros | RH | TH |
| B22, B24, B25 | Outer roots of the Jensen polynomials; collisions at small time; frequency below one | RH | LA, ZCG |
| B27, B28, B47 | Runs of simple critical zeros; local positivity at fixed `λ` on density-one heights; multiplicity by a non-size input | sub | ZCG, RW |
| B29–B45 | The single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | Finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146 | An independent family of bounded index converging to ξ (index certified without the zeros) | RH (producer) | W1C, PTR, IRP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48–B54 | Deciding input at square-root precision; endpoint energy; trivial-gauge half power; moving power windows; rows and BSY; regularized partial sums; extremal inequality | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | Polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½`; implies AAL [D]; implied by the transfer of S3 [D] | sub | whole programme |
| B57 | Depth density `o(T)`: all but `o(N)` zeros within `o(1/log T)` of the line | sub | WD, CTF, MC, RW, PM |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub | WD, MC |
| B62, B63, B66 | Cofinal long moment; collision charge; near-unit holomorphic budgets | RH | WD, CTF, AIF |
| B91, B94 | Cut-kernel mass; cubic theta identification and rational transfer | RH; past VK | RAC, MMD |
| B96, B97, B100, B121, B137 | Tail law at the Kronecker scale; first return past the VK rung; savings on moving blocks; freezing beyond the cap; collective depth floor uniform in `π(y)` | sub | BAG, PTT, TAPO, TTPO, CDGeo |
| B106 | A correspondence on the orientation cover with bounded local indices | RH | MC, HAT |
| B110, B126, B127 | Thick crude count; a one-sided bound on a sampling set; positive-measure lag recurrence | AAL | WL, ZCG, ACS, IWT |
| B145 | The filtered centred Vaughan current in the growth range | AAL [D] | ZCG, BAG, ELT |
| B148 | The transfer of candidate S3 | ≥B56 [D] | S3, BAG |
| B150 | A form factor bounded by `4` on `(1,10/9)` | sub | census |
| B64, B65 | Signed pair information beyond bandwidth one; genus upper law and logarithmic Serre duality | sub; indep. | census, ACS |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B113 | Möbius × quarter-disc remainder `O(X^{½+ε})` | beyond RH | PM |

### Γ — selection, reflection, transport, count
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13 | Finitely many off-line zeros ⇒ none | sub | whole programme |
| B138 | Landing for ζ (as an atom) | sub | ZCG, LA, ELT, HF |
| B141 | Deuring–Heilbronn for ζ: `¬AAL⇒ZAL` (§2.5) | sub | BAG, ZCG, ELT |
| B83 | AAL = B13 ∧ Landing ∧ DH | sub | BAG, JAS, SC, ZCG, WL |
| B89, B112, B128 | A bounded aligned return at each right zero; the FE into vertical transport; replication | sub | BAG, ZCG, EFT |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates `y^{¾−ε}` | RH | PM |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part / of the Gram defect | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a confined companion of the horizon | producer | PM |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one Hecke eigenform | indep. | PM |
| B149 | A section count with Riemann–Roch and Bézout on an infinite-type object carrying contacts and jets | RH (producer) | ACS, HF, AGZ |
| B69, B70 | A positive physical or graph carrier; a lower bound for the Hecke dispersion from it | producer; sub | PM, W1C, PTR |
| B77 | `0∉E`: polynomial repulsion at the value zero | indep. | ZCG, LA |
| B78, B79 | Rosati positivity of the window reflection; band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, PM |
| B82 | Inner-field decay | ≥qRH | BAG, CTF |
| B92, B93 | A rotated relation with coefficients of the size of `Q`; a contradiction beyond the extremal law | RH | ZCG |
| B111, B116 | `ZAL⇒RH` = B13 ∧ Landing; linear AAL at one fixed slope | sub | ZCG, WL |
| — | ZAL | ≥qRH | whole programme |

### Settled method questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B140 | Shortest decisive radius: logarithmic or log-square | logarithmic radius `32 log(T+2)` decides, with exceptional sets; no fixed length decides every configuration; the residual is B143 | [L*] |
| B139, A64, A66 | Sparse scale-local windows; log-square criterion; sign-free local decision | yes; absolute, width and signed-deletion forms | [L*] |
| B138 (as a method question) | Which structures decide landing | three-atom factorization; fails for the FE alone and for the Euler product alone | [L*] |
| B85, B142 | A family producing purity at ζ | none: fixed-part theorem | [L*] |
| B133, question (G) | One glued carrier object for the diagonal | no; survivors: comb finite parts, weighted covariance, the clock, the scattering tower | [L*] |
| B125 | No halving pairs as a condition for the one-eigenform receiver | void; the condition is the Shimura zero (B147) | [L*] |
| B131, B136 | Deuring–Heilbronn on models; gappy decisive samples | classified; they exist | [L*]/[L] |
| A69 | Full-degree adelic configuration | constructed, with commuting prime operators | [L] |
| A50 | Finite-stratum laws on the cosine and shifted Jensen families | Jensen: finitely many exceptional shifts at each degree, and the law gives RH; cosine: the law gives RH ⇔ ZAL | [L*] |
| A65 | Two-prime local criterion | for distinct primes `p,q` and `r>0`: RH ⇔ a lower bound on the two-prime difference lags in `\|ℓ−T\|≤r√T` for arbitrarily late `T` | [L*] |
| A67 | Dominant-ordinate divergence | ¬AAL gives a top layer whose corrected current diverges whenever one ordinate dominates | [L*] |
| A74 | Graded recurrence against the density theorem | fewer than `T^c` one-separated returns to a small disc at a zero right of `σ`, `c>(30/13)(1−σ)`, `½≤σ≤5/6` | [L*] |
| — | Periodicity of the zeros in height | none: no vertical progression of zeros and no `ℓ²` perturbation of one, at any real part | [L*] |
| (S1) | A Frobenius with cheap simultaneous vanishing over ℤ | no: one prime per power map; cost `m·θ(S)` | [L*] |
| (S2) | A sign-free quantity bounding the fibres of the height map | a receiver: ordinate injectivity ⇔ RH | [L*] |
| 𝔽₁ questions Q1–Q9 | Endomorphisms, multiplicity, locality of the diagonal, ampleness, Gamma factor and pole, integer-norm monoids, normal direction, duality, diagonal as finite part | answered (§2.14) | [L*] |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has an open input of RH, AAL or ≥qRH strength, or names one. Their value is to collapse independent problems into one, to decouple the producers a proof needs, or to fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Two-world skeleton.** Unbounded-window or Bohr-dense floor (kills world I) with any ZAL receiver (kills world II); or attained top with a thick crude count | RH [L*] | one AAL-type floor and ZAL; or attainment and a thick `O(√X)` deviation | two inputs of different kind, one per world |
| F2 | **One inequality per prime, local, with exceptions.** Prime two-bumps, Stepanov count, count door, sign-free form, logarithmic windows, power-thin exceptional sets | Σ, Π and count readings are one number per prime on sparse windows [L*] | B130 on one sequence of windows | every prime-side route has one target, at scales and with exceptions it may choose |
| F3 | **Deligne skeleton over ℤ.** Tensor positivity, Künneth, Rankin square, gauge family with big monodromy | every step except the family step, which the fixed-part theorem closes [L*] | none exists inside families | the tensor branch is support, not a route |
| F4 | **Critical curve.** Threshold identities, compactness, ground states, classification | one inequality and one orthogonality [L*] | B104 | RH ⇔ `R_c=W₀` if the orthogonal case is excluded [D] |
| F5 | **Horizon.** Cavity receivers, reflection Krein forms, one-eigenform reduction, count at bounded distance | physics reduces to one rate or one reflection sign [L*] | B71 or B68 | receivers complete and sharp |
| F6 | **The diagonal.** Adelic Green formula, comb finite parts, scattering tower, clock, refutation of the glued carrier | Weil's form has three exact presentations with one sign [L*] | B88 | every glued invariant presentation is closed |
| F7 | **Rigidity.** Hamburger, FE-defect isolation, count distance, isozeric gauge deformations, fixed part | ζ is identified by any two of its structures and has no moduli [L*] | B112 | no calibration with both structures exists |
| F8 | **Finite-layer world.** Free strip, Mertens power saving, late heavy returns, filters at every speed, VK bounds, centred Vaughan current | a complete receiver with an exact gap `a(1−β)/2` [L*] | B145 | the missing bound is the exclusion; no contradiction from identities |
| F9 | **Exactness.** Frobenius at one prime, `m·θ(S)`, Chebyshev auxiliaries, orbit rigidity, lattice and trace no-gos | every exact method over ℤ returns the product formula or Chebyshev [L*] | B97, B137, B121 | what survives is approximate, growing-height information |
| F10 | **Count skeleton.** Tate principle, hyperelliptic count law, contacts in `𝒢`, tower of lines, section counts | Riemann–Roch has an exact count; Bézout is the Hodge index [L*] | B87, B149 | the count door and the sign door need the same statement |
| F11 | **Construct, then identify.** Index semicontinuity with FE rigidity: a nonzero limit of index-one functions that has ζ's FE and a Dirichlet series is a multiple of ζ and gives RH | identification is free; the index of the approximants is the input [L*]/[D] | B146 | names a producer class: bounded index certified without the zeros |
| F12 | **Graded recurrence.** Transport receivers with the density theorem | `T^c` one-separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [L*] | quantitative transport | BAG needs power-sparse returns, not positive density |
| F13 | **Sign-free skeleton.** Signed deletion, two-sided windows, ordinate injectivity, Newton polygons, heavy-return laws | RH from `\|c_p\|≤K` on log-square windows without positive averaging [L*] | a two-sided producer; the transfer has strength ≥B56 | under the constraint the receiver is complete and every producer priced |
| F14 | **Dark range.** Savings, heavy-return dictionary, strip breadth, collective counts, collision counts | one first-return statement, proved to the VK height and, in a strip, to `exp(c·y^{1−Θ∞})` [L*] | B97, B137 | gap `(log y)^{3/2}` against `y^c` |
| F15 | **Theta wall.** Adaptive head `=ζ(½+ib)` up to `O(\|b\|^{−½})` [L*] | all ranks reduce to the size and sign of ζ on the line near its zeros | B102 | merges TH with the critical-line sizes |
| F16 | **Census.** Covariance equivalence, exchange rates, near-line alternatives | `70%` ⇔ covariance ceiling `6π/5`; follows from a bounded form factor [L*] | B150 | a law statement with exact receivers |

**Closest to the open core: F1, F2, F8, F11.** F2 is the common target. F1 decouples the two worlds. F8 shows that world I is fully instrumented and that its missing bound is the exclusion. F11 is the one conversion from law to point whose identification step is a theorem.

### What a contradiction search may assume in world I (F8)
| In world I | Evidence |
|---|---|
| `Θ<1`; isolated top `β`, attained; remainder `≤Θ∞<β` above the layer's heights | [L*] |
| `M(x)=O(x^{β′})`, `β′<1` | [L*] |
| heavy returns at `t≥T₁` need `log t≥c·y^{1−β″}`, `β″<Θ` | [L*] |
| filters read each top residue at every damping speed and every contraction rate below `a(β−σ)/2` | [L*] |
| VK bounds for the same filters with exponent `a(1−σ)/2` | [L*] |
| a dominant top ordinate (in particular a single one) ⇒ the corrected current diverges | [L*] |
| one-separated returns to a small disc at a zero right of `σ` number fewer than `T^c`, `c>(30/13)(1−σ)` | [L*] |
| no vertical progression of zeros through a top zero, nor an `ℓ²` perturbation of one | [L*] |
| on every late window of some fixed length a prime violates every floor `−Kp^{a}`, `a<β−½` | [D] from finite-spectrum oscillation [L] |

No contradiction comes from exact identities alone, from positivity, Euler products, integrality or counting alone, from the FE with order one and reality, from a property shared by the heat family, or from any in-law statement [L*]/[L]/[D].

## Validation tests for 2.4, 2.5 and 3

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH; for §2.5 and §3 also not implying AAL (or a method question implied by nothing about ζ's zeros) |
| T2 | Answered by proving or refuting a stated inequality, identity or implication |
| T3 | A named consequence can be written down for either answer |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake, or calibrated on the fakes |
| T6 | Names an input not refuted in Lean |
| T7 | Moves a wall; not a shape already answered |
| T8 | Not a named long-standing problem in disguise (RH, quasi-RH, ZAL, AAL, B13, Lindelöf, pair correlation, Hardy–Littlewood, Chowla, past VK, Landau–Siegel, strip self-improvement); its first step uses corpus objects and has one named obstacle |

**No question passes all tests and is a door to RH.** Every statement about the zeros of ζ below AAL is one of the sectors B13, Landing, DH or a structure theorem of world I; every pointwise prime-side statement past the VK saving is a named problem; the transfer of S3 and B56 imply AAL [D]. The questions below are the strongest that pass; each states its limit.

## 2.4 Breakthrough question below RH and quasi-RH: does the pole channel see every failure first?

**Question (B104).** *If RH fails, is every critical half-line ground state charged?* At the critical curve `R=c⁸/log N` the three cases are RH; ¬RH with `R_polar<W₀`; ¬RH with `R_polar=W₀` finite and every unit critical half-line ground state orthogonal to the polar source [L*]. Is the third case empty?

**What is proved [L*].** `R_c=R_c^{PSD}=R_polar=R_halfline`; `R_polar=W₀` ⇔ half-line polar positivity at every `R<W₀`; below `W₀` the form is eventually positive definite on the pole-orthogonal complement; RH, or a finite `W₀>0` with a unit critical half-line ground state; the classification. No finite or countable square-bounded family of holomorphic multipliers dominates the depleted kernel [L].

**What either answer gives.**
| Answer | Effect |
|---|---|
| The third case is empty | ¬RH ⇒ `R_polar<W₀`. RH ⇔ `R_c=W₀` ⇔ polar payment at every ratio below the window threshold: the five routes that meet at the critical curve (HF, SRT, AIP, ACS, SC) and their nine programmes have one inequality, a rank-one payment, with no separate window statement; the ground-state branch is closed [D] |
| A polar-orthogonal ground state is consistent | a second failure mode that the pole channel does not see: its transform vanishes at the pole points; at such a threshold the complete matrix carries no information beyond the windows, and the critical-curve programme ends at the window sign |

**Why this question.** The critical curve is the one place where the corpus has a complete reduction — compactness, threshold identities, ground states, classification — with exactly one undecided case. It is a statement about a variational problem on a half-line, implied by RH and implying nothing about the width.

**First step and obstacle.** Write the Euler–Lagrange equation of the Gamma-truncated charged critical form at `W₀`; the polar pairing is one linear functional of the ground state; test whether the equation forces it to be nonzero through the depleted kernel `m(z)=4/(¼−z²)−12/(64−z²)`. Named obstacle: the ground state is a limit of nonpositive directions and its equation contains the full zero side.

**Tests.** T1: vacuous under RH; implies no width. T2: emptiness of a case. T3: the table. T4: no finite rung. T5: the classification itself separates the cases; tempered fixed-ratio models show positivity at a fixed ratio is not automatic [K]. T6: not refuted. T7: moves Σ135, Σ139, B6, B101. T8: not a named problem.

**Limit.** Confined to the critical curve; it produces no sign.

### Alternatives
| Question | Why it matters | Verdict |
|---|---|---|
| Decisive radius (B143, §3) | the resolution of the minimal face | passes; the one question |
| Separation of the off-line ordinates (B144) | bounded windows for ζ by an `[L*]` theorem | passes T1–T7; no first step |
| Depth density `o(T)` (B57) | first unconditional input "in law" for seven near-line receivers | a 100%-type census problem; cannot decide an atom |
| Shimura nonvanishing at `ρ/4+¼` (B147) | the one-eigenform receiver without side condition | excludes coincidences of zeros of two functions |
| Bounded form factor (B150) | `70%` on the line | a pair-correlation problem past the diagonal |
| Count door on logarithmic windows (A72); upper side (A73); cluster windows (A78) | sharper receivers | just work |

## 2.5 Breakthrough question below AAL: the Deuring–Heilbronn sector, with a free strip

**Question (B141).** *Does an isolated top layer of ζ force the zeros to approach the line?* That is, is the world `½<Θ∞<Θ<1` empty.

**Position [L*]/[D].** AAL ⇔ B13 ∧ Landing ∧ DH, and a failure of AAL fails exactly one of the three. B13 contains the exclusion of one off-line quartet; Landing is an atom of the RH path. DH is the only sector of AAL off the RH path, and it is vacuous in every ZAL world. B56 implies it.

**What the sector looks like.** Every world in which AAL fails has `Θ<1` [L*]. A DH-violating world is therefore doubly instrumented [L*]/[D]:
- at the top: a finite layer at `β`, read by prime-only filters at every damping speed; Mertens power saving; a zero-free strip `Re s>β`;
- in the tail: infinitely many zeros approaching `Re s=Θ∞∈(½,β)`, with heavy returns later than `exp(c·y^{1−Θ∞−ε})`.

**Calibrations [L*].** Positive integer-norm two-scale Euler products with linear counting have an isolated top over a remainder at positive depth, and every graded repulsion bound is refuted on that class; classical Deuring–Heilbronn holds for a real zero of a quadratic `L(s,χ)`; ζ has no Siegel regime: `(1−Re ρ₁)log(|Im ρ₁||Im ρ₂|)>1/58` for every pair of zeros.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | world I consists of ZAL worlds only (finite stratum; approaching remainders): AAL ⇔ B13 ∧ Landing = (ZAL ⇒ RH); AAL research is RH-path research; the finite-layer receiver needs to be run only over remainders on the line |
| A proof that no FE ∧ Euler identity decides it | a world `½<Θ∞<Θ<1` is consistent with everything the corpus uses; AAL needs vertical transport (B112) |

**First step and obstacle.** The classical mechanism needs a zero that nearly cancels the pole; ζ has none. The anchor available here is the tail: on a line `Θ∞<σ<β` the complete filter that deletes the finite top is bounded by `C h^d t^N e^{at(c−σ)/2}` for every `c>Θ∞` when the remainder lies left of `c` [L*], and the top modes grow at rate `a(β−σ)/2`. The question is whether the reflected top `1−β̄`, entering through the FE, forces a term on the tail side that this bound forbids. Named obstacle: every filtered current is the filtered zero sum; a contradiction needs an inequality that the explicit formula does not imply, and no model with both structures exists to test one (§1.4).

**Tests.** T1: implied by AAL; implies none of ZAL, B13, quasi-RH. T2: an implication. T3: the table. T4: a tail statement. T5: false on integer-norm two-scale products [L*]. T6: not refuted. T7: moves B83, Γ184, F1, F8. T8: contains the exclusion of an isolated top over a ¬ZAL remainder; not Landau–Siegel.

**Limit.** One sector of AAL; B13 and Landing are separate atoms.

### Alternatives
| Question | Effect | Verdict |
|---|---|---|
| The filtered centred Vaughan current in the growth range (B145) | contradiction in world I | fails T1: it is the exclusion of the layer [D] |
| The transfer of S3 (B148); B56 | AAL and more | fail T1: imply AAL [D] |
| Graded recurrence; dominant-ordinate divergence | receivers in world I | theorems [L*]; neither excludes a layer |
| B13; the one-quartet world | the minimal finite layer | fail T8: single-quartet exclusion |
| Thick crude count, sampling-set bound, lag recurrence (B110, B126, B127) | AAL | contain AAL |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form; "positivity" includes nonnegativity of counts, Dirichlet coefficients, kernels and averaging measures, the Hodge index and Tate limits. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, continuation, power sums, integrality, Diophantine approximation and transcendence, recurrence, Jensen and Rouché.

**What survives [L*].**
- **Receiver.** RH ⇔ `|c_p|≤K` on arbitrarily late log-square windows, proved with complex deletion filters and no positive averaging; width form; RH ⇔ the ordinate is injective on the zeros.
- **Counting by winding.** A Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points; the bound passes to locally uniform limits; the Eisenstein constant term is pure because its dominant half lives where the Euler product converges absolutely.
- **Priced producers.** Frobenius at one prime, cost `m·θ(S)`, primorial inseparability; integrality reaches Chebyshev; exponential sums reach VK; heavy returns are excluded to the VK height and, in a strip, to `exp(c·y^{1−Θ∞})`; separation by absolute value is excluded for ζ.
- **The transfer.** "No heavy identity return below a power height ⇒ the floor on one window" implies `Θ<1⇒Θ=½`; its hypothesis is implied by quasi-RH [D]. It is not a question below quasi-RH.

**The question.** *Is there an arithmetic splitting `ξ=E+E^♯`, `E^♯(s)=\overline{E(1−\bar s)}`, whose defect is bounded and certified by sizes?* That is: an entire `E`, a finite divisor `W` in the right half-plane of degree `κ`, and an inequality `|W^♯(s)E^♯(s)|≤|W(s)E(s)|` on `Re s>½` proved from Dirichlet-series sizes, Stirling and exponential sums alone. By the index law ξ then has at most `κ` right zeros [L*].

**Why it opens the path under the constraint.**
- It is the only conversion from sizes to the location of every zero that uses neither a sign of a form nor an operator, and the corpus has its two theorems: the index law and its semicontinuity [L*].
- It has a calibration where it works and one where it fails: the Eisenstein pencil (certified by absolute convergence) [L*]; the natural theta half-transform (infinitely many right zeros of the half) [L].
- For the natural deformations the defect degree is the width axis (§1.9): a certificate must reach inside the strip, which sizes on `Re s>1` do not. What is asked is a size statement at the exact normalization, the place where the non-tempered pair fails.
- Candidate splittings outside the corpus: the Riemann–Siegel halves [C]. Whether the right-half zeros of such a half are finitely many is not known to the corpus.

**Strength.** A bounded defect is finite off-line support, hence at least ZAL; RH then needs B13. The question is strong; under the constraint no question below quasi-RH passes (§3, tests).

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L*]/[L].** The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; its resonances sit at the zeros of `ξ(2s)`; one cavity function of Hecke forms sees every resonance and RH ⇔ its energy decays at `y^{¾−ε}`; the reflection Krein form has one negative square per off-line zero. With a cutoff at cusp height `Y≥1` the constant term `Λ(2s)Y^s+Λ(2s−1)Y^{1−s}` has no non-real zero off the line, and one real exceptional zero exists exactly above `Y=4πe^{−γ}`. Weil's functional on packets is the limit of energies built from truncated Maass–Selberg diagonals at cusp height one with one scalar counterterm. A bulk built from one adelic-invariant kernel with Weil's diagonal does not exist; a summably weighted adelic Green kernel is a positive covariance and does not sign Weil's form.

**The reading [D].** Every regulated horizon in the corpus is pure: the cutoff makes the secular function an index-one object, by unitarity in the physical reading and by the parity of the Maass–Selberg defect in the proof. Purity is lost only in the renormalized limit, and the limit of the cutoff family is `Λ(2s)+Λ(2s−1)`-type, not ξ. The index is lower semicontinuous: a limit of regulated systems with at most one complex mode has at most one.

**The question.** *Is there a unitary regulator of the modular horizon whose secular functions converge to ξ?* A family of self-adjoint boundary conditions on the quotient of the wedge — a wall, a stretched horizon, a defect at a marked point — whose secular functions are conjugation-real, have at most one right-half zero, and converge locally uniformly to ξ as the regulator is removed. Then RH holds [L*].

**Why it opens the path.**
- It replaces a sign at the horizon by two structural properties: unitarity of each regulated system and continuity of the limit.
- The identification of the limit is free: a limit with ζ's FE and a Dirichlet series is a multiple of ζ [L].
- It is what the closed classes leave: internal modular conjugation, vacuum-fixing partners, half-sided inclusions and the glued invariant bulk are excluded [L]/[L*]; regulators are not.
- It is calibrated: the cutoff family is pure and converges to the wrong limit; graph black holes with `t²>4q` are impure at every size [L]; the exceptional mode born at `4πe^{−γ}` shows what a regulator may create on the real axis and not off it.

**Second physical question (B147).** For one Hecke eigenform the receiver is complete up to one selection rule: no zero of its Shimura integral at `ρ/4+¼` for a nonhalving right zero `ρ` [L*]. A physical reason for that nonvanishing would make every single mode of the cavity a sharp receiver.

**Limit.** A regulator whose secular function is built from the zeros is a restatement; the family must be built from the places and the horizon.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*].** The arithmetic square is a curve whose diagonal has torsion conormal classes; its graphs meet in the primes and the contacts are the prime part of Weil's off-diagonal; the archimedean part is the trace of the same Frobenius on the jets; no object of finite type carries the contacts; a tower of lines does, with an exact count of sections; a section count with Riemann–Roch and Bézout exists iff the Hodge index holds. The gluing index of the first `N` graphs is `N!`; with `T_n=2π(n+½)`, the zeros with height in `(T_n,T_{n+1}]` minus the `log(n+1)` gluing conditions of `Γ_{n+1}` minus the increment of the remainder `S` tends to `0`. Weil's diagonal is the finite part of the jets on combs, with counterterm the logarithm of the comb's density. The pairing of the degree points — jets plus twice the contacts minus the comb counterterm — tends on packets to the pole minus Weil's functional. The orientation cover over ℤ has centred count `M(N)`, weight `≥½`, weight `½` ⇔ RH.

**Geometric question (B149).** *Does Bézout hold for effective classes on the tower of lines with the comb pairing?* The tower supplies the Riemann–Roch half: sections of level `M` with `b` digits in `[−A,A]` on each of `τ(M)` lines are counted exactly. The pairing of two classes is contacts plus jets minus the comb counterterm. Is the pairing of two classes with sections nonnegative, on packets of one logarithmic window and off power-thin exceptions? By the section-count theorem and the window criteria this is RH; the geometric content is a reason other than the explicit formula.

**Topological question.** *Is the remainder `S(T)` the index of the archimedean gluing?* Graph by graph the square counts the zeros up to the increments of `S`. Is there a complex attached to the tower and its archimedean weight fibre whose Euler characteristic over the height window `(T_n,T_{n+1}]` is `log(n+1)` plus an archimedean correction equal to the increment of `S`, with first cohomology spanned by the zeros of that window? Purity would then be a statement about one graded piece per graph.

**Why these open the path.**
- They are the only two-dimensional statements the no-gos leave: not finite type, not a glued invariant carrier, not a duality between contacts and jets, not a diagonal attached to a point.
- Both use objects with exact counts: the digit count of the tower and the gluing index.
- The calibration is exact over `𝔽_q[T]`: no carries, `N(qx)=qN(x)+1`, the orientation cover has `qⁿ` points; over ℤ the carry term is `(2 log 2−1)N` [L*].

**Limit.** Bézout on effective classes is the Hodge index; an index theorem with correction `S` counts zeros and does not locate them.

## 2.9 New field for RH: Hodge theory of a fixed part

**Does RH need a new field?** Yes. Each known conversion of a statement in law into a statement at every zero has an exact price over ℤ: a sign needs a two-dimensional object, and the square is a curve; an integrality gap needs cheap vanishing, and its cost is the count; recurrence stops at the Kronecker scale; a family sees only its variable part; separation is a receiver; limits of pure objects follow the width axis (§1.4–§1.9). ζ is rigid, infinite-rank, and its diagonal is a comb finite part. No existing theory proves a Hodge index for such an object.

| Aspect | Content |
|---|---|
| What it is about | Positivity and index theorems for one rigid object: the pairing of degree points given by contacts, jets and a comb counterterm; its effective classes; its defects in the sense of the index law |
| What it would be like | Arakelov theory in which the datum at a point is the density of a comb, not a metric; intersection numbers that are finite parts; statements local in scale, on packets of one logarithmic window, with power-thin exceptional sets; no families and no moduli |
| Criteria | Reproduce Weil's proof for curves, where the comb is `q^ℤ`. Reproduce the Lagarias–Suzuki line law as an index-one statement. Fail on the golden datum, the integer-norm one-offs, the approaching Euler product, the `cosh` models, the heat family and the non-tempered pair. Use the coefficient size exactly. Not be uniform in real characters unless it excludes exceptional zeros. Be pointwise. Respect the no-gos: no finite type, no glued invariant carrier, no duality between contacts and jets, no diagonal attached to a point |
| Questions it must answer | Which comb is canonical on a window? What is the second axiom that turns the exact section count into Bézout? Is the index of the degree-point pairing at most one on every window? How do the carries, the defect between the Λ-structure and addition, enter the pairing? Why does the argument fail for integer-norm monoids, which the square does not see? |
| Tools it aims to develop | Calculus of comb finite parts (Lévy–Khintchine on combs); section counts on towers of lines; the index law at infinite rank; window locality with exceptional sets; the carry cocycle; ordered approximations (the arithmetic clock) |
| Objects | The arithmetic square and its graphs; contacts; jets and weight lines; combs and their densities; the tower of lines; the toric surface of a base; clock energies; defects |
| Language | comb, density, finite part, contact, jet, weight line, gluing index, effective class, defect, index, window, exception |
| Mechanisms | Built on: contacts plus jets, comb finite parts, section count ⇔ Hodge index, index law and its semicontinuity, logarithmic windows with exceptions [L*]. To discover: Bézout for effective comb classes, or the bound "index at most one", from a property of the tower |

**Main conjecture (Castelnuovo–Severi for combs).** On packets of degree points in one logarithmic window the comb pairing satisfies `D·D≤2d₁d₂` off a power-thin exceptional set, for a reason intrinsic to the tower. **Milestones.** M1 [L*] contacts, jets, comb finite parts, section-count theorem, windows. M2 the degree-point pairing in Lean on the tower. M3 the statement over a curve in comb language. M4 Bézout on windows of bounded aperture, checked against the verified windows. M5 RH.

## 2.10 New field for AAL: arithmetic surgery theory

**Does AAL need a new field?** Yes. AAL says that no finite layer of zeros can be isolated at the top. World I is completely described and its identities are consistent; over a curve the statement is free by periodicity; over ℤ the zeros contain no vertical progression and no `ℓ²` perturbation of one, the only exact symmetries of the prime orbit are dilations and the FE preserves height [L*]/[L]. What is missing is an obstruction theory for finite modifications of the divisor of an object with both structures.

| Aspect | Content |
|---|---|
| What it is about | Finite surgery on the zero divisor of an FE–Euler object: which of the structures — Euler product, Dirichlet series, FE, coefficient size, the count `⌊x⌋` — survive the insertion, removal or relocation of finitely many quartets; isolated layers as obstructed surgeries |
| What it would be like | Obstruction theory: a finite layer has a class in arithmetic data (first integer gap, Bohr almost periodicity, annihilator mass, heavy-return exponents), and AAL is the vanishing of the set of unobstructed layers |
| Criteria | Reproduce periodicity over `𝔽_q`. Fail on the one-offs, the two-scale and approaching Euler products, the `cosh` models and `ζ(s−h)`. Not be a statement in law. Respect the two-scale law. Permit real isolated zeros where the classical theory permits them and forbid non-real ones |
| Questions it must answer | Is the divisor of ζ surgery-rigid? Which invariant detects an inserted layer in the presence of both structures? Does the FE turn an isolated layer into a second layer at another height? Does the tail at `Θ∞` constrain the top (DH)? |
| Tools it aims to develop | Relocation calculus (rational surgery destroys the Dirichlet series; first-gap negativity) [L]; finite-layer filters; heavy-return laws in a strip; positive annihilators and their phase geometry; graded recurrence against density theorems |
| Objects | Finite layers, tails, filters, corrected currents, annihilators, relocation densities, Euler heads and tails |
| Language | layer, tail, surgery, relocation, obstruction, sector, transport, replication |
| Mechanisms | Built on: the sector theorem, the instrumentation of world I, the calibrations, classical Deuring–Heilbronn [L*]. To discover: an obstruction to isolating a non-real layer that uses the FE and the Euler product jointly |

**Main conjecture (surgery rigidity).** No object with ζ's functional equation, Euler product and coefficient size has an isolated non-real top layer. **Milestones.** M1 [L*] world I instrumented. M2 an obstruction class for a one-quartet layer. M3 DH (B141). M4 the landing sector. M5 AAL.

## 2.11 New field for RH without positivity: sign-free index theory of arithmetic splittings

**Does a positivity-free RH need a new field?** Yes. The two sign-free proofs of a Riemann hypothesis have priced shadows over ℤ: Stepanov's needs a Frobenius with zero derivative, and the cost of simultaneous vanishing is the count; separation by a Newton polygon needs coefficient gaps, and the critical ordinates have none [L*]. The transfer from returns has the strength of strip self-improvement [D]. What remains inside the constraint is counting by winding.

| Aspect | Content |
|---|---|
| What it is about | Splittings `ξ=E+E^♯`, their defects, and size certificates for the defect degree; limits of functions of bounded index |
| What it would be like | Hermite–Biehler theory with no positive kernel: only comparisons of moduli and winding numbers, with sizes supplied by Dirichlet series, Stirling's formula and exponential sums; two-sided local bounds on windows as the prime-side interface |
| Criteria | No sign of a form and no operator. Prove the Lagarias–Suzuki law in its own language. Fail for the non-tempered pair. Be pointwise. Not be uniform in real characters unless it excludes exceptional zeros. Explain why the natural theta half fails |
| Questions it must answer | Which splitting has a bounded defect? How does the defect degree move along the natural deformations, where it is the width axis? Can a two-sided bound on logarithmic windows be converted into a size comparison of two halves? What is the archimedean substitute of a Newton polygon for a function whose zeros are not lacunary? |
| Tools it aims to develop | The index law and its semicontinuity; Rouché counts; signed deletion filters; two-sided window criteria; exponential sums at the exact normalization; ultrametric calibration |
| Objects | Halves, defects, pencils, exceptional parameters, deletion filters, windows |
| Language | half, defect, index, exceptional point, size certificate, winding |
| Mechanisms | Built on: index law, semicontinuity, signed window criteria, ordinate injectivity [L*]. To discover: a size certificate inside the strip |

**Main conjecture (bounded defect).** Some arithmetic splitting of ξ has a defect of bounded degree, certified by sizes. **Milestones.** M1 [L*] index law; pencil; signed windows. M2 the Lagarias–Suzuki law and `ξ(s+½)±ξ(s−½)` from sizes alone. M3 a splitting with defect `O(log T)` in height windows. M4 a bounded defect (finite stratum). M5 B13 without a sign.

## 2.12 New field for RH as AdS physics: cutoff holography of arithmetic horizons

**Does it need a new field?** Yes. The horizon has complete receivers and exact Krein bookkeeping; the bulk reading with one invariant kernel is refuted; every regulated horizon in the corpus is pure and converges to the wrong limit. There is no theory of the regulators of an arithmetic horizon and of the index along their flow.

| Aspect | Content |
|---|---|
| What it is about | Families of self-adjoint boundary conditions on the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`: cutoffs at cusp height `Y`, walls, defects at marked points; their secular functions; the number of complex modes along the flow; renormalized limits |
| What it would be like | Holographic renormalization with a Krein count: each regulated system is unitary and has index at most one; exceptional real modes are born at explicit thresholds; the renormalized limit inherits the index bound |
| Criteria | Build from the places and the horizon, never from the zeros. Reproduce the line law at every cutoff, the threshold `4πe^{−γ}`, the scattering-tower normalization, the reflection Krein law and the cavity receivers. Make graph black holes with `t²>4q` and the non-tempered pair impure. Avoid the closed classes |
| Questions it must answer | Which regulator has secular functions converging to ξ? Is the index monotone in the cutoff? What is the mode born at `4πe^{−γ}`? Is the reflection Krein form the limit of the positive forms of regulated systems? What selects the Shimura nonvanishing for one eigenform? |
| Tools it aims to develop | Walls and pseudo-Laplacians [C]; Maass–Selberg calculus at general cutoff; the index law and its semicontinuity; the scattering tower; cavity energies and reflection Krein forms |
| Objects | The modular horizon, cutoffs, seeds, cavity functions, constant terms, exceptional parameters, reflection Krein forms, weighted adelic Green kernels |
| Language | regulator, cutoff, wall, secular function, exceptional mode, index, renormalized limit, cavity, resonance |
| Mechanisms | Built on: line law, exceptional parameter, scattering tower, cavity receivers, Krein law, index semicontinuity [L*]. To discover: the regulator |

**Main conjecture (unitary regulator).** A family of self-adjoint regulated horizons has secular functions of index at most one converging locally uniformly to ξ. **Milestones.** M1 [L*] cutoff family, tower, receivers. M2 the index along one regulator flow other than the cusp cutoff. M3 a regulator whose limit has ζ's FE. M4 a universal positive decay rate (zero-free strip). M5 RH.

## 2.13 New field for RH as topology or geometry: gluing index theory of the arithmetic square

**Does it need a new field?** Yes. The geometric objects exist with exact counts — the square, its contacts, the tower of lines, the gluing index, the orientation cover — and the classical forms of the surface are closed: finite type, an invariant glued carrier, a duality between the finite and the archimedean parts. There is no index theory for an object of infinite type whose analytic index is a zero count in a height window.

| Aspect | Content |
|---|---|
| What it is about | The lattice of gluing conditions of the Frobenius graphs, of index `N!`; the comparison of its growth with the zero count; the archimedean correction `S(T)`; section counts on the tower of lines; the weight of the orientation cover |
| What it would be like | An index theorem per graph: zeros in the height window `(T_n,T_{n+1}]` against `log(n+1)` gluing conditions, with an archimedean correction of eta type; a cohomology of infinite rank with a filtration by height windows; geometry in which carries are the defect from the function-field case |
| Criteria | Reproduce `𝔽_q[T]`: no carries, self-similar counts, an orientation cover with `qⁿ` points. Explain the carry proportion `2 log 2−1`. Respect the no-gos. Express purity as a statement about one graded piece. Calibrate on integer-norm monoids, which the square does not see |
| Questions it must answer | Is there a complex whose first cohomology in a height window is spanned by the zeros of that window? Is `S` the index of the archimedean gluing? Does Bézout hold for effective comb classes? What is the weight filtration on the middle cohomology of the orientation cover at infinite rank? |
| Tools it aims to develop | Necklace lattices and gluing indices; counts on towers of lines; comb finite parts; infinite-rank Lefschetz theory with the Meyer flow; carries as a cocycle |
| Objects | Graphs, contacts, necklace matrices, towers of lines, weight lines, combs, the orientation cover, the Meyer flow |
| Language | gluing condition, gluing index, height window, correction, carry, effective class, weight |
| Mechanisms | Built on: gluing index against the zero count, contacts, tower of lines, section count ⇔ Hodge index, orientation-cover weight [L*]. To discover: the local index theorem and Bézout |

**Main conjecture (local index).** For every graph the zeros of its height window, its gluing conditions and the increment of an archimedean index are the three terms of one index formula, and the comb pairing is nonnegative on effective classes. **Milestones.** M1 [L*] gluing index and its asymptotics. M2 a complex realizing the count per window. M3 the correction identified with `S`. M4 Bézout on windows of bounded aperture. M5 RH.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a product with itself and one of the two proofs for curves runs: Weil's (a surface with a Hodge index) or Stepanov's (an endomorphism and an auxiliary). The programme is `AbsoluteGeometryOfSpecZ`; its nine founding questions are answered [L*].

**What the corpus fixes.**
| Question | Answer | Evidence |
|---|---|---|
| Which endomorphisms have `N(n)` fixed points | the Witt Frobenius `F_n` on `𝒢=W(ℤ)`; on the diagonal `log#(ℤ/J(1,n))=Λ(n)`; `1+1/(n²−1)` is the trace of `F_n` on the jets; `N` itself is not an element of the square | [L*] |
| Multiplicity at a prime over `𝔽₁` | the order of the `p`-derivation; on ℤ it is `v_p`; between graphs the contact order | [L*] |
| Why the diagonal is not local | it is a branch of a curve with torsion conormal classes; its archimedean entry is `log(density/2π)` of a comb | [L*] |
| Ampleness; Riemann–Roch ⇒ Hodge index | not without a second axiom: Riemann–Roch and Bézout together are the Hodge index; no finite-type object carries the contacts | [L*] |
| Gamma factor and pole as geometry | weights of the same Frobenius on the sequence ring: `0,1` for the pole plane, `−2j` for the jets; not in `𝒢` | [L*] |
| Integer-norm monoids other than ℤ | invisible to the square: the lift goes through the norms; the dividing line is the additive count `⌊x⌋` | [L*] |
| Normal direction of the diagonal | none in characteristic zero in the square; `∂/∂Y` on the toric surface of a base, restricting to `δ_p` through a Fermat quotient | [L*] |
| A duality exchanging contacts and jets | none; transposition is the FE and preserves both parts | [L*] |
| Weil's diagonal as a finite part | on combs of degree points, with the comb's counterterm; on the adelic carrier a density; never one glued invariant object | [L*] |

**State of the constructions.**
| Construction | State |
|---|---|
| A. Frobenius lifts (the Stepanov side) | closed: order `m` at the primes of `S` costs `m·θ(S)`; survivor: the cofree square with exact contacts [L*] |
| B. Carries (transport from `𝔽_q[T]`) | closed: the carry term is a fixed proportion `2 log 2−1` of the window count [L*] |
| C. The surface (the Weil side) | the invariant glued carrier is refuted; survivors: comb finite parts, the weighted covariance, the scattering tower, the clock [L*] |
| D. The archimedean fibre | built as weight lines with the jets and the pole plane; no gluing by a duality [L*] |
| E. A second dimension | the toric surface of a base (normal direction, bilinear count, forced zeros are the contacts) and the tower of lines (contacts with an exact count) [L*] |

**Criteria the construction must meet.**
1. Reproduce Weil's and Stepanov's proofs for curves; over `𝔽_q[T]` there are no carries.
2. Counts alone are not enough: the golden datum has effective elements and is impure [L*].
3. Use the FE: the integer-norm one-off and the approaching Euler product must fail.
4. Use the Euler product: `cosh` models and the heat family must fail.
5. See the coefficient size: the non-tempered pair must fail.
6. Infinite type: no finite fibre; no finitely generated Frobenius-stable lattice.
7. The diagonal is a comb finite part with Weil's constant, not the discriminant and not a number attached to a point.
8. Positivity, if used, is derived: Riemann–Roch and Bézout are two axioms.
9. The archimedean place is a fibre of the same Frobenius.

**Questions the programme must answer.**
- Q10 One object: is there a ring of sequences, stable under the shifts `F_k`, that contains the tower of lines, the pole plane and the jets, and in which the cyclic module of the prime-counting sequence has the zeros as weights?
- Q11 Bézout: on that object, do classes with sections pair nonnegatively in the comb pairing (B149)?
- Q12 The comb: which density is canonical on a logarithmic window, and how does the pairing change between combs?
- Q13 Carries: is the carry cocycle the class of the deformation from `𝔽_q[T]` to ℤ, and does it bound the defect of the window count by anything better than a proportion?
- Q14 Integer norms: which additive datum, invisible to the Λ-structure, separates ℤ from an integer-norm monoid with an off-line pair?

**Tools.** Witt vectors and Λ-structures; necklace coordinates and gluing indices; towers of lines with digit counts; comb finite parts; weight lines of the shift; the carry cocycle; the index law.

**Objects and language.** Arithmetic square, graph, contact, ghost component, Teichmüller point, orbit, tower of lines, base, weight line, jet, pole plane, comb, density, carry, effective class.

**Mechanisms.** Built on the answered questions and the section-count theorem [L*]. To discover: Bézout for effective classes on the infinite-type object; the additive datum of Q14.

**Milestones.** M1 [L*] questions Q1–Q9. M2 the object of Q10 with its section count in Lean. M3 the comb pairing on it equal to pole minus Weil's functional on packets. M4 Bézout on windows of bounded aperture, against the verified windows. M5 Bézout (RH).

**Decisive early test.** An integer-norm system with an off-line pair lifts to the square through its norms and is invisible there [L*]; it violates the Stepanov bound at the prime degrees [L]. A construction whose Bézout holds for it cannot prove RH; the additive datum of Q14 must make it fail.

## 3. The one big question: what is the resolution of the minimal face?

**Question (B143).** Let `𝒵` be the class of tempered reflection-symmetric zero configurations without real zeros, with lowest ordinate at least `γ_min>0` and local counts `N(t+1)−N(t)≤C log(|t|+3)`.
1. *Bounded windows.* Is there `L=L(γ_min,C)` such that a floor `2 Re S(u)≥−K` on windows `[u_k,u_k+L]`, `u_k→∞`, forces every zero of a configuration in `𝒵` onto the line?
2. *Unbounded windows.* If not, does every radius `R(T)→∞` decide `𝒵`, or is there a configuration in `𝒵` with an unattained or accumulating top that is bounded below on windows of radius `R(T)=o(log T)` beyond every bound?

**What is proved [L*].** Radius `32 log(T+2)` decides ζ, with power-thin exceptional sets and in width form. Radius `r√T` decides every tempered configuration. Under `δ`-separation of the deep ordinates the length `80/δ+1` decides, from either side. Without a lowest ordinate no fixed length decides: an off-line pair of ordinate below `π/L` passes. On windows of unbounded length a floor puts an attained top on the line, so it excludes world I.

**What the proofs show [D].** With ordinates at least `γ_min`, a single off-line mode is negative inside every window longer than `2π/γ_min`. A configuration can pass a floor on a window only if, for every cluster of deep ordinates, the envelope of the cluster is small on the whole window. A cluster of `n` modes of diameter `ε` has envelope at least of order `(εR)^{n−1}` times its size on a window of radius `R`, and its size grows like `e^{bT}`; a fixed finite cluster therefore becomes visible on every later window of fixed radius. A counter-configuration needs fresh clusters at every scale and compensation between clusters at different ordinates.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Bounded windows decide `𝒵` | RH ⇔ `∃C,K`: for infinitely many `x`, `P(p)≤A(p)+K` at the primes of `[x,Cx]`, off power-thin exceptions; the count door, the upper side and the two-sided form hold on the same windows; the separation hypothesis (B144) is unnecessary; a producer may work at bounded ratio on scales of its choice |
| Every unbounded radius decides, bounded ones do not | RH ⇔ the Stepanov bound on runs of integers `[x,e^{L}x]`, `L→∞`, with no ZAL premise: every window-type receiver of AAL is a receiver of RH, and world II cannot hide below the logarithmic radius |
| Only radius `≍log T` decides | an interference theorem: tail worlds with ζ's counting pass every sub-logarithmic floor; the logarithmic radius is the resolution of the minimal face; ZAL cannot be removed from sub-logarithmic receivers; the construction exhibits the cluster structure world II must have |

**Why this question.** RH has one minimal face shared by the three wall families, and the resolution of that face is the last open parameter of its receiver. The answer decides whether the exceptional coordinate can be bypassed on the prime side: on unbounded windows world I is excluded by a floor, and the question is whether world II is too. It is a statement about configurations, implied by nothing about ζ.

**First step and obstacle.** Replace separation by a cluster decomposition (A78): group the deep ordinates into clusters of diameter `η`; inside a cluster of at most `C log γ` modes a Turán-type inequality bounds the envelope on a window from below at a cost polynomial in `γ`, so each cluster is visible once `e^{bT}` exceeds a power of `γ`. The named obstacle is compensation between clusters when the deep ordinates have no gap structure at the scale of the window: a compactly supported positive kernel isolates one carrier only if the neighbouring clusters are separated from it by more than the inverse window length.

**Tests.** T1: method. T2: three stated alternatives. T3: the table. T4: no finite rung. T5: calibrated on the low off-line pair (bounded fails without `γ_min`), separated configurations (bounded suffices), general tempered configurations (`√T`), one Frobenius (aliasing). T6: not refuted. T7: moves Σ146, Σ148, B130, B126, B144, F1, F2. T8: not a named problem; first step in corpus objects, one named obstacle.

**Limit.** It decides where the bound must be proved, not whether it holds. No question below AAL that passes the tests does more.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| Polar orthogonality (B104, §2.4) | the critical curve becomes one inequality | passes; Σ block only |
| Deuring–Heilbronn for ζ (B141, §2.5) | AAL reduced to the RH path | passes; no model with both structures to test a mechanism |
| Shimura nonvanishing (B147) | one eigenform as a sharp receiver | receiver only |
| Separation of the off-line ordinates (B144) | bounded windows for ζ | no first step |
| Depth density `o(T)` (B57); bounded form factor (B150) | first unconditional near-line inputs | census problems; cannot decide an atom |
| `Θ<1⇒Θ=½` (B56); the transfer of S3 (B148) | RH from quasi-RH; a route through returns | fail T1: imply AAL [D]; no mechanism |
| The filtered centred Vaughan current (B145) | contradiction in world I | fails T1: the exclusion itself |
| An independent family of bounded index (B146); Bézout on the tower (B149) | RH | producers of RH strength |
| Finite stratum (B13); landing as an atom (B138) | atoms of the RH path | B13 fails T8; landing is settled as a method question and is not posed |
