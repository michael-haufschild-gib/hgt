# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`), `walls-ledger.md` (labels
Σ/Π/Γ) and `route-unification-ledger.md` (core problems, route classes). Corpus: `9ff1dbfc9a` with
the working tree. Evidence: `[L]` integrated Lean; `[S]` working tree or not wired into its umbrella;
`[D]` derived here from Lean statements. Window lengths `A`; LST/ACS/RW half-widths `a = A/2`.

## 1. The big picture

### 1.1 RH has become a statement about a tower of finite objects
The corpus has turned Weil's criterion into a statement about **windows**: RH holds iff Weil's form
`Q` is nonnegative on every test supported in `[−A, 0]`, for every length `A` [L]. A window is a
finite-type arithmetic object:
- it sees only the prime powers `n ≤ e^A` — two weights agreeing there have the same functional on
  every test of the window [L];
- on it, Weil's form is
  `Q(H) = Ω(0)‖H‖² + J_∞(H) + Σ_{n≤e^A}(Λ(n)/√n)(½fold_n(H) − sym_n(H)) + 2Ĥ(0)Ĥ(1)`:
  the Gamma factor contributes a negative constant `Ω(0)` and a Lévy jump energy `J_∞ ≥ 0`, each prime
  power acts by **one fold** of the window onto itself (left end `[−A, −log n]` onto right end
  `[log n − A, 0]`), and the pole contributes `½⟨2cosh(u/2),H⟩² − ½⟨2sinh(u/2),H⟩²` [L], which is the
  product `2Ĥ(0)Ĥ(1)` of the transform at `0` and `1` [D];
- each fold is a nonnegative antisymmetric count minus a **symmetric fold mass**
  `sym_n = ½∫(H + H(·+log n))²` over the left end; these are the only negative arithmetic terms [L];
- the prime cost of the window is a canonical density `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})`, the
  half-weighted Chebyshev function at the distances to the two ends, with degree
  `deg K_A = 2ψ_{1/2}(e^A) − Ω(0) ≈ 4e^{A/2}` [L];
- its negative index `ι(A)` is finite, Shannon-bounded, monotone in `A`, zero for `A ≤ 3/5`, and
  `sup_A ι(A)` is the number of zeros right of the line [L]; negativity lives only at the two pole
  values and in a finite frequency band `|τ| ≤ τ₀(A/2)` [L].

So **each window is a decidable finite problem, and RH is uniformity in `A`.** The analogy with
verifying zeros up to height `T` is exact in shape: a window of length `A` sees zeros up to its
Landau height `2πe^A` [L/D]. Proving positivity on longer and longer windows is calibration, not a
proof; the proof is a law valid for all `A`.

### 1.2 The degeneration has located `H¹`
The complete atomic Weil family degenerates along the resolution axis, and its pieces are
classified [L/S]:
- **bulk** (fixed conductor packets): the point count `J(1)#ℙ⁷(ℤ/m)` — positive, zero-blind, the same
  law over every finite ring, so the same over `ℤ` and over `𝔽_q[T]`;
- **twisted horizon windows** (weights twisted by any mean-zero periodic function — Ramanujan sums,
  characters): zero-blind, positive at every resolution, coercive; the conductor-two window has second
  order exactly `(7J(2)/K)∫e^{−8y}H²` with `J(2) = J(1)#ℙ⁷(𝔽₂) = 255J(1)` — a count, no Weil term [S];
- **untwisted horizon windows**: Weil's window form, plus at the critical curve the conductor-one count
  `(7J(1)/K)∫e^{−8y}H²`.

Read as a weight decomposition: every piece of the family is a **Tate piece** (a point count of
projective space over a residue ring) except one, and that one is `H¹` — Weil's window form. The
degeneration does not orient `H¹`, but it isolates it on the horizon layer: every complete-family
route (HF, SRT, AIP, ACT, SC, RW, CHMD) has the same sign problem, and the twisted directions are not
where zeros can hide. On the full space the cross-terms between the pieces are open (B2).

### 1.3 Every finite piece is paid; all of RH sits at infinity
Two finite statements are theorems:
- **Semiboundedness** [S]: `Q ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` on every window. The canonical degree
  bounds how negative a window can be.
- **The pencil** [S]: the critical-curve form `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` is nonnegative on every
  window with `κ·windowFloor(A) ≤ βJ/K`. The prime-free count term pays the whole arithmetic of any
  window of bounded length at bounded multiple `K`.

Together with the window-index law (index of the pencil monotone in `K`, equal to Weil's index for
large `K`, never above the right-zero count) [L], the sign question has a phase diagram in the
`(A, K)` plane: positivity holds near `A = 0` and near `K = 0`; RH is positivity on the whole
quadrant, i.e. in the double limit `A → ∞`, `K → ∞`.

The canonical degree has a direct meaning [D]: a zero `ρ = ½ + δ + iγ` contributes to a window of
length `A` at most `e^{δA}`; the budget `e^{A/2}` is the trivial strip `δ < ½`. The size of window
negativity is therefore the exponent `Θ − ½` in disguise: an exponent `< ½` is a zero-free strip,
subexponential growth is RH. The window form converts "where are the zeros" into "how fast does
negativity grow with the window length".

### 1.4 The producer must be a tower of unbounded rank
- No window has a finite-dimensional realization `Q(H) = ‖rH‖²`: short windows are coercive, so every
  window contains infinite-dimensional positive subspaces [L].
- Weil's kernel has no finite-rank realization: a rank-`r` form has positive index `≤ r`, while
  `K_ζ` has infinitely many positive squares whenever the right zeros are finite; under RH no
  finite-rank realization exists [S]. Scaling classes cannot be divisor classes on one arithmetic
  surface with a finite-dimensional Néron–Tate pairing.
- The window genus has main term `2e^A`, the Young conjugate of the zero density, equal to twice the
  theta count of `ℤ` at degree `A` [S]. Over a curve the genus saturates at `2g` and every window is
  realized in one fixed `ℂ^{2g}`; over `ℤ` it grows without bound [S].
- Counts already pay everything but the primitive part: on a window, Künneth Riemann–Roch reads
  `h_K(x) + h_K(−x) = χ(x) + h¹_K(x) + ½Q(H)` with `h¹_K > 0` a product of counts [S]. A naive height at
  bounded distance from the window Rosati form exists iff the window is positive (windowed Tate law)
  [S]; for one spectrally generic orbit an `ℕ`-valued count height on `ℤ[p^ℤq^ℤ]` decides RH, and the
  golden and complex fakes admit none [L].

So a geometric proof needs a **tower** — one finite object per window, of rank `≈ 2e^A`, compatible
as `A` grows — carrying `½Q(H)` as a count. Flooring a form already known to be nonnegative is
circular; the count must be produced independently.

### 1.5 Selection is a law in `A`
- Windows of bounded length cannot select ζ: a prime flip beyond `e^A` is invisible to every test of
  length `A` and is not Weil positive [S].
- Zero density cannot select: exact spline divisors with the full Riemann–von Mangoldt count, bounded
  undamped two-prime cone coupling and unattained positive width exist [S]. With a fixed Gaussian
  damping `exp(τ(ρ−½)²)` the same coupling bound is equivalent to RH [L].
- Contractive scattering positivity cannot place zeros: Blaschke pairs preserve the functional
  equation product, conjugation symmetry, boundary modulus and every Schur inequality while placing
  zeros anywhere in the half-plane [L].
- On a window, Frobenius at infinity is the involution `σ_AH(u) = H(−A−u)`, acting on transforms by
  `e^{−(s−½)A}Ĥ(1−s)`; its multiplier is unitary exactly on `Re s = ½`, but pair products are invariant,
  so `σ_A` is an isometry on every datum and orients nothing [S].

What distinguishes the line is a **growth rate in `A`** — the multiplier `e^{−(s−½)A}`, the window
energy `e^{t(z−½)}` of WD, the Gaussian damping. Local data, densities and contractions are blind.

### 1.6 What the three walls are
| Wall | Window form |
|---|---|
| Σ sign | the symmetric fold masses, `|Ω(0)|` and the odd pole square are paid by the Lévy jumps and the antisymmetric fold counts at every length; nonlocally (pointwise Markov calibration fails at `½ log 2`, `½ log 3`) |
| Π precision / production | the growth exponent of window negativity in `A` (budget `e^{A/2}` = trivial strip) and a count for the primitive window `h¹`, produced by a tower of rank `≈ 2e^A` |
| Γ selection | a law in `A`: the reflection `ρ ↔ 1 − ρ̄` must act as a positivity whose fixed line is `Re s = ½`; local, density and contraction selectors are blind |

They are three readings of the limit `A → ∞` of one tower. One sentence states what is missing: **an
arithmetic mechanism making the symmetric fold masses of every window a count, uniformly in the
window length.**

### 1.7 Where the edge is
The first window where the sign is not a theorem is prime-free: all-test positivity is proved for
`A ≤ 3/5`, and the window has no prime until `A = log 2 ≈ 0.693` [L]. The first unproved windows are a
statement about the Gamma factor alone, and are just work. The first prime (`T₂`, `log 2 ≤ A < log 3`)
is passed on the odd sector (to `0.724`) and on the `cosh`-orthogonal hyperplane (to `log 2 + 1/50`),
not on all tests [L]. The first place where arithmetic must be paid by a count is `sym₂`.

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Join at `1/8`: band–far cross and threshold block `e ≍ c` against the three coercive pieces (risk: shifted prime-pair correlation, B41) | HF, SRT, AIP, ACS | coercive pieces in Lean; Schur and PNT-level inputs |
| A2 | Explicit horizons and constants (`1/9` theorem, logarithmic profile, Beurling schedule, horizon criterion, window-index convergence) | HF, SRT, AIP, ACS, RW, SC | constants |
| A3 | Certified window positivity by stage: all tests on prime-free windows `3/5 < A < log 2` (Gamma factor only); first-fold stage `log 2 ≤ A < log 3`; stages `log 3, log 4, log 5` | RW, EWU, OWU, HF, ACS, CWS | finite band, finitely many folds, Shannon-bounded index: interval-certified Schur complements |
| A4 | Phase diagram `(A, K)`: sharpen the pencil floor (exact pole product, weight `e^{−(β+1)y}`), tabulate `K*(A)` lower bounds, equality case `K = K*` | HF, SRT, AHD, CWS | estimates of explicit forms |
| A5 | Twisted windows at every conductor: second order of `c_m`- and character-twisted windows (Möbius–Poisson computation predicts the Jordan count at `m`); untwisted–twisted cross-terms at fixed twist; integrate conductor two | HF, SRT, AHD | the `m = 2` proof is the template |
| A6 | Integrate `[S]`: conductor-two window; six CWS modules (canonical-degree bound, window Frobenius, window genus, naive heights, curve windows, selection battery) and the Künneth edit; finite-rank no-go; RVM completed divisor; terminal-support loss; Cayley ladder; first-variation transfer; Poisson rigidity | all | proofs exist |
| A7 | Prime-successor comparison with the shell payment | HF, AIP, SRT | Mertens law and affine sampling |
| A8 | Quantitative depth law, star horizons, gcd-strata tabulation | HF, ACS | effectivization |
| A9 | Björner wedge decomposition of the squarefree complex | MC, HF | classical topology |
| A10 | WD polynomial stage as one statement; certified stopping prefix; flow threshold `Λ_X`; `ΔO` ⇒ density one ⇒ Lindelöf | WD, LA, TG | composition |
| A11 | Prime-free windows as a count: Lévy Poincaré inequality on an interval beyond length `1/1000`, with the pole signs | ACS, HF, RW, CWS | target is the Gamma factor alone |
| A12 | Künneth primitive `h¹` on the finite divisor at small degree | ACS, HF | calibration |
| A13 | Mixed-jet recovery for `≥ 3` primes; explicit main-term producer | WL, ACS | algebra |
| A14 | Census: `S_cos(λ)`, `λ ≤ 1`; odd stabilizer; `β = 2` | census, ACS | classical pair estimates |
| A15 | Voronoi summation; Zwegers' indefinite theta | ACS, HF | classical theorems |
| A16 | `𝔽_q(X)` calibration incl. second order over `𝔽_q(T)` and curve windows at second order | SC, ACS, HF, AHD | curve theory proved |
| A17 | Selberg-zeta normalization; scattering continuation into `Re(2s) < 1`; Lax–Phillips; Lewis–Zagier separation | PM | known mathematics |
| A18 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | PM | spectral-Eisenstein template |
| A19 | Prime-side identity for the Gaussian-damped two-prime coupling (heat-smoothed explicit formula) | SC, ACS | explicit formula |
| A20 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A21 | Hausdorff shifts, Jensen horizons, two-grid degrees, Toeplitz minors | PA, LA, HCF | effectivization |
| A22 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A23 | Mixed Schur debit; first-prime / coarse / polar costs | AIP, CHMD | fixed-dimensional estimates |
| A24 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A25 | Classical calibration of window negativity: express the classical zero-free region and density theorems as window-form bounds | all window routes | known zero information, explicit formula |
| A26 | General profiles beyond polynomial spans `θ < 1/1080` and the super-log-log clocks | HF, SRT, SC | constants and cutoffs |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ every `K·c*` ≡ horizon criterion ≡ Beurling schedule ≡ glued index `≤ 1` ≡ `ι(A) = 0` ∀A) | RH; fixed length sub | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD, MSC, FEL |
| B2 | Tate decomposition of the complete family on the full space (general conductors, cross-terms, growing twists, horizon localization) | sub | HF, SRT, AIP, ACS, SC, AHD |
| B3 | One fixed critical multiple on windows of every length (dense clusters) | sub | HF, SRT, AHD |
| B4 | Joint shell–pole / Gamma-graph payment | sub | HF, SRT, AIP, CHMD |
| B5 | Conductors above `√N`; general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B6 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B7 | Cluster exclusion below the Landau height | sub | RW, SRT |
| B8 | HL on the positive locus | RH | HF, TG, SC |
| B9 | Top coprime stratum | RH | HF, ACS, ADT |
| B10 | Cross-tower gap through the archimedean channel | method; RH | HF, AIP |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law | sub | SC, HF, ACS |
| B14 | Heat counts and horizons | sub / ≥qRH / LH | WD, LA, SC |
| B36 | Source-faithful realization (a tower of unbounded rank) | RH | RN, PTR, W1C, PM |
| B37 | Window Markov capacity: nonlocal Poincaré inequality at every length | RH; fixed length sub | CHMD, TT, HF, RW, OWU |
| B38 | Laguerre–Pólya (all ranks / degrees) | RH | TH, LA, HCF, PA, GTA |
| B39 | Scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B41 | Shifted prime-pair correlation (only if A1 needs it) | sub | HF, SRT, AIP |
| B42 | A count for the symmetric fold masses, starting with `sym₂` | sub per stage; RH uniformly | CWS, RW, ACS, HF |
| B43 | Growth law of window negativity: exponent `< ½` (zero-free strip), subexponential (RH) | ≥qRH; RH | all window routes, WD |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B15 | Subexponential window energy on every unit window | ≥qRH (log); RH (polynomial) | WD, TG |
| B16 | Log-free near-line density | sub | WD, census |
| B17 | Near-line density rate `≥ 1`; critical-scale clustering | sub | WD, census |
| B18 | Hecke defect pointwise / dyadic-uniform | ≥qRH / RH | WD |
| B19 | Input beyond counts + linear explicit formula | method | WD, HEF |
| B20 | Count-valued primitive `h¹` (naive height; generic two-prime `ℕ`-count; window tower) | RH; fixed length sub | ACS, HF, CWS, IRK |
| B21 | Genus law `≤ (2+η)e^A` | indep. | ACS |
| B22 | Logarithmic Serre duality | sub | ACS, HF |
| B23 | `ε`-uniform producer | sub / RH | WL |
| B24 | Square-root source input; Redheffer determinant | RH | WL, MC, PBM, RB, JAS, CTF |
| B25 | Near-band cyclotomic energy | ≥qRH | MC |
| B26 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B27 | First Epstein real zero on the boost line | sub | ACS |
| B28 | Bounded dense two-prime coupling | RH | SC, ACS |
| B29 | Bounded Gaussian-damped natural-cone coupling from the prime side | RH | SC, ACS |
| B30 | Finite-sieve Hodge positivity → global | RH | SC |
| B35 | PM energy / charge control | sub / ≥qRH / RH | PM |
| B44 | Mollified log-mean `= o(1)` from distributional input | sub | WD |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B11 | Band-pole noncancellation of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B31 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B32 | Frobenius at infinity as a positivity (Rosati / naive height; Hecke similitude; a positivity with symmetry `σ_A`) | RH | HF, ACS, CWS, PM |
| B33 | Euler-product FE twins; unimodular gauges | sub | HF, ACS, SC |
| B34 | A structure placing the `SL₂(ℤ)` resonances (via the reflection, not contraction) | RH / ≥qRH | PM, W1C |
| B40 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

**Q1. Does a count pay the first prime fold?**

In hand: the first-fold window form
`Q = Ω(0)‖H‖² + J_∞ + (log 2/√2)(½fold₂ − sym₂) + 2Ĥ(0)Ĥ(1)` [L]; the Lévy jump count pays the
prime-free form on windows of length `≤ 1/1000` [L]; positivity on odd tests to `0.724` and on the
`cosh`-orthogonal hyperplane to `log 2 + 1/50` [L]; pointwise folded-Markov payment fails at
`½ log 2` and `½ log 3` while Schur squares survive [L]; Künneth counts pay everything but `½Q` [S].

The question, in order: (0) certify all-test positivity on the prime-free windows `3/5 < A < log 2`
and read it as a Lévy count (A3, A11); (1) find an identity on the first-fold stage
`Q = (Lévy count) + (count attached to T₂) + (manifest squares)` that pays `sym₂` nonlocally; (2) if no
such identity exists, classify the counts that can read a fold and name the exact obstruction.

Why: `sym_n` are the only negative arithmetic terms of every window; a count for `sym₂` is the first
place over `ℤ` where a prime is paid by a count rather than by an estimate, and it is the seed of the
window tower (B42 → B20). It is finite, sub-RH, and decides whether the count programme (ACS, LST,
CWS, AE) can cross a prime at all.

**Q2. Is the complete family a count everywhere except on untwisted windows?**

In hand: bulk = `#ℙ⁷(ℤ/m)` [L]; twisted windows zero-blind and positive [L]; conductor-two window =
`J(2)` count [S]; untwisted windows = Weil + `J(1)` count [L]; pencil and window-index law [L/S].

The question: compute the second order of every `c_m`- and character-twisted window (predicted: the
Jordan count at `m`), and the cross-terms between untwisted windows, twisted windows and bulk
packets on the full space along `c⁸ = K log N`.

Why: if the answer is yes, the full complete-family form at the critical curve is
`(Weil's window form) ⊕ (point counts over ℤ/m)`, an identity with no estimate, so it crosses the edge.
HF, SRT, AIP, ACT and SC become literally Weil's window criterion plus counts (B2 closed), the join at
`1/8` (A1) is needed only below the critical curve, and the Tate/non-Tate split tells a window
cohomology which classes are counts (`ℙ⁷` over residue rings) and which one is `H¹`. If a mixed term
survives, it is new zero-carrying structure and a candidate producer.

**Q3. What is the growth law of window negativity in `A`?**

In hand: semiboundedness by the canonical degree `≈ 4e^{A/2}` [S]; the pair bound `e^{δA}` [D];
visibility law for isolated pairs [L]; window energy abscissa = twice the maximal depth [L]; log-stage
certificate ⇔ inverse-log corridor [L]; almost all unit windows zero-free beyond
`(1+ε) log log T/log T` [L]; moments cannot fix the mollified log-mean [L].

The question: (1) state the exact dictionary between the negativity of windows of length `A` and the
zero configuration (exponent `Θ − ½`, heights up to `2πe^A`); (2) read the classical zero-free
region and density theorems as unconditional improvements of the canonical-degree bound on
high-frequency and almost-all-height windows (A25); (3) prove subexponential negativity growth on
almost all windows — equivalently a log-free near-line density (B16).

Why: it unifies the precision routes (WD's window energy, the Hecke defect, the census) with the
sign routes (the window form) on one axis, and it turns "precision" into a growth exponent of a
quantity the sign routes already control at finite `A`. Its first step is sub-RH and belongs to the
classical mollifier/zero-detector toolbox.

## 2.4 A wildly different route

**Verdict: no route escapes all three walls. One direction escapes Σ and Π by its mechanism and meets
Γ in a new form: arithmetic measure rigidity of resonant states.**

Directions examined:

| Direction | Producer | Wall it falls on |
|---|---|---|
| Centered curve products / function-field limits | approximation + Hurwitz | Laguerre–Pólya closure (Σ26) |
| Extremal certificates from modular forms; crystalline rigidity | dual certificate | zero-side positivity is RH (Γ8) |
| Effective horocycle equidistribution | mixing rates | square-root precision of the Eisenstein constant term (Π) |
| Discrete Morse theory on the squarefree complex | cancellation | cancellation between dimensions (Π1) |
| One arithmetic surface (Faltings–Hriljac Hodge index) | Néron–Tate pairing | no finite-rank realization (Π18) |
| Iwasawa-type towers of growing rank | control theorems | it is the window tower itself (CWS); the positivity is B20 |
| Renormalization of the window tower in `A` (Lyapunov exponents, Hodge-norm variation) | sign of a variational formula | the curvature sign is the window sign (Σ1) |
| Contractive scattering / Lax–Phillips | Schur positivity | blind to zero position (Γ22) |
| Deformation / heat flow | noncrossing | crossing-free ⇔ positivity (Σ14) |

**The rigidity direction.** Every route produces a sign, a precision or a selector. A classification
theorem is a fourth kind of producer: it identifies an object by entropy and invariance, not by an
inequality.
- *Objects.* The scattering resonances of `SL₂(ℤ)\ℍ` sit at `s = ρ/2`; RH places them on `Re s = 1/4`.
  Each carries a resonant state (truncated Eisenstein series at `ρ/2`) with exact Hecke data and the
  partner angle `cos² = 4 Re ρ(1 − Re ρ)` [L].
- *Mechanism [D, heuristic].* Semiclassical limits of resonant states as `Im ρ → ∞` are conformal
  measures on the unit tangent bundle whose decay rate is fixed by `Re ρ`; the window Frobenius
  multiplier `e^{−(s−½)A}` is the same rate read on windows [S/D]. Hecke operators act on the limits.
  A rigidity theorem — positive entropy from Hecke recurrence, then classification of
  Hecke-recurrent conformal measures — would pin the rate to the symmetric value, i.e. `Re ρ = ½`.
- *Why it is far from every route.* No quadratic form, no window positivity, no prime count at any
  precision, no index. Its tools (entropy, measure classification, microlocal lifts) appear nowhere
  in the corpus. It uses exactly what every corpus selector lacks: a growth rate as an invariant, not
  a positivity.
- *Walls it meets.* Γ4 in a new form: the reflection `ρ ↔ 1 − ρ̄` (the fixed line `Re s = 1/4` of
  `s ↦ ½ − s̄`) is not a symmetry of the Laplacian; resonant states are not `L²`; their Hecke
  eigenvalues are non-tempered, which breaks the positive-entropy step as it stands; a semiclassical
  limit sees only infinite families, so it could first exclude off-line zeros accumulating at a fixed
  depth profile (a Lindelöf-type statement) before RH.

First test (sub-RH): Hecke-recurrent semiclassical limits of truncated resonant states along any
sequence `ρ_n` with `Re ρ_n → β` have conformal exponent determined by `β`, and positive entropy.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — a count pays the first prime
**Question.** Prove `ι(A) = 0` for all `A < log 3` by an identity whose terms are cardinalities, Lévy
jump counts and manifest squares — the Gamma factor's jump count, a count attached to the fold `T₂`
that pays `sym₂`, and the pole product.
- **Below RH.** A finite-window statement, implied by RH; its truth (not its count form) is reachable
  by certified computation (A3).
- **Advance.** The first prime over `ℤ` paid by a count: the first level of the window tower as a
  count, the first instance of B42, and the decisive calibration for B20. It either produces the
  object every count route lacks or names the exact obstruction at the first prime, where the
  pointwise Markov mechanism provably fails.

### 2.5.2 Route PM — a Mayer `Z`-function
**Question.** Build from the Mayer operator alone (geodesic Euler product, Lewis period functions,
whose three-term relation carries the reflection `s ↔ 1 − s`) a function real on the critical line
of the scattering parameter whose sign changes are the scattering resonances — the operator analogue
of Hardy's `Z(t)` — and prove infinitely many sign changes (Hardy's theorem), then a positive
proportion.
- **Below RH.** Hardy's and Selberg's theorems are classical; the content is their operator-native
  form.
- **Advance.** Contractive positivity is proved blind to zero position; the reflection is what PM
  lacks. A real-on-the-line Mayer object is the first statement in which PM uses the reflection, and
  the template for 2.6.2.

### 2.5.3 Route WD — almost every window is certified
**Question.** Prove the log-free near-line density `#{ρ : V ≤ γ ≤ 2V, |β − ½| ≥ A/log V} ≤ ε(A)V`,
`ε(A) → 0` — equivalently the log-stage Bessel–Szegő certificate on almost all unit windows; with it
the mollified log-mean `E log|ζM| = o(1)` that moment data cannot give.
- **Below RH.** A density statement; no Lindelöf, no zero-free region.
- **Advance.** WD's window machinery (prefix scale, canonical multiplier, Bessel cepstrum, door opener)
  is complete; this is its open input. It also gives `o(log U)` Hecke means and is the almost-all
  form of Q3.

### 2.5.4 Route HF — the Tate decomposition
**Question.** Prove that along `c⁸ = K log N` the complete tilted-spline form on all vectors is the
orthogonal sum of Weil's form on untwisted horizon windows plus point counts — `(7J(m)/K)∫e^{−8y}H²` on
each conductor-`m` twisted window and the Jordan counts on bulk packets — with vanishing
cross-terms.
- **Below RH.** It is an identity of limits; it needs no sign of Weil's form.
- **Advance.** HF's complete family becomes exactly Weil's window criterion plus counts; every
  complete-family route collapses onto one statement; the negative directions are localized on the
  full space; the whole-space `1/8` join is needed only below the critical curve. It also delivers the
  Tate/non-Tate split a window cohomology must reproduce.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — the window tower
**Question.** Construct for every window length `A` a finite object — a lattice or section space of
rank `≈ 2e^A` with an integral count — whose primitive `h¹` equals `½Q(H)` on window tests, compatible
under lengthening (folds acting as correspondences, departing folds paying their creation), with the
symmetric fold masses expressed as counts.
- **Why it opens the path.** A count at bounded distance from the window Rosati form is positivity by
  Tate's limit law, at every length; that is RH [L/S]. The finite-rank no-go says such an object must
  be a tower; the window genus says its rank; the Künneth law says counts already carry everything but
  `½Q`; the degeneration says which classes are Tate. What is asked is the one missing level structure.

### 2.6.2 Route PM — a reflection positivity on period functions
**Question.** Find a positive-definite Hermitian structure on the space of Lewis period functions
(or on the scattering channel of the Mayer operator) invariant under the reflection
`ψ(z) ↦ z^{−2s}ψ(1/z)`, such that a resonance off `Re s = 1/4` produces a negative norm — a Krein or
Lax–Phillips realization where the resonances are eigenvalues of a definite operator.
- **Why it opens the path.** RH is the placement of the poles of `Λ(s)/Λ(s+1)` [L]. Contraction cannot
  place them; a positivity whose symmetry is the reflection can, exactly as the window multiplier
  `e^{−(s−½)A}` is unitary only on the line.

### 2.6.3 Route WD — subexponential window energy from the source
**Question.** For every unit window at the polynomial stage and prefix `Θ(√m)`, prove from the
integer-theta source that `|𝒵_N(t)|²` grows subexponentially in `t`, via a source identity cancelling
the `e^t` flux through the right edge against its functional-equation image.
- **Why it opens the path.** Equivalent to RH at the polynomial stage [L]; the multiplier and the
  certificate follow automatically [L]. It is the growth law of Q3 on WD's own windows.

### 2.6.4 Route HF — the window Markov capacity
**Question.** For every window length `A`, prove the nonlocal Poincaré inequality
`J_∞(H) + Σ_{n≤e^A}(Λ(n)/(2√n))fold_n(H) + ½⟨c,H⟩² ≥ |Ω(0)|‖H‖² + Σ_{n≤e^A}(Λ(n)/√n)sym_n(H) + ½⟨s,H⟩²`.
- **Why it opens the path.** It is Weil's window criterion, hence RH, and by the horizon criterion and
  the Tate decomposition it is the whole sign problem of the complete family. It is a spectral-gap
  statement for an explicit jump process on an interval — archimedean Lévy jumps plus prime folds —
  whose payment must be nonlocal (graph Schur complements, harmonic hubs), since pointwise calibration
  fails at the first two primes.

## 2.7 Does closing RH need a new field?

**Assessment: yes, and its seed exists as CWS.** The corpus has built every structural layer of a
cohomology of windows of `Spec ℤ` — datum, locality, canonical class, Serre duality, Frobenius at
infinity, index, genus, naive heights, curve calibration, selection battery, Künneth form — and has
proved each axiom holds for every weight on the prime powers, ζ or not. The missing layer is the one
that produces positivity: the `h¹` as a count, uniformly in the window length. Three proved laws fix
its shape: it cannot be finite-dimensional or finite-rank (Π18); its rank grows like `2e^A` (Π16); its
Tate classes are point counts of projective space over residue rings and its single non-Tate class is
Weil's window form (Σ1j).

*What the field is about.* A **theory of the window tower of `Spec ℤ`**: for each length `A` a finite
arithmetic object `W_A` attached to the integers `n ≤ e^A`, with restriction maps as `A` grows, whose
first cohomology carries Weil's window form as a dimension or a count; an arithmetic Hodge theory
whose positivity comes from counting, organized as a tower with control theorems — closer in shape
to Iwasawa theory (towers of growing rank, characteristic objects, control) than to the cohomology of
one variety.

*Criteria it must meet.*
1. `h⁰` from arithmetic counts (theta count of `ℤ`); `h¹ ≥ 0` because it is a dimension, a cardinality
   or a log-count.
2. Locality: `W_A` depends only on `n ≤ e^A` and the Gamma factor; departing folds pay their creation.
3. Primitive `h¹(W_A) = ½Q(H)` exactly; the Künneth part `h¹_K` is the existing count.
4. The symmetric fold masses are counts; the antisymmetric fold counts and Lévy jumps are the
   correspondences acting on `W_A`.
5. Rank `≈ 2e^A` (window genus), never finite; Riemann–Roch with canonical class `k_A` (the half-weighted
   Chebyshev profile) and Serre duality `σ_A`.
6. Tate pieces reproduce the degeneration: `#ℙ^β(ℤ/m)` at first order and on twisted windows, with the
   profile exponent `β` as a dimension.
7. Frobenius at infinity: a positivity whose symmetry is `σ_A`, so that the multiplier `e^{−(s−½)A}`
   orients the line.
8. Selection by a law in `A`: fails for prime flips beyond their level, the golden fake, Epstein and
   `m² + 64n²` fakes; reproduces curves (genus saturating at `2g`, Stepanov, Castelnuovo–Severi).
9. Avoids every proved no-go: finite realizations, pointwise Markov calibration, contractive
   positivity, density selection, semilocal and trace carriers, separable gluing, free deformation,
   zero-blind limits, flooring.

*Questions it must answer.*
- What finite set does `sym₂` count? What is the count attached to a fold `T_n`?
- What are the restriction maps `W_A → W_{A'}` and their control theorem (how much of `h¹` is new at the
  stage where `n` enters)?
- Is there a scheme over `ℤ` whose points over `ℤ/m` give the twisted second-order counts and whose
  "conductor-one" part is the window form?
- What lattice of rank `≈ 2e^A` carries the sections of `W_A`, with what metric (the Gamma factor as
  Gaussian and as Lévy measure)?
- What growth law in `A` does the tower obey, and why does it force the exponent of window negativity
  to vanish?
- Which axiom fails for the fakes?

*Tools it aims to develop.* Nonlocal Dirichlet forms and Poincaré inequalities for arithmetic jump
kernels on intervals (graph Schur complements, harmonic hubs); point counting over finite rings and
Hensel towers; Iwasawa-style control of towers; λ-rings and Néron–Tate theory on `ℤ[ℚ_{>0}^×]`;
Arakelov `h⁰` on growing-rank lattices; Stepanov's auxiliary sections; Wiener–Hopf / Szegő
factorization; Krein-space scattering; entropy and measure rigidity (for 2.4).

*Objects, language, mechanisms.*
- Objects: windows `[−A, 0]`, stages `log n ≤ A < log(n+1)`, folds `T_n`, symmetric and antisymmetric
  fold masses, canonical class `k_A`, canonical degree, window involution and its multiplier, window
  index `ι(A)`, window genus, window Rosati form and naive heights, Tate pieces `#ℙ^β(ℤ/m)`, the tower
  `A ↦ W_A`.
- Mechanism A (count): `sym_n` as counts ⇒ window naive heights ⇒ Tate limit `≥ 0` ⇒ window positivity
  ⇒ RH.
- Mechanism B (capacity): nonlocal Poincaré inequality of the window jump process at every length ⇒
  window criterion ⇒ RH.
- Mechanism C (growth): a law in `A` forcing subexponential window negativity ⇒ RH; its exponent form is
  a zero-free strip.
- Mechanism D (placement): a reflection positivity on the scattering side ⇒ poles of `Λ(s)/Λ(s+1)` on
  the line ⇒ RH.

No corpus result shows that this field closes RH. Its first tests are 2.5.1 (a count at the first
prime) and 2.5.4 (the Tate decomposition), neither obstructed by zeros.
