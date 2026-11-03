# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`), `walls-ledger.md` (labels
Σ/Π/Γ) and `route-unification-ledger.md` (core problems, route classes). Corpus: `00c145cc47` with the
working tree. Evidence: `[L]` integrated Lean; `[S]` working tree or not wired into its umbrella;
`[P]` paper proof or plan on a pipeline card; `[N]` numerical; `[D]` derived here from Lean
statements. Window lengths `A` (window `[−A, 0]`); RW/LST/ACS half-widths `a = A/2`.

## 1. The big picture

### 1.1 A window is a module over a finite local algebra
RH holds iff Weil's form `Q` is nonnegative on every test supported in `[−A, 0]`, for every `A` [L].
The arithmetic acting on such a window is the Dirichlet ring truncated at `⌊e^A⌋`: the Hecke shifts
`n^{−1/2}H(· − log n)` compose like Dirichlet convolution and die past the window length, so
`ρ_A : f ↦ Σ_{n≤e^A} f(n)n^{−1/2}T_{log n}` is a ring map whose kernel is exactly the truncation ideal
[L]. In this language
`Q(H) = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H, H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²`, and `ρ_A(Λ)` is the logarithmic
derivative of the window zeta operator: `Z M Z^{−1} = M − ρ_A(Λ)` [L].

The tower `A ↦ W_A` is a chain of small extensions of local Artinian rings: each stage
`log n ≤ A < log(n+1)` adds one fold `δ_n`, which composes to zero with every other fold until stage
`2n`; the maximal ideal has Loewy length `⌊log₂N⌋ + 1`; the cotangent space is spanned by the primes
`≤ e^A`; the inverse limit is the Dirichlet ring [L]. Algebraically the tower is completely
controlled.

### 1.2 Weil's window form is the dimension-zero derivative of point counts
The commutators of the window zeta operator with the Tate flow `f ↦ f·n^{−k}` are the Jordan
totients `J_k(m) = φ(m)#ℙ^{k−1}(ℤ/m)` — point counts of punctured affine space over residue rings,
the Tate pieces of the degeneration (AHD). With `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`,

`Q(H) = Ω(0)τ_H(0) − 2τ′_H(0) + J_∞(H) + pole` [L]:

Weil's arithmetic term is the derivative at dimension zero of a family whose values at positive
integers are counts. Equivalently it is a signed count: if `P = Σp_jx^j` interpolates `log` on
`1, …, ⌊e^A⌋`, then `Q = Ω(0)‖H‖² + J_∞ + pole − 2Σ_j p_jτ_H(j)` [L]. Character twists carry the
structure (`L(s,χ)`: Tate pieces `χφ#ℙ^β`, non-Tate piece `χΛ`) [L].

Positivity in positive dimension is soft: `ζ(s)ζ(s−ε)`, with zeros off the line, has nonnegative Tate
pieces in every positive dimension; at a prime, the positivity that survives `∂_k` at `k = 0` is
exactly the sign of the weight [L]. The Taylor coefficients of the family at `k = 0` are Bombieri's
generalized von Mangoldt functions, `J_k = Σ_j (k^j/j!)Λ_j`, `Λ_j = μ * log^j`, `Λ₁ = Λ`,
`Λ₂ = Λ log + Λ*Λ` (Selberg) [D]. The first coefficient is the one sieve theory cannot see (parity);
the higher ones are sieve-accessible. The dimension-zero derivative is the parity barrier on
windows [D, heuristic identification].

### 1.3 A new fold is one collar-to-collar correlation; the obstruction is the bulk
Crossing a stage adds one fold, whose only cost is its end mass on two collars of width
`ε = A − log(N+1)`: `Q = Q_N + w_{N+1}(fold energy − end mass)` [L]; equivalently the new fold enters as
the single collar-to-collar correlation `−2w_{N+1}∫H(u)H(u+log(N+1))du` over the left collar [D].
Every archimedean jump longer than `ε` carries the collars out of the window, so the collar exit charge
`Ω(ε)∫_{collars}H² ≤ J_∞`, and on every stage `Ω(ε) ≥ log 3 > 2/e ≥ Λ(n)/√n`: **the exit charge pays
every new fold pointwise, uniformly along the tower** [L]. Composite stages are free [L]. The payment
is by AM–GM and drops the new fold's own energy; since margins are doubly exponentially small (1.4),
the lossy condition `Q_N − Ω(ε)∫_{collars}H² ≥ 0` (bulk room) is sufficient, not necessary. New folds
are never the obstruction pointwise; the obstruction is the accumulated canonical class in the bulk,
and the stage step has to be exact.

Pointwise, `Q ≥ ∫V_A H² + pole` with the universal end profile
`V_A = Ω_Γ + φ(−u) + φ(A+u)`, `φ(t) = Ω(t) − ψ_{1/2}(e^t)` [L]: the Gamma factor's exit tail minus
the half-weighted Chebyshev count at the distances to the two ends. Windows of length `≤ 1/7` are
positive by the exit charge alone [L]; the pointwise mechanism stops near `0.18`, where `φ` turns
negative like `−2e^{t/2}`. Beyond, interior jumps and antisymmetric fold counts must pay — the fold
capacity inequality, which is RH [L].

Read as a Schrödinger form, `Q − pole` is the energy of a jump process on the window — archimedean
jumps with a logarithmic-Laplacian kernel `ω(x) = e^{x/2}/sinh x` and prime jumps of length `log n` at
rate `Λ(n)/√n` — with potential `V_A` [L]. On the sector odd about the window centre the cosh square
vanishes, and odd positivity at every length is RH [L]; there `Q = M − ½⟨s,H⟩²` with `M` the jump
energy plus `∫V_A H²`. Folding the process onto the half-window makes some conductances negative
(pointwise calibration fails past the plastic root [L]); after Schur elimination of those conductances
(variable hubs [L]), nonnegativity of `M` is the existence of a positive supersolution
(Allegretto–Piepenbrink). So RH is the criticality of the folded arithmetic jump process on every
window, with sinh capacity at most one [D].

### 1.4 Exact balance: Weil positivity has no slack
- The Weil cone is a point: every real weight `λ` with full Weil positivity equals `Λ` on `n ≥ 2`; no
  hypothesis on `λ` [L]. Damped, truncated, smoothed or finitely supported weights all fail on long
  windows.
- Window margins collapse doubly exponentially: `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L]; at half-width
  `½log3` the Galerkin ground energy is `≈ 5.6×10⁻⁸` (even), `1.5×10⁻⁵` (odd) [N]. The near-null tests
  are interpolants vanishing at the zeros below the Landau height [N/D].
- No identity with finitely many squares exists at the first prime: on `log 2 ≤ A < 2log 2`,
  `Q − J_∞ = Ω(0)‖H‖² < 0` on an infinite-dimensional space of fold-free, pole-free tests [L].
- No finite-dimensional window realization; no finite-rank realization of `K_ζ`; under RH the level
  carrying the slopes `1, …, N` has rank `≥ N` [L].

So every estimate that loses a factor fails, every finite identity fails, and every finite carrier
fails. A proof is an exact identity of unbounded rank per window, compatible along the tower — or a
soft structural argument that loses nothing (index, rigidity, compactness).

### 1.5 The degeneration: every fixed conductor is a count
Along the critical curve `c⁸ ≍ K log N` the complete tilted-spline family splits [L]:
- bulk packets: `J(1)#ℙ⁷(ℤ/m)`, zero-blind;
- every Ramanujan window of fixed conductor `m ≥ 2`: `7φ(m)J(m)‖H‖²_{−8}/K`, a count with no Weil term
  (general regular profile: `J_{β+1}(m)βJ‖H‖²/K`); divisor twists give sums of conductor counts;
- untwisted windows: `κQ(H) + 7J(1)‖H‖²_{−8}/K`;
- untwisted and prime-conductor windows are orthogonal at second order.

The only non-count piece of the complete family is Weil's untwisted window form; in WTZ's language
the count pieces are the Tate family at positive dimension and Weil's piece is its derivative at
dimension zero. Below the curve, whole-space positivity is proved for `α < 1/9`, and the plan to
`α < 1/8` has every piece in Lean except the final assembly [L/P].

### 1.6 The reflection exists on both sides; its positivity is RH
- Window side: Serre duality `σ_A` is the Rosati involution of the window algebra; its multiplier
  `e^{−(s−½)A}` is unitary exactly on `Re s = ½`; it is an isometry on every datum [L].
- Mayer side: on the canonical period space `H_LP`, the reflection is the Hilbert adjoint
  `I_s† = I_{1/2−s̄}`; the co-isometry defect of a resonant Lewis period is `≤ 0`, zero iff
  `Re s = ¼`; on resonant cores there is a Krein–Lax–Phillips space with `2κ₋ =` polar defect, and
  Krein positivity ⇔ RH ⇔ renormalized Hodge index [L]. The operator-native `Z_PM` is Hardy's `Z` [L].
- Bridge [S]: the logarithmic period transform `U_LP : H_LP ≃ L²(ℝ)` intertwines `I_s` with the window
  multiplier; the co-isometry defect of the Mayer lift of a window test is its window Frobenius defect,
  bounded above and below by the symmetric and antisymmetric fold energies.
- The transfer structure reflects about `Re w = 1`, the zeta events about `Re w = ½`; the arithmetic
  reflection is not an operator symmetry of the transfer operator [P].

Selection selects only through positivity: local data, densities, contractions, cutoff Grams, Hecke
quasimodes and congruence levels are all blind [L].

### 1.7 Precision is one density statement in eight forms
[S] The critical-line log-mean `o(1)`, the mollified log-mean `o(1)`, the linear-mollifier outer law,
the dyadic off-line horizontal moment `o(T)`, `100%` critical-scale clustering and `o(log U)` Hecke
readings are one statement. Almost-all window certificates are equivalent to log-free unit-window
occupancy, strictly weaker than log-free multiplicity density. Unconditionally, almost all Planck
windows are zero-free beyond `A/log V` and all but `O(V/log log V)` unit windows are certified at the
double-log stage. On the window-energy side, the right-edge flux never cancels against its
functional-equation image; Cauchy caps cancel it down to `σ_m = 1 − 1/(116log(m+5))`, and the inner
caps `[½, σ_m]` are the zero-free-region problem itself; the polynomial stage is RH [S]. The growth
rate of two-bump window negativity equals the maximal zero depth; the full window negativity exponent lies between it and `½` [L].

### 1.8 What the three walls are
| Wall | Window form |
|---|---|
| Σ sign | the exact stage step: the censored jump process (Lévy + prime jumps) pays the end-profile potential `V_A < 0` and the sinh capacity in every stage, without loss (no slack); each new fold is one collar-to-collar correlation |
| Π precision / production | the derivative at dimension zero of the Tate counts (parity on windows); the growth exponent of window negativity (between `Θ − ½` and `½`); a production of the window `h¹` by an exact identity of unbounded rank |
| Γ selection | the reflection is present on both sides; what is missing is its positivity (Rosati / Krein); every selector without positivity is blind; the Weil cone is a point and its nonemptiness is prime-blind |

They are three readings of one statement: **on the odd sector of every window, the folded arithmetic
jump process has a positive ground state and its sinh capacity is at most one.**

### 1.9 Where the edge is
All real C² tests are coercive through total window length `A=181/250`, with margin `1/5000`
(SP `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`) [L]. This includes the entire
prime-free range and the first part of the prime-2 stage. The earlier cosh-capacity base task is
therefore closed. Beyond `181/250`, the open content is joint Gamma, prime and pole payment;
the exact stage identity alone supplies no sign.

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Eighth-root join: band–far specialization, top mass and pairing (T3.2–T3.3), Schur synthesis (T4.2), discharge of the upward-rate parameter; result: tilted-spline whole-space positivity for every `α < 1/8` | HF, SRT, AIP, ACS, SC | plan complete on the cards; far reserve, polynomial complement, three-band reserves, band–far channels, jet–pole cancellation, deep-row residuals in Lean |
| A2 | Explicit horizons and constants (`1/9`, `1/8`, logarithmic profile, Beurling schedule, horizon criterion, window-index convergence) | HF, SRT, AIP, ACS, RW, SC | constants |
| A3 | Closed: all-parity coercivity through total length `181/250`, beyond `log 2 + 1/50` | RW, EWU, CWS, ACS, HF | SP `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`, margin `1/5000` [L] |
| A4 | Certified first-fold and later stages (Lehmann–Goerisch with a Lévy comparison operator): margins `1.5×10⁻⁵` (odd), `5.6×10⁻⁸` (even) at `½log3`; `< 10⁻¹⁴` at `5, 7` | RW, OWU, EWU, CWS | finite computation; not scalable |
| A5 | Phase diagram with the sharp floor; `K*(A)` table; equality case; finite-`N` sign at jump thresholds | HF, SRT, AHD, CWS | explicit forms |
| A6 | Fixed-conductor Tate decomposition: Ramanujan-basis diagonalization (joint conductors), character twists, cross terms for fixed finite conductor sets, bulk second order, uniform bulk ledger to `N^{1/2−ε}` | HF, SRT, AHD | the `m = 2`, prime and Ramanujan proofs are templates |
| A7 | Formalize paper-proven items: odd interior jump identity; Mayer window-fold transfer; Farey–Lewis cusp separation; WD near-line density and log-mean; WD port flux and polynomial stage; resonant height law | OWU, PM, WD | paper proofs complete |
| A8 | Atomic-lattice bound `λ_max ≤ ½log N` via Mertens with explicit error | CWS/WTZ, HF | classical |
| A9 | Quantitative depth law, star horizons, gcd-strata tabulation | HF, ACS | effectivization |
| A10 | Björner wedge decomposition of the squarefree complex | MC, HF | classical topology |
| A11 | Higher critical lengths of the window index as functions of a hypothetical off-line configuration | CWS, SRT | conditional calculus |
| A12 | WD composition: stopping prefix, flow threshold, `ΔO ⇒` density one `⇒` Lindelöf | WD, LA, TG | composition |
| A13 | Künneth primitive `h¹` at small degree; mixed-jet recovery `≥ 3` primes; main-term producer | ACS, WL | calibration, algebra |
| A14 | Census: `S_cos(λ)`, odd stabilizer, `β = 2` | census, ACS | classical pair estimates |
| A15 | Voronoi summation; Zwegers' indefinite theta | ACS, HF | classical |
| A16 | Function-field calibration: complete family, horizon layer and second order over `𝔽_q(T)` and `𝔽_q(C)` | AHD, SC, ACS, HF | the sign is known there |
| A17 | Window index lower bound in the length; location of the jump multiples | AHD, SRT, CWS | conditional zero calculus |
| A18 | General profiles past `θ = 1/1080` and past the super-log-log clocks | HF, SRT, SC | constants, cutoffs |
| A19 | Prime-side identity for the Gaussian-damped coupling | SC, ACS | explicit formula |
| A20 | PM classical: Selberg-zeta normalization, Lax–Phillips, Lewis–Zagier separation, `+1` Mayer eigenspace classification, Garland loop-group identification of the rational Weyl sum | PM, W1C | known theories |
| A21 | Operator-native nonvanishing on `Re w = 1` | PM | spectral-Eisenstein template |
| A22 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A23 | Hausdorff shifts, Jensen horizons, two-grid degrees, Toeplitz minors | PA, LA, HCF | effectivization |
| A24 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A25 | Mixed Schur debit; first-prime / coarse / polar costs | AIP, CHMD | fixed-dimensional estimates |
| A26 | Logarithmic two-point Chowla | MC | Tao's theorem |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ fold capacity ≡ horizon criterion ≡ Beurling schedule ≡ every `2K(log N)^{1/8}` ≡ `ι(A) = 0` ∀A ≡ Mayer Krein positivity) | RH; fixed length sub | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD, TT, MSC, FEL, PM |
| B2 | Exact stage step (each new fold = one collar-to-collar correlation, paid without AM–GM loss); its lossy form, bulk room, is sufficient and fails at the first stage [K] | RH as induction; each step sub | RW, CWS/WTZ, HF |
| B3 | Window capacity: Poincaré inequality for the censored jumps where `V_A < 0`; Agmon ground state of the arithmetic jump process | RH; fixed length sub | CWS/WTZ, RW, CHMD, TT, OWU, HF |
| B4 | Positivity surviving the derivative at dimension zero (parity on windows) | method; uniform RH | CWS/WTZ, ACS, AHD |
| B5 | Growing-conductor Tate decomposition; conductors above `√N` | sub | HF, SRT, AIP, ACS, SC, AHD |
| B6 | One fixed critical multiple on windows of every length | sub | HF, SRT, AHD |
| B7 | Full-space positivity of general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B8 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B9 | Cluster exclusion below the Landau height | sub | RW, SRT |
| B10 | HL on the positive locus (no edge / zero mode) | RH | HF, TG, SC, EHT |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Cross-tower gap through the archimedean channel | method; RH | HF, AIP |
| B13 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B41 | Zero–one law `κ ∈ {0, ∞}` (the finite nonzero stratum is Lindelöf-deep [L]) | sub | SC, HF, ACS, CWS, SRT |
| B14 | Laguerre–Pólya (all ranks / degrees) | RH | TH, LA, HCF, PA, GTA |
| B15 | Scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B17 | Source-faithful realization: a tower of unbounded rank | RH | RN, PTR, W1C, PM |
| B18 | Prime-blind positivity: archimedean + pole part `≥ 0` on positive combinations vanishing on `±log ℕ_{≥2}` | RH | (no route; Section 2.4) |
| B19 | Growth exponent of window negativity (`≥ Θ − ½` on two-bump tests, `≤ ½`) | ≥qRH (`< ½`); RH (`0`) | all window routes, WD |
| B42 | A count for the untwisted window (Weil piece as a Tate piece of a second degeneration) | RH | HF, AHD |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B20 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH | WD, TG |
| B21 | `100%` critical-scale clustering ⇔ critical log-mean `o(1)` ⇔ Hecke `o(log U)` ⇔ horizontal moment `o(T)` | sub | WD, census, MC, HEF |
| B22 | Log-free unit-window occupancy `D_win`; log-free multiplicity density `D_zero` | sub | WD, census |
| B23 | Hecke defect pointwise / dyadic-uniform | ≥qRH / RH | WD |
| B24 | Distributional input beyond counts and moments | method | WD, HEF |
| B25 | Count-valued primitive `h¹` as an inequality (naive height; generic two-prime `ℕ`-count) | RH; fixed length sub | ACS, HF, CWS, IRK |
| B26 | Genus law `≤ (2+η)e^A` | indep. | ACS |
| B27 | Logarithmic Serre duality of the split surface, primitive part | sub | ACS, HF |
| B28 | `ε`-uniform producer; square-root source input; Redheffer determinant | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B29 | Near-band cyclotomic energy | ≥qRH | MC |
| B30 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B31 | First Epstein real zero on the boost line | sub | ACS |
| B32 | Bounded dense two-prime coupling; damped cone coupling from the prime side | RH | SC, ACS |
| B33 | Finite-sieve Hodge positivity → global | RH | SC |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Frobenius at infinity as a positivity (Rosati positivity of the window algebra; naive height; Hecke similitude with positive form) | RH | HF, ACS, CWS/WTZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B37 | Euler-product FE twins; unimodular gauges | sub | HF, ACS, SC |
| B38 | Arithmetic `D_s ≥ 0` on finite-cusp-energy resonances (Mayer Krein positivity) | RH; separated gap ≥qRH | PM, W1C |
| B39 | A statistic of resonant states selecting the decay rate | method | PM |
| B40 | Global arithmetic reflection intertwiner of the Mayer family | sub (identity) | PM |
| B16 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every route's last wall is a face of one statement — criticality
of the arithmetic jump process on every window (B1–B3) — so assembling routes removes route-specific
blockers but never the shared core. One assembly is strictly better than every single route: it
reduces RH to one stage-local statement with every other segment proved or just work.

### F1. The tower assembly (recommended)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ window sign; locality in `n ≤ e^A` | CWS | [L] |
| Arithmetic = truncated Dirichlet ring; stages = small extensions; primes generate | WTZ | [L] |
| Base: all real C² tests coercive through total length `181/250`, margin `1/5000`; through `2a*`, `a*=enlargedWeilFloorAperture>181/500`, margin `1/8000` | SP, AIP | [L]; A3 closed |
| Short windows by exit charge (`≤ 1/7`) | WTZ | [L] |
| Entrance: every new fold paid by the collar exit charge; composite stages free | WTZ | [L] |
| Upper control: sharp floor `(4A+1)e^{A/2}`; negativity confined below an archimedean frequency horizon | WTZ, AHD | [L] |
| Nonlocal payment tools: variable-hub Schur squares and `T₂`-stick elimination; two-sided fold–Frobenius bounds; logarithmic jump gap | ACT-L, RIT [S], LST | [L/S] |
| Frozen odd unit window: `Q₁+20M²≥‖F‖²/125`, `M=∫F(x)x(1−16x²/5)dx` | WTZ | [K]; signed prime-2 coupling open |
| Complete odd unit window: `Q≥‖F‖²/100` on `∫xF=∫x³F=0`; prime and pole paid | LST, WTZ | [K]; two low moments and their cross terms open |
| Core: the exact stage step in every stage | — | B2 (RH) |

What F1 bypasses: growing conductors and the `√N` barrier (HF/SRT/AIP; the window criterion is RH
directly, so the complete family is never needed); the prime-side damping bound (SC); log-free density
(WD); count identities (ACS: refuted at the first prime); the missing operator symmetry (PM: the
window side carries the reflection as the Rosati involution of its algebra). What it does not bypass:
exactness (doubly-exponential margins).

The core in its sharpest form: for every `N` and every `A ∈ [log(N+1), log(N+2))`,
`Q_N(H) ≥ 2w_{N+1}∫H(u)H(u+log(N+1))du` (left collar) on `W_A`, exactly. The lossy version (bulk room,
`Q_N ≥ Ω(ε)∫_{collars}H²`) is false already at the first stage: a real C² test supported in
`[-21/20,0]` has `Q₁(H)<0<Q(H)` [K]
(`WTZ.exists_first_stage_positive_exit_loan_failure`). Prime `2` repairs the negative frozen
direction; the signed fold must be retained. Under RH the exact step says [D]: near-null tests of the frozen form anticipate
every new prime-power fold — their end-to-end correlation at the lag `log(N+1)` is nonpositive up to the
margin. Understanding that anticipation is the core.

### F2. The reflection assembly (PM ⊕ CWS ⊕ WTZ)
PM supplies the reflection as a Hilbert adjoint, a Krein space whose negative index is the polar
defect, Hecke operators that intertwine the inversion and the three-term operator [S], and an explicit
negative-norm vector for each off-line resonance [L]. The window side supplies the reflection as the
Rosati involution of the window algebra and fold energies that bound the Frobenius defect [L/S]. The
bridge `U_LP` [S] transports the weighted period integral pairing to logarithmic `L²` and relates
the co-isometry defect to window fold energies. It does **not** identify the coefficient-defined
PM Krein pairing with the complete Weil window form. Fixed-parameter modular inversion fixes
each period; the Krein reflection exchanges spectral parameters. RH ⇔ PM Krein positivity ⇔
window positivity follows from separate criteria; the integral map alone supplies no form identification.
Available: [the actual completed Lewis period has source Hecke eigenvalue
`1+2·2^(−2s)`](../../drafts/pipeline/3-formalized/f2-global-lewis-hecke-eigenvalue.md) throughout the
open strip and positive line, individually Lean-audited. The [window reflection
centralizer](../../drafts/pipeline/3-formalized/f2-window-reflection-centralizer.md) is scalar:
a non-scalar commuting correspondence must include adjoints or larger stages. The [sharp cusp law](../../drafts/pipeline/3-formalized/f2-sharp-hecke-cusp-admission.md) admits every smooth window test exactly below `log2`; at and above that stage, the first-prime germ controls the Hecke tail [K]. The [audited
Mellin correspondence](../../drafts/pipeline/3-formalized/f2-hecke-window-mellin-correspondence.md)
realizes `T₂−Id` as `√2 H(·+log2)` into stage `A+log2`, scales the complete Weil form by two,
and recovers its full zero sum. Reflection exchanges this branch with `√2 H`; the parameter
reflection includes conjugation and an exponential twist. PM's boundary-subtracted core carries
an [audited nonzero Hecke correction](../../drafts/pipeline/3-formalized/f2-hecke-scattering-boundary-correction.md)
at every upper resonance [K]. [Positive odd window tests rule out a literal linear
form-isometry intertwining Serre duality with PM's Krein reflection](../../drafts/pipeline/5-failed/f2-literal-linear-reflection-isometry.md) [K].
The [audited core-sum bridge](../../drafts/pipeline/3-formalized/f2-weil-form-as-core-packet-limit.md) now identifies complete Weil energy as the limit of twice the real Krein squares of finite sums of actual PM cores, with the exact twisted reflection and source Hecke coefficient transport [K].
Every positive-length window [surjects onto every finite core span](../../drafts/pipeline/3-formalized/f2-finite-core-projection-and-tail-compensation.md) [K]. Such a projection is positive on all tests iff its resonances lie on the critical line. If an off-line pair occurs, short-window coercivity requires a strictly compensating omitted tail; it cannot establish positivity of that projection.
First-step compact admission does not iterate: [every positive window contains one test with compact first Hecke image and noncompact second image at every complex parameter](../../drafts/pipeline/3-formalized/f2-second-hecke-endpoint-admission.md) [K]. Below `log(4/3)`, the exact second-step admission condition is vanishing on a left germ at endpoint `0`. The [stable cusp-carrier theorem](../../drafts/pipeline/3-formalized/f2-hecke-cusp-decay-carrier.md) proves that every finite ordered word in `T₂,T₃` on a window lift retains `O((1+a)^(−2 Re s))` decay and finite upper Haar square and dyadic cusp energies for `Re s>0`, at every aperture [K].
The [second-prime source correspondence](../../drafts/pipeline/3-formalized/f2-second-prime-source-hecke.md) is also audited [K]: seven determinant-three branches give `T₃E_s=(1+3·3^(−2s))E_s`, and `T₃−Id` realizes `√3 H(·+log3)` with complete Weil similitude factor three. Thus both prime grids have actual source realizations.
[Actual PM cores belong to the same stable decay carrier](../../drafts/pipeline/3-formalized/f2-physical-core-cusp-carrier.md) throughout the upper open strip; every finite mixed Hecke word has finite upper Haar square and dyadic cusp energy [K]. The [uniform spectral estimate](../../drafts/pipeline/3-formalized/f2-uniform-physical-core-spectral-bound.md) now bounds every upper-resonant core by `C(1+Im s)^N exp(π Im s/2)a^(−Re s)` [K]. [Gaussian synthesis](../../drafts/pipeline/3-formalized/f2-gaussian-physical-core-synthesis.md) now gives absolute pointwise and upper Haar `L²` convergence of actual core sums; the damped coefficient reflection pairing tends to complete Weil energy [K]. [Zero-specific endpoint control](../../drafts/pipeline/3-formalized/f2-resonant-core-two-endpoint-bound.md) sharpens the physical bound to `K(s)min(a⁻¹,a^(1−2 Re s))` [K]. [Whole-axis synthesis](../../drafts/pipeline/3-formalized/f2-whole-axis-gaussian-mellin-synthesis.md) now gives Haar `L²` convergence on `(0,∞)` and exact Mellin interchange on `0<Re u<1`; individual transforms are holomorphic on `2 Re s−1<Re u<1` [K]. [Upper-coordinate faithfulness](../../drafts/pipeline/3-formalized/f2-faithful-gaussian-core-completion.md) is now audited [K]: local normal continuation and nonzero residues prove uniqueness even from Haar-almost-everywhere vanishing. A [universal arithmetic antiunitary](../../drafts/pipeline/3-formalized/f2-arithmetic-mellin-reflection.md) exchanges the actual Gamma-normalized resonant theta fields in logarithmic Haar `L²`; the exact core Mellin identity retains its Cauchy correction [K]. Its [exact order and operator norm](../../drafts/pipeline/3-formalized/f2-cauchy-reflection-order.md) give a sharp unweighted Haar boundary: bounded iff `Re s≥1/4`, bounded in both directions iff `Re s=1/4` [K]. This does not identify the linear PM Krein form with a positive physical metric. Positivity remains open.
Residual: prove positivity of this signed correspondence from arithmetic or a compatible positive source metric (B34, B38). The integral metric and factor-two similitude alone supply no such sign.

### F3. The density–index assembly (WD ⊕ AHD ⊕ CWS ⊕ AKLT)
WD: almost all unit windows certified at the double-log stage [S]; Planck windows zero-free beyond
`A/log V` outside `O(e^{−rA}/A)` [S]. CWS/AHD: window index finite, monotone, Shannon-bounded,
counting jump multiples [L]. AKLT: an attained positive depth is seen by almost every prime tower [L].
Assembled: off-line zeros, if any, live in a density-zero set of windows, each raising the index.
Residual: excluding density-zero exceptional sets — the zero–one law plus an index ceiling (B41, B13),
≥qRH as a whole.

The complete-family assembly (eighth-root join A1 + Tate decomposition B5 + horizon criterion) is a
Frankenstein of HF/SRT/AIP/AHD whose residual is B1; for RH it is a detour around the window
criterion, valuable as calibration and as the source of the count structure.

## 2.4 A wildly different route

**Verdict: one candidate far from every route — the prime-blind, existence-first route. It escapes Π
and Γ by proved theorems and meets Σ in a form with no primes in it.**

*Facts.* Every real weight with full Weil positivity is `Λ` [L]; the Weil cone is nonempty iff the pole
and archimedean part of Weil's functional is nonnegative on every positive combination of test
autocorrelations whose values vanish at every `±log n`, `n ≥ 2` [L] (M. Riesz extension). Together:
**RH ⇔ prime-blind positivity** [D, two lines].

*The route.* Let `𝒦` be the cone of positive combinations `g = Σc_f(f ⋆ f̃)` with `g(±log n) = 0` for all
`n ≥ 2`. Prove `W_∞(g) := pole(g) + arch(g) ≥ 0` on `𝒦`. No von Mangoldt value enters; the integers enter
only as the zero set `±log ℕ_{≥2}`; ζ enters only through its Gamma factor and pole.

*Finite levels* [D]. Let `C_A` be the set of weights on `{2, …, ⌊e^A⌋}` making Weil's form (ζ's Gamma
factor and pole, weight `λ`) nonnegative on `W_A`. Two-bump tests bound each `λ(n)`, so `C_A` is compact;
restriction maps `C_{A'} → C_A`; the inverse limit of nonempty compacta is nonempty, and the uniqueness
theorem forces its element to be `Λ`. Hence **RH ⇔ `C_A ≠ ∅` for every `A`**: at each level the witness
can be any weight. Equivalently, the archimedean–polar kernel on `(−A, A)` becomes positive definite
after adding point masses at `±log n`, `n ≤ e^A` — a truncated Krein extension problem with prescribed
atom positions.

*Why it is far.* Every route estimates, counts, degenerates, scatters, heats or indexes `Λ`'s own form.
Here `Λ` is never touched; prime sums are never estimated (no Π); selection is a theorem (no Γ). Its
tools appear nowhere in the corpus: Krein's extension problem and de Branges/Krein strings on intervals;
linear-programming duality with auxiliary functions vanishing on a prescribed arithmetic set
(Cohn–Elkies, Viazovska's modular-form constructions); Beurling–Selberg extremal problems;
Landau–Pollak–Slepian concentration; sampling and completeness of `{n^{iτ}}`.

*Walls it meets.*
1. Σ without primes: on `𝒦`, the explicit formula gives `W_∞(g) = Σ_ρ ĝ(γ_ρ)`, so the route is zero-side
   positivity restricted to the prime-annihilated cone — Poisson rigidity (Γ8) in a restricted form.
2. No finite-level slack [D, heuristic count]: the near-null space of a window has dimension of order
   `e^{2A}` (free directions below the Landau height), more than the `≈ e^A` annihilator constraints, so
   the best finite-level certificate has a margin comparable to `Λ`'s own; finite-level constructions
   must be exact.
3. Square-root balance [D]: the pole pairs `g` with `2cosh(x/2)` (growth `e^{x/2}`), the constraint set
   `log ℕ` has density `e^x` at `x`; RH says the constraints win by exactly a square root.

*First test (sub-RH).* Compute `v(A) = max_{λ} min_{H∈W_A} Q_λ(H)/‖H‖²` by semidefinite programming for
`A ≤ log 6`, compare with `Λ`'s ground energy, and locate where the optimal weights differ from `Λ`
(near `n ≈ e^A`). This decides whether finite levels carry exploitable freedom.

*The measure-rigidity direction.* Tested: cutoff Gram data have a positive realization at every rate,
Hecke residual gaps hold at every rate including the critical one, the core source limit retains the
rate, and the Lewis defect is the window Frobenius defect [L/S]. The rate is retained, not selected;
the direction lands on B39 and on the window Frobenius wall.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — `100%` critical-scale clustering
**Question.** Prove that for every `κ > 0`,
`#{ρ : T < γ ≤ 2T, β > ½ + κ/log T} = o(T log T)`.
Equivalently [S]: `∫_T^{2T} log|ζ(½+it)|dt = o(T)`; the mollified log-mean law; the off-line horizontal
moment `Σ(β − ½) = o(T)`; `o(log U)` Hecke readings.
- **Below RH.** A density statement: no zero-free region, no Lindelöf. Selberg's density gives an
  off-line fraction `≤ Ce^{−κ/4}` beyond `κ/log T`, not `o(1)`; moments cannot supply it [L].
- **Advance.** One statement closes the analytic block of WD, the census's near-line mass, MC's
  mollifier law and the Hecke defect simultaneously, and gives the window growth law on almost all
  windows. It requires distributional input (a rate in Selberg's limit law for `log|ζ|`), a tool the
  corpus lacks (B24).

### 2.5.2 Route PM — the arithmetic reflection as an operator identity
**Question.** Construct a meromorphic family of bounded operators `Θ_s` on the Lewis period space,
defined for every `s` in the strip `0 < Re s < ½` (not only at resonances), intertwining the Mayer
transfer / Farey–Lewis structure at `s` with that at `½ − s̄`, up to the explicit factor carrying
`ζ(1+w)/ζ(2−w)` — analytic and nonvanishing on the strip — and agreeing with the reflection `Θ_PM` on
resonant cores.
- **Below RH.** An identity; true or false independently of where the zeros are. The two-centres
  analysis [P] shows the reflection is not a symmetry of `L_w` but that the defect is an explicit,
  harmless arithmetic factor.
- **Advance.** PM's reflection becomes a symmetry of the whole operator family. The Krein form extends
  off the resonance set to a Hermite–Biehler-type structure in `s`, Krein positivity becomes a question
  about one explicit operator family, and through `U_LP` it acts on every window length. It also turns
  the composite of the two reflections (`w ↦ w + 1`) into an exact operator formula.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove log-free unit-window occupancy `D_win`: for every `A > 0`, the number of unit windows
`[t, t+1] ⊂ [V, 2V]` containing a zero of depth `≥ A/log V` is `≤ ε(A)V` with `ε(A) → 0`. Equivalently,
almost all unit windows satisfy the log-stage Bessel–Szegő certificate [S].
- **Below RH.** A density statement; strictly weaker than log-free multiplicity density, independent of
  the log-mean law even under RvM, `> 68%` simple critical zeros and Selberg density [S].
- **Advance.** WD's certificate machinery (prefix scale, canonical multiplier, Bessel cepstrum, port
  decomposition, cap cancellation) is complete; this is its one analytic input at the log stage. The
  unconditional double-log stage (all but `O(V/log log V)` windows) shows the mechanism works one
  logarithm short of it.

### 2.5.4 Route HF — the Tate decomposition with growing conductors
**Question.** Along `c⁸ = K log N`, prove that the complete tilted-spline form on all vectors is
asymptotically the orthogonal sum of Weil's form on untwisted horizon windows and the conductor counts
`7φ(m)J(m)‖·‖²_{−8}/K` on every Ramanujan window, uniformly for conductors `m ≤ M(N)` with `M(N) → ∞`,
with the bulk counts on fixed packets and vanishing mixed terms; then push `M(N)` to `N`.
- **Below RH.** An identity of limits; no sign of Weil's form is used. Fixed conductors are done [L];
  the joint form of different conductors is in progress [S]; large conductors meet the `√N` barrier.
- **Advance.** With the eighth-root join (A1), HF/SRT/AIP/ACS/SC become literally Weil's window
  criterion plus counts on the whole space: one sign problem, all negative directions localized, every
  other direction a point count of projective space over a residue ring.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — window criticality
**Question.** For every window length `A`, construct a positive function `φ_A` on the half-window that
is a supersolution of the folded arithmetic jump Schrödinger operator of the odd sector — archimedean
jumps with kernel `e^{x/2}/sinh x`, prime jumps of length `log n` at rate `Λ(n)/√n`, potential
`V_A = Ω_Γ + φ(−u) + φ(A+u)`, negative folded conductances removed by variable-hub Schur elimination —
with sinh capacity `≤ 1`, compatible with the stage transfer.
- **Why it opens the path.** It is RH [D: odd-sector criterion, fold capacity criterion,
  Allegretto–Piepenbrink]. It converts the sign of a quadratic form (a statement about all tests) into
  the existence of one positive function satisfying a linear pointwise inequality — checkable,
  approximable, organizable stage by stage. The ground-state representation then writes the odd window
  form exactly as a sum of squares of jump differences of `H/φ_A` minus one capacity term: an exact
  identity of unbounded rank (the only kind the no-slack facts allow), the window `h¹` as a weighted
  count of jumps, and the realization every producer needs. Each new fold is one collar-to-collar
  correlation [L/D], so at an entrance a supersolution needs only a correction localized on the two
  collars.

### 2.6.2 Route PM — finite cusp energy forces zero defect
**Question.** Prove that every Lewis period of finite dyadic cusp energy has zero co-isometry defect:
`∫_1^∞ |ψ(2a) − 2^{1−2s}ψ(a)|² da/a < ∞ ⇒ D_s(ψ) = 0`.
- **Why it opens the path.** Finite cusp energy ⇔ resonance [S]; `D_s = 0` ⇔ `Re s = ¼` at a resonance
  [L]; so the implication is RH, and it is an implication between two explicit quadratic functionals of
  one explicit function on `(0, ∞)` — the cusp energy at `a = ∞` and the reflection defect across
  `a = 1`. Every other piece of PM (faithful divisor, Krein space with explicit negative basis, Hecke
  intertwining, window bridge) is in place. Naive three-term + inversion invariance is refuted off the
  line [S]; the missing input is arithmetic, and the Hecke operators that commute with both functionals
  are the natural carriers.

### 2.6.3 Route WD — inner-cap cancellation
**Question.** On every Burnol unit window, at every polynomial stage with prefix `Θ_k(√m)`, cancel the
right-port flux through the inner caps `[½, σ_m]` by a source identity, so that
`e^{−xt}|P₊(t)|²` is integrable at `x = 1/(2n_{m,k})`.
- **Why it opens the path.** Across all degrees this is RH; at each fixed degree it is the
  inverse-polynomial corridor `|β − ½| ≤ C/|γ|^k` [S]. The exterior caps cancel to
  `σ_m = 1 − 1/(116log(m+5))`, the classical zero-free region read as window energy; the
  functional-equation image never cancels the right edge [S]. Everything else in WD is an equivalence;
  this is its single producer.

### 2.6.4 Route HF — a count for the untwisted window
**Question.** Find a second degeneration of the complete family in which the untwisted horizon window is
itself a Tate piece: a one-parameter family of profiles (e.g. the profile dimension `β + 1 ↓ 0`) whose
critical-curve limits are positive combinations of conductor point counts and converge, after the
normalization dictated by `J_k = Σ_j k^jΛ_j/j!`, to `κQ(H)` plus counts, uniformly in `K`.
- **Why it opens the path.** Every other piece of the degeneration is a point count [L]; Weil's piece is
  the derivative at dimension zero of the same counts [L]. A degeneration whose limit carries positivity
  through that derivative is RH and would make the horizon criterion a counting statement. It must be
  selective: Tate positivity in positive dimension holds for fakes [L], so the normalization at
  dimension zero has to use the archimedean data.

## 2.7 Does closing RH need a new field?

**Assessment: yes. Its outline is visible in CWS, WTZ, AHD, ACT and PM: an arithmetic criticality
theory of the window tower — the dimension-zero geometry of `Spec ℤ`.**

*What it is about.* For every length `A`, a module over the truncated Dirichlet ring carrying an
arithmetic jump process and a reflection, organized as a tower of small extensions; its cohomology is
read through families of point counts over residue rings in a continuous dimension `k`, and its
positivity lives at `k = 0`. It is closer to Iwasawa theory (towers, control, characteristic objects)
and to criticality theory of nonlocal operators than to the cohomology of one variety; the
dimension-zero derivative of point counts is the arithmetic counterpart of the `𝔽₁` limit `q → 1`
(Soulé, Connes–Consani) [heuristic].

*What it would be like.* Exact, not estimative: every statement an identity, an integer or a soft
structural law, because Weil positivity has no slack (the Weil cone is a point; margins are doubly
exponential). Infinite-dimensional at every level, local in `n ≤ e^A`, functorial along small
extensions.

*Criteria it must meet.*
1. Locality and control: `W_A` depends on `n ≤ e^A` and the Gamma factor; transitions are small
   extensions; new folds pay their entrance (proved); composite stages are free (proved).
2. Exactness: positivity by identities of unbounded rank (ground-state representations, realizations),
   never by finite squares (refuted) or lossy estimates (no slack).
3. Dimension: values at positive `k` are point counts `φ(m)#ℙ^{k−1}(ℤ/m)`; the theory must say what
   positivity the family carries through `∂_k` at `k = 0`, and why the higher Taylor coefficients
   (Bombieri's `Λ_j`, sieve-accessible) control or fail to control the first (parity).
4. Reflection: Serre duality = Rosati involution of the window algebra; multiplier unitary exactly on
   `Re s = ½`; the theory must supply its positivity (Weil's argument needs Rosati positivity plus a
   similitude).
5. Selection by positivity: fails for flip twins, shifted products `ζ(s)ζ(s−ε)`, Epstein and
   `m² + 64n²` fakes, the golden curve; reproduces curves over `𝔽_q` (genus saturating, Stepanov,
   Castelnuovo–Severi). Selectors without positivity are blind (proved).
6. Prime-blindness: `Λ` must come out of the theory, not go in — the Weil cone is a point, and its
   nonemptiness is a statement about the Gamma factor and the set `log ℕ`.
7. Rank: towers of rank `≈ 2e^A` (window genus); rank `≥ N` for `N` slopes under RH.

*Questions it must answer.*
- Does the window jump process have an Agmon ground state at every length; what is its shape at the
  window ends and in the bulk; how does it pass a stage?
- What positivity of a family of point counts survives the derivative at dimension zero, and which
  normalization at `k = 0` uses the archimedean data?
- Is there a unique-continuation principle for the window Euler–Lagrange equation (logarithmic
  Laplacian plus `Λ`-weighted shifts plus two pole constraints)? Zero modes are exactly the edges, and
  their absence is RH.
- Is there a Hecke operator on windows commuting with `σ_A` and acting as a similitude of `Q`?
- What is the archimedean place in dimension `k` — the Gamma factor's counterpart of the point counts
  `φ(m)#ℙ^{k−1}(ℤ/m)` — and does it dominate them near `k = 0`?
- Is the archimedean place positive on the annihilator of `log ℕ`?
- Over `𝔽_q(C)`, which structure supplies each answer, and which of them has an analogue over `ℤ`?

*Tools it aims to develop.* Dirichlet forms and criticality theory for nonlocal operators
(Allegretto–Piepenbrink, Agmon ground states, Doob transforms, Keller–Pinchover–Pogorzelski); the
logarithmic Laplacian (Chen–Weth) with arithmetic shifts, Hardy and Poincaré inequalities on intervals,
Carleman and unique-continuation estimates; Krein and Pontryagin spaces; Krein strings and de Branges
spaces; LP duality and auxiliary functions on arithmetic sets; sieve theory at dimension zero
(Bombieri's `Λ_j`, parity); point counting over finite rings and Hensel towers; Iwasawa-type control of
small extensions; Lewis–Mayer transfer operators; Hecke correspondences on windows.

*Objects, language, mechanisms.*
- Objects: windows, stages, folds `T_n`, the window algebra and its maximal ideal, collars, exit charge,
  end profile `V_A`, canonical class `k_A`, Tate function `τ_H(k)`, Bombieri tower `Λ_j`, window
  involution `σ_A`, Lewis period space and its Krein form, window index, prime-blind cone `𝒦`.
- Mechanism A (criticality): Agmon ground state of the folded odd-sector process + sinh capacity `≤ 1`
  ⇒ exact sum of squares ⇒ window positivity ⇒ RH.
- Mechanism B (dimension zero): an archimedean Tate family `A_k` dominating the Tate counts,
  `P_k = A_k − 2(τ_H(k) − ‖H‖²) ≥ 0` with `P_0 = 0` and `∂_kP_k|₀ = Q` ⇒ `Q ≥ 0`.
- Mechanism C (reflection): Rosati positivity + Hecke similitude ⇒ RH (Weil's argument).
- Mechanism D (prime-blind): archimedean positivity on `𝒦` ⇒ Weil cone nonempty ⇒ `Λ` by uniqueness ⇒ RH.

No corpus result shows that this field closes RH. Its first tests are 2.8 at the first-fold stage,
2.6.1 at the first-fold stage, and the function-field calibration A16.

## 2.8 The one question

**Is there an archimedean Tate family — a form `A_k` built only from the Gamma factor and the pole, in
every dimension `k ≥ 0`, with `A_0 = 0` and `∂_kA_k|_{k=0} = Ω(0)‖H‖² + J_∞(H) + pole(H)` — that
dominates the arithmetic Tate counts on every window,
`A_k(H) ≥ 2(τ_H(k) − ‖H‖²)` for `0 < k ≤ k₀`?**

Here `τ_H(k) − ‖H‖² = ⟨ρ_A(J_k − δ₁)H, H⟩` is the window's point count in dimension `k`: Jordan's
totients, i.e. `φ(m)#ℙ^{k−1}(ℤ/m)` for `m ≤ e^A`, read against the autocorrelation of `H`. Dividing by
`k` and letting `k ↓ 0` turns the domination into `Q(H) ≥ 0`, because Weil's window form is exactly
`Ω(0)τ_H(0) − 2τ′_H(0) + J_∞ + pole` [L]. Positivity at `k = 0` is then inherited from a comparison in
positive dimension.

- **Why this is the frontier question.** It is the open core of the window tower in its exact form.
  Everything around it is settled: the algebra acting on a window is the truncated Dirichlet ring; the
  arithmetic term is the dimension-zero derivative of point counts; the counts in positive dimension are
  nonnegative and computed by the degeneration as its Tate pieces; finite-square count identities are
  impossible at the first prime; positivity in positive dimension alone selects nothing (`ζ(s)ζ(s−ε)`
  passes, and at a prime only the sign of the weight survives the derivative); Weil positivity has no
  slack. What no programme has is the archimedean side of the comparison in dimension `k`: the Gamma
  factor's counterpart of `#ℙ^{k−1}(ℤ/m)`. That missing object is the window analogue of the
  Lefschetz–Castelnuovo comparison that closes RH over `𝔽_q`, where the archimedean side is replaced by
  the geometry of `C × C`.
- **Why it is less hard than RH.** It is a comparison between two explicit families of forms on window
  tests — arithmetic point counts and an archimedean object to be constructed — in positive dimension,
  with no zero of ζ and no prime-error term in it. It is finite at every stage and fully explicit at the
  first ones: on prime-free windows the counts vanish and the question is `A_k ≥ 0` (the single cosh
  capacity of A3); on the first-fold stage `log 2 ≤ A < log 3` it reads
  `A_k(H) ≥ √2(2^k − 1)·∫H(u)H(u + log 2)du`, one autocorrelation against an archimedean form, a
  two-variable problem in `k` and `H`.
- **Why the answer tells us whether this is the path.** The Tate family, the Tate twist and the Gamma
  factor are defined uniformly in the window length, and the tower adds one fold per stage. An `A_k`
  built from the Gamma factor alone and dominating the counts at the first stages by a rule, not by
  numerics, is a uniform statement along the tower; with it RH is one line (differentiate at `k = 0`),
  and HF, ACS, AHD, CWS and WTZ close together, since the degeneration produces exactly these counts.
  If no archimedean family can dominate the counts already at the first fold — the Taylor coefficients
  of `J_k` at `k = 0` are Bombieri's `Λ_j`, so the domination has to beat the parity barrier at first
  order — then the count/Hodge/degeneration programme cannot close RH, and the remaining paths are the
  criticality of the folded jump process (2.6.1) and the reflection positivity of PM (2.6.2).
