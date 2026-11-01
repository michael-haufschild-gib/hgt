# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `6e0189d741` and the working tree.

Evidence:
- `[L]` Lean statement or module docstring read.
- `[U]` Lean file unfinished or not yet integrated.
- `[M]` frontier-map or killed-routes entry, Lean not re-read.
- `[D]` derived here, not formalized.

## Picture

1. **One even integer, one hyperplane, one Kähler package.** Every route reads `κ = #` distinct
   zeros right of the line. Glued at any place it is `κ + 1` [L]. It is the Hodge defect on
   `v₁^⊥`, and the number of zeros moved by `σ(ρ) = 1 − ρ̄` [L]. HWV makes `(W_{c,N}, v₁)` a formal
   Kähler package [L]:
   - Hodge–Riemann (HR) transports along the overlap flow wherever hard Lefschetz (HL) holds on the
     HR locus; transport costs nothing.
   - Losing HR forces a primitive zero mode.
   - RH ⇔ HL on the positive locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½`. The Liouville property is
     HL [U].
   Every deformation argument therefore has the same content: nondegeneracy.
2. **The overlap axis is the aperture axis.** Each profile `φ` has a critical overlap `c*_φ(N)`.
   There the tail energy, which is both the margin of the complete form and its synthesis error,
   equals the Weil weight `1/log N` [L].
   - For Denjoy–Carleman and sinc profiles `c*_N ≍ L(log L)²`, `L = loglog N`.
   - RH ⇔ positivity at every multiple `K·c*_N`, and the multiple `K` sees every smooth test of
     radius `½ log K + O(1)` [L].
   - The quasi-analytic boundary forbids critical overlaps below `(loglog N)^{1+ε}` [L].
   - Below `c*_φ` the synthesizable radius is negative: the **rough regime** carries no aperture
     [D].
3. **Aperture is a zero-free box.** An isolated off-line pair of depth `δ` at height `ξ` in an RVM
   background is seen at aperture `a` iff `S_δ(a) = sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)` [L].
   - Positivity at aperture `a` excludes exactly the pairs below `2π exp(2π S_δ(a))`, about
     `exp((π/δ)e^{2δa})` for `δa ≫ 1` [D].
   - A Σ-theorem with content about zeros is a zero-free-box theorem. A Σ-theorem without such
     content lives in the rough regime. RH is unbounded aperture.
4. **The rough regime of the tilted spline.**
   - Proved [L]: all vectors for `c ≤ (log N)^{1/16}` (binding: quadratic single-conductor
     residual against floor², `c¹⁶/log N`); complement of polynomial conductors `1/9`;
     confinement `log R' ≤ Cc¹¹`.
   - In progress [U]: packets to `1/8`.
   - Its proved receiver is `α > ¼` by second-order synthesis [L]. Its Fourier decay `ξ⁻⁴` places
     the critical overlap at `(log N)^{1/8}` once fourth-order synthesis is in place [D].
   - These exponents belong to the profile, not to ζ.
5. **Kernel, coupling and window error are one quantity.** RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` [L]; one
   lattice `⟨p⟩ × ⟨q⟩` decides; coupling rate = zero width; the integer cone decides up to
   attainment [L]. `K_ζ(u)` is the normalized smoothed prime error in a fixed-length
   multiplicative window [D].
6. **The complete form on packets is an identity.** It equals `J_N + ½A_N` + bounded diagonal
   − `Σ d_n F²` + boundary terms, exact through `Λ ∗ 1 = log` [M]. The shell degree `d_n` is the
   only overlap-growing non-square term.
7. **Stars and renormalization.**
   - The star of `d` is the complete family at `(c⌊N/d⌋/N, ⌊N/d⌋)`, an isometry for every weight
     [L].
   - Positivity descends from `(c, N)` to every star; negative directions appear first at the top
     of the divisor lattice; deep stars are positive [L].
   - The counterterm pays the boundary flux `log d`. The flux is self-similar exactly for
     generalized von Mangoldt weights, and among twists only for `ζ` [L].
   - Möbius inversion on `gcd` with the star isometry gives the unique exact star decomposition
     `W_{c,N} = −Σ_{d≥2} μ(d)·(star form of d) + W^{cop}` [D]. The coprime coupling `W^{cop}`
     consists of the archimedean Gamma kernel, both poles, the row-one prime terms and the
     successor shells between coprime atoms.
   - Ascent from stars to the top is therefore a Möbius-signed statement about star energies.
8. **The Hecke defect has an exact hierarchy** [L]:
   - Means: dyadic means of the unit-window defect are `O_c(log U)` for `c < 22/51` and
     `O(U^η)` for `c < 2/3`; mean `o(log U)` ⇔ 100% of zeros within `κ/log T` for every `κ > 0`.
   - Almost all unit windows are free of zeros at depth `≥ (6/5)loglog T/log T`.
   - Fixed scale: `O(1)` ⇔ log corridor (≥qRH). All scales: one constant over dyadic scales ⇔ RH,
     also in a zero-coordinate-free finite-theta form.
   - Limits of the linear tools: counts + linear explicit formula cannot bound the defect, and the
     bare prime polynomial grows like `e^L/L²` at anti-nodal ordinates even under RH.
9. **Frobenius at infinity has four RH-equivalent readings** [L]:
   - `σ` trivial on the zeros;
   - every Hecke translation is a similitude of the collided form;
   - one constant for the dyadic Hecke defects;
   - saturation of the partner angle between the resonant Eisenstein states of `ρ` and `1 − ρ̄`
     (`cos² = 4Reρ(1 − Reρ)`).
10. **Selection among prime flips is closed; selection does not produce sign** [L/M]. Every
    nontrivial prime-set flip is separated by an atomic margin, with no density assumption. Flip
    twins of relative density `κ < ½` have harmonic correlation `≍ (log N)^{−2κ}` with positive
    constant. Every selector is a margin, index or counterterm statement on a partial form.
11. **Finite index has a constraint classification** [L]. `κ ≤ r` iff translation-stable positive
    constraints of dimension `≤ r` exist; `κ ≤ r + 1` admits a character hyperplane of index
    `≤ r`, on any abelian group, with no growth assumption.
12. **PM has a constructed determinant** [L]. The regularized Gauss–Mayer operator has a global
    Fredholm determinant `D(w,λ) = A + ζ(w)B` with exact pole structure and `B(w,−1) = 0`.
    Resonance exclusion is RH, and algebraic recentering of the critical parabola is impossible.
13. **Census and growth.** Simple critical zeros `≥ 0.67250071` [L]; a 70%-or-near-line dichotomy
    [M]; `ζ(5/6+it) ≪ t^{2/53} log t` [L]; `μ(½) ≤ 33/200` [U].
14. **Reformulations do not soften; falsification certificates have no converse.** The Künneth
    defect is `2n₊n₋` at every horizon; tensor powers are all-or-nothing [L]. Second Donoghue
    periodic point, repeated Jensen root and nonnegative Ritz velocity refute RH but prove nothing
    [M].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Fourth-order synthesis for the tilted spline: receiver at `K(log N)^{1/8}` for every `K`, and the hyperplane analogue | HF, SRT, AIP, ACS, RW, SC | Euler–Maclaurin synthesis exists for smooth profiles; the spline's third derivative is BV (Stieltjes remainder) |
| A2 | Bilinear conductor-residual theorem: packets and polylog subspaces for `α < 1/8` | HF, SRT, AIP, ACS | file in progress; linear-in-`c` residual identified |
| A3 | Rough regime for a Denjoy–Carleman / sinc profile up to `ε·c*_N` | HF, SRT, AIP, ACS, RW | floor `(log N)^{−O(ε)}` against residuals polynomial in `c ≍ loglog N`; profile constants |
| A4 | Edge of one off-line pair at atomic resolution: `≲ C e^{2a(ρ)} c*_N` in the RVM model | HF, SRT, AIP, RW, EHT, SC | composition of the visibility law with the `K ↔ ½ log K` transfer |
| A5 | Propagate `1/16` into the EHT edge-window and crossing theorems (Lean: `1/59`) | EHT, HF, SRT, SC | composition of proved theorems |
| A6 | Explicit horizon `N₀` for the `1/16` theorem | HF, SRT, AIP, ACS | proved mechanism; constants |
| A7 | Single-`K` completeness of the Steklov/sinc schedule | SRT, HF | synthesis error at one explicit scale |
| A8 | Size of the shell degree `d_n` at overlap `c`; comparison with `½A_N` and the pole term | HF, AIP, SRT, ACS | explicit arithmetic sums |
| A9 | CSAR rigidity vs complete energy on fixed and slowly growing packets | HF, SRT, AIP, ACS | fixed-dimensional comparison through the packet identity |
| A10 | Rate for the smooth no-real-zero tilt profile at power-of-log overlap | HF, SRT, EHT | rerun of the universal argument |
| A11 | Critical-scale identification of smooth-bump packets with ratCorr Grams | SC, HF, ACS | synthesis + Lévy continuity, as in the receivers |
| A12 | Certified Weil positivity past `½ log 3`, and as far as verified zeros + explicit zero-free regions allow | RW, EWU, OWU, CHMD | certified numerics + visibility law |
| A13 | Quantitative star range (explicit `M₀`, `α*`; list of non-universal stars at `(c, N)`) | HF, ACS | effectivize `exists_star_positive_tiltedUnitSpline` |
| A14 | Integrate `μ(½) ≤ 33/200` and transfer it to the heat floor `33/50` | WD, LA | file and card in progress; sharp size-only repair model |
| A15 | Certified de Bruijn–Newman upper bound as an index-one heat time | SC-heat, WD | certified numerics |
| A16 | One Lean statement: `ΔO = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf | WD, SRT | composition |
| A17 | Computable stopping prefix (interval bounds) | WD | interval arithmetic |
| A18 | Same-order mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A19 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer | WL | Farkas / rounding |
| A20 | Cosine prime Gram certificate on the pinching window; stabilizer calibration `β = 2` | census, ACS | file in progress; same-window evaluation |
| A21 | `𝔽_q(X)` calibration: higher-degree local walls, Hecke product formula, archimedean state of a curve | SC, ACS, RIT | curve coupling and curve edge proved |
| A22 | `𝔽₃` loop chain: unfolding, Eisenstein convergence, constant term | ACS | loop-group foundations in Lean |
| A23 | Mayer determinant: general-`λ` finite part; primitive-geodesic coding; Mayer–Selberg identity | PM | known mathematics |
| A24 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| A25 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF | effectivize eventual statements |
| A26 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| A27 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A28 | Toeplitz minors of the Xi centre sequence beyond PF₃₇ | LA, 2.4 | certified computation |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (Lindelöf + zero-free half-plane); **LH** (Lindelöf); **sub**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Positivity at every multiple `K·c*_φ` (all-aperture Weil positivity; no zero mode on `v₁^⊥`) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| B2 | Joint shell–pole payment on all vectors (confinement exponent `≤ 8`) | sub | HF, SRT, AIP, ACS |
| B3 | Low-conductor spans below `(log N)^A` | sub | HF, SRT, AIP, ACS |
| B4 | Conductors `N^{½} < m ≤ N` (Elliott–Halberstam type) | sub | HF, SRT, AIP, SC |
| B5 | Non-arithmetic Gamma graph + signed diagonal + roots + poles on growing packets | sub | CHMD, AID, HF |
| B7 | Exact sum-of-squares identity for the dilation form on one two-prime lattice | RH | SC, HF, RIT |
| B8 | HL on the positive locus (source-defined noncrossing) | RH | HF, TG, SC, WD |
| B9 | Star ascent: the coprime coupling dominates the Möbius-signed star sum on primitive zero modes | RH (all overlaps); sub (rough regime) | HF, ACS, SC |
| B10 | Emptiness of the loop-Eisenstein band poles | RH | HF, ACS, SC |
| B11 | Arithmetic index ceiling uniform in resolution | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | CHMD, SRT, WD, AID, SC |
| B12 | Subcritical heat count `a < 1` | sub | WD, SC-heat |
| B13 | Pointwise heat horizon constant `< ½` | ≥qRH | WD, LA |
| B14 | Collision charge `< 2` per window; no heat-index jump | RH | WD, TG, SC-heat |
| B15 | Cumulative charge `O(T) = o(N(T))` | sub | WD, census |
| B16 | `ΔO = o(log T)` | LH | WD, census |
| B35 | Source-faithful realization (PTR port, W1C Ising limit, RN directed sign) | RH | RN, PTR, W1C |
| B36 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| B37 | All-rank / all-degree theta, heat, Jensen, PF and two-grid signs | RH | TH, LA, HCF, PA, GTA |
| B38 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |

### Π — precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| B6 | Critical-scale residual sign: signed cancellation of the overlap residual at `K·c*_φ` | RH (all `K`) | HF, SRT, AIP, ACS |
| B17 | Gap-independent detection scale for collision readings | sub | WD |
| B18 | Hecke defect at doubly-logarithmic scale `o(log|γ|)` | sub | WD |
| B19 | Dyadic Hecke-defect mean `o(log U)` ⇔ 100% critical-scale clustering | sub | WD, census |
| B20 | Fixed-scale `E_γ(c log T) = O(1)` | ≥qRH | WD |
| B21 | One constant across dyadic scales (uniform finite-theta aperture readings) | RH | WD, HF, SRT |
| B22 | An input beyond counts + linear explicit formula for the conjugate diagonal | method | WD, census, HEF |
| B23 | `ε`-uniform producer | sub / RH | WL |
| B24 | Any unconditional square-root source input (one-sided count, Möbius, primorials, budgets) | RH | WL, MC, PBM, RB, JAS, CTF |
| B25 | Unconditional Serre-dual `h⁰` with quadratic RR | RH | ACS, RIT, HF |
| B26 | Near-band cyclotomic energy `O(N^{3/2+ε})` | ≥qRH | MC |
| B27 | Signed prime surplus `≤ (1/18 + o(1))N` at bandwidth `4/3`, or `E(1/9) ≤ 4` | sub | census, ACS |
| B28 | Bounded coupling on one two-prime lattice (window PNT at `√` precision) | RH | SC, ACS |
| B29 | Cone attainment | sub | SC |
| B34 | Zero-free region near `Re s = 1` from the Mayer operator and Maass–Selberg alone | sub | PM |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B30 | Zero-independent selection at the trivial gauge point | RH | MC, BAG, XN |
| B31 | Frobenius at infinity as an operator (conformal correspondence of factor `≠ 1`; Hecke similitude) | RH | HF, ACS, PL, CDG, EHT |
| B32 | Unimodular gauges with `S_N/H_N → 1`; FE twins without Euler product; zero-density flip twins | sub | HF, ACS, AIP, SRT, SC |
| B33 | Off-line resonance exclusion (zero-selecting scattering rigidity; partner saturation) | RH | PM |
| Γ5 | Pre-divisor sections / potentials coupled to Ξ | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

**Q1. Is the overlap axis the aperture axis for one actual profile?** Prove both halves for one
profile `φ`:
- (a) all-vector positivity of the complete Weil family for `c ≤ ε·c*_φ(N)`;
- (b) RH ⇔ eventual positivity at every `K·c*_φ(N)`, with `K` seeing radius `½ log K`.

What is in hand:
- (b) for Denjoy–Carleman and sinc profiles [L]; the rough regime of the tilted spline to `1/16`
  [L]; the visibility law [L].
- Sinc: (a) is A3.
- Tilted spline: (b) is A1, and (a) is A2 plus the joint shell–pole payment B2.
- The model edge of a single off-line pair is A4.

Why first:
- It decides where the RH content of the twelve complete-family and aperture routes sits.
- If (a) and (b) hold, the rough-regime programme is complete and carries no information about
  zeros. The Σ problem is then Weil's aperture problem, with the dictionary aperture ↔ zero-free
  box, and the edge of every hypothetical zero sits at a constant multiple `e^{2a(ρ)}` of `c*_φ`.
- If (a) fails before `ε·c*_φ` for every `ε`, an estimate-detectable obstruction sits inside the
  rough regime. That would be a new phenomenon to classify.

Character: mostly just work (A1, A3, A4), with one sub-RH open step (B2) for the spline.

**Q2. Does the Möbius renormalization identity propagate positivity?** On `v₁^⊥`,
`W_{c,N} = −Σ_{d≥2} μ(d)·S_d + W^{cop}`, where `S_d` is the star form of `d` at overlap
`c⌊N/d⌋/N`. Does `W^{cop}` dominate the Möbius-signed star sum on primitive zero modes? First ask
this inside the rough regime (sub), then at `K·c*_φ` (RH).

What is in hand: star isometry, positivity descent and deep-star positivity [L]; the self-similar
counterterm [L]; the packet identity and successor/dyadic rigidity [M]; the Gamma reserve [M].
Over `𝔽_q[T]` the Möbius degree sums are `1, −q, 0, 0, …` [M], so the Möbius-signed star sum
collapses degree by degree [D].

Why: the positivity mechanism that crossed edges in other theories is local-to-global: matroids
(Adiprasito–Huh–Katz), Soergel bimodules (Elias–Williamson), buildings (Garland). Here its
obstruction is identified exactly: Möbius signs on stars, plus the coprime link. Over ℤ the
star-level cancellation carries the Mertens function. Ascent is therefore where Σ meets Π. It is
selective, because only `Λ` has a self-similar counterterm.

Character: open (B9). The rough-regime version is a test that can fail or succeed without touching
RH.

**Q3. What arithmetic input controls the conjugate diagonal?** Test case: `o(log U)` for the dyadic
mean of the unit-window Hecke defect at one `c < 22/51`. Equivalently, for every `κ > 0`, all but
`o(V log V)` zeros up to `V` lie within `κ/log V` of the line.

What is in hand:
- three-scale mollification giving `O(log U)`, and the TFAE with critical-scale clustering [L];
- the almost-all `(6/5)loglog T/log T` corridor [L];
- the counts-only no-go [L]; Lorentzian triple and quadruple form factors [M].

Why: this is the Π side's cleanest sub-RH frontier with an exact equivalence. The gap is the
`loglog` factor between the proved corridor and the critical scale. The first input that closes it
identifies what WD needs beyond counts and the linear explicit formula. Averages are blind to
density-zero clusters, so the input must act on the near-line shell itself: a mollifier gain that
tends to zero there, or a quadratic (pair) statement.

## 2.4 A wildly different route

**Assessment.** No route in view avoids all three walls:
- Estimates meet Σ: at fixed aperture they are zero-free boxes.
- Prime statistics meet Π.
- Identity-based producers need source data with a selecting structure, which is a form of Γ.

Routes that avoid Σ and Π, and turn Γ into a concrete algebraic representability problem, exist.
One of them uses a producer type that is absent from the corpus.

**Candidate: real-rootedness by interlacing identities on the Jensen sections of Ξ.**

*Receiver (in the corpus).* RH ⇔ every Xi Jensen polynomial `J^{d,n}` is real-rooted [M]. Every
fixed degree is eventually real-rooted in the shift [M]. The centre sequence is PF₃₇ [L].

*Producer (absent from the corpus; known theorems).*
- After normalization, `J^{d,n}_Ξ` tends to the Hermite polynomial `H_d` as `n → ∞`
  (Griffin–Ono–Rolen–Zagier). `H_d` is the expected characteristic polynomial of a `d × d` GUE
  matrix.
- Mixed characteristic polynomials `E det(X − Σ v_i v_i^*)` of independent rank-one PSD terms are
  real-rooted.
- Finite free additive and multiplicative convolutions preserve real-rootedness, and a positive sum
  of real-rooted polynomials with a common interlacer is real-rooted (Marcus–Spielman–Srivastava).

An exact representation `J^{d,n}_Ξ = E det(X − M_{d,n})` by such a model proves real-rootedness
degree by degree, by an identity.

*Source data.* The Taylor coefficients of Ξ are moments of Riemann's kernel `Φ ≥ 0`, so they are
zero-independent. Writing them through the cosh coefficients gives
`J^{d,0}_Ξ(X) = E_U[p_d(U²X)]`, a mixture over dilations of one real-rooted polynomial `p_d`, the
Jensen polynomial of `cosh √·` [D]. The moment Hankel matrices of `Φ` are PSD. The question is
whether the Toeplitz (Jensen) data are mixed characteristic polynomials of PSD matrices assembled
from Hankel moment data.

*Why it avoids the walls.*
- **Σ**: one identity per degree. Degree plays the role of aperture, and nothing in an identity
  degrades with it. No edge, no floor, no critical overlap.
- **Π**: no prime statistic enters. The data are theta moments, i.e. sums over integers.
- **Γ**: selection becomes a structural property of the source, not a margin. Positivity of `Φ`
  alone cannot select: Epstein zeta functions have positive theta kernels and off-line zeros. The
  candidate selector is the one-variable product structure of `θ₃` (Jacobi triple product), which
  Epstein thetas lack. The Hermite limit says the model must be GUE-like at large shift,
  consistent with Montgomery–Dyson statistics.

*Its own wall.* Mixtures over dilations are not interlacing families in general. The dilates
`p_d(u²X)` have no common interlacer when `u` ranges over `(0, ∞)`. The route needs a conditional
(tree-structured) interlacing family supplied by the source. Equivalently, it needs an
exchangeable, Appell-compatible random matrix family whose expected characteristic polynomials
reproduce the moments of `Φ`. The same mixture problem blocks total positivity by planar networks:
TP is preserved by products and compositions, not by sums. Interlacing families are the tool built
for sums.

*First steps.*
- Decompose `U ~ Φ` into dyadic shells and compute, for `d ≤ 20`, whether the conditional Jensen
  polynomials admit a common interlacer at each level of the shell tree. Record the minimal
  interlacing defect.
- Run the same computation for an Epstein zeta with off-line zeros; it must fail.
- Search for a random Hermitian model built from the triple product of `θ₃` whose expected
  characteristic polynomials match the first Jensen sections (A28 supplies the numerics).

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — the critical-overlap theorem
**Question.** For one admissible profile, prove that its complete Weil family is positive on all
vectors up to `ε·c*_φ(N)` and that positivity at every `K·c*_φ(N)` is RH, with `K` seeing radius
`½ log K + O(1)`.
- **Below RH.** Both halves are consistent with off-line zeros: a pair with visibility aperture
  `a(ρ)` is seen only at `K ≈ e^{2a(ρ)} > 1`. The statement implies no zero-free region.
- **Advance.** It turns the complete-family cluster (HF, SRT, AIP, ACT, ACS-atomic, CHMD) and the
  aperture routes (RW, EWU, OWU) into one problem: Weil positivity at every aperture.
  - It closes the rough regime and certifies that its exponents carry no information about zeros.
  - It places the edge of every hypothetical zero at `≍ e^{2a(ρ)}·c*_φ(N)`.
  - It gives the dictionary aperture ↔ zero-free box as a theorem at atomic resolution.
  - For sinc the receiver half is proved [L] and the positivity half is A3. For the tilted spline
    they are A1 and A2 + B2.

### 2.5.2 Route PM — a spectral zero-free region
**Question.** From the regularized Gauss–Mayer operator and the Maass–Selberg relations alone,
without the Euler product, prove `ζ(σ + it) ≠ 0` for `σ > 1 − η(t)` with an explicit `η(t) > 0`.
Equivalently, prove a resonance-free strip of the modular surface just left of the Maass line
`Re s = ½`.
- **Below RH.** It is a classical-type zero-free region.
- **Advance.** It would be PM's first unconditional output that touches zeros. It would show that
  the continued-fraction dynamics of the modular surface carries the zero-free region of ζ.
  - The classical spectral reason for `ζ(1+it) ≠ 0` is unitarity of the scattering matrix on
    `Re s = ½`; it is not in the corpus.
  - The corpus has the Maass–Selberg truncated norms with exponent `1 − Re ρ`, the partner-angle
    law [L], and the Mayer determinant with its exact `ζ(w)`-pole structure [L].
  - The step that is missing is quantitative: positivity of truncated Eisenstein norms near the
    line, transported through `D(w, ±1)` to an eigenvalue-free region of the regular part `R(w)`.

### 2.5.3 Route WD — critical-scale clustering
**Question.** Prove that the dyadic mean of the unit-window Hecke defect at one `c ∈ (0, 22/51)`
is `o(log U)`. Equivalently, for every `κ > 0` all but `o(V log V)` zeros up to height `V` lie
within `κ/log V` of the line.
- **Below RH.** It implies neither Lindelöf nor a zero-free region, and it is consistent with
  off-line zeros at density zero.
- **Advance.** It removes the `loglog` factor between the proved almost-all corridor
  `(6/5)loglog T/log T` and the critical scale `1/log T` [L]. Classical near-line density
  estimates bound the proportion beyond `κ/log T` by a constant decaying in `κ`, not by `o(1)`.
  It would be the first unconditional statement of the conjugate-diagonal object at the critical
  scale.
- The input needed is a mollifier or pair-correlation gain that tends to zero on the near-line
  shells (scales I and II of the three-scale mollification).

### 2.5.4 Route HF — positivity by renormalization in the rough regime
**Question.** Use the Möbius renormalization identity `W_{c,N} = −Σ_{d≥2} μ(d)·S_d + W^{cop}` and
star descent to prove positivity of one profile's family on `v₁^⊥` up to `ε·c*_φ` by induction on
the overlap. Stars of `d` sit at overlap `≈ c/d`. Use no residual estimate beyond a bounded-overlap
base case.
- **Below RH.** The rough regime is sub (Σ1b, Σ3).
- **Advance.** It would be the first positivity proof by an exact renormalization identity and
  induction. It tests on known ground the mechanism that 2.6.1 and 2.6.4 need: it measures the sign
  of the coprime coupling (archimedean + poles + row-one primes + coprime shells) and the size of
  the Möbius-signed star sum. The estimate-side counterpart is the joint shell–pole payment B2.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a renormalization proof of hard Lefschetz
**Question.** Does the complete Weil family of ζ satisfy the renormalization inequality
`W^{cop}_{c,N}(x) ≥ Σ_{d≥2} μ(d)·W_{c⌊N/d⌋/N, ⌊N/d⌋}(x|_d)` on every primitive zero mode `x`?
- **Why it opens the path.** Descent is proved [L]: positivity flows down the divisor lattice.
  Ascent with this inequality gives HL at every overlap, starting from the rough regime. HL along
  the flow is RH (HWV receiver [U], built from the [L] transport and the RIT hyperplane receiver). The mechanism unifies the three walls:
  - **Σ**: the sign propagates by induction, with no aperture-dependent constant.
  - **Π**: the Möbius-signed star sum is a Möbius-cancellation statement on star energies. Over
    `𝔽_q[T]` it collapses degree by degree because the Möbius degree sums vanish from degree two
    [M/D]; over ℤ it carries the Mertens function.
  - **Γ**: the stars are copies of lower horizons for every weight, but the counterterm is
    self-similar only for `Λ` [L]. A twin's family is not a fixed point of the renormalization, so
    the mechanism is selective. It would be the first selector that also produces sign.

### 2.6.2 Route PM — a Krein structure at the resonance line
**Question.** Is there a Hermitian (Krein) form on eigenfunctions of the regularized Mayer operator
for which the eigenvalue-±1 problem of `R(w)` is J-self-adjoint with definite J on the resonant
sector? The eigenfunctions in question are period-type functions in the sense of Lewis–Zagier,
extended to Eisenstein resonances.
- **Why it opens the path.** RH ⇔ Cauchy–Schwarz saturation between every resonant state and its
  partner under `σ` [L]. Krein definiteness on the resonant sector turns saturation into a
  consequence.
- No algebraic change of spectral variable maps the critical parabola to a real spectrum [L]. The
  structure must therefore come from the operator, nonlocally. It is Frobenius at infinity on the
  Mayer side, and with A23 it would carry the zeros of `ζ(2s)` into a definite spectral problem.

### 2.6.3 Route WD — a non-holomorphic explicit formula
**Question.** Is there an identity that expresses the Hecke translates of the collided form through
prime-pair sums, with an error uniform across all dyadic scales `2^k c₀ log T`? Equivalent targets
are `E_γ(L)` and the finite integer-theta aperture readings.
- **Why it opens the path.** RH ⇔ one constant across dyadic scales [L]; linear tools are proved
  insufficient [L]; a fixed scale gives only the corridor [L]. A quadratic identity with
  scale-uniform error turns the dyadic bound into a prime-pair statement, where form-factor
  theorems exist [M]. It is the analytic form of Frobenius at infinity: the identity of the
  conjugation and reflection pairings, read through primes.

### 2.6.4 Route HF — Hodge–Riemann for the coprime link
**Question.** Is the coprime coupling `W^{cop}_{c,N}` positive semidefinite on `v₁^⊥`, uniformly in
`(c, N)`? It consists of the archimedean Gamma kernel, both poles, the row-one prime terms and the
successor shells between coprime atoms. Positivity on `v₁^⊥` means it is Lorentzian with the pole
class as Kähler class.
- **Why it opens the path.** In the local-to-global scheme of Adiprasito–Huh–Katz and
  Elias–Williamson, HR on links and on stars gives HL. Here:
  - The stars are lower horizons, positive by descent or induction [L].
  - The coprime coupling is the only part of `W` that no proper star carries: it is the link [D].
  - Its entries contain no prime ratio except in row one. Its positivity is therefore an
    archimedean and additive statement (Gamma kernel and successor shells): the `+` side of the
    archimedean channel that glues `+` and `×`.
- A positive answer reduces RH, through 2.6.1, to one Möbius-cancellation inequality among star
  energies.

## 2.7 Does closing RH need a new field?

**Assessment: yes. The corpus lacks one type of positivity producer.** Every producer in the
corpus has one of three types, and each type has a proved limit:
1. *Estimates* stop at the critical overlap. At fixed aperture they are zero-free boxes; the rough
   regime is information-free.
2. *Counts* stop at the main term. The kernel is the window error, and counts plus the linear
   explicit formula cannot bound the Hecke defect.
3. *Selectors* separate ζ from every prime-set flip but are margins or counterterm identities on
   partial forms.

HWV supplies the formal frame: the Kähler package, transport, stars and divisor-identity
selection. It proves that the content is HL on the positive locus. The missing type is positivity
uniform in aperture, produced by an exact local-to-global induction.

**Working name: arithmetic renormalization Hodge theory** (Hodge theory of the self-similar
divisibility–successor complex).

*What it is about.* Quadratic forms on the atoms `log n` of `[1, N]` (orbits of `Aff(ℚ)`),
organized by two structures:
- the multiplicative structure: stars, the divisibility lattice, renormalization maps `n ↦ dn`;
- the additive structure: successor shells `n ↦ n + h` and the archimedean coupling between coprime
  atoms.

The pole class is the Kähler class and `v₁^⊥` the primitive part. The overlap `c` plays the role of
degree, the critical overlap `c*_φ` is the scale at which HL must be decided, and the aperture
`½ log K` is the genus truncation. Over a curve the genus is finite (edge `≤ 2g` [L]); over ℤ it is
infinite.

*What it would be like.* A positivity theory by induction along the renormalization flow
(`d ↦` star of `d`, `c ↦ c/d`).
- It rests on the exact Möbius renormalization identity.
- HR on stars comes by induction, and HR on the coprime link by archimedean and additive positivity.
- HL comes from both, through a Möbius inequality among star energies.
- All constants are independent of the level.
- It would resemble Adiprasito–Huh–Katz and Elias–Williamson (stars and links), Garland (local
  spectral gaps), and the multiscale renormalization group of constructive field theory (block
  spins = stars, positivity preserved by the flow).

*Criteria it must meet.*
1. Aperture uniformity: no constant degrades with aperture, overlap or level. A degrading constant
   reduces the statement to a zero-free box.
2. Exact renormalization: star isometry and the Möbius identity (present).
3. Local HR: on stars (descent and deep-star positivity present) and on the coprime link (missing).
4. Arithmetic HL: the Möbius-signed star sum controlled by the link (missing). This is the
   Lefschetz step and contains Möbius cancellation.
5. Selectivity through `Λ ∗ 1 = log` (present as the self-similar counterterm). Twins must fail to
   be renormalization fixed points.
6. Compatibility with the no-gos:
   - local forms do not sum, and separable assemblies are blind;
   - tensor and Künneth powers are all-or-nothing;
   - paths are free;
   - mixtures do not preserve TP or real-rootedness.
7. Calibration:
   - Over `𝔽_q(X)` it reproduces Weil, with finite genus, conformal Frobenius of factor `q`, and
     Möbius degree sums vanishing from degree two.
   - On the golden datum it fails at the first window.
   - Its finite-aperture truncations reproduce the zero-free boxes of the visibility law.

*Questions it must answer.*
- What is the signature of the coprime link (Gamma kernel + successor shells + row-one primes)?
- Which operator is the Lefschetz operator: the Möbius-signed star sum, the overlap generator
  `∂_c W`, the coupling Laplacian `L_pL_q`, or a Hecke similitude?
- Can the induction run from the rough regime through `c*_φ` with level-independent constants?
- What replaces finite genus over ℤ: a trace-class or Fredholm condition on the link?
- Over `𝔽_q[T]`, does the renormalization identity recover the Hodge index on `C × C`?
- Is Frobenius at infinity the symmetry of the renormalization fixed point?

*Tools it aims to develop.*
- Inductive HL and HR for self-similar complexes.
- Garland's method and trickling-down for weighted divisibility graphs.
- Multiscale renormalization with uniform constants.
- Pontryagin-space invariant subspaces for zero modes (HKT `Index`).
- Möbius inversion on lattices of quadratic forms.
- Lorentzian forms for the archimedean link.
- The synthesis and receiver calculus that moves statements between atomic families and apertures.

*Objects, language, mechanisms.*
- Objects: the divisibility–successor complex, stars as lower horizons, the coprime link, the pole
  class, the primitive part, the critical overlap, the aperture, the Möbius-signed star sum, the
  self-similar counterterm, zero modes.
- Mechanisms:
  - renormalization descent (present);
  - renormalization ascent through link positivity and Möbius control (missing);
  - transport along the overlap flow (present);
  - selection by the renormalization fixed point (present as an identity).

No result in the corpus shows that such a theory exists for ζ. Its first test is 2.5.4: positivity
by renormalization inside the rough regime, where the answer is known to be yes by estimates.
