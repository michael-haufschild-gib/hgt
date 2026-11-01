# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `91e9c8f54f` and the working tree.

Evidence: `[L]` Lean; `[S]` Lean in progress; `[D]` derived here from Lean statements.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = #` distinct zeros right of the
   line, on the pole-orthogonal hyperplane `v₁^⊥` [L]. `κ` is even, RH is `κ < 2`, and finite `κ`
   already gives all high zeros critical and `Θ < 1` [L]. Glued at any place the index is `κ + 1`
   [L]. Kernel, coupling and window prime error are one quantity [L].

2. **The rough regime is closed up to a constant factor.**
   - Tilted spline: all vectors positive to `c ≤ (log N)^{1/9−}`; packets to `(log N)^{1/8−}`;
     receiver at every `K(log N)^{1/8}`. Under ¬RH the first failure sits in
     `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often [L].
   - Zero-free logarithmic profile: positive on `[1, ε·c*]`, and RH ⇔ positive at every `K·c*` [L].
   - At the receiver scale the relative cross-conductor residuals stop decaying; only the exact
     leading term decides [L].
   So Σ for the complete-family routes has one coordinate left: the multiple `K`. A fixed `K` sees
   radius `½ log K − O(1)` and is a finite-aperture statement (sub); all `K` together are RH.

3. **The degree axis has three proved laws** (degree = aperture = `½ log K`).
   - *Ceiling:* `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L].
   - *Near radical:* `(2 − η)e^{2a}` independent tests of degree `a` with
     `|W| ≤ exp(−η²e^{2a}/(300a))‖f‖²`, built to be blind to every zero below the Landau height
     `2πe^{2a}` (Shannon number minus zero count) [L].
   - *Finite divisor:* off the pole and a finite low-frequency grid `D_a`, `W` is coercive with
     constant `(10 + 68e^a)(1 − 1/π)`; the Hodge defect at degree `a` is finite. Mechanism: the
     Gamma symbol grows like `log|τ|`, the Euler product bounds the prime symbol by `68√X` [L].
   - Over `𝔽_q` the opposite holds: the exact radical is infinite beyond the genus aperture, the
     defect is `0` or `∞`, and the golden fake admits no finite divisor [L].

   Reading [D]: at each degree the Hodge index of `ℤ` is a finite-dimensional problem, but it holds
   `≈ 2e^{2a}` near-null directions whose energy is doubly exponentially small and is fixed by zeros
   above `2πe^{2a}`. An estimate that decides the sign must be accurate to `exp(−e^{2a})` — this is
   why estimates stop, why each degree is sub, and why all degrees are RH. `ℤ` has infinite genus
   with a finite near radical at every degree; a curve has finite genus with an infinite radical.

4. **Visibility.** An isolated pair is seen at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`;
   finite-aperture positivity forces an off-line companion next to every deep isolated zero [L].
   Finite apertures exclude isolated zeros; only clusters survive them [D].

5. **Deformation is free and empty.** The Kähler package transports Hodge–Riemann along the overlap
   flow wherever hard Lefschetz holds; Liouville = HL; RH ⇔ HL on the PSD locus. None of the three
   Lefschetz candidates (dilation, overlap flow, coupling Laplacian) is free [L].

6. **Gluing localizes in one stratum.**
   - Stars are lower horizons; positivity descends; deep stars are positive with depth margin
     `log d − C₀` [L].
   - The gcd stratification writes `W` as a sign-free sum of coprime parts of stars. Every successor
     pair and the whole archimedean overlap of consecutive atoms lie in the top stratum `g = 1` [L].
   - Links of the dilation complex are disconnected (towers of distinct primes never meet; over a
     curve they do), so coprime atoms couple only through the archimedean place [L].
   - The nerve of the star cover has Euler characteristic `−M(N)` [L].
   HL is the gluing of the stars across the top stratum.

7. **Riemann–Roch: what a section theory must be.**
   - *Cones fail:* on any polar surface, an ample cone of nonnegative degree satisfies the RR axiom
     iff it contains the open positive cone and the Hodge index holds; on an orbit, RR ⇔ orientation
     [L].
   - *Simple counts fail:* bidegree counts see no primitive class; fixed-rank lattice counts violate
     RI; definite counts have off-line zeros (`ℤ ⊕ 8ℤ`); the Siegel majorant `≥ 0` is the Hodge
     index; the isotropic cone count is `ζ²` with a double pole and no Poisson pair [L].
   - *What survives:* Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ` splits `h¹` into a count part
     and a primitive part `½δ = ½W`; boost averaging restores the Euler product
     (`∫Z⁺e^{2wu}du = Kζ(s+w)ζ(s−w)`); Hecke correspondences are similitudes of the primitive `h¹`;
     over a curve the primitive `h¹` of a graph is the degree of the correspondence (`N₁` for
     `1 − F`) [L].
   The open core is a count-valued primitive `h¹`.

8. **Weil's correspondence algebra exists over `ℤ` without its positivity.** Hecke graphs satisfy
   the Lefschetz, adjunction and `ππ′ = q` relations; Rosati positivity is the orbit Hodge index; the
   Lefschetz trace of a corrector is primitive energy; eventual Hasse–Weil implies Hasse–Weil [L].
   All identities hold on the golden fake.

9. **Precision has three ladders** [L/S].
   - One-point: one-sided count ⇔ RH; producers reach the main term, not the square root.
   - Conjugate diagonal: Hecke-defect means `O_c(log U)` to `c < 1/2` [S] are a near-line density
     ladder (rate `r < 2c*`, up to `2/3`) [S]; `o(log U)` ⇔ critical-scale clustering; fixed scale ⇔
     corridor; dyadic-uniform ⇔ RH.
   - Census: simple critical `≥ 0.6725`; every further gain is a bound on a signed prime-pair
     surplus beyond bandwidth one (`R_cos(2) ≥ 5/6 + 43/3750` once `S_cos = o(N)`).

10. **Quantization.** RH = an even integer `< 2` per window; integer-theta Fredholm indices read it
    exactly and a source-intrinsic stopping rule certifies it, but the first stabilized prefix is
    unbounded in height [L].

11. **Selection.** Every prime-set flip is separated, including zero-density twins below `1/4`;
    self-similar star flux selects `Λ`. Frobenius at infinity has four RH-equivalent readings. Every
    selector is a margin, index or counterterm statement [L].

12. **PM has a determinant and a coding.** `D(w,λ) = A + ζ(w)B` is constructed; for real `w` the
    derivative cone, `B ≠ 0` and `D(w,−1) ≠ 0` hold; even Gauss words code the hyperbolic classes
    of `SL₂(ℤ)`. The trace identity and the scattering link are not formalized [L].

13. **Heat.** Slice floor `133/200` from sub-Weyl profiles; flow floor `2/3 + ε`; heat Hodge defect
    `N(t)/2` [L].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Tilted spline from `α < 1/9` to `α < 1/8` on all vectors (split cross payment `c⁹ → c^{8+o(1)}`) | HF, SRT, AIP, ACS | collective packet coercivity and logarithmic confinement in progress; rough regime |
| A2 | Explicit `ε` of the logarithmic profile; largest multiple `K_est` reachable by absolute estimates | HF, SRT, AIP, ACS, RW | constants |
| A3 | Edge of one off-line pair in the RVM model | HF, SRT, RW, EHT | composition of the visibility law with `K ↔ ½ log K` |
| A4 | Propagate `1/9` into statements carrying `1/59` | EHT, HWV, HF, SC | composition |
| A5 | Explicit horizons `N₀` | HF, SRT, AIP, ACS | constants |
| A6 | Single-`K` completeness of the Steklov/sinc schedule | SRT, HF | one explicit scale |
| A7 | ratCorr Grams at `K·c*` from smooth-bump packets | SC, HF, ACS | synthesis + Lévy continuity |
| A8 | Shell degree `d_n`; CSAR rigidity vs complete energy | HF, AIP, SRT, ACS | explicit sums, packet identity |
| A9 | Certified Hodge index at small degree past `½ log 3` | RW, EWU, OWU, HF | finite divisor ⇒ certified Schur complement; practical only at small degree |
| A10 | Quantitative depth law `d₀(c)`; explicit star horizons | HF, ACS | effectivization |
| A11 | Finite-`N` tabulation of the gcd strata | HF | exact identities, numerics |
| A12 | Half-gate chain to `c < 1/2`, density equivalence to `2/3` | WD | in progress |
| A13 | Flow threshold `Λ_X` from sub-Weyl profiles | LA, WD | existing machinery |
| A14 | Certified de Bruijn–Newman bound as an index-one heat time | SC-heat, WD | certified numerics |
| A15 | `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf in one statement | WD, SRT | composition |
| A16 | Computable stopping prefix | WD | interval arithmetic |
| A17 | Strip-zero count of finite theta prefixes | WD | zero counting for explicit entire functions |
| A18 | Mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A19 | Explicit main-term producer | WL | Farkas / rounding |
| A20 | Census: `S_cos(λ)` for `λ ≤ 1`; odd-stabilizer calibration | census, ACS | classical pair estimates; in progress |
| A21 | Künneth primitive `h¹` on the finite divisor at small degree | ACS, HF | calibration computation |
| A22 | `𝔽_q(X)` calibration | SC, ACS, RIT | curve coupling and edge proved |
| A23 | `𝔽₃` loop chain | ACS | loop-group foundations |
| A24 | Mayer–Selberg identity and scattering link | PM | known mathematics, heavy formalization |
| A25 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A26 | Hausdorff shifts, Jensen horizons, two-grid degrees | PA, LA, HCF | effectivization |
| A27 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A28 | Mixed Schur debit; first-prime/coarse/polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A29 | Toeplitz minors beyond PF₃₇ | LA | certified computation |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH**; **LH**; **sub**; **indep.**; **method**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Positivity at every fixed multiple `K·c*` (all-aperture Weil positivity) | RH; fixed `K` sub | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| B2 | Exact leading term at the critical scale (constant-factor wall) | RH (all `K`) | HF, SRT, AIP, ACS |
| B3 | Critical-scale identification of the fixed-`K` limit form | sub | HF, SRT, AIP, ACS, SC |
| B4 | Joint shell–pole / Gamma-graph payment on growing packets | sub | HF, SRT, AIP, CHMD |
| B5 | Low-conductor spans; conductors above `√N` | sub | HF, SRT, AIP, SC |
| B6 | Exact SOS for the dilation form on one two-prime lattice | RH | HF, SC, ACS, RIT |
| B7 | Cluster exclusion below the Landau height | sub | RW, SRT |
| B8 | HL on the positive locus | RH | HF, TG, SC, WD |
| B9 | Gluing across the coprime stratum (star ascent) | RH | HF, ACS |
| B10 | Cross-tower spectral gap (connected-link substitute) | method; uniform RH | HF, AIP |
| B11 | Loop-Eisenstein band-pole noncancellation | RH | HF, ACS, SC |
| B12 | Arithmetic index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, AID, SC |
| B13–B17 | Heat count `a < 1` (sub); heat horizon `< ½` (≥qRH); charge `< 2` (RH); `O(T) = o(N(T))` (sub); `ΔO = o(log T)` (LH) | — | WD, LA, TG, SC-heat |
| B41 | Source-faithful realization | RH | RN, PTR, W1C |
| B42 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| B43 | All-rank / all-degree signs | RH | TH, LA, HCF, PA, GTA |
| B44 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B18 | Gap-independent detection scale | sub | WD |
| B19 | Hecke defect at doubly-log scale | sub | WD |
| B20 | Near-line density at rate `r ≥ 1` (gate beyond `½`) | sub | WD, census |
| B21 | Dyadic mean `o(log U)` ⇔ critical-scale clustering | sub | WD, census |
| B22 | Fixed-scale `E = O(1)` | ≥qRH | WD |
| B23 | One constant over dyadic scales | RH | WD |
| B24 | Arithmetic input beyond counts + linear explicit formula | method | WD, HEF |
| B25 | Height-uniform quantized reading | indep. | WD, TG, SC |
| B26 | Count-valued primitive `h¹` | RH | ACS, HF, RIT |
| B27 | Genus law: near radical `(2 + o(1))e^{2a}` | sub | ACS, RW, HF |
| B28 | Logarithmic Serre duality for the split surface | sub | ACS, HF |
| B29 | `ε`-uniform producer | sub / RH | WL |
| B30 | Unconditional square-root source input | RH | WL, MC, PBM, RB, JAS, CTF |
| B31 | Near-band cyclotomic energy | ≥qRH | MC |
| B32 | Signed prime-pair surplus beyond bandwidth one | sub | census, ACS |
| B33 | Bounded coupling on one two-prime lattice | RH | SC, ACS |
| B34 | Cone coupling ⇒ RH (pure implication) | sub | SC, ACS |
| B40 | Hermitian structure on the Mayer operator near `Re w = 1` | sub | PM |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B35 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, SRT |
| B36 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B37 | Frobenius at infinity as an operator (Rosati positivity) | RH | HF, ACS, PL, CDG, EHT |
| B38 | Unimodular gauges, FE twins, zero-density/irregular twins | sub | HF, ACS, AIP, SRT, SC |
| B39 | Off-line resonance exclusion | RH | PM |
| B45 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

The corpus has reduced the sign problem of every complete-family route to one axis (the degree
`a = ½ log K`) and the producer problem to one object (a primitive `h¹`). The three questions sit
on that axis: one producer question and two sub-RH questions that fix what the producer must do.

**Q1. Is Weil's primitive form a count?**

For a primitive class `f` of the scaling surface, the Künneth count splits
`h_K(x) + h_K(−x) − χ(x) = h¹_K(x) + ½δ(f, f)`, and on primitive classes `δ(f, f) = Re W(f, f)`
[L]. The question: construct a section theory whose primitive `h¹` of every test class is
`½W(f, f)` and is a dimension or a log-count, nonnegative by construction.

What is in hand [L]:
- the universal floor law and orbit RR ⇔ orientation: the theory must be a count, not a cone;
- bidegree blindness: it must read the test component; rank law: its lattices must grow in rank with
  the class;
- definite counts are fakes and Siegel majorants presuppose the sign: no fixed-boost metric;
- the isotropic count is `ζ²` with a double pole: the duality needs a logarithmic completion, the
  same logarithm as `h⁰(D) − h⁰(D^∨) = log(D²/2)` on the pole plane;
- boost averaging restores the Euler product: the arithmetic part is the boost-equivariant part;
- Weil's correspondence algebra over `ℤ` with Lefschetz traces; for a corrector the Lefschetz trace
  is primitive energy;
- over a curve the primitive `h¹` of a graph is the degree of the correspondence (`N₁` for `1 − F`).

Why first: it is the only producer type that escapes the doubly exponential ceiling (an identity
plus a count), it is Weil's own producer, and every simpler form of it has now been refuted, so the
target is sharp: *a cardinality equal to the Lefschetz trace of `ξ ⋆ ξ′` for correctors `ξ`*.
- First test: degree `≤ 3/10`, where no prime is visible and `W` is the archimedean form minus the
  poles. Is that form the primitive `h¹` of an honest count? Its natural source is the Gaussian of
  `Spec ℤ`, whose `h⁰` has `Λ(s)` as Mellin generating function.
- Second test: past `½ log 2`, where the first Hecke graph `T₂` enters.
- Decisive negative form: classify counts with Poisson-type duality that read the test component;
  if none has `h¹ ≥ 0` on the finite divisor at small degree, the Riemann–Roch branch closes.

**Q2. What is the genus of `ℤ` at degree `a`?**

In hand [L]: near radical of dimension `≥ (2 − η)e^{2a}`, made of tests blind to every zero below
`2πe^{2a}`; finite divisor with a doubly exponential count; floor ceiling `exp(−πe^{2(a−2)})`; over
`𝔽_q` an infinite exact radical beyond the genus aperture and no finite divisor for fakes.

The question: prove the upper Landau–Widom half, `dim ≤ (2 + η)e^{2a}` for the near radical at its
natural threshold, and characterize the near radical as the tests whose transforms are small at the
zeros below the Landau height.

Why:
- It is the `h¹` that Q1 must reproduce: an RR over `ℤ` has a genus function `g(a) ≈ 2e^{2a}`, not
  a genus.
- It cuts the fixed-degree Hodge index from a doubly exponential to an exponential finite problem
  (A9 becomes practical at larger degree).
- It separates the two sources of smallness at degree `a` [D]: the complement of the near radical
  is decided by zeros below `2πe^{2a}`, which finite verification reaches; the near radical is decided
  by zeros above it. RH becomes one sign on the near radical at every degree.
- It is sub-RH and uses only the explicit formula, zero counts and time–frequency concentration.

**Q3. What is the complete Weil family at a fixed multiple of its critical overlap?**

In hand [L]: positivity to `ε·c*` (logarithmic profile) and `(log N)^{1/9}` (spline); receivers at
every `K·c*`; block synthesis `K ↔ e^{2R}`; relative residuals of order one at the receiver scale;
fixed-overlap limit form diagonal in conductors with energies `E_m(c)`; localization of nonpositive
directions in finite conductor sectors.

The question: compute the `N → ∞` limit, suitably normalized, of the family at `c = K·c*_N` for fixed
`K`. Is it Weil's form on radius-`½ log K` tests (the synthesized block) plus a coercive conductor
form? What is the exact leading term?

Why: if yes, every complete-family route (HF, SRT, AIP, ACS-atomic, RW, EWU, OWU, ACT; SC through
ratCorr) becomes the degree axis of Q1–Q2, and positivity at small fixed `K` becomes certifiable. If
no, the extra term is the true arithmetic object at the critical scale and the constant-factor wall
gets an explicit form. Either answer ends the estimate stage of these routes.

## 2.4 A wildly different route

**Verdict: the literal Euler-product proposal fails; a centered-numerator variant remains an
unconstructed approximation route.** It does not yet escape the selection problem.

For a smooth projective curve,
`Z_C(t) = P_C(t)/((1-t)(1-qt))`, with reciprocal roots of `P_C` of modulus `√q`.
Under `u = as+b`, `a > 0`, centering the zeros at `Re s = 1/2` forces `b = (1-a)/2`.
The ordinary Euler product then converges only on

`Re s > σ_E = (1+a)/(2a)`.

Write `h = a log q`. The proposed effective `q → 1` means **`h → 0`**, not merely `a → 0`.
Since `q ≥ 2`, this forces `a → 0` and `σ_E → ∞`. Thus those Euler products cannot converge on
the fixed half-plane `Re s > 1`. More generally, centering weight `w` for a variety of dimension
`d` gives `(σ_E - 1/2)h = (d-w/2)log q` [L: parameter identity]. Pole removal permits analytic
continuation; it does not extend the domain of the original positive Euler product.

**What survives.** Set `z = s-1/2`. Pairing the curve's conjugate Frobenius eigenvalues and
centering its numerator gives, for an explicit positive scalar normalization,

`F_n(z) = A_n ∏_{j=1}^{g_n}(cosh(h_n z) - cos θ_{n,j})`, `A_n > 0`.

Every factor has nonnegative even Taylor coefficients. Hence
`|F_n(z)| ≤ F_n(R)` whenever `|z| ≤ R` [L]. Pointwise convergence for every real `R > 1/2`
therefore already supplies local boundedness on the whole plane [L]. Vitali and Hurwitz then
give RH if the limit is the specified normalization of `ξ(1/2+z)`; their receiver and blow-up
alternative already exist in `RHTower/XiCRealZeroVitaliBlowup.lean` [L].

**Open core:** construct the curves, scales and scalar normalizations from arithmetic, and prove
that real-axis convergence. No such construction is supplied here. Numerator convergence is a
different requirement from convergence of the original Euler products. The existing ART no-gos
exclude exact finite realizations, not this limit.

**Corrections to the original proposal.**
- Deligne gives one line per cohomological weight, not one line for every variety's full zeta
  function. Use curves or a specified pure factor. The desired zeros of `ξ(s)` lie on `Re s=1/2`;
  those of `Ξ(t)=ξ(1/2+it)` are real.
- Vitali requires a common connected open domain containing a uniqueness set and the target
  strip. Bounds only inside `0 < Re s < 1` do not supply the missing boundary neighborhoods.
- Zero counts alone do not bound amplitudes (`exp(nz²)` has no zeros and equals one at zero).
  For the centered products above the real-axis bound supplies the required control directly.
- The fractional-dimension argument is not a no-go for normalized limits: it omits the affine
  shift and uses point-count asymptotics without uniform control as genus grows.
- Pseudofinite-field transfer concerns first-order statements. It supplies neither analytic
  convergence nor identification with `ξ`; “only bounded genus” is not its precise limitation.

The `𝔽₁` analogy itself is established literature: Connes–Consani already recover the completed
zeta through a `q → 1` counting-distribution formalism. This does not construct a sequence of
finite-field varieties to which Deligne and Hurwitz apply. Sources, exact scope and Lean
declarations: [route audit](../../drafts/pipeline/5-failed/finite-field-euler-approximation-route-audit.md).

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — the genus law of `ℤ`
**Question.** Prove that the near radical of Weil's form at degree `a` has dimension
`(2 + o(1))e^{2a}` and consists of tests whose transforms are small at the zeros below `2πe^{2a}`
(Q2, B27).
- **Below RH.** It asserts nothing about the location of any zero.
- **Advance.**
  - It computes the "genus" of `ℤ` that every Riemann–Roch approach must reproduce, and confirms the
    Connes–Consani count from both sides.
  - It splits Weil positivity at degree `a` into a part decided by finitely many low zeros
    (verifiable) and a part decided by zeros above the Landau height (the near radical) [D].
  - It turns the fixed-degree Hodge index into a finite problem of exponential size, so certified
    positivity can move well past the first primes.

### 2.5.2 Route PM — a Hermitian structure on the Mayer operator at the Maass line
**Question.** With the Mayer–Selberg identity (A24) as input, construct a sesquilinear
(Lewis–Zagier / Krein) structure on eigenfunctions of the regularized operator `R(w)` near
`Re w = 1`, scattering sector included, that makes the eigenvalue-`±1` problem self-adjoint there.
Derive `ζ(1 + it) ≠ 0` and a zero-free region near `Re s = 1` (B40).
- **Below RH.** It gives a classical-type zero-free region.
- **Advance.**
  - PM's positivity results hold only for real `w` (derivative cone, `B ≠ 0`, `D(w,−1) ≠ 0`).
    Cone or contraction methods cannot separate the cusp-form events on `Re w = 1` from scattering
    events just left of it; a Hermitian structure can.
  - It would be the first statement about ζ zeros from PM's own operator and the template for 2.6.2.

### 2.5.3 Route WD — critical-scale clustering
**Question.** Prove that 100% of the zeros up to `V` lie within `κ/log V` of the line for every
`κ > 0`; equivalently, dyadic means of the unit-window Hecke defect are `o(log U)` at one
`c < 1/2` (B21). Stepping stone: near-line zero density at exponential rate `r ≥ 1`, which carries the
`O_c(log U)` gate beyond `½` (B20).
- **Below RH.** It implies neither Lindelöf nor a zero-free region; every pointwise step on WD's
  ladder is at least qRH, so this mean statement is the route's sub-qRH breakthrough.
- **Advance.**
  - It closes the gap between the almost-all corridor `(1 + ε)loglog T/log T` and the critical scale.
    Classical density bounds give a proportion decaying in `κ`, not `o(1)` at fixed `κ`.
  - The input must be a mollifier gain that tends to zero on near-line shells: arithmetic acting on
    the conjugate diagonal's mean.

### 2.5.4 Route HF — positivity past the constant-factor wall at one multiple
**Question.** Prove eventual positivity of the complete Weil family (logarithmic profile or tilted
spline) at one explicit multiple `K₀·c*` with `½ log K₀ − O(1) > ½ log 2`, so that the multiple sees
the first prime. This needs the exact leading term of Q3 at one `K₀` (B2 at one `K`, B3).
- **Below RH.** It is a finite-aperture statement.
- **Advance.**
  - Every proved positivity of the family lies below `ε·c*`, where estimates dominate; one multiple
    past `K_est` is the first exact payment at the critical scale.
  - It tells HF whether its exact identities (Mertens polarization, jump and incidence squares,
    conductor/star duality) can decide a sign where residual and margin are of the same order, and
    whether the method is uniform in `K` (that uniformity is RH).

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — Weil's form as a count
**Question.** Construct a section theory of the scaling surface whose primitive `h¹` of every class
is a dimension or log-count equal to `½` of Weil's form on the primitive part: on graph classes of
correctors, a cardinality equal to the Lefschetz trace of `ξ ⋆ ξ′` (Q1, B26).
- **Why it opens the path.** A count-valued primitive `h¹` gives the RR inequality from the RR
  identity; by the universal floor law the RR inequality of an ample nonnegative-degree effectivity is
  the Hodge index; the Hodge index of the scaling surface is RH [L].
- Over `𝔽_q` this is Weil's proof; LST checks it on curve windows (Künneth effectivity ⇔ unitarity;
  primitive `h¹` = degree of the correspondence).
- Over `ℤ` the algebra (Hecke graphs, Rosati, Lefschetz trace of correctors), the base RR and the
  pole-plane RR exist. The finite divisor and the genus law (2.5.1) say where the count has work to
  do: on `≈ 2e^{2a}` directions at each degree.

### 2.6.2 Route PM — a Krein-definite structure on the resonance strip
**Question.** Extend 2.5.2 to the strip `½ < Re w < 1`: make `R(w)` J-self-adjoint with `J`
definite on the resonant sector, so that eigenvalue `±1` occurs only on `Re w = ½` (partner
saturation forced).
- **Why it opens the path.** With A24, ζ zeros in the strip are eigenvalue-`±1` events of `R(w)`;
  partner saturation is RH [L]; definiteness forces it.
- The structure must come from the operator: no algebraic map takes the critical parabola to a real
  spectrum [L], and positive resonant norms do not select zeros.

### 2.6.3 Route WD — quantized reading with an `O(1)` source bound
**Question.** Find a height-uniform integer reading of the window collision charge (B25), then bound
that integer by a source quantity that is `< 2` with `O(1)` precision.
- **Why it opens the path.** RH ⇔ every window index `< 2` [L]. Quantization removes the doubly
  exponential accuracy that blocks estimates. What remains:
  - a separation or boundary-modulus lower bound (independent of RH), whose first piece is the
    strip-zero count of theta prefixes (A17);
  - an `O(1)` bound for an explicit integer built from finitely many theta values.
- No other route reduces RH to an `O(1)`-precision statement about computable integers.

### 2.6.4 Route HF — gluing across the coprime stratum
**Question.** Prove that the top gcd stratum `g = 1` — every successor pair and the archimedean
overlap of consecutive atoms — is paid at every `N` by the root defect and the depth margins
`log d − C₀` of the stars it couples (B9; equivalently HL on the positive locus, B8).
- **Why it opens the path.** The gcd stratification is exact and sign-free in its signs; deep stars
  are positive; positivity descends; the only unpaid coupling sits in the top stratum [L]. Paying it
  at every resolution is RH.
- Its restriction to one two-prime lattice is the exact SOS identity B6, and over a curve it is
  Castelnuovo–Severi on the Frobenius span [L].
- Links are disconnected over `ℤ`, so the payment must use the archimedean channel; a cross-tower
  gap (B10) is the missing tool.

## 2.7 Does closing RH need a new field?

**Assessment: yes — an intersection theory of correspondences on the scaling surface with a genus
function in place of a genus.**

*Why.* Over `𝔽_q` there are three proofs of RH, and each rests on an object that `ℤ` lacks:
- *Weil (Castelnuovo–Severi):* a surface with correspondences whose intersection numbers are counts.
  Over `ℤ` the surface and the correspondence algebra exist, but the primitive `h¹` is not a count
  (Q1).
- *Stepanov–Bombieri:* auxiliary polynomials whose vanishing is counted. Over `ℤ` integer producers
  reach the main term, never the square root (B29).
- *Deligne:* tensor powers of a realization in which the zeros are eigenvalues with Euler-product
  tensor powers. Over `ℤ` every tensor amplification is all-or-nothing, and the Künneth square carries
  `ρ + ρ′` without an Euler product.

The remaining producer types are excluded by proved laws:
- estimates, by the doubly exponential ceiling and the near radical;
- deformation, because it is free and empty;
- selection, because every selector is a margin.

What is left is an exact count, and no current field supplies it.

*What it is about.*
- The scaling surface of `ℤ`: pole plane `aH + bV`, test classes `f`, correspondences (finitely
  supported measures on the scales: graphs of scalings and Hecke operators).
- Their degrees as counts; the Lefschetz trace of correctors as primitive energy.
- A cohomology `h⁰, h¹, h²` whose `h¹` is a dimension, with infinite genus organized by a genus
  function `g(a) ≈ 2e^{2a}` and a finite divisor `D_a` at each degree.
- The archimedean place as the source of the finite divisor (Gamma dominance) and as the only channel
  that couples distinct primes.

*What it would be like.*
- Weil's second proof transplanted: correspondences, Rosati involution, Lefschetz trace; Rosati
  positivity obtained because traces of `ξ ⋆ ξ′` are counts.
- Riemann–Roch with a growing genus: `h⁰ − h¹ + h² = χ` holds at every degree; `h¹` is read on the
  finite divisor, and the near radical is the part of `h¹` that low zeros cannot see.
- The explicit formula as its Lefschetz fixed-point formula; Hasse's bound as square-root precision;
  Frobenius at infinity as the Rosati identification of the reflection and conjugation pairings.
- Quantization as its index theory: the Hodge defect is the even integer read by collision charges.

*Criteria it must meet.*
1. `h⁰` defined from arithmetic counts; `h¹ ≥ 0` because it is a dimension or a log-count.
2. An RR identity at every degree, proved by a Poisson-type duality on lattices whose rank grows with
   the class; the indefinite (split) duality completed logarithmically.
3. Primitive `h¹` of a test class = `½W(f, f)`; for graph classes of correctors a cardinality equal
   to the Lefschetz trace.
4. Calibrations: over curves it returns `deg(m − nF)`, `N₁`, and Künneth effectivity ⇔ unitarity;
   the genus function is `g(a) ≈ 2e^{2a}`; the obstructed directions at degree `a` lie on `D_a`.
5. It avoids the proved no-gos: cones (universal floor law), bidegree counts, fixed rank, definite
   counts, Siegel majorants at a fixed boost, ordinary Poisson pairs for the isotropic count, finite
   readings, positive majorants.
6. Selection: it fails for the golden fake (no finite divisor), prime flips and Epstein lattices, and
   reproduces Weil over `𝔽_q`.
7. Consistency with quantization: the defect it forces to zero is the even integer read by collision
   charges.

*Questions it must answer.*
- What lattice carries the sections of a test class of degree `a`? Its rank should grow like the
  Shannon number `≈ e^{2a}`; integer Dirichlet polynomials of length `e^{2a}` (the Riemann–Roch of
  the multiplicative group) are the first candidate.
- What metric? The Gamma factor should be its Gaussian.
- What is the degree of a Hecke correspondence over `ℤ` as a cardinality, and what set does
  `L(x, ξ ⋆ ξ′)` count?
- What is the logarithmic completion of the isotropic count, and does it commute with boost
  averaging (which restores the Euler product)?
- Why `ζ` and not an Epstein function: the boost-equivariant part of the split count is `ζ ⊗ ζ`.
- What replaces finite genus: is `g(a)` the dimension of the near radical?

*Tools it aims to develop.*
- Indefinite theta series with completions (Zwegers–Vignéras), Siegel–Weil for the split plane.
- Arakelov `h⁰` (van der Geer–Schoof) on products and on lattices of growing rank.
- Time–frequency concentration (Slepian, Landau–Widom) for the genus function.
- The correspondence calculus of AOG (Lefschetz trace of correctors, Rosati).
- Integer-theta Fredholm indices as consistency checks.
- Function-field calibration through curve windows and Stepanov counts.

*Objects, language, mechanisms.*
- Objects: scaling surface; classes `aH + bV + f`; correspondences `ξ`; Rosati involution;
  Lefschetz trace; correctors; section lattices `Λ_a`; `h⁰, h¹, h²`; genus function `g(a)`; finite
  divisor `D_a`; near radical; Hodge defect.
- Mechanism: count ⇒ `h¹ ≥ 0` ⇒ RR inequality ⇒ Hodge index (universal floor law) ⇒
  Castelnuovo–Severi ⇒ bounded coupling on one two-prime lattice ⇒ RH.

No corpus result shows that such a theory exists for `ζ`. Its first tests are Q1 at small degree,
where existence is not obstructed by zeros, and the genus law (2.5.1), which fixes what its `h¹`
must be.
