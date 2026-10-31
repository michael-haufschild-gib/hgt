# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems). Labels `A*`, `B*`, `S*` refer to `route-obstacles.md`,
wall labels to `walls-ledger.md`. `[L]` Lean anchor read; `[S]` source-level result in the frontier
map.

## Picture

1. Every route reads one integer: the index `κ` of Weil's correlation on the dilations of `Aff(ℚ)`.
   The archimedean Weil state `φ_c` has index exactly `κ + 1`, so RH is an index-one statement for an
   explicit affine state — equivalently, positivity of the Weil Gram form on the hyperplane
   orthogonal to the pole conductor `v_1`, which is the ground state of the complete Weil matrix.
2. On the complete Weil matrix the sign problem is localized. Conductor averages are positive at
   RH-complete overlap [S]; the low-conductor block is the pole ground state [L]; all vectors are
   positive up to overlap `(log log N)^{<1/16}` [L]. What remains is confinement of negative vectors
   to low conductors beyond that range, a set of `o(N^θ)` exceptional conductors, and the conductors
   above the square-root horizon `N^{½}`, where zero detectors live.
3. Every finite-index waypoint implies Lindelöf and a zero-free half-plane; every exponent gain on a
   count is quasi-RH; the pointwise local count is not even implied by RH.
4. The signature calculus is complete locally and blind globally: twin-invariant, pole-blind after
   archimedean gluing, zero-or-infinity for supported carriers, one square per place for separated
   local poles. The global pole of ζ is not an assembly of local poles at two or more places.
5. Integer producers reach the PNT main term; their precision is the convergence rate of
   `Σ μ(b) log b/b`, so square-root precision is the Möbius problem in dual form.

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| 1 | Lean closure of the `[S]` conductor-average results: level of distribution, conductor-average positivity, Ramanujan Riesz frames (A1) | HF, SRT, AIP, ACS, SC | proofs exist at source level |
| 2 | Exceptional conductors inside the Siegel–Walfisz range: the `o(M)` exceptional set avoids `m ≤ (log N)^A` (A2) | same | individual uniform residual bound is proved there |
| 3 | Growing-packet head-pole cancellation, packets up to `exp(c√log Y)` (A3) | CHMD, HF, AIP | window PNT with classical error |
| 4 | Growing-conductor control of the undilated hyperbolic term; moving-head packet norms, keeping the `−2T` boundary (A4) | HF, SRT, AIP | estimates on explicit finite parts |
| 5 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` (A5) | SRT, HF | synthesis error at one explicit scale |
| 6 | Explicit capture stage for complete-cell indices (A6) | AID, HF, CHMD | effectivise a compactness transfer |
| 7 | Stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` (A7) | WD, LA | known exponent; calibration |
| 8 | Effective rounding of theta-prefix collision readings on a fixed window (A8) | WD, TG, HF | explicit Gaussian tails |
| 9 | Same-order mixed-jet recovery for `≥ 3` primes (A9) | WL, ACS | Dirichlet-jet algebra |
| 10 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer (A10) | WL | quantify the Farkas / rounding construction |
| 11 | `XiZeroCopy`-free PW-B theta instantiation where notational (A11) | PW-B | rewriting |
| 12 | Heat-deformed archimedean state: configuration theorem for the zeros of `H_t`, `t > 0` | SC, WD | instance of a proved theorem |
| 13 | F₃ automorphic chain: global Haar change of variables, spectral-section / local-kernel matching, absolute convergence, Bruhat unfolding, constant-term evaluation | ACS | function-field loop-group mathematics |
| 14 | Certified Weil positivity past the two-prime aperture `r ≥ ½ log 3`, odd and full | RW, EWU, OWU, CHMD | finite aperture; certified numerics |
| 15 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| 16 | Explicit thresholds: Hausdorff shifts (PA), Jensen degree horizons (LA), two-grid fixed degrees (HCF) | PA, LA, HCF | effectivise eventual statements |
| 17 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| 18 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (implies Lindelöf and a zero-free half-plane); **sub**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| Σ-1 | Positivity on an RH-complete schedule / on `v_1^⊥` (B1, SC) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU |
| Σ-2 | Polynomial conductor confinement: logarithmic reserve beyond `(log log N)^{1/16}` (B2) | sub below `¼`; RH at RH-complete overlap | same |
| Σ-3 | Full-complement / mixed Schur payment below the floor (B5) | Σ1 | same |
| Σ-4 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| Σ-5 | All-rank / all-degree theta, heat, Jensen signs | RH | TH, LA, HCF, PA, GTA |
| Σ-6 | Arithmetic index ceiling uniform in resolution (B6) | ≥qRH | CHMD, SRT, WD, AID |
| Σ-7 | Subcritical heat count `a < 1` (B8) | sub | WD |
| Σ-8 | Source-side collision charge `< 2`; every `Λ_X = 0` (B10, B11) | RH | WD, TG |
| Σ-9 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL |
| Σ-10 | Spectral reality of a realized operator | RH | RN, PTR, W1C, PM |
| Σ-11 | One-square coupled assembly of local pole states (B16) | sub | SC, AKG |
| Σ-12 | Joint positivity of non-arithmetic Gamma graph + signed diagonal + prime reserve + poles | unknown | CHMD, AID |

### Π — square-root precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| Π-1 | Unconditional one-sided count at square-root precision (B14) | RH | WL, PBM, RB, JAS, CTF |
| Π-2 | ε-uniform producer (B13): zero-free-region error is **sub**; square-root error is **RH** | sub / RH | WL |
| Π-3 | Moving-scale half-power Möbius cancellation; near-band cyclotomic energy | RH; ≥qRH | MC |
| Π-4 | Characteristic-0 quadratic effectivity (B15) | RH | ACS |
| Π-5 | Exceptional conductors beyond `(log N)^A` (B3) | sub | HF, MC, CAF |
| Π-6 | Square-root conductor barrier: control of conductors `N^{½} < m ≤ N` (B4) | sub | HF, SRT, AIP, SC |
| Π-7 | 100% census; pointwise local count | sub | ACS, SRT, IGP, LA, WD |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| Γ-1 | Zero-independent selection at the trivial gauge point (B17) | RH | MC, BAG, XN, PM, PW-B |
| Γ-2 | Hecke invariance of the collided form | RH | AP, CDG |
| Γ-3 | Pre-divisor sections / potentials coupled to Ξ | RH | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF |
| Γ-4 | A conformal correspondence over ℤ whose factor is not archimedean size, with bounded self-intersection | RH | ACS |
| Γ-5 | Selection input on `v_1^⊥` (the glued state is pole-blind; selection must come from Gamma and prime data) | RH-coupled | SC |

## 2.3 The three questions to answer next

**Q1. Can exponential conductor confinement be replaced by polynomial confinement?**
Negative unit vectors of the complete Weil matrix are captured by conductors `m ≤ exp(O(c¹⁶))`; with
the logarithmic reserve this becomes logarithmic growth only while `c ≤ (log log N)^{<1/16}`, which is
exactly where all-vector positivity is proved [L]. A capture by `m ≤ c^K` at overlap `c` would put
every negative vector inside the conductor range where individual residuals are controlled (`m ≤
(log N)^A`) for `c = (log N)^α` with `α` small — all-vector positivity at a power of `log N`. Under ¬RH
confinement must fail somewhere below `α = ¼`, because zero detectors have long Möbius transforms
(RAPT `TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons`). Determining the largest unconditional
`α` locates the RH content of the HF/SRT/AIP/ACS/SC cluster precisely. Starting points: CACT
`TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap`, `NegativeWeilPacketsHaveExponentialConductorCutoffs`,
RAPT `BoundedPrimeDefectHasAnExponentialConductorCutoff`.

**Q2. Are the exceptional conductors and the super-square-root conductors harmless?**
The level of distribution leaves `o(N^θ)` nonpositive conductors and says nothing about `N^{½} < m ≤ N`.
Two sub-questions decide the remaining layers of Σ1: (a) does every exceptional conductor carry an
exceptional character (a Siegel-type zero) — the complete-Weil face of exceptional moduli — so that
it can be removed by the uniform Dirichlet inputs, or is the exceptional set empty above `(log N)^A`
for structural reasons? (b) do the large completed energies `E_m(c) ≥ log(m/c) ≥ ½ log N − log c` make
the form coercive on the super-square-root conductors without a frame there (an
Elliott–Halberstam-type input would otherwise be needed)? Starting points: CAF
`CompleteWeilConductorAveragePositivity`, `RamanujanConductorFrames`; RAPT
`TheConductorEnergyKeepsALogarithmicReserve`.

**Q3. Is the global pole a product-formula coupling of local poles?**
Local pole–successor states at distinct places keep one square each (`κ = k`), real + p-adic gives 2,
and boosts multiply to `1` only on principal units [L]. A Hermitian state on `Aff(ℚ)` built from the
local states at `∞` and finitely many primes, coupled through the product formula on principal units,
with exactly one negative square, would be the first finite-place model of the one-square global
state that RH requires (`κ(φ_c) = 1`); a proof that no such coupling exists would show the global
pole is irreducibly global and close local–global assembly as a strategy. The question involves no
zeros and is strictly weaker than RH. Starting points: AKG `LocalSignaturesAddOverDistinctPlaces`,
`TheSignatureOfASeparableAssembly`, `TheShellDecompositionOfAPoleSuccessorForm`.

## 2.4 A wildly different route

**The weight route (tensor-power amplification over a family).** Over `𝔽_q`, purity is proved by
(i) a crude bound `|α| ≤ q^{w/2 + 1/2}` with a loss independent of the weight, from a Rankin square
with nonnegative coefficients and Landau's theorem; (ii) tensor powers, of weight `kw`, for which the
same loss gives `|α|^k ≤ q^{kw/2 + 1/2}`, so the loss disappears as `k → ∞`; (iii) a family (a lisse
sheaf on a curve) so that tensor powers are again arithmetic objects with Euler products, with big
monodromy controlling their top cohomology. No critical sign and no square-root estimate is used.

Over ℤ the route reads: construct arithmetic objects `Z_k` whose spectrum contains `ρ₁ + … + ρ_k`, with
an Euler product, and prove a crude bound `Re ≤ k/2 + C` with `C` independent of `k`; then
`k Re ρ ≤ k/2 + C` for all `k` gives `Re ρ ≤ ½`.

How it avoids the walls:
- **Σ**: the only positivity is nonnegativity of Dirichlet coefficients and Landau's theorem (corpus:
  `ZetaMultipleLandauZeroFree`, `FiniteOffLineLandau` [L]); the abstract inertia version exists —
  bounded negative index over all tensor degrees ⇔ positivity (`TensorPolarizationAmplification`
  [L]). The archimedean state `φ_c` always carries its successor square, so the amplification must act
  on `K_ζ` restricted to `v_1^⊥`, not on `φ_c`.
- **Π**: any fixed loss is amplified away; the dead "no extra exponent at fixed total support" does not
  apply because the weight grows with `k`.
- **Γ**: weights select. The Liouville twin `ζ(2s)/ζ(s)` is mixed (zeros from `ζ(2s)`, poles from
  `ζ(s)`); Davenport–Heilbronn combinations have no Euler product to tensor.

Its own wall is **realization**: Euler-product tensor powers of the spectrum of ζ. Over `𝔽_q` they are
the cohomology of `C^k`; over ℤ the analogue is the scaling surface and its powers (ACS) with a
Künneth formula whose H² carries `ρ + ρ'`. The corpus contains neither arithmetic tensor powers of the
Weil form nor a Künneth statement beyond point-count positivity.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — complete Weil positivity at a power of `log N`
**Question.** Prove that the complete Weil matrix is positive on all vectors for `1 ≤ c ≤ (log N)^α`
for some fixed `α > 0`.
- **Below RH / quasi-RH**: RH-completeness starts at `α > ¼`; below it no test family is known to be
  RH-complete, and no implication to a zero-free region is known.
- **Advance**: the first all-vector positivity theorem at a power of `log N` for the full source (all
  primes, poles, Gamma); it needs exactly Q1 (polynomial confinement) plus the individual residual
  bounds already proved for `m ≤ (log N)^A`, and it would quantify how far below `¼` unconditional
  methods reach — the distance between the proved region and RH becomes a single exponent.

### 2.5.2 Route SC — the heat-deformed archimedean state as a Pontryagin homotopy
**Question.** Build the archimedean state `φ_c^{(t)}` from the Gaussian-weighted theta kernel of
`H_t` (source data only) and prove: `κ(φ_c^{(t)})` is finite for every `t > 0`, equals the number of
nonreal right zeros of `H_t` plus one, is lower semicontinuous and nonincreasing in `t`, and changes
only at collisions, by one per collided pair.
- **Below RH**: an identity and a monotonicity statement; it fixes no index value.
- **Advance**: SC becomes a continuous family of finite-index Pontryagin spaces `Π_{κ(t)}` converging to
  `φ_c`, so Krein-space perturbation theory (stability of the index under compact or small
  perturbations) applies, and RH becomes: no index jump on `(0, Λ]`. It joins SC's index-one
  formulation with WD's collision counting in one source-defined object.

### 2.5.3 Route WD — an integer realization of the collision charge
**Question.** Construct from integers alone (theta prefixes, primes, Gamma) a Fredholm operator or a
winding number on each natural-height window whose index equals the horizontal collision charge `O`.
First milestone: an explicit rate for the theta-prefix readings to round to `O` on a fixed window
(A8), then uniformly in height.
- **Below RH / quasi-RH**: an identity between an index and `O`.
- **Advance**: the required precision becomes integrality (error `< 1`) instead of square-root
  precision, and homotopy invariance becomes available along the heat flow; the theta-cusp causal
  Hardy index (one-dimensional defect = winding charge) shows the mechanism exists for a single
  resonance.

### 2.5.4 Route ACS — RH for `y² = x³ − x` over `𝔽₃` through the loop Eisenstein series
**Question.** On the restricted central loop group of the curve, where the arithmetic Eisenstein series
and its constant-term integral are defined, prove absolute convergence, unfold, evaluate the constant
term as a ratio of `ζ_E`-values, and show that convergence and positivity force `|α| = √3` without
Frobenius acting on cohomology.
- **Below RH**: RH for this curve is a theorem; the question asks for a new proof by the automorphic
  ACS mechanism.
- **Advance**: decides whether the automorphic branch produces or only receives; a positive answer
  isolates the step where the quantized conformal factor `q = 3` enters (Γ10) and gives the template
  for the characteristic-0 loop group.

### 2.5.5 Route WL — a producer with zero-free-region precision
**Question.** Do parity-selective integer auxiliaries, with support and coefficients controlled
uniformly as `ε ↓ 0`, give `ψ(x) ≤ x + O(x exp(−c√log x))` by vanishing order alone?
- **Below RH / quasi-RH**: the classical zero-free-region error term; the exponent stays `1`.
- **Advance**: the main-term producer [L] has error `C_ε log²x` only for fixed `ε`, and its Farkas dual
  ties the slope gap to the convergence rate of `Σ μ(b) log b/b`. A uniform producer would show that
  integrality can encode analytic information about ζ near `Re s = 1`; a proof that it cannot would
  bound every integer-auxiliary producer at PNT strength and leave WL a receiver.

### 2.5.6 Route CHMD — the odd-sector ground state at the two-prime aperture
**Question.** Prove nonnegative Doob energy — `⟨Rw, w⟩ ≤ ½‖w‖²` — for every odd compact test supported in
`[−r, r]` with `r = 0.55` (`2r > log 3`, so primes 2 and 3 both enter), using the Doob/nodal
decomposition and the Gamma-graph payment of the prime-two and prime-three blocks.
- **Below RH**: fixed aperture is never RH-complete.
- **Advance**: for every `r > 27/50` one odd test has `W_ζ > mass/25` and `W_Liouville < −3 mass/10`
  [map]; positivity on all odd tests at `r = 0.55` would be the first theorem in which a full test
  space is positive for ζ and selective against the twin, with two interacting prime atoms paid by the
  non-arithmetic Gamma graph — the joint payment CHMD lacks (Σ-12), at its smallest nontrivial scale.

## 2.6 Does closing RH need a new field?

**Assessment: yes.** Each existing language is provably insufficient alone:
- *Estimates* give positivity to `(log log N)^{<1/16}` for all vectors and to `(log N)^{<1/19}` on fixed
  packets; averages reach RH-complete overlap only on conductor averages; the remaining layers are
  confinement, exceptional conductors and super-square-root conductors (Σ1c, Σ1g, Σ1h).
- *Index calculus* is local-complete and global-blind: twin-invariant, pole-blind after archimedean
  gluing, zero-or-infinity for supported carriers, one square per separated place; any finite index is
  already ≥qRH (Σ5, Σ11, Γ3, Γ11).
- *Effectivity geometry* has an exact linear Riemann–Roch for the base and none quadratic for the
  surface (Π-4).
- *Integer producers* reach the main term and inherit Möbius precision in dual form (Π3).
- *Heat and realization* convert the sign into an equally hard reality statement (Σ5, Σ6, Σ8).

The signature theory required by local–global questions exists as adelic Krein geometry; its theorems
pin the gap down: the archimedean place glues by one hyperplane (`v_1^⊥`), distinct places do not glue,
and the global pole is not an assembly of local poles. The missing field is the geometry in which the
places are coupled through the product formula, the horizon counterterm is canonical, and the
archimedean dilation acts like a Frobenius.

**Working name: renormalized intersection theory of the scaling surface.**

*What it is about.* Intersection theory on `Spec ℤ × Spec ℤ` (the scaling surface) where the Frobenius
graph of `C × C` is replaced by the continuous family of scaling correspondences `Γ_u`, `u ∈ ℝ_{>0}`,
whose intersection numbers with the diagonal are the explicit formula, whose self-intersections
diverge and are renormalized by a running counterterm (`log N − γ`), and whose local terms at all places
are coupled through the product formula.

*What it would be like.* Arakelov geometry with a continuous Frobenius: local terms are shell
decompositions (agreement shells at finite places, dyadic Haar cells and tails at the real place),
the archimedean place enters as a hyperplane constraint (the boost hyperplane), global terms are
renormalized pairings, and the central theorem is a renormalized Hodge index theorem on the
pole-orthogonal hyperplane.

*Criteria it must meet.*
1. Calibration: over `𝔽_q` it reproduces Weil's RH with the quantized factor `q`; on the golden datum it
   fails where the Hodge index fails.
2. Positivity by identity on `v_1^⊥`: a sum-of-squares identity uniform in the cutoff, not an estimate.
3. Confinement as a theorem: negative directions of the renormalized pairing are supported on finitely
   many conductors, with polynomial dependence on the resolution.
4. Product-formula gluing: local pole states at all places combine into exactly one global square.
5. Quadratic Riemann–Roch: a sign-free `h⁰` on the scaling surface with Hilbert–Samuel growth.
6. One topology for both readings: archimedean dilation and finite-adelic height decay continuous
   together (removing Γ9).
7. Integrality: indices and intersection numbers are integers, so precision `< 1` suffices (Σ8).
8. Zero-independence and twin sensitivity: built from integers and adeles, reading Gamma and prime data
   (the pole alone is invisible on `v_1^⊥`).

*Questions it must answer.*
- What is the renormalized self-intersection `Γ_u · Γ_u`, and does a Castelnuovo–Severi inequality hold
  for it?
- On `v_1^⊥`, is the renormalized pairing definite (renormalized Hodge index)?
- How do local pole states couple through principal units to give one square (Q3)?
- Why are negative directions confined to low conductors, and with which dependence (Q1)?
- What is `h⁰` on the scaling surface, and its Serre dual?
- Is the collision quantum `O` an intersection number or an index?
- Is there a Künneth formula whose H² carries `ρ + ρ'` with an Euler product (2.4)?

*Tools it aims to develop.* Renormalized Pontryagin spaces with running counterterms and
product-formula gluing; adelic shell decompositions with an archimedean shell calculus; conductor
(Ramanujan) frames beyond the square-root horizon; index theorems for renormalized Toeplitz/Fredholm
forms; theta log-volumes as `h⁰`; loop-group Eisenstein series as global carriers; the heat flow as a
homotopy of Pontryagin spaces.

*Objects, language, mechanisms.* The adele class space and the scaling surface; correspondences `Γ_u`;
pole–successor hyperbolic planes, conformal successors and the boost hyperplane; agreement shells and
Ramanujan conductors; renormalized pairings and counterterms; collided and Weil forms as the positive
and the equivariant reading of one pairing; collision quanta; tensor powers of `H¹(Spec ℤ)`.
