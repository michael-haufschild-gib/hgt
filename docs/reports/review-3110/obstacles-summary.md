# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`, wall labels to `walls-ledger.md`. `[L]` Lean statement read; `[S]` Lean source
unfinished or outside its umbrella; `[map]` frontier-map status.

## Picture

1. **One integer on one hyperplane.** Every route reads `κ = κ(K_ζ) = #` zeros right of the line.
   Glued at `∞` or at any prime, Weil's correlation has index `κ + 1`; the translation reading always
   has exactly one square, so the zeros live entirely in the multiplicative reading [L]. The boost
   hyperplane, the Markov hyperplane, the harmonic hyperplane and `v₁^⊥` (orthogonal to the
   complete-Weil ground state) coincide [L]. RH is the renormalized Hodge index: positivity of the
   pairing of scaling correspondences on that hyperplane.
2. **Reformulations do not soften.** Castelnuovo–Severi at rational scales, a uniform bound on `K_ζ`,
   positivity of any Hadamard power `K_ζ^n`, positivity of the Künneth square, glued test index one:
   each is RH [L]. The Künneth square is all-or-nothing — RH or infinitely many negative squares —
   so a finite index for `K_ζ⊠K_ζ` is already RH, while a finite index for `K_ζ` is Lindelöf-deep [L].
3. **Local–global is settled.** Every place glues Weil's data at full index; the archimedean form on
   the hyperplane is Weil's dilation form plus exact shell squares; finitely many prime towers have
   a signature formula; the global pole is the extremal weight of the product of local poles, the
   only archimedean-continuous weight; no sum, product or renormalized infinite product of local
   poles at two or more primes has one square [L]. The one square is supplied by the archimedean place, whose exponents
   are dense as soon as two primes are present — the feature that separates ℤ from `𝔽_q[T]` [L].
4. **Estimates reach a universal regime and stop at a detection edge.** The tilted-spline complete
   Weil matrix is positive on all vectors for `c ≤ (log N)^{α}`, `α < α*` (ineffective, `≤ 1/500`)
   [L]. Positivity is RH at `2(log N)^{α>¼}` for the same profile, at every power of `log N` on
   `v₁^⊥` for C^∞ profiles, and at `≍ L(log L)²`, `L = log log N`, for the sinc profile [L]. A regime
   where positivity is proved without zero information cannot exclude an off-line zero beyond what is
   excluded unconditionally, so RH is positivity across the edge between the two regimes. The ground energy is the profile's Fourier
   tail `τ(c)`; at the sinc threshold `τ(c) log N ≈ 1`. The binding losses of the current method are
   the norm residual against the floor (`19 = 5 + 2·7` for fixed packets) and exponential
   confinement (defect `≤ C c¹⁶`, conductors `≤ exp(C c¹⁶)`).
5. **Integer readings are exact; detection is gap-dependent.** From finite integer theta prefixes
   the horizontal collision charge is the winding number of a Zhukovsky loop and the Fredholm index
   of a Wiener–Hopf operator, on every window, with explicit constants; RH ⇔ the rounded readings
   vanish for every height and every stage `n ≥ 6`; index `0` on `T ≤ 3` [L]. A collision is read only
   from a stage inversely proportional to its gap; the first stabilized prefix is unbounded in height
   [L].
6. **Heat is a homotopy of the glued state.** `κ(φ_c^{(t)}) = N(t)/2 + 1`, source-defined, antitone,
   dropping by one per collided pair, equal to `1` for `t ≥ 1/8`; it is the Hodge defect of `K_t` plus
   one and the number of future collisions plus one [L]. SC's heat branch and WD compute the same
   integer function of `t`; RH is the absence of jumps, i.e. `Λ = 0` (`0 ≤ Λ < 1/8` [L]).
7. **Selection is partial and sharp.** The index is twin-blind and the glue pole-blind, but the glued
   test index is `∞` for every finite prime flip and `κ + 1` for ζ, and the atomic Hodge index
   separates ζ from exactly the sign gauges of submaximal margin [L]. Unselected: infinite twins of
   maximal margin (flipped primes `≥ 11`, `S_N/H_N → 1`). Source-uniform extinction (PW-B) is refuted.
8. **Counts are where they were.** Integer producers reach the PNT main term with precision tied to
   the convergence rate of `Σ μ(b) log b/b`; Möbius cancellation is open at half power; the census
   has `≥ 0.6725` simple critical zeros; deep zeros are `o(V)` [L].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Effectivise `C_cut` (explicit `α*`); optimise the power-log proof's internal exponents (low band `(log N)^{1/12}`, cutoff `c⁴⁶`, cubic `η` dependence) up to the method ceilings `1/19` and `1/16` | HF, SRT, AIP, ACS, SC | proved mechanism; constants and bookkeeping |
| A2 | Growing-packet head-pole cancellation, packets up to `exp(c√log Y)` | CHMD, HF, AIP | window PNT with classical error |
| A3 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` | SRT, HF | synthesis error at one explicit scale |
| A4 | Explicit capture stage for complete-cell indices | AID, HF, CHMD | effectivise a compactness transfer |
| A5 | Stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` | WD, LA | known exponents; calibration |
| A6 | Source-intrinsic stopping rule: soundness and eventual completeness of the perforated and loop certificates; integrate the seam-smooth prefixes [S] | WD | Rouché stability and Gaussian tail bounds; proof plan in source |
| A7 | Certified de Bruijn–Newman bound below `1/8` as an index-one time of the heat state | SC-heat, WD | known method (barrier + certified numerics) |
| A8 | Same-order mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A9 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer | WL | quantify the Farkas / rounding construction |
| A10 | Relative splitting for general nonzero proper rational subgroup successors | SC, AKG | the integer-Haar case is the template |
| A11 | `𝔽_q(X)` calibration: local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve; function-field extremal-weight gluing | SC, ACS, RIT | local wall at `∞` and quantized exponents are proved |
| A12 | Margins of infinite flip sets with harmonic correlation decaying slower than `(log N)^{−½}` | RIT, Γ | margin calculus of SMAP / ACP |
| A13 | `𝔽₃` loop chain: measure-compatible Bruhat unfolding and constant-term evaluation | ACS | function-field loop-group mathematics; Haar, kernels, sections and Weyl convergence are in Lean |
| A14 | Certified Weil positivity past the two-prime aperture `r ≥ ½ log 3`, odd and full | RW, EWU, OWU, CHMD | finite aperture; certified numerics |
| A15 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| A16 | Explicit thresholds: Hausdorff shifts (PA), Jensen degree horizons (LA), two-grid fixed degrees (HCF) | PA, LA, HCF | effectivise eventual statements |
| A17 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| A18 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (implies Lindelöf and a zero-free half-plane); **sub**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| Σ-1 | Positivity on `v₁^⊥` across the detection edge (B1) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| Σ-2 | Signed (quadratic-form) estimate on the subthreshold conductor block beating the residual-versus-floor exponent (B2) | sub | same |
| Σ-3 | Defect bound below `c¹⁶` for nonpositive vectors (confinement below `√N` at larger overlap) (B3) | sub; RH at RH-complete overlap | same |
| Σ-4 | Exact detection threshold of the tilted spline in `[α*, ¼]` (B6) | sub | same |
| Σ-5 | Exact sum-of-squares identity for Weil's dilation form on the boost hyperplane (B19) | RH | SC, HF, RIT |
| Σ-6 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| Σ-7 | All-rank / all-degree theta, heat and Jensen signs | RH | TH, LA, HCF, PA, GTA |
| Σ-8 | Arithmetic index ceiling uniform in resolution (B7) | ≥qRH for `K_ζ`; RH for `K_ζ⊠K_ζ` | CHMD, SRT, WD, AID, SC |
| Σ-9 | Subcritical heat count `a < 1` (B10) | sub | WD, SC-heat |
| Σ-10 | Collision charge `< 2` on every window; no heat-index jump; every `Λ_X = 0` (B12, B14) | RH | WD, TG, SC-heat |
| Σ-11 | Uniform-in-height bound on the collision charge (B13) | sub | WD, census |
| Σ-12 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL |
| Σ-13 | Spectral reality of a realized operator | RH | RN, PTR, W1C, PM |
| Σ-14 | Joint payment of non-arithmetic Gamma graph + signed diagonal + prime reserve + roots + poles | unknown | CHMD, AID, HF |
| Σ-15 | Prime-local decomposition of `κ(K_ζ)` (B20) | sub | SC, AKG |
| Σ-16 | `κ₊(K_ζ)` on the infinite stratum (B9); converse Krein–Langer beyond zero configurations (B8) | sub | RIT, HKT |

### Π — square-root precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| Π-1 | Unconditional one-sided count at square-root precision (B17) | RH | WL, PBM, RB, JAS, CTF |
| Π-2 | ε-uniform producer (B16): zero-free-region error **sub**, square-root error **RH** | sub / RH | WL |
| Π-3 | Moving-scale half-power Möbius cancellation; near-band cyclotomic energy | RH; ≥qRH | MC |
| Π-4 | Characteristic-0 quadratic effectivity (B18) | RH | ACS |
| Π-5 | Exceptional conductors beyond `(log N)^A` (B4) | sub | HF, MC, CAF |
| Π-6 | Conductors `N^{½} < m ≤ N` (B5) | sub | HF, SRT, AIP, SC |
| Π-7 | 100% census; pointwise local count | sub | ACS, SRT, IGP, LA, WD |
| Π-8 | Gap-independent detection scale for collision readings (B15) | sub | WD |
| Π-9 | Pointwise heat horizon constant `< ½` (B11) | ≥qRH | WD, LA |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| Γ-1 | Zero-independent selection at the trivial gauge point (B21) | RH | MC, BAG, XN, PM |
| Γ-2 | Hecke invariance of the collided form; an arithmetic conjugation on the divisor (B23) | RH | HF, AP, CDG, WD |
| Γ-3 | Pre-divisor sections / potentials coupled to Ξ | RH | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF |
| Γ-4 | A conformal correspondence over ℤ with factor `≠ 1` and bounded self-intersection | RH | ACS |
| Γ-5 | Selection of maximal-margin infinite flip twins (B22) | sub | HF, ACS, AIP, SRT, SC |
| Γ-6 | Half-parameter cusp selection (`Λ(s) = 0` ⇒ critical) | RH | PM |

## 2.3 The three questions to answer next

**Q1. Where is the detection edge of the complete Weil matrix, and can unconditional positivity reach
it?** The tilted spline is positive on all vectors to `(log N)^{α*}` and RH-complete above
`(log N)^{¼}`; C^∞ profiles are RH-complete on `v₁^⊥` at every power of `log N` [L]. The edge
`α_det` of the tilted spline lies in `[α*, ¼]`. Two method ceilings sit below it: the norm residual
against the floor (`Q⁵ c¹⁴ · rate ≤ 1/36`, fixed packets `1/19`) and exponential confinement
(defect `≤ C c¹⁶`, below `√N` only for `α < 1/16`) [L]. The question has three parts: (a) a signed
estimate on the subthreshold block `m ≲ c`, where the floor is `≍ (m/c)⁷` and only `≍ c` conductors
are involved; (b) a defect bound for nonpositive vectors with exponent below `16`; (c) a lower bound
for `α_det` by a model computation (a zeta-like zero configuration with one off-line pair, and the
least overlap at which the tilted-spline family produces a negative vector). It gives the most
progress because it is the only cluster in which unconditional positivity grows with resolution; it
measures the distance to RH as one exponent; and a result `α_det = α*` (or close to it) would show
that estimate methods are exhausted at the edge and redirect the programme to identities (Q2).
Starting points: CACT `TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap`,
`CompleteConductorResidualsAreUniformOnLogarithmicFamilies`, CAF `ConductorBandTopTailBounds`, RIT
`TheHodgeIndexAtGrowingOverlap`, SSHA `TheOverlapLawAtEveryRoot`, TM
`TheSincProfileHasAnExactCriticalOverlap`.

**Q2. Is there an exact sum-of-squares identity for Weil's dilation form on the boost hyperplane?**
Every structural piece around it is already an identity: the local pole–successor forms are a
renormalized hyperbolic pair plus shell squares; on `ℓ = 0` the archimedean Weil state is Weil's
dilation form plus the exact squares of the half-line shells of the shifts; the matched prime form
has exactly one positive direction on every full finite sieve; the collided form is a sum of squares
[L]. What is missing is the dilation side: an indexing of `K_ζ` on `ℓ = 0` by arithmetic agreement
data (conductors, successor shells, prime towers) with a remainder that vanishes on the hyperplane.
An identity is the only kind of statement that is not subject to the detection-edge obstruction,
because it does not pay errors against the ground energy. A test is available: at every fixed overlap
the form on `v₁^⊥` is positive with gap `E₁ + g/2` [L]; a candidate identity must reproduce that gap
at fixed `c` before it is tried at growing `c`. Starting points: AKG
`TheArchimedeanWeilFormIsAShellIdentity`, `TheShellDecompositionOfAPoleSuccessorForm`, SSH
`TheNonRatioFormIsAFiniteSumOfShells`, RAPT `Signature/TheMatchedPrimeFormHasOnePositiveDirection`,
RIT `TheHodgeIndexHoldsAtEveryFixedOverlap`.

**Q3. Can the horizontal collision charge be bounded uniformly in height from integer theta data?**
The charge is an exactly computable integer on every window (Fredholm index of a source-defined
Wiener–Hopf operator), `0` on `T ≤ 3`, and changes along the shell-pencil homotopy only through a
window-boundary crossing or an ordered root difference entering the Zhukovsky ellipse [L]. A bound
`O(T) ≤ C` for all `T` (any constant) bounds the off-line zeros per window, which with RVM gives a
critical-zero fraction `→ 1` [L], bounds the heat index jumps per window, and reduces RH to lowering
an integer constant to below `2`. It is the first height-uniform statement the integer machinery
could produce, and it ties WD, SC-heat and the census together. Starting points: CDG
`IntegerThetaCollisionFredholmIndex`, `EffectiveThetaCollisionRounding`, `ThetaPrefixIndexTransition`,
`ThetaPrefixCuspAndSectoriality`; SRT `TheLocalCountHoldsForAlmostAllHeights`; RIT
`TheHeatFlowIsAHomotopyOfHodgeDefects`.

## 2.4 A wildly different route

**The rigidity route: RH from higher-rank rigidity of the joint action of two primes.**

All routes in the map are either quantitative (a sign estimate on a growing family, a count at
square-root precision) or index computations on the affine group of ℚ. In every one of them the
multiplicative action is effectively rank one: on the adele class space principal ideles act
trivially, and on `S`-units the product formula identifies the archimedean boost with the extremal
weight of the local poles [L]. The rigidity route uses the action where it has higher rank and asks
for a qualitative conclusion.

Setting. On an `S`-arithmetic solenoid `X_S = (ℝ × ∏_{p∈S} ℚ_p)/ℤ[1/S]`, `|S| ≥ 2`, the primes of `S`
act by commuting automorphisms; their exponent group `Σ n_p log p` is dense in ℝ exactly when
`|S| ≥ 2` and a lattice for one prime or over `𝔽_q[T]` [L]. Higher-rank actions of this kind are rigid:
positive-entropy invariant measures of `×p, ×q` are Haar (Rudolph, Johnson), higher-rank diagonal
actions have measure rigidity (Einsiedler–Katok–Lindenstrauss), and smooth cocycles over higher-rank
Anosov actions are cohomologous to constants (Katok–Spatzier). Rank-one hyperbolic actions instead
carry resonances: eigendistributions with non-unitary eigenvalues.

Route. (i) Attach to an off-line zero `ρ` a positive object on `X_S` — an invariant measure of positive
entropy, or a joint eigendistribution of the prime action with eigenvalues `|p|_p^{±(Re ρ − ½)}` that
are not unitary. (ii) Apply higher-rank rigidity: such objects are Haar or vanish. (iii) Conclude that
no off-line zero exists.

Precedent. Arithmetic quantum unique ergodicity was proved by measure rigidity (Lindenstrauss, with
the Bourgain–Lindenstrauss entropy bound) where the L-function route needs a subconvexity bound that
is not available: a qualitative "exactly Haar" statement obtained without the analytic estimate that
would give it with a rate. RH is likewise a qualitative statement.

How it avoids the walls.
- **Σ**: no sign estimate on a growing test family; positivity is that of measures, which is free.
  The detection-edge obstruction does not apply because nothing is estimated against a ground energy.
- **Π**: the conclusion is qualitative; no error term at square-root or any other precision appears.
- **Γ**: the higher-rank structure is specific to ℤ: dense exponents for two primes, a lattice over
  `𝔽_q[T]`, where the action is rank one in the relevant sense and RH holds for a different reason.
  Unitary twists change eigenvalues by unitary characters and do not create non-unitary ones.

Its own wall: **the zero-to-measure construction.** No object is known that carries a single zero of ζ
as a joint eigendistribution (or entropy-carrying measure) of the prime action before the quotient by
principal units; after the quotient the action collapses to the archimedean scaling, where resonances
exist and rigidity is unavailable. Corpus contact points: the Mautner phenomenon for `Aff(ℚ)` (APD) and
infinite index for Haar carriers with continuous dilation (AKG) show rigidity acting as an obstruction
to carriers; RH ⇔ the trivial gauge point is typical (AGT) is an almost-everywhere statement of the kind
rigidity upgrades to every point, but only for continuous observables, which the Möbius exponent is
not. First question: does the joint `ℤ^S` action on `X_S`, `|S| ≥ 2`, admit nonzero eigendistributions
of finite order with non-unitary eigenvalues for every `p ∈ S` simultaneously, on Sobolev spaces
adapted to the archimedean flow? If not, what single-zero object maps into that space?

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — all-vector positivity beyond both method ceilings
**Question.** Prove that the tilted-spline complete Weil matrix is positive definite on all vectors,
eventually in `N`, for `1 ≤ c ≤ (log N)^{1/12}`.
- **Below RH / quasi-RH**: RH-completeness of this profile is proved only above `(log N)^{¼}`; no
  implication from positivity at `(log N)^{1/12}` to a zero-free region is known.
- **Advance**: `1/12` lies above the fixed-packet residual ceiling `1/19` and the confinement ceiling
  `1/16`, so a proof needs exactly the two missing tools — a signed estimate on the subthreshold
  conductor block and a defect bound below `c¹⁶` — and shows both ceilings are methodological. It
  brackets the detection edge in `[1/12, ¼]` and supplies the edge-scale tool (a quadratic-form
  rather than norm control at floor scale) that every route of class C1 needs.

### 2.5.2 Route SC — a signature formula for Weil's correlation
**Question.** Express `κ(K_ζ)` through local data: is there a sequence of finite prime-tower
assemblies `K_S = Σ_{p∈S} k_p^{(S)}(v_p(·))`, built from the `S`-truncated complete explicit formula
(primes in `S`, Gamma, pole, running counterterm), such that
`κ(archGlue(K_S, c)) = Σ_{p∈S} κ₀(k_p^{(S)}) + 1 + ε_S`, `ε_S ∈ {0, 1}`, converges to `κ(K_ζ) + 1`?
- **Below RH**: an identity; it fixes no index value.
- **Advance**: a Hasse principle for the off-line zeros: RH becomes vanishing of local polar
  defects plus the archimedean square, each local defect being a finite-tower computation for which
  AKG has the complete calculus (tower signature formula, gluing at every place, readings add). The
  Hecke states already obey an exact Hasse principle for the index [L], which is the template. A
  negative answer — the Weil kernel's index is not a limit of tower signatures — would locate the
  zeros in the non-separable coupling between towers and identify that coupling as SC's object.

### 2.5.3 Route WD — a height-uniform collision-charge bound
**Question.** Prove from integer theta data that the horizontal collision charge is bounded uniformly
in height: `sup_T O(T) < ∞`.
- **Below RH / quasi-RH**: it bounds off-line zeros per window, not their existence; no zero-free
  region and no Lindelöf statement follow.
- **Advance**: with RVM it gives a critical-zero fraction `→ 1` [L] (beyond the `0.6725` simple-critical
  census), bounds heat-index jumps per window, and turns RH into improving one integer constant to
  below `2`. It would be the first height-uniform output of the Fredholm machinery, whose present
  limits are gap-dependent detection stages and height-dependent stabilization [L].

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a renormalized Hodge index theorem by identity
**Question.** At every resolution `(φ, c, N)`, is the complete Weil form on `v₁^⊥` an exact sum of
squares of arithmetic functionals (indexed by conductors, successor shells and prime towers) plus a
remainder that vanishes identically on `v₁^⊥` — a Castelnuovo–Severi identity for scaling
correspondences?
- **Why it opens the path**: an identity at RH-complete resolution is RH. It is the only mechanism
  not excluded by the detection-edge logic, it is compatible with the local–global structure (every
  local form and the successor side are already identities), and over `𝔽_q` it is the Hodge index of
  the Frobenius graph. It would also explain the universal regime: there the identity's squares would
  dominate trivially, at the edge they would carry the whole form.

### 2.6.2 Route SC — an index theorem for the glued Weil state
**Question.** Is `κ(φ_c) − 1` the Fredholm index of an operator `D_ζ` built from integers and adeles
(a Toeplitz operator on the boost hyperplane, or a global version of the theta-prefix window
operators), connected through Fredholm operators to an operator of index `0`, along a path whose
symbol stays invertible for a structural reason (as sectoriality gives index `0` on `T ≤ 3`)?
- **Why it opens the path**: integrality and homotopy invariance replace both sign and precision: an
  index needs precision `< 1` and is constant along Fredholm paths. The heat homotopy shows that a
  source-defined Pontryagin homotopy from `φ_c` to an index-one state exists, but its index jumps at
  collisions iff RH fails [L]; the question is whether another homotopy has no crossing by
  construction. It also answers AKG's open question of a purely additive counter of the zeros.

### 2.6.3 Route WD — Frobenius at infinity
**Question.** Is there an arithmetic correspondence acting on the zero divisor as complex conjugation,
identifying the collided pairing `(ρ, ρ̄)` with the reflection pairing `(ρ, 1 − ρ)` — equivalently, a
prime-side upper bound for the Hecke defect `D(T_L f) + D(T_{−L} f) − 2D(f)` at translation scale
`L ≍ log T` below the collision quantum?
- **Why it opens the path**: the collided side is computed exactly from theta data, every depth
  moment, local count and collision charge included [L]; positivity of `D` is free and its translation
  invariance is RH [L]. A conjugation correspondence would make the collided form a Weil form, force
  the Hecke defect and the collision charge to vanish, and give WD the canonical object that Frobenius
  gives over `𝔽_q`. Its quantitative face, a defect bound at logarithmic scale, is a zero-density
  statement read through `D` and is the natural first target.

## 2.7 Does closing RH need a new field?

**Assessment: yes, and it is not one of the existing structural fields.** Renormalized intersection
theory (RIT) together with adelic Krein geometry (AKG) is the intersection-theoretic field the
Frobenius-graph analogy calls for, and it exists as Lean theory. It answers its own questions: how local poles glue (only the extremal
weight, supplied by the archimedean place), what Castelnuovo–Severi says (RH at rational scales), what
a Künneth square adds (nothing; all-or-nothing), what separates ℤ from `𝔽_q[T]` (density of exponents),
whether the heat flow is a homotopy (yes, paying one unit of Hodge defect per collision), and whether
the pairing selects ζ (against finite flips and submaximal margins). Its success criterion — a sign
statement on the pole-orthogonal hyperplane beyond fixed overlap without an estimate its own no-gos
exclude — is met only in the universal regime, by estimates. The remaining obstruction is logical,
not technical: an estimate proved without zero information is valid in a regime that cannot see
zeros, so no refinement of estimates crosses the detection edge. Signature calculus cannot cross it
either, because every index reformulation reproduces RH exactly (Künneth, Hadamard, glued index,
heat). What is needed is a theory whose statements hold at the edge by structure.

**Working name: edge Hodge theory of the scaling surface.**

*What it is about.* The family of finite-resolution intersection forms `W_{φ,c,N}` of scaling
correspondences (atoms of profile `φ` at overlap `c` on the horizon `{1, …, N}`), viewed as a
degenerating family as the resolution grows: its universal regime, its RH regime, the edge between
them, and the structure that persists across the edge. Its central object is the edge itself — the
resolution at which the family first sees the zeros, `τ(c) log N ≈ 1` for the sinc profile — and the
pole-orthogonal hyperplane on which the Hodge index must hold.

*What it would be like.* Hodge theory of degenerations rather than of a single variety. In the
degeneration of polarized Hodge structures, positivity survives in the limit by structure: the
nilpotent-orbit and `SL₂`-orbit theorems polarize the limiting mixed structure by representation
theory, with no estimates. The scaling surface already carries the ingredients: the boost and the
conformal successor form one hyperbolic plane on which the affine group acts through `SL(2, ℝ)`
(AKG's Borel model), the pole is a Krein state of that plane, and the resolution and heat flows are
one-parameter degenerations with integer invariants (Hodge defect, collision charge). The field
would be the theory in which "positivity on `v₁^⊥` at infinite resolution" is the polarization of a
limiting structure, inherited along an `SL₂`-type orbit of the resolution flow.

*Criteria it must meet.*
1. Edge validity: its positivity statements hold uniformly across the detection edge; they are
   identities, inherited polarizations or index computations, never estimates against the ground
   energy.
2. Calibration: over `𝔽_q` the resolution flow is trivial and the theory reproduces Weil's Hodge
   index with quantized exponents; on the golden datum it fails where the Hodge index fails.
3. Archimedean source of the square: the single global square comes from the archimedean place, and
   the density of the extremal-weight exponents for two primes is used, not avoided.
4. No-softening compatibility: it must give the sign at degree one (Künneth and Hadamard powers are
   RH at every degree), or an index ceiling for the Künneth square (any finite one is RH).
5. Integrality: indices and charges are integers, so precision `< 1` suffices along homotopies.
6. Selectivity: the inherited structure exists for ζ and fails for flip twins and maximal-margin
   twins; it is built from integers and adeles, never from zero copies.
7. Profile covariance: the edge location as a function of the profile's Denjoy–Carleman class is a
   theorem of the theory (RH-complete receivers end at the quasi-analytic boundary [S]).

*Questions it must answer.*
- What is the limiting structure of `W_{φ,c,N}` as the resolution grows, and is it polarized on
  `v₁^⊥` by an `SL₂`-type mechanism?
- Why is the edge at `τ(c) log N ≈ 1`, and what changes in the form exactly there?
- Is there a monotone or conserved quantity along the resolution flow that controls the Hodge
  defect (an analogue of a `c`-theorem)?
- What is Frobenius at infinity: the correspondence acting as conjugation on the divisor?
- Does Weil's dilation form on `ℓ = 0` admit a shell identity (Q2), and is it the edge limit of the
  universal-regime decompositions?
- Is `κ(φ_c) − 1` an index computed by deformation to a model (2.6.2)?

*Tools it aims to develop.* Asymptotic (nilpotent-orbit type) expansions of families of Hermitian
forms along resolution and heat flows; Krein-space spectral flow and index theorems for such
families; arithmetic sum-of-squares certificates indexed by conductors and successor shells; a
Denjoy–Carleman calculus of profiles and their edges; integer Fredholm readings as edge detectors;
renormalized determinants and counterterms along the flow.

*Objects, language, mechanisms.* Scaling correspondences at resolution; the pole class and the
pole-orthogonal hyperplane; profile classes, universal regime, detection edge, RH regime; the glued
state, its multiplicative and additive readings, Hodge defect; heat homotopy and collision charge;
extremal weight and dense exponents; collided and reflection pairings, Frobenius at infinity;
mechanisms: identities, inherited polarization, homotopy invariance of integers — the three ways a
statement can hold at the edge without seeing the zeros through an estimate.
