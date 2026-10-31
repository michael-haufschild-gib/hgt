# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`, wall labels to `walls-ledger.md`. `[L]` Lean statement read; `[S]` Lean source
unfinished or outside its umbrella; `[map]` frontier-map status. Corpus checkpoint `d4682186c7`.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = κ(K_ζ) = #` zeros right of the
   line, an even number. Glued at `∞` or at any prime, Weil's correlation has index `κ + 1`, hence odd
   or infinite; the translation reading always has exactly one square [L]. The boost, Markov and
   harmonic hyperplanes coincide with `v₁^⊥` [L]. The same integer counts the band poles of the
   loop-Eisenstein factor `Λ(s)/Λ(s+1)` [L].
2. **Reformulations do not soften.** Castelnuovo–Severi at rational scales, a uniform bound on `K_ζ`,
   positivity of any Hadamard power, positivity of the Künneth square, glued test index one, and a
   Serre-dual `h⁰` with quadratic Riemann–Roch on the scaling surface: each is RH [L]. A crossing-free
   deformation of a Hermitian matrix to the identity exists iff the matrix is positive definite, so an
   index computed by deformation to a positive model is the sign itself [L].
3. **Local–global is settled, and it is zero-blind.** Every place glues Weil's data at full index; the
   archimedean form on the hyperplane is Weil's dilation form plus exact shell squares; the global
   pole is the extremal weight of the local poles [L]. Every separable assembly of finitely many
   prime towers built from the truncated explicit formula has glued index `∞` or `r_S + 1`, `r_S + 2`,
   whatever the zeros are, and no pole-free family of them converges to `κ_ζ + 1` on the finite non-RH
   stratum [S]. A two-prime test lattice carries the full `κ` [L]. The zeros are a property of the
   coupling that the infinite prime tail induces between towers.
4. **Estimates reach a universal regime and stop at a defined edge.** The detection edge `e_φ(N)`
   (first overlap with a negative square) is a Lean object; RH ⇔ `e_φ ≡ ∞` for every admissible profile;
   without RH, `e_φ ≤ 2(log N)^β` infinitely often for every `β > ¼` [L]. The tilted-spline edge is
   `≥ (log N)^{α}` for every `α < 1/144` (explicit) and tends to `∞` unconditionally [L]. Optimising
   the binding inequalities of that proof gives a method optimum `≈ 1/114`; the structural ceilings are the
   residual-versus-floor exponent `19` and confinement `16`. The universal regime holds for the tilted
   spline, the strongest RH receivers (every power of `log` on `v₁^⊥`) for C^∞ profiles, and nothing
   transfers between the two profiles. In the plane of resolutions the edge is a threshold curve:
   `W_{φ,c,N}` PSD ⇔ `N < h(atom of width c/N)`; over a curve the edge is `≤ 2g` [S].
5. **Packet arithmetic is rigid, and the pole costs a logarithm.** On conductor packets, one successor
   step and one dyadic dilation see every nonconstant conductor with the sharp constant `3/4`, uniformly
   in the cutoff, with the constant packet as exact kernel [L]. Prime heads and the literal prime
   residual are controlled by the adjunction energy with polylogarithmic conductor cost [S]. The
   prime-pole response costs exactly `S_Q = log Q + O(1)` against adjunction energy, also on every
   pole hyperplane, so no adjunction-only bound is uniform in `Q` [S].
6. **Integer readings are exact and source-certified; detection is gap-dependent.** The horizontal
   collision charge is the Fredholm index of an integer-theta Wiener–Hopf operator on every window; a
   root-free source certificate fixes the stopping prefix, is sound, eventually complete and needs no
   simplicity; RH ⇔ the stopping-prefix index vanishes eventually in scale at every integer height
   [L]. The admissible stage depends on divisor separation. Per unit window
   `n_off ≤ ΔO ≤ 2n·n_off`, `ΔO ≪ log²T` unconditionally [L].
7. **Heat is a homotopy of the glued state.** `κ(φ_c^{(t)}) = N(t)/2 + 1`, antitone, `1` for
   `t ≥ 1/8`; RH is the absence of jumps, `Λ = 0` [L].
8. **Selection is partial and sharp.** The glued test index is `∞` on every finite prime flip; the
   edge of every single prime flip stays bounded while ζ's edge diverges; the atomic Hodge index
   separates every prime-set flip of greatest gap `< 2 log 2`, including thin, co-thin and cofinite
   flips [L]. Unselected: twins with `c_P = c_{Pᶜ} = 0` and general maximal-margin gauges. Local
   counterterms cannot select: on every finite assembly they give `Λ` and a prime-flip twin index `1`
   [S].
9. **Counts are where they were.** Integer producers reach the PNT main term; Möbius cancellation is
   open at half power; the census has `≥ 0.6725` simple critical zeros; deep zeros are `o(V)` [L].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit horizon `N₀` for the `1/144` theorem; optimise the low-band exponent and the overlap/residual budgets up to the method optimum `≈ 1/114` | HF, SRT, AIP, ACS, SC | proved mechanism; constants and bookkeeping |
| A2 | Finish the single-mode exceptional-conductor floor `((1−2θ)/4) log m ≤ W(v_m)`, `(log N)^A ≤ m ≤ N^θ`, `α < ¼`, `A > 8α` | HF, SRT, AIP, MC | paper proof exists; Lean draft unfinished |
| A3 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` | SRT, HF | synthesis error at one explicit scale |
| A4 | Compare CSAR rigidity and relative prime-residual energies with the complete Weil energy on fixed and slowly growing packets | HF, SRT, AIP, ACS | fixed-dimensional comparison with Gamma, poles, mixed Schur terms retained |
| A5 | Gamma/polar head-pole cancellation for packets up to `exp(c√log Y)` | CHMD, HF, AIP | window PNT with classical error; prime side controlled |
| A6 | Edge dictionary: edge exponent of a finite model configuration (one off-line pair of depth `δ`, height `γ`) for the tilted spline | HF, SRT, AIP, SC, EHT | analysis of an explicit model kernel |
| A7 | Explicit capture stage for complete-cell indices | AID, HF, CHMD | effectivise a compactness transfer |
| A8 | Stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` | WD, LA | known exponents; calibration |
| A9 | Certified de Bruijn–Newman bound below `1/8` as an index-one time of the heat state | SC-heat, WD | barrier method + certified numerics |
| A10 | One Lean statement: `ΔO(T) = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf | WD, SRT | composition of `CollisionChargeIncrements` and `BacklundLindelofConverse` |
| A11 | Computable stopping prefix: replace compact minima by certified interval bounds | WD | interval arithmetic on finite theta prefixes |
| A12 | Same-order mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A13 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer | WL | quantify the Farkas / rounding construction |
| A14 | Canonical relative split for general nonzero proper rational subgroup successors | SC, AKG | integer-Haar split is the template; classification and index preservation proved |
| A15 | `𝔽_q(X)` calibration: higher-degree local walls, global Hecke product formula, archimedean Weil state of a curve | SC, ACS, RIT | local wall at `∞`, quantized exponents and the curve edge are proved |
| A16 | Wirsing–Gronwall decay and separation of regular-density flips with `κ > ¼` | RIT, Γ | Wirsing equation proved; discrete Gronwall step remains |
| A17 | `𝔽₃` loop chain: measure-compatible Bruhat unfolding and constant-term evaluation | ACS | Haar, kernels, sections and Weyl convergence are in Lean |
| A18 | Certified Weil positivity past the two-prime aperture `r ≥ ½ log 3`, odd and full | RW, EWU, OWU, CHMD | finite aperture; certified numerics |
| A19 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| A20 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF | effectivise eventual statements |
| A21 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| A22 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A23 | Transfer of the universal regime to the glued state on atomic test families, through the threshold curve | SC | identification of the fixed-width horizon Gram with the complete Weil matrix |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (implies Lindelöf and a zero-free half-plane); **LH** (implies Lindelöf);
**sub**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| Σ-1 | Positivity on `v₁^⊥` across the detection edge (B1) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| Σ-2 | Signed estimate on the subthreshold conductor block beating the residual-versus-floor exponent `19` (B2) | sub | same |
| Σ-3 | Defect bound below `c¹⁶` for nonpositive vectors (B3) | sub; RH at RH-complete overlap | same |
| Σ-4 | Edge location of ζ inside the edge window; sign-preserving profile transfer (B6) | sub | same |
| Σ-5 | Joint prime + Gamma + pole payment of the `log Q` prime-pole cost (B7) | sub | HF, SRT, AIP, ACS |
| Σ-6 | Exact sum-of-squares identity for Weil's dilation form on the boost hyperplane, coupling all towers (B21) | RH | SC, HF, RIT |
| Σ-7 | Index law for nonseparable coupled tower assemblies of the untruncated source (B22) | sub | SC, AKG |
| Σ-8 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| Σ-9 | All-rank / all-degree theta, heat and Jensen signs | RH | TH, LA, HCF, PA, GTA |
| Σ-10 | Arithmetic index ceiling uniform in resolution (B8) | ≥qRH for `K_ζ`; RH for `K_ζ⊠K_ζ` | CHMD, SRT, WD, AID, SC |
| Σ-11 | Subcritical heat count `a < 1` (B11) | sub | WD, SC-heat |
| Σ-12 | Collision charge `< 2` on every window; no heat-index jump; every `Λ_X = 0` (B13, B16) | RH | WD, TG, SC-heat |
| Σ-13 | Uniform collision increment `ΔO ≤ M` or `o(log T)` (B15) | LH | WD, census |
| Σ-14 | Cumulative collision charge `O(T) = o(N(T))` (B14) | sub | WD, census |
| Σ-15 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL |
| Σ-16 | Spectral reality of a realized operator | RH | RN, PTR, W1C, PM |
| Σ-17 | Joint payment of non-arithmetic Gamma graph + signed diagonal + prime reserve + roots + poles | unknown | CHMD, AID, HF |
| Σ-18 | A source-defined noncrossing path to an index-one model | RH | SC, TG, WD |
| Σ-19 | Emptiness of the loop-Eisenstein band poles by a noncancellation theorem (B10) | RH | HF, ACS, SC |
| Σ-20 | Converse Krein–Langer beyond zero configurations (B9) | sub | RIT, HKT |

### Π — square-root precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| Π-1 | Unconditional one-sided count at square-root precision (B19) | RH | WL, PBM, RB, JAS, CTF |
| Π-2 | ε-uniform producer (B18) | sub / RH | WL |
| Π-3 | Moving-scale half-power Möbius cancellation; near-band cyclotomic energy | RH; ≥qRH | MC |
| Π-4 | An unconditional Serre-dual `h⁰` with quadratic RR (B20) | RH | ACS, RIT |
| Π-5 | Exceptional conductor spans beyond `(log N)^A` (B4) | sub | HF, MC, CAF |
| Π-6 | Conductors `N^{½} < m ≤ N` (B5) | sub | HF, SRT, AIP, SC |
| Π-7 | 100% census; pointwise local count | sub | ACS, SRT, IGP, LA, WD |
| Π-8 | Gap-independent detection scale for collision readings (B17) | sub | WD |
| Π-9 | Pointwise heat horizon constant `< ½` (B12) | ≥qRH | WD, LA |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| Γ-1 | Zero-independent selection at the trivial gauge point (B23) | RH | MC, BAG, XN, PM |
| Γ-2 | Hecke invariance of the collided form; an arithmetic conjugation on the divisor (B25) | RH | HF, AP, CDG, WD |
| Γ-3 | Pre-divisor sections / potentials coupled to Ξ | RH | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF |
| Γ-4 | A conformal correspondence over ℤ with factor `≠ 1` and bounded self-intersection | RH | ACS |
| Γ-5 | Selection of maximal-margin twins with `c_P = c_{Pᶜ} = 0` (B24) | sub | HF, ACS, AIP, SRT, SC |
| Γ-6 | Half-parameter cusp selection (`Λ(s) = 0` ⇒ critical) | RH | PM |

## 2.3 The three questions to answer next

**Q1. Where is the edge of the complete Weil family for an off-line configuration, and how close can
unconditional positivity get to it?** The edge is a defined invariant: RH ⇔ it is infinite; without RH
the tilted-spline edge lies in `[(log N)^{1/144}, 2(log N)^{¼+}]` infinitely often [L]. Four parts.
(a) *Edge dictionary* (A6): compute the edge exponent of a model configuration with one off-line pair
of depth `δ` at height `γ`. This tells what zero-free information positivity at `(log N)^α` carries,
and whether `¼` is the sharp detection exponent. (b) A signed (quadratic-form) estimate on the
subthreshold block `m ≲ c`, where the floor is `≍ (m/c)⁷`, beating the exponent `19` that norm
residuals impose. The adjunction-relative residual of CSAR, which costs `(1+log Q)²` instead of a
power of the conductor, is the model for such an estimate. (c) A defect bound for nonpositive vectors
with exponent below `16`. (d) A sign-preserving profile transfer from the tilted spline to a C^∞
profile, whose hyperplane receiver is RH at every power of `log N`. This question gives the most
progress because the C1 cluster is the only place where unconditional positivity grows with
resolution, the edge measures the distance to RH as one exponent, and the dictionary turns every
exponent gained into an explicit statement about zeros. Starting points: CACT
`TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap`; EHT `TheEdgeOfTheCompleteWeilFamily`,
`TheEdgeIsAThresholdCurve`, `TheHorizonFlowAtFixedWidth`; RAPT `Conductor/QuadraticConductorConfinement`;
CAF `PrimePacketCoercivity`; CSAR `RelativePrimeResidual`, `AdjunctionResidualCoercivity`; TM
`TheSincProfileHasAnExactCriticalOverlap`.

**Q2. Is there an exact sum-of-squares identity for Weil's dilation form on the boost hyperplane that
couples all prime towers?** Every structural piece around it is an identity: the local pole–successor
forms are a hyperbolic pair plus shell squares; on `ℓ = 0` the archimedean state is Weil's dilation
form plus the squares of the half-line shells; the matched prime form has one positive direction on
every full finite sieve; a shifted packet's error splits exactly into projection error plus successor
leakage, with sharp `3/4` and constant kernel [L]. The identity is localized by three facts. Separable
tower assemblies are zero-blind [S], so the identity must be nonseparable. The prime-pole response
costs `log Q` against adjunction energy on the hyperplane [S], so the squares must cancel the pole
jointly with Gamma rather than bound it. Quadratic RR is the same datum as the Hodge index [L], so a
Serre-dual `h⁰` is an equivalent target. An identity is the only kind of statement not subject to the
edge obstruction, because it does not pay errors against the ground energy. Test: at fixed overlap the
form on `v₁^⊥` is positive with gap `E₁ + g/2` [L]; a candidate must reproduce that gap. Starting
points: AKG `TheArchimedeanWeilFormIsAShellIdentity`, `TheShellDecompositionOfAPoleSuccessorForm`,
`TowerCoupling/PolarSecondDifference`, `TowerCoupling/STruncatedExplicitTowers`; CSAR
`SuccessorProjection`, `DyadicPoleRigidity`, `PrimeGeneratorPole`, `HarmonicPoleCentering`; RAPT
`Signature/TheMatchedPrimeFormHasOnePositiveDirection`; RIT `TheHodgeIndexHoldsAtEveryFixedOverlap`,
`TheQuadraticRiemannRochIsTheRenormalizedHodgeIndex`.

**Q3. Can the integer collision machinery give a height-uniform statement?** Per window it is
complete: exact Fredholm reading, source-certified stopping prefix, no simplicity assumption, index
`0` on `T ≤ 3` [L]. Every height-uniform output is blocked by one dependence: the admissible stage
depends on the divisor separation of the window [L]. The question has two layers. (a) A detection
stage depending only on `T` (B17); without it no uniform bound can be read from the integers.
(b) A cumulative bound `O(T) = o(N(T))`, which forces `N_off(T) = o(N(T))`, i.e. 100% of the zeros on
the line, with no Lindelöf implication. The calibration of the targets is exact [L]: `ΔO = o(log T)`
already gives Lindelöf, `sup O < ∞` is finite off-line support, `O < 2` per window is RH. This ties
WD, SC-heat and the census together and is the only place where integrality gives exact readings.
Starting points: CDG `SourceIntrinsicStoppingRule`, `CollisionChargeIncrements`,
`IntegerThetaCollisionFredholmIndex`, `ThetaPrefixIndexTransition`, `ThetaPrefixCuspAndSectoriality`;
AOG `TheIndexExit`; RHTower `BacklundLindelofConverse`.

## 2.4 A wildly different route

**The rigidity route: RH from rigidity of the joint prime action, taken over the whole prime set.**

All routes in the map are either quantitative (a sign estimate on a growing family, a count at
square-root precision) or index computations on the affine group of ℚ. The rigidity route asks for a
qualitative conclusion from the multiplicative action where it has higher rank.

Setting. On `S`-arithmetic solenoids `X_S = (ℝ × ∏_{p∈S} ℚ_p)/ℤ[1/S]`, `|S| ≥ 2`, the primes act by
commuting automorphisms with dense exponents [L]. Higher-rank actions are rigid: positive-entropy
invariant measures of `×p, ×q` are Haar (Rudolph, Johnson), higher-rank diagonal actions are measure
rigid (Einsiedler–Katok–Lindenstrauss), smooth cocycles over higher-rank Anosov actions are
cohomologous to constants (Katok–Spatzier). Rank-one hyperbolic actions instead carry resonances.

Route. (i) Attach to an off-line zero `ρ` a positive object: an invariant measure of positive entropy,
or a joint eigendistribution of the prime action with non-unitary eigenvalues `p^{±(Re ρ − ½)}`.
(ii) Apply higher-rank rigidity: such objects are Haar or vanish. (iii) Conclude that no off-line zero
exists. Precedent: arithmetic quantum unique ergodicity was proved by measure rigidity (Lindenstrauss)
where the L-function route needs an unavailable subconvexity bound; RH is likewise qualitative.

How it avoids the walls.
- **Σ**: no sign estimate on a growing family; the positivity is that of measures. The edge
  obstruction does not apply because nothing is estimated against a ground energy.
- **Π**: the conclusion is qualitative; no error term appears.
- **Γ**: the higher-rank structure is specific to ℤ (dense exponents for two primes, a lattice over
  `𝔽_q[T]`); unitary twists cannot create non-unitary eigenvalues.

Its wall, in sharpened form: **rank against visibility.** Every finite-`S` structure is zero-blind:
separable `S`-truncated assemblies have zero-independent index [S], and the renormalized infinite
product of local poles forgets the global pole [L]. Objects that see the zeros need the whole prime
tail, and after the quotient by principal units the continuous part of the action is the rank-one
archimedean scaling, where resonances exist. The route survives only on an infinite-rank system that
keeps the tail: the affine semigroup `{n ↦ n + 1, n ↦ pn}` acting on `Ẑ` together with the
archimedean flow. The corpus has one rigidity statement of exactly this type. On conductor packets
(functions on `Ẑ` through finite quotients) one successor step and one dyadic dilation detect every
nonconstant conductor with constant `3/4`, uniformly in the cutoff, and the joint kernel is the
constant packet [L]. That gap does not degrade as `Q → ∞`.

First question: does the affine semigroup on `L²₀(Ẑ)` coupled to the archimedean scaling admit joint
eigendistributions whose dilation eigenvalues are non-unitary, outside the packet space where the
`3/4` gap holds? If not, what single-zero object maps into that space?

No second route was found that avoids all three walls. Two corpus results constrain any candidate:
by the edge principle, a statement proved without zero information holds only where zeros are
invisible; by finite-prime blindness, a statement built from finitely many primes cannot see the
zeros. A distant route therefore has to be qualitative and global in the primes. The rigidity route
is the only one of that shape.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — all-vector positivity beyond every method ceiling
**Question.** Prove that the tilted-spline complete Weil matrix is positive definite on all vectors,
eventually in `N`, for `1 ≤ c ≤ (log N)^{1/12}`.
- **Below RH / quasi-RH**: RH-completeness of this profile starts at `(log N)^{¼}`. Without the edge
  dictionary (A6) no implication from positivity at `(log N)^{1/12}` to a zero-free region is known.
  With it, the result becomes an explicit exclusion of the configurations whose edge exponent is below
  `1/12`.
- **Advance**: `1/12` is above the method optimum `≈ 1/114`, the residual-versus-floor ceiling `1/19`
  and the confinement ceiling `1/16`. A proof needs exactly the two missing tools, a quadratic-form
  estimate at floor scale on the subthreshold block and a defect bound below `c¹⁶`. It would show all
  three ceilings are methodological, bracket the edge of ζ in `[(log N)^{1/12}, 2(log N)^{¼+}]` under
  ¬RH, and supply the edge-scale tool every class-C1 route needs.

### 2.5.2 Route SC — a two-prime coupling index law
**Question.** For kernels on the `{2,3}` `S`-unit lattice `ℤ²`, express the polar index through second
differences, as `κ₀(k) = κ(Δ²k)` does on `ℤ`. Mean-zero finitely supported vectors on `ℤ²` are exactly
the divergences of finitely supported vector fields, and pulling a Hermitian form back along a
surjection preserves its negative index. So `κ₀(k) = κ(H_k)`, where `H_k` is the `2 × 2` matrix kernel
of mixed second differences `∂_i ∂_j^* k`. Prove the two-dimensional zero-or-infinity law and pole
trichotomy for decaying `H_k`. Then apply it to `K_ζ` on `ℤ²`, which carries the full index. The goal
is to split `κ_ζ` into a separable diagonal part, which the `S`-truncated classification computes, and
the index contributed by the off-diagonal coupling `∂₂ ∂₃^* K_ζ`.
- **Below RH**: an identity and a classification; it fixes no index value.
- **Advance**: SC gets its canonical object. Separable assemblies are zero-blind [S], so all zero
  information of the glued state must sit in the mixed differences. The law turns SC from "bound the
  index of `φ_c`" into "bound the index of one explicit coupling operator on `ℤ²`", whose prime-side
  expression involves only primes acting across both towers. It is the Hasse principle for `κ` with
  its global correction term made explicit, and it gives Q2 its domain: the identity has to be found
  for the coupling operator, not for the whole state. The one-dimensional identity and trichotomy
  ([S]) are the template.

### 2.5.3 Route WD — 100% of the zeros from integer theta data
**Question.** Prove from integer theta data that the cumulative horizontal collision charge satisfies
`O(T) = o(N(T))`.
- **Below RH / quasi-RH**: it forces `N_off(T) ≤ O(T) = o(N(T))`, a critical-line proportion `→ 1`, with
  no known Lindelöf or zero-free-region consequence. The stronger per-window bound
  `ΔO(T) = o(log T)` already gives Lindelöf through Backlund's equivalence, and `sup O < ∞` is finite
  off-line support. The cumulative bound is the correctly placed sub-Lindelöf target.
- **Advance**: it would be the first height-uniform output of the Fredholm machinery. It goes beyond
  the `0.6725` simple-critical census and every known critical proportion, by an integer mechanism and
  not by mollification. Its prerequisite is a gap-independent detection stage (B17), which is itself a
  structural result for WD: the integer reading would be valid at a scale chosen from the height alone.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a renormalized Hodge index theorem by a coupled identity
**Question.** At every resolution `(φ, c, N)`, is the complete Weil form on `v₁^⊥` an exact sum of
squares of arithmetic functionals plus a remainder that vanishes on `v₁^⊥`? The functionals must be
indexed by conductors, successor shells and the coupling between prime towers. Equivalently, does
the scaling surface carry a nonnegative Serre-dual `h⁰` with quadratic Riemann–Roch growth?
- **Why it opens the path**: an identity at RH-complete resolution is RH [L for the equivalence with
  quadratic RR]. It is the only mechanism not excluded by the edge logic. It is compatible with every
  local identity and with the sharp packet rigidity. The finite-prime classification tells it where its
  squares must live. Over `𝔽_q` it is the Hodge index of the Frobenius graph, where the edge is bounded
  by `2g`.

### 2.6.2 Route SC — a kernel-rigid homotopy
**Question.** Is there a source-defined continuous path of Hermitian forms from the glued Weil state
`φ_c` to an index-one model along which every null vector is forced, by an arithmetic rigidity
theorem, to be the pole mode? An example of such a theorem: a vector neutral under successor and prime
dilations is constant.
- **Why it opens the path**: along a nondegenerate path the negative index is constant, and at a
  crossing it can change only through a null vector [L]. A crossing-free deformation to a positive model
  is the sign itself [L], so the sign cannot be avoided. It can be converted into a kernel statement.
  If every null vector along the path is pole-like, and pole-like vectors are excluded on the boost
  hyperplane, the path is crossing-free and `κ(φ_c) = 1`. Kernel statements are qualitative: they are
  unique-continuation or rigidity theorems, and the joint successor/dyadic kernel being the constant
  packet [L] is a corpus instance. The heat homotopy is a source path whose crossings are exactly the
  collisions [L]; the question asks for a path whose crossings are excluded by rigidity.

### 2.6.3 Route WD — Frobenius at infinity
**Question.** Is there an arithmetic correspondence acting on the zero divisor as complex conjugation,
identifying the collided pairing `(ρ, ρ̄)` with the reflection pairing `(ρ, 1 − ρ)`? Equivalently, is
there a prime-side upper bound for the Hecke defect `E(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` at one
large dyadic scale?
- **Why it opens the path**: the collided side is computed exactly from theta data, including every
  depth moment, the local count and the collision charge [L]. Positivity of `D` is free and its
  translation invariance is RH [L]. Dyadic amplification `E(2L) ≥ 4E(L) + E(L)²/D` makes the collided
  mass a non-scaling invariant, the arithmetic stand-in for the genus in Weil's tensor-power argument.
  RH is equivalent to subexponential growth of `E(2^k)`, and a bound at one large dyadic scale
  transfers losslessly to every smaller scale [L]. A conjugation correspondence would make the
  collided form a Weil form, force `E` and the collision charge to vanish, and give WD the canonical
  object that Frobenius gives over `𝔽_q`.

## 2.7 Does closing RH need a new field?

**Assessment: yes. Its first layer exists in Lean, and its core is missing.** Renormalized
intersection theory (RIT) and adelic Krein geometry (AKG) are the intersection-theoretic field the
Frobenius-graph analogy calls for. They answer their own questions: how local poles glue (only the
extremal weight), what Castelnuovo–Severi and quadratic Riemann–Roch say (RH), what a Künneth square
adds (nothing), whether the heat flow is a homotopy (yes, one unit of Hodge defect per collision), and
whether the pairing selects ζ (against finite flips and submaximal margins). Edge Hodge theory (EHT)
is the resolution-theoretic layer. It defines the detection edge and proves that RH is its
nonexistence, that the edge diverges unconditionally over ℤ and is bounded by `2g` over a curve, that
at fixed width the Hodge defect is a monotone integer converging to the number of seen zeros, and
that an index computed by deformation to a positive model is the sign [L/S]. CSAR is its arithmetic
layer: exact rigidity of conductor packets and the sharp cost of the pole [L/S].

The remaining obstruction is logical. Estimates proved without zero information are valid only where
zeros are invisible. Index reformulations reproduce RH exactly. Homotopy invariance reproduces it as
noncrossing. Finite-prime constructions are zero-blind. What is needed is a theory whose statements
hold at the edge by structure and whose objects are global in the primes.

**Working name: edge Hodge theory of the scaling surface (EHT, extended).**

*What it is about.* The family of finite-resolution intersection forms `W_{φ,c,N}` of scaling
correspondences, viewed as a degenerating family over the plane of resolutions `(w, N)`. Its central
object is the threshold curve `h(w)`, the horizon at which the width-`w` atom first sees a zero, and
the edge where the section `w = c/N` meets it. Its second object is the coupling of the prime towers
through the infinite prime tail, the only place the zeros can live.

*What it would be like.* Hodge theory of degenerations rather than of a single variety. In
degenerations of polarized Hodge structures, positivity survives in the limit by representation
theory: the nilpotent-orbit and `SL₂`-orbit theorems polarize the limiting mixed structure without
estimates. The scaling surface has the ingredients. The boost and the conformal successor form one
hyperbolic plane on which the affine group acts through `SL(2, ℝ)`. The pole is a Krein state of that
plane. The resolution and heat flows are one-parameter degenerations with integer invariants: Hodge
defect, horizon defect, collision charge.

*Criteria it must meet.*
1. Edge validity: its positivity statements hold uniformly across the edge. They are identities,
   inherited polarizations, or index statements whose noncrossing is forced by rigidity; never
   estimates against the ground energy.
2. Calibration: over `𝔽_q` the resolution flow is trivial and the edge is `≤ 2g`. The theory reproduces
   Weil's Hodge index with quantized exponents and fails on the golden datum, whose edge is `2`.
3. Archimedean source of the square: the single global square comes from the archimedean place. The
   density of the extremal-weight exponents for two primes is used, not avoided.
4. Global in the primes: its objects are not limits of separable finite-prime assemblies, which are
   zero-blind. The coupling of all towers is a primary object.
5. No-softening compatibility: it gives the sign at degree one, since Künneth and Hadamard powers are
   RH at every degree.
6. Integrality and parity: indices and charges are integers, the glued index is odd, and precision
   `< 1` suffices along nondegenerate paths.
7. Selectivity: the inherited structure exists for ζ and fails for every sign-gauge twin, including
   those with `c_P = c_{Pᶜ} = 0`. It is built from integers and adeles, never from zero copies.
8. Profile covariance: the edge as a function of the profile's Denjoy–Carleman class is a theorem.
   Positivity transfers between profiles.

*Questions it must answer.*
- What is the limiting structure of `W_{φ,c,N}` along the threshold curve, and is it polarized on
  `v₁^⊥` by an `SL₂`-type mechanism?
- What is the edge dictionary: which zero configurations have which edge exponent, and why is the RH
  threshold at `τ(c) log N ≈ 1`?
- Is there a quantity along the resolution flow that controls the Hodge defect from above, the
  counterpart of the horizon defect, which controls it from below?
- What is the index law of the nonseparable tower coupling, and does Weil's dilation form admit a shell
  identity on that coupling?
- What is Frobenius at infinity: the correspondence acting as conjugation on the divisor?
- Which arithmetic rigidity theorems make source paths crossing-free?

*Tools it aims to develop.* Asymptotic (nilpotent-orbit type) expansions of families of Hermitian
forms along resolution and heat flows. Krein-space spectral flow with noncrossing criteria from kernel
rigidity. Polar second-difference calculus on `ℤ^S` for coupled towers. Arithmetic sum-of-squares
certificates indexed by conductors, successor shells and tower couplings. A Denjoy–Carleman calculus of
profiles and their edges. Integer Fredholm readings with height-only detection stages. Renormalized
determinants and counterterms along the flow.

*Objects, language, mechanisms.* Scaling correspondences at resolution; the plane of resolutions, the
threshold curve and the edge; the pole class and the pole-orthogonal hyperplane; universal regime and
RH regime; the glued state, its multiplicative and additive readings, Hodge and horizon defects; tower
coupling and the prime tail; heat homotopy and collision charge; extremal weight and dense exponents;
collided and reflection pairings, Frobenius at infinity. Its mechanisms are the three ways a statement
can hold at the edge without seeing the zeros through an estimate: identities, inherited polarization,
and rigidity-forced noncrossing.
