# Suzuki stage-2 → stage-3 promotion ledger

Working file for the promotion of every card in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki/`.

**Destination convention.** A promoted card is `git mv`-ed to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki/<id>.md` with its `Stage:` line
set to `3 — formalized in Lean 4`, and a certificate `<id>-formalized.md` sits beside it.  Any
pre-existing flat companion at `3-formalized/new_scientific_knowledge/<id>.md` is `git mv`-ed to
that name and its relative links deepened by one level.  Inbound links are repaired repo-wide.

**Promotion rule.** A card may be promoted only when every statement it labels `[PROVED]`,
`[PROVED HERE]` or `[PAPER-PROVED]` has an unconditional Lean declaration whose axiom surface is
`propext, Classical.choice, Quot.sound`.  Gates that are open *research* ("prove RH", "identify the
restricted-Weil trace", "specialist novelty review", "3 → 4 publication-ready") do not block
promotion; gates that name missing Lean do.

## A. Promoted (66 of 103)

- `suzuki-affine-resolvent-krein-defect`
- `suzuki-affine-sewn-weil-robin-far-tail-factorization`
- `suzuki-aperture-rees-superpolynomial-conditioning`
- `suzuki-bicausal-displacement-overlap-conservation`
- `suzuki-bicausal-no-free-splice-classification`
- `suzuki-causal-depth-frostman-transfer`
- `suzuki-causal-depth-rectangular-caratheodory-growth`
- `suzuki-causal-entry-third-jet-boundary-law`
- `suzuki-causal-hinge-boundary-tail-green-law`
- `suzuki-causal-weil-robin-green-identity`
- `suzuki-coherent-causal-depth-fusion`
- `suzuki-coherent-response-gain-no-go`
- `suzuki-compactified-inverse-phase-lattice-holography`
- `suzuki-completed-eigenmode-atomic-jump-boundedness`
- `suzuki-critical-affine-cauchy-residual-divergence`
- `suzuki-critical-aperture-quarter-shift-current`
- `suzuki-critical-apex-vacuum-capacity-no-go`
- `suzuki-critical-entry-wall-quarter-shift-green-law`
- `suzuki-critical-rooted-bianchi-cofinal-no-go`
- `suzuki-critical-wall-field-resolvent-dressing-law`
- `suzuki-critical-wall-field-square-root-weld`
- `suzuki-donoghue-defect-spectral-measure-law`
- `suzuki-dyadic-orbit-chart-h1-coverage`
- `suzuki-finite-morse-resolvent-jet-completion`
- `suzuki-finite-shift-flat-projective-resolvent-holonomy`
- `suzuki-full-frequency-neumann-holonomy-survivor`
- `suzuki-global-local-compound-bezoutian-weld`
- `suzuki-global-phase-conjugacy-divisor-flow`
- `suzuki-ground-edge-aperture-robin-obstruction`
- `suzuki-ground-residue-polarization-selection`
- `suzuki-high-clock-prime-tangent-tomography`
- `suzuki-homogeneous-projective-resolvent-plucker-lift`
- `suzuki-interior-excursion-shift-selection`
- `suzuki-jump-kernel-loewner-growth-gap`
- `suzuki-localized-orbit-lift-selfadjointness-trilemma`
- `suzuki-low-frequency-boundary-counterterm-renormalization`
- `suzuki-mangoldt-apex-lock-rigidity`
- `suzuki-mangoldt-log-haar-bicausal-transport`
- `suzuki-mangoldt-macroscopic-prime-block-surplus`
- `suzuki-mangoldt-uniform-dyadic-block-surplus`
- `suzuki-marked-secant-midpoint-lorentz-completion`
- `suzuki-negative-projector-coherent-completion`
- `suzuki-negative-shift-defect-escape`
- `suzuki-parity-hankel-infinite-negative-index`
- `suzuki-parity-hankel-infinite-rank-no-go`
- `suzuki-parity-resolvent-transport-budget`
- `suzuki-physical-log-low-frequency-boundary-lock`
- `suzuki-position-torque-prime-clock-irreducibility`
- `suzuki-prime-clock-atom-velocity-transference`
- `suzuki-prime-seam-parity-hankel-strong-indefiniteness`
- `suzuki-projective-affine-secant-tensor-lift`
- `suzuki-rectangular-positive-arch-lag-completion`
- `suzuki-rectangular-ward-defect-semiboundedness`
- `suzuki-resolvent-jet-homogeneous-plucker-tomography`
- `suzuki-screw-cesaro-curvature-recurrence`
- `suzuki-screw-compact-hull-parity-law`
- `suzuki-shift-spectral-monotone-likelihood-transfer`
- `suzuki-shifted-xi-target-flat-pencil`
- `suzuki-support-pruned-evaluation-rigging-fracture`
- `suzuki-support-pruned-selfadjoint-seam-carrier`
- `suzuki-two-jet-shifted-hankel-gate`
- `suzuki-volterra-cartesian-phase-defect`
- `suzuki-wall-field-projective-density-separation-law`
- `suzuki-xi-first-defect-jet-gap`
- `suzuki-xireal-fe-bipolarization-completion`
- `suzuki-zero-trace-cofinal-convex-recurrence`

## New Lean modules written for this promotion

```text
HTGeometry/AlternatingChordLaw.lean                  2-alternating chord law + exterior instance
HTGeometry/AtomicJumpForm.lean                       translation-pair identity, truncation
                                                     coercivity, positive weighted combination
HTGeometry/DyadicLatticeCover.lean                   lattice window cover, finite subcover, weight
RHTower/SuzukiCausalEntryMovingCutRealization.lean   moving-cut integrals, their three derivative
                                                     laws, hypothesis-free jet chain, entry law
RHTower/SuzukiCriticalAperturePrimeCurrent.lean      absolute prime summability of the critical
                                                     quarter-shift current; cofinal current
RHTower/SuzukiPrimeClockPhysicalSine.lean            velocity = truncated critical sine transform
RHTower/SuzukiProjectiveResolventBlade.lean          Plücker blade form of the resolvent chord
RHTower/SuzukiSupportPrunedSeamCarrierBounds.lean    adjoint law, norm bounds, pruned action
RHTower/SuzukiGammaShiftKappa.lean                   kappa_sigma finiteness, integrated
                                                     numerical-range bound, multiplier form
HTGeometry/MollifierPositionCommutator.lean          the position commutator of a mollifier
HTGeometry/HadamardFinitePart.lean                   punctured Cauchy kernel in closed form and
                                                     the exact cutoff finite-part split
```

All eight are wired into their area umbrella, build green, and are axiom-clean.

## B. Remaining (37)

- `bv-copoisson-sharp-critical-half-weight-log-flux`
- `suzuki-arithmetic-tangent-inverse-moment-holography`
- `suzuki-boundary-log-nonclock-nonflat-tangent`
- `suzuki-carleman-flat-port-weighted-strip-barrier`
- `suzuki-complementary-primitive-flux-derivative-recovery`
- `suzuki-coordinate-cutoff-covariance-classification`
- `suzuki-coordinate-cutoff-primitive-flux-identity`
- `suzuki-exact-log-remainder-signed-trace-rigidity`
- `suzuki-exterior-feshbach-pruning-law`
- `suzuki-exterior-residual-rigged-wiener-realization`
- `suzuki-finite-aperture-boundary-phase-locking`
- `suzuki-flat-primitive-flux-volterra-liouville`
- `suzuki-forced-gamma-upper-strip-gluing`
- `suzuki-gamma-homogeneous-half-log-scattering-classification`
- `suzuki-gamma-prime-normal-corona-equivalence`
- `suzuki-gamma-skew-frequency-flux-liouville`
- `suzuki-gamma-three-grade-delay-root-observability`
- `suzuki-gamma-wall-block-hardy-and-derivative-scattering`
- `suzuki-gamma-weighted-tail-coercivity`
- `suzuki-interior-seam-indicial-dipole-exclusion`
- `suzuki-log-recurrence-polynomial-carrier-trichotomy`
- `suzuki-neumann-dominated-shift-cone-obstruction`
- `suzuki-paired-seam-carleman-logistic-normal-form`
- `suzuki-physical-log-grade-nuclear-summability`
- `suzuki-polar-remainder-lipschitz-gamma-subcriticality`
- `suzuki-prime-normal-binomial-resolvent`
- `suzuki-primitive-flux-nonnormal-graph-reduction`
- `suzuki-residual-overcrowding-entire-pair-closure`
- `suzuki-root-retained-exterior-dilation`
- `suzuki-scalar-analytic-forcing-trace-zero-h1`
- `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy`
- `suzuki-two-port-return-redundancy-and-interior-null-core`
- `suzuki-weak-signed-half-log-trace`
- `suzuki-weil-position-torque-recurrence`
- `suzuki-wiener-cutoff-closed-graph-relation`
- `suzuki-wiener-neumann-plancherel-order-repair`
- `suzuki-wiener-nuclear-boundary-carrier`

Every one is listed in section C with the exact Lean object it still needs.

## C. Open Lean debt — the remaining work

Each entry names the exact missing Lean object as the card itself states it.

### C1. Mechanical (wiring / audit only)

| card | missing |
|---|---|
| `suzuki-aperture-rees-superpolynomial-conditioning` | targeted module build, lint, axiom audit, umbrella wiring |
| `suzuki-xi-first-defect-jet-gap` | umbrella imports, formal lint, `#print axioms` audit |

### C2. Elementary or near-elementary core stated by the card

| card | missing |
|---|---|
| `suzuki-dyadic-orbit-chart-h1-coverage` | real-line lattice-cover lemma `(11)` and weight inequality `(6)` |
| `suzuki-gamma-three-grade-delay-root-observability` | exact finite-step squared-norm sum `(11)` |
| `suzuki-completed-eigenmode-atomic-jump-boundedness` | shift-pair/atomic-jump identity `(7)–(8)`, truncation monotonicity `(9)–(10)`, finite positive weighted sum, source specialization `c_n = Λ(n)/√n ≥ 0` |
| `suzuki-two-port-return-redundancy-and-interior-null-core` | redundancy `(2)–(5)` (needs the analytic graph object) |
| `suzuki-primitive-flux-nonnormal-graph-reduction` | Bochner-`L²` estimate `(15)` |
| `suzuki-complementary-primitive-flux-derivative-recovery` | weak Bochner derivative theorem |
| `suzuki-gamma-skew-frequency-flux-liouville` | frequency current `(9)` and its zero-current consequence |

### C3. Substantial analytic infrastructure named by the card

| card | missing |
|---|---|
| `suzuki-arithmetic-tangent-inverse-moment-holography` | module `SuzukiArithmeticTangentHolography.lean` does not exist; six declarations listed |
| `suzuki-carleman-flat-port-weighted-strip-barrier` | improper integration, `s = e^{-L}` chart, Carleman kernel, logistic approximate identity |
| `suzuki-coordinate-cutoff-covariance-classification` | high-oscillation `L²` corollary `(15)` |
| `suzuki-coordinate-cutoff-primitive-flux-identity` | analytic block estimates `(18)–(23)` |
| `suzuki-exact-log-remainder-signed-trace-rigidity` | half-line kernel `(2)`, BV cutoff convergence, two kernel moments, penalized extrema |
| `suzuki-exterior-feshbach-pruning-law` | analytic Feshbach–log conjugation `(37)`, infinite Neumann norm bound |
| `suzuki-exterior-residual-rigged-wiener-realization` | no Lean section at all |
| `suzuki-flat-primitive-flux-volterra-liouville` | Gamma commutator block estimate, exponential envelopes, infinite-tail Volterra lemma, Bochner block summation |
| `suzuki-forced-gamma-upper-strip-gluing` | Gamma-ratio strip modulus and vector-valued Paley–Wiener translation |
| `suzuki-gamma-homogeneous-half-log-scattering-classification` | Hilbert-valued oscillatory Fourier/Paley–Wiener connector; branch gluing `(21) → (25)` |
| `suzuki-gamma-prime-normal-corona-equivalence` | forced-domain theorem `(21)` |
| `suzuki-gamma-wall-block-hardy-and-derivative-scattering` | Hilbert-valued weighted Hardy inequality `(39)`, cutoff identity `(47)`, equivalence `(45)` |
| `suzuki-interior-seam-indicial-dipole-exclusion` | slowly varying Fourier Abelian asymptotics, principal symbol of the logarithmic jump |
| `suzuki-log-recurrence-polynomial-carrier-trichotomy` | six-item chain `(8)`, `(14)`, `(15)`, `(17)`, `(21)–(24)`, `(28)` |
| `suzuki-neumann-dominated-shift-cone-obstruction` | `(4)`: strong-resolvent convergence of the actual restricted operator |
| `suzuki-paired-seam-carleman-logistic-normal-form` | singular integral cancellation, improper beta integration, weighted `L²` convolution, physical logarithmic chart |
| `suzuki-physical-log-grade-nuclear-summability` | the exact physical word-profile object `(16)` |
| `suzuki-polar-remainder-lipschitz-gamma-subcriticality` | Suzuki's literal polar kernel and completed convolution operator |
| `suzuki-prime-normal-binomial-resolvent` | `(2)`: parameter derivative of the continuous functional calculus of `A_L^{-1/2}` |
| `suzuki-root-retained-exterior-dilation` | root-retained boundary-log-domain theorem `(23)` |
| `suzuki-scalar-analytic-forcing-trace-zero-h1` | vector-valued Paley–Wiener strip translation, Gamma-ratio modulus, block `L²` convolution, weak mollifier passage |
| `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy` | `ℓ²(ℤ^d)` weighted shifts, prime-log recurrence, Borel–Cantelli, physical boundary chart |
| `suzuki-weak-signed-half-log-trace` | half-line/whole-line identity `(6)–(7)`, commutator `(17)`, moving mollifier `(21)`, penalized extrema |
| `suzuki-weil-position-torque-recurrence` | moving-cutoff torque continuity/exponential order, absolute Fubini for the prime tent sum, cofinal sign theorem `(19)` |
| `suzuki-wiener-cutoff-closed-graph-relation` | unbounded Fourier multiplier `a_a(D)`, sharp interval projection, Carleman cross block |
| `suzuki-wiener-neumann-plancherel-order-repair` | discrete convolution domination, geometric `ℓ¹` resolvent, mixed-norm Minkowski, coordinatewise Plancherel |
| `suzuki-wiener-nuclear-boundary-carrier` | completed Hardy amplitudes, valuation convolution, infinite Neumann series, nonlinear charts |
| `bv-copoisson-sharp-critical-half-weight-log-flux` | Theorem D: analytic Rademacher logarithmic Gram and Stein defect |

### C4. Cards to re-audit before promoting

| card | reason |
|---|---|
| `suzuki-residual-overcrowding-entire-pair-closure` | statement `(19)` is FALSE on the corpus's order-isomorphism carrier model (`not_fixedLatticeJets_determine_reflectionNormalized_carrier`); it is a theorem about the analytic carrier class only |
| `suzuki-finite-aperture-boundary-phase-locking` | multi-module plan, "general `k` still open" |
| `suzuki-finite-morse-resolvent-jet-completion` | claims complete; verify |
| `suzuki-compactified-inverse-phase-lattice-holography` | long Lean-target list; verify each |
| `suzuki-global-phase-conjugacy-divisor-flow` | ditto |
| `suzuki-finite-shift-flat-projective-resolvent-holonomy` | ditto |
| `suzuki-donoghue-defect-spectral-measure-law` | operator equality `(7)` general case |
| `suzuki-shift-spectral-monotone-likelihood-transfer` | long list |
| `suzuki-negative-shift-defect-escape` | long list |
| `suzuki-screw-cesaro-curvature-recurrence`, `suzuki-screw-compact-hull-parity-law`, `suzuki-two-jet-shifted-hankel-gate`, `suzuki-projective-affine-secant-tensor-lift`, `suzuki-resolvent-jet-homogeneous-plucker-tomography`, `suzuki-zero-trace-cofinal-convex-recurrence`, `suzuki-high-clock-prime-tangent-tomography`, `suzuki-prime-clock-atom-velocity-transference`, `suzuki-ground-residue-polarization-selection`, `suzuki-localized-orbit-lift-selfadjointness-trilemma`, `suzuki-low-frequency-boundary-counterterm-renormalization`, `suzuki-physical-log-low-frequency-boundary-lock`, `suzuki-support-pruned-evaluation-rigging-fracture` | claim complete; verify declarations against numbered statements |

## Corpus debt discovered on the way

- **Ramaré–Zuniga Alterman capacity** `∑_{d ≤ X} Λ(d)/d ≤ log X` (`MangoldtLogHaarCapacity` in
  `RHTower/SuzukiMangoldtLogHaarTransport.lean`) is a named `Prop`, not a theorem.  The corpus has
  `mertens_first` (`|∑ Λ(d)/d − log n| ≤ log 4 + 4`) only.  Numerically the slack is `≥ 0` with
  minimum `0` at `n = 1` and `0.3466` at `n = 2`, tending to `γ`; the inequality is true.  An
  unconditional proof needs an effective saving over the trivial `ψ(n) ≈ n` bound.

## D. Executable routes for the remaining cards

Written so the next working session can start from a proof plan rather than a re-audit.

### D1. Seam-carrier `ℓ²` computations

`suzuki-gamma-three-grade-delay-root-observability` `(11)`:
`‖P T β‖² = c_a² (|β₋|² + |β₊|²)` for `β = β₋ e_(left,0) + β₊ e_(right,0)`.
The mathematical content is an *admissibility count*: with `x(left,ν) = −a + λ(ν)` and
`x(right,ν) = a − λ(ν)`, the step `+j e_p` is admissible from the left root and inadmissible from
the right, and `−j e_p` the other way round. So exactly one of the two terms of
`U_(j e_p) + U_(−j e_p)` survives the projection at each root, and the survivors are pairwise
orthogonal basis vectors with coefficient `w_(p,j) = (log p)/p^(j/2)`. Summing squares gives
`c_a² = ∑ (log p)²/p^j`. Build on
`RHTower/SuzukiSupportPrunedSelfAdjointSeamCarrier.lean` (carrier, shift, adjacency,
`suzukiAdmissibleSeamVertices`) and `RHTower/SuzukiSupportPrunedSeamCarrierBounds.lean`
(`suzukiSupportPrunedPrimeAdjacency_apply` already gives the coordinatewise action, which is the
whole input). What is missing is only the `lp` norm of a finite orthogonal family.

### D2. Analytic infrastructure to build, in dependency order

Each of these is named by several cards at once, so building one closes part of several.

1. **Hadamard finite part on an interval.**  *(Done — `HTGeometry/HadamardFinitePart.lean`.)*
   What remains on top of it: the `ε → 0` limit of `cutoffDividedDifference` for a Lipschitz
   weight (dominated convergence against the constant Lipschitz bound), and then the operator-level
   statement `(4)`, which needs `A_a`.
   `Pf ∫_{-a}^{a} v(y)/|x−y| dy = ∫ (v(y)−v(x))/|x−y| dy + v(x) log(a²−x²)`.
   Definition: `lim_{ε→0} (∫_{|x−y|>ε} v/|x−y| + 2 v(x) log ε)`. The proof is the exact
   computation `∫_{(-a,a), |y−x|>ε} dy/|x−y| = log(a²−x²) − 2 log ε` plus dominated convergence
   for the Lipschitz divided difference. Closes Theorem A `(4)`–`(8)` of
   `suzuki-boundary-log-nonclock-nonflat-tangent`, and is the kernel of
   `suzuki-exact-log-remainder-signed-trace-rigidity` `(2)`.
2. **Vector-valued Paley–Wiener strip translation** and the **Gamma-ratio strip modulus**.
   Named by `suzuki-forced-gamma-upper-strip-gluing`,
   `suzuki-scalar-analytic-forcing-trace-zero-h1`,
   `suzuki-gamma-homogeneous-half-log-scattering-classification`,
   `suzuki-gamma-prime-normal-corona-equivalence`.
3. **Hilbert-valued weighted Hardy inequality** `(39)` of
   `suzuki-gamma-wall-block-hardy-and-derivative-scattering`.
4. **Mixed-norm Minkowski + coordinatewise Plancherel** for
   `suzuki-wiener-neumann-plancherel-order-repair` `(4)`.
5. **Carleman kernel and the `s = e^{-L}` chart** for
   `suzuki-carleman-flat-port-weighted-strip-barrier` and
   `suzuki-paired-seam-carleman-logistic-normal-form`.
6. **Unbounded Fourier multiplier `a_a(D)` with sharp interval projection** for
   `suzuki-wiener-cutoff-closed-graph-relation` and `suzuki-wiener-nuclear-boundary-carrier`.
7. **Weighted `ℓ²(ℤ^d)` shifts + prime-log recurrence + Borel–Cantelli** for
   `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy` and
   `suzuki-log-recurrence-polynomial-carrier-trichotomy`.

### D3. Cards whose gap is one identified step

- `suzuki-neumann-dominated-shift-cone-obstruction` — only `(4)`, the strong-resolvent limit of the
  actual restricted operator. Everything else on the card is already unconditional.
- `suzuki-prime-normal-binomial-resolvent` — only `(2)`, the parameter derivative of the continuous
  functional calculus of `A_L^{-1/2}`. In the inverse coordinate this is a derivative of
  `x ↦ (1 − Lx)^{-1/2}` composed with a bounded operator, so it should follow from
  `CFC` continuity plus a difference quotient, not from the spectral theorem.
- `suzuki-gamma-weighted-tail-coercivity` — only the section-4 mollifier limit; `(3)`, `(10)`,
  `(11)`, `(17)` are now theorems.
- `suzuki-primitive-flux-nonnormal-graph-reduction` — only the Bochner-`L²` estimate `(15)`.
- `suzuki-complementary-primitive-flux-derivative-recovery` — only the weak Bochner derivative.
- `bv-copoisson-sharp-critical-half-weight-log-flux` — only Theorem D's Rademacher Gram.
- `suzuki-arithmetic-tangent-inverse-moment-holography` — the module
  `SuzukiArithmeticTangentHolography.lean` does not exist; its six target declarations are all
  derivative/identity statements about objects that already exist
  (`suzukiDonoghueTransform`, `herglotzOfCayley`, `suzukiUpperCayleyInv`), so this is assembly,
  not new analysis.

### D4. Held back on mathematical grounds

`suzuki-residual-overcrowding-entire-pair-closure` — `(19)` is false on the corpus's
order-isomorphism carrier model. It must first be restated for the analytic (Hermite–Biehler /
Herglotz) carrier class, which is itself a construction the corpus does not yet have.

### D5. `suzuki-arithmetic-tangent-inverse-moment-holography` — Theorem A route

None of the six target declarations exists yet; `suzukiDonoghueTransform` and
`suzukiFourierLivsic` are not defined anywhere either, so the module has to introduce them.
`suzukiUpperCayleyInv` and `suzukiHerglotz` do exist
(`RHTower/SuzukiFiniteApertureHermiteBiehler.lean`), and `herglotzOfCayley` with its derivative is
in `RHTower/SuzukiDonoghueHerglotzTransform.lean`.

Theorem A is self-contained real/complex analysis and does **not** need the operator:

```text
R ν z = ∫ (t - z)⁻¹ dν t                    Cauchy transform of a measure
m ν z = z + (z^2 + 1) * R ν z               Donoghue transform            (1)
q ν n = ∫ t^(-2n) dν t                      inverse even moments          (2)
```

- `(13)` `iteratedDeriv j (R ν) 0 = j ! * ∫ t^(-j-1) dν` — differentiation under the integral for a
  measure whose support is separated from `0`; the `j`-th `z`-derivative of `(t − z)⁻¹` is
  `j! (t − z)^(-j-1)`, dominated on a small disc by `j! δ^(-j-1)`.
- `(5)` `iteratedDeriv (2n+1) (m ν) 0 / (2n+1)! = q ν n + q ν (n+1)` — Leibniz on `(1 + z²) R`,
  only the zeroth and second derivatives of `1 + z²` survive at `0`; the `n = 0` case picks up
  `q 0 = 1` from the leading `z`.
- `(6)` the recursion, `(10)` the first two values — corollaries of `(5)`.
- `(7)` pushforward moments: `∫ y^n d(ν.map (t ↦ t^(-2))) = q ν n`, by
  `MeasureTheory.integral_map`; combined with the corpus's own
  `HTGeometry/CompactMomentDeterminacy.lean` (`ext_of_forall_integral_pow_eq`) this gives the
  determinacy claim with no new analysis.
- `(8)`–`(9)` dilation invariance of `κ n = q n / q 1 ^ n`: `q` scales by `c^(-2n)` under
  `t ↦ c t`, again by `integral_map`.
- `(12)` the free-clock values need `coth`/`tan` Taylor coefficients at `0`.

Theorem B `(15)`–`(24)` is the part that needs `A_a`; it should stay paper-level, and the card
already says so.

## E. The restricted Weil form is now an explicit Lean definition

`formal/GaloisForLFunctions/RHTower/SuzukiRestrictedWeilForm.lean` assembles Suzuki's kernel

`k = −½ Pf(1/|t|) − (2A+1) δ₀ − ∑_{n ≤ e^{2a}} Λ(n)/√n (δ_{log n} + δ_{−log n}) − r''`

into the form `Q(u, φ)` as a *definition*, with all four blocks explicit:

```text
cauchyFinitePart               the cutoff-free Hadamard finite part at an interior point
weilFinitePartBlock            −½ ∫ (finite part) φ
weilScalarBlock                −(2A+1) ⟪u, φ⟫
weilPrimeBlock                 −∑ Λ(n)/√n (⟪u(·+log n), φ⟫ + ⟪u(·−log n), φ⟫)
weilRegularBlock               −screwRegularForm u φ   (corpus's regular screw kernel)
restrictedWeilForm             their sum
IsRestrictedWeilRepresentative what a card means by `A_a u = w`
weilPrimeBlock_eq_jumpForms    the prime block is ∑ Λ(n)/√n J_{log n}(u,φ) − 2(∑ Λ(n)/√n)⟪u,φ⟫
weilPrimeBlock_jumpPart_nonneg its jump part is nonnegative against a truncation
cutoffFinitePart_eq_of_split   the cutoff-independence of the logarithmic coefficient
cauchyFinitePart_log_coefficient
```

**This removes the "unbounded operator `A_a` is not represented in Lean" blocker at the level the
cards actually use it.** No Friedrichs extension and no spectral theorem is involved: a card's
`A_a u = w` becomes `IsRestrictedWeilRepresentative a A s u w`, a statement about an explicit
integral pairing. The reusable inputs are `HTGeometry/HadamardFinitePart.lean` (the finite part),
`HTGeometry/AtomicJumpForm.lean` (the translation pairs and their positivity), and the corpus's own
`RHTower/SuzukiScrewCorrelationPairing.lean` / `SuzukiExplicitScrewRegularKernel.lean` (the regular
kernel and its shear identity).

Next steps on top of it, in order:

1. `cauchyFinitePart` for `u = exp`: compute the divided-difference integrals' endpoint behaviour
   and conclude Theorem A `(4)`–`(6)` of `suzuki-boundary-log-nonclock-nonflat-tangent` as a
   representative statement.
2. The two-port redundancy `(2)`–`(5)` of
   `suzuki-two-port-return-redundancy-and-interior-null-core`, which the card says is elementary
   once the form exists.
3. `(4)` of `suzuki-neumann-dominated-shift-cone-obstruction` — the strong-resolvent limit — in the
   resolvent coordinate, reusing `RHTower/SuzukiStrongResolventLimit.lean`.

## F. Session 2 additions

```text
RHTower/SuzukiGammaShiftKappa.lean              (3), (10), (11) of gamma-weighted-tail-coercivity
HTGeometry/MollifierPositionCommutator.lean     (17) of the same card
HTGeometry/HadamardFinitePart.lean              the cutoff-free Cauchy finite part split
RHTower/SuzukiRestrictedWeilForm.lean           the restricted Weil form as a definition
RHTower/SuzukiBoundaryLogEndpointBlowUp.lean    (5), (6) of boundary-log-nonclock-nonflat-tangent
```

Thirteen new modules total across both sessions, all umbrella-wired, built green, axiom-clean.

**The `A_a` blocker is dissolved at the level the cards use it.**  `restrictedWeilForm` is an
explicit definition and `IsRestrictedWeilRepresentative` replaces every `A_a u = w`.  The cards
that parked on "the actual restricted-Weil operator has not been constructed" can now be attacked
directly; what each still needs is its own computation, not the operator.
