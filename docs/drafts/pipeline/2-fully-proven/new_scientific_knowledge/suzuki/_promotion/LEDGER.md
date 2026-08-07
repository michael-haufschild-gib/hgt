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

```text
HTGeometry/TwoPortReturnRedundancy.lean   sections 1-3 of two-port-return-redundancy: the
                                          exterior evaluation condition is the support condition,
                                          the three-condition collapse, and the cutoff commutator
                                          identity for an idempotent
```

Remaining on `suzuki-two-port-return-redundancy-and-interior-null-core`: section 4's `H^s`
membership of a compactly supported bounded-variation function for `s < 1/2`.  That is a clean
self-contained target — the `‖u(·+h) − u‖₂² ≤ ‖u(·+h) − u‖₁ ‖u(·+h) − u‖_∞` interpolation the card
displays, plus the Fourier characterization of `H^s` — and it is worth building as reusable
`HTGeometry` infrastructure since the Carleman-barrier card needs the same profile.

## G. Immediate next step (identified, not yet done)

`SuzukiRestrictedWeilForm.lean` has one internal inconsistency to repair before
`suzuki-boundary-log-nonclock-nonflat-tangent` can be promoted:

- `weilPrimeBlock` uses the **whole-line** `pairing` (so that `jumpForm_eq_two_pairing_sub`
  applies), while `IsRestrictedWeilRepresentative` uses the **interval** integral
  `∫ x in (-a)..a`.

The fix is not to change either definition but to state the representative theorem on the honest
domain — test functions with `tsupport φ ⊆ Ioo (-a) a` — and add the bridge
`∫ x, f x * φ x = ∫ x in (-a)..a, f x * φ x` for such `φ`
(`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero` or
`intervalIntegral.integral_of_le` plus a support argument). Then

```text
IsRestrictedWeilRepresentative a A s k u (restrictedWeilRepresentative a A s k u)
```

follows from `integral_add`, `integral_sub`, `integral_const_mul` and `Finset.sum`, and Theorem A
`(4)` of `suzuki-boundary-log-nonclock-nonflat-tangent` is complete: `(5)` and `(6)` are already
theorems, and the remaining blocks are continuous hence bounded on the compact aperture.

A stale companion `suzuki-boundary-log-nonclock-nonflat-tangent-formalized.md` already sits in
`3-formalized/new_scientific_knowledge/suzuki/` from an earlier generation pass; the paper card is
still in stage 2. Regenerate the companion and `git mv` the card once `(4)` closes.

## H. The BV → `H^s` target (serves two cards)

`suzuki-two-port-return-redundancy-and-interior-null-core` section 4 and
`suzuki-carleman-flat-port-weighted-strip-barrier` both need: a compactly supported
bounded-variation function lies in `H^s(ℝ)` for every `0 < s < 1/2`. Route the card displays:

```text
‖u(·+h) − u‖₂² ≤ ‖u(·+h) − u‖₁ · ‖u(·+h) − u‖_∞ ≤ |h| · TV(u) · TV(u)
```

then the Gagliardo/Besov characterisation `∫ ‖u(·+h) − u‖₂² |h|^{-1-2s} dh < ∞`. mathlib has
`eVariationOn`/`BoundedVariationOn` but not the fractional Sobolev characterisation, so that
characterisation is the piece to build; the translation estimate itself is elementary.

```text
HTGeometry/SobolevWeightDecay.lean   the s < 1/2 threshold: a transform bounded and decaying at
                                     order one is square integrable against (1+ξ²)^s
```

Section H's remaining piece is now only the **bounded-variation input**: for compactly supported
`BV u`, `‖û(ξ)‖ ≤ ‖u‖₁` and `‖û(ξ)‖ ≤ TV(u)/(2π|ξ|)`.  The second is one Stieltjes integration by
parts. mathlib has `eVariationOn`/`BoundedVariationOn` and the Fourier transform, but not that
estimate; it is the single missing lemma for both
`suzuki-two-port-return-redundancy-and-interior-null-core` section 4 and
`suzuki-carleman-flat-port-weighted-strip-barrier`.

```text
HTGeometry/FourierDecayFromDerivative.lean   ‖f̂‖·2π|ξ| ≤ ‖f'‖₁ and ‖f̂‖ ≤ ‖f‖₁, hence Sobolev
                                             membership below one half from an integrable
                                             derivative
```

Section H is reduced to one step: extend `norm_fourier_mul_le_integral_norm_deriv` from
`Differentiable ℝ f` to bounded variation, by Stieltjes integration by parts.  The card's flat
profile is monotone with infinite one-sided derivative at the endpoint, so it needs the `BV` form;
everything downstream of that estimate is already proved.

```text
HTGeometry/GraphFluxStabilityEstimate.lean   (15), (16), (10) of primitive-flux-nonnormal-graph-
                                             reduction: the scalar closure of the flux system and
                                             the nonnormal numerical-range bound
```

`suzuki-primitive-flux-nonnormal-graph-reduction` is now reduced to `(13)` alone — the Fourier
resolvent estimate `σ‖Y‖₂ ≤ ‖(∂_L − σ)Y‖₂` for a weighted flux supported in `[L₀,∞)`.  That is a
Plancherel statement about one derivative, not about the source.

```text
HTGeometry/ShiftedDerivativeCoercivity.lean   d/dt ‖Y t‖² = 2 Re(Y'(t) conj Y(t)) — the cross-term
                                              identity behind (13)
```

Route for `(13)` now that the cross-term derivative is available, **without Plancherel**: for
compactly supported `C¹` `Y`,

```text
‖Y' − σY‖₂² = ‖Y'‖₂² − 2σ ∫ Re(Y' conj Y) + σ²‖Y‖₂²
            = ‖Y'‖₂² + σ²‖Y‖₂²          (the middle integral is ∫ d/dt‖Y‖², hence 0)
            ≥ σ²‖Y‖₂².
```

The vanishing is `intervalIntegral.integral_deriv_eq_sub'` over an interval containing the support,
with `‖Y‖²` zero at both endpoints. That closes `(13)` and with it
`suzuki-primitive-flux-nonnormal-graph-reduction`.

## I. Route for `suzuki-gamma-skew-frequency-flux-liouville` `(9)`--`(13)`

The frequency-current conservation is abstract Hilbert-space calculus, not Gamma analysis.  For
`f : ℝ → E` with

```text
HasDerivAt f (-(1/(2η)) • f η + (Complex.I/2) • S (f η)) η,   S self-adjoint,
```

the two ingredients are

1. `Re ⟪I • S v, v⟫ = 0` for self-adjoint `S` — because `⟪S v, v⟫` is real and `I` times a real
   number is purely imaginary.  This is the load-bearing cancellation `(11)`: the exact Gamma
   multiplier survives in full and transports phase only.
2. `d/dη ‖f η‖² = 2 Re ⟪f'(η), f(η)⟫` — the vector form of `hasDerivAt_normSq_comp`, already proved
   for `ℂ` in `HTGeometry/ShiftedDerivativeCoercivity.lean`; the general form needs
   `HasDerivAt.inner` plus `re` of the conjugate-symmetry identity.

Together they give `d/dη ‖f‖² = -‖f‖²/η`, hence `d/dη [η ‖f η‖²] = 0`, which is `(9)`; `(10)` is
its integral form and `(13)` is the same computation with the forcing retained.  The `L²` Liouville
conclusion `(14)` then follows from `(10)` because `|η|^{-1}` is not integrable at either end — an
elementary step once `(10)` is available.

Nothing in `(9)`--`(14)` needs the Bochner Fourier transform, the logarithmic jump multiplier, or
the completed seam carrier that the card's Lean-decision section lists; those are needed only for
the passage from `(1)` to `(8)`, which is the card's own separate claim.

### I.1 Both ingredients of `(9)` are now proved

`HTGeometry/SkewFrequencyCurrent.lean` carries

```text
inner_self_im_eq_zero_of_isSelfAdjoint            ⟪S v, v⟫ is real
re_inner_I_smul_isSelfAdjoint_eq_zero             (11): Re⟪i • S v, v⟫ = 0
re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero   the (c·i) form the equation produces
hasDerivAt_normSq_path                            d/dt ‖f t‖² = 2 Re⟪f'(t), f(t)⟫ in a complex
                                                  Hilbert space, via HasDerivAt.inner
```

What is left is the two-line assembly:

```text
d/dη ‖f‖² = 2 Re⟪-(1/(2η)) • f η, f η⟫ + 2 Re⟪(c i) • S(f η), f η⟫
          = -‖f η‖²/η + 0
d/dη [η ‖f η‖²] = ‖f η‖² + η · (-‖f η‖²/η) = 0.
```

The only fiddly step is `Re ⟪(r : ℝ) • x, y⟫ = r * Re ⟪x, y⟫` for a real scalar in a complex inner
product (`real_inner_smul_left` is for real spaces; the complex form needs `inner_smul_left` plus
`Complex.conj_ofReal`), and then `HasDerivAt.mul` for the product `η · ‖f η‖²`.  `(10)` is the
integral form; `(14)` follows because `|η|^{-1}` is not integrable at either end.

### I.2 State of the `(9)` assembly

Attempted and reverted twice; the tree is green and sorry-free.  The blocking step is small and
specific — write it down before retrying:

```text
hval : (⟪(↑r) • f η + (↑c * I) • S (f η), f η⟫_ℂ).re = r * ‖f η‖²      for r : ℝ
```

The rewrite chain `inner_add_left, Complex.add_re, hcross, add_zero, inner_smul_left,
Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hself` leaves a residual
goal that neither `ring` nor `simp` closes.  Diagnose it by stating `hval` as a standalone
`example` with the goal printed, rather than inside the larger proof where the error message is
truncated.  Likely cause: `hself` rewrites one occurrence of `(⟪f η, f η⟫).re` but the `.im`
factor introduced by `Complex.mul_re` is not syntactically `0 * _` after `Complex.ofReal_im`.

Everything else in the assembly is verified to work:

```text
hsq   := hasDerivAt_normSq_path h                     ✓
hid   := hasDerivAt_id η                              ✓
hprod := hid.mul hsq                                  ✓  (value 1*‖f‖² + η*(2*(r*‖f‖²)))
hzero : that value is 0, via `hcancel : η * (2 * (-(1/(2η)) * X)) = -X` by `field_simp`, then `ring`
```

So the whole theorem is one lemma away, and that lemma is a two-line complex-scalar computation.

### I.3 `(9)` is closed

`hasDerivAt_radialCurrent` proves `d/dη [η ‖f η‖²] = 0` for the skew frequency equation with an
arbitrary bounded self-adjoint block.  The blocking sub-goal of I.2 was resolved by isolating it as
`re_inner_real_smul_self` — a standalone lemma compiles where the same rewrite chain inside the
larger proof did not.  The other trap was `hasDerivAt_id η` producing `id η` rather than `η`,
fixed by `simp only [id_eq]`.

Left on `suzuki-gamma-skew-frequency-flux-liouville`: `(10)` (constancy on each half-line from the
vanishing derivative — `constant_of_has_deriv_right_zero` on `Ioi 0` and `Iio 0`) and `(14)` (the
`L²` Liouville conclusion, immediate from `(10)` since `|η|^{-1}` is not integrable at either end).

### I.4 `(10)` is closed; only `(14)` remains

`radialCurrent_const_Ioi` / `radialCurrent_const_Iio` give `|η| ‖f η‖²` constant on each half-line,
via `IsOpen.is_const_of_deriv_eq_zero` on `Ioi 0` and `Iio 0` (both open and preconnected).

`(14)` is then: set `C = 1 * ‖f 1‖²`; by `(10)`, `‖f η‖² = C/η` for `η > 0`; if `C > 0` this
contradicts `IntegrableOn (fun η => ‖f η‖²) (Ioi 0)` because `∫_1^∞ dη/η` diverges
(`integrableOn_Ioi_rpow_iff` at exponent `-1`).  Hence `C = 0` and `f` vanishes on the ray; the
negative ray is symmetric.  That closes `suzuki-gamma-skew-frequency-flux-liouville`, whose other
gates are all research.

## J. The `BV` Fourier decay, without `BV`

`suzuki-two-port-return-redundancy-and-interior-null-core` section 4 and
`suzuki-carleman-flat-port-weighted-strip-barrier` need order-one decay for a profile that is
**not** globally differentiable: `exp(-sqrt(log(1/r)))` has an infinite one-sided derivative at the
endpoint, so `norm_fourier_mul_le_integral_norm_deriv` (which assumes `Differentiable ℝ f`) does
not apply.

The classical translation trick avoids bounded variation altogether and needs only integrability.
mathlib supplies the key step, found this session:

```text
VectorFourier.fourierIntegral_comp_add_right
  fourier (f ∘ (· + v₀)) = fun w => e (L v₀ w) • fourier f w
```

Specialised to `ℝ` with `L v w = v * w` and `h = 1/(2ξ)`, the phase is
`fourierChar (h * ξ) = fourierChar (1/2) = exp(π i) = -1`, so

```text
fourier (fun x => f (x + 1/(2ξ))) ξ = - fourier f ξ
2 * fourier f ξ = fourier (fun x => f x - f (x + 1/(2ξ))) ξ
2 ‖fourier f ξ‖ ≤ ∫ ‖f x - f (x + 1/(2ξ))‖ dx.
```

Any `L¹` modulus-of-continuity bound `∫ ‖f(·+h) - f‖ ≤ |h| V` then gives `‖f̂(ξ)‖ ≤ V/(4|ξ|)`,
which is the second hypothesis of `memSobolevWeight_of_decay`.  For a monotone profile on a collar
`V` is its total variation, and no Stieltjes integration by parts is needed anywhere.

Remaining Lean work for this route: linearity of `fourier` across the subtraction (an
`integral_sub` with both translates integrable) and the `Circle` coercion for
`fourierChar (1/2) = -1`.

### J.1 Two concrete obstacles, both diagnosed

Probed against this toolchain; neither is conceptual.

1. **The phase value.**  `Real.fourierChar_apply` leaves
   `Complex.exp (2 * π * (1/2) * I) = -1`.  Close it with
   `rw [show (2:ℂ) * π * (1/2) = π by ring, Complex.exp_pi_mul_I]` — `norm_num` alone does not.
2. **The bilinear form.**  `Real.fourier` is
   `VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)`, so
   `fourierIntegral_comp_add_right` produces the phase at `⟪h, ξ⟫_ℝ`, not at `h * ξ`, and the
   `Circle` coercion elaborates through `Submonoid.unitSphere ℂ`.  State the translation lemma with
   `inner ℝ h ξ` and convert with `real_inner_comm`/`RCLike.inner_apply` rather than writing
   `h * ξ` and hoping `simp` bridges it; `simp only [Function.comp]` before the rewrite breaks the
   instance path and must be avoided.

With those two, section J's chain is mechanical.

### J.2 Probed to one remaining step

Worked in `formal/tmp/probeD.lean`, not in the tree, so nothing is half-built.  Three of the four
steps now compile:

```text
hval := congrFun (VectorFourier.fourierIntegral_comp_add_right (E := ℂ) Real.fourierChar
          (volume : Measure ℝ) (innerₗ ℝ) f (1/(2*ξ))) ξ                       ✓
hph  : ((Real.fourierChar ((1:ℝ)/2) : Circle) : ℂ) = -1                        ✓
       by  rw [Real.fourierChar_apply, show (2 * π * (1/2) : ℝ) = π by ring]
           exact Complex.exp_pi_mul_I
hgoal : 𝓕 (fun x => f (x + 1/(2*ξ))) ξ = 𝐞 (1/2) • 𝓕 f ξ  :=  hval             ✓ (defeq bridge
       from the VectorFourier form to the `Real.fourierIntegral` notation)
```

The one open step is evaluating the bilinear form:

```text
hin : ((innerₗ ℝ) (1/(2*ξ)) ξ : ℝ) = 1/2
```

`show (1/(2*ξ)) * ξ = 1/2` fails — `innerₗ ℝ a b` is **not** reducibly defeq to `a * b` on `ℝ`.
Unfold through `RCLike.inner_apply` (`⟪x,y⟫ = conj x * y`, with `star_trivial` on `ℝ`) rather than
by `show`; `innerₗ_apply` does not exist under that name in this toolchain.  Once `hin` is proved
the rest of the chain already type-checks as written above.

### J.3 The translation lemma is proved

`HTGeometry/FourierDecayFromDerivative.lean` now carries

```text
fourier_translate_half : 𝓕 (fun x => f (x + 1/(2ξ))) ξ = -𝓕 f ξ      for ξ ≠ 0
```

The `hin` step of J.2 is `simp only [innerₗ]` followed by `simp [innerₛₗ, mul_comm]` and
`field_simp` — the `RCLike.inner_apply` route was a dead end, and `innerₛₗ_apply` does not exist
under that name.

Remaining for the decay bound: linearity of `𝓕` across `f x - f (x + h)` — an `integral_sub` with
both translates integrable — giving

```text
2 * ‖𝓕 f ξ‖ ≤ ∫ ‖f x - f (x + 1/(2ξ))‖ dx,
```

and then any `L¹` modulus bound `∫ ‖f(·+h) - f‖ ≤ |h| V` yields `‖𝓕 f ξ‖ ≤ V/(4|ξ|)`, the second
hypothesis of `memSobolevWeight_of_decay`.  That completes section 4 of
`suzuki-two-port-return-redundancy-and-interior-null-core` and the profile membership needed by
`suzuki-carleman-flat-port-weighted-strip-barrier`.

### J.4 The decay bound is proved

```text
two_mul_norm_fourier_le_translationDistance
  2 * ‖𝓕 f ξ‖ ≤ ∫ ‖f x - f (x + 1/(2ξ))‖ dx      for integrable f and ξ ≠ 0
```

No differentiability, no bounded variation.  The chain used
`VectorFourier.fourierIntegral_add`, `fourierIntegral_const_smul` at `-1`, and
`norm_fourierIntegral_le_integral_norm`, bridged to the `𝓕` notation by `exact` (never `simpa` —
that normalises across the `VectorFourier`/`Real` coercion and blocks the defeq).

Section J is therefore reduced to one arithmetic step for each consuming card: supply an `L¹`
modulus bound `∫ ‖f(·+h) − f‖ ≤ |h| V` for the profile, then

```text
‖𝓕 f ξ‖ ≤ V / (4|ξ|)
```

feeds `memSobolevWeight_of_decay` with `K = V/4`, giving `H^s` membership for every `s < 1/2`.
For a monotone profile on a collar the modulus bound is its total variation.

### J.5 The one remaining step, and why it is the honest one

Everything in section J is proved except the `L¹` modulus bound itself:

```text
∫ ‖f (x + h) - f x‖ dx ≤ |h| * V
```

Two routes, and the cheap-looking one does not work:

* **Does not work.** `‖f(x+h) − f x‖ ≤ 2‖f‖_∞` with bounded support gives
  `∫ ≤ 2‖f‖_∞ · |supp|` — a *constant*, independent of `h`, so it yields no decay at all.  The
  `|h|`-linearity is the entire content.
* **Works.** For `f` absolutely continuous with `f' ∈ L¹`, `f(x+h) − f(x) = ∫_x^{x+h} f'`, hence
  `∫ ‖f(x+h) − f x‖ dx ≤ ∫∫ |f'| = |h| ‖f'‖₁` by Tonelli on the strip.  This needs FTC for the
  Lebesgue integral plus one Tonelli application, both in mathlib.

For the card's profile `exp(-sqrt(log(1/r)))` cut off on a collar: it is monotone and bounded there,
`C¹` on the open collar, and `‖f'‖₁` equals its total variation (a finite endpoint-to-collar
change plus the cutoff's variation), so the second route applies with `V = ‖f'‖₁` even though `f`
is not differentiable at the endpoint — the FTC route needs only absolute continuity, which the
monotone bounded profile has.

That single estimate closes section 4 of `suzuki-two-port-return-redundancy-and-interior-null-core`
and the profile membership of `suzuki-carleman-flat-port-weighted-strip-barrier`.

### J.6 The modulus estimate: everything but the Tonelli swap

Probed in `formal/tmp/probeK.lean` (scratch only — nothing entered the tree).  Use the form
`f(x+h) − f(x) = ∫_0^h f'(x+s) ds`, which avoids a triangular domain.  Verified to compile:

```text
hinv : ∀ s, (∫ x, ‖g (x + s)‖) = ∫ x, ‖g x‖        integral_add_right_eq_self      ✓
       then intervalIntegral.integral_const and simp give  h * ∫ ‖g‖                ✓
```

The single open step is the swap

```text
∫ x, ∫ s in (0:ℝ)..h, ‖g (x + s)‖  =  ∫ s in (0:ℝ)..h, ∫ x, ‖g (x + s)‖
```

i.e. `MeasureTheory.integral_integral_swap` on `ℝ × [0,h]`, whose hypothesis is joint integrability
of `(x,s) ↦ ‖g (x+s)‖` on the product.  That follows from `hg` by the measure-preserving shear
`(x,s) ↦ (x+s, s)`, which is where the work is.

With that swap, `∫ ‖f(x+h) − f x‖ dx ≤ h ‖f'‖₁` follows, and section J closes both consuming cards.

### J.7 Executable plan for the Tonelli swap

Do **not** reach for the `ENNReal`/`lintegral` form: converting back to Bochner integrals costs more
than supplying the integrability directly.  The Bochner route:

```text
μ := volume.restrict (Ioc 0 h)     ν := volume
F : ℝ → ℝ → ℝ  ,  F s x = ‖g (x + s)‖
```

`MeasureTheory.integrable_prod_iff` (note the *order*: the outer variable must be the one the
criterion quantifies over, so put `s` outside and `x` inside — the naive `x`-outside orientation
gives the wrong criterion and is the trap here) reduces joint integrability to two facts, both
immediate:

```text
∀ s, Integrable (fun x => ‖g (x + s)‖) volume      from (hg.comp_add_right s).norm
Integrable (fun s => ∫ x, ‖g (x + s)‖) μ           the inner integral is the constant ‖g‖₁ by
                                                   integral_add_right_eq_self, and a constant is
                                                   integrable on the finite-measure set Ioc 0 h
```

The only real work is `AEStronglyMeasurable` of the uncurry `(s, x) ↦ ‖g (x + s)‖` on the product:
obtain it from `hg.aestronglyMeasurable` composed with the continuous shear `(s, x) ↦ x + s`, using
that the shear is measure preserving on `ν` for each fixed `s`.

Then `MeasureTheory.integral_integral_swap` gives the swap, `intervalIntegral.integral_of_le`
converts to and from the interval form, and J.6's verified remainder finishes

```text
∫ ‖f (x + h) - f x‖ dx ≤ h * ‖f'‖₁ .
```

### J.8 J.7's plan verified; one measurability fact left

`formal/tmp/probeL.lean` confirms the whole of J.7 compiles **except** the measurability side
condition.  With that granted, `integrable_prod_iff` closes joint integrability exactly as planned:
`(hg.comp_add_right s).norm` for the inner factor, and the inner integral is the constant `‖g‖₁`
(`integral_add_right_eq_self` after `norm_norm`), integrable on `Ioc 0 h` by `integrableOn_const`.

The remaining fact is

```text
AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g (p.2 + p.1)‖)
  ((volume.restrict (Ioc 0 h)).prod volume)
```

Route: `AEStronglyMeasurable.comp_quasiMeasurePreserving` applied to `hg.aestronglyMeasurable.norm`
and the shear `p ↦ p.2 + p.1`.  There is **no** ready-made `QuasiMeasurePreserving` instance for
that shear — `exact?` finds nothing — so it has to be built from its definition: measurability of
the shear (continuous), plus

```text
Measure.map (fun p => p.2 + p.1) ((volume.restrict (Ioc 0 h)).prod volume) ≪ volume,
```

which holds because the pushforward is `h • volume`: for fixed `s` the map `x ↦ x + s` preserves
`volume` (`measurePreserving_add_right`), and Fubini integrates that over `s ∈ Ioc 0 h`.

Trying to dodge this by passing to a strongly measurable representative of `g` is circular — the
a.e. equality still has to be transported to the product measure, which is the same absolute
continuity.

### J.9 All ingredients present; the FTC step is verified

`HTGeometry/TranslationModulus.lean` now supplies the measure-theoretic half.  The analytic half is
verified too (`formal/tmp/probeQ.lean`):

```text
(∫ s in (0:ℝ)..h, deriv f (x + s)) = f (x + h) - f x
  by  intervalIntegral.integral_comp_add_left
      intervalIntegral.integral_eq_sub_of_hasDerivAt   ring_nf
```

Assembly, with every name now known:

```text
hptw : ‖f (x+h) - f x‖ ≤ ∫ s in (0:ℝ)..h, ‖deriv f (x+s)‖
       FTC above + intervalIntegral.norm_integral_le_integral_norm (needs 0 ≤ h)
swap : ∫ s in Ioc 0 h, ∫ x, ‖g (x+s)‖ = ∫ x, ∫ s in Ioc 0 h, ‖g (x+s)‖
       integral_integral_swap (integrable_uncurry_norm_shear g hg h)     -- orientation already
                                                                        -- matches: s outer
value: the left side is h * ‖g‖₁ by integral_integral_shear_eq
outer integrability of x ↦ ∫ s in Ioc 0 h, ‖g (x+s)‖ : Integrable.integral_prod_right'
conclude by integral_mono
```

Note the orientation of `integrable_uncurry_norm_shear` was chosen (J.7) so that
`integral_integral_swap` produces exactly the direction needed here — `s` outer, `x` inner — with no
re-proof.

### J.10 The modulus bound is proved — section J is complete

```text
integral_norm_translation_le
  (∫ x, ‖f (x + h) - f x‖) ≤ h * ∫ x, ‖deriv f x‖        for 0 ≤ h
```

in `HTGeometry/TranslationModulus.lean`.  No bounded variation, no Stieltjes integration by parts.

Name traps hit on the way, all fixed:

* `Integrable` unfolds to an `And`, so dot notation on a hypothesis of that type resolves to
  `And.*`.  Fully qualify: `MeasureTheory.Integrable.integral_prod_left`.
* It is `integral_prod_left` (integrate out the *second* variable, leaving the first), not
  `integral_prod_right`; and there is no primed `'` variant at `Integrable` level, only at
  `StronglyMeasurable` level.
* `Integrable.swap` needs an explicit type ascription to be usable, because its stated type is the
  unfolded conjunction.

**Section J now closes end to end**:

```text
integral_norm_translation_le            ∫‖f(·+h) - f‖ ≤ h‖f'‖₁
two_mul_norm_fourier_le_translationDistance   2‖𝓕 f ξ‖ ≤ ∫‖f - f(·+1/(2ξ))‖
  ⟹ ‖𝓕 f ξ‖ ≤ ‖f'‖₁ / (4|ξ|)
memSobolevWeight_of_decay               ⟹ H^s membership for every s < 1/2
```

so the profile membership needed by `suzuki-two-port-return-redundancy-and-interior-null-core` §4
and by `suzuki-carleman-flat-port-weighted-strip-barrier` is available.

### J.11 Honest scope check before promoting

`integral_norm_translation_le` assumes `Differentiable ℝ f` and `Continuous (deriv f)`.  The card's
profile

```text
u (a - r) = exp (-sqrt (log (1/r))),   cut off on a collar
```

is **not** differentiable at `x = a`: the difference quotient is `-exp(-sqrt(log(1/r)))/r`, which is
`-e^{L - sqrt L}` at `r = e^{-L}` and diverges.  So section J as proved covers `C¹` profiles, not
this one, and `suzuki-two-port-return-redundancy-and-interior-null-core` must **not** be promoted on
it.

Closing the mismatch needs the estimate for *absolutely continuous* `f`, i.e. replacing the FTC step

```text
intervalIntegral.integral_eq_sub_of_hasDerivAt   (needs HasDerivAt at every point)
```

by its a.e. form for an `AC` function.  In mathlib that is
`MeasureTheory.integral_eq_sub_of_hasDerivAt_of_le` (derivative a.e. on the interior, plus
continuity on the closed interval and integrability of the derivative) — exactly the hypotheses the
monotone bounded profile satisfies.  Everything downstream of the FTC step is unchanged, since
`integral_integral_shear_eq` and the swap never touch differentiability.
