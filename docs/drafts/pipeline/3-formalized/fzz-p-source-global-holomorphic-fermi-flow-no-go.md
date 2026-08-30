# FZZ-P source-global holomorphic Fermi-flow conjecture

- **ID:** FZZ-P-SOURCE-GLOBAL-HOLO-FERMI-FLOW
- **Stage:** 3-formalized
- **Type:** NO-GO THEOREM WITH POSITIVE SURVIVOR
- **Source:** `rh-current-frontier-map.md` · FZZ-P `ORIENT DYN`; shared PW-B Ward producer
- **Statement:** Literal source-changing FZZ dynamics is generated on the open critical strip by a holomorphic vector field whose horizontal velocity is the exact negative reflected-Fermi information force.

## Goal

Close the surviving shared source-dynamical chain

`literal FZZ Mellin analyticity → source-global holomorphic spectral generator → exact reflected-Fermi inward velocity on every Xi copy → FZZ/Deninger/PW Ward equilibrium → RH`.

This is not a bound optimization. It asks whether the corpus's already exact nonlinear information force is an actual analytic spectral transport law rather than only an ambient source-coordinate orientation. If false, kill the whole source-global holomorphic implementation class and identify the minimal non-holomorphic successor.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, physical statement frozen before proof work, route passport and falsifiers recorded
- [x] 1 → 2  fully-proven: complete paper proof or complete no-go with strongest positive survivor
- [x] 2 → 3  formalized: exact dependency-closed theorem in Lean, targeted build and axioms audit PASS; project-wide lint was run and is red only on unrelated concurrently owned unwired modules
- [ ] 3 → 4  publication-ready: standalone paper and external priority review

## Frozen conjecture and RH proof chain

Let `S = {z : ℂ | 0 < Re z < 1}` and let

`V(σ) = -fzzCigarParityReflectedFermiInformationForce(σ)`.

**Conjecture FZZ-P-D1 `[FROZEN]`.** There is a holomorphic vector field `G : S → ℂ` governing a source-changing family of literal FZZ Mellin amplitudes such that

`Re G(z) = V(Re z)`

for every `z ∈ S`. At every simple moving FZZ divisor point, the source variation supplies the complementary vertical velocity and the induced horizontal zero velocity is `V`.

If the literal dynamics additionally preserves its physical divisor modes at equilibrium, then `G` is stationary on every Xi copy exactly when `V(Re ρ)=0`. Corpus transmutation identifies this with vanishing Deninger/PW Ward charge, and universal stationarity is already equivalent to RH.

The conjecture is believed because the literal FZZ Mellin amplitude is holomorphic in spectral parameter, the fixed-source divisor-flow route is already impossible, and source deformation is the unique continuous survivor. It is not tailored to current proof machinery.

## Public sentence

The analytic FZZ source itself should move its spectral modes along the exact information-gradient field, instead of merely assigning an inward arrow to otherwise immobile zeros.

## Universal-shadow map

| Corpus/literature item | Proposed shadow of FZZ-P-D1 |
|---|---|
| Exact Fermi force has unique wall equilibrium and strict inward orientation | Horizontal component of `G` |
| Force is positive multiplier times Deninger Ward displacement | Same generator in arithmetic gauge |
| PW recoil imbalance is positive multiplier times Fermi force | Same generator in tunnelling-response gauge |
| Same-source continuous divisor flow is constant | Necessity of source-changing amplitude family |
| Regular reflection interfaces and fixed-source local probes are terminal | Boundary shadows of one global analytic generator |
| FZZ duality identifies analytic descriptions of same theory | Physical motivation for source-global holomorphic covariance |

**Ontological reversal.** Fermi force is conjectured to be a component of one source-deforming holomorphic vector field, not a scalar diagnostic attached after divisor selection.

**Risky consequence.** Every ordinate with the same real part must receive identical horizontal velocity while retaining holomorphic dependence on the full complex spectral coordinate.

## Hostile attack plan

1. Prove the missing rigidity theorem: if `G` is holomorphic on `S` and `Re G(z)` depends only on `Re z`, then this horizontal profile is affine. This is stronger than the corpus theorem for `G` itself depending only on `Re z`.
2. Determine whether exact Fermi velocity is affine without numerical evaluation. Use the hard Mellin edge at `σ ↓ 0`: the normalizer has at least reciprocal growth, convexity forces its logarithmic derivative `fermiLogMean` below every floor, and positivity of variance transfers this to the reflected force.
3. If velocity is unbounded below on `(0,1/2)`, it cannot be affine on `(0,1)`, falsifying FZZ-P-D1.
4. Extract strongest survivor: any exact source-global realization must violate harmonic/holomorphic horizontal stratification. Candidate successors are an explicitly Wirtinger/antiholomorphic term, a singular boundary-domain generator, divisor-indexed feedback, or source data whose horizontal velocity depends on the ordinate.

## Conjecturing loop

- **A — fixed-source flow:** falsified and Lean-closed by discrete divisor rigidity.
- **B — source-changing holomorphic flow (FZZ-P-D1):** frozen here; current hostile target.
- **C — if B fails:** classify the maximal regularity boundary, not merely negate B. Test harmonic horizontal components, then isolate the first admissible non-holomorphic primitive capable of producing exact Fermi velocity.
- **D — if B survives:** construct moving amplitude family and prove zero-velocity equation, then weld universal stationarity to the existing RH equivalence.

## Closest parent theories and novelty residue

- Cauchy--Riemann rigidity for horizontally stratified harmonic functions is classical; it is not the novelty claim.
- Berkson--Porta theory classifies holomorphic semigroup generators but does not identify the project-specific Fermi force or FZZ/PW/Deninger Ward chain.
- Standard Fermi--Dirac/Mellin asymptotics explain a hard endpoint but do not classify the exact reflected information velocity as an obstruction to source-global holomorphic spectral transport.
- FZZ duality literature proves equivalence of descriptions, not an RH-selecting nonlinear zero-flow law.

Exact unoccupied residue: route-level compatibility or incompatibility between the literal Fermi information force and a source-global holomorphic spectral generator, together with the sharp successor architecture forced by the answer.

## Falsifiers

- A holomorphic `G` with the stated real part.
- Proof that exact Fermi velocity is affine on `(0,1)`.
- Evidence that physical source evolution need only be holomorphic along the discrete divisor rather than on the source-global strip; this would falsify the source-global premise but leave a divisor-indexed successor.

## Literature audit seed (through 2026-08-30)

- Hikida--Schomerus, arXiv:0805.3931: proof of FZZ duality; no spectral gradient-flow generator.
- Pakman, arXiv:hep-th/0606067: classical cigar scattering does not uniquely determine the quantum reflection coefficient without added input.
- Berkson--Porta semigroup-generator theory and later approximation work: general holomorphic dynamics, no Fermi/FZZ/RH identification.
- DLMF Gamma/Mellin references: classical hard-edge pole structure only.
- D. H. J. Polymath, arXiv:1904.12438: zeros move under a changing entire function `H_t`; supports source deformation but supplies no FZZ generator.

## Log

- 2026-08-30 — corpus and current primary-literature absorption completed; physical conjecture frozen before paper proof.
- 2026-08-30 — FZZ-P-D1 falsified without numerical input; full hard-edge and holomorphic-rigidity proof closed on paper.
- 2026-08-30 — exact no-go and affine-profile survivor formalized in Lean; module wired into `RHTower` umbrella.

## Complete no-go proof

Write

`Z(σ) = ∫₀∞ t^(σ-1)/(exp t + 1) dt`, `L(σ) = log Z(σ)`,

`m(σ) = L'(σ)`, and `q(σ) = m'(σ) > 0`. The corpus identifies `m` and `q` with the Fermi log-mean and log-variance. The exact reflected information force is

`F(σ) = 2(m(σ)-m(1-σ)) + (2σ-1)(q(σ)+q(1-σ))`,

and the proposed horizontal velocity is `V = -F`.

### 1. Hard-edge blow-up

For `0 < σ` and `0 < t ≤ 1`,

`1/(exp t + 1) ≥ 1/(exp 1 + 1)`.

Therefore

`Z(σ) ≥ (exp 1 + 1)⁻¹ ∫₀¹ t^(σ-1) dt = (exp 1 + 1)⁻¹/σ`.

Thus `Z(σ) → +∞` and `L(σ) → +∞` as `σ ↓ 0`.

Fix any real floor `B`. For small `σ`, choose the mean-value point `c ∈ (σ, 1/2)` satisfying

`m(c) = (L(1/2)-L(σ))/(1/2-σ)`.

The right side falls below `B`, while strict convexity of `L` gives `m(σ) < m(c)`. Hence

`m(σ) → -∞` as `σ ↓ 0`.

For `0 < σ < 1/2`, strict increase of `m` gives `m(1-σ) > m(1/2)`, while both variances are positive and `2σ-1 < 0`. Consequently

`F(σ) ≤ 2(m(σ)-m(1-σ)) → -∞`,

so

`V(σ) → +∞` as `σ ↓ 0`.

### 2. Holomorphic horizontal-profile rigidity

Assume `G` is holomorphic on `S = {0 < Re z < 1}` and `Re G(z) = v(Re z)`. For each real vertical shift `t`, set

`E_t(z) = exp(G(z+it)-G(z))`.

Vertical translation preserves `S`. Because the real part of `G` depends only on `Re z`, `|E_t| = 1` throughout `S`. The strip is open and connected, so the strong maximum-modulus theorem makes `E_t` constant. Differentiating and using nonvanishing of the exponential gives

`G'(z+it) = G'(z)`.

Thus `G'` depends only on `Re z`. The corpus's open-critical-strip analytic real-profile rigidity theorem then makes `G'` constant. Restriction to the real axis and the mean-value theorem yield real constants `a,b` with

`v(x) = ax+b` for every `0 < x < 1`.

### 3. Contradiction and route kill

Apply the rigidity result to `v = V`. Every affine profile on `(0,1)` is bounded above there; explicitly,

`ax+b ≤ |a|+|b|`.

But Step 1 proves `V(σ) → +∞` as `σ ↓ 0`. Contradiction. Therefore no source-global holomorphic vector field on the critical strip can have the exact reflected-Fermi horizontal velocity as a horizontal-stratified real part. FZZ-P-D1 is false.

This kills the shared FZZ-P/PW-B implementation class

`source-global holomorphic generator + ordinate-independent exact Fermi horizontal velocity`.

It does not kill source deformation itself or either full route.

## Strongest positive survivor

**Sharp regularity boundary.** Every holomorphic critical-strip generator with ordinate-independent horizontal velocity has affine horizontal velocity. Since the exact Fermi velocity has a hard-edge divergence, any exact FZZ/PW realization must cross at least one of these boundaries:

1. horizontal velocity depends on ordinate;
2. generator contains an explicitly antiholomorphic/Wirtinger component;
3. generator is defined only on a singular boundary domain, not the whole open strip;
4. transport is divisor-indexed or source-feedback dependent rather than one source-global vector field.

The survivor is dependency-closed and stronger than a bare negation: it classifies the maximal holomorphic, horizontally stratified transport class and isolates the first admissible successor architectures.

## Novelty and contamination audit

- Classical input: maximum modulus, mean-value theorem, elementary Mellin hard-edge estimate.
- Corpus input: exact Fermi normalizer, log-mean/variance identities, strict log-mean monotonicity, exact reflected information force, existing analytic real-profile rigidity for a complex-valued function.
- New residue: combining the harder real-part-only holomorphic rigidity with the exact nonlinear Fermi hard-edge law to exclude the source-global FZZ/PW spectral generator class and classify its survivor boundary.
- No computation, zero census, or numerical bound is used.

## Lean artifact

Module: `GaloisForLFunctions.RHTower.FZZCigarParitySourceGlobalHolomorphicFermiFlowNoGo`.

Key unconditional theorems:

- `fermiMellinNormalizer_reciprocal_lower` — explicit reciprocal hard-edge lower bound.
- `tendsto_fermiLogMean_nhdsGT_zero_atBot` — Fermi log-mean tends to `-∞` at the hard edge.
- `tendsto_fzzCigarParityReflectedFermiInformationVelocity_nhdsGT_zero_atTop` — exact velocity tends to `+∞`.
- `analytic_horizontalRealPart_profile_affine` — every holomorphic horizontally stratified real-part profile is affine.
- `not_exists_analytic_horizontalRealPart_eq_fzzCigarParityReflectedFermiInformationVelocity` — source-global holomorphic exact-Fermi generator no-go.

Audit:

- `lake env lean GaloisForLFunctions/RHTower/FZZCigarParitySourceGlobalHolomorphicFermiFlowNoGo.lean` — PASS.
- `lake build GaloisForLFunctions.RHTower.FZZCigarParitySourceGlobalHolomorphicFermiFlowNoGo` — PASS.
- `#print axioms` on all five key theorems — only `propext`, `Classical.choice`, `Quot.sound`.
- Local banned-token scan — PASS.
- `scripts/formal_tools.py lint` — executed; project-wide result remains red on unrelated concurrently owned `RiemannGaussian` and `RatFuncLaurentDifferential` umbrella reachability. No error names this module.
