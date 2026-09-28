# DifferentialGeometry geometry/topology: RH mechanism audit

- **Date:** 2026-09-28
- **Stage:** 0-backlog; source audit complete, proposed integrations unimplemented.
- **Type:** Research assessment, not a new RH theorem or independently new proof route.
- **Source:** qinz1yang/differential-geometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`.
- **Question:** Which additional geometric/topological mechanisms can reach an actual missing RH premise?

## Work and evidence

- [x] Consult current RH frontier, relevant STATUS constraints, previous Hodge/Markov and topological completion attempts.
- [x] Search local Lean and research corpus before proposing imports. Deep search `Weil ground Bochner curvature heat semigroup Hodge --any --mode deep --budget-seconds 60 --no-refresh` returned partial results over 61,082 inventoried/indexed files; most compiler metadata pending/stale. Inspect source statements rather than treating suggested ingredient sets as proofs. One suggested Hodge certificate already assumes purity and cannot produce it.
- [x] Inspect upstream Bochner/Weitzenböck endpoints, tensor first-contact hypotheses, Perelman square derivative, harmonic-map lower semicontinuity, conformal/regularized Gauss–Bonnet, de Rham complex and low-degree Hurewicz signatures.
- [x] Complete the direct translation-Bochner and constrained-Weil tests below; preserve the remaining arithmetic term explicitly.
- [x] Inspect smooth Poisson existence and its regularity producer; distinguish it from local disk Poisson kernels and abstract Green inverses.
- [x] Record final ranking and applicability boundaries; correct the two overstatements in the prior note.

No upstream endpoint in this audit has been compiled against the local toolchain. Four local scratch declarations combining existing results were checked as recorded below; this audit does not claim a fresh full-corpus build. Upstream uses Lean/mathlib 4.33.1; the local project uses 4.32.2, so imports require a dependency and compatibility audit.

## 1. Exact Bochner identities for the actual Weil operator

Upstream has a substantive intrinsic identity, not merely a Bochner-assumption wrapper:
`Geometry/Curvature/Bochner/WeitzenbockIdentity.lean:1426`,
`bochner_pointwise_abstract_of_smooth`. It constructs both the Leibniz and curvature-commutator
inputs. The mixed-tensor integration-by-parts identity is
`Analysis/Elliptic/ConnectionLaplacian/Weitzenbock/IntegratedMixedTensor.lean:104`,
`weitzenbock_integrated_covGrad_l2_normSq_rs`.

Potential use: derive an exact sum-of-squares plus curvature/boundary identity for the
**literal prime–Gamma operator on the pole-constrained domain**. This is a proposed nonlocal
adaptation; the upstream theorem is about smooth Riemannian differential operators and cannot
be applied to prime translations without a bridge.

The local source identity already retains genuine prime-edge squares:
`CCMPrimePoleSchurDefect.ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential`.
On the pole-constrained domain it combines with the exact source decomposition to give

`Q_a(u) = ||u||²_form + cΓ ||Ju||² + E_a(Ju) - R_a(Ju)`,

where `E_a` is the actual nonnegative prime-edge energy, `R_a` the actual spatial row potential,
and `cΓ = 2 * gammaHardyPhaseRate 0 - 1`. No prime coefficient is replaced by a majorant.

The direct hard test is whether the full arithmetic identity, at a hypothetical first zero
ground state, forces `E_a(Ju)=0`. If it did, the proved
`CCMPrimePoleSchurKernel.eq_zero_of_ccmSchurEnergy_zero_of_polar` would force `u=0`, contradicting
normalization (once `2a >= log 2 + log 3`; smaller apertures need their own established bounds).
At present `Q_a(u)=0` gives only
`E_a(Ju) = R_a(Ju) - ||u||²_form - cΓ ||Ju||²`. Neither side is proved zero.
This remaining comparison, not the generic Bochner theorem, carries the RH difficulty.

The direct translation test is exact. For a finite constant-rate jump generator
`Lf(x) = Σ_h r_h (f(x+h)-f(x))`, `r_h >= 0`, commuting translations give

`Γ₂(f)(x) = (1/4) Σ_{h,k} r_h r_k |Δ_h Δ_k f(x)|² >= 0`.

For real functions, the per-pair algebra was checked in Lean:

`((d-c)²-(b-a)²)/4 - (b-a)(d-b-c+a)/2 = (d-b-c+a)²/4`.

This positivity survives arbitrary nonnegative changes of the jump weights. It therefore
cannot by itself distinguish the exact zeta coefficients from perturbed arithmetic sources.
The infinite archimedean jump measure, aperture compression, variable Doob rates, source
potential and pole constraints are **not** included in that finite constant-rate calculation.
An adaptation must retain their exact contributions; using the flat identity alone fails.

Generic compactness is already insufficiently quantitative:
`CCMPrimePoleSchurGammaInterpolation.exists_ccmPolarConstrained_gamma_schur_interpolation`
provides `||Ju||² <= ε||u||²_form + C(a,ε)E_a(Ju)` at each aperture, with no usable cofinal
rate. An exact identity could still matter; another unspecified compactness constant would not.

## 2. Geometric charge through singular completion

Upstream useful components:

- `Geometry/Curvature/ConformalGaussBonnet.lean:23`, `gaussBonnet_conformalDisk`:
  intrinsic curvature-area plus boundary-turning identity.
- `Geometry/Curvature/RegularizedGaussBonnet.lean:21`, `gaussBonnet_regularizedDisk_trace`:
  retains the trace boundary term under regularization of a conformal disk map. It has explicit
  conformality, trace and boundary-derivative hypotheses; those require producers in an application.
- `Geometry/HarmonicMap/WeakLowerSemicontinuity.lean:21`,
  `exists_pullback_dirichlet_integral_le_liminf`: lower semicontinuity under supplied weak
  gradient convergence and almost-everywhere map convergence into a compact smooth target.
  This is not an automatic bubble-tree or integer-charge compactness theorem.

Potential use: a concrete geometric realization of the existing TG completion problem,
retaining both bulk action and boundary framing. Existing local theory already knows the
integer winding and its RH consequence. The missing statement remains an arithmetic identity
`E_base = E_residual + integer charge`, with `E_residual >= 0`, or another source-derived
charge bound below one. Ordinary homotopy invariance assumes away a singular passage; weak
lower semicontinuity allows lost energy and does not identify or bound a topological defect.

An explicit diagnostic is the classical regularized divisor density, for holomorphic F,

`A_ε(F;D) = (1/π) ∫_D ε² |F'|² / (|F|² + ε²)² dA`,  `ε > 0`.

For `F(z)=z^m`, `m>=1`, on the radius-R disk, polar integration gives
`A_ε = m R^(2m)/(R^(2m)+ε²) -> m` as `ε -> 0+`. Smooth nonnegative densities can therefore
concentrate an entire integer at a zero. This classical calculation is a diagnostic, not a
new RH receiver to add to the corpus. With `F=ξ`, a sub-unit bound must come from the exact
arithmetic source; smoothness, positivity and Gauss–Bonnet alone cannot supply it.

Paper check: the radial integral is
`∫₀ᴿ 2 ε² m² r^(2m-1)/(r^(2m)+ε²)² dr`; its primitive is
`m r^(2m)/(r^(2m)+ε²)`, with value zero at the origin. No general divisor-measure
convergence theorem was formalized in this audit. In a conformal metric with exponent
`f_ε = (1/2)log(|F|²+ε²)`, this positive divisor density corresponds to `Δf_ε/(2π)`;
the Gaussian curvature-area density has the opposite sign. Boundary terms cannot be dropped.

The previously failed holomorphic Gaussian-passage argument remains failed (frontier TG,
`AnchoredPhasePassageRigidity`, KR-R1). A non-holomorphic regularization changes which objects
are studied but does not by itself solve the source comparison.

## 3. Concrete differential forms and higher-period topology

Upstream `Tensor/Exterior/Cochain.lean` constructs a genuine de Rham cochain complex from
the proved `exteriorDerivative_sq`; `pullbackCochainMap` and induced cohomology maps are
functorial. `Topology/Homology/HurewiczLowDegrees.lean` proves the degree-two Hurewicz
isomorphism for simply connected spaces, and degree three additionally under vanishing π₂,
with a chosen sphere homology generator.

These can support concrete realizations of local nomological form/period structures,
including S² × S³ examples and geometric differential-character inputs. They do not constitute
an arithmetic Hodge theorem. Need adapters between the actual form calculus, integration,
singular chains and the local `PeriodGeometry` fields; Hurewicz does not give a positive
pairing or make Frobenius compatible with a Hodge star.

The inspected `Geometry/Hodge/Codifferential.lean` defines minus divergence on vector
fields and identifies the scalar form Laplacian with minus the geometric Laplacian.
It is not a full Hodge decomposition or a theorem giving harmonic representatives in every
degree. Do not infer an arithmetic Hodge theorem from that directory name.

## 4. Concrete elliptic solvability

`Analysis/Spectral/Scalar/PoissonExistence.lean:512`,
`existsUnique_meanZero_smooth_poisson`, proves existence and uniqueness of a smooth
mean-zero solution `Δ_g f = q` for a smooth mean-zero source on a compact connected
boundaryless smooth Riemannian manifold of positive finite dimension. The endpoint uses
`smoothRepresentativeOfLaplacianImage_holds` at line 481 to discharge its analytic
regularity premise. It does not leave smooth representability as an assumed certificate.

This supplies concrete normalized Green solutions in that geometric setting. Linearity
and the two inverse identities on the mean-zero smooth subspace follow from uniqueness,
after constructing the appropriate local linear maps and checking the sign convention.
Local `ClockPropagatorSelfCalibration` and `ClockBackreactionTwoMass` instead accept
abstract Green inverse identities; these upstream results could provide a geometric
instance where their operator/domain hypotheses match. No match to their mass-shifted
operators or to the actual arithmetic source is asserted here. The compact-resolvent
construction provides separate candidates for shifted operators.

The additional local research query `"mean zero" Poisson --any --mode lexical --no-refresh`
returned mainly disk/Euler Poisson results; it supplied no ready adapter for this endpoint.
This is useful infrastructure with a concrete producer, not an RH spectral realization.

## Lower-priority or inapplicable shortcuts

- **Perelman entropy:** `Entropy/W/Variation/Monotonicity.w_rev_square` at line 281 really
  gives the integral square of `Ric + Hess f - g/(2τ)`, but assumes an actual Ricci-flow solution
  and a positive conjugate-heat solution on a compact manifold. No such source-preserving
  geometric realization of the prime–Gamma current is supplied. An arbitrarily chosen
  dissipative flow would not prove the arithmetic sign.
- **Hamilton first contact:** `MaximumPrinciple/Tensor/FirstNull/Signs.scalarSigns_of_eval`
  needs a parabolic inequality and a null-eigenvector reaction condition. The latter is the
  nontrivial preservation condition. Our aperture ground energy is strictly decreasing;
  calling aperture a time variable supplies neither condition.
- **Riemannian spectral theory:** compact resolvent and eigenbasis infrastructure may remove
  analytic boilerplate in geometric models, but no finite-dimensional compact manifold has
  been identified with the actual infinite-rank arithmetic cohomology. Self-adjointness of
  an unrelated operator does not identify its spectrum with Xi zeros.
- **Poincaré:** useful for three-manifold classification, not a source positivity law or a
  proof that arithmetic cohomology has the required geometry.

## Prior-note scope corrections applied

`hf-positive-hodge-attack/krein-producer-loops.md`, L62, derives
`λ₂(Q₀) <= ε_a` and `λ₂(Q₀) >= λ₁(Q_full)`, then states the chain gap is
`|λ₀| + O(ε_a)`. Those two inequalities alone provide no unconditional lower bound near zero
for `λ₂(Q₀)`. The supported conclusion is the one-sided upper bound
`gap <= |λ₀| + ε_a`; the desired `gap >= |λ₀|` remains open. This excludes a fixed positive
slack above the target, not all possible exact curvature identities.

L60 also calls `w(t)=exp(-t/4)/(1-exp(-t))` log-concave for `t>0`.
In fact `(log w)'' = exp(-t)/(1-exp(-t))² > 0`, so it is strictly log-convex.
The proposed log-concavity shortcut still fails. Both corrections were applied to the
prior note, preserving its other content. They narrow claims about failed arguments;
they are not evidence for RH.

## Ranking and verification

1. **RH research priority:** derive the full arithmetic Bochner/commutator identity and test
   its remaining sign at a hypothetical normalized zero ground state. The exact row bound
   at such a state would suffice, but remains unproved; a uniform bound over all vectors is
   neither claimed nor required by this proposed first-contact argument.
2. **Second RH research candidate:** identify the exact arithmetic bulk/boundary action
   with a geometric charge under singular completion. The monomial test shows why ordinary
   smooth positivity and weak compactness cannot close this step.
3. **Infrastructure priority:** concrete de Rham/period adapters and normalized compact
   Poisson solvers. These have clearer reusable mathematical outputs; no RH premise was
   discharged by this audit.

`lake --old env lean /tmp/hgt-dg-rh-mechanism-check.lean` passed on the local toolchain:
`translation_bochner_pair`, `constrained_source_exact`, `zero_source_energy`, and
`source_zero_impossible_of_exact_row_bound`. The last declaration explicitly assumes the
missing row bound and uses the existing edge-kernel rigidity; it is a dependency test,
not a new theorem for the main corpus. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for all four. No scratch declarations were added
to the repository's Lean modules.

The formal lint gate was run and failed on existing/concurrent modules unreachable from
the RHTower/HTGeometry umbrellas, including `CCMApertureChainProfile` and
`GammaHorizontalRatio`. This audit changed no Lean modules or umbrella imports and does
not claim a clean global gate. These unrelated files were left untouched.
