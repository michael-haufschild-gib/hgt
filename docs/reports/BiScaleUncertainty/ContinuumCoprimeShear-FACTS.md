# Continuum coprime shear: knowledge ledger

## Scope and certified contribution count

Target: 100 substantive mathematical packages in continuum coprime shear and
multiplicative/additive regularity. Certified packages: **16 / 100**. Supporting algebra,
coordinate changes, and restatements do not separately increment this count.

**Package 1 — continuum trace, affine commutator, and finite nodal-edge control.**
The two Lean leaves below certify one connected mathematical contribution, not
34 separate contributions. It broadens Pillar VII to actual continuum endpoints,
identifies the correct Dirichlet weight and exact interpolation defect, and removes
the physical-origin extension restriction. It does not establish external novelty
of the underlying interval energy principle.

## Exact continuum trace law — paper proof

Let q be any continuous real function, F(t)=∫₀ᵗq(s)ds, and f(x)=F(eˣ).
These are actual constructed functions, with F'=q and f'(x)=eˣq(eˣ).
Write E(a,b)=∫ₐᵇq², allowing oriented intervals. For L=b−a and Δ=F(b)−F(a),

    ∫ₐᵇ(Lq−Δ)² = L² E(a,b) − LΔ².                         (1)

Proof: continuity makes all integrands integrable on compact intervals. Additivity
of oriented integrals gives ∫ₐᵇq=Δ. Expand the square and integrate; ∫ₐᵇ1=L.
If L>0, nonnegativity gives Δ²≤LE(a,b). If L=0 both sides vanish.
For L>0 the normalized form is

    E(a,b)=Δ²/L + ∫ₐᵇ(q−Δ/L)².                           (2)

Equality holds exactly when q is constant on [a,b]: a continuous nonnegative
integrand with integral zero vanishes throughout that interval. Thus the least
energy extension of two trace values is affine in the physical coordinate t,
and exponential-affine in x=log t.

Change variables t=eˣ and use the displayed derivative to obtain

    ∫ᵤᵛ e^(−x) f'(x)² dx = E(eᵘ,eᵛ).                    (3)

This is the additive Dirichlet form in logarithmic coordinates. For 0<a<b its
endpoint resistance is b−a, not log(b/a).

For any real a, k≥0 and integer N≥0, define
Δₙ=F(a+k(n+1))−F(a+kn). Add (1) over the N adjacent cells:

    k² E(a,a+kN) − k Σₙ<N Δₙ²
      = Σₙ<N ∫_{a+kn}^{a+k(n+1)} (kq(t)−Δₙ)² dt ≥0.     (4)

For k>0, ΣΔₙ²≤k E(a,a+kN); for k=0 this is trivial. The coefficient k is
sharp: q≡1, N>0 gives equality. Taking a>0 and applying (3) gives the requested
continuum version of the dilated additive-step estimate. For k=1, (4) is the
exact discrete trace energy plus interpolation defect. Constant q on each cell
is the equality condition; globally continuous q forces these constants to agree
on adjacent cells. Piecewise affine H1 extensions allow independent cell slopes.

## Shear and operator boundary

σ_b(x)=log(eˣ+b), b≥0. Then e^(σ_b(x))=eˣ+b,
σ_b∘σ_c=σ_(b+c), and

    σ_(eˢb)(x+s)=s+σ_b(x).

These follow by exponentiating and using exp injectivity. σ_1(log n)=log(n+1)
for n>0. σ_b has range (log b,∞) for b>0: it is not onto R. Thus positive
translation on t>0 gives a semigroup, not a globally invertible unitary group.
Any ax+b uncertainty claim must specify its representation and operator domains.

## Coprime and graph boundaries

- Divisor support constrains discrete traces. A continuous function supported on
  the discrete logarithmic divisor set is zero; literal continuum support is an
  invalid lift.
- If traces vanish off multiples of d≥2, neighboring traces around a positive
  multiple n are zero. Equation (2) on both unit cells gives energy ≥2F(n)²,
  with the exact sum of the two interpolation defects. Package 2 constructs and
  certifies the finite coprime-supported interpolant.
- SourceGraph in `CHMDDoobSourceGraph.lean` is a closed graph over continuous
  edge coordinates (lag,u), with endpoints u and u+lag. It is not the integer
  trace graph itself. Its measures, representative domains, and ground transform
  must be checked before claiming an actual SourceGraph embedding.

## Prior-art and evidence boundary

The trace-energy variational principle belongs to classical resistance/Dirichlet
form theory; see Jorgensen–Pearse, *A Hilbert space approach to effective resistance
metric*, [arXiv:0906.2535](https://arxiv.org/abs/0906.2535). Its abstract explicitly
discusses trace forms and effective resistance. The present contribution sought
is a proved connection to the corpus's arithmetic shear, not a novelty claim for
the elementary interval inequality. Initial corpus searches returned Pillar VII,
general derivative-energy identities, and CHMDClosedJump's energy representation;
no exact continuum trace bridge was found. Searches completed without errors;
semantic coverage was unmeasured, so absence is not established exhaustively.

## Open obligations

1. Global Sobolev-space identification and rigidity beyond the L2 primitive layer
   and finite coprime trace realization now certified by package 2.
2. Arithmetic interaction and commutation of the infinite coprime projections
   constructed by package 9.
3. Direct identification with existing SourceGraph closed-graph and ground-transform
   APIs, beyond the constructed mixed measure's energy-domain results.
4. Closed form/Sobolev extension and precise affine operator uncertainty.
5. Further substantive research cycles; 100-package target remains open.

## Multiplicative-edge consequence — paper proof

For every n≥0, x∈R, put Jₙ(x)=f(x+log(n+1))−f(x). The physical edge length is
Lₙ(x)=n exp x. Applying (1) to [exp x,(n+1)exp x] and (3) proves

    Jₙ(x)² ≤ n exp x ∫ₓ^{x+log(n+1)} exp(−y) f'(y)² dy.  (5)

This holds at every continuum x, with no lattice-sampling assumption. Multiplying
by arbitrary nonnegative finite edge weights and summing preserves it. For endpoint
values A,B, elementary positive/negative part algebra gives

    (A−B)²=(|A|−|B|)²+4(A⁺B⁻+A⁻B⁺).

Consequently the same right side of (5) controls the opposite-sign nodal pairing,
including finite weighted prime-edge families. These are pointwise and finite-sum
statements. They do not yet assert infinite SourceGraph domain membership.

## Removal of the physical-origin regularity restriction — paper proof

A global continuous physical velocity q restricts F near t=0. To cover arbitrary
continuously differentiable logarithmic states up to constants, instead take an
arbitrary continuous logarithmic velocity v and g(x)=∫₀ˣv. Define
D(a,b)=∫ₐᵇexp(−x)v(x)², L=exp b−exp a, and Δ=g(b)−g(a). Then

    ∫ₐᵇ exp(−x) (L v(x)−Δ exp x)² = L² D(a,b)−L Δ².    (6)

Expansion cancels exp(−x)exp x; ∫v=Δ and ∫exp x=L give the identity. For a<b,
nonnegativity and L>0 prove Δ²≤LD(a,b). This removes the artificial physical-origin
restriction from (5), the shear bound, and their finite weighted nodal consequences.
It also gives equality only for v(x)=c exp x on a nondegenerate interval, exactly
the exponential-affine extremizers. Constants added to g do not change jumps,
derivatives or either energy; nodal pairing is controlled for each such state by
the same scalar identity.

For b,s≥0 set A=σ_b(x+s), B=σ_b(x)+s. The affine relation gives
exp B−exp A=b(exp s−1)≥0, hence A≤B. Applying (6) yields the quantitative
noncommutativity law

    |g(σ_b(x)+s)−g(σ_b(x+s))|²
      ≤ b(exp s−1) ∫_A^B exp(−y)|g'(y)|² dy.             (7)

The physical commutator length is independent of x. This is an energy estimate
for the affine semigroup; it does not claim a unitary full affine-group
representation or a Robertson inequality for self-adjoint generators.

## Formal theorem map

Namespace `GaloisForLFunctions.BiScaleUncertainty.ContinuumShear`.

- `ContinuumShearDirichlet.lean`: explicit shear; physical primitives; physical/log
  energy transport; exact interval and summed cell defects; sharp constant-velocity
  witnesses; arbitrary continuous log velocities; weighted trace defect and affine
  commutator estimate.
- `ContinuumMultiplicativeEdgeControl.lean`: actual continuum multiplicative edges,
  finite nonnegative edge weights, exact nodal decomposition for arbitrary added
  source constants, and weighted nodal-energy control.

Domain: continuous velocities and their constructed primitives. All compact-interval
integrability and derivatives are proved. These are C1 results; general H1/weak
derivative completion, zero-defect rigidity, and coprime interpolant classification
are not yet Lean-certified.

## Verification evidence

- Both final leaves passed `lake --old env lean <leaf> -o <corresponding .olean>`:
  exit 0, no diagnostics. No full or umbrella build was run.
- `/tmp/continuum_shear_axioms.lean` imports the edge leaf, checks four main
  signatures, and prints axioms for **all 34 theorems**. Direct Lean audit passed;
  every theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Both imports are present in `formal/GaloisForLFunctions/BiScaleUncertainty.lean`.
  Generated indexes were refreshed successfully; the new endpoints are present.
- Whitespace checks passed. No added axioms, proof placeholders, native
  computations, heartbeat increases, commits, or numerical experiments.
- Final repository lint exited 1 on three concurrent modules missing umbrella
  imports: `AsymptoticTailCoercivityAndNyquistTrap5Closure`,
  `MultiCosetGramPackingAndNyquistDensity`, and
  `ProducerConsumerDualityAndNymanBeurlingBridge`. No error names either task leaf.
  This is not a global green lint claim. Full output:
  `/tmp/continuum-shear-lint-final.log`.
- Build logs: `/tmp/continuum-shear-build.log`, `/tmp/continuum-edge-build.log`;
  axiom log: `/tmp/continuum-shear-axioms.log`;
  index log: `/tmp/continuum-shear-index.log`.

## Reusable formalization facts

- `Real.exp_lt_exp.mpr` is available; `Real.strictMono_exp` is not in this toolchain.
- Open the `NNReal` scope for `ℝ≥0`; otherwise it parses as an order expression.
- Specify `μ := volume` when compact-interval integrability is inferred inside a
  standalone `have`. Specify explicit integrand lambdas for integral rewrites:
  inferred pointwise powers of continuous maps can obstruct rewriting.
- Beta-reduce integrand lambdas with `dsimp only` before rewriting derivatives.
- Serena rejects these ignored Lean paths; direct file edits were required.

## Path-congestion candidate — resolved for constructed mixtures in package 3

For a nonnegative measure κ on forward logarithmic edges (h,u), h≥0, define

    Kκ(y)=∫ (exp(u+h)−exp u) 1_[u,u+h](y) dκ(h,u).

Conjectured extended-energy theorem for constructed differentiable states:

    ∫ |f(u+h)−f(u)|² dκ ≤ ∫ Kκ(y) exp(−y)|f'(y)|² dy.

Nonnegative extended integrals should remove every integrability premise; Tonelli
transfers the proven interval bound. A finite scalar constant requires separate
control of Kκ, and cannot be uniform over arbitrary rescalings of κ. The actual
SourceGraph κ contains the archimedean measure plus every von-Mangoldt weighted
prime-power line, all multiplied by its two kernel factors. No comparison with its
signed energy or mass follows until these exact weights are treated. This is a
prior candidate. Package 3 below proves the constructed mixed-measure version,
including the measure condition needed for Tonelli. It does not assert a theorem
for unrestricted measures or an external novelty claim for path comparison.

## Package 2 — constructed sharp logarithmic Sobolev traces

**Certified 2026-10-17. One contribution, not 55.** This closes the finite coprime
trace-realization gap left by package 1. The C1 layer cannot realize independent
cell slopes; the new space is actual `Lp ℝ 2 volume` physical velocities.

For arbitrary q in that space, F(t)=∫₀ᵗq is locally absolutely continuous,
F'=q almost everywhere, and the exact interval and unit-cell defects hold.
For f(x)=F(exp x), measurable substitution proves local integrability of
exp x q(exp x), absolute continuity of f, its actual a.e. derivative, and
finiteness of the weighted derivative energy on every compact interval. Thus

    ∫ₐᵇ exp(−x)|f'(x)|² dx = ∫_(exp a)^(exp b)q(t)² dt.

These analytic facts are proved from the L2 type; they are not supplied as
interface premises. No pointwise differentiability at the step corners is used.

For arbitrary amplitudes a, divisor D≥2, and cutoff N, define w(j)=a(j) at
positive interior multiples of D, zero otherwise. Construct

    Q(t)=Σ_{j<N}(w(j+1)−w(j)) 1_(j,j+1](t).

The formal construction proves Q belongs to L2, interpolates w at every integer
0≤j≤N, and has exact energy 2Σ_{j<N}w(j)². Adjacent active traces are impossible.
Because w(0)=w(1)=w(N)=w(N+1)=0, shifting the physical energy window from [0,N]
to [1,N+1] preserves its value. Consequently its logarithmic primitive satisfies

    ∫₀^(log(N+1)) exp(−x)|f'(x)|² dx = 2Σ_{j<N}w(j)².

Nonvacuity is explicit: cutoff N=D+1 realizes arbitrary amplitude a(D) at D.
The Lean natural parameter is d with D=d+2, avoiding a divisor-size premise.

For every competing L2 velocity q, put sj=w(j+2)−w(j+1) and
ej=Fq(j+2)−Fq(j+1)−sj. The unconditional exact comparison is

    weighted log energy = 2Σw² + 2Σsj ej + Σ∫_(j+1)^(j+2)(q−sj)².

The last term is nonnegative. Matching trace increments removes the explicit
error term; the constructed state attains the lower bound. The formal API proves
both the full identity and its corrected lower bound. The paper also describes
the equality characterization; no separate global uniqueness theorem is claimed
in the current formal API. The rough-state nonlinear shear bound is also proved:

    |f(log(exp x+b))−f(x)|² ≤ b∫_x^(log(exp x+b))exp(−y)|f'(y)|²dy.

### Proof, prior art, and boundaries

Full dependency-closed proof: `CoprimeSobolevTrace.md`.
The classical parent is piecewise affine interpolation and its Dirichlet
minimum, documented in Driscoll–Braun, *Fundamentals of Numerical Computation*,
§5.2, https://fncbook.com/pwlin/. The project contribution is the constructive
arithmetic trace realization, rough logarithmic transport, and exact corrected
coercivity. No external novelty claim for finite elements or the Dirichlet principle.

Both corpus searches completed without errors or partial results. Semantic
coverage remained unmeasured; reported coverage snapshot lagged the index.
Search artifacts: `/tmp/continuum-coprime-interpolation-search.json` and
`/tmp/continuum-sobolev-search.json`. They identified the L2/Lebesgue
differentiation/Jacobian machinery, not an existing arithmetic realization.

The formal state space is homogeneous Dirichlet representatives generated by
L2 velocities. No global unweighted L2 mass or identification with mathlib's
Bessel-potential `MemSobolev` is claimed. Infinite edge measures, full graph-domain
admission, and unitary affine uncertainty remain open. This closes a finite
coercivity component, not the whole research objective.

### Formal evidence and repository audit

Namespace: `GaloisForLFunctions.BiScaleUncertainty.SobolevShear`.

| Leaf | Public theorems | Certified surface |
|---|---:|---|
| `SobolevTraceEnergy.lean` | 13 | Actual L2 primitives, absolute continuity, a.e. derivative, exact trace defects |
| `CoprimeSobolevInterpolation.lean` | 20 | Constructed step velocities, all finite traces, exact energy and nonvacuity |
| `SobolevLogarithmicTransport.lean` | 10 | Measurable substitution, actual log derivative, finite weighted energy |
| `CoprimeLogSobolevCoercivity.lean` | 12 | Attained coefficient two, explicit trace error, nonnegative defect, rough shear bound |

All four current leaf sources passed serial foreground `lake --old env lean`
with `-o` to their normal `.olean` paths, exit 0 and no diagnostics. Supporting
private lemmas are checked in those leaves and included transitively in the
public theorem axiom audit. `/tmp/coprime_sobolev_axioms.lean` checked all 55
public theorem declarations and printed principal signatures: only `propext`,
`Classical.choice`, `Quot.sound`; no additional analytic premise or custom axiom.

All four imports are wired into `BiScaleUncertainty.lean`. Index generation
completed and published their declarations to `formal/LEAN_API.md`. `git diff
--check` passed. Global lint exited 1 with exactly two concurrent, unrelated
unreachable modules: `InfiniteGridPolarRecovery` and `LogarithmicCompressionEnergy`.
No lint error concerned these four leaves. Unrelated work was preserved.

Logs: `/tmp/coprime-sobolev-build.log`, `/tmp/coprime-interpolation-build.log`,
`/tmp/coprime-log-transport-build.log`, `/tmp/coprime-log-coercivity-build.log`,
`/tmp/coprime-sobolev-axioms.log`, `/tmp/coprime-sobolev-index.log`,
`/tmp/coprime-sobolev-lint.log`.

### Reusable toolchain facts

- L2 local L1: `integrableOn_Lp_of_measure_ne_top`; square integrability:
  `(Lp.memLp q).integrable_sq`; finite step functions: `memLp_indicator_const`,
  `memLp_finsetSum`, then `MemLp.toLp` and `MemLp.coeFn_toLp`.
- Lebesgue differentiation uses the root name
  `_root_.LocallyIntegrable.ae_hasDerivAt_integral`; dot notation on the local
  namespace did not resolve. Arbitrary-integrand exponential substitution uses
  `Mathlib.MeasureTheory.Function.JacobianOneDim` and its Icc theorems.
- `integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg` proves finiteness, while
  `integral_Icc_deriv_smul_of_deriv_nonneg` proves the value. Prove both when the
  intended statement is a genuine finite Dirichlet form.
- `min_le_max` has implicit endpoints. Mixed Fin/Nat/Real endpoint casts need
  `simpa`; a raw `exact` can leave `↑(d+2)` versus `↑d+2` mismatches.

## Package 3 — exact infinite-edge congestion and nodal transfer

**Certified 2026-10-17. One contribution.** The finite-edge restriction is removed
for actual mixtures of a diffuse lag density and countably many weighted lag
lines. The transfer is an exact extended-energy identity, including its excess
energy. This discharges the measure and measurability obligations needed to
integrate the rough-state trace bound; it does not yet bound the resulting kernel.

An `EdgeMixture` contains only three data fields: a nonnegative plane weight,
real lags h_n, and nonnegative line weights. Its measure is

    κ = ((Lebesgue restricted to h>0) × Lebesgue).withDensity(W)
          + Σ_n (u↦(h_n,u))_* (Lebesgue.withDensity(w_n)).

Weighted Lebesgue measures, their pushforwards, and countable sums are s-finite.
The formal constructor proves these instances. No s-finiteness, integrability,
finite-energy, or desired comparison premise appears in the main signatures.
For nonmeasurable input weight functions, the API retains `withDensity` measures;
it makes no unsupported expansion into raw density integrands.

For e=(h,u), set a=min(u,u+h), b=max(u,u+h), R=exp b−exp a, and
P(e,y)=R1_(a,b](y). Ordered endpoints include reversed and zero-length edges.
All endpoint maps are continuous; P is jointly measurable. For actual L2 q,
F(t)=∫₀ᵗq and f(x)=F(exp x), define

    H(y)=exp y q(exp y)² = exp(−y)|f'(y)|² almost everywhere,
    J(e)=|f(u+h)−f(u)|²,
    B(e)=∫P(e,y)H(y)dy = R∫_(exp a)^(exp b)q(t)²dt,
    S(e)=B(e)−J(e)≥0,       K(y)=∫P(e,y)dκ(e).

Every B(e) is finite, and the local trace bound proves J≤B. Measurability of
J, B, and S is derived. Tonelli and nonnegative additivity give

    ∫ K(y)exp(−y)|f'(y)|²dy = ∫J(e)dκ(e)+∫S(e)dκ(e).       (5)

The totals lie in [0,∞]; no difference of infinite total energies is taken.
The right side retains all countably many jump lines. Their energy and K each
have an exact diffuse-plus-countable-line decomposition in the formal API.

For every real constant c, four times the integrated opposite-sign endpoint
pairing of c+f is bounded by ∫J and hence by the left side of (5). This lifts
the finite nodal control to the actual mixed measure without losing the source
offset or silently truncating its arithmetic lines.

### Proof, parent theory, and exact limitation

Paper proof: `ContinuumPathCongestion.md`. The classical path-comparison parent
is Diaconis–Saloff-Coste, *Comparison Theorems for Reversible Markov Chains*;
the authors' path argument is also presented by Aldous–Fill, §8.1:
https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch8.S1.html.
The contribution is the continuum logarithmic, rough-state, mixed-measure exact
transfer; no novelty claim for classical Cauchy–Schwarz/Tonelli path comparison.

Corpus searches `/tmp/continuum-congestion-search.json` and
`/tmp/continuum-congestion-deep-search.json` completed without errors or partial
results. They found the existing mixed edge geometry and s-finiteness proof,
and generic kernel integration tools, but no applicable continuum congestion
transfer. Semantic coverage was unmeasured and coverage snapshots lagged the index.
Only the source-independent measure geometry was reused; no application-specific
module is imported by the new leaves.

General Tonelli requires a measure condition. This was a proof-gap correction,
not a counterexample to a special unrestricted-measure path formula. Constructing
the mixed measure resolves the condition for the intended edge geometry.
Equation (5) alone does not prove finite graph-domain admission or weighted
source-mass membership. A concrete bound on K remains necessary. No signed
spectral, unitary affine, or application-specific conclusion follows yet.

### Formal evidence

Namespace: `GaloisForLFunctions.BiScaleUncertainty.PathCongestion`.

- `LogarithmicPathKernel.lean`: 22 public theorems, including actual density
  transport, joint measurability, finite local budget, jump bound, and exact slack.
- `MixedEdgePathCongestion.lean`: 12 public theorems and 3 constructed measure
  instances, including exact derivative-energy decomposition, all-line expansion,
  and nodal transfer with arbitrary added constant.

Both final direct leaf checks used `lake --old env lean` with normal `.olean`
outputs, exit 0 and no diagnostics. `/tmp/continuum_congestion_axioms.lean`
audited all 37 public theorem/instance declarations and printed the principal
signatures and the proof-free `EdgeMixture` fields. Only `propext`,
`Classical.choice`, `Quot.sound` occur, including private dependencies.

Both imports are wired; generated indexes refreshed. All 34 public theorem names
appear in `LEAN_API.md`; that view omits the three instance names, which were
checked directly in Lean and in the complete axiom audit. `git diff --check` passed.
Global lint exited 1 with six unrelated concurrent unreachable modules:
`RHTower.NonTemperedShiftedZetaPairCountermodel`, `RHTower.WeilConeMismatchWitnesses`,
`RHTower.ZeroCountRemainderNotIntegrable`, `BiScaleUncertainty.PairedCosetSphereDuality`,
`BiScaleUncertainty.ProductCoupledCollarHierarchy`, and
`BiScaleUncertainty.SignedCosetProductCoupling`. No error concerns the two new leaves.

Logs: `/tmp/continuum-path-kernel-build.log`,
`/tmp/continuum-mixed-congestion-build.log`, `/tmp/continuum-congestion-axioms.log`,
`/tmp/continuum-congestion-index.log`, `/tmp/continuum-congestion-lint.log`.

### Reusable toolchain facts

- `Lp.stronglyMeasurable q` is explicit; `q.stronglyMeasurable` fails after the
  `Velocity` abbreviation elaborates to a subtype. Its `.measurable` gives joint
  measurability after composition with exp.
- `lintegral_lintegral_swap` requires s-finite measures and joint a.e.
  measurability. `Measurable.lintegral_prod_left/right` give measurable marginals.
- `Measure.withDensity` preserves s-finiteness without a density-measurability
  premise. Countable sums and fixed-lag pushforwards preserve it too.
- `ofReal_integral_eq_lintegral_ofReal` bridges the finite interval energy to
  extended integrals. `lintegral_add_measure`, `lintegral_sum_measure`, and
  `lintegral_map` expose every countable branch without summability assumptions.
- `intervalIntegral.continuous_primitive` applies directly to the proved local
  interval integrability. `sq_sub_comm` is not available here; `ring` handles
  reversed endpoint squares. Canonical `zero_le` has an implicit argument.

## Package 4 — compact-source mixed graph admission

**Certified 2026-10-17. One connected contribution, not 32.** For an arbitrary
real continuous compact source ψ and arbitrary finite nonnegative coefficients
λ_n, `compactMixture` constructs diffuse weight `w_arch(h)ψ(u)²ψ(u+h)²` on h>0
and lag-line weights `λ_n ψ(u)²ψ(u+log(n+2))²`. Every physical L2 velocity q
has finite congestion, jump, slack and nodal energies for this actual measure.
Weighted source mass is finite as well, including arbitrary added constants.

Paper: `CompactSourceGraphAdmission.md`. Formalized card:
`docs/drafts/pipeline/3-formalized/compact-source-graph-admission.md`.

### Exact mechanism

Reuse `multiplierSourceRadius ψ = B>0`, derived from actual compact support.
For h>0 the physical resistance cancels the singularity exactly:

    (exp(u+h)−exp u) w_arch(h)
      = 2 exp(u+h/2)/(1+exp(−h)).

The right side, multiplied by ψ(u)²ψ(u+h)², is continuous on all R² and
supported in `[-2B,2B]×[-B,B]`. Its integral is finite. Each line resistance
density is continuous and compactly supported in u. Every line with
`n≥ceil(exp(2B))+1` vanishes. No summability condition on the entire sequence
λ is needed: compact support proves that only finitely many terms survive.

`resistanceMass_eq_finite` gives an exact nonsingular diffuse integral plus
finite atom sum for `C=∫R dκ`. `resistanceMass_ne_top` proves C<∞.
`compact_congestion_le_indicator` proves `K≤C 1_[-B,B]`. Hence

    jump energy + integrated slack
      = ∫K(y)exp(-y)|f'(y)|²dy
      ≤ C ∫_[-B,B] exp(y)|q(exp y)|²dy < ∞.

This uses the established actual rough derivative and local integrability.
Nodal energy of c+f is bounded by jump energy for every real c. The function
ψ²(c+f)² is continuous with compact support, proving finite weighted source
mass and therefore admission to the source-mass plus jump-energy domain.

### Boundary and prior-art audit

Finite resistance mass is sufficient; finite total edge mass is neither assumed
nor proved. The diffuse 1/h singularity may survive before resistance weighting.
This constructs the natural energy-domain admission for the specified squared
source weights. It does not identify the existing SourceGraph closed-graph or
ground-transform APIs, prove closability, a spectral gap, or a unitary affine
representation. Noncompact source kernels remain outside this theorem.

The actual `archLevySinhWeight` definition is exp(x/2)/sinh(x) on all reals;
the measure restricts to positive lags. Both field dictionaries were corrected
to remove their inaccurate claim that the definition is zero for all x≤0.

Corpus query `compact source jump energy Sobolev congestion` completed with
`partial=false`, no errors, and no matching prior admission theorem. Semantic
coverage was unmeasured and the coverage snapshot lagged the index. Generic
Sobolev-to-jump-domain admission is classical; Rutkowski's nonlocal Lévy-type
Dirichlet-problem abstract was inspected as background, not used as a theorem.
No external novelty claim for the generic principle. The contribution discharges
the actual field-specific admission gap by exact cancellation and finite lag support.

### Formal evidence

Namespace: `GaloisForLFunctions.BiScaleUncertainty.PathCongestion`.

- `CompactSourceResistanceMass.lean`: 19 public theorems and 6 definitions.
- `CompactSourceGraphAdmission.lean`: 13 public theorems and 2 definitions.
- Both final direct `lake --old env lean -o <normal-output> <leaf>` checks
  passed with exit 0 and no diagnostics. No full or umbrella build was run.
- `/tmp/compact_source_axioms.lean` audits all 40 public declarations and
  checks actual main signatures. Every axiom set is exactly a subset of
  `propext`, `Classical.choice`, `Quot.sound`; no missing audit or diagnostic.
- Both imports are wired. All 32 theorem names appear in the generated API.
  `scripts/formal_tools.py lint` passed (only existing large-file warnings),
  as did the whitespace check. Earlier concurrent wiring errors are absent
  from this successful current lint run.

Logs: `/tmp/compact-resistance-build.log`, `/tmp/compact-admission-build.log`,
`/tmp/compact-source-axioms.log`, `/tmp/compact-source-index.log`,
`/tmp/compact-source-lint.log`. No owned process remains live.

### Reusable proof facts

- `HasCompactSupport.of_support_subset_isCompact` proves support bounds using
  the actual endpoint geometry. Continuous compact support gives integrability
  for `volume.prod volume`; restricted products follow by `Integrable.mono_measure`.
- `Measure.ae_prod_iff_ae_ae` (the `Measure` namespace is required) transports
  positive-lag membership from the restricted first coordinate.
- `tsum_eq_sum` needs pointwise vanishing outside the finite set; the cutoff
  follows from `Nat.le_ceil` and `Real.lt_log_iff_exp_lt`.
- For `lintegral_map` and `lintegral_withDensity_eq_lintegral_mul`, explicit
  lambda-typed measurability facts avoid rewrite matching failures with composed
  functions. The latter theorem produces density times integrand, in that order.

## Package 5 — compact-source variance coercivity and rigidity

**Certified 2026-10-17. One connected contribution, not 21.** For every continuous
compact source ψ, arbitrary nonnegative finite atom weights, physical L² velocity
q and added constant c, put f(x)=c+∫₀^{exp x}q, M=∫ψ², A=∫ψ²f and Q=∫ψ²f².
With B the constructed source radius and J its actual finite mixed jump energy,

    0 ≤ M Q − A² ≤ sinh(2B) J,
    J=0 iff f(u)=f(v) for every u,v with ψ(u)≠0 and ψ(v)≠0.

This closes the variance-coercivity and continuous nullspace questions for the
admitted compact mixed graph. Positive diffuse long jumps connect all nonzero
source regions, even when support is disconnected. No positive-mass, nonzero-source,
connected-support, atom-summability or finite-energy admission premise is assumed.
Nothing is asserted about f inside source holes. The coefficient depends on B;
optimal constants, expanding-support uniformity, closed-operator identification
and unitary affine actions remain open.

### Exact bridge and additive consequence

For any continuous f, define

    P(u,v)=ψ(u)²ψ(v)²(f(v)−f(u))²,    L(h,u)=P(u,u+h).

All moments and both two-variable functions have constructed compact-support
integrability proofs. Expansion, Fubini, translation and lag-evenness give

    ∫P=2(MQ−A²),    ∫_{h>0}∫L(h,u)du dh=MQ−A².

On contributing positive lags h≤2B, `1≤sinh(2B) exp(h/2)/sinh h`. Comparing
densities gives the diffuse lower bound; every arithmetic term is nonnegative.
The previous finite-admission result justifies the real-valued statement and
also yields `MQ−A² ≤ sinh(2B) C D`, where C is actual resistance mass and D
is source-local additive Dirichlet mass. If variance vanishes, P=0 a.e.; continuity
and full support of product Lebesgue measure give P=0 everywhere. The nonzero
source factors give the pointwise classification, including the zero-source case.

Paper proof: `CompactSourceVarianceCoercivity.md`.
Card: `docs/drafts/pipeline/3-formalized/compact-source-variance-coercivity.md`.

### Corpus and novelty audit

Focused hybrid query `continuous compact source pair variance integral positive lag
spectral coercivity` completed without errors or partial results. All returned
candidate-lemma and source-argument entries were inspected. Existing
`CenteredHyperbolicGramControl.lean` proves a variance inequality for a particular
cosh multiplier; it does not provide the general pair/lag transport or actual
compact-graph comparison. Semantic coverage is unmeasured and the coverage
snapshot lags the index, so no exhaustive novelty claim follows.

Variance identities and positive-kernel comparisons are classical. The contribution
is their premise-free application to the constructed singular diffuse/arithmetic
graph and actual rough states. Barlow–Bass–Chen–Kassmann's jump-form paper is
linked in the paper note as background only; its abstract was inspected, and
no theorem from it is used.

### Formal evidence

Namespace: `GaloisForLFunctions.BiScaleUncertainty.PathCongestion`.

- `CompactSourcePairVariance.lean`: 12 public theorems and 4 definitions.
- `CompactSourceGraphCoercivity.lean`: 9 public theorems and 2 definitions.
- Both final serial direct `lake --old env lean -o <normal-output> <leaf>` checks
  passed with exit 0 and no diagnostics. Compiled outputs postdate their sources.
  No full or umbrella build, heartbeat increase, or numerical experiment.
- `/tmp/compact_variance_axioms.lean` audits all 27 public declarations and checks
  the five main signatures. Exact declaration coverage was checked; all axiom
  sets contain only `propext`, `Classical.choice`, `Quot.sound`, with no diagnostics.
- Both imports are wired. Index refresh passed; all 21 public theorem names
  occur in the generated API.
- Repository whitespace check passed after removing trailing blank lines from
  the touched formal field README.
- `scripts/formal_tools.py lint` exited 1 solely for seven unrelated concurrent
  modules unreachable from the umbrella: `CappedBlockSupport`,
  `CappedCosetSphereDuality`, `FullGridCappedCollarEnergy`,
  `HyperbolicMultiplierIncrementAndOddSignCoercivity`,
  `KreinKantorovichMeasureTransportAndPrimePolarPairing`,
  `LocalCorrelationEnergyStability`, `SignedKreinCollarAndPrimeDeficitTransfer`.
  No lint error concerns either new leaf; large-file warnings remain global.

Logs: `/tmp/compact-pair-variance-build.log`, `/tmp/compact-graph-coercivity-build.log`,
`/tmp/compact-variance-axioms.log`, `/tmp/compact-variance-index.log`,
`/tmp/compact-variance-lint.log`. All owned verification processes are terminal.
Obsolete owned API-probe scratch files were removed.

### Reusable proof facts

- `integral_comp_abs` gives the positive-half integral with factor 2 and no
  integrability argument; import `Mathlib.MeasureTheory.Measure.Lebesgue.Integral`.
- `integral_add_left_eq_self` and `integral_sub_right_eq_self` take the function
  before the shift. `Integrable.mul_prod` proves separated-product integrability.
- `Measure.eq_of_ae_eq` upgrades a.e. equality of continuous functions under a
  full-support measure. Explicit `f` and measure arguments can be necessary for
  `integral_nonneg` on a product measure.
- Explicit lambda-typed integrability/measurability facts avoid Pi.add/Pi.mul
  rewrite mismatches. A final `rfl` resolves definitionally identical products
  after rewriting the weighted lintegral.

## Package 6 — actual rough modulus and exact nodal slack transfer

**Certified 2026-10-17. One connected contribution, not 25.** For arbitrary
physical L² q and c∈ℝ, let G(t)=c+primitive q t. The actual L² velocity
`m=modulusVelocity q c` satisfies

    m(t)=sign(G(t))q(t) almost everywhere,
    |c|+primitive m t=|G(t)| for every t,
    energy m a b=energy q a b for every a,b.

The derivative-zero law on {G=0} is proved, not assumed. In logarithmic
coordinates, the state (m,|c|) is exactly the modulus of (q,c); all local
weighted logarithmic Dirichlet energies are unchanged.

For any constructed mixed edge measure D, with no finite-total-energy premise,

    jumpEnergy D q=jumpEnergy D m+nodalEnergy D q c,
    slackEnergy D m=slackEnergy D q+nodalEnergy D q c,
    congestionEnergy D m=congestionEnergy D q.

Every individual path budget is unchanged. Thus nodal jump loss is transferred
exactly into slack inside the actual rough-state domain. Compact-source admission
makes every energy finite; the ordinary real jump-energy difference equals
nodal energy, and `sourceMass ψ m |c|=sourceMass ψ q c`. The whole source-mass
plus jump form consequently has the same exact nodal defect.

Paper: `RoughSobolevModulus.md`.
Card: `docs/drafts/pipeline/3-formalized/rough-sobolev-modulus-nodal-defect.md`.
This discharges nonlinear modulus-domain realization and sharpens the nodal
upper bound to an exact decomposition. It does not identify the full closed
operator domain or a unitary affine action, and it does not claim a new general
Sobolev chain rule or Beurling–Deny principle.

### Proof mechanism and reusable facts

Absolute value contracts endpoint distances, so the actual G has locally
absolutely continuous modulus. A countable [-n,n] cover gives differentiability
of |G| a.e. At a zero of G where both derivatives exist, |G| and |G|+G attain
minimum zero. Fermat's theorem forces both derivatives to vanish, hence q=0.
Away from zero, the ordinary chain rule applies. Therefore `(|G|')²=q²` a.e.
Measurability and norm domination construct its L² class. The fundamental
theorem of absolute continuity gives its exact primitive for all t, including
negative endpoints. This avoids imposing a derivative or zero-level premise.

The existing discrete nodal identity is reused on an encoded pair of actual
continuum endpoints. All terms are measurable and nonnegative, so their entire
mixed-measure integrals add, even at infinity. Edgewise budget equality and
finite individual jumps justify the slack cancellation before integration;
subtracting potentially infinite total energies would not prove the result.

- `absolutelyContinuousOnInterval_iff` plus
  `abs_abs_sub_abs_le_abs_sub` proves modulus absolute continuity directly.
- `AbsolutelyContinuousOnInterval.ae_differentiableAt` and `ae_all_iff` give the
  global a.e. derivative statement from the countable interval cover.
- `IsLocalMin.hasDerivAt_eq_zero` and `IsLocalMin.deriv_eq_zero` implement the
  zero-level argument. `HasDerivAt.const_add` keeps the original velocity.
- `stronglyMeasurable_deriv`, `MemLp.of_le` and `MemLp.coeFn_toLp` construct and
  identify the actual modulus velocity.
- `ENNReal.add_right_inj` cancels a finite left summand; `C_c` notation
  requires `open scoped CompactlySupported`.

### Corpus and source audit

Deep query `absolutely continuous modulus derivative zero level set primitive
Sobolev sign` returned applicable mathlib a.e. differentiability and derivative
integrability APIs. All 20 candidate lemmas, 20 source arguments and the proposed
ingredient group were inspected. Results were partial: the final sign-change
query was unfinished. No execution errors; semantic coverage unavailable and
coverage snapshot older than the index. The generated ingredient claim
"Derivative zero implies absolute continuity" was rejected: it is false
without additional hypotheses, as the Cantor-function obstruction illustrates.
The proof establishes absolute continuity first. No suggested private or
unrelated result was imported. The paper links primary Sobolev lecture notes
for background; all needed modulus and zero-level facts are proved here.

### Formal evidence

- `RoughSobolevModulus.lean`, namespace `SobolevShear`: 14 public theorems and
  2 definitions; `RoughModulusGraphDecomposition.lean`, namespace
  `PathCongestion`: 11 public theorems.
- Both final serial direct `lake --old env lean -o <normal-output> <leaf>`
  checks exited 0 without diagnostics. Output timestamps postdate final sources.
  No umbrella/full build, heartbeat increase or numerical experiment.
- `/tmp/rough_modulus_axioms.lean` audited every public declaration and printed
  seven main signatures. All 27 have only `propext`, `Classical.choice`,
  `Quot.sound`; exact name coverage was verified, with no missing audit or diagnostic.
- Both imports are wired. Final index refresh passed and all 25 theorem names
  are present in the generated API. Repository whitespace check passed.
- Global lint exited 1 solely for four unrelated concurrent modules lacking
  umbrella reachability: `RHTower.FermiNymanDyadicFoldGeometry`,
  `BiScaleUncertainty.CappedCollarArrayComparison`,
  `BiScaleUncertainty.CappedSupportComparison`, and
  `BiScaleUncertainty.InfiniteGridUniformTail`. Neither new leaf has a lint error.
  Existing global large-file warnings remain.

Logs: `/tmp/rough-sobolev-modulus-build.log`, `/tmp/rough-modulus-graph-build.log`,
`/tmp/rough-modulus-axioms.log`, `/tmp/rough-modulus-index.log`,
`/tmp/rough-modulus-lint.log`. All owned processes are terminal.

## Package 7 — nodal mass coercivity and strict modulus contraction

For every compact continuous source ψ, physical L² velocity q, constant c and
arbitrary nonnegative arithmetic weights, set f=c+logPrimitive q,
P=∫ψ²max(f,0), N=∫ψ²max(−f,0), and C=sinh(2 multiplierSourceRadius ψ).
The exact finite laws are

    Vψ(f)−Vψ(|f|)=4PN ≤ C * nodalEnergy = C [J(q)−J(modulusVelocity q c)].

Zero nodal energy, and equivalently equality under modulus, holds iff f≥0
throughout {ψ≠0} or f≤0 throughout {ψ≠0}. Strict contraction holds iff both
signs occur at nonzero source points. No connected-support, positive-mass,
atom-summability or finite-energy admission premise appears. Equality here
allows nonconstant one-sign states; zero jump energy requires constancy.

### Proof mechanism and boundaries

- Positive/negative weighted source masses are integrals of nonnegative
  continuous compactly supported functions. Zero integral is equivalent to
  vanishing everywhere by continuity and full support of Lebesgue measure.
- The exact first moments are P−N and P+N; second moments agree under modulus.
  Their variance difference is 4PN. The positive-lag nodal integrand is the
  integrable difference of the two pair-gap functions, so its integral is 4PN.
- On contributing positive source pairs, h≤2B and 1≤C*w_arch(h). Compare the
  nonnegative nodal integrand directly and retain all nonnegative arithmetic
  lines. Subtracting independent variance coercivity inequalities is invalid.
- The reverse zero-loss implication kills both diffuse and every arithmetic
  density pointwise. Finite compact-source energies justify cancellation in
  the actual rough-modulus decomposition.
- One-sign is a global source condition, including disconnected components.
  No optimality claim is made for C. No closed SourceGraph/operator identity
  or external novelty is claimed. Parent jump-form theory is classical; the
  paper records the primary source and exact evidence boundary.

### Formal evidence

`CompactSourceNodalVariance.lean` has 13 public theorems and 4 definitions;
`CompactNodalMassCoercivity.lean` has 9 public theorems. Both final serial direct
`lake --old env lean -o <normal-output> <leaf>` checks exited 0 without diagnostics.
Output timestamps postdate final source edits. All 26 public declarations were
audited with exact name coverage; only `propext`, `Classical.choice`, `Quot.sound`.
Seven main signatures were inspected and contain no extra analytic premises.
No full/umbrella build, numerical experiment, heartbeat increase or added axiom.
Both imports, both field maps and all 22 theorem names in the generated API are
present. Index refresh and whitespace check passed.

Final global lint exited 1 for five unrelated concurrent missing imports:
`RHTower.FermiNymanDyadicFoldGeometry`,
`BiScaleUncertainty.DyadicMultiplierFrameBound`,
`BiScaleUncertainty.InfiniteGridCorrelationCompactness`,
`BiScaleUncertainty.InfiniteGridLimitEnergy`, and
`BiScaleUncertainty.SignedPrimePolarCoupling`. Neither new leaf has a lint error;
existing global large-file warnings remain. These unrelated modules were untouched.

Paper: `docs/reports/BiScaleUncertainty/CompactNodalMassCoercivity.md`.
Card: `docs/drafts/pipeline/3-formalized/compact-nodal-mass-coercivity.md`.
Evidence: `/tmp/compact-nodal-variance-build.log`, `/tmp/compact-nodal-mass-build.log`,
`/tmp/compact_nodal_mass_axioms.lean`, `/tmp/compact-nodal-mass-axioms.log`,
`/tmp/compact-nodal-mass-index.log`, `/tmp/compact-nodal-mass-lint.log`.
All owned processes are terminal. Package 7 is **progress**.

## Package 8 — actual Markov clamp and firm graph control

For any physical L² velocity q and constant c, set T(a)=min(max(a,0),1),
q_T=(modulusVelocity q c−modulusVelocity q (c−1))/2 and q_R=q−q_T.
These actual velocities realize T(c+primitive q) and its residual exactly,
including their anchoring constants. The clamped state is locally absolutely
continuous, with derivative q*1_{0<c+primitive q<1} a.e. Threshold derivatives
follow from the proved zero-level law, not an admission premise.

### Exact laws and rigidity

- q²=q_T²+q_R² a.e.; hence local physical and weighted logarithmic derivative
  energies split exactly for every oriented interval.
- Every path budget splits exactly; total congestion has the same addition law
  for the full mixed measure, even with infinite total energies.
- J(q_T)+J(q_R)≤J(q). Weighted source mass and the entire admitted compact form
  satisfy the same firm contraction inequality.
- Vψ(Rf)≤sinh(2B)[J(q)−J(q_T)], where Rf=f−T(f) is the actual residual state.
- J(q_T)=J(q) iff f is sourcewise constant OR every nonzero-source value is in
  [0,1]. Constant states outside the band have zero jump energy and must remain
  in this classifier. Source-mass equality is different.
- Covers zero/disconnected sources and arbitrary nonnegative arithmetic weights;
  no extra analytic premise. No closed SourceGraph or unitary affine claim.

The construction uses T(a)=(|a|−|a−1|+1)/2 and L² linear operations. T and R are
increasing, so their jump interaction is nonnegative. Derivative orthogonality
therefore does NOT imply jump orthogonality: the nonlocal split is an inequality.
Equality forces zero residual jump energy; existing compact-graph rigidity makes
Rf constant sourcewise. Every nonzero fiber of R is a singleton, and its zero
fiber is [0,1], giving the complete classifier. This avoids a new singular-kernel
nullspace proof and keeps the actual constructed graph measure throughout.

### Formal evidence and reusable APIs

`RoughSobolevClamp.lean` (SobolevShear) has 25 public theorems, 3 definitions;
`RoughClampGraphControl.lean` (PathCongestion) has 11 public theorems. Both final
serial direct `lake --old env lean -o <normal-output> <leaf>` checks passed
without diagnostics. Normal outputs postdate final sources. All 39 public
declarations audited with exact coverage; only `propext`, `Classical.choice`,
`Quot.sound`. Ten main signatures checked, no extra analytic admission premise.
Imports, field maps, all 36 theorem names in generated API and whitespace checks
pass. Global formal lint passes: earlier concurrent import failures are absent.
Existing large-file warnings remain. No full/umbrella build, numerical experiment,
added axiom or heartbeat increase. All owned processes terminal.

`primitive_velocity_sub` and `primitive_velocity_smul` handle actual L² classes
through `Lp.coeFn_sub/smul`. Explicit arguments avoid ambiguous ordered-group
instances in `max_eq_left`; `dsimp only` exposes unapplied lambdas before integral
rewrites. The graph equality converse uses `lintegral_eq_zero_iff` on the actual
residual squared jump, then exact primitive linearity.

Paper: `docs/reports/BiScaleUncertainty/RoughMarkovClamp.md`.
Card: `docs/drafts/pipeline/3-formalized/rough-markov-clamp-domain.md`.
Evidence: `/tmp/rough-sobolev-clamp-build.log`, `/tmp/rough-clamp-graph-build.log`,
`/tmp/rough_clamp_axioms.lean`, `/tmp/rough-clamp-axioms.log`,
`/tmp/rough-clamp-index.log`, `/tmp/rough-clamp-lint.log`.
Fresh clamp search inspected all 20 candidate lemmas and 20 source arguments,
with no execution errors/partial stages. Semantic coverage and source/compiler
freshness incomplete. Classical contraction theory is background, not an
external novelty claim; primary links are in the paper. Package 8 is **progress**.

## Package 9 — infinite coprime extension and exact orthogonal projection

For d∈ℕ, m=d+2 and n_j=m(j+1), define h_j as the difference of the actual
L² indicators of (n_j−1,n_j] and (n_j,n_j+1]. Their normalized family h_j/√2
is orthonormal. Actual ℓ² data v have a convergent L² extension E_d(v)=Σv_jh_j,
with every nonnegative integer trace specified exactly:

    primitive E_d(v)(n) = v_(n/m−1) if 0<n and m divides n, else 0,
    ∫ℝ E_d(v)² = 2Σ_jv_j².

Logarithmic traces at log n_j equal v_j. Existing rough logarithmic transport
supplies local absolute continuity, actual derivative and weighted interval
energy for this constructed velocity. The full physical energy includes the
negative half-line; no unproved global logarithmic-energy identification is used.

### Intrinsic coefficients, exact defect and rigidity

For every actual physical L² q, with F=primitive q,

    a_j = 2F(n_j)−F(n_j−1)−F(n_j+1)

is square summable. The proof constructs normalized synthesis S:ℓ²→ₗᵢL² and
its Hilbert adjoint A, with (Aq)_j=a_j/√2. Therefore b=Aq/√2 is actual ℓ²,
b_j=a_j/2, and P_dq=SAq=E_d(b) is the orthogonal projection onto the closed
tent-extension range. This range is the closed span of the normalized tents.

    ∫q² = ½Σa_j² + ∫(q−P_dq)²,
    ∫(q−E_d(v))² = ∫(q−P_dq)² + 2Σ(b_j−v_j)².

Projection fixes every extension, is idempotent, and its residual is orthogonal
to every extension. The first equality yields the sharp curvature bound, with
equality iff q belongs to the extension range. The second proves that E_d(b)
is the unique nearest extension. The core theorems assume neither neighboring
trace zeros nor summability of a raw function: all convergence follows from
actual ℓ²/Hilbert input types and the adjoint construction. If neighboring traces
vanish, a_j=2F(n_j) recovers sharp infinite coprime coercivity as a paper consequence.
No closed SourceGraph or unitary affine-group identification is asserted.

### Formal evidence and reusable facts

- `CoprimeTentHilbertFrame.lean`: 197 lines, 17 public theorems, 8 definitions,
  one abbreviation. `InfiniteCoprimeTraceProjection.lean`: 260 lines, 23 public
  theorems and 3 definitions. Namespace `SobolevShear`.
- Both final serial direct leaf checks passed without diagnostics; normal
  compiled outputs are newer than their sources. No full/umbrella build,
  numerical experiment, heartbeat increase or added axiom.
- Every one of 52 public declarations audited with exact name coverage; only
  `propext`, `Classical.choice`, `Quot.sound`. Twelve main signatures inspected.
- Both imports and both maps wired; all 40 theorem names indexed. Index refresh
  passed. Scoped whitespace check passed. Repository-wide whitespace check
  found one unrelated blank line at EOF in `bi-scale-uncertainty-foundation-2026-10-17.md`.
- Global lint exited 1 only for nine concurrent unreachable field modules:
  `DyadicSchurCollarEnergy`, `DyadicSchurSupport`, `FourthMomentJumpReceiver`,
  `InfiniteGridStrictEnergyLoss`, `ShortSupportEnergyInjection`,
  `SmallSourceCorrelationStability`, `TwoColumnSchurGeometry`,
  `TwoColumnSchurSupport`, `UnitEnergySmallSources`. No error concerns either
  new leaf. Existing large-file warnings remain; unrelated work was preserved.

`L2.inner_indicatorConstLp_one` turns primitive evaluation into a continuous
Hilbert functional. The indicator-intersection theorem needs explicit finite
measure arguments, avoiding its expensive default finiteness tactic. Map the
convergent series with `innerSL.hasSum`; simplify tent pairings before general
primitive pairings. `Orthonormal.orthogonalFamily.linearIsometry` constructs the
actual synthesis; its adjoint derives summability without a Bessel admission
premise. When rewriting an energy identity, pass d explicitly: d does not occur
on the left side, so an unqualified rewrite can leave a metavariable.

Fresh corpus search inspected all 20 candidate lemmas and all 20 source arguments.
Finite construction/defect results existed; no matching infinite construction
or projection found. No partial stages or errors, but snapshot freshness and
semantic coverage remain incomplete. NPTEL's Riesz–Fischer/projection parent
theory was checked; no external novelty claim for these classical tools.

Paper: `InfiniteCoprimeTraceExtension.md`.
Card: `docs/drafts/pipeline/3-formalized/infinite-coprime-trace-extension.md`.
Evidence: `/tmp/coprime-tent-frame-build.log`,
`/tmp/infinite-coprime-projection-build.log`, `/tmp/infinite_coprime_axioms.lean`,
`/tmp/infinite-coprime-axioms.log`, `/tmp/infinite-coprime-index.log`,
`/tmp/infinite-coprime-lint.log`. All owned verification processes are terminal.
Package 9 is **progress**; certified count **9/100**, goal active.

## Package 10 — arithmetic classification of infinite projection commutators

**Certified 2026-10-17. One connected contribution.** For every pair of spacings
m=d+2,n=e+2≥2, let V_m,V_n be the actual closed infinite tent-extension ranges,
P_m,P_n their constructed projections, and L=lcm(m,n). Proved:

    V_m ∩ V_n = V_L,
    P_m P_n = P_n P_m  iff  gcd(m,n)≥2,
    gcd(m,n)≥2  implies  P_m P_n=P_L.

The cross-tent Gram formula is 2 at equal centers, −1 at adjacent centers,
zero otherwise. A shared divisor greater than one excludes adjacency, so
projection retains precisely coincident centers. Mapping the convergent Hilbert
series extends this calculation to the full infinite operators. Nested projection
absorption and self-adjointness give the lcm product. Intersection for arbitrary
spacings uses every integer trace: coefficients outside the common multiples
vanish, and the lcm projection fixes every nonzero summand. It does not assume
that intersections of closed spans equal spans of intersected index sets.

For gcd(m,n)=1, a modular inverse gives positive active centers a=b+1 with
m|a,n|b. Input q=H_a is fixed by P_m. At b the P_m P_n trace is zero while
the P_n P_m trace is −1/2. Thus

    primitive((P_m P_n−P_n P_m)H_a)(b)=1/2.

This exact witness includes m=2 or n=2, where a tent may have two adjacent
partners. No leakage, operator, summability or analytic admission premise is
assumed. The unconditional main iff quantifies arbitrary d,e and actual L² q.
This is an arithmetic interaction inside the continuum Dirichlet domain;
unitary affine-group and closed SourceGraph identifications remain open.

### Formal evidence and reusable facts

| Leaf | Lines | Public theorems | Definitions |
| --- | ---: | ---: | ---: |
| `CoprimeProjectionCrossGram.lean` | 112 | 12 | 1 |
| `CoprimeProjectionLattice.lean` | 122 | 9 | 1 |
| `CoprimeProjectionCommutator.lean` | 101 | 7 | 0 |

All direct serial leaf checks and the exact-coverage audit of all 30 public
declarations pass. Only standard axioms `propext`, `Classical.choice`,
`Quot.sound`; nine main signatures inspected. All three imports wired, and all
30 declarations appear in the generated API under the correct module. No full
or umbrella build, heartbeat increase, numerical experiment or added axiom.

`ContinuousLinearMap.hasSum` transports actual tent series; self-adjointness
supplies reverse nested absorption. Use `ContinuousLinearMap.ext` explicitly:
bare `ext q` can descend into Lp's a.e.-equality representation. `lp.ext` leaves
a function equality, so follow it with `funext`. Use `simp only` to rewrite an
iff inside a natural-divisibility conditional; `rw` may produce an ill-typed
dependent `Decidable` motive. Put attributes on their own lines so the API
indexer sees every declaration.

The relocated 242-line `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`
was read fully after the user's update and treated as read-only. The old report
README is gone; module mapping is recorded here and in the generated API.

Fresh corpus search inspected all 20 candidate lemmas and all 20 source
arguments. Single-family projections and finite trace results existed; no
cross-family classifier found. No partial stages or errors, semantic coverage
unmeasured, background refresh incomplete. Primary Hilbert projection and
Bezout/lcm sources are linked in the paper; no external novelty claim for those
classical tools.

Paper: `CoprimeProjectionCommutator.md`.
Card: `docs/drafts/pipeline/3-formalized/coprime-projection-arithmetic-commutator.md`.
Evidence: `/tmp/coprime-cross-gram-build.log`,
`/tmp/coprime-projection-lattice-build.log`,
`/tmp/coprime-projection-commutator-build.log`,
`/tmp/coprime_commutator_axioms.lean`, `/tmp/coprime-commutator-axioms.log`,
`/tmp/coprime-commutator-index.log`, `/tmp/coprime-commutator-lint-final.log`.
Final `scripts/formal_tools.py lint` exits 1 solely for three concurrent
unreachable field modules: `HyperbolicGaugeChebyshevEnergyRepresentation`,
`OptimizedHyperbolicRayReceiver`, and `SignedPhysicalGramEnergy`. No error
concerns this package; existing large-file warnings remain. Earlier
`--check-generated` also caught index drift; the index was refreshed afterward,
and exact coverage of all 30 package declarations was verified. Unrelated work
was preserved. Scoped whitespace, compiled-output freshness, unique imports,
and stage-transition checks pass. All owned verification processes are terminal.

Package 10 is **progress**; certified count **10/100**, goal active.

## Package 11 — sharp arithmetic angles and alternating projection errors

**Certified 2026-10-17. One connected contribution.** For actual infinite
projections P=P_m,Q=P_n, m,n≥2, let R=P_lcm(m,n), T=PQ−R and K=PQ−QP.
Define c=0 when gcd(m,n)≥2, c=1/2 when the spacings are coprime and one is two,
and c=1/4 otherwise. Proved unconditionally:

    T²=cT,                   ‖T‖²=c,
    K³=−c(1−c)K,             ‖K‖²=c(1−c),
    (PQ)^k−R=c^(k−1)T,       ‖(PQ)^k−R‖²=c^(2k−1)  (k≥1).

Both operator norms are attained by actual nonzero physical L² velocities.
The square-root forms are also formalized. Thus coprime spacings at least
three give norms 1/2 and √3/4; spacing two changes them to 1/√2 and 1/2.
The arithmetic angle is independent of how large the coprime spacings are.
The resulting alternating-projection rate is exact, not an upper estimate.

### Proof mechanism and boundary

After removing coincident centers, spacings at least three allow only isolated
adjacent pairs. A non-even center in a spacing at least three has two positive
even neighbors, producing a two-arm star for spacing two. Exact analysis
coefficients give projection −H_a/2 in the first case and −(H_a+H_a')/2 in
the second. These are identities for actual infinite projections, derived from
actual finite ℓ² coefficient data. The positive-half-line boundary loses no arm.

Mapping convergent tent series proves T²=cT on the full L² space. Projection
algebra gives A=TT*, A²=cA and K³=−c(1−c)K. The C*-norm identity plus the
previous exact noncommutation witness supplies the exact norms. For attainment,
use B=S^* S for S=T or K: B≠0, choose x with Bx≠0, and q=Bx satisfies Bq=λq,
so ‖Sq‖²=λ‖q‖². In the commuting case a nonzero tent attains both zero norms.
No spectral, decomposition, summability or analytic admission premise is used.

This closes the quantitative two-projection problem in the actual continuum
Dirichlet velocity domain. It does not identify a unitary affine representation,
a closed SourceGraph form, or a joint prescribed-value trace extension.

### Formal evidence and reusable facts

| Leaf | Lines | Public theorems | Definitions |
| --- | ---: | ---: | ---: |
| `CoprimeProjectionNeighbors.lean` | 141 | 10 | 1 |
| `CoprimeProjectionAnglePolynomial.lean` | 150 | 10 | 2 |
| `CoprimeProjectionAngleNorm.lean` | 271 | 16 | 1 |
| `CoprimeAlternatingProjectionRate.lean` | 64 | 5 | 0 |

All four final serial direct leaf checks pass without diagnostics. Every one of
45 public declarations audited with exact name coverage; only standard axioms.
Twelve main signatures inspected, including unconditional norm attainments and
iteration laws. Four unique umbrella imports, all 45 API entries at current
source lines, and current compiled outputs verified. The field README was read
fully and remained read-only. No full/umbrella build, numerical experiment,
heartbeat increase or added axiom.

Refolding a definition with `simp [← definition]` is invalid; expose an iff
lemma and refold that lemma instead. When applying an equality-on-tents lemma
to a composed/scaled operator, supply d,e explicitly and `change` the pointwise
goal before invoking the tent identity. This avoids a genuine 200000-heartbeat
definitional-equality failure without increasing limits. Use explicit arguments
when refolding `coprimeProjector_apply`; an unqualified reverse rewrite can
target the wrong projection. C*-norm lemmas live in `CStarRing`. Bare
`have := @Name` probes may need explicit universe levels; the final scratch
audit verified these API probes as well. Prefer `sub_apply` and
`mul_apply_eq_comp` to deprecated continuous-linear-map aliases.

Fresh focused corpus query inspected all 20 candidate lemmas and all 20 source
arguments. Existing projection classifier and generic Gram tools found, no
matching angle classification. Results were partial without execution errors;
refresh incomplete, semantic coverage not supplied. The classical
Friedrichs-angle/alternating-projection parent theory was checked in
Badea–Grivaux–Müller, linked in the paper. No external novelty claim for it.

Paper: `CoprimeProjectionAngleGap.md`.
Card: `docs/drafts/pipeline/3-formalized/coprime-projection-angle-gap.md`.
Evidence: `/tmp/coprime-projection-neighbors-build.log`,
`/tmp/coprime-angle-polynomial-build.log`, `/tmp/coprime-angle-norm-build.log`,
`/tmp/coprime-alternating-projection-build.log`, `/tmp/coprime_angle_axioms.lean`,
`/tmp/coprime-angle-axioms.log`, `/tmp/coprime-angle-index.log`,
`/tmp/coprime-angle-lint.log`. Global `lint --check-generated` exits 1 for
four unrelated concurrent unreachable modules: `AnnularSourceRegularity`,
`SignedGramCapacity`, `SignedGramCutoffComparison`, and
`SignedGramCutoffHierarchy`, plus drift in `LEAN_API.md`/`LEAN_OVERVIEW.md`.
No error concerns this package; no active proof-debt error. Existing large-file
warnings remain. Index refreshed afterward; all 45 exact current-source API
entries and compiled-output freshness reverified. Scoped whitespace and stage
transition checks pass. Unrelated work preserved; all owned processes terminal.
Final index log: `/tmp/coprime-angle-index-final.log`.
Package 11 is **progress**; count **11/100**, goal active.

## Certified package 12 — sharp infinite joint trace interpolation

For m=d+2,n=e+2, shared nodes belong to the first grid. The actual closed data
space D={(a,b)∈ℓ²×ℓ²:R(E_e b)=0} is equivalent to b_j=0 whenever m divides
n(j+1). Arbitrary ℓ² pair data map into D by deleting the common component.
E(a,b)=E_d a+E_e b has every integer and logarithmic trace, with zero values at
all off-union integer nodes. M=‖a‖²+‖b‖² counts union values once; the ambient
product Banach norm is max(‖a‖,‖b‖), not √M.

Exact energy is 2M−2Σ_j a_j[B(m(j+1)−1)+B(m(j+1)+1)], where B is the second
primitive. The scalar series is summable, and its explicit divisibility formula
reads the two adjacent second-family values. Shared nodes have no active neighbors;
within-family adjacency is impossible. Thus every adjacent union edge occurs once.

Sharp lower/upper factors are (2,2) if gcd(m,n)≥2, (1,3) for coprime m,n≥3,
and (2−√2,2+√2) for the coprime spacing-two case. Both are attained by actual
positive-mass data. E is injective with closed range equal to V_m+V_n; no closure
of the algebraic sum is needed. Mechanism: |⟨E_d a,E_e b⟩|≤√c M from the
proved reduced product T=PQ−R. Its positive square A=T* T obeys A²=cA;
choose y=Az≠0, x=Ty/√c, then take coefficients of (±x,y). The zero-angle
case uses a single nonzero first-family tent. No spectral admission assumption.

For every physical q, exact competitor energy retains two summable residual
curvature pairings. Matching every integer trace kills them, leaving excess
‖q−E(a,b)‖²; equality iff q=E(a,b). Prescribing only union traces is a different
variational problem. The main mismatch identity is unconditional. No unweighted
logarithmic H¹ or full affine operator identification is claimed.

Paper: `TwoGridCoprimeTraceExtension.md`. Stage-3 card:
`docs/drafts/pipeline/3-formalized/two-grid-coprime-trace-extension.md`.
Four leaves: TwoGridTraceData, TwoGridTraceStability, TwoGridTraceSharpness,
TwoGridTraceMinimality. All four final serial direct checks pass with empty logs;
normal outputs are newer than sources. All 49 public declarations (40 theorems,
7 definitions, 1 abbreviation, 1 instance) were axiom-audited with exact coverage;
only propext, Classical.choice, Quot.sound. Thirteen main signatures inspected.
Four unique imports, all 48 catalog-supported public entries at current source
lines and scoped whitespace verified. Named instance audited separately.

Final `lint --check-generated` exits 1 solely for ten unrelated concurrent
unreachable modules: AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis,
DistantCopyCompactness, DistantCopyCorrelationTopology, DistantCopyEnergyTopology,
DistantCopyPolarTopology, DistantCopySharpness,
HyperbolicGaugeMeanSquareChebyshevWeilSynthesis, SignedGramDualSupport,
SignedGramPhysicalPrices, SignedGramTrialCertificate. No own, proof-debt or
stale-generated error. Existing large-file warnings remain. No full build,
new axiom, numerical experiment or heartbeat increase. README remained read-only.

Evidence: `/tmp/two-grid-{data,stability,sharpness,minimality}-build.log`,
`/tmp/two_grid_axioms.lean`, `/tmp/two-grid-axioms.log`,
`/tmp/two-grid-audit-names.json`, `/tmp/two-grid-api-entries.txt`,
`/tmp/two-grid-index-final.log`, `/tmp/two-grid-lint-final.log`.
Focused corpus search: all16 candidates/all17 source arguments inspected;
partial=false/errors=[], semantic unmeasured, refresh incomplete. Classical hat
interpolation checked in the primary Driscoll–Braun textbook; no external novelty
claim for parent methods. One significant package, count12/100, goal active.

Lean lessons: `real_inner_comm x y` rewrites ⟪y,x⟫ to ⟪x,y⟫.
`HasSum.congr_fun` expects new summand = old summand. The bundled scaled
synthesis and scalar-inside synthesis are propositionally, not definitionally,
equal; rewrite the application lemma explicitly. Keep attributes on separate
lines so generated catalog captures declarations. Avoid `convert` when a known
limit equality can be rewritten directly; it can expose stuck lp coercions.

## Certified package 13 — finite-grid longest-run coercivity

`docs/drafts/pipeline/3-formalized/finite-grid-run-length-coercivity.md` and
`FiniteGridRunLengthCoercivity.md`: for the actual family {d+2}∪{e+2:e∈D},
the longest active run r satisfies 1≤r<L and is attained in one lcm period.
The actual masked successor T=P R* P is a contraction with T^r=0. Its
existing sine bound gives sharp factors 2±2cos(π/(r+1)); finite sine and
alternating-sine packets attain both. Unit-cell synthesis S(v−Rv) gives the
infinite physical L² interpolant, all integer/log traces, exact adjacent
energy, closed range and the unconditional curvature-mismatch identity.
Matching every integer trace yields exact minimum-energy defect and uniqueness.
The dependency-closed paper proof and exact Lean package are certified.
One mathematical package: certified count 13/100, goal active.

The focused corpus query's eight candidate/eight source entries and deep query's
twenty candidate/twenty source entries/one ingredient group were all inspected.
No finite-family theorem found; both searches partial with interrupted retrieval
or semantic timeout, semantic coverage unmeasured and refresh incomplete.
Exact search located reusable existing finite sine and nilpotent-contraction
proofs. Classical discrete Wirtinger theory checked against Izmestiev's primary
paper; no external novelty claim for the parent result.

Trap 10 discipline: retain actual producers and proved error bounds. This
package constructs its interpolant and exact competitor error, with no
Chebyshev/floor-sum input. For the supplied factorial example, the first
stencil retains 2N log 2; only its centered remainder is O(log N). The second
stencil cancels that term. Symbolic Stirling justification and source appear
in the paper. README remains read-only; research stays on coprime shear.

### Formal evidence and reusable facts

Eight leaves, all final serial direct normal-output `lake --old env lean`
checks exit 0 with empty logs and current compiled outputs:
FiniteGridRunLength (150 lines,18 public), SuccessorSequenceHilbert (131,12),
IntegerHatTraceExtension (132,20), FiniteGridTraceData (125,20),
FiniteGridTraceStability (180,18), FinitePathSinePackets (138,15),
FiniteGridTraceSharpness (113,12), FiniteGridTwoSpacingRuns (190,9).
Total 1159 lines, 124 public declarations: 98 theorems,23 definitions,2 abbreviations,
1 instance. Exact axiom audit covers all 124, only propext/Classical.choice/Quot.sound;
eighteen principal signatures and 35 mathlib probes inspected. The main masked
producer bound accepts arbitrary ambient TraceData, with mask mass explicitly
summed over active nodes. Variational corollaries follow the unconditional
curvature-mismatch identity and fix every off-union integer trace to zero.

Eight unique imports wired. All 123 catalog-supported public entries match
exact source lines; the named complete-space instance is separately audited.
Global final lint exits 1 for unrelated concurrent unreachable modules:
CoprimeShearArithmeticWeightsAndChebyshevCellIncrement,
FiniteIntegerTrainCompactness,FiniteIntegerTrainEnergy,FiniteIntegerTrainPackets,
FiniteIntegerTrainPeak,FiniteIntegerTrainPolar,FiniteIntegerTrainProducers,
FoldFreeKernelGramAndFranelGcdCancellation,LocalCoherentFilter,
SignedPrimePolarFactorialLift,SignedPrimePolarFactorialProducer,
SignedPrimePolarHarmonicCorrection,TernaryPacketPolarGrowth,TernaryPacketTrain;
also LEAN_API/LEAN_OVERVIEW drift. No own/proof-debt error; existing large-file
warnings. Refreshed index afterward and reverified own exact coverage. Preserve
other agents' files. Scoped whitespace and stage transition pass. No fullbuild,
numerical experiment, heartbeat increase or added axiom.

Evidence: /tmp/finite-grid-{run,data,stability,sharpness,two-spacing}-build.log,
/tmp/successor-sequence-build.log, /tmp/integer-hat-build.log,
/tmp/finite-path-sine-build.log, /tmp/finite_grid_axioms.lean,
/tmp/finite-grid-axioms.log, /tmp/finite-grid-audit-names.json,
/tmp/finite-grid-api-entries.txt, /tmp/finite-grid-index-post-lint.log,
/tmp/finite-grid-lint-final.log.

Lean proof facts: orthonormal shifted lp.single vectors construct the right
shift directly; its Hilbert adjoint reads successor coordinates. Explicit
HasSum types prevent stuck PreLp coercions when mapping inner products.
Use `change` to expose ambient subtype norms and the concrete identity-map
application before rewriting. Nat.dvd_add_iff_right/left point from the
smaller divisibility statement to the sum; use `.mpr` to remove the known
divisible summand. Finite sine recurrence plus shifted finite sums proves
attainment exactly. Forced alternation proves the four-node two-grid obstruction
within existing heartbeats; broad propositional splitting timed out.
The generated API has hundreds of thousands of rows: stream it once and match
short declaration name, module and source location, not fully qualified names.
Guard potentially long metadata jobs; /tmp/check_finite_grid_catalog.py is the
small verified single-pass checker. Public instances are not catalog rows.

## Certified package 14 — arbitrary-family run-gap classification

For d:ℕ and arbitrary D:Set ℕ, put A(k) iff some e∈{d}∪D has e+2 dividing
k+1. The actual mask-fixed ℓ² space H_A is closed and complete. Its physical
extension E_A(v)=S(v−Rv) realizes every integer/log trace and the exact adjacent
energy, unconditional mismatch and all-integer-trace minimum-energy defect.
All these hold independently of a run bound. E_A is always injective.

Exact unconditional classification:

    closed physical range ↔ positive uniform energy coefficient
                          ↔ uniformly bounded consecutive active runs.

For bounded runs, least exclusion length r≥1 is the attained longest run,
without any periodicity assumption. The actual masked successor is contractive
and nilpotent at r. Sharp factors 2±2cos(π/(r+1)) are attained by finite sine
and alternating packets. If runs are unbounded, least-start sine packets of
length n+1, normalized by their actual ℓ² norm, have norm1 and exact energy
2−2cos(π/(n+2))→0. The unit-data energy infimum is exactly the lower sine
factor in the bounded case and zero otherwise. It is attained iff runs are
bounded. Zero energy is never attained on unit data, by actual trace injectivity.
D=Set.univ supplies a concrete nonclosed-range example with every k≥1 active.

The reverse closed-range implication uses the certified Banach open mapping
theorem: closed range plus unconditional injectivity supplies an antilipschitz
constant, contradicted by the unit near-null packets. No bounded inverse,
summability, analytic admission or spectral gap is assumed in the final
classifiers. This is the fully proved positive survivor of the no-gap obstruction.
Classical parent sine/closed-range results are not claimed externally novel.

Five leaves, 666 lines, 76 public declarations:

| Module | Lines | Public declarations |
|---|---:|---:|
| DivisorGridTraceData |140|23|
| DivisorGridRunGeometry |87|13|
| DivisorGridTraceStability |172|14|
| DivisorGridSinePackets |145|16|
| DivisorGridClosedRange |122|10|

Total: 56 theorems, 18 definitions, one abbreviation and one instance; counted
as one mathematical contribution. All five serial direct leaf checks passed
with empty logs and current normal outputs. Exact all-76 axiom audit passed:
only propext/Classical.choice/Quot.sound. Nineteen principal signatures and
30 mathlib API probes passed and were inspected. Five unique imports and all
75 catalog-supported entries match source locations; named instance separately
audited. Scoped whitespace passes. README fully read and never edited.

Final global lint exits1 only for 15 unrelated unreachable modules:
CoprimeShearArithmeticWeightsAndChebyshevCellIncrement,
FiniteIntegerTrainCompactness, FiniteIntegerTrainEnergy, FiniteIntegerTrainPackets,
FiniteIntegerTrainPeak, FiniteIntegerTrainPolar, FiniteIntegerTrainProducers,
FoldFreeKernelGramAndFranelGcdCancellation, SignedPrimePolarFactorialLift,
SignedPrimePolarFactorialProducer, SignedPrimePolarHarmonicCorrection,
SpectralLaplaceEnergyCriticalLine, TernaryPacketPolarGrowth, TernaryPacketTrain,
WitnessGermOriginMassAndJointTailHeadSynthesis; also LEAN_API/LEAN_OVERVIEW drift.
No own or proof-debt error. Index refreshed afterward; scoped coverage reverified.
No full/umbrella build, numerical experiment, heartbeat increase or added axiom.

Paper: `docs/reports/BiScaleUncertainty/InfiniteDivisorRunGap.md`.
Stage3: `docs/drafts/pipeline/3-formalized/infinite-divisor-run-gap-classification.md`.
Evidence: /tmp/divisor-grid-{data,geometry,stability,packets,closed}-build.log,
/tmp/divisor_grid_axioms.lean, /tmp/divisor-grid-axioms.log,
/tmp/divisor-grid-audit-names.json, /tmp/divisor-grid-api-entries.txt,
/tmp/divisor-grid-index-final.log, /tmp/divisor-grid-lint-final.log.
All owned Lean/search/index/lint jobs terminal at certification. Count14/100;
goal remains active. This turn is progress.

Corpus audit: first hybrid query yielded no candidates; partial=true with
interrupted text/source retrieval and pending coverage generation1445895.
Focused lexical fallback returned20 declaration hits and5 exploration hits,
all inspected. General closed-range interfaces and integer extension occur,
without an arbitrary-family run classifier. Lexical output supplies no semantic
coverage or compiler certification. No absence/novelty conclusion follows.
Primary mathlib Banach operator documentation and Izmestiev's discrete Wirtinger
paper were opened and checked; source links are in the paper proof.

Lean facts: `Filter.tendsto_add_atTop_iff_nat` needs its namespace outside an
`open Filter` scope; shift the scalar sine-gap limit to positive packet lengths.
`ge_of_tendsto'` converts pointwise lower bounds on packet energies to a bound
on the zero limit. Use the complete-space closed-range/antilipschitz theorem
after proving trace injectivity, and square its norm inequality. Subtype norms
can be exposed with `change` before applying interval-packet identities.
Normalize by the actual packet norm; finite sine recurrence gives exact energy
without separately evaluating the sine-square sum. Capture lint stderr as well
as stdout. Stream the API catalog once, matching short names/module/source line.

## Certified package 15 — physical energy completion

For arbitrary d:ℕ,D:Setℕ, let A(k) be the divisor-union active node predicate,
p_n(w)=Σ_(j<n)w_j and C_A={w∈ℓ²:p_(k+1)(w)=0 whenever ¬A(k)}. This is a
closed complete Hilbert domain. Unit-cell synthesis S gives an actual isometric
physical extension with primitive at n equal to p_n(w), logarithmic trace at
log(k+1) equal to p_(k+1)(w), and energy Σw_k².

Exact unconditional identification:

    closure(range E_A) = S(C_A).

This equality is in the full physical L² space and explicitly retains cellular
membership. C_A is exactly the zero-sum space on every finite active-edge
component [a,b). Its orthogonal complement in ℓ² consists exactly of currents
constant along each active edge; these are constant on finite components and
zero on infinite active tails. The proof uses least missing edges, finite
prefix conservation and ℓ² tail decay, followed by Hilbert orthogonal
decomposition. No spectral gap or closed-range premise is assumed.

The completed trace v_k=p_(k+1)(w) has discrete gradient w. It need not belong
to ℓ². Exact recovery: S(w) has an old ℓ² divisor-trace preimage iff v∈ℓ²;
the preimage is unique by the existing trace injectivity theorem. Every
completed datum is recoverable iff active runs are uniformly bounded. With
unbounded runs, an actual completed datum outside the old range exists.
General-family existence is not claimed to give a quantitative coordinate
formula. Projection onto the proved closed C_A constructs admitted data from
every ambient current, with exact physical-energy plus projection-error
Pythagoras and an unconditional contraction bound.

Explicit full-family producer: D=ℕ gives C_A={w:w_0=0}. The unit current δ_1
synthesizes unitCell1, has energy1, and has cumulative trace0 at index0 and1
at every later index; hence no old ℓ² preimage. For N=n+1, finite old trace
data v_N(1+j)=1−j/N, 0≤j<N, satisfy

    G(v_N)=δ_1−(1/N)Σ_(j<N)δ_(j+2),
    ‖E(v_N)−unitCell1‖²=1/N →0.

A compensating return current spread over N cells costs only1/N energy.
Finite-component conservation survives completion because finite sums are
bounded; total-current conservation on an infinite component can disappear.
This is a concrete producer with exact error, consistent with Trap10 while
remaining within continuum coprime shear. No RH, full SourceGraph, affine
unitary or unweighted logarithmic H1 identification is claimed.

Five leaves / lines / public declarations:
CellPrefixHilbert107/17, DivisorCellConstraints195/16,
DivisorGradientClosure110/8, DivisorEnergyCompletion152/19,
FullDivisorEnergyEscape135/13. Total699 lines and73 public declarations:
59 theorems,12 definitions, one abbreviation and one instance. Counted once.
All five serial direct leaf checks pass with empty logs and current normal
compiled outputs. Exact all-73 axiom audit passes with only propext,
Classical.choice,Quot.sound;13 principal signatures inspected and52 mathlib
API probes checked. Five unique imports and all72 catalog-supported entries
match source locations; instance separately audited. Scoped whitespace passes.
README fully read,260 lines, never edited. No full build or heartbeat increase.

Global lint --check-generated exits1 only for six unrelated unreachable
modules: AntitoneDyadicStencil, BandLimitedLaplaceEnergy, ClampedExponentialRamp,
FiniteFilterSchurResidual, NyquistResidualMass, SignedPrimePolarContinuousFactorialLift.
No own, proof-debt or generated-index error; existing large-file warnings.
Paper: `DivisorTraceEnergyCompletion.md`, written before Lean.
Card: `docs/drafts/pipeline/3-formalized/divisor-trace-energy-completion.md`.
Evidence: /tmp/trace_completion_axioms.lean, /tmp/trace-completion-axioms.log,
/tmp/trace-completion-audit-names.json, /tmp/trace-completion-api-entries.txt,
/tmp/trace-completion-index-final.log, /tmp/trace-completion-lint-final.log.
All owned jobs terminal. Certified15/100; overall goal remains active.

Corpus search: all20 candidates and20 source-argument statements inspected.
partial=true, text/source retrieval interrupted, generation1446063 pending,
refresh incomplete/background_indexer_running, compiler metadata source-only.
No matching completion classifier appeared; this is not an absence or novelty
proof. MIT18.102 orthogonal-decomposition/range-kernel theory and mathlib
projection documentation checked as classical parents; paper contains links.

Lean facts: simplify inner-prefix cell terms before rewriting arbitrary
inner-prefix expressions as primitives. Expose continuous-linear-map and
submodule/set coercions with `change` or `rfl`; simplification need not unfold
them. Give omega the interval endpoint inequality explicitly. Inner products
of real lp singles simplify to scalar multiplication with the relevant one
on the left. Full-family ramp data need their definition explicitly unfolded
when using intervalTraceData_at. No heartbeat changes were needed.

## Certified package 16 — explicit component averaging and best approximation

For arbitrary divisor family d,D, let A(k) be its active-edge predicate and
C_A its certified completed current space. The canonical first missing edge
e(k) identifies every finite component I_j=[s(j),j+1) exactly once, at its
missing endpoint j. Components have positive length L_j. An endless active
tail receives zero mean correction.

For actual w∈ℓ², construct μ_w(k) as its finite-component average, or zero
on an infinite tail. Then μ_w=w−P_Cw, so μ_w is square-summable and
c_w=w−μ_w belongs to C_A. Neither membership nor convergence is assumed.
The nonnegative endpoint charges Γ_j(w)=(Σ_Ij w)²/L_j at missing edges,
zero at active edges, form a convergent series with sum ‖μ_w‖². Proof:
group the actual summable squared residual by canonical endpoint fibres.

For every physical q∈L²(ℝ), B=S* is actual bounded cell analysis,
b_k=(Bq)_k=∫_(k,k+1]q=F(k+1)−F(k), F(t)=∫₀ᵗq. The explicit producer
P_Aq=S(c_b) has range exactly closure(range E_A), is idempotent and
contractive, and has cell coefficients b_k−μ_b(k). Its exact error is

    ‖q−P_Aq‖² = ‖q−Qq‖² + Σ_(j:¬A(j))(F(j+1)−F(s(j)))²/L_j,
    Qq=S(Bq).

The arithmetic series is proved convergent for every q,d,D. For every
completed competitor v, the excess squared error equals ‖c_b−v‖²,
proving unique best approximation. There is no finite-family, run-gap,
trace-summability or physical-domain admission premise.

The negative half-line is explicit: q⁻=1_(-∞,0]q is an actual L² class,
Bq⁻=P_Aq⁻=0, and

    ‖q−Qq‖²=∫_(-∞,0]q²+‖q−q⁻−Qq‖².

The first producer cell and primitive trace at1 vanish. For D=ℕ,
P_Aq=Qq−b_0 unitCell0 and error=‖q−Qq‖²+b_0². This explicitly handles
the nonclosed old-range case. Trap10 directs this contribution toward an
instantiated producer with unconditional exact error, within continuum shear.
No factorial/RH receiver, full SourceGraph, affine-unitary or unweighted
logarithmic H1 identification is claimed.

Five leaves / lines / public declarations: DivisorCellEndpoints137/17,
DivisorComponentAverages129/16, DivisorComponentCharge83/7,
PhysicalCellAveraging136/19, DivisorPhysicalProjection226/28.
Total711 lines,87 public declarations:72 theorems and15 definitions.
All five serial direct leaf checks pass without diagnostics. All87 public
axiom checks pass with only propext,Classical.choice,Quot.sound;17 principal
signatures inspected and50 mathlib API probes checked. Five unique imports
and87 catalog entries match source locations. README fully read, read-only.
Paper preceded Lean; no full build, numerical experiment or heartbeat increase.

Global lint --check-generated exits1 for eight unrelated unreachable modules:
DyadicRenewalChain, ExponentialTentMoments, NyquistPolarSourceEscape,
PhysicalCollarMixture, PhysicalPriceResponse, RegularizedGramGeometry,
RegularizedPhysicalGram, SignedPrimePolarSourceParameters; also concurrent
LEAN_API/LEAN_OVERVIEW drift. No own or proof-debt error. Index refreshed
after lint; own catalog coverage checked separately. Do not claim global lint
passed. Exact evidence: /tmp/divisor-averaging-{axioms,lint-final,index-post-lint}.log,
/tmp/divisor-averaging-audit-names.json, /tmp/divisor-averaging-api-entries.txt,
/tmp/divisor-averaging-lint-errors.json, /tmp/divisor_averaging_axioms.lean.
Paper: `DivisorComponentAveragingProjection.md`. Card:
`docs/drafts/pipeline/3-formalized/divisor-component-averaging-projection.md`.
Counted once; certified16/100, overall goal active.

Corpus: all20 candidates and20 source arguments inspected; partial=true,
text/source interrupted, snapshot1446427 vs current1446428, refresh incomplete,
compiler coverage mostly pending/source-only. Existing component/closed-space
results reused; search gives no absence or external novelty proof. Primary
MIT18.102 orthogonal-decomposition and official mathlib projection sources
checked as classical parents; paper links them.

Lean facts: parenthesize a squared norm used as a HasSum argument, otherwise
parsing can attempt to square a proposition. Use an explicitly typed calc step
with Finset.tsum_subtype' when coercion transparency defeats rw. Nat.card_Ico
is the interval cardinality theorem. To prove a zero tsum, establish every
summand zero and simplify with tsum_zero. Actual MemLp.indicator.toLp and
ae_restrict_mem give the physical negative-half-line split directly.

## Next unproved candidate — integer dilation and cell coisometry

`docs/drafts/pipeline/0-backlog/integer-dilation-cell-coisometry.md`.
Construct actual A_mq(t)=m q(mt) and B_mw(j)=Σ_(r<m)w(mj+r), prove
cell-analysis intertwining, exact coisometry/adjoint and the convergent
infinite variance defect; seek B_m R^m=R B_m. No Lean assigned, uncounted.
All20 candidates and20 source arguments inspected; existing finite dilated
trace defects are parents. Search partial, text/source interrupted,
generation1446587 pending, refresh incomplete. Draft hits were unverified
and not independent evidence. Reaudit before paper proof. Do not assume
completed divisor spaces are dilation-invariant: the first trace becomes F(m).
