# Continuum coprime shear: knowledge ledger

## Scope and certified contribution count

Target: 100 substantive mathematical packages in continuum coprime shear and
multiplicative/additive regularity. Certified packages: **5 / 100**. Supporting algebra,
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
2. Infinite coprime trace domains beyond the certified finite interpolants.
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

## Next falsifiable candidate — actual rough modulus and nodal defect

Backlog card: `docs/drafts/pipeline/0-backlog/rough-sobolev-modulus-nodal-defect.md`.
Construct the L² velocity `q_abs(t)=sign(c+primitive q t)*q(t)` and prove
`|c|+primitive q_abs t=|c+primitive q t|`, including the derivative-zero law
on the state's zero-level set. Prove equality of local physical Dirichlet energies
and exact actual mixed-graph identity `J(q)=J(q_abs)+nodalEnergy(q,c)`; the
existing nodal energy already includes factor 4. Weighted source mass is unchanged.

Focused search `absolute value Sobolev primitive nodal jump decomposition`
completed without errors or partial results. All candidate and source-argument
entries were inspected. Existing finite/continuous nodal algebra and extended
mixed-graph bounds do not construct the modulus in the actual rough L² primitive
domain. Coverage warnings remain; classical chain-rule and Dirichlet-form
ingredients carry no novelty claim. This candidate is unproved and not counted.
This turn is **progress**. Goal remains active at **5/100**.
