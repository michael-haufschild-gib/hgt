# Coprime Sobolev trace realization

## Precise theorem and proof

Let q be any real L2 velocity on the physical line and F(t)=∫₀ᵗq. Then F is
locally absolutely continuous and F'=q almost everywhere. For a<b, L=b−a,
Δ=F(b)−F(a), square completion gives

    ∫ₐᵇ(Lq−Δ)² = L²∫ₐᵇq²−LΔ².

All terms are integrable: local L1 follows from L2 on finite-measure intervals,
and q² is globally L1. Thus the previous C1 trace identity extends to actual
Sobolev representatives, including piecewise affine interpolants.

For finite traces v(0),...,v(N), define the concrete step velocity

    Q_v(t)=Σ_{j<N}(v(j+1)−v(j)) 1_(j,j+1](t).

The intervals are disjoint and have length one. Hence Q_v belongs to L2,

    ∫ Q_v² = Σ_{j<N}(v(j+1)−v(j))²,
    v(0)+∫₀ᵐQ_v = v(m)                    (0≤m≤N).

On each cell the primitive is the affine interpolant. For any other L2 velocity
with the same nodal increments, summing the unit-cell square completions gives
the exact orthogonal energy decomposition

    ∫₀ᴺq² = Σ_{j<N}(v(j+1)−v(j))²
              + Σ_{j<N}∫ⱼ^{j+1}(q−(v(j+1)−v(j)))².

The step extension therefore attains the least energy; equality means the
velocity agrees with Q_v almost everywhere on [0,N].

## Coprime specialization

For arbitrary amplitude data a, d≥2, and N≥0, construct

    v(j)=a(j) if 0<j<N and d divides j; v(j)=0 otherwise.

Adjacent traces cannot both be active. Therefore v(j)v(j+1)=0 and

    Σ_{j<N}(v(j+1)−v(j))² = 2Σ_{j<N}v(j)².

The two endpoint values vanish. This constructs, without a trace-support premise,
a locally absolutely continuous interpolant whose energy is exactly twice the
squared active trace norm. Any competing Sobolev interpolant with those traces
pays that energy plus the nonnegative interpolation defect. This is the sharp
continuum version of Pillar VII's coprime successor coercivity.

In logarithmic coordinates f(x)=F(exp x), set r(x)=exp x q(exp x). Monotone
change of variables proves r is locally L1 and
f(b)−f(a)=∫ₐᵇr. Hence f is locally absolutely continuous and f'=r almost
everywhere by the Lebesgue differentiation theorem. Applying the measurable
Jacobian formula again to q² proves both integrability and the exact identity

    ∫ₐᵇ exp(−x)|f'(x)|² dx = ∫_(exp a)^(exp b) q(t)² dt.

For the constructed divisor trace, v(0)=v(1)=v(N)=v(N+1)=0. Its velocity
vanishes on (0,1] and (N,N+1]; additivity of interval energy therefore gives

    ∫₀^(log(N+1)) exp(−x)|f'(x)|² dx = 2Σ_{j<N}v(j)².       (1)

This covers N=0 and N=1 as zero cases. Nonvacuity is explicit: for N=d+1,
the primitive at the active node d realizes the arbitrary amplitude a(d).
Lean uses the parameter d+2 to encode divisors at least two without a premise.

For any competing L2 velocity q, write Fq(t)=∫₀ᵗq, sj=v(j+2)−v(j+1),
and ej=Fq(j+2)−Fq(j+1)−sj. The shifted slope energy is still 2Σv², since
the omitted first slope and the added last slope both vanish. Expanding the
square on each positive cell proves the unconditional identity

    ∫₀^(log(N+1)) exp(−x)|(Fq∘exp)'(x)|² dx
      = 2Σ_{j<N}v(j)² + 2Σ_{j<N}sj ej
          + Σ_{j<N}∫_(j+1)^(j+2)(q(t)−sj)² dt.             (2)

Thus the trace error is explicit; it has not been assumed away. Dropping the
nonnegative last term gives the formal lower bound. Matching nodal increments
sets every ej to zero, and the constructed velocity attains the bound. The
paper equality characterization follows from the zero integral criterion for
nonnegative integrable squares; the current formal API exposes the exact defect
and attained value, not a separate global uniqueness theorem.

Finally, for every q in this L2 velocity space and b≥0, the interval trace bound
on [exp x, exp x+b] gives the actual rough-state nonlinear shear inequality

    |f(log(exp x+b))−f(x)|²
      ≤ b∫_x^(log(exp x+b)) exp(−y)|f'(y)|² dy.

These are statements about homogeneous Dirichlet representatives. No global
unweighted L2 mass, identification with mathlib's Bessel-potential `MemSobolev`,
infinite SourceGraph-domain admission, or unitary affine representation is claimed.

## Scope and prior art

This is a constructive arithmetic/logarithmic bridge, not a novelty claim for
piecewise linear finite elements. Hat-function interpolation is classical; see
Driscoll–Braun, [*Fundamentals of Numerical Computation*, §5.2](https://fncbook.com/pwlin/).
The corpus search found L2 integrability and absolute-continuity machinery but no
applicable arithmetic Sobolev trace realization. Search completed without errors;
semantic coverage was unmeasured and the coverage snapshot lagged the index.

Status: certified package 2/100. Four direct Lean leaves pass without diagnostics;
all 55 public theorem axiom reports use only standard Lean axioms. Imports are wired
and indexes refreshed. Global lint reports two unrelated concurrent missing imports;
see `ContinuumCoprimeShear-FACTS.md` for exact evidence and scope.
