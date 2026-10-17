# Physical energy completion of arbitrary divisor traces

Status: formalized as contribution15/100. The dependency-closed paper proof
preceded formalization. Five direct leaf checks and the exact all-73-declaration
axiom audit pass; only propext, Classical.choice and Quot.sound occur.

## Explicit complete domain

Fix d∈ℕ, D⊆ℕ and A(k) iff ∃e∈{d}∪D with e+2 dividing k+1.
For cell coefficients w∈ℓ²(ℕ), define the finite prefix functional
p_n(w)=Σ_(j<n)w_j. Each p_n is bounded, represented by a finite indicator vector.
The concrete complete energy domain is

    C_A={w∈ℓ² : p_(k+1)(w)=0 whenever A(k) is false}.

It is an intersection of closed kernels. Unit-cell synthesis S is the existing
linear isometry into physical L². For w∈C_A the physical state F_w(t)=∫₀ᵗS(w)
has integer values F_w(n)=p_n(w), and logarithmic values
f_w(log(k+1))=p_(k+1)(w). Its exact energy is ‖S(w)‖²=Σw_j².
The completed trace is v_k=p_(k+1)(w); v_0=w_0 and v_(k+1)−v_k=w_(k+1).
No ℓ² condition on these cumulative traces is imposed.

For arbitrary ambient w∈ℓ², orthogonal projection onto the proved closed C_A
followed by S constructs an admitted producer. Its physical energy plus the
squared coefficient projection error equals ‖w‖², giving an unconditional
quantitative error identity and contraction bound.

## Exact range closure

Let G_A(v)=v−Rv on the old mask-fixed ℓ² trace space. Prefix telescoping gives
p_(k+1)(G_Av)=v_k, so its range lies in C_A. Put M=closure(range G_A).
Since C_A is closed, M⊆C_A.

For w∈C_A, decompose w=m+z with m∈M and z∈M⊥ by Hilbert projection.
Then z∈C_A. Each active edge k admits the old datum δ_k; its gradient is
δ_k−δ_(k+1), so orthogonality gives z_k=z_(k+1) whenever A(k).
These local equalities and the zero inactive prefixes force z=0:

- Use strong induction at cell j, so earlier coefficients already vanish.
- If there is a missing edge at or after j, take the first one j+r. Constancy
  on the intervening active edges makes z_j,…,z_(j+r) equal. The zero prefix
  at j+r+1 is therefore (r+1)z_j, giving z_j=0.
- Otherwise z has a constant infinite tail beginning at j. The squares of an
  ℓ² sequence tend to zero, forcing that constant to vanish.

Thus C_A=M. Since S is an isometry of a complete space, it is a closed embedding
and carries closures to closures. Consequently

    closure(range E_A)=S(C_A),

as subsets of the full physical L² space. This explicitly retains cellular
membership; a noncellular physical velocity is not silently admitted.

## Finite components and conservation

A finite component of the active-edge cell graph is an interval [a,b), a<b,
with a=0 or edge a−1 missing, edge b−1 missing, and every internal edge active.
Its coefficient sum is p_b(w)−p_a(w). The prefix criterion implies that every
such sum is zero. Conversely, the component ending at any missing edge k can
be constructed recursively: start(0)=0 and
start(k+1)=start(k) if A(k), otherwise k+1. Induction proves it is the left
endpoint of that component. Strong induction over missing edges then shows
all p_(k+1) vanish from component conservation. Hence C_A is exactly the
cellular finite-component conservation space.

The gradient-range orthogonal complement consists exactly of ℓ² sequences
constant along active edges. They are constant on every finite component and
zero on every infinite active tail. The converse orthogonality follows by
pairing with the actual convergent single-coordinate synthesis of old data.

## Exact recovery and completion defect

For w∈C_A, S(w) belongs to the old interpolation range exactly when the
cumulative trace k↦p_(k+1)(w) is square-summable. In that case it defines the
unique old datum: support follows from the C_A constraints and its discrete
gradient is w. Conversely, every old preimage has those exact traces.

Therefore every completed datum has an old ℓ² preimage iff active runs are
uniformly bounded, by the already proved closed-range classification.
If runs are unbounded, the strict inclusion range E_A⊊S(C_A) proves the
existence of an actual completed datum with no ℓ² preimage. A general-family
witness may be selected from this proved nonempty difference; no quantitative
formula for that selection is claimed. The following concrete witness and
approximating producers have fully explicit formulas and errors.

## Explicit full-family escape with exact approximation error

For D=ℕ, A(k) iff k≥1, so C_A={w:w_0=0}. Take w=δ_1 and q=S(w)=unitCell1.
The completed trace is 0 at k=0 and 1 for every k≥1. It is not square-summable,
although q has unit physical energy.

For N≥1 define actual old trace data supported on k=1,…,N by

    v_N(1+j)=1−j/N,  0≤j<N.

Direct subtraction gives

    G_A(v_N)=δ_1−(1/N)Σ_(j<N)δ_(j+2),
    ‖E_A(v_N)−unitCell1‖²=1/N →0.

Thus the completed state and its approximation are concrete producers, with
an unconditional exact error. Finite traces can converge in physical energy
while their limiting trace sequence exits ℓ². Completion is not a missing
spectral premise; it is an explicitly identified larger domain.

The compensating return current has total mass −1 spread over N cells, with
energy cost 1/N. Conservation on finite components survives completion because
finite sums are bounded functionals. A total-current constraint on an infinite
component can disappear as its return current spreads farther out.

## Provenance and scope

Hilbert orthogonal decomposition and range/kernel duality are classical; see
[MIT 18.102 notes, Theorem189](https://ocw.mit.edu/courses/18-102-introduction-to-functional-analysis-spring-2021/8fb8d5c170f1613151aca71de21027bc_MIT18_102s21_full_lec.pdf)
and [mathlib projection theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Basic.html).
No external novelty claim is made for those parent tools. The contribution is
the exact physical arithmetic completion, conservation law, cumulative recovery
criterion and explicit escaping trace producer in the existing shear framework.

All20 candidate lemmas and20 source arguments from the current corpus query
were inspected. Hits include existing integer minimum-energy and run-gap laws,
plus unrelated compact-source and collar energies; no completion classifier
appeared. Search partial=true, text/source retrieval interrupted, generation
1446063 pending, background refresh incomplete; compiler metadata source-only.
This does not establish absence or external novelty. README remains read-only.
No RH work, full affine-unitary action or unweighted logarithmic H1 claim.

## Formal certificate

Leaves: CellPrefixHilbert, DivisorCellConstraints, DivisorGradientClosure,
DivisorEnergyCompletion, FullDivisorEnergyEscape. Total699 lines, 73 public
declarations: 59 theorems, 12 definitions, one abbreviation and one instance.
All five serial `lake --old env lean -o <normal-output> <leaf>` checks pass
without diagnostics; compiled outputs are current. The scratch audit
`/tmp/trace_completion_axioms.lean` covers every public declaration,13 principal
signatures and52 mathlib API probes. Five unique umbrella imports and all72
catalog-supported entries match current source locations; the instance is
separately axiom-audited. No full/umbrella build or heartbeat increase.

Global `lint --check-generated` exits1 solely for six unrelated unreachable
modules: AntitoneDyadicStencil, BandLimitedLaplaceEnergy, ClampedExponentialRamp,
FiniteFilterSchurResidual, NyquistResidualMass, SignedPrimePolarContinuousFactorialLift.
No own, proof-debt or generated-index error. Existing large-file warnings remain.
Logs: `/tmp/{cell-prefix-hilbert,divisor-cell-constraints,divisor-gradient-closure,
divisor-energy-completion,full-divisor-energy-escape}-build.log`,
`/tmp/trace-completion-{axioms,index-final,lint-final}.log`.
