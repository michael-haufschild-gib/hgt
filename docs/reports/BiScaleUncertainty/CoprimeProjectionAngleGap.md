# Sharp arithmetic angles and alternating coprime projections

Let m,n≥2, let P,Q be the actual infinite tent projections, and let R be the
projection for spacing lcm(m,n). Define

    c(m,n)=0                   if gcd(m,n)≥2,
           1/2                 if gcd(m,n)=1 and min(m,n)=2,
           1/4                 otherwise.

The exact laws to formalize are

    ‖PQ−R‖²=c(m,n),
    ‖PQ−QP‖²=c(m,n)(1−c(m,n)),
    (PQ−R)²=c(m,n)(PQ−R).

Consequently, for every integer k≥1,

    (PQ)^k−R=c(m,n)^(k−1)(PQ−R),
    ‖(PQ)^k−R‖²=c(m,n)^(2k−1).

These are unconditional laws for the concrete operators. Square roots give
the proposed product norms 1/2 and 1/√2, and commutator norms √3/4 and 1/2.

## Arithmetic component classification

Normalize each tent H_a to e_a=H_a/√2. Within either spacing family the
vectors are orthonormal. Across families their pairings are 1 at equal
centers, −1/2 at adjacent centers, and zero otherwise, by package 10.

Coincident centers are isolated: every other center in either family is at
least two integer units away. They span precisely the common range R.

If both spacings are at least three, an integer center can have at most one
adjacent center in the other family. Indeed, its two potential neighbors are
two units apart and cannot both be multiples of a spacing at least three.
Thus each remaining nonzero cross interaction is an isolated edge. Its two
unit vectors have inner product −1/2. All other active centers are isolated.

If m=2 and gcd(m,n)=1, then n≥3 is odd. Even n-centers are coincident centers.
Each odd n-center b is at least three and has exactly two positive even
neighbors b−1,b+1. Each of these even centers has no other adjacent n-center,
because n≥3. Thus each remaining interacting component is a two-edge star.
The positive-half-line boundary removes no arm: b≥3. Exchanging m,n treats
n=2. The case m=n=2 has already been classified as commuting.

For a star with orthogonal unit arms e₁,e₂ and center f, set
u=(e₁+e₂)/√2 and w=(e₁−e₂)/√2. Then u,w are orthonormal,
⟨u,f⟩=−1/√2 and ⟨w,f⟩=0. The w direction is a one-sided projection
component; the interacting two-dimensional component has squared angle cosine
1/2. For an isolated edge that value is 1/4.

Distinct components are mutually orthogonal, by all same- and cross-family
pairings. Finite sums of their vectors are dense in the sum of the two closed
tent spans. Both projections vanish on its orthogonal complement. Hence a
bounded operator identity proved on every component extends to the full L²
space; no finite truncation or sampled matrix is used.

## Exact two-dimensional identities and sharpness

In an interacting component choose a unit vector u in the P range, write the
Q-range unit vector as f=ρu+sqrt(1−ρ²)v with u,v orthonormal, and put c=ρ².
Here c is 1/4 or 1/2. Relative to u,v,

    P = [1 0; 0 0],
    Q = [c ρsqrt(1−c); ρsqrt(1−c) 1−c].

Direct symbolic multiplication gives (PQ)²=cPQ and
(PQ−QP)²=−c(1−c)I on this component. Also
‖PQx‖²≤c‖x‖², with equality at x=f; the commutator has norm squared
c(1−c) on every vector in the interacting component. One-sided components
give zero products and commutators. On coincident components PQ=R=I.

For coprime m,n, package 10's positive adjacent multiples guarantee at least
one interacting component. Therefore both norm bounds are attained, so the
constants are exact. For noncoprime m,n package 10 proves PQ=QP=R, giving zero.
Orthogonal summation and continuity prove all stated global identities.

## Operator-algebra realization without an admitted decomposition

The formal proof may avoid constructing an explicit Hilbert direct sum. The
single-neighbor projection formula is P H_b=−H_a/2. The two-neighbor formula
is P H_b=−(H_a+H_a')/2. Both follow from every analysis coefficient, using
the actual finite ℓ² data and existing synthesis. Applying these identities
twice gives T²=cT for T=PQ−R on every Q-tent. Since TQ=T, the actual convergent
Q-tent series extends this to an operator identity on all L² inputs. Taking
adjoints covers the exchanged spacing-two case.

Projection algebra then gives A=TT*=PQP−R, A*=A, and A²=cA. The C*-norm
identity yields ‖T‖²=‖A‖ and ‖A‖²=c‖A‖. Existing noncommutation implies
T≠0, hence A≠0, so ‖T‖²=c. For K=PQ−QP, projection algebra and T²=cT
give K*=-K and K³=−c(1−c)K. Thus B=K*K=−K² is self-adjoint,
B²=c(1−c)B, and K≠0 yields ‖K‖²=c(1−c). These identities establish both
upper bounds and sharpness directly in the infinite operator algebra.

Norm attainment is also constructive at the operator level. For a nonzero
operator S with A=S^* S and A²=λA, A is nonzero by the C*-identity. Choose x
with Ax≠0 and put q=Ax. Then Aq=λq, so ‖Sq‖²=⟨Aq,q⟩=λ‖q‖².
Apply this to S=T and S=K. In the commuting case any nonzero tent supplies
a norm attainer for the zero operator. Thus both attainment statements
quantify all spacings, without an existence or spectral premise.

Finally RT=TR=0 and R²=R. Induction gives (R+T)^k=R+c^(k−1)T for k≥1,
including c=0. The norm identity above gives the exact alternating-product law.

## Parent theory and scope

The general link between Friedrichs angles and alternating projections is
classical; see [Badea–Grivaux–Müller, §1](https://users.math.cas.cz/~muller/BGM_cras.pdf).
The arithmetic pair/star classification and exact constants are derived here
from the constructed tents. No external novelty claim for two-subspace theory.
This is operator uncertainty inside the physical Dirichlet velocity space;
it does not identify a unitary affine representation or a closed SourceGraph form.

## Formal realization

All laws above, including both norm-attainment statements and every positive
iterate, are formalized in four leaves under `SobolevShear`:
`CoprimeProjectionNeighbors`, `CoprimeProjectionAnglePolynomial`,
`CoprimeProjectionAngleNorm`, and `CoprimeAlternatingProjectionRate`.
The main norm and iteration statements quantify all d,e,k∈ℕ without premises.
There are 41 public theorems and four definitions, audited as one contribution.
All direct checks and all 45 public axiom audits pass, using only `propext`,
`Classical.choice`, and `Quot.sound`. Twelve main signatures were inspected.
The knowledge ledger records index/import checks and repository-wide lint status.
