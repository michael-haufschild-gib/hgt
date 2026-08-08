# Maximal-volume replica target-skeleton law

- **ID:** `maximal-volume-replica-target-skeleton-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Parent:** `return-excised-replica-coarea-incidence-law.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [FRONTIER ADVANCE] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-07
- **Statement:** A maximal-volume basis of the occupied replica target image replaces the complete target union by at most its Hilbert-number many fixed-target moments, with a universal Hilbert-number Cauchy cost and no circuit-label entropy.

## Goal

The return-excised pair law reduced complete shortcut capture to an occupied-image compressed
collision.  A hostile attack exposes a remaining obstruction: compressed pair overlap is not
bounded by physical source-pair fidelity.  Orthogonal full vectors can have parallel projections.
Consequently an ordinary recurrence tail cannot by itself bound the compressed collision.

Replace projection covariance by a target skeleton whose members are actual occupied circuit
endpoints.  Then every term requiring anti-concentration is a genuine fixed-target replica moment,
to which the existing spectral-action and weighted-crowding machinery can apply.

## Gates

- [x] 0 -> 1 in-progress: exact conjecture, falsification chain, proof, and Door passport fixed
- [x] 1 -> 2 fully-proven: dependency-closed paper proof below
- [x] 2 -> 3 formalized: maximal-volume coefficient theorem and complete-incidence capstone
- [ ] 3 -> 4 publication-ready: only after ordinary-local-Hamiltonian moment decay and priority audit

## Frozen theorem

Let `Z = {z_c : c in C}` be a finite family in a finite-dimensional complex Hilbert space.  At
replica order `r >= 1`, put

```text
v_c = z_c^(tensor r),
S_r(Z) = span_C {v_c : c in C},
h = dim_C S_r(Z).
```

If `h > 0`, there are indices `c_1,...,c_h` in `C` such that:

```text
v_c = sum_(j=1)^h a_j(c) v_(c_j),    |a_j(c)| <= 1          (MV1)
```

for every `c`.  Therefore every replica source vector `u` satisfies

```text
max_c |<u,v_c>|^2
  <= h sum_(j=1)^h |<u,v_(c_j)>|^2.                         (MV2)
```

For a finite source measure `mu`, source state `psi`, fidelity threshold `a > 0`, and

```text
E_a = {x : exists c, a <= |<psi(x),z_c>|^2},
```

the complete-union bound is

```text
a^r mu(E_a)
  <= h sum_(j=1)^h integral |<psi(x),z_(c_j)>|^(2r) dmu(x). (MV3)
```

Hence a uniform fixed-target moment ceiling `M_r` on the selected occupied skeleton gives

```text
mu(E_a) <= h^2 M_r / a^r.                                  (MV4)
```

No cardinality of circuit descriptions or of the original target family occurs.

## Conjecturing protocol

### C0 -- physical pair-fidelity tails control the compressed pair kernel

Conjecture:

```text
k_(r,Z)(x,y) <= |<psi(x),psi(y)>|^(2r).
```

**Verdict:** `[FALSIFIED]`.

Orthogonal projection is contractive in norm but not in pairwise inner-product magnitude.  In
`C^2`, take `u=(e_1+e_2)/sqrt(2)`, `v=(e_1-e_2)/sqrt(2)`, and project to `span(e_1)`.  Then
`<u,v>=0` while `<Pu,Pv>=1/2`.  Replica physical-recurrence tails therefore do not control the
occupied-image compressed collision.

**Positive survivor:** use actual occupied targets, not their projection kernel.

### C1 -- choose an arbitrary occupied target basis

Conjecture: any target basis gives coefficient-uniform complete-union control.

**Verdict:** `[FALSIFIED]`.

An arbitrarily ill-conditioned target basis has arbitrarily large expansion coefficients.  Linear
dimension alone does not control a chosen basis.

**Positive survivor:** choose a basis maximizing absolute determinant among all target `h`-tuples.

### C2 -- maximal-volume occupied skeleton

**Verdict:** `[PROVED HERE]`.

Choose coordinates on `S_r(Z)` and, among the finitely many ordered `h`-tuples of target vectors,
choose `B=(v_(c_1),...,v_(c_h))` maximizing `|det B|`.  Since the target family spans `S_r(Z)`, one
tuple has nonzero determinant; therefore the maximizer is a basis.

For a target `v_c`, write `v_c=B a(c)`.  Replacing column `j` of `B` by `v_c` multiplies its
determinant by `a_j(c)` by Cramer's rule.  Maximality gives

```text
|det B| |a_j(c)| <= |det B|.
```

Since `det B != 0`, cancellation proves `|a_j(c)| <= 1`, which is `(MV1)`.

### C3 -- D-optimal weights reduce `h^2` to `h`

Conjecture: there are occupied-image weights whose maximum leverage is exactly at most `h`, giving
an `h` rather than `h^2` fixed-target cost.

**Verdict:** `[KNOWN DESIGN-THEORY DIRECTION / NOT USED HERE]`.

This is the Kiefer--Wolfowitz D/G-optimal equivalence.  Importing it as the claimed frontier advance
would be rediscovery, while formalizing its convex-optimization existence theory would not supply
the still-missing local-Hamiltonian moment decay.  The maximal-volume skeleton is weaker by one
factor `h` but elementary, exact, finitely supported on actual targets, and sufficient to change
the remaining physics input.

## Dependency-closed proof of the incidence law

Fix `x`, put `u=psi(x)^(tensor r)`, and suppose target `c` captures `x`.  Tensor inner products
factor, so

```text
a^r <= |<u,v_c>|^2.
```

Using `(MV1)` and Cauchy--Schwarz in `C^h`,

```text
|<u,v_c>|^2
 = |sum_j a_j(c) <u,v_(c_j)>|^2
 <= (sum_j |a_j(c)|^2) (sum_j |<u,v_(c_j)>|^2)
 <= h sum_j |<u,v_(c_j)>|^2.
```

This proves the pointwise event domination `(MV2)`.  Integrating over every source point proves
`(MV3)`; no source fibre is quotiented.  If every selected moment is at most `M_r`, the sum has `h`
terms and `(MV4)` follows.

Duplicate labels cannot change the maximal attainable determinant or `h`; a skeleton may select one
representative of each occupied vector.  At positive replica order, zero target residues never
occur in a nonzero determinant and are automatically omitted.  Thus exact-return removal is built
into maximal-volume selection.

## Frontier movement

The previous hard quantity was

```text
one compressed covariance collision on S_r(Z),
```

whose pair kernel suffers projection cancellation.  The new hard quantities are

```text
at most h_r(Z) genuine fixed-target replica moments,
```

with total geometric cost `h_r(Z)^2`.  This is independent of target labels and can be combined
directly with targetwise spectral-action or Gaussian anti-concentration estimates without a union
over all circuit descriptions.

For a circuit image of positive algebraic dimension, `h_r(Z)` is its degree-`r` homogeneous Hilbert
function.  Thus the circuit side is polynomial in growing replica order whenever that Hilbert
function is polynomial, rather than exponential in word count.  The statement does not assert such
a polynomial bound for any circuit model until its Hilbert function is separately proved.

## Hostile novelty audit

- Maximal-volume submatrix coefficient bounds, Cramer's rule, Auerbach bases, and Cauchy--Schwarz are
  classical and are not novelty claims.
- D-optimal design can improve the skeleton factor and is explicitly acknowledged rather than
  rediscovered.
- Candidate application novelty is the exact composition with the occupied return-removed Veronese
  circuit image: complete quantum shortcut capture is reduced to Hilbert-number many actual
  fixed-target moments, avoiding both circuit-label entropy and projection-covariance cancellation.
- Targeted searches did not locate this recurrence/complexity composition.  Search noncollision is
  not priority evidence; status remains `[APPLICATION NOVELTY UNVERIFIED]`.
- A 2026-08-08 collision audit covered maximal-volume/Auerbach basis selection, replica moments,
  quantum circuit anti-concentration, circuit lower bounds, and Hilbert-function circuit images.
  It recovered classical max-volume algorithms and the established random-circuit/design literature,
  but no use of an occupied Veronese endpoint skeleton to replace the complete shallow-circuit union
  in a return-excised recurrence bound.  This narrows the collision risk but still does not authorize
  a priority claim.
- Brown--Freedman--Lin--Susskind prove saturation and recurrence for random circuits and stochastic
  local-Hamiltonian evolution, and explicitly identify purely local Hamiltonian dynamics without
  continuously injected randomness as the desired realistic extension.  The present theorem removes
  target-union entropy from that extension; it does not supply the remaining ordinary-Hamiltonian
  fixed-target moment decay.
- This law does not prove ordinary-local-Hamiltonian anti-concentration.  A hostile reviewer must
  reject any claim that `(MV4)` alone establishes Brown--Susskind growth.

## Door passport

- **Door 0:** finite-dimensional linear algebra and finite-measure integration only.
- **Door 1:** complete finite target union, duplicate invariant, exact-return-zero invariant, all
  source fibres retained.
- **Door 2:** classical max-volume/D-optimal parentage must be cited; application priority open.
- **Door 3:** formalize maximal determinant selection, Cramer coefficient bound, pointwise replica
  incidence, integrated law, and uniform-moment corollary.

## Lean realization

- Module: `GaloisForLFunctions.HTGeometry.MaximalVolumeReplicaTargetSkeletonLaw`
- Coordinate matrix: `finiteTargetMatrix`
- Max-volume coefficient theorem: `exists_maxVolumeTargetBasis_coeff_norm_le_one`
- Pointwise capstone: `replicaTarget_maxVolumeSkeleton_pointwise`
- Quenched capstone: `measure_completeTargetCapture_le_maxVolumeSkeletonMoments`
- Uniform-moment corollary: `measure_completeTargetCapture_le_hilbert_sq_mul_fixedMoment`

The formal quenched law uses the restricted original source measure on `R^c`, so no source points
or fibre sheets are identified.  Its selected targets are members of the original occupied target
family.  The only assumptions beyond finite dimensionality are positive replica order and threshold,
measurability of the independently fixed return set, and integrability of the displayed moments.
No randomness, independence, locality, spectral gap, transversality, or unproved asymptotic premise
enters the theorem.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/MaximalVolumeReplicaTargetSkeletonLaw.lean`: PASS.
- `lake build GaloisForLFunctions.HTGeometry.MaximalVolumeReplicaTargetSkeletonLaw`: PASS,
  8669/8669 jobs.
- Axiom audit of the maximal-volume basis, replica skeleton, pointwise, quenched, and uniform-moment
  theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token scan of the new module: PASS.
- Area umbrella import: wired through `GaloisForLFunctions.HTGeometry`.
- Global formal lint reaches the new module and reports no defect in it.  Repository lint remains red
  only on concurrently added, unrelated unwired modules
  `RHTower.ProlateCanonicalSeparationLimit` and `RHTower.XiMassCriticalCenteredCosineCone`.

## Log

- 2026-08-07 -- C0 physical-fidelity domination falsified by projection cancellation.  C1 arbitrary
  target basis falsified by conditioning.  C2 maximal-volume target skeleton paper proof closed.
  C3 D-optimal improvement identified as known design theory and excluded from novelty claim.
- 2026-08-08 -- C2 formalized end to end, including actual replica endpoints, complete-union
  pointwise domination, return-excised quenched integration, and uniform `h_r^2` moment corollary.
