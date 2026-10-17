# Arithmetic commutation of continuum coprime projections

For integers m,n≥2, let V_m⊂L²(ℝ) be the closed range of the infinite coprime
tent extension with spacing m, and let P_m be its constructed orthogonal
projection. Write L=lcm(m,n), g=gcd(m,n). The exact classification is

    V_m ∩ V_n = V_L,
    P_m P_n = P_n P_m  iff  g≥2,
    g≥2  implies  P_m P_n=P_L.

All spaces and operators are the actual objects constructed in the infinite
extension theorem. They are not abstract interfaces with unproved premises.
Formal parameters are d,e∈ℕ, m=d+2,n=e+2, and L−2 for the lcm spacing.

## Cross-tent geometry

For integer a≥1, set H_a=1_(a−1,a]−1_(a,a+1]. The unit-cell indicators are
orthonormal. Expanding four pairings therefore gives

    ⟨H_a,H_b⟩ = 2 if a=b; −1 if a=b+1 or b=a+1; 0 otherwise.

The coefficient of H_a in P_mq is ⟨H_a,q⟩/2, for a a positive multiple of m.
This is exactly half the centered primitive difference established previously.
If g≥2, any common divisor g divides every center in both families. Adjacent
centers would force g|1, impossible. Hence on every n-tent,

    P_m H_b = H_b if m|b, else 0.                     (1)

The retained case follows because H_b is itself an m-tent. In the other case
every m-tent pairing vanishes, so every coordinate of the actual analysis map
vanishes. Applying synthesis proves zero; no completeness assumption about the
whole ambient L² space is used.

## Infinite operator identities

Each P_m=S_mS_m* is a bounded self-adjoint operator. Mapping the proved convergent
tent series by a continuous linear map extends agreement on individual n-tents
to all of V_n. Thus (1) is an infinite operator statement, not a finite matrix
argument. If m|L, every L-tent belongs to V_m, so P_mP_L=P_L. Taking adjoints
gives P_LP_m=P_L. In particular V_L⊂V_m and V_L⊂V_n.

When g≥2, (1) and n|b show that P_m and P_L agree on every n-tent: m|b iff
L|b. Therefore P_mP_n=P_LP_n=P_L. Exchanging m and n proves commutation.

## Intersection for every pair of spacings

Let q∈V_m∩V_n and write q=E_m(v), with actual v∈ℓ². Every integer primitive
trace of q vanishes unless its index is a positive multiple of both m and n,
hence unless L divides that index. For an m-center a with L∤a, the exact trace
law gives v_a=0. Since m|L, the separated-family formula for P_L on m-tents
retains precisely those with L|a. It therefore fixes each nonzero summand of
the convergent series for q. Continuity gives P_Lq=q, so q∈V_L. Combined with
the preceding inclusions, this proves the intersection formula even when g=1.
This argument uses exact traces and actual convergent series, rather than
assuming that intersections of closed spans are spans of intersected indices.

## Coprime noncommutation with an exact witness

Suppose g=1. Bezout's identity provides a modular inverse k of m modulo n:
0≤k<n and mk mod n=1. Since m,n≥2, k≥1, a=mk≥2, and b=a−1 is a positive
multiple of n. Both a and b are active centers; m cannot divide b, since m|a
and a=b+1. Set q=H_a. Then P_mq=q, while the cross-tent law gives

    primitive(P_nP_mq)(b)=⟨H_b,H_a⟩/2=−1/2.

Every primitive trace of P_mP_nq at a forbidden m-node is zero, so

    primitive((P_mP_n−P_nP_m)q)(b)=1/2.              (2)

Thus the commutator is nonzero. This also covers m=2 or n=2: a tent may have
two adjacent partners, but its coefficient at the chosen b is still exactly
−1/2. No uncancelled-sum guess is needed. Since g>0, the alternatives g=1 and
g≥2 exhaust all spacings, completing the classifier.

## Scope and parent theory

The result isolates a concrete arithmetic source of noncommutativity within
the continuum Dirichlet trace domain. A common divisor eliminates additive
neighbor coupling; coprimality forces an exact observable commutator. This does
not identify a unitary affine-group representation or a closed SourceGraph
operator. The physical primitive traces transfer to logarithmic grid traces
at positive integers through the existing transport theorem.

Parent tools are classical: Hilbert series/projection theory in [NPTEL,
Spaces, §1.5](https://archive.nptel.ac.in/content/storage2/courses/111106047/chapter1.pdf),
and Bezout/lcm facts in [Southampton MATH1001, §3.4](https://www.southampton.ac.uk/~wright/1001/coprime-integers.html).
The arithmetic projection classification and witness are proved here from the
specific constructed tents; no external novelty claim is made for parent tools.
Fresh corpus search found no matching cross-family result, subject to recorded
semantic/freshness limitations.

## Formal realization

The package is formalized in three leaves under the `SobolevShear` namespace:

- `CoprimeProjectionCrossGram.lean`: cross-family Gram formula, bundled
  self-adjoint projector, extension of agreement through actual convergent
  series, and common-divisor coefficient restriction.
- `CoprimeProjectionLattice.lean`: nested absorption, lcm product, simultaneous
  fixed-point classification and exact intersection of closed extension ranges.
- `CoprimeProjectionCommutator.lean`: positive adjacent centers from the modular
  inverse, exact primitive witness and both pointwise/bundled commutation iff laws.

All 30 public declarations passed the axiom audit, using only `propext`,
`Classical.choice`, and `Quot.sound`; nine main signatures were inspected.
The 28 theorems and two definitions form one connected contribution. Formal
verification details and repository-wide lint limitations are recorded in
`ContinuumCoprimeShear-FACTS.md`. No numerical experiment, added axiom,
unproved analytic premise, heartbeat increase, or full/umbrella build was used.
