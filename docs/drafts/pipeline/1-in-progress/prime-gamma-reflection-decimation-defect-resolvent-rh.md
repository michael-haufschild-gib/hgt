# Prime--Gamma reflection-decimation defect resolvent to RH

- **ID:** `prime-gamma-reflection-decimation-defect-resolvent-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, TOP-DOWN SOURCE PRODUCER, STATIC REFLECTION GEOMETRY
- **Scientific status:** `[OPEN] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  `../3-formalized/not_new_scientific_knowledge/bv-prime-window-dilation-residue-orientation.md`;
  `../3-formalized/not_new_scientific_knowledge/euclidean-spectral-pushforward-hankel-rh-capstone.md`;
  `../3-formalized/not_new_scientific_knowledge/prime-arch-positive-moment-representation-to-rh.md`;
  `../2-fully-proven/not_new_scientific_knowledge/ccm-gamma-damped-cauchy-frame-trace-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/prime-arch-explicit-circle-state-reflection-law.md`.
- **Statement:** `[CONJECTURE]` The normalized prime--Gamma moment germ is the cyclic resolvent of
  a positive reflection-sewn decimation-defect operator constructed from resolved prime channels,
  the Gamma cyclic source, and the finite BV square-decimation identity before continuation.

## Goal

Construct positivity rather than postulate a positive measure.  The desired object must retain all
four data which divisor sets, finite jets, abstract fields, and principal symbols lose:

1. functional-equation reflection exchanges the two source channels;
2. the positive cone selects one orientation of that exchange;
3. prime channels and the archimedean counterterm enter one completed identity;
4. every vector and operator is produced from explicit finite source incidence before any Xi zero
   or target moment measure is read.

The consumer end is already closed in Lean.  If a positive operator `A` and a source vector
`Omega` satisfy

```text
normalizedPrimeArchMoment(n)=<Omega,A^n Omega>           (1)
```

for every `n`, then the spectral measure of `(A,Omega)` is a positive moment representation and
RH follows.  No infinite-support, determinacy, compactness, simplicity, or determinant hypothesis
is required.

## Source evidence already proved

Let `W` be an actual compact-BV prime window.  For a positive integer `r`, Lean now proves that its
forward and inverse argument dilations obey the exact finite coefficient law

```text
p_(W(r·))(n)=p_(W(·/r))(r^2 n).                         (2)
```

The coefficient includes both the finite von-Mangoldt window and its archimedean Mellin
counterterm.  After canonical continuation, the two actual Laurent residues transform by

```text
R_+(rho)=r^(rho-1/2)R_W(rho),
R_-(rho)=r^(1/2-rho)R_W(rho),                            (3)
```

and their squared-norm difference has the strict sign of `Re(rho)-1/2`.  Thus orientation is the
continued image of a finite prime--Gamma source action; it is not added as a divisor predicate.

On coefficient space, square-index decimation `D` has the exact positive defect

```text
||a||^2-||Da||^2
 =sum_(r^2 does not divide n)|a(n)|^2.                   (4)
```

The Gamma-damped channel-resolved Cauchy construction supplies the complementary ingredient: a
positive prime-channel covariance whose trace remains Euler-additive and whose Gamma diagonal
crosses the critical half-weight.  Its exact critical prime--Gamma relative channel is not yet
constructed.

## Medalist conjecture

`[CONJECTURE]` There is a source-defined singular boundary completion `H_src`, a completed
prime--Gamma incidence map `V`, a reflection-compatible square-decimation contraction `D_src`, and
a distinguished source vector `Omega` such that

```text
Delta_src = I-D_src^*D_src >= 0,
A_src     = V^* Delta_src V >= 0,                         (5)

normalizedPrimeArchMomentGerm(z)
 = <Omega,(I-z A_src)^(-1)Omega>                         (6)
```

near `z=0`.

The notation in `(5)` is schematic only to the extent that `V` and the singular completion remain
to be constructed.  The required content is exact:

- `Delta_src` must descend from the off-multiple sum in `(4)`;
- `V` must contain the resolved von-Mangoldt channels and Gamma boundary channel before trace;
- reflection must exchange the forward and inverse BV source channels;
- `(6)` must be proved from the continued prime--Gamma source formula, not used to define `A_src`.

Expanding `(6)` gives `(1)`, hence the formal chain

```text
source reflection-decimation defect resolvent identity
  -> positive cyclic moment representation
  -> complete prime--Gamma trace-Hankel cone
  -> RH.                                                   (7)
```

This is a constraint construction.  `A_src` is a static positive observable obtained by
compression of a source defect; it is not a Hamiltonian or a flow whose evolution is assumed to
carry the proof.

## Strong weakening: local finite source certificates

The global operator is stronger than the Lean consumer needs.  It is enough that for every `N`
the finite source incidence produce a finite-dimensional `H_N`, `A_N>=0`, and `Omega_N` with

```text
normalizedPrimeArchMoment(k)=<Omega_N,A_N^k Omega_N>
for 0<=k<2N.                                              (8)
```

The witnesses may vary with `N`; no compatibility, limiting measure, or support theorem is an
input.  Equation `(8)` makes the first `N` by `N` source Hankel block a literal Gram matrix.  The
existing local finite-positive-atomic closure theorem then closes `(7)`.

This is the operational meaning of removing the infinite-support hypothesis.  It does not make a
single finite global spectrum plausible.  The corpus proves that no fixed finite KMS/Wightman
system realizes the complete normalized moment tower.  Since every finite positive-atomic moment
sequence has such a KMS realization, a fixed finite positive-atomic global model is also excluded.
Spectral proliferation is therefore an automatic consequence of exact source matching, not a
condition to establish before positivity.

## Discriminator

The first nontrivial test is not another global RH equivalent.  Construct directly from the
completed source channels a vector `Psi_src` and a positive defect `Delta_src` for which

```text
m_0 m_2-m_1^2 = ||Delta_src^(1/2) Psi_src||^2,           (9)
```

where `m_k=normalizedPrimeArchMoment(k)`.  The right side must be defined without `m_0 m_2-m_1^2`
and without Xi divisor coordinates.  Equation `(9)` would discharge the first genuinely
nonconstant Hankel block and distinguish this mechanism from a generic positive carrier or a
renamed moment criterion.

The next discriminator is the `3 x 3` block: the same construction must provide three source
vectors with Gram entries `m_(i+j)`.  A mechanism which proves only `(9)` by a special scalar
identity but has no three-vector source polarization is not the sought carrier.

## Attacks and positive residues

1. **Arbitrary positive measure.**  Choosing a representing measure after reading the moments is
   exactly the RH-equivalent consumer.
   **Positive requirement:** construct `Delta_src`, `V`, and `Omega` before moment comparison.
2. **Fixed finite spectrum.**  The formal finite-KMS obstruction excludes one finite system
   matching the entire source tower.
   **Positive requirement:** use either the singular global source carrier or independently
   source-produced finite blocks of growing width.
3. **Raw coefficient `ell^2`.**  Every uncensored meromorphic prime-window coefficient lies outside
   the ordinary Dirichlet--Hardy space; completing there deletes the Laurent boundary data.
   **Positive requirement:** use the pole-cancelled graph and retain its principal-part boundary
   coordinate.
4. **Diagonal prime damping.**  The Gamma diagonal fixes summability but scalar coherent summation
   creates cross-prime terms absent from the Euler trace.
   **Positive requirement:** preserve prime-channel resolution until the positive Gram is formed,
   then take its trace or source compression.
5. **Scale-free orientation.**  Orientation alone cannot pay a fixed archimedean budget under
   positive rescaling.
   **Positive requirement:** the exact Mellin counterterm and Gamma normalization must occur in
   the same defect identity as the von-Mangoldt channels.
6. **Ordinary circle positivity.**  The explicit positive analytic circle state is unconditional,
   but generic densities arbitrarily close to Haar have negative reflected Hankel directions.
   **Positive requirement:** `(5)` must perform source-specific positive radialization, not use
   density coercivity or Schur norm alone.
7. **Hidden divisor norm.**  Summing squared residues over Xi zeros would manufacture the desired
   sign.
   **Positive requirement:** residues may be used only after the source Gram and its bounded
   evaluation map have been constructed.

## Ranked research targets

1. **Finite completed defect factorization.**  Prove `(9)` from the actual BV off-multiple defect,
   the Gamma cyclic covariance, and the pole-cancelled prime source.
2. **Channel-resolved relative incidence.**  Construct the exact archimedean/boundary channel
   missing from the Gamma-damped Cauchy frame so that its trace is the centered prime--Gamma source,
   not merely the absolute-Euler source.
3. **Finite block Gram identity.**  Extend the two-vector factorization to `(8)` for arbitrary
   `N`.  This is already sufficient for RH and avoids a premature global completion.
4. **Singular boundary completion.**  If the finite blocks are compatible, construct `H_src` and
   prove `(5)`--`(6)`.  Bounded Laurent evaluation must follow from the pole-cancelled graph norm,
   not be assumed.
5. **HTGeometry abstraction.**  Extract a general theorem: a reflected hypertranscendental source
   constraint with a positive decimation defect and an exact completed incidence resolvent produces
   a positive cyclic state.  The zeta source is the pressure test, not the definition of the
   abstraction.

## Gates

- [x] source-pure finite square-decimation identity formalized
- [x] forward/inverse Mellin residue orientation formalized
- [x] arbitrary positive moment representation to RH formalized
- [x] Euclidean spectral specialization without support assumptions formalized
- [x] fixed finite KMS realization of the complete tower excluded in Lean
- [x] channel-resolved Gamma-damped critical Cauchy domain formalized
- [ ] prove the first source defect norm identity `(9)`
- [ ] construct the exact completed relative prime--Gamma incidence
- [ ] prove the arbitrary finite block identity `(8)`
- [ ] construct the global singular defect resolvent `(5)`--`(6)` if needed
- [ ] compose an unconditional proof of RH

## Log

- 2026-07-16 -- Created after the arbitrary-support Euclidean capstone and the exact BV
  reflection-decimation source law.  Infinite support was demoted from input to automatic output;
  the live carrier was isolated as a source-produced reflection-decimation defect resolvent.
