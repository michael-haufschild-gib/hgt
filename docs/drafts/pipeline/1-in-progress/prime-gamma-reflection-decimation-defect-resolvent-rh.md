# Prime--Gamma reflection-decimation defect resolvent to RH

- **ID:** `prime-gamma-reflection-decimation-defect-resolvent-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, TOP-DOWN SOURCE PRODUCER, STATIC REFLECTION GEOMETRY
- **Scientific status:** `[OPEN] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  `../3-formalized/not_new_scientific_knowledge/bv-prime-window-dilation-residue-orientation.md`;
  `../3-formalized/not_new_scientific_knowledge/euclidean-spectral-pushforward-hankel-rh-capstone.md`;
  `../3-formalized/not_new_scientific_knowledge/prime-arch-positive-moment-representation-to-rh.md`;
  `../3-formalized/not_new_scientific_knowledge/inverse-tilted-prime-gamma-central-source-value-relation.md`;
  `../3-formalized/not_new_scientific_knowledge/finite-skew-green-trace-positivity.md`;
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

## Sharper conjecture: finite reflected-scale Green Gram jets

The weakest source-producing target is smaller than `(8)`.  No operator powers, common spectrum,
or compatibility between cutoffs are needed.  For every `N` it is enough to construct a
source-defined net of positive semidefinite matrices

```text
G_(N,X)(i,j),   0<=i,j<N,
```

from finitely many BV dilation channels, their positive off-square decimation defects, a finite
inverse of the centered scale generator, and the Gamma/boundary channel, such that

```text
lim_(X->infinity) G_(N,X)(i,j)
  =normalizedPrimeArchMoment(i+j).                       (10)
```

The cutoff form must be positive before the comparison with the target moments, for example in
the schematic source form

```text
G_(N,X)(i,j)
 =<Delta_(r,X)^(1/2) Psi_(N,X,i),
    Delta_(r,X)^(1/2) Psi_(N,X,j)>
  +<Gamma_(N,X,i),Gamma_(N,X,j)>,                        (11)
```

where `Delta_(r,X)` is the literal finite off-`r^2` projection supplied by square-index
decimation.  Neither `Psi`, `Gamma`, nor the renormalization may be defined from the Xi divisor,
the target Hankel matrix, or a Cholesky factor of that matrix.

`[CONJECTURE]` Such finite reflected-scale Green Gram jets exist with an explicit prime--Gamma
boundary subtraction depending on `N` but not on any zero.  The now-formalized inverse-tilted
source identity then proves `(10)`.  Since the positive semidefinite cone is closed in every fixed
matrix size, `(10)` gives every finite prime--Gamma Hankel block and hence RH.

This is the exact gain from removing support assumptions.  A global scale-zero Hilbert completion,
bounded Laurent evaluation, tightness of spectral measures, and a common thermodynamic family are
all optional.  The only limiting statement is entrywise convergence of one finite source Gram at
a time.  The resulting chain is

```text
finite BV off-square defect + completed Gamma boundary jet
  -> source-built positive finite Gram packet
  -> entrywise prime--Gamma moment-jet comparison
  -> complete source Hankel cone
  -> RH.                                                   (12)
```

The proposed packet is a static reflection constraint on a finite scale set.  The dilation
parameter labels the two reflected source channels; it is not used as an evolution producing Xi.

### Exact value relation `[CLOSED]`

Lean now identifies the normalized centered moments with the Taylor coefficients of one explicit
inverse-tilted prime--Gamma source.  At `s=1+iz`, the zero-free inverse-tilted Mellin aperture is
divided out of the continued finite-prime source after subtracting its explicit quadrature
correction; adding the fixed Gamma connection gives exactly
`continuedPrimeArchSourceRelativeTrace`.  Every normalized moment is the corresponding even Taylor
coefficient of this reconstructed source.  The theorem uses no divisor data.

What remains is therefore only the positive lift:

```text
finite positive reflected BV/Gamma Green kernel
  --source trace comparison-->
Taylor-Hankel kernel of inverseTiltedPrimeGammaSourceTrace.       (13)
```

Proving only positivity of the continued Cauchy kernel is not an acceptable substitute: that sign
is already an RH-equivalent consumer.  The left side of `(13)` must be positive by its finite
prime-channel construction before the value identity is invoked.

### Why the inverse centered scale generator is forced

The BV dilation orbit acts on an uncensored Laurent fibre by

```text
exp(t*(rho-1/2)).                                         (14)
```

Taylor differentiation in `t` therefore produces positive powers of `rho-1/2`.  The canonical
moment node is instead

```text
lambda_rho=-(rho-1/2)^(-2).                              (15)
```

Consequently dilation and finite decimation alone cannot produce the moment tower.  A Green
operator for the centered scale generator is mathematically forced.

The corpus already proves the source algebra.  For `C=D+1/2`, weight-one inversion gives
`CJ=-JC`; on a Mellin power of exponent `rho`, `C` has symbol `1/2-rho`.  Hence

```text
A=-C^(-2)                                                (16)
```

has precisely the symbol `(15)`.  On the natural `L^2(dt)` scale space, the paper-proven closure
makes `C` skew-adjoint, so whenever its inverse is defined,

```text
A=(C^(-1))^* C^(-1) >= 0.                               (17)
```

This is the structural reason that a positive Euclidean representation appeared: it is the Green
square of the reflection-odd centered scale constraint, not an independently postulated spectrum.

### Finite Hodge--Green target

For each source cutoff `X`, construct a finite completed prime--Gamma complex with:

```text
Gamma_X       grading,
d_X           odd source differential,
P_X           orthogonal harmonic projection,
C_X           invertible skew-Hermitian centered scale generator,
A_X=-C_X^(-2)>=0.                                       (18)
```

Require `P_X` to commute with `C_X`.  The finite vectors

```text
V_(X,i)=P_X C_X^(-1) A_X^i                              (19)
```

in Hilbert--Schmidt space then satisfy

```text
<V_(X,i),V_(X,j)>_HS=Tr(P_X A_X^(i+j+1))>=0.            (20)
```

The matrix algebra in `(20)` is now closed in Lean.  A left inverse `G_X` of a skew-Hermitian
`C_X` is automatically skew-Hermitian, its Green square

```text
A_X=G_X^*G_X=-G_X^2
```

is positive semidefinite, and the shifted trace powers `Re Tr(A_X^(n+1))` form a
reflection-positive Hankel sequence.  Thus no spectral theorem, diagonalization, support
hypothesis, or independently chosen measure remains in this finite step.

The source theorem to prove is

```text
Tr(P_X A_X^(n+1))
  -> normalizedPrimeArchMoment(n)                       (21)
```

for every fixed `n`.  No common spectrum, support theorem, determinant identity, or compatible
choice between unrelated finite cutoffs is required.

There is one essential sign firewall.  `SeamSuspensionTrace` currently compresses a **graded**
trace.  To obtain the ordinary positive trace in `(20)`, the source construction must prove

```text
Gamma_X P_X=P_X                                         (22)
```

or an equivalent positive-parity/effectivity theorem.  Without `(22)`, Hodge compression yields a
signed supertrace and does not produce the Euclidean/Hankel cone.  This is the precise
constraint-orientation junction; it must not be hidden inside the words “spectral realization.”

Lean now also proves the exact parity interface: graded Hodge compression together with
`Gamma_X P_X=P_X` equals the ordinary compressed trace.  Therefore trace cyclicity and the
graded-to-ungraded conversion are no longer open.  The only parity input left is the
source-specific effectivity theorem itself.

### Hodge--Stieltjes source conjecture

`[CONJECTURE]` The inverse-tilted finite-prime source admits cutoff complexes for which the
completed source germ is the locally uniform Green-resolvent trace limit

```text
normalizedTraceMomentGerm(inverseTiltedPrimeGammaSourceTrace)(z)
 =lim_(X->infinity) Tr(P_X A_X (I-z^2 A_X)^(-1)),         (22a)
```

with `C_X`, `G_X`, `A_X`, and `P_X` constructed from the finite prime channels, quadrature
correction, Gamma boundary channel, and reflection before the right side is compared with the
target germ.  Source degree is effective:

```text
Gamma_X P_X=P_X.                                         (22b)
```

Expanding `(22a)` produces `(21)` simultaneously for all fixed moments.  Positivity is already
forced by the Green square and `(22b)`, while the formalized inverse-tilted value relation
identifies the limit with the canonical prime--Gamma moments.  This would give RH without a
global spectrum, an infinite-support argument, or a flow.

The geometric content of `(22b)` should be sought as a relative effectivity theorem for the
completed source mapping cone: finite-prime and Gamma/boundary incidence cancel in opposite
degrees, while the surviving harmonic class is carried by the designated positive source degree.
It should not be proved by inspecting Xi zeros or by assuming positivity of the target kernel.

There is a secondary charge test.  `[CONJECTURE]` The common first-prime seam charge is the finite
boundary-index shadow of the negative harmonic block `(1-Gamma_X)P_X/2`.  An exact index formula
of this kind would make `(22b)` a source-side reason for common-charge vanishing, instead of a new
charge hypothesis.  This identification is not yet proved and is not needed if `(22a)`--`(22b)`
can be established directly.

## Discriminator

The first nontrivial test is not another global RH equivalent.  Construct directly from the
completed source channels a vector `Psi_src` and a positive defect `Delta_src` for which

```text
m_0 m_2-m_1^2 = ||Delta_src^(1/2) Psi_src||^2,           (23)
```

where `m_k=normalizedPrimeArchMoment(k)`.  The right side must be defined without `m_0 m_2-m_1^2`
and without Xi divisor coordinates.  Equation `(23)` would discharge the first genuinely
nonconstant Hankel block and distinguish this mechanism from a generic positive carrier or a
renamed moment criterion.

The next discriminator is the `3 x 3` block: the same construction must provide three source
vectors with Gram entries `m_(i+j)`.  A mechanism which proves only `(23)` by a special scalar
identity but has no three-vector source polarization is not the sought carrier.

For the finite-jet formulation the corresponding first test is a positive `2 x 2` cutoff Gram
whose three entries converge separately to `m_0,m_1,m_2`.  This is stronger evidence for the
mechanism than a posteriori algebraic rewriting of `m_0*m_2-m_1^2`: it forces one common
source packet to produce the mixed value `m_1` as well as both diagonal values.

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

1. **Two-vector finite jet packet.**  Construct the positive cutoff Gram in `(11)` for `N=2` and
   prove the three source limits `G_00->m_0`, `G_01->m_1`, and `G_11->m_2`.  This subsumes `(23)`
   without defining its square root from the determinant.
2. **Finite centered Green square.**  Construct `C_X`, `P_X`, and `A_X` in `(18)` directly from a
   finite inverse-tilted prime--Gamma complex.  The skew-inverse, positive-square, and
   trace-Hankel algebra is already formalized; only the source construction remains.
3. **Positive harmonic parity.**  Prove `(22)` from source degree/effectivity, not from Xi zero
   locations or a target spectral measure.
4. **Finite source trace comparison.**  Prove the entrywise limit `(21)` using the formalized
   inverse-tilted central source identity.
5. **Channel-resolved relative incidence.**  Construct the exact archimedean/boundary channel
   missing from the Gamma-damped Cauchy frame so that its trace is the centered prime--Gamma source,
   not merely the absolute-Euler source.
6. **Arbitrary finite Gram jet.**  Extend the two-vector construction to `(10)` for arbitrary
   `N`.  This is already sufficient for RH and avoids a premature global completion.
7. **Singular boundary completion.**  Only if the finite packets reveal natural compatibility,
   construct `H_src` and
   prove `(5)`--`(6)`.  Bounded Laurent evaluation must follow from the pole-cancelled graph norm,
   not be assumed.
8. **HTGeometry abstraction.**  Extract a general theorem: a reflected hypertranscendental source
   constraint with a positive decimation defect and an exact completed incidence resolvent produces
   a positive cyclic state.  The zeta source is the pressure test, not the definition of the
   abstraction.
9. **Charge-index comparison.**  Test whether the common first-prime seam charge is the boundary
   index of the negative harmonic block.  Promote this only if an exact source-side index formula
   is obtained; a value-level equivalence with orientation energy is already known and adds no
   mechanism.

## Gates

- [x] source-pure finite square-decimation identity formalized
- [x] forward/inverse Mellin residue orientation formalized
- [x] arbitrary positive moment representation to RH formalized
- [x] Euclidean spectral specialization without support assumptions formalized
- [x] fixed finite KMS realization of the complete tower excluded in Lean
- [x] channel-resolved Gamma-damped critical Cauchy domain formalized
- [x] inverse-tilted finite-prime/Gamma source reconstructed the complete central trace in Lean
- [x] every normalized prime--Gamma moment transferred to that explicit source germ
- [x] arbitrary cutoff-dependent finite positive certificates identified as sufficient
- [x] inverse centered scale generator identified as the forced reciprocal-square mechanism
- [x] finite skew-inverse Green square and trace-power Hankel positivity formalized
- [x] positive harmonic parity isolated as sufficient for graded-to-ordinary trace compression
- [ ] construct the common positive `2 x 2` source cutoff packet
- [ ] prove its three entrywise moment limits
- [ ] construct the finite skew-Hermitian centered Green square
- [ ] prove positive harmonic parity/effectivity
- [ ] prove the finite reflected-scale Gram jet theorem for arbitrary cutoff
- [ ] prove the first source defect norm identity `(23)`
- [ ] construct the exact completed relative prime--Gamma incidence
- [ ] prove the arbitrary finite block identity `(8)`
- [ ] construct the global singular defect resolvent `(5)`--`(6)` if needed
- [ ] compose an unconditional proof of RH

## Log

- 2026-07-16 -- Created after the arbitrary-support Euclidean capstone and the exact BV
  reflection-decimation source law.  Infinite support was demoted from input to automatic output;
  the live carrier was isolated as a source-produced reflection-decimation defect resolvent.
- 2026-07-16 -- Closed the inverse-tilted finite-prime/Gamma central value relation in Lean.  The
  scale-character/moment-node mismatch forced replacement of raw dilation jets by the centered
  Green square `-C^(-2)`.  The new open core is a finite positive-parity Hodge--Green trace
  comparison, not a representing-measure or support theorem.
