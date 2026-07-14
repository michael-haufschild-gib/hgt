# Compressed commuting Euler sources carry the Sonin orientation Gram

- **ID:** `semilocal-compressed-euler-constraint-orientation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[VALUE RELATION]`, `[TOP-DOWN GAP SIMPLIFICATION]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SemilocalCompressedEulerOrientation.lean`
- **Parents:** `sonin-prime-seam-exterior-factorization.md`;
  `semilocal-euler-kernel-chart-differentiability.md`;
  `xi-prime-seam-coherence-collapse.md`
- **Statement:** The finite seam-difference Sonin Gram is exactly the negative commutator created
  by compressing two commuting Hardy--Titchmarsh Euler source multipliers. Compactness of that
  commutator is equivalent to constancy of the complete coefficient packet.

## Exact constraint--orientation identity

Let `P_a` be the actual archimedean Hardy--Titchmarsh realization of the Sonin carrier projection.
For distinct finite scales `r_i>1`, let

```text
G_i=M_|1-r_i^(-1/2-is)|^2
```

be the literal positive Euler Gram multipliers. For `u:Fin n->C`, put

```text
A_u=sum_i u_i G_i,
A_1=sum_i G_i,
T_u=P_a A_u P_a,
T_1=P_a A_1 P_a,
C_i=(1-P_a)G_i P_a.                                     (1)
```

Lean proves unconditionally that the uncompressed source multipliers commute:

```text
G_i G_j=G_j G_i,
A_u A_1=A_1 A_u.                                         (2)
```

Compression is the only source of orientation. The Toeplitz--Hankel semicommutator identity gives
the exact operator equality

```text
sum_(i,j)(u_i-u_j) C_i^* C_j
  =-(T_u T_1-T_1 T_u).                                   (3)
```

Thus the ordered Sonin Gram coboundary is not the curvature of a hidden prime flow. It is the
failure of two commuting source values to remain commuting after imposing one fixed constraint.

The formal surface includes:

```text
compression_commutator_eq_neg_boundary_skew
archimedeanPrimeEulerGram_commute
finiteArchimedeanEulerSource_commute
finiteArchimedeanEulerOrientationGram_eq_boundary_skew
finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator
```

## Finite faithfulness

For an injective finite prime packet `p_i`, the already formalized quadratic Sonin Calkin
injection and `(3)` imply

```text
[T_u,T_1] is compact
  <-> sum_(i,j)(u_i-u_j) C_i^* C_j is compact
  <-> u_i=u_j for every i,j.                              (4)
```

The exact Lean theorem is

```text
finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff.
```

This retains every coefficient difference. It is stronger than checking a scalar relative trace,
and it avoids the known bounded-response obstruction for the canonical finite Sonin trace.

## Top-down RH chain

At an actual Xi divisor point `rho`, specialize

```text
u_i=a_(p_i)(rho)
   =log(p_i)(p_i^(-conj(rho))-p_i^(-(1-rho))).             (5)
```

Define `XiFiniteEulerCompressionEssentiallyCommuting a` to assert compactness of `[T_u,T_1]` for
every actual Xi divisor fibre and every injective finite prime packet. Lean proves

```text
XiFiniteEulerCompressionEssentiallyCommuting a
  <-> RH,                                                  (6)
```

for every positive Sonin aperture `a`. The forward chain is substantive before the final
equivalence:

```text
essential commutation of compressed finite source values
  -> all finite Xi seam packets are constant by (4)
  -> pairwise prime-seam coherence
  -> the common charge is zero by unconditional cofinal prime decay
  -> RH.                                                   (7)
```

Equation `(6)` is an endpoint, not a proof of its left side. The new reduction is `(3)`: it removes
the moving-projection and tangential-connection construction from the statement of the missing
source theorem.

## Correct remaining source problem

The remaining positive assertion is now:

```text
[OPEN] For every actual Xi divisor rho and finite prime packet F,
       [P_a A_(a(rho)) P_a, P_a A_1 P_a] is compact.       (8)
```

It must be proved from a genuine source--divisor value relation. It cannot follow from ambient
finite-place commutativity, because compression deliberately creates the nonzero boundary Gram.
It also cannot follow from one-prime quasi-inner compactness: Lean proves that the one-prime
commutator with the actual Sonin projection is noncompact.

The likely value interface is Burnol's bounded Sonine/de Branges evaluators at every actual zeta
zero, including multiplicity jets. The Connes--Consani zeta-cycle construction is not an
unconditional replacement: its periodic action decomposes into unitary characters and therefore
selects only zeros already on the critical line. It may describe the RH chamber, but using it to
produce `(8)` at hypothetical off-line divisor points would be circular.

Connes--Consani--Moscovici's semilocal square still supplies the exact source geometry: adjoining a
finite place is multiplication by the local Euler factor, and the primal--dual pairing is flat.
The theorem here identifies the required second-order remainder of that geometry without asking
for a differentiated connection. A successful Burnol/Poisson value theorem must show directly
that the commutator in `(8)` has only a compact divisor-evaluator remainder.

## Literature boundary

- Connes--Consani--Moscovici,
  [*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423), proves the semilocal
  Hardy--Titchmarsh square and stability of the Sonin spaces.
- Connes--Consani,
  [*Spectral triples and zeta-cycles*](https://arxiv.org/abs/2106.01715), proves that zeta-cycle
  spectra consist of imaginary parts of critical-line zeros; it does not supply evaluators at
  hypothetical off-line zeros.
- Burnol,
  [*Two complete and minimal systems associated with the zeros of the Riemann zeta function*](https://arxiv.org/abs/math/0203120),
  supplies continuous zero and multiplicity-jet evaluators for the full nontrivial divisor.

The abstract compression identity is the standard Toeplitz--Hankel semicommutator law. Its value
here is the exact identification with the already faithful prime Euler Gram and the consequent
removal of a speculative connection interface.

## Gates

- [x] literal Euler Gram multipliers commute before compression
- [x] arbitrary finite Euler source packets commute before compression
- [x] exact exterior boundary factorization
- [x] exact orientation-Gram/compressed-commutator identity
- [x] finite Calkin compactness iff coefficient constancy
- [x] Xi finite essential-commutation endpoint iff RH
- [x] module imported by the `RHTower` umbrella
- [ ] prove source-divisor essential commutation `(8)` without RH-equivalent input
- [ ] identify the compact remainder through actual Burnol divisor evaluators
