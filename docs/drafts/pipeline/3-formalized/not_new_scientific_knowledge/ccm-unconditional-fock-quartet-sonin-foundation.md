# CCM unconditional Fock--quartet--Sonin foundation

- **ID:** `ccm-unconditional-fock-quartet-sonin-foundation`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean umbrella:**
  `formal/GaloisForLFunctions/RHTower/CCMUnconditionalFoundation.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Statement

For finite complex Gram matrices `A,C`, define the diagonal-Fock leakage and defect

\[
L(A,C)=A\circ C,
\qquad
D(A,C)=A-A\circ C,
\]

where `\circ` is Hadamard multiplication. Lean proves the exact equivalence

\[
D(A,C)\succeq0
\quad\Longleftrightarrow\quad
q_{A\circ C}(v)\le q_A(v)\quad\text{for every }v.
\]

For finite feature families `u_i,v_i`, Lean also proves the underlying tensor identity

\[
\operatorname{Gram}(u_i\otimes v_i)
=\operatorname{Gram}(u_i)\circ\operatorname{Gram}(v_i).
\]

Thus the Hadamard leakage matrix is the actual Gram matrix of the diagonal tensor lift rather than
an abstractly stipulated product.

If the transport incidence is

\[
C=E-B+M,
\]

then the same condition is exactly

\[
q_{A\circ E}(v)+q_{A\circ M}(v)
\le q_A(v)+q_{A\circ B}(v)
\quad\text{for every }v.
\]

The equivalence is also formalized cofinally for arbitrary families of finite sections.

For a centered quartet parameter `\lambda`, Lean formalizes the causal and reflected anti-causal
resolvents

\[
f_\lambda(x)=(x-\lambda)^{-1},
\qquad
g_\lambda(x)=(x+\overline\lambda)^{-1}.
\]

Their Hermitian cross packet has the exact bilateral polarization

\[
f\overline g+g\overline f
=\frac12(f+g)\overline{(f+g)}
-\frac12(f-g)\overline{(f-g)},
\]

and

\[
f_\lambda(x)-g_\lambda(x)
=\frac{\lambda+\overline\lambda}
{(x-\lambda)(x+\overline\lambda)}.
\]

Thus every genuinely transverse quartet has a nonzero negative bilateral coordinate away from its
poles. The full functional-equation/Schwarz quartet Cauchy quotient is proved equal to the sum of
the two conjugate cross packets.

For two Sonin forbidden projections `A,B`, let

\[
V=(1-BAB)^{-1},
\qquad
E=1-A,
\qquad
Q=E-EVBE.
\]

For every bounded observable `X` commuting with `A`, Lean proves

\[
[X,Q]
=-EV\bigl([X,B]ABVB+BA[X,B]VB+[X,B]\bigr)E.
\]

The theorem is specialized to the exact Hilbert-space Sonin intersection projection. Consequently,
the resolvent correction introduces no independent commutator channel: the exact anomaly factors
through the Fourier-edge commutator and is dressed by the prolate/Sonin resolvent.

## Reused formal foundation

The umbrella also exposes the already formalized route components:

- causal Cauchy/Laplace readers and exact Cauchy inner products;
- prime-log Herglotz transport divergence and finite Cauchy packet summability;
- Gamma-damped critical carrier transition;
- the polar signed rank-two kernel and critical Mellin defect identity;
- the exact Sonin resolvent projection and Hilbert--Schmidt projection correction;
- the multiplicity-exact Hermitian Xi--Weil polarization and its closed Cauchy Hilbert core;
- the exact Xi relative-resolvent trace and completed prime-plus-archimedean flux identity;
- the exact continued source formula for separated finite Cauchy packets;
- locally uniform zero transfer, Hermitian determinant transfer, and sub-log-square prime-energy
  transfer to RH.

## Remaining RH-bearing theorem

The global RH-bearing assertion is now a named Lean predicate:

```text
RHTower.CCMGlobalWeilPassivity
```

Lean proves the exact equivalence

\[
\texttt{CCMGlobalWeilPassivity}\quad\Longleftrightarrow\quad\mathrm{RH}.
\]

The reverse direction uses an explicit finite conjugate-orbit sign test. Every nonreal centered Xi
divisor point produces a strictly negative square equal to minus the total multiplicity of its
conjugate pair.

Lean further proves the sharper rank-two criterion

\[
\texttt{CCMRegularTwoPolePassivity}\quad\Longleftrightarrow\quad\mathrm{RH}.
\]

Normalized regular Cauchy poles approaching a divisor point converge in the divisor `ell^2` carrier
to its complete multiplicity-fiber indicator. Subtracting the conjugate limit recovers the negative
sign test. Full Cauchy-core density is therefore unnecessary.

The existing corpus also proves that the Xi--Weil form on every separated finite Cauchy packet is
exactly the continued prime-plus-archimedean relative-resolvent source form. Therefore the remaining
CCM construction theorem has the following positive form:

```text
the distinguished semilocal Sonin/source form is positive on every regular
two-pole Cauchy packet and retains the normalized cofinal pole approach.
```

This supplies `CCMRegularTwoPolePassivity` and hence RH. The missing theorem is not full test-space
density or the target/source identity on separated Cauchy packets; both are unnecessary or already
available. The missing content is source-side rank-two positivity through the principal-relative
Sonin graph.

At the finite diagonal-Fock level the same obligation is represented by the named predicate

```text
RHTower.CCMCofinalSourceResolvedPassivity A E B M
```

for the actual cofinal Euler, boundary, Mellin, and safe-kernel sections.

Equivalently, after that incidence is constructed, the remaining finite-section inequality is

\[
q_{A_N\circ E_N}(v)+q_{A_N\circ M_N}(v)
\le q_{A_N}(v)+q_{A_N\circ B_N}(v)
\quad\text{for every }N,v.
\]

This is the precise point at which arithmetic must pay for every transverse quartet. The Lean
foundation proves all algebraic equivalences around this assertion but does not assert the
inequality for zeta.

## Formal declarations

The new modules provide:

```text
RHTower.ccmDiagonalDefect_kreinNonneg_iff_passivity
RHTower.ccmFiniteFeatureGram_diagonalTensor
RHTower.ccmDiagonalLeakage_incidence
RHTower.ccmFiniteFockPassivity_iff_sourceResolved
RHTower.ccmDiagonalDefect_kreinNonneg_iff_sourceResolved
RHTower.ccmQuartetCrossPacket_eq_positive_sub_negative
RHTower.ccmQuartetPairResolvent_kernel_split
RHTower.ccmQuartetResolvent_eq_crossPackets
RHTower.ccmCausal_sub_antiCausal
RHTower.ccmCausal_sub_antiCausal_ne_zero
RHTower.ccmCommutator_inv_one_sub
RHTower.ccmCommutator_dressed_two_projection
RHTower.ccmCommutator_soninIntersectionProjection
RHTower.ccmCofinalFiniteFockPassivity_iff_sourceResolved
RHTower.ccmCofinalDefect_kreinNonneg_iff_sourceResolved
RHTower.riemannHypothesis_iff_xiWeilPolarization_nonneg
RHTower.ccmGlobalWeilPassivity_iff_riemannHypothesis
RHTower.exists_normalizedCauchyLp_tendsto_fiberIndicator
RHTower.riemannHypothesis_iff_regularTwoCauchy_nonneg
RHTower.ccmRegularTwoPolePassivity_iff_riemannHypothesis
```

## Verification

- [x] existing Lean declarations searched before implementation
- [x] non-q62 formal corpus audited for route-relevant declarations
- [x] diagonal tensor Gram identity compiled
- [x] finite diagonal-Fock algebra compiled
- [x] quartet bilateral resolvent algebra compiled
- [x] exact Sonin resolvent commutator compiled
- [x] cofinal foundation umbrella compiled
- [x] exact full square-summable Xi--Weil positivity criterion compiled
- [x] normalized Cauchy-pole fiber exhaustion compiled
- [x] exact regular two-pole positivity criterion compiled
- [x] exact finite Cauchy packet prime-plus-archimedean source formula reused
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] distinguished semilocal source form proved positive on regular two-pole packets
- [ ] full actual Euler/boundary/Mellin finite-section incidence constructed
- [ ] cofinal source-resolved passivity proved for the actual carrier
- [ ] divisor-preserving global completion proved
- [ ] RH
