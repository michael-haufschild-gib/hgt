# The Mobius divisor-incidence clock has exactly four units of critical relative energy

- **ID:** `mobius-incidence-clock-gini-fisher-four-unit-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HT-TO-RH SOURCE CURVATURE
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `../3-formalized/finite-clock-star-kadison-observability.md`
- **Statement:** The moving signed squarefree source line and the complementary divisor-threshold
  clock have a canonical commutator curvature.  Its semifinite channel-time energy, multiplied by
  the critical clock scale, tends exactly to four.  Equivalently, the source curvature energy is
  four times the Gini mean difference of the critical exponential clock.  This supplies a fully
  explicit four-unit source budget before Gamma/Sonin continuation.

## Pointed source projection and incidence clock

For `sigma>1`, put `epsilon=sigma-1` and

```text
P_sigma(d)=mu(d)^2d^(-sigma)/Z(sigma),
psi_sigma(d)=mu(d)sqrt(P_sigma(d)).                       (1)
```

Let `H_sq=ell2` of the squarefree positive integers and

```text
Pi_sigma=|psi_sigma><psi_sigma|.                         (2)
```

For `t>=0`, define the divisor-incidence projection and its clock involution by

```text
Q_t e_d=1_(log d<=t)e_d,
S_t=2Q_t-I.                                               (3)
```

The inequality in `(3)` is exactly the lower half of the proved complementary floor/tail
incidence.  No Xi divisor, target vector, or chosen norm enters `(1)`--`(3)`.

Define the source curvature

```text
kappa_(sigma,t)=[Pi_sigma,S_t].                          (4)
```

At every `t`, `(4)` is finite-rank and Hilbert--Schmidt.  Over the continuous incidence clock use
the canonical semifinite relative energy

```text
E_sigma
 =epsilon integral_0^infinity
    ||kappa_(sigma,t)||_HS^2dt.                          (5)
```

The factor `epsilon` is the intrinsic critical clock scale already fixed by the source law
`epsilon log d=>Exp(1)`.

## Exact finite-energy identity `[PROVED HERE]`

Let

```text
A_sigma(t)=P_sigma(log d<=t).                            (6)
```

Then

```text
||[Pi_sigma,Q_t]||_HS^2
 =2A_sigma(t)(1-A_sigma(t)),                             (7)

||kappa_(sigma,t)||_HS^2
 =8A_sigma(t)(1-A_sigma(t)).                             (8)
```

### Proof

Write

```text
psi_sigma=Q_t psi_sigma+(I-Q_t)psi_sigma.                (9)
```

The squared norms of the two orthogonal components are `A_sigma(t)` and `1-A_sigma(t)`.  Relative
to this decomposition, the commutator of the rank-one projection `(2)` with `Q_t` has two
off-diagonal rank-one blocks.  Each has squared Hilbert--Schmidt norm
`A_sigma(t)(1-A_sigma(t))`, proving `(7)`.  Since `S_t=2Q_t-I`, equation `(8)` follows. `QED`

Let `H_sigma` be a random variable with

```text
P(H_sigma=log d)=P_sigma(d),                             (10)
```

and let `H_sigma'` be an independent copy.  The layer-cake identity gives

```text
E|H_sigma-H_sigma'|
 =2 integral_0^infinity
    A_sigma(t)(1-A_sigma(t))dt.                          (11)
```

Combining `(5)`, `(8)`, and `(11)` yields the exact source formula

```text
E_sigma
 =4epsilon E|H_sigma-H_sigma'|.                          (12)
```

Thus the relative clock curvature is four times the Gini mean difference of the logarithmic
divisor aperture.

## Critical four-unit theorem `[PROVED HERE]`

The boundary-layer product theorem gives

```text
Y_sigma=epsilon H_sigma=>Y,
Y~Exp(1).                                                 (13)
```

The Fisher theorem also gives

```text
E(Y_sigma)->1,
E(Y_sigma^2)->2.                                         (14)
```

Hence `(Y_sigma)` is uniformly integrable, as is the independent pair difference.  Equations
`(13)`--`(14)` imply

```text
epsilon E|H_sigma-H_sigma'|
 =E|Y_sigma-Y_sigma'|
 ->E|Y-Y'|=1.                                            (15)
```

The last equality follows either by direct integration or from the memoryless exponential law.
Therefore `(12)` gives

```text
lim_(sigma->1+)E_sigma=4.                                (16)
```

This is an exact four-unit source curvature, not a normalization imposed from the RH consumer.

## Fisher--Gini collision

The same critical source has the proved projective Fisher energy

```text
||chi_sigma||^2
 =4epsilon^2 Var_sigma(log d)->4.                        (17)
```

Equations `(16)`--`(17)` show that two different source geometries collide at the critical law:

```text
projective Fisher tangent energy
 =divisor-incidence commutator relative energy
 =4.                                                      (18)
```

At the limiting exponential distribution this is the elementary identity

```text
4 Var(Y)=4 E|Y-Y'|=4.                                    (19)
```

The equality is special: variance and Gini mean difference do not coincide for a general source
law.  It is selected here by the zeta pole and the squarefree critical clock.

**Positive general-HT statement.**  A source constraint can carry the same calibrated tangent
budget in an infinitesimal metric and in a cofinal incidence curvature even though no bounded
operator identifies their finite-clock realizations.  The critical law, not an assumed flow,
performs the calibration.

## Finite-window profile and anti-theatre boundary

For a scaled incidence cutoff `t=u/epsilon`, `(13)` and `(8)` give

```text
epsilon integral_0^(u/epsilon)
 ||kappa_(sigma,t)||_HS^2dt
 ->4(1-e^(-u))^2.                                       (20)
```

This is **not** the Euler-pole window profile `4(1-e^(-u))`.  Reparameterizing the source clock by
its cumulative energy could force those formulas to agree, but every continuous distribution can
be uniformized in that way.  Such a reparameterization would be target fitting and is rejected.

Equation `(16)` is therefore a global four-unit source budget.  Its honest RH consumer is the
global pole-to-divisor criterion

```text
||ell_E||_2^2<=4 -> RH,                                  (21)
```

not the local relative-trace density unless another source theorem changes the window geometry.

## Remaining source transfer

The curvature `(4)` sees the signed Mobius line and exact divisor incidence, but it does not yet
see the Gamma boundary primitive or the distinguished Xi framing.  In particular a symmetric
rational quartet does not change `(1)`--`(4)`.  Thus `(16)` cannot be identified directly with
`ell_E`.

The precise positive successor is:

> Apply the explicit Gamma/Sonin completion to the curvature `(4)` before taking the cofinal
> relative trace, preserve its source framing, and construct a nonexpansive readout whose output
> is the pole-to-divisor seam `ell_E`.

If such a readout is constructed, `(16)` gives `(21)` and proves RH.  The four-unit input side of
that theorem is now completely explicit and proved; the completed readout is not.

## Literature gate

The Gini layer-cake identity, rank-one projection commutator calculation, exponential limit, and
Fisher information are established parent mechanisms.  Targeted searches have not located their
combination `(16)`--`(19)` for the squarefree Mobius incidence clock.  Project results used here
remain admissible source inputs.  External specialist audit is still required before any novelty
claim.

## Gates

- [x] signed source projection constructed
- [x] divisor-incidence clock involution constructed
- [x] exact commutator Hilbert--Schmidt density proved
- [x] exact Gini relative-energy identity proved
- [x] critical exponential uniform integrability proved
- [x] exact four-unit global limit proved
- [x] Fisher--Gini calibration identified
- [x] local-profile mismatch computed and target-fitting rejected
- [ ] apply the Gamma/Sonin completion before the relative trace
- [ ] preserve the rational-gauge/source framing
- [ ] identify the completed readout with `ell_E`
- [ ] prove nonexpansiveness of the completed readout
- [ ] independent specialist literature audit
- [ ] RH
