# Mobius incidence curvature--Gamma/Sonin pole-to-divisor transfer

- **ID:** `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [HTGEOMETRY-TO-RHTOWER SOURCE PRODUCER]`
- **Scientific status:** `[OPEN CORE] [CONDITIONAL RH PROOF] [LITERATURE NOVELTY OPEN]`
- **Proved source inputs:**
  - `../2-fully-proven/mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `../2-fully-proven/mobius-critical-fisher-tangent-hilbert-lift.md`
  - `../2-fully-proven/mobius-causal-fisher-connection-flatness.md`
  - `../2-fully-proven/gamma-damped-mobius-clock-critical-amplification.md`
  - `../2-fully-proven/not_new_scientific_knowledge/coupled-floor-mobius-complementary-shift-incidence-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
- **Proved completion inputs:**
  - `../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`
  - `../2-fully-proven/not_new_scientific_knowledge/sonin-burnol-conductor-cutoff-bounded-graph-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/semilocal-dual-pair-euler-connection-source-law.md`
- **RH consumer:**
  - `../2-fully-proven/not_new_scientific_knowledge/euler-pole-four-unit-anti-causal-budget-law.md`
- **Statement:** Complete the explicit four-unit Mobius divisor-incidence curvature by the actual
  Gamma/Sonin boundary primitive and construct its canonical relative readout.  If that readout is
  nonexpansive and equals the pole-to-divisor seam `ell_E`, then `||ell_E||_2^2<=4` and RH follows.

## Exact source curvature

For `sigma>1`, `epsilon=sigma-1`, let

```text
psi_sigma(d)=Z(sigma)^(-1/2)mu(d)d^(-sigma/2),
Pi_sigma=|psi_sigma><psi_sigma|.                         (1)
```

On the squarefree divisor channel define

```text
Q_t e_d=1_(log d<=t)e_d,
S_t=2Q_t-I,
kappa_(sigma,t)=[Pi_sigma,S_t].                          (2)
```

The input is completely explicit on basis pairs:

```text
kappa_(sigma,t)(d,e)
 =psi_sigma(d)psi_sigma(e)
   (s_e(t)-s_d(t)),
s_d(t)=2*1_(log d<=t)-1.                                (3)
```

The proved incidence-curvature theorem gives the canonical semifinite energy

```text
E_sigma
 =epsilon integral_0^infinity
    ||kappa_(sigma,t)||_HS^2dt,
lim_(sigma->1+)E_sigma=4.                                (4)
```

This is simultaneously calibrated by the proved four-unit Fisher tangent, but it is not obtained
by mapping that tangent through a guessed orbit operator.  It already contains the signed source
line and the lower/upper divisor incidence.

## Exact source packets and completion

Put `sigma=1+2omega`.  For `delta>0`, the complementary packet is

```text
B_(omega,delta,d)
 =d^(-delta)V_(log d)k_(omega,delta)
  -(1/(1+omega))(I-Q_(log d))q_delta.                    (5)
```

The signed coisometry with direction `psi_sigma` sends the direct sum of these packets to the
normalized coupled floor--Mobius error.  The actual archimedean completion has Mellin multiplier

```text
G_omega(s)=gamma(s-omega)/gamma(s+omega).                (6)
```

In logarithmic Sonin coordinates, the scattering involution reverses every divisor translation,
and the logarithmic-position anticommutator is the Burnol conductor:

```text
J_log tau_h=tau_(-h)J_log,
M_tJ_log+J_logM_t=H_infinity J_log.                      (7)
```

The exact Sonin cutoff and its prolate resolvent are already constructed, and the conductor
commutator with that cutoff is bounded.  Thus no common-domain or abstract-intertwiner problem is
left.  The open operation is the source-framed relative readout after `(3)`, `(5)`, and `(6)` have
been sewn.

## Completed incidence-curvature conjecture `[CONJECTURE]`

For finite squarefree `D`, `delta>0`, and `omega>0`, there are source-defined finite relative
operators

```text
K_(omega,delta,D)
 =Comp_(omega,delta,D)(kappa_(sigma,.)|_D),
R_(omega,delta,D)K_(omega,delta,D)
 =completed boundary readout,                            (8)
```

where `Comp` and `R` are obtained only from `(3)`, the packets `(5)`, the Gamma kernel `(6)`, the
Sonin cutoff/resolvent, and the fixed semilocal Euler connection.  They satisfy all five clauses.

1. **Incidence-before-Gamma basis formula.**  Every `(d,e)` entry is the explicit coefficient
   `(3)` multiplied by the two complementary packets `(5)`, then Gamma-completed and Sonin
   compressed.  The order may not be reversed.  No polar decomposition, Xi Gram factorization,
   zero-indexed basis, or target norm may define `Comp`.

2. **Source framing.**  The safe Euler normalization and calibrated Gamma primitive are part of
   `(8)`.  Under insertion of a centered FE--Schwarz rational quartet, the completed readout
   changes by the explicit residue packet of that quartet.  A construction factoring only through
   `(1)`--`(4)` is rejected because those data alone are rational-gauge blind.

3. **Nonexpansive relative readout.**  In the source relative trace fixed by the channel-time
   decomposition,

   ```text
   limsup_(D->all,delta->0,omega->0)
   ||R_(omega,delta,D)K_(omega,delta,D)||_2^2
    <=lim_(sigma->1+)E_sigma=4.                          (9)
   ```

   The inequality must follow from the exact Sonin/Lueders or Schur energy partition on the
   completed source graph.  Merely rescaling the readout to norm one is rejected.

4. **Direct pole-to-divisor identity.**  Before expanding a zero sum, the finite readout is the
   difference between the incoming Euler-pole boundary channel and the completed all-prime
   continuation of the same source connection.  No equality defined only after naming
   `ell_E` is accepted.

5. **Cofinal graph convergence.**  On one source-defined graph core, in the order

   ```text
   D->all, delta->0+, omega->0+,                         (10)
   ```

   the readouts converge weakly in the anti-causal boundary space to `ell_E`.  Changing the order
   requires a uniform graph estimate.

These clauses are the **completed Mobius incidence-curvature transfer**.

## Conditional proof of RH

Clause 5 and weak lower semicontinuity, followed by `(9)`, give

```text
||ell_E||_2^2<=4.                                        (11)
```

The proved Cauchy-energy threshold says `(11)` is equivalent to the absence of a right-half Xi
divisor, hence to RH.  This implication is complete.  Clauses 1--5 are the source producer.

## Why this is not the old contraction criterion

The input of `(9)` is not an arbitrary norm-two vector.  It is the explicit basis curvature `(3)`
with exact source energy `(4)`.  Clause 1 fixes every finite entry before Xi is read; clause 2
forces orbit-sensitive framing; clause 4 requires the pole cancellation identity before residue
expansion.  Without those three clauses, `(8)` would indeed be only the RH-equivalent contraction
criterion in different notation.

## Hard attacks, positive statements, and HT consequences

### 1. Orbit-diagonal completion no-go

An orbit-diagonal Sonin intertwiner consumes the Mobius sign.  The undamped image is outside the
Hilbert domain; canonical Gamma damping repairs the domain but has critical energy
`C_Gamma=4.5085689807...>4`.

**Positive successor:** the signed line enters through the off-diagonal incidence curvature `(3)`,
and Gamma acts only after this curvature is formed.

**HT consequence:** symmetry intertwining can erase a source character on invariant vectors while
retaining it in a commutator curvature.

### 2. Causal derivative no-go

The assembled coupled causal source is Fisher-flat: its Fisher-scaled parameter derivative tends
strongly to zero.

**Positive successor:** the two cancelling causal connection terms are split by the Gamma/Sonin
boundary constraint; their off-diagonal curvature, not their sum, is transported.

**HT consequence:** nonzero projective motion and flat assembled realization can coexist; the
boundary invariant belongs to a change of completion.

### 3. Local-profile no-go

The honest truncated source curvature is

```text
4(1-e^(-u))^2,
```

not the Euler-pole window `4(1-e^(-u))`.

**Positive successor:** use the global norm threshold `(11)`.  Cumulative-energy
reparameterization is rejected as target fitting.

**HT consequence:** equality of total calibrated charge does not imply equality of local boundary
density; global and filtered realizations are distinct invariants.

### 4. Rational-gauge no-go

The squarefree probability and incidence clock survive a symmetric rational quartet insertion.

**Positive successor:** the calibrated Euler connection and Gamma primitive enter clause 2 before
the divisor readout.

**HT consequence:** tangent/incidence geometry may be source-local while exceptional-divisor
orientation lives only in the framed integration torsor.

### 5. Abstract-intertwiner no-go

Any two infinite involutions with matching multiplicities admit many abstract unitary
intertwiners.  Their existence says nothing about the arithmetic source.

**Positive successor:** clauses 1 and 4 demand the exact floor/tail basis packet and the direct
completed source identity.

**HT consequence:** an integration of a constraint curvature has content only after symbol,
affine origin, boundary self-symbol, and source anomaly are retained.

## Novelty and anti-theatre gate

Project theorems are source inputs even when independently found by other agents.  Novelty is
tested only against external literature.  The established external parents include Fisher/Gini
geometry, projection commutators, Sonin spaces, Burnol's conductor, Suzuki's shifted-Xi operator,
and semilocal Euler connections.  Targeted searches have not located the five-clause completed
incidence-curvature transfer.

That search result does not promote the conjecture.  New knowledge begins only with the explicit
finite kernel in clause 1 and its direct identity/nonexpansive cofinal limit.  Until then this card
is a precise research target, not an RH proof.

## Gates

- [x] canonical signed source projection
- [x] exact divisor-incidence commutator kernel
- [x] exact global four-unit relative source energy
- [x] Fisher--Gini calibration
- [x] complementary floor/tail packets
- [x] Gamma/Sonin scattering and bounded conductor cutoff graph
- [x] semilocal Euler connection source
- [x] orbit-diagonal, causal-derivative, and local-profile shortcuts rejected positively
- [ ] write `Comp_(omega,delta,D)` entry by entry
- [ ] prove the direct completed pole-to-divisor identity
- [ ] prove the source-framed nonexpansive relative estimate
- [ ] prove cofinal graph convergence to `ell_E`
- [ ] independent specialist literature audit
- [ ] RH
