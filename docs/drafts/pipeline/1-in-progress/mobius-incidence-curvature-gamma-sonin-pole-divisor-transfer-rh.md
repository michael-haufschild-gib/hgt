# Mobius incidence curvature--Gamma/Sonin pole-to-divisor transfer

- **ID:** `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [HTGEOMETRY-TO-RHTOWER SOURCE PRODUCER]`
- **Scientific status:** `[OPEN CORE] [CONDITIONAL RH PROOF] [LITERATURE NOVELTY OPEN]`
- **Proved source inputs:**
  - `../2-fully-proven/mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `../2-fully-proven/gamma-sonin-asymptotic-passivity-incidence-curvature.md`
  - `../2-fully-proven/complementary-packet-euler-connection-weld.md`
  - `../2-fully-proven/complementary-packet-critical-gini-isometry.md`
  - `../2-fully-proven/mobius-fixed-current-von-mangoldt-critical-transport-weld.md`
  - `../2-fully-proven/complementary-packet-affine-flux-fisher-ward-isometry.md`
  - `../2-fully-proven/squarefree-fixed-current-right-half-ward-localization.md`
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

The unframed analytic part is now proved.  If `mathcalG_omega` is the critical-line multiplier by
`G_omega` and `Q_tau^Sonin` is the exact Sonin projection, then entrywise

```text
kappa^(Gamma,Sonin)_(omega,tau)(d,e)
 =Q_tau^Sonin mathcalG_omega(kappa_(sigma,.)(d,e)),       (7a)
```

and the Gamma multiplier norm tends to one.  Consequently

```text
limsup_(omega->0,D->all)
 2omega sum_(d,e in D)
 ||kappa^(Gamma,Sonin)_(omega,tau)(d,e)||_2^2<=4.         (7b)
```

Thus Gamma/Sonin analytic passivity is closed.  The remaining energy question is whether welding
the floor/tail packet and calibrated Euler connection is trace-neutral or Lueders-orthogonal.

The affine/source weld is also now explicit.  For the continuous packet path `B_h`, the proved
distributional connection equation is

```text
(partial_h-(1+omega))B_h
 =q_delta
  -sum_(m>=1)e^(-delta h)m^(-1-delta)delta_(h+log m).    (7c)
```

Signed Mobius synthesis of `(7c)` is exactly

```text
q_delta/zeta(1+2omega)
 -sum_(n>=1)c_omega(n)n^(-1-omega-delta)delta_(log n).   (7d)
```

Suzuki's Gamma zero moment kills the first term and sends the second to the completed causal
source.  Hence the incidence-before-Gamma basis/source identity is proved; only its placement in
the relative square and the anti-causal graph limit remain open.

That placement now has a proved source-framed energy kernel.  At the boundary `delta=0`, let `B_h`
be the affine packet path and set

```text
K^B_sigma(d,e)
 =2psi_sigma(d)psi_sigma(e)(B_(log e)-B_(log d)).         (7e)
```

Its relative energy satisfies

```text
epsilon sum_(d,e)||K^B_sigma(d,e)||_2^2->4.              (7f)
```

Moreover, entrywise Gamma completion and Sonin projection give

```text
limsup epsilon sum_(d,e)
 ||Q_tau^Sonin mathcalG_omega K^B_sigma(d,e)||_2^2<=4.   (7g)
```

The proof is cofinal rather than pointwise: the packet distance has local slope `zeta(2)>1`, but
at separation `a` it is `a/(1+omega)^2+O(1)`, and the critical divisor separations are of order
`1/epsilon`.  Thus the complete packet framing preserves the four-unit budget on the actual
escaping source state.

## Canonical normal current and critical source transport

The anti-causal readout is no longer an unspecified scalar functional.  Put

```text
A(s)=-zeta'(s)/zeta(s),
nu_sigma(n)=Lambda(n)n^(-sigma)/A(sigma),
tau_sigma(u)=zeta(2sigma)/
  [zeta(sigma)zeta(sigma+u epsilon)].                    (7h)
```

The proved fixed-current transport theorem gives the exact identity

```text
partial_u log tau_sigma(u)
 =epsilon A(sigma+u epsilon)
 =epsilon A(sigma) E_(nu_sigma)
    exp(-u epsilon log n).                               (7i)
```

Thus the normal readout selected by the HT torsor structure is the logarithmic current of the
actual signed Mobius multiplier, and that current is exactly the positive von Mangoldt law.  It is
also the normal derivative of the packet connection because

```text
partial_alpha c_alpha(n)|_(alpha=0)=2Lambda(n).          (7j)
```

The normal shift `alpha` and thermal escape `epsilon` must be kept independent.  At fixed
`Re s>1`, differentiation of

```text
sum_n c_alpha(n)n^(-s)=zeta(s-alpha)/zeta(s+alpha)
```

gives `2A(s)`, whereas the diagonal specialization `s=1+2alpha` tends to `3`.  Hence the old
one-parameter diagonal does not recover the normal current.

After the ordered normal derivative, the squarefree clock `epsilon log d` and the Euler-current
clock `epsilon log n` converge in `W_1` to the same `Exp(1)` law.  Their monotone quantile coupling
has vanishing critical packet cost:

```text
epsilon E||B_(log d)-B_(log n)||_2^2->0.                 (7k)
```

The induced two-edge fields are asymptotically equal in the scaled packet norm, and the Euler
current therefore inherits the same four-unit Gamma/Sonin upper budget:

```text
limsup epsilon E
 ||Q_tau^Sonin mathcalG_omega
   2(B_(log n')-B_(log n))||_2^2<=4.                    (7l)
```

Equations `(7i)`--`(7l)` close the metric-to-source transport.  The remaining operation is sharply
defined: construct the charged anti-causal codifferential of this completed Euler-current edge
field, prove it nonexpansive, and prove that its graph limit is the contour-jump part of
`-2Xi'/Xi`.

The incidence-to-Fisher part of that codifferential is now explicit.  On the affine packet
cocycle, the flux of a packet difference is

```text
Phi_omega(B_k-B_h)=-(k-h)/(1+omega).                    (7m)
```

Conditional edge flux therefore sends

```text
2(B_(H')-B_H)
```

exactly to the centered Fisher coefficient `-2epsilon(H-EH)`.  The input packet energy and output
Fisher energy both tend to four, so this Ward map is an asymptotic isometry on the distinguished
source state.  Its critical Laguerre contact sends the score `2(1-y)` isometrically to the pole
ground state `2e^(-y/2)`.

There is also no longer a divisor ambiguity.  If

```text
J_sq(s)=-d/ds log[zeta(s)/zeta(2s)]
        =A(s)-2A(2s),
Q_sq(s)=Q_arch(s)+2J_sq(s),                              (7n)
```

then

```text
-2Xi'(s)/Xi(s)-Q_sq(s)=4A(2s).                          (7o)
```

The right side is holomorphic for `Re s>1/2`.  Hence `Q_sq` and `-2Xi'/Xi` have exactly the same
strict anti-causal principal-part profile `ell_E`.  The RH-bearing seam has therefore narrowed to
one graph equality: the completed affine-flux Ward curvature must equal the Hardy block curvature
of `Q_sq`.

For a normalized differentiable boundary-unitary source column `(A_alpha,C_alpha)` with
`C_0=0`, twice differentiated unitarity gives

```text
||C'_0||^2
 =-Re <A''_0,A_0>-||A'_0||^2.                           (7p)
```

The second term is nonnegative.  If the first curvature in `(7p)` is the four-unit source
curvature fixed by `(7m)`, then `(7n)`--`(7o)` identify `C'_0=ell_E` and prove RH.  This is the
anti-causal Ward estimate being attacked; it is no longer deferred to an unspecified readout.

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

   The full source-framed packet/Gamma/Sonin inequality is already proved in `(7e)`--`(7g)`, and
   `(7h)`--`(7l)` transfer it to the actual Euler fixed current.  What remains in this clause is
   only that the charged anti-causal codifferential is a contraction of that relative kernel.
   Merely rescaling the readout to norm one is rejected.

4. **Direct pole-to-divisor identity.**  Before expanding a zero sum, the finite readout is the
   charged codifferential of the logarithmic current `(7i)`, equivalently the difference between
   the incoming Euler-pole boundary channel and the completed all-prime continuation of the same
   source connection.  The prime-power current and its Gamma completion are already fixed by
   `(7j)` and the source identity `(7d)`.  Equation `(7o)` proves that the completed squarefree
   current has exactly the Xi strict anti-causal principal parts.  The remaining identity is the
   equality between the completed affine-flux curvature and that squarefree Hardy block.  No
   equality defined only after naming `ell_E` is accepted.

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

### 6. One-clock diagonal no-go

The normal packet shift and the thermal squarefree clock cannot be tied before differentiation:
the diagonal shifted-Euler total tends to `3`, while the correctly ordered normalized normal
current tends to `1`.

**Positive successor:** take the fixed-current derivative first, then use the canonical `W_1`
coupling `(7k)` to transport the thermal four-unit geometry to that current.

**HT consequence:** a constrained HT object can have distinct normal and tangential clocks whose
singular diagonal loses the invariant current even though both parameters approach the same
boundary point.

### 7. Continuous metric selector no-go

The formalized prime-coherence saturation theorem places a continuum-rank differentially
independent orientation family inside every positive weighted prime-metric neighborhood.  Thus no
continuous readout of the incidence metric alone can select the Xi source orientation.

**Positive successor:** the logarithmic current `(7i)` is source-sensitive and necessarily
singular at the vanishing critical overlap; its natural domain is the charged graph rather than
the ambient metric completion.

**HT consequence:** infinitesimal metric neighborhoods of a prime HT source can have continuum
differential rank.  Orientation can live in a fixed current transverse to all continuous metric
coordinates.

### 8. Bounded Fisher-to-current readout no-go

Let

```text
B_sigma(u)=Z_sq(sigma+u epsilon)/Z_sq(sigma),
S_sigma(u)=<chi_sigma,T_(sigma,u)psi_sigma>,
m_sigma=J_sq(sigma).
```

The exact Fisher matrix-coefficient identity is

```text
S_sigma(u)
 =2epsilon B_sigma(u)
   [m_sigma-J_sq(sigma+u epsilon)].                      (12)
```

Therefore

```text
epsilon J_sq(sigma+u epsilon)
 =epsilon m_sigma-S_sigma(u)/(2B_sigma(u)),              (13)

epsilon B_sigma(u)J_sq(sigma+u epsilon)
 =-partial_u B_sigma(u).                                 (14)
```

The Fisher tangent controls the numerator in `(14)`, but extracting the fixed current requires
division by the squarefree overlap.  Under continuation, zeros of `B_sigma` are exactly the strict
right-half Xi divisor by `(7n)`--`(7o)`.  Thus no bounded linear readout of the Fisher tangent can
produce the anti-causal current; hiding `B_sigma^(-1)` inside a named codifferential would be
theatre.

**Positive successor:** formulate the Ward theorem on the closed multiplication graph

```text
Graph(B_sigma)
 ={(f,B_sigma f)},                                      (15)
```

and prove the completed Gamma/Sonin affine-flux numerator in `(14)` lies in its source-selected
range with graph quotient curvature at most four.  This is a concrete divisibility/range theorem,
not an arbitrary contraction.

**HT consequence:** a multiplicative HT torsor can have a Hilbert-controlled tangent numerator
while its fixed logarithmic current lives only in a singular quotient graph.  Exceptional divisors
are failures of graph divisibility, not large tangent vectors.

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
- [x] entrywise Gamma multiplier written on the curvature kernel
- [x] Gamma multiplier norm proved asymptotic to one
- [x] unframed Gamma/Sonin four-unit passivity proved
- [x] continuous complementary packet connection differentiated exactly
- [x] signed packet connection welded to the shifted-Euler source
- [x] Gamma main-density annihilation and completed causal source identity proved
- [x] packet two-point metric computed exactly
- [x] local `zeta(2)` expansion and pointwise-contraction no-go proved
- [x] cofinal packet Gini isometry proved
- [x] full source-framed Gamma/Sonin four-unit energy proved
- [x] logarithmic Mobius fixed current identified with the von Mangoldt source
- [x] normal-shift/thermal-clock diagonal shortcut rejected
- [x] squarefree and Euler clocks coupled with vanishing critical packet cost
- [x] four-unit Gamma/Sonin budget transferred to the Euler fixed current
- [x] affine packet flux proved to recover the Fisher score exactly
- [x] source packet-to-Fisher Ward map proved asymptotically isometric
- [x] Fisher score-to-pole Laguerre contact fixed canonically
- [x] completed squarefree current proved to have anti-causal profile `ell_E`
- [x] boundary-unitary Ward curvature decomposition written explicitly
- [x] semilocal Euler connection source
- [x] orbit-diagonal, causal-derivative, and local-profile shortcuts rejected positively
- [x] write the unframed `Comp_(omega,D)` entry by entry
- [x] write the affine packet/Euler connection weld entry by entry
- [x] prove the packet/Euler-connection weld preserves the critical four-unit energy
- [ ] construct the charged anti-causal fixed-current codifferential
- [ ] prove the completed affine-flux curvature equals the squarefree Hardy block curvature
- [ ] prove the Fisher numerator is divisible by the completed squarefree overlap on the charged graph
- [ ] prove its source-framed nonexpansive relative estimate via `(7p)`
- [ ] prove cofinal graph convergence to `ell_E`
- [ ] independent specialist literature audit
- [ ] RH
