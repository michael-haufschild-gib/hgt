# Möbius Fisher tangent--Sonin boundary lift to the Xi seam

- **ID:** `mobius-fisher-tangent-sonin-boundary-lift-rh`
- **Stage:** 5-failed
- **Type:** `[RETIRED CONJECTURE] [POSITIVE SUCCESSOR EXTRACTED]`
- **Scientific status:** `[FAILED AS FORMULATED] [NOT AN RH PROOF]`
- **Proved source inputs:**
  - `../2-fully-proven/mobius-critical-fisher-tangent-hilbert-lift.md`
  - `../2-fully-proven/gamma-damped-mobius-clock-critical-amplification.md`
  - `../2-fully-proven/mobius-causal-fisher-connection-flatness.md`
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `../3-formalized/not_new_scientific_knowledge/mobius-critical-fisher-stein-contact-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/coupled-floor-mobius-complementary-shift-incidence-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
- **Proved HT inputs:**
  - `../3-formalized/opposite-variance-seam-conservation.md`
  - `../3-formalized/gamma-capacity-current-transgression.md`
  - `source-rigged-clock-domain.md`
- **RH consumer:**
  - `../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/euler-pole-four-unit-anti-causal-budget-law.md`
- **Statement:** Lift the concrete four-unit Fisher tangent of the squarefree-Mobius source through
  the exact complementary floor/tail incidence, the Gamma completion, and the Sonin cutoff.  If
  that source lift converges nonexpansively to the anti-causal Xi seam, the existing four-unit
  criterion proves RH.

## Failure verdict and positive successor

This conjecture is retired as formulated.  Three independent source calculations defeat its
proposed observable:

1. every orbit-diagonal Sonin intertwiner erases the Mobius sign, and the canonical Gamma-damped
   odd tangent has critical energy `C_Gamma=4.5085689807...>4`;
2. the full Fisher-scaled derivative of the assembled coupled causal source tends strongly to
   zero, so the total Leibniz derivative is not the contact seam;
3. the honest divisor-incidence commutator has global energy four but scaled window profile
   `4(1-e^(-u))^2`, not the asserted local profile `4(1-e^(-u))`.

The nontrivial positive successor is
`../1-in-progress/mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`.  It retains
the proved global four-unit incidence curvature and targets the global pole-to-divisor norm
criterion.  No cumulative-energy reparameterization is used to disguise the local-profile
mismatch.

## Why this conjecture is narrower than a contraction criterion

For `sigma>1`, `epsilon=sigma-1`, define the proved source state and tangent

```text
psi_sigma(d)=Z(sigma)^(-1/2)mu(d)d^(-sigma/2),
chi_sigma=-2epsilon(log d-E_sigma log d)psi_sigma.        (1)
```

The paper theorem proves

```text
||psi_sigma||=1,
||chi_sigma||^2 ->4.                                     (2)
```

There is no freedom to choose the input vector or its metric.  The positive and signed critical
responses are the matrix coefficients of the same diagonal semigroup and Mobius parity.  The
completed contact score is the limit of the tangent coefficient.

The only open operation is the analytic boundary lift from this fixed source tangent to the fixed
Xi seam.  Saying merely that some contraction sends one norm-two vector to `ell_E` is rejected.

## Exact doubled clock and signed incidence derivative

At a finite squarefree cutoff `D`, let `psi_(sigma,D)`, `chi_(sigma,D)`, and `J_D` be the finite
normalizations of the source state, tangent, and Mobius parity.  On the doubled source put

```text
S_D(f,g)=(J_D g,J_D f),
Psi_(sigma,D)=2^(-1/2)(psi_(sigma,D),J_D psi_(sigma,D)),
X_(sigma,D)=epsilon diag(L_D-m_(sigma,D),-(L_D-m_(sigma,D))). (3)
```

The source theorem proves exactly

```text
S_D Psi_(sigma,D)=Psi_(sigma,D),
S_D X_(sigma,D)Psi_(sigma,D)=-X_(sigma,D)Psi_(sigma,D),
||[X_(sigma,D),S_D]Psi_(sigma,D)||^2
 =||chi_(sigma,D)||^2.                                      (4)
```

The same source state is the signed coisometry direction of the complementary incidence.  On the
channel sum, write

```text
R_(sigma,D)((f_d))=sum_(d in D)psi_(sigma,D)(d)f_d,
Pi_(sigma,D)=R_(sigma,D)^*R_(sigma,D).                     (5)
```

For the finite incidence feature `Y_(sigma,delta,D)` obtained from the packets below, the parent
projection theorem gives

```text
R_(sigma,D)Y_(sigma,delta,D)
 =the normalized finite coupled floor--Mobius error.        (6)
```

Differentiating the finite normalized source law is exact:

```text
4epsilon partial_sigma R_(sigma,D)((f_d))
 =sum_(d in D)chi_(sigma,D)(d)f_d,

4epsilon partial_sigma Pi_(sigma,D)
 =|chi_(sigma,D)><psi_(sigma,D)|
  +|psi_(sigma,D)><chi_(sigma,D)|.                         (7)
```

Thus the Fisher tangent, the signed cancellation angle, and the incidence feature are three faces
of one moving pointed projection.  Their total causal connection is the covariant Leibniz derivative

```text
4epsilon partial_sigma(R_(sigma,D)Y_(sigma,delta,D))
 =4epsilon(partial_sigma R)Y
  +4epsilon R(partial_sigma Y),                            (8)
```

The causal-flatness theorem proves that `(8)` tends strongly to zero at Fisher scale after the
coupled source is assembled.  Therefore `(8)` itself is not the contact tangent.  The surviving
candidate is its **boundary splitting curvature**: the Gamma/Sonin projection acts on the two
terms before they recombine, and the Lueders-erased cross block records their failure to cancel in
the boundary completion.  The first term retains the Fisher normalization and signed incidence;
the second is its causal connection counterterm.  Neither may be discarded or recombined before
the boundary projection.

## Exact finite source incidence

Put `sigma=1+2omega`.  For `delta>0`, let

```text
H=L2(R_(>=0)),
P_d=1_([log d,infinity)),
q_delta(t)=e^(-delta t),
k_(omega,delta)(t)
 =e^(-(1+omega+delta)t)R_omega(e^t).                     (9)
```

The proved complementary-incidence packet is

```text
B_(omega,delta,d)
 =d^(-delta)V_(log d)k_(omega,delta)
  -(1/(1+omega))(I-P_d)q_delta.                         (10)
```

At a finite squarefree cutoff `D`, form the channel space

```text
K_D=direct_sum_(d in D) H                               (11)
```

and the basis-defined incidence

```text
I_(omega,delta,D)e_d
 =the vector supported in channel d with value B_(omega,delta,d). (12)
```

The signed synthesis is not conjectural: with the normalized squarefree weights it is the finite
version of the proved coisometry, and its cofinal limit reproduces the coupled floor--Mobius error.
The diagonal projection

```text
P_D=direct_sum_(d in D)P_d                              (13)
```

is also source-fixed.  It records the divisor incidence `d<=e^t`; it is not chosen from Xi.

The Gamma completion is Suzuki's explicit kernel, whose Mellin multiplier is

```text
G_omega(s)=gamma(s-omega)/gamma(s+omega).               (14)
```

Its zero at the Euler main pole supplies the singular boundary renormalization which is missing
from the raw `L2` incidence.

## Source tangent boundary-lift conjecture `[CONJECTURE]`

There is a source-rigged completion of `(11)`--`(14)` on which the following finite objects are
defined from the displayed formulas alone:

```text
X_(omega,delta,D,u)     completed clock-incidence derivative observable,
Phi_(omega,delta,D,u)  Sonin/Lueders cutoff channel,
A_(omega,delta,D,u)=X-Phi(X).                           (15)
```

They must satisfy all six clauses below.

1. **Clock--coisometry input.** Before Gamma completion, `X` is the self-adjoint finite clock
   connection `(3)`--`(4)` acting on the ordered pair of signed incidence terms in `(8)`.  Its
   channel-index tangent is exactly `(7)`.  Both terms must occur with their displayed
   coefficients, but the Gamma/Sonin projection must split them before their proved causal
   cancellation.  Replacing this curvature by an arbitrary rank-one operator, the total flat
   derivative, or either isolated term is rejected.

2. **Basis formula.** On every channel basis pair, the lifted kernel is obtained by applying the
   packets `(10)`, signed coisometry `(5)`--`(8)`, the explicit Gamma kernel `(14)`, and the cutoff
   `(13)`.  Incidence must occur before the Gamma square.  No
   polar decomposition, target Gram factorization, Xi Blaschke factor, or zero-indexed basis may
   be used to define it.

3. **Structural energy.** The disturbance identity is the already formalized star-Kadison/Lueders
   orthogonal decomposition, so before the critical limit

   ```text
   ||A_(omega,delta,D,u)||_HS
    <=||X_(omega,delta,D,u)||_HS.                        (16)
   ```

   The completed incidence-relative observable, not the diagonal orbit lift, must obey:

   ```text
   limsup_(delta->0,D->all,omega->0)
   ||X_(omega,delta,D,u)||_HS^2
    <=4(1-e^(-u))+o(u).                                 (17)
   ```

   Equation `(17)` must be derived from `(2)`, `(6)`--`(8)`, and the contact identity, not imposed
   as an independent estimate.  The diagonal Gamma orbit energy is known to tend to
   `C_Gamma>4`; the incidence/relative term must account source-theoretically for any energy
   removed before `(17)` can hold.

4. **Direct source identity.** At every finite stage, `A` is the completed boundary strip of the
   signed prime--Gamma logarithmic graph produced from `(5)`--`(14)`.  Equality only after expanding Xi
   residues is rejected.

5. **Graph-core convergence.** On one source-defined core, in the order

   ```text
   D->all, delta->0+, omega->0+,                         (18)
   ```

   the operators `A_(omega,delta,D,u)` converge weakly to `Q_uD_Xi`, the one-sided anti-causal Xi
   boundary operator.  The order may be changed only after proving uniformity.

6. **Framing test.** A centered FE--Schwarz rational quartet changes the lifted normal boundary
   functional and therefore changes the limit in clause 5.  If the lift factors only through the
   unframed DA/HT source quotient, it is rejected.

Call these clauses the **Möbius Fisher tangent--Sonin boundary lift**.

## Conditional proof of RH

The star-Kadison identity gives `(16)`.  The source calibration `(17)` and weak lower
semicontinuity give

```text
Delta_Xi(u)=||Q_uD_Xi||_(HS,ext)^2
 <=4(1-e^(-u))+o(u).                                    (19)
```

Divide by `u` and let `u->0+`:

```text
limsup Delta_Xi(u)/u<=4.                                (20)
```

The proved relative-trace/Cauchy-energy theorem says that any off-critical zero makes this density
strictly greater than `4`.  Hence `(16)`--`(20)` prove RH once the six clauses hold.

The implication is complete.  Clauses 1--5, especially the incidence-before-Gamma identity and
its calibration/convergence, are the open proof-bearing content.

## Hard attacks, positive statements, and general HT consequences

### 1. Ordinary-Hardy-block no-go

For a Hankel kernel `ell(x+y)`, the kernel value `ell(x)` is obtained from a boundary delta, not
from an `L2` input.  Applying the ordinary Hankel block to an `L2` vector smooths `ell`; it cannot
realize clause 5 with the Fisher tangent by a formal identification.

**Positive successor:** the lift is a source-incidence map on the doubled continuation graph,
not the standard leakage Hankel operator.  The source-rigged boundary functional is essential.

**General HT insight:** a constrained HT boundary comparison can be bounded on its tangential
Hilbert sector while remaining distributional in its normal source direction.

### 2. Singular signed-response no-go

The signed Mobius coefficient is `O(epsilon^2)`.  Its nonzero critical response appears only after
`epsilon^(-2)` renormalization, which is not uniformly bounded on the squarefree Hilbert space.

**Positive successor:** sew the Fisher tangent and signed normal response inside the Gamma rigging
before taking the critical limit.

**General HT insight:** the critical source object is a tangent--normal pair, not one Hilbert
vector or one scalar transfer function.

### 3. Factorial-Fock no-go

The proved prime--Laplace/Gamma theorem shows that every finite jet incidence is Hilbert--Schmidt
but the cofinal factorial-Fock map has unbounded prime columns.

**Positive successor:** clause 5 uses the projective/source-rigged graph topology and asks only for
the relative boundary trace.

**General HT insight:** all finite observations may be faithful while no bounded Hilbert colimit
exists; cofinality and bounded synthesis are independent properties.

### 4. Universal Gamma-current no-go

Pairing the rank-one Gamma current

```text
C_n(a)_i=(n+1)a_n/(n+1-i)!                              (21)
```

with the factorial conormal gives

```text
Lambda(C_n a)
 =(n+1)a_n(2^(n+2)-2)/(n+2)!.                           (22)
```

For the jet of any entire function, Cauchy's estimate at any radius `R>2` makes `(22)` tend to
zero.  Therefore “the boundary charge vanishes at infinity” is universal analyticity and cannot
annihilate the zeta-specific reflected Mertens orbit charge.

**Positive theorem:** a Gamma boundary current can remain nonzero at every finite clock while its
conormal evaluation tends to zero on every entire section.

**General HT insight:** nontermination of a finite source current and nonzero evaluated charge at
the analytic boundary are distinct invariants.  A useful RH coupling must preserve the Euler
framing, not merely entire-section convergence.

### 5. Isometric-graph no-go

The canonical Xi multiplier graph is already closed and isometric on its maximal Hardy domain;
its missing model-space inputs are exactly the off-line zeros.  Constructing another isometric
graph is not progress.

**Positive successor:** clause 5 targets one concrete source tangent and the relative boundary
trace, while clause 4 forces a pre-divisor source identity.

**General HT insight:** the obstruction may be a domain defect rather than a norm defect; source
framing must decide whether a distinguished tangent crosses that domain boundary.

### 6. Rational-gauge falsifier

FE, Schwarz symmetry, order one, and unframed HT data survive a centered rational quartet.

**Positive successor:** the exact safe Euler normalization and Gamma boundary primitive are part
of the rigged lift, so the inserted orbit changes the normal functional.

**General HT insight:** localized differential/source classes describe the tangent geometry but a
calibrated primitive is needed to retain exceptional-divisor orientation.

### 7. Orbit-diagonal Gamma--Sonin no-go

Every basis-diagonal map intertwining the doubled Mobius clock with Sonin reflection must attach
the Mobius sign to one of the two reflected orbit sectors.  On the invariant Fisher state this
sign cancels identically.  Without Gamma damping the resulting positive orbit sum is not a Hilbert
vector for `1<sigma<=2`.  With the canonical time-one damping, the odd tangent is a valid Hilbert
vector but has the proved critical energy

```text
C_Gamma
 =6sqrt(2)Gamma(1/4)/(pi^(3/2)Gamma(3/4))
 =4.5085689807...>4.                                    (23)
```

Thus the canonical orbit lift both loses signed arithmetic and amplifies the unit doubled tangent.

**Positive successor:** use the moving signed coisometry and the full Leibniz derivative `(8)`;
insert the complementary floor/tail packets before the Gamma square and take only the canonical
principal-relative boundary trace.  The incidence term must supply the missing signed angle and
account for the source-derived Gamma excess in `(23)`.

**General HT insight:** an archimedean completion can repair the cofinal Hilbert domain while
failing metric passivity by a finite residue-density constant.  Domain repair and energy
contraction are independent invariants of a constrained HT boundary object.

### 8. Assembled-causal-derivative no-go

The exact coupled causal multiplier is right-differentiable at the critical boundary in Hardy
norm.  Consequently its Fisher-scaled parameter derivative, and the derivative of the normalized
coisometry value `R_sigma Y_sigma`, tend strongly to zero.  Thus the total Leibniz derivative `(8)`
cannot be the nonzero completed contact score.

**Positive successor:** the two terms of `(8)` form a causally cancelling connection pair.  Apply
the Gamma/Sonin projection before recombination and identify its Lueders-erased off-diagonal block
with the anti-causal boundary seam.  This is a concrete calibrated clock curvature, and the
formalized Bianchi/boundary-channel conservation laws become actual compatibility tests rather
than metaphors.

**General HT insight:** finite-clock projective motion may be nonzero while the assembled causal
realization is connection-flat.  A nontrivial HT boundary invariant can therefore be curvature of
a change of completion even when no source flow survives.

## Literature novelty gate

The ingredients have established parents: exponential-family Fisher geometry, Mobius inversion,
Hardy/Sonin projections, Lueders pinching, conservative realization, and Suzuki's shifted-Xi
canonical system.  Targeted searches located no published construction of the six-clause lift,
nor a squarefree-Mobius Fisher tangent whose Gamma/Sonin disturbance converges to the Xi
anti-causal seam.

This is the correct relaxed novelty verdict:

- the project's source theorems are valid new inputs to be composed, not novelty failures;
- a literature theorem already providing clauses 2, 4, and 5 would make this route unlikely to be
  new or RH-bearing;
- no such theorem was located;
- the conjecture itself is not knowledge.  Only the explicit basis lift and convergence proof
  would be novel and significant.

## Gates

- [x] canonical source Hilbert state and tangent constructed
- [x] exact four-unit Fisher limit proved
- [x] positive/signed matrix coefficients and contact limit proved
- [x] complementary floor/tail incidence constructed
- [x] signed source coisometry constructed
- [x] doubled source clock and exact QFI commutator constructed
- [x] signed coisometry derivative tied exactly to the Fisher tangent
- [x] Gamma/Sonin and relative-trace consumers identified
- [x] generic bounded-colligation redressing rejected
- [x] universal entire-current trace rejected with positive theorem
- [x] orbit-diagonal Sonin lift rejected with exact super-four Gamma energy
- [x] assembled causal derivative rejected by exact Fisher-flatness theorem
- [x] boundary splitting curvature selected as the surviving source object
- [ ] write the finite basis lift in clause 2
- [ ] prove the direct completed-source identity in clause 4
- [ ] prove the source calibration `(17)` from the Fisher contact law and incidence derivative
- [ ] prove graph-core convergence in clause 5
- [ ] prove the four-unit relative-trace estimate
- [ ] RH
- [ ] independent specialist literature audit
