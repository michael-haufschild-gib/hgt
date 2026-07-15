# Möbius Fisher tangent--Sonin boundary lift to the Xi seam

- **ID:** `mobius-fisher-tangent-sonin-boundary-lift-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [HTGEOMETRY-TO-RHTOWER SOURCE PRODUCER]`
- **Scientific status:** `[OPEN CORE] [CONDITIONAL RH PROOF] [LITERATURE NOVELTY OPEN]`
- **Proved source inputs:**
  - `../2-fully-proven/mobius-critical-fisher-tangent-hilbert-lift.md`
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `../3-formalized/not_new_scientific_knowledge/mobius-critical-fisher-stein-contact-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/coupled-floor-mobius-complementary-shift-incidence-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
- **Proved HT inputs:**
  - `../3-formalized/opposite-variance-seam-conservation.md`
  - `../3-formalized/gamma-capacity-current-transgression.md`
  - `source-rigged-clock-domain.md`
- **RH consumer:**
  - `../2-fully-proven/not_new_scientific_knowledge/euler-pole-four-unit-anti-causal-budget-law.md`
- **Statement:** Lift the concrete four-unit Fisher tangent of the squarefree-Mobius source through
  the exact complementary floor/tail incidence, the Gamma completion, and the Sonin cutoff.  If
  that source lift converges nonexpansively to the anti-causal Xi seam, the existing four-unit
  criterion proves RH.

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

## Exact finite source incidence

Put `sigma=1+2omega`.  For `delta>0`, let

```text
H=L2(R_(>=0)),
P_d=1_([log d,infinity)),
q_delta(t)=e^(-delta t),
k_(omega,delta)(t)
 =e^(-(1+omega+delta)t)R_omega(e^t).                     (3)
```

The proved complementary-incidence packet is

```text
B_(omega,delta,d)
 =d^(-delta)V_(log d)k_(omega,delta)
  -(1/(1+omega))(I-P_d)q_delta.                          (4)
```

At a finite squarefree cutoff `D`, form the channel space

```text
K_D=direct_sum_(d in D) H                                (5)
```

and the basis-defined incidence

```text
I_(omega,delta,D)e_d
 =the vector supported in channel d with value B_(omega,delta,d). (6)
```

The signed synthesis is not conjectural: with the normalized squarefree weights it is the finite
version of the proved coisometry, and its cofinal limit reproduces the coupled floor--Mobius error.
The diagonal projection

```text
P_D=direct_sum_(d in D)P_d                               (7)
```

is also source-fixed.  It records the divisor incidence `d<=e^t`; it is not chosen from Xi.

The Gamma completion is Suzuki's explicit kernel, whose Mellin multiplier is

```text
G_omega(s)=gamma(s-omega)/gamma(s+omega).                (8)
```

Its zero at the Euler main pole supplies the singular boundary renormalization which is missing
from the raw `L2` incidence.

## Source tangent boundary-lift conjecture `[CONJECTURE]`

There is a source-rigged completion of `(5)`--`(8)` on which the following finite objects are
defined from the displayed formulas alone:

```text
X_(omega,delta,D,u)     completed Fisher-tangent contact observable,
Phi_(omega,delta,D,u)  Sonin/Lueders cutoff channel,
A_(omega,delta,D,u)=X-Phi(X).                            (9)
```

They must satisfy all six clauses below.

1. **Fisher input.** Before the incidence and Gamma lift, `X` is the rank-one tangent observable

   ```text
   |chi_sigma,D><psi_sigma,D|.                           (10)
   ```

   At finite cutoff, `Z(sigma)` and `m_sigma` are replaced by their finite partition function and
   finite expectation, so `psi_sigma,D` is normalized and `chi_sigma,D` remains centered.  These
   are canonical restrictions of the source law, not fitted approximations.

2. **Basis formula.** On every channel basis pair, the lifted kernel is obtained by applying the
   packets `(4)`, signed synthesis, the explicit Gamma kernel `(8)`, and the cutoff `(7)`.  No
   polar decomposition, target Gram factorization, Xi Blaschke factor, or zero-indexed basis may
   be used to define it.

3. **Structural energy.** The disturbance identity is the already formalized star-Kadison/Lueders
   orthogonal decomposition, so before the critical limit

   ```text
   ||A_(omega,delta,D,u)||_HS
    <=||X_(omega,delta,D,u)||_HS.                         (11)
   ```

   The Gamma boundary rigging must make the source tangent line isometric in the limit:

   ```text
   limsup_(delta->0,D->all,omega->0)
   ||X_(omega,delta,D,u)||_HS^2
    <=4(1-e^(-u))+o(u).                                  (12)
   ```

   Equation `(12)` must be derived from `(2)` and the contact identity, not imposed as an
   independent estimate.

4. **Direct source identity.** At every finite stage, `A` is the completed boundary strip of the
   signed prime--Gamma logarithmic graph produced from `(4)`.  Equality only after expanding Xi
   residues is rejected.

5. **Graph-core convergence.** On one source-defined core, in the order

   ```text
   D->all, delta->0+, omega->0+,                          (13)
   ```

   the operators `A_(omega,delta,D,u)` converge weakly to `Q_uD_Xi`, the one-sided anti-causal Xi
   boundary operator.  The order may be changed only after proving uniformity.

6. **Framing test.** A centered FE--Schwarz rational quartet changes the lifted normal boundary
   functional and therefore changes the limit in clause 5.  If the lift factors only through the
   unframed DA/HT source quotient, it is rejected.

Call these clauses the **Möbius Fisher tangent--Sonin boundary lift**.

## Conditional proof of RH

The star-Kadison identity gives `(11)`.  The source calibration `(12)` and weak lower
semicontinuity give

```text
Delta_Xi(u)=||Q_uD_Xi||_(HS,ext)^2
 <=4(1-e^(-u))+o(u).                                    (14)
```

Divide by `u` and let `u->0+`:

```text
limsup Delta_Xi(u)/u<=4.                                 (15)
```

The proved relative-trace/Cauchy-energy theorem says that any off-critical zero makes this density
strictly greater than `4`.  Hence `(15)` proves RH.

The implication is complete.  Clauses 2, 4, and 5 are the open proof-bearing content.

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
C_n(a)_i=(n+1)a_n/(n+1-i)!                              (16)
```

with the factorial conormal gives

```text
Lambda(C_n a)
 =(n+1)a_n(2^(n+2)-2)/(n+2)!.                           (17)
```

For the jet of any entire function, Cauchy's estimate at any radius `R>2` makes `(17)` tend to
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
- [x] Gamma/Sonin and relative-trace consumers identified
- [x] generic bounded-colligation redressing rejected
- [x] universal entire-current trace rejected with positive theorem
- [ ] write the finite basis lift in clause 2
- [ ] prove the direct completed-source identity in clause 4
- [ ] prove the source calibration `(12)` from the Fisher contact law
- [ ] prove graph-core convergence in clause 5
- [ ] prove the four-unit relative-trace estimate
- [ ] RH
- [ ] independent specialist literature audit
