# Coherence-local prime-tail differential-building saturation

- **ID:** `coherence-local-prime-tail-differential-building-saturation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GENERAL HT CONSTRAINT GEOMETRY
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY UNVERIFIED]`
- **Parents:** `prime-dirichlet-tail-differential-matroid`,
  `prime-tail-differential-building-polarization-law`, and the classical coherent-shift
  square-summability criterion
- **Statement:** Whenever the local amplitudes of a countable sign carrier have zero as an
  accumulation point, every arbitrarily small Hilbert-coherence neighborhood contains continuum
  many tail classes whose every finite subfamily is linearly independent.  For prime Dirichlet
  carriers this produces, inside one coherent sector and at arbitrarily high pairwise fidelity, a
  differential field of transcendence degree continuum.

## Abstract coherence--tail dichotomy

Let `I` be countably infinite, let `r_i>0`, and put

```text
d_r(epsilon,delta)^2
  = sum_i r_i^2 |epsilon_i-delta_i|^2,
epsilon,delta in {+1,-1}^I,                              (1)
```

with value `+infinity` when the series diverges.  Let

```text
Q_I = C^I / C^(I)                                      (2)
```

be the quotient by finite support.

### Theorem A: sharp coherence-faithfulness dichotomy `[PROVED HERE]`

Exactly one of the following alternatives holds.

1. If `inf_i r_i>0`, then

   ```text
   d_r(epsilon,delta)<infinity
     iff epsilon and delta differ at finitely many coordinates.     (3)
   ```

   Thus Hilbert-coherence equivalence is exactly equality in the finite-tail quotient.

2. If `inf_i r_i=0`, then for every base orientation `epsilon_0` and every `eta>0` there is a
   family

   ```text
   E subset {+1,-1}^I,       |E|=2^aleph_0,                         (4)
   ```

   such that

   ```text
   d_r(epsilon,epsilon_0)<eta                for every epsilon in E,
   d_r(epsilon,delta)<eta                    for epsilon,delta in E,
   {[epsilon]:epsilon in E} is finitely linearly independent in Q_I. (5)
   ```

   The last clause means that every finite subfamily of distinct classes is linearly independent.
   Hence every coherence neighborhood contains a free tail matroid of rank continuum.

Define the local tail-information capacity of a coherence ball by

```text
Cap_r(epsilon_0,eta)
  = dim_C Span{[epsilon] : d_r(epsilon,epsilon_0)<eta} in Q_I.  (6)
```

Theorem A gives the exact zero--one law

```text
Cap_r(epsilon_0,eta)
  = 1             if inf_i r_i>0,
  = 2^aleph_0     if inf_i r_i=0,                            (7)
```

for every base orientation and every finite `eta>0`.  Indeed, in the positive-floor branch every
finite-distance orientation differs only finitely and hence has the same tail line; in the
zero-floor branch `(5)` gives the lower bound `2^aleph_0`, while `C^I` itself has dimension at most
`2^aleph_0`.  Thus local HT capacity has no intermediate phase: collapse of the per-coordinate
distinguishability floor produces maximal tail rank in every neighborhood.

### Proof of Theorem A

If `r_i>=c>0` and two sign sequences differ on an infinite set, every nonzero summand in `(1)` is
at least `4c^2`; the sum diverges.  Finite differences plainly have finite energy.  This proves the
first alternative.

Assume `inf_i r_i=0`.  Choose a countably infinite set `S subset I` with

```text
sum_(i in S) r_i^2 < eta^2/4.                            (8)
```

This is possible by choosing distinct `i_n` successively with, for example,
`r_(i_n)^2 < eta^2 2^(-n-4)`.

We use an explicit independent family on a countable set.  Put

```text
Omega = {(n,h): n in N and h:{0,1}^n -> {0,1}}.
```

The set `Omega` is countable.  For each infinite binary sequence `x in {0,1}^N`, define

```text
B_x = {(n,h) in Omega : h(x restricted to n)=1}.          (9)
```

Fix distinct `x_1,...,x_m` and a Boolean pattern `b in {0,1}^m`.  For every sufficiently large
`n`, the prefixes `x_j restricted to n` are distinct, so one may choose `h` taking the prescribed
value `b_j` at those prefixes.  Therefore every Boolean membership pattern for
`B_(x_1),...,B_(x_m)` occurs at infinitely many points of `Omega`.

Transport the family `(B_x)` to `S` by a bijection.  Define `phi_x in {+1,-1}^I` to equal `-1` on
the transported copy of `B_x` and `+1` elsewhere.  Every sign pattern for a finite family
`phi_(x_1),...,phi_(x_m)` consequently recurs infinitely often on `S`.

Suppose

```text
sum_(j=1)^m a_j [phi_(x_j)] = 0 in Q_I.                 (10)
```

Outside a finite set, the linear form `v |-> sum_j a_j v_j` therefore vanishes on the recurring
sign vectors.  Every `v in {+1,-1}^m` recurs infinitely, so it vanishes on the entire sign cube.
Comparing `v` with the vector obtained by reversing only its `j`th coordinate gives `2a_jv_j=0`.
Thus every `a_j=0`, proving finite linear independence.

Finally set

```text
epsilon_x = epsilon_0 phi_x.                             (11)
```

Multiplication by `epsilon_0` is an invertible diagonal map of `Q_I`, so it preserves the
independence just proved.  Every difference in `(11)` is supported in `S`; equations `(1)` and `(8)`
give all the strict bounds in `(5)`.  Since `{0,1}^N` has cardinality `2^aleph_0`, this proves the
second alternative.  QED.

## The sector-blind sparse-tail algebra

For sign carriers, the exact information discarded by coherence is the Boolean ideal

```text
J_r = {A subset I : sum_(i in A) r_i^2 < infinity}.      (12)
```

Finite-tail equality uses the ideal `Fin`.  Thus

```text
J_r/Fin                                                  (13)
```

is the sparse-tail information that a Hilbert-sector label cannot see.  Theorem A says:

```text
J_r=Fin                    iff inf_i r_i>0,
J_r/Fin nontrivial         iff inf_i r_i=0,              (14)
```

and in the second case the blindness is locally maximal rather than one-dimensional: every
coherence ball contains a continuum-rank free tail matroid.

## Half-density dephasing fiber

Let `p_i>0` be a probability distribution on a countably infinite set `I`, and define its signed
half-density lifts

```text
psi_epsilon(i)=sqrt(p_i) epsilon_i,       epsilon in {+1,-1}^I.  (15)
```

Every lift has unit mass.  Moreover

```text
||psi_epsilon-psi_delta||_2^2
  = 4 sum_(i:epsilon_i!=delta_i) p_i,                         (16)

<psi_epsilon,psi_delta>
  = 1-2 sum_(i:epsilon_i!=delta_i) p_i.                       (17)
```

Because a faithful probability distribution on a countably infinite set has `inf_i p_i=0`,
Theorem A applies with `r_i=sqrt(p_i)`.

### Corollary A1: maximal dephasing-erasure capacity `[PROVED HERE]`

For every signed half-density `psi_(epsilon_0)` and every Hilbert radius `eta>0`, its `eta`-ball
contains continuum many signed half-densities whose sign classes are finitely linearly independent
in `Q_I`.  All of their pure density matrices have the same complete dephasing:

```text
Dephase(|psi_epsilon><psi_epsilon|)=diag(p).                 (18)
```

Thus one diagonal state has a continuum-rank tail-constraint fiber, locally in every phase lift.
Every quantity determined only by `p`--including its Rényi-2 purity, diagonal Hamiltonian moments,
and energy-origin gauge class--is constant on that entire fiber.  Tensor products multiply the
half-density overlaps but do not remove the fiber: applying the construction in either factor
already supplies continuum local tail rank.

The conclusion is specific to the infinite carrier.  A finite state space has no nontrivial
finite-support quotient.  Passing from finite systems to a faithful countably infinite state
therefore changes the local tail-information capacity from trivial finite rank to continuum,
without requiring a special Hamiltonian or a thermodynamic flow.

The companion formalization target
`coherence-end-projective-ht-tail-reconstruction.md` proves the exact sparse
off-diagonal repair.
If only density-matrix entries along a connected locally finite graph are retained, their
finite-defect ambiguity is the clopen algebra of the graph's end space.  They recover the
projective HT field class for every phase lift exactly when the graph is one-ended.  Moreover, the
Cartesian product of two infinite connected locally finite graphs is one-ended.  Hence diagonal
tensor factorization preserves the dephasing fibre, while the associated product coherence network
can eliminate all end-wise projective-tail ambiguity.  These are different statements: tensoring
does not make diagonal data phase-sensitive, but it can make a retained sparse off-diagonal
network tail-faithful.

## Prime-Dirichlet specialization

Enumerate the rational primes and take

```text
r_p=p^(-sigma),                  sigma>0.                (19)
```

Then `inf_p r_p=0`, so the second branch of Theorem A applies at every positive horizontal weight,
including the critical half-density `sigma=1/2`.

For a sign orientation `epsilon`, put

```text
P_epsilon(z)=sum_p epsilon(p)p^(-z),       Re(z)>1,       (20)
K_epsilon=E_fin<P_epsilon>_D.                            (21)
```

Let `E` be the family supplied by Theorem A.  Every finite subfamily has finite joint coefficient
range and linearly independent tail classes.  The finite-range operator-tail theorem therefore
gives:

### Theorem B: local maximal differential independence `[PROVED HERE]`

For every `sigma>0`, every base orientation, and every `eta>0`, there are continuum many
orientations in its `d_r`-ball of radius `eta` such that every finite family of their prime
Dirichlet carriers, together with every finite translate palette whose shifts have distinct real
parts, is differentially algebraically independent over `E_fin`.

Consequently the differential compositum generated by this family has

```text
dtrdeg_(E_fin) = 2^aleph_0.                              (22)
```

The prime-tail differential building generated by these orientations therefore has continuum
rank inside every coherence neighborhood.

## Coherent-sector formulation

Attach to `epsilon` the formal prime displacement

```text
alpha_epsilon(p)=r_p epsilon(p).                         (23)
```

The standard coherent-shift criterion identifies two CCR representations precisely when the
difference of their displacements is square summable.  Hence all orientations in Theorem B lie in
one normal/unitary coherent sector.  In a common coherent realization their pairwise vector
overlaps satisfy

```text
|<Psi_epsilon,Psi_delta>|
  = exp(-d_r(epsilon,delta)^2/2)
  > exp(-eta^2/2).                                       (24)
```

Thus arbitrarily high pairwise fidelity is compatible with continuum differential transcendence
degree.  Coherence, purity, Rényi overlap, and normal-sector equivalence metrize a quotient of the
HT landscape; none is a complete invariant of its differential fields.

## Significance and parent-theory attack

- **Coherent-state parent:** square-summable displacement equivalence and `(24)` are classical.
- **Set-theoretic parent:** independent families of subsets of a countable set of cardinality
  continuum are classical; `(7)` supplies the needed construction directly.
- **Differential-algebra parent:** the passage from recurring sign patterns to differential
  independence is the operator-tail theorem of the parent card.
- **Lineability/algebrability parent:** large free algebras and dense pathological subsets of
  Dirichlet-series Banach spaces are established themes.  In particular, Alves--Brito--Carando
  prove strong algebrability and large Hilbert/Banach subspaces for Dirichlet series with maximal
  Bohr strip (`arXiv:2109.14305`).  Their property is convergence geometry, not differential
  independence of all jets; their neighborhoods are not coherent-shift sectors; and their
  coefficients are not confined to one Boolean tail cube.  Theorem B is therefore not an instance
  of that result, but the algebrability literature is a mandatory adjacent audit.
- **Candidate residue:** the sharp local saturation statement: every arbitrarily small coherent
  neighborhood contains a continuum-rank prime-tail differential building.  No parent theory can
  formulate this without simultaneously using the Hilbert-sector quotient and the exact
  Dirichlet differential-field classifier.
- **Preliminary literature verdict:** searches across coherent CCR representations, Dirichlet
  hypertranscendence, and Boolean independent-family theory found the three parents separately but
  no theorem asserting local maximal differential transcendence inside one coherent sector.
- **Retirement condition:** downgrade to `[BRIDGE]` if an existing source proves the combined local
  saturation theorem, or if the operator-tail analytic transfer fails for the continuum family.
  The latter risk is limited because differential independence is a finite-character property and
  is applied only to finite subfamilies.

The result is stronger than the existing `E_0`/indiscrete-quotient theorem.  That theorem says
same-field strata are topologically inseparable.  The present theorem says a physically natural
metric may regard continuum many maximally independent fields as arbitrarily close and normally
equivalent.

## Positive needle in a saturated coherence sector

Let `epsilon_+(p)=1` for every prime.  The parent prime-tail theorem proves that, for every
`x>1`, the vertical function

```text
t |-> P_epsilon(x+it)                                    (25)
```

is positive definite exactly when `epsilon=epsilon_+`: it is the Fourier transform of the atomic
measure `sum_p epsilon(p)p^(-x) delta_(log p)`, and Fourier-transform uniqueness forces every atom
to have nonnegative mass.

Combining this pointing theorem with Theorem B gives the following exact geometry.

### Theorem C: order-pointed, information-nonisolated zeta tail `[PROVED HERE]`

For every `sigma>0` and every `eta>0`, the `d_(p^(-sigma))`-ball of radius `eta` about
`epsilon_+` contains continuum many orientations whose prime Dirichlet carriers are finitely
differentially algebraically independent, while `epsilon_+` is the unique orientation in the
entire Boolean cube satisfying the positive-definiteness condition `(25)`.

Thus the zeta tail is a unique order point but is maximally nonisolated in coherence geometry.
The exact pointing is necessarily discontinuous for the coherence topology: flipping one
sufficiently remote prime makes an arbitrarily small coherent perturbation and destroys positive
definiteness.  The order cone and the information metric are therefore transverse structures, not
two descriptions of one phase.

## RH audit

The theorem neither proves nor reformulates RH.  It leaves the reflected Shale diagonal intact:
the specific source pair `s` and `1-conj(s)` is sector-compatible only on the critical line.

It does impose a new positive architectural requirement on any RH route using prime coherence:

```text
source-faithful coherent carrier
  = coherent-sector datum
    + a polarization separating J_r/Fin.                (26)
```

A normal intertwiner, fidelity, purity, or sector label can locate a compatibility wall, but it
cannot identify the zeta tail inside that wall.  A viable route must additionally retain a
source-marked observable sensitive to sparse infinite prime changes, or a transverse
Euler--archimedean polarization that separates them.  The missing zero-to-sector implication in
the prime-clock route cannot be derived from sector geometry alone, because sector geometry is
locally saturated by unrelated differential fields.

## Formalization target

The paper proof is complete.  Before promotion to stage 3, formalize unconditionally:

1. the finite-rank form of Theorem A for arbitrary `m` and `eta`;
2. the explicit prefix-function independent family `(9)`;
3. preservation of tail independence under a common sign multiplier;
4. the weighted-distance bounds from `(8)`;
5. the prime specialization through the existing finite-range operator-tail interface;
6. the continuum-cardinality and differential-transcendence-degree capstone.

## Gates

- [x] sharp coherence-faithfulness dichotomy proved
- [x] explicit continuum independent family proved
- [x] local continuum-rank tail saturation proved
- [x] prime-Dirichlet differential-independence specialization proved on paper
- [x] coherent-sector and overlap consequences proved from the classical interface
- [x] unique positive pointing combined with local coherence saturation
- [x] RH consequence restricted to a route architecture constraint
- [ ] complete primary-literature audit of the combined theorem
- [ ] unconditional formalization of every original deduction
- [ ] integrate into the pure-mathematical paper only after the novelty verdict
