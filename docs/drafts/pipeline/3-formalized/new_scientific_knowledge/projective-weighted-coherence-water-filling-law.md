# Projective weighted-coherence water-filling law

- **ID:** `projective-weighted-coherence-water-filling-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM / WEIGHTED KRONECKER MINIMAX LAW /
  PROJECTIVE RATE--DISTORTION LAW
- **Scientific status:** `[UNCONDITIONAL THEOREM] [COMPLETE PAPER ARGUMENT]`
  `[FULL LEAN FORMALIZATION 2026-07-20]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE: EXACT-OBJECT SEARCH PASSED 2026-07-20]`
- **Statement:** The logarithm of the least deadline that guarantees pure-state Floquet recurrence
  for every eigenphase packet with a prescribed spectral probability vector is, up to explicit
  universal errors linear in the support size, the projective Gaussian rate--distortion function
  of that vector.  The rate--distortion value is not an analogy: it is the exact minimum of the
  Gaussian distortion program after one common phase is removed, is attained by reverse water
  filling, and controls both the constructive recurrence ceiling and an adversarial Haar floor.

## 1. Weighted projective clock

Let `I` be a nonempty finite set and let

```text
a_i >= 0,        sum_i a_i=1,
S={i:a_i>0},     r=#S.                                    (1)
```

For `omega in R^I` and `n>=1`, put

```text
A_a(n;omega)=|sum_i a_i exp(i n omega_i)|,                 (2)

tau_a(eta;omega)
 =min{n>=1:A_a(n;omega)>=1-eta},                           (3)

T_a(eta)=sup_omega tau_a(eta;omega),       0<eta<1.        (4)
```

The clock is projective: adding the same real number to every `omega_i` does not change `(2)`.
Consequently only `r-1` relative phases can carry recurrence entropy.

## 2. The intrinsic entropy

For a pivot `k in S` and `epsilon>0`, define

```text
H_(a,k)(epsilon)
 =inf { (1/2)sum_(j in S\{k}) log x_j :
          x_j>=1,
          sum_(j in S\{k}) a_j/x_j<=epsilon },             (5)

H_a^proj(epsilon)=min_(k in S) H_(a,k)(epsilon).           (6)
```

The infimum is attained.  It has the exact reverse-water-filling form.  If
`epsilon>=1-a_k`, then `H_(a,k)(epsilon)=0`.  Otherwise there is a unique
`lambda_(k,epsilon)>0` such that

```text
sum_(j in S\{k}) min(a_j,1/lambda_(k,epsilon))=epsilon,    (7)
```

and

```text
H_(a,k)(epsilon)
 =(1/2)sum_(j in S\{k}) log_+(lambda_(k,epsilon)a_j).      (8)
```

Thus a coordinate is active exactly when

```text
a_j>1/lambda_(k,epsilon).                                  (9)
```

Coordinates below the water level are not charged.  This is not an imposed truncation: the
active set is selected intrinsically by the weights and the requested coherence defect.

### 2.1 Exact Gaussian rate--distortion identity

Assume the weights on `S` are positive.  For a pivot `k`, let `D_j` be positive distortion
allocations satisfying

```text
0<D_j<=a_j,       sum_(j!=k) D_j<=epsilon.                 (9a)
```

Define their Gaussian rate cost by

```text
R_(a,k)(D)=(1/2)sum_(j!=k)log(a_j/D_j).                    (9b)
```

The change of variables `x_j=a_j/D_j` is a bijection between `(9a)` and the feasible set in
`(5)`, preserving the objective.  Hence

```text
H_(a,k)(epsilon)=min_D R_(a,k)(D).                         (9c)
```

The unique active allocation is the classical Gaussian reverse-water-filling allocation

```text
D_j^*=min(a_j,1/lambda_(k,epsilon)),                       (9d)
```

with the inactive convention when `epsilon>=1-a_k`.  Therefore

```text
R_a^proj(epsilon)
 :=min_k min_D R_(a,k)(D)=H_a^proj(epsilon).               (9e)
```

The content of the main theorem is that this exact compression functional is also the minimax
recurrence exponent of the deterministic phase clock.

## 3. Universal recurrence--rate-distortion law `[THEOREM]`

For every system `(1)` and every `0<eta<1`, one has

```text
R_a^proj(eta) - (pi/4)(r-1) - log(2r)
 <= log T_a(eta)
 <= R_a^proj(eta) + (r-1)log(2 pi sqrt(2)).                (10)
```

Equivalently,

```text
log T_a(eta)=R_a^proj(eta)+O(r),                           (11)
```

with the two absolute constants in `(10)`, uniformly over all finite probability vectors `a`,
all support sizes, and all defects `0<eta<1`.

This is the proposed universal law.  It identifies the correct carrier positively:

```text
worst-spectrum quantum recurrence entropy
 = projective Gaussian rate--distortion + universal extensive error.  (12)
```

No coordinate is paid merely because it exists.  A coordinate is paid exactly when its weight
crosses the water level determined jointly by all other coordinates and the target defect.

## 4. Proof of the upper bound

Fix a pivot `k in S` and numbers `x_j>=1` satisfying the constraint in `(5)`.  Put

```text
Q_j=ceil(pi sqrt(2x_j)),       j in S\{k},
P=product_(j in S\{k}) Q_j.                                (13)
```

Partition the `j`-th circle into `Q_j` equal arcs and apply the pigeonhole principle to the
`P+1` points

```text
(m(omega_j-omega_k) mod 2pi)_(j!=k),       0<=m<=P.        (14)
```

Two points occupy the same product box.  Their difference gives an integer `1<=n<=P` and
integers `r_j` with

```text
|n(omega_j-omega_k)-2pi r_j|<=2pi/Q_j.                    (15)
```

After removing the common pivot phase, `cos u>=1-u^2/2` yields

```text
A_a(n;omega)
 >=1-2pi^2 sum_(j!=k) a_j/Q_j^2
 >=1-sum_(j!=k) a_j/x_j
 >=1-eta.                                                  (16)
```

Hence `T_a(eta)<=P`.  Since `x_j>=1`,

```text
Q_j<=2pi sqrt(2x_j),                                       (17)
```

and therefore

```text
log T_a(eta)
 <=(1/2)sum_(j!=k)log x_j+(r-1)log(2pi sqrt(2)).           (18)
```

Take the infimum in `(5)` and then the minimum over pivots to obtain the upper half of `(10)`.

## 5. Proof of the target-measure bound

Let `(z_i)_(i in S)` be independent Haar phases and put

```text
m=sum_i a_i z_i.                                           (19)
```

The weighted pairwise identity is

```text
sum_(i,j) a_i a_j |z_i-z_j|^2=2(1-|m|^2).                 (20)
```

On `|m|>=1-eta`, the right side is at most `4eta`.  Since

```text
sum_k a_k [sum_j a_j|z_j-z_k|^2]
 =sum_(j,k)a_j a_k|z_j-z_k|^2,                            (21)
```

some `k in S` satisfies

```text
sum_j a_j|z_j-z_k|^2<=4eta.                               (22)
```

Write

```text
M(u)=integral_T exp(-u|z-1|^2) dz.                         (23)
```

The projective shear `(z_k,(z_j/z_k)_(j!=k))` preserves product Haar measure.  Exponential
Markov and independence therefore give, for every `lambda>0`,

```text
P(sum_j a_j|z_j-z_k|^2<=4eta)
 <=exp(4lambda eta) product_(j!=k) M(lambda a_j).          (24)
```

On the standard fundamental interval the chord satisfies `|exp(i theta)-1|>=2|theta|/pi`.
The full-line Gaussian integral then gives the global bound

```text
M(u)<=min(1,sqrt(pi)/(4sqrt(u))),       u>0.               (25)
```

Suppose first that `H_(a,k)(eta)>0` and let `lambda_0=lambda_(k,eta)` be given by `(7)`.
Choose `lambda=(pi/16)lambda_0`.  Equations `(8)`, `(24)`, and `(25)` give

```text
P(sum_j a_j|z_j-z_k|^2<=4eta)
 <=exp((pi/4)lambda_0 eta-H_(a,k)(eta)).                   (26)
```

Multiplying `(7)` by `lambda_0` gives

```text
lambda_0 eta
 =sum_(j!=k)min(lambda_0 a_j,1)
 <=r-1.                                                     (27)
```

If `H_(a,k)(eta)=0`, the same final estimate is trivial because its right side is at least one.
Taking the union over the possible pivots in `(22)` therefore proves

```text
mu_a(eta):=P(|m|>=1-eta)
 <=r exp((pi/4)(r-1)-H_a^proj(eta)).                       (28)
```

## 6. Proof of the lower clock bound

Multiplication by every positive integer preserves Haar measure on the torus.  Hence

```text
P(exists 1<=n<=N with A_a(n;omega)>=1-eta)
 <=N mu_a(eta).                                            (29)
```

If the right side is below one, some frequency packet avoids the target through time `N`.
Using `(28)` and the integer part of half the reciprocal budget gives

```text
log T_a(eta)
 >=H_a^proj(eta)-(pi/4)(r-1)-log(2r).                      (30)
```

When the right side of `(30)` is nonpositive, the inequality follows directly from `T_a(eta)>=1`.
This proves the lower half of `(10)`.

## 7. Consequences

### 7.1 Fixed support

If exactly `r>=2` weights are positive and fixed, then every nonpivot weight is eventually above
the water level as `eta->0`.  Thus

```text
H_a^proj(eta)
 =((r-1)/2)log(1/eta)+O_a(1),                             (31)
```

and `(10)` gives

```text
lim_(eta->0) log T_a(eta)/log(1/eta)=(r-1)/2.              (32)
```

The common scalar phase removes exactly one half-entropy coordinate.

### 7.2 Equal weights

For `a_i=1/r`, the water level is explicit and

```text
H_a^proj(eta)=((r-1)/2)log((r-1)/(r eta))                  (33)
```

whenever `eta<(r-1)/r`.  Consequently `(10)` recovers the universal half-entropy law while
sharpening its interpretation: the coefficient `1/2` is the equal-weight face of a projective
water-filling invariant.

### 7.3 Cofinal effective dimension

For a triangular array `a^(d)` and defects `eta_d`, define

```text
r_eff(d,eta_d)
 =#{j!=k_d:lambda_(k_d,eta_d)a_j^(d)>1},                  (34)
```

where `k_d` is an entropy-minimizing pivot.  Then `(8)` and `(10)` identify the clock cost as the
logarithmic volume of precisely these active coordinates.  Heavy coordinates enter first; a tail
whose total mass lies below the requested distortion is free.  This supplies a carrier law absent
from dimension-only recurrence bounds.

### 7.4 Superextensive universality

For any triangular array for which

```text
H_(a^(d))^proj(eta_d)/#supp(a^(d))->infinity,              (35)
```

the finite theorem immediately gives the constant-free law

```text
log T_(a^(d))(eta_d)/H_(a^(d))^proj(eta_d)->1.             (36)
```

Thus `(10)` is not merely a pair of estimates.  It identifies an exact asymptotic invariant on
every cofinal high-resolution regime in which the requested phase information dominates the
one-constant-per-coordinate implementation cost.  Equal weights with `log(1/eta_d)->infinity`
are one example, but `(35)` permits arbitrary changing weight profiles and active sets.

### 7.5 Prime weights

For normalized prime weights, `(10)` is unconditional and applies before any arithmetic property
of the vector `(log p)`.  It determines the worst-frequency ambient carrier cost.  It does **not**
prove that the one prime-log frequency vector is worst, typical, Poisson, or even positive-entropy.
That arithmetic problem remains the signed prime-product pressure conjecture in
`prime-log-kronecker-coherence-capacity-conjecture.md`.

## 8. Anti-theatre audit

### Classical parents

1. anisotropic simultaneous Dirichlet approximation and the pigeonhole principle;
2. weighted centroid/pairwise-variance identities;
3. Gaussian domination of the one-circle chord Laplace transform;
4. reverse water-filling in Gaussian rate--distortion theory;
5. Haar-union avoidance for torus endomorphisms.

Each ingredient is classical.  The novelty candidate is their uniform projective identification
`(10)`: the same endogenous water-filling functional controls both the deterministic minimax
recurrence ceiling and the Haar-avoidance floor for every finite probability vector.

### Preliminary search, 2026-07-20

Searches across weighted simultaneous approximation, quantitative Kronecker theorems, torus
shrinking targets, weighted exponential polynomials, phase-coherence recurrence, and
rate--distortion theory found the parent ingredients but no joined theorem matching `(10)`.
In particular:

1. current weighted Diophantine approximation theorems concern metric approximation exponents or
   nondegenerate manifolds, not the worst-frequency first coherence clock of a weighted phasor;
2. localized quantitative Kronecker theorems control coordinatewise phase approximation, not a
   weight-selected projective target with a matching Haar lower bound;
3. reverse water-filling gives `(7)`--`(8)` as a convex optimizer in compression theory, but not
   its recurrence interpretation or the two-sided clock theorem;
4. shrinking-target laws for toral maps and integrable flows do not provide a uniform minimax
   theorem over the frequency vector with the same weighted entropy on both sides.

The closest current frontier result is M. Kotowski and M. Oszmaniec, *Tight bounds on recurrence
time in closed quantum systems*, arXiv:2601.10409v2 (27 June 2026). They prove deterministic
packing upper bounds, generic random-Hamiltonian lower bounds, and improvements using a hard
effective support. They also show that inverse participation ratio does not control recurrence and
argue that effective support does. Their result does not optimize coordinate resolutions against
the actual spectral probabilities, does not identify reverse water filling, and does not give a
matching worst-spectrum lower bound for every fixed probability vector. The present theorem
therefore proposes an exact refinement of that frontier:

```text
hard effective support  ->  continuous projective water entropy.       (37)
```

For stroboscopic pure-state evolution with spectral probabilities `a_i`, the return amplitude is
exactly `(2)`. Thus `(10)` identifies the least deadline that works uniformly over every
eigenphase packet having those fixed probabilities. This is different from exact Floquet
recurrence, treated arithmetically by Anand--Valluri--Davis--Ghose, and from monitored quantum
return problems.

The search also found the older information-theoretic literature relating recurrence times of
approximately matching blocks in stationary ergodic sources to source rate--distortion functions
(for example Kanaya--Muramatsu, 1997).  That theory is an important conceptual parent but is not
an equivalent theorem: its recurrence is a random-string return as block length tends to infinity,
whereas `(10)` is a deterministic finite-dimensional minimax over all quantum eigenphase packets,
removes the common phase projectively, and proves explicit matching upper and adversarial lower
bounds for every fixed spectral probability vector.

The exact-object searches found no theorem joining all four defining features of `(10)`:

1. least universal deadline over every frequency packet with fixed weights;
2. exact projective Gaussian rate--distortion value of those weights;
3. deterministic anisotropic construction for the ceiling;
4. an adversarial Haar-avoidance floor governed by the same value.

The card is therefore classified as `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE: EXACT-OBJECT SEARCH
PASSED]`.  This is a positive novelty classification, not a claim that bibliographic search can
logically prove nonexistence of an unknown source.

### Immediate kill tests

The claimed novelty is dead if the literature already contains any theorem equivalent to one of
the following, uniformly over arbitrary positive weights:

1. `log T_a(eta)=H_a^proj(eta)+O(r)` for weighted phasor recurrence;
2. a two-sided minimax first-return theorem with the active set selected by `(7)`;
3. an equivalent projective rate--distortion characterization of weighted Kronecker recurrence;
4. the finite sandwich `(10)` up to different universal constants.

A source containing only weighted Dirichlet approximation, only reverse water-filling, only a
target-volume estimate, or only the fixed-weight exponent `(32)` is a parent, not a kill.  A source
that already joins the ceiling and floor through the same functional kills the result.

### Significance kill tests

The result is not paper-level if:

1. the `O(r)` error can conceal the only regime of interest and no superextensive or normalized
   consequence survives;
2. `(34)` does not yield a genuinely different prediction from support cardinality for natural
   weight arrays;
3. the projective pivot merely rewrites a standard scalar quantization theorem without a new
   recurrence consequence;
4. no downstream prime, spectral, oscillator, or quantum-coherence problem uses the active-weight
   carrier rather than the old dimension-only bound.

The two-level separation in Section 8.1 defeats tests 1--3: it supplies a regime where the hard
effective support is identical but the new invariant, and hence the recurrence law, changes.  The
pure-state Floquet translation supplies the direct quantum use required by test 4.  The exact
paper proof and its full dependency surface have survived unconditional formal verification.

## 8.1 Exact separation from effective support `[PAPER-PROVED]`

The water entropy is not merely a smooth notation for effective-support cardinality. Consider the
two-level probability vector

```text
a(c)=(1-c,c),       0<eta<c<=1/2.                            (38)
```

For the first pivot the water equation is

```text
min(c,1/lambda)=eta,
```

and for the second it is

```text
min(1-c,1/lambda)=eta.
```

The hypotheses force the unique solution `lambda=1/eta` in both cases. The two pivot entropies are

```text
(1/2)log(c/eta),        (1/2)log((1-c)/eta),                (39)
```

so `c<=1-c` gives the exact minimum

```text
H_(a(c))^proj(eta)=(1/2)log(c/eta).                         (40)
```

Consequently the least universal deadline obeys

```text
(1/2)log(c/eta) - pi/4 - log 4
  < log T_(a(c))(eta)
  <= (1/2)log(c/eta) + log(2 pi sqrt(2)).                   (41)
```

Now fix `q>1` and set `c=q eta`, with `q eta<=1/2`. Any subset carrying mass at least `1-eta`
must contain both coordinates: the heavy coordinate alone has mass `1-q eta<1-eta`, while the
light coordinate alone has mass at most `1/2<1-eta`. Hence the hard `eta`-effective support is
identically two. Nevertheless `(40)` becomes

```text
H_(a(q eta))^proj(eta)=(1/2)log q,                          (42)
```

and the universal recurrence deadline stays bounded as `eta` decreases through this family. For
the uniform two-level state, by contrast,

```text
H_(1/2,1/2)^proj(eta)=(1/2)log(1/(2 eta)),                  (43)
```

which diverges. Therefore two state families with the same effective support have different
recurrence exponents. Effective support is not the recurrence invariant; it is a coarse
cardinality envelope of the water entropy.

This is the strongest significance delta on the card. It directly answers the state-complexity
question left by the 2026 quantum-recurrence frontier, without randomness, genericity, or a
Hamiltonian ensemble.

## 9. Formalization plan

1. Reuse the weighted phase floor in `RHTower/CCMPrimePoleFiniteCoherence.lean`.
2. Generalize the existing equal-weight pairwise pivot in
   `RHTower/UniversalPhaseCoherenceEntropy.lean` to probability weights.
3. Generalize the existing pivot shear and chord Laplace product in
   `RHTower/UniversalPhaseCoherenceTargetMeasure.lean` to weighted energies.
4. Add anisotropic finite simultaneous approximation by a product-box pigeonhole theorem.
5. Formalize the finite water-filling optimizer `(7)`--`(8)` without importing any asymptotic
   statement.
6. Package `(10)` as the master finite theorem; derive `(32)` and the equal-weight specialization
   only afterwards.

### Completed formal theorem surface

The certificate-free construction theorem is formalized in
`formal/GaloisForLFunctions/RHTower/ProjectiveCanonicalWaterEntropy.lean`.  It constructs the
active/inactive canonical level for every pivot, proves global optimality on every pivot fibre,
and takes the actual finite minimum.  The exact least universal deadline and both inequalities in
`(10)` are formalized in
`formal/GaloisForLFunctions/RHTower/ProjectiveWeightedCoherenceMinimax.lean` (with `d` in place of
the positive support size; restricting to the support gives `r`).

The dependency-closed formal surface is:

1. exact reverse-water-filling optimizer:
   `ProjectiveWaterFillingOptimizer.lean`;
2. exact weighted target Laplace envelope:
   `ProjectiveWeightedTargetEntropy.lean`;
3. Haar avoidance and the entropy floor:
   `ProjectiveWeightedCoherenceAvoidance.lean`;
4. constructive anisotropic recurrence and entropy ceiling:
   `ProjectiveWeightedCoherenceCeiling.lean`;
5. canonical active/inactive completion and the master sandwich:
   `ProjectiveCanonicalWaterEntropy.lean`;
6. exact active-set support and finite normalized superextensive law:
   `ProjectiveWaterEntropyConsequences.lean`;
7. least universal deadline, exact minimax sandwich, and normalized minimax law:
   `ProjectiveWeightedCoherenceMinimax.lean`;
8. exact pure-state Floquet fidelity translation:
   `ProjectiveWeightedFloquetRecurrence.lean`;
9. exact Gaussian distortion feasible set, optimizer, global projective minimum, and the
   recurrence--rate-distortion capstone:
   `ProjectiveGaussianRateDistortion.lean`;
10. two-level separation from hard effective support:
   `ProjectiveBinaryWaterEntropy.lean`.

No theorem in this surface assumes randomness, rational independence, genericity, an arithmetic
source, an asymptotic hypothesis, or the conjectural prime-log pressure law.

## 10. Gates

- [x] exact finite theorem candidate stated
- [x] dependency-closed paper argument written
- [x] boundary cases `r=1`, zero weights, inactive tails identified
- [x] exact falsifier and anti-theatre tests recorded
- [x] targeted exact-object literature audit completed through 2026-07-20
- [x] hostile mathematical audit of constants and integer rounding completed
- [x] anisotropic product-box recurrence formalized unconditionally in
  `RHTower/AnisotropicPhaseRecurrence.lean`
- [x] weighted pivot, water-level existence, and Haar target union bound formalized
  unconditionally in `RHTower/ProjectiveWeightedCoherence.lean`
- [x] exact free-pivot anisotropic quadratic recurrence formalized unconditionally in
  `RHTower/ProjectiveWeightedCoherenceRecurrence.lean`
- [x] canonical active/inactive water-level selection formalized unconditionally
- [x] exact active-coordinate support theorem formalized unconditionally
- [x] finite normalized superextensive consequence formalized unconditionally
- [x] exact least universal deadline and its two-sided minimax sandwich formalized unconditionally
- [x] unconditional Lean formalization completed
- [x] novelty status decided:
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE: EXACT-OBJECT SEARCH PASSED]`
