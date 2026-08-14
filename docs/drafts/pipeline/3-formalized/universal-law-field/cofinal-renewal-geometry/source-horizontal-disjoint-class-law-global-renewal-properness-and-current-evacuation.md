# Source-horizontal disjoint class-law global renewal properness and current evacuation

- **ID:** ULF-CRG-3
- **Stage:** 3-formalized
- **Type:** THEOREM / LITERAL SOURCE FORMATION / GLOBAL NO-GO
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [LITERAL SOURCE LAW]`
  `[LEAN NOT YET WRITTEN] [NOT RH]`
- **Programme:** `cofinal-renewal-geometry`
- **Parents:**
  - `disjoint-aperture-global-renewal-moment-properness-and-cubic-threshold-law.md`
  - `../../../3-formalized/source-horizontal-abelian-class-law-aperture-evacuation.md`

## 1. Result

The source-horizontal aperture family is already a pairwise-disjoint tower inside one fixed
probability source law.  No path-space enlargement, independent-scale product, or declared
disjointification is needed.

Consequently, every single global renewal of finite relative entropy has finite total admitted
source-horizontal Jeffreys current.  This strengthens the previously formalized native-current
limit: it applies to **every** absolutely continuous global renewal of finite KL action, not only to
the unrenewed class law.

## 2. Literal source tower

Fix a prime `p`, a real parameter `a` with

```text
0 <= a < 1,
```

and let `G` be the discrete class space of finite abelian groups used by the abelian zeta gas.  For
every integer `N>=1`, set

```text
A_N = (Z/pZ)^(N+1),
B_N = Z/p^(2N)Z,
E_N = {A_N,B_N}.                                      (SHG.1)
```

Use the two fixed convergent class laws

```text
mu_+ = classLaw(sigma=1,tau=1-a),
mu_- = classLaw(sigma=1,tau=1+a).                     (SHG.2)
```

These laws do not depend on `N`.

### Theorem 2.1 — the canonical apertures are pairwise disjoint

For `N,M>=1`,

```text
E_N intersects E_M is nonempty  iff  N=M.             (SHG.3)
```

Hence `(E_N)_(N>=1)` is a pairwise-disjoint measurable tower in each of the single probability
spaces `(G,mu_+)` and `(G,mu_-)`.

### Proof

The class invariants already computed in the source-horizontal aperture theorem are

```text
order(A_N)=p^(N+1),       socleOrder(A_N)=p^(N+1),
order(B_N)=p^(2N),        socleOrder(B_N)=p.           (SHG.4)
```

If `A_N=A_M`, equality of orders and injectivity of positive prime powers give `N=M`.  If
`B_N=B_M`, the same argument gives `2N=2M`, hence `N=M`.  Finally `A_N` cannot equal `B_M`:
`N>=1` gives

```text
socleOrder(A_N)=p^(N+1)>p=socleOrder(B_M).
```

This proves `(SHG.3)`.  The class space has the discrete measurable structure, so every `E_N` is
measurable.

## 3. Exact masses and formation partition functions

Write

```text
c_+ = ennNormalizer(mu_+).toReal,
c_- = ennNormalizer(mu_-).toReal.
```

The formalized singleton masses give the exact event masses

```text
epsilon_N^+
 = mu_+(E_N).toReal
 = c_+[p^((a-2)(N+1)) + p^(-2N-1+a)],                (SHG.5)

epsilon_N^-
 = mu_-(E_N).toReal
 = c_-[p^(-(a+2)(N+1)) + p^(-2N-1-a)].               (SHG.6)
```

The equality between the event mass and the displayed sum uses Theorem 2.1 and finite additivity.
For `N>=1`,

```text
epsilon_N^+ <= 2c_+ exp(-(2-a)(log p)N),
epsilon_N^- <= 2c_- exp(-2(log p)N).                  (SHG.7)
```

Indeed the first term of `(SHG.5)` is a fixed factor times `p^(-(2-a)N)` and the second decays at
least that fast; both terms in `(SHG.6)` decay at least as fast as `p^(-2N)`.

Define the source height

```text
H(g)=N,  g in E_N,
    =0,  otherwise.                                   (SHG.8)
```

Pairwise disjointness makes this well-defined.  Its formation partition functions satisfy

```text
Z_+(lambda)=integral exp(lambda H)dmu_+ < infinity
  for 0<lambda<(2-a)log p,

Z_-(lambda)=integral exp(lambda H)dmu_- < infinity
  for 0<lambda<2log p.                                (SHG.9)
```

### Proof

Insert `(SHG.7)` into

```text
Z_±(lambda)
 = mu_±(G minus union_N E_N)+sum_N exp(lambda N)epsilon_N^±.
```

Each remaining series is geometric.

## 4. One-law global renewal theorem

Let `nu_+` and `nu_-` be arbitrary probability laws satisfying

```text
nu_+ << mu_+,       D(nu_+||mu_+)<infinity,
nu_- << mu_-,       D(nu_-||mu_-)<infinity.           (SHG.10)
```

Put

```text
alpha_N^±=nu_±(E_N).toReal.                           (SHG.11)
```

### Theorem 4.1 — finite action forces finite cofinal occupation moment

For every `lambda` in the ranges `(SHG.9)`,

```text
sum_N N alpha_N^+
 <= [D(nu_+||mu_+)+log Z_+(lambda)]/lambda < infinity,

sum_N N alpha_N^-
 <= [D(nu_-||mu_-)+log Z_-(lambda)]/lambda < infinity. (SHG.12)
```

### Proof

Apply the global entropy-height inequality

```text
lambda integral H dnu
 <= D(nu||mu)+log integral exp(lambda H)dmu
```

to `(mu_+,nu_+)` and `(mu_-,nu_-)`.  By Theorem 2.1 and `(SHG.8)`,
`integral H dnu_±=sum_N N alpha_N^±`.

## 5. Global adaptive-information evacuation

Let

```text
W_N(a)=sourceHorizontalPrimeAdaptiveJeffreysWork(p,Na). (SHG.13)
```

The existing exact Bernoulli calculation proves

```text
0 <= W_N(a) <= 2a(log p)N.                             (SHG.14)
```

### Theorem 5.1 — every finite-action global renewal has summable current

Under `(SHG.10)`,

```text
sum_N alpha_N^+ W_N(a)
 <= [2a log p/lambda]
    [D(nu_+||mu_+)+log Z_+(lambda)] < infinity,

sum_N alpha_N^- W_N(a)
 <= [2a log p/lambda]
    [D(nu_-||mu_-)+log Z_-(lambda)] < infinity.        (SHG.15)
```

Consequently

```text
alpha_N^± W_N(a) -> 0.                                (SHG.16)
```

In particular, no finite-KL renewal can sustain

```text
alpha_N^± W_N(a) >= c>0
```

for every grade, or even a nonsummable total linear adaptive current.

### Proof

Multiply `(SHG.14)` by `alpha_N^±`, sum, and apply `(SHG.12)`.  A convergent series of nonnegative
terms has terms tending to zero.

## 6. What changed

The previous formalized theorem showed

```text
mu_±(E_N) W_N(a) -> 0.
```

The new theorem quantifies over every one-law renewal `nu_±` of finite information action.  Thus
the obstruction is not a poor native weighting.  Beating evacuation requires at least one of:

1. infinite global KL action;
2. a renewal singular to the fixed class law;
3. superlinear observer work whose gauge quotient is summable;
4. a non-probability-preserving source operation;
5. failure of the claimed source-horizontal current to live in these apertures.

This closes the disjoint-source-formation gate for the abelian organ.  It does **not** construct the
arithmetic renewal or identify its current with another organ.

## 7. Relation to functional equation and common recovery

The theorem is compatible with, but not generated by, the functional-equation packet lift.  Any
parameter-independent common recovery kernel preserves the KL terms in `(SHG.10)` and recovers the
same height observable, so `(SHG.12)`--`(SHG.16)` lift unchanged to formed packets.

The forward and reverse class laws are two fixed orientations, not proved here to be pushforwards
of one source involution.  Therefore no functional-equation exchange between `mu_+` and `mu_-` is
claimed.  Information-neutral packet formation conserves the global obstruction; it does not
create the missing cross-orientation source map.

## 8. Hostile loops

1. **The cofinal aperture family needs an artificial product source.** False.  The original class
   space and one fixed class law contain a disjoint tower.
2. **Different grades might reuse the same group class.** False by order and socle invariants.
3. **Finite KL only controls each aperture separately.** False.  The single height partition
   function controls the complete first occupation moment.
4. **A clever finite-KL reweighting can keep linear adaptive current alive at every grade.** False
   by `(SHG.15)`.
5. **The theorem selects the critical line.** False.  Selection still needs a source theorem that
   makes the off-center current persistent while deriving finite action.
6. **The two class laws are already a functional-equation pair.** Not proved.  Mutual absolute
   continuity is known; a source-native involutive exchange is not.
7. **The result is an entropy theorem in disguise.** The entropy inequality is classical.  New
   leverage is the literal source identification of one disjoint arithmetic aperture tower and its
   exact adaptive current.

## 9. Literature boundary

The variational inequality used in Theorem 4.1 is established entropy mathematics.  Current work
continues to use the same exponential-integral duality to control risks over KL balls; see Wolf and
McMahon, *Relative Entropy-Bounded Ambiguous Chance Constraints for Robust Planning in Nonlinear
Systems*, [arXiv:2607.16977](https://arxiv.org/abs/2607.16977).  Minimum-relative-entropy updating
by exponential tilts is the classical Esscher mechanism; a recent noncommutative extension is
Hansen and Sokol, *The Quantum Esscher Transform*,
[arXiv:2401.07561](https://arxiv.org/abs/2401.07561).  Entropic transport and bridge theory study
global path-law interventions, including recent relative-entropy control of conditional moments;
see Del Moral, [arXiv:2504.18822](https://arxiv.org/abs/2504.18822).

Probability laws on finite-group isomorphism classes and Cohen--Lenstra heuristics are also parent
mathematics; current examples include Pink--Rubio's probability space for Schur sigma-groups,
[arXiv:2505.05569](https://arxiv.org/abs/2505.05569).

None of these sources identifies the literal HGT class-law tower `(SHG.1)`, its two-observable
forward/reverse masses, or the global adaptive-information evacuation `(SHG.15)`.  The entropy
engine is classical; the source-specific fusion is new to the corpus.  External priority for the
exact fusion remains unverified.

## 10. Lean boundary

No Lean was written or built in this research phase.  Existing formal parents already certify the
class laws, exact atom masses, order/socle invariants, exponential admission bounds, and linear
Jeffreys bound.  New formal obligations are only:

1. pairwise disjointness of `E_N`;
2. event-mass equality with the existing two-singleton admission;
3. the discrete entropy-height inequality and summable-current corollary.

These remain Stage-2 obligations for a later formalization pass.

## Log

- 2026-08-13 — disproved the programme's claim that a one-law disjoint source tower was missing.
- 2026-08-13 — proved exact forward/reverse formation partition ranges and global finite-KL
  adaptive-current evacuation.
- 2026-08-14 — Full unconditional literal-source Lean closure: canonical class apertures are pairwise disjoint; exact masses, sharp forward/reverse partition ranges, finite-KL cofinal moments, quantitative summable adaptive current, and termwise evacuation are kernel-checked; targeted build, umbrella, scoped scan, and standard-only axiom audit pass.
