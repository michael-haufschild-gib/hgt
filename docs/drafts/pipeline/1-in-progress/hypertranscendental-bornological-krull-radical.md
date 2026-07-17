# The bornological Krull intersection is invisible to every finite derived HT order

- **ID:** `hypertranscendental-bornological-krull-radical`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / FILTERED COMPLETION NO-GO / POSITIVE REES SUCCESSOR
- **Scientific status:** `[ABSTRACT THEOREM REDISCOVERED / PARENT FUNCTION-ALGEBRA THEORY]`
  `[STRICT-POWER AND NONZERO ALL-POWER PERIOD CORE LEAN-FORMALIZED]`
  `[MULTIPLE-GAMMA SOURCE COMPARISON OPEN] [NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-physical-characteristic-fat-point.md`
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-period-excess-closure-phase-transition.md`
  - `../3-formalized/hypertranscendental-controlled-cohomology-and-bornological-shape.md`
  - `hypertranscendental-socle-frame-clock-field.md`
- **Statement:** The separated formal physical filtration `(lambda^k)` cannot be conservatively
  identified with the powered ideals of the bare bounded period multiplier.  The latter have
  strictly decreasing algebraic ranges but equal norm closures and a nonzero intersection of all
  powers.  The missing invariant is therefore a nonseparated filtered Rees object retaining its
  flat intersection, not another finite derived thickening.

## Exact target

Let `I` be a set, let `w in ell^infinity(I,C)` satisfy

```text
0 < |w(i)| <= 1   for every i,
inf_i |w(i)| = 0,
```

and put

```text
A=ell^infinity(I,C),
J_k=w^k A,                    k>=1,
Flat(w)=intersection_(k>=1) J_k.
```

The target theorem is

```text
J_(k+1) is a proper subset of J_k                    for every k>=1;       (1)
closure(J_k)=closure(J_1)                            for every k>=1;       (2)
0 != exp(-1/|w|) belongs to Flat(w);                                        (3)
closure(Flat(w))=closure(J_k) for every k>=1;                               (4)
ker(A -> inverse_limit_k A/J_k)=Flat(w) != 0.                               (5)
```

Equation `(1)` says that every finite incidence order remains genuinely distinct algebraically.
Equation `(2)` says that ordinary norm closure forgets all of those orders.  Equations `(3)`--`(5)`
say that keeping every finite order still does not make the bounded filtration separated: a
source-defined positive flat section is zero in every finite quotient.

For a nondiscrete integral period module `Lambda subset C`, take

```text
w(q)=q/(1+|q|),                  q in Lambda\{0}.
```

Then the hypotheses hold.  Thus `(1)`--`(4)` apply to the powered period-incidence multipliers
already used as the analytic realization of the multiple-Gamma physical fat point.

## Proof attack

For `(1)`, the target `|w|^(k+1/2)` lies in `w^k A`, while division by `w^(k+1)` has norm
`|w|^(-1/2)`, which is unbounded along a small-period sequence.

For `(2)`, the inclusion from right to left is the only issue.  If `y=wx`, cut off the formal
preimage `w^(1-k)x` on `{|w|>=delta}`.  It is bounded for fixed `delta`, and its `w^k`-image differs
from `y` by at most `delta ||x||`.

For `(3)`, put `b(i)=exp(-1/|w(i)|)`.  For every `k`,

```text
|b(i)/w(i)^k|=u^k exp(-u),       u=1/|w(i)|>=1,
```

which is bounded by `k!` because `u^k/k! <= exp(u)`.  Hence `b=w^k x_k` for every `k`, and `b`
is pointwise positive.  For `(4)`, if `f` lies in the common closed ideal, then
`f exp(-epsilon/|w|)` lies in `Flat(w)` and converges uniformly to `f` as `epsilon` decreases to
zero.  Equation `(5)` is the definition of the kernel of the adic comparison.

## Why the earlier comparison target is too strong

The multiple-Gamma formal source has the separated local filtration

```text
C[[lambda]] superset (lambda) superset ...,
intersection_k (lambda^k)={0}.
```

The bounded period realization has the nonzero flat intersection `(3)`.  Therefore a map
`lambda^k -> w^k` may be exact at every fixed `k` without being conservative at the inverse-limit
boundary.  This is a concrete failure of completion to commute with the source filtration, not a
missing proof of a presumed equivalence.

This conclusion is deliberately limited.  The universal flat section may lie outside the image of
the genuine multiple-Gamma source algebra.  Therefore it proves that the bare bounded target
filtration is nonseparated; it does not yet compute the kernel or cofiber of a source comparison
which has not been constructed.  The significant theorem must build that filtered morphism and
identify its actual source-produced completion defect.

## Exact algebraic source comparison `[PROVED]`

The finite-order physical source map itself can nevertheless be constructed.  Assume the set of
values of `w` accumulates at zero through nonzero values and define

```text
phi:C[lambda] -> A,               phi(p)=p(w).
```

Then `phi` is injective and, for every `k>=1`,

```text
phi^(-1)(J_k)=(lambda^k),
phi^(-1)(closure(J_k))=(lambda).                                (6)
```

To prove injectivity, a polynomial vanishing on the infinite value set of `w` is zero.  For the
first identity, write a nonzero polynomial as `p=lambda^m u` with `u(0)!=0`.  If `m<k`, then
`p(w)/w^k=w^(m-k)u(w)` is unbounded along a small-value sequence, while `m>=k` gives an evident
bounded quotient.  For the second identity, `p(w)` lies in the common closure exactly when it
vanishes along every sequence with `w->0`, equivalently exactly when `p(0)=0`.

Equation `(6)` is the exact conservation law missing from the earlier slogan `lambda^k -> w^k`:

```text
exact nonclosed realization:  preserves every source multiplicity k;
Hausdorff closed realization:  radicalizes every positive multiplicity to one.          (7)
```

Thus ordinary closure cannot simultaneously repair attainment and retain the nilpotent depth of
the multiple-Gamma physical fat point.  The positive receiver is the non-Hausdorff filtered map
`phi` itself.  This theorem still does not compute the completed comparison cofiber or produce a
multiple-Gamma-specific flat class.

## No-go and positive successor

```text
[NO-GO]
No tower of finite derived thickenings, followed only by ordinary Banach closure, can recover the
complete bounded incidence germ.  Closure identifies all positive orders, while the inverse tower
annihilates the nonzero flat intersection.
```

```text
[POSITIVE]
The maximal exact receiver is the nonseparated filtered incidence algebra, equivalently its Rees
object together with the map to the bounded realization.  Its associated graded records finite
constraint depth; its flat intersection records infinite-order nonattainment; its nonclosed inclusions
record approximate spectral blindness.  A source comparison is conservative only if it preserves
all three.
```

This gives a precise candidate for the missing layer above the derived physical characteristic:

```text
source filtered Rees object
  -> bounded realization with strictness defects
  -> flat intersection at the infinite-order boundary.
```

Orientation and calibration are still additional data; the flat radical does not recover a frame
forgotten by the source.

## Novelty and significance gate

The following are parent mathematics and cannot support a priority claim:

- Krull intersection can fail in non-Noetherian function algebras;
- smooth or bounded function algebras contain nonzero flat elements;
- diagonal multiplier ideals and cutoff approximation are elementary Banach-algebra theory;
- reduced versus unreduced Hilbert-complex cohomology and small-divisor nonclosedness are classical.

The external audit gives a hard `[REDISCOVERED]` verdict on `(1)`--`(5)`.  Mortini--Rupp--Sasane,
*On the Krull Intersection Theorem in Function Algebras*, proves the parent function-algebra
phenomenon (`https://doi.org/10.2989/16073606.2017.1289482`,
`https://arxiv.org/abs/1605.08204`).  Rees separatedization and the formal-versus-flat-functions
contrast are also parent mathematics.

The candidate-new residue is therefore not `(1)`--`(5)` alone.  It is the theorem
that the already constructed multiple-Gamma DA fat-point filtration and its natural bounded period
realization necessarily differ by this explicit flat intersection, thereby refuting conservative
finite-derived reconstruction and forcing a nonseparated Rees layer in the HT obstruction object.

Significance passes only if this comparison changes the unified theory and survives a second
independent natural HT realization.  Until then the result is a strong correction and bridge, not
a paper claim.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` If several RH chains are realizations of one source filtration,
finite positivity, finite continuation, and finite spectral matching may all agree while differing
by a flat boundary class.  A proof factoring only through finite derived neighborhoods or their
Hausdorff closures cannot exclude that class.  The zeta-specific content would begin only after a
source-pure zeta Rees object and two conservative comparison functors are constructed.

## Gates

- [x] corpus collision gate for the weaker torus-Koszul depth proposal
- [x] fatal-hypothesis test for rational independence versus ergodic translation action
- [x] exact paper proof of the abstract bounded-multiplier theorem drafted
- [x] external novelty/significance audit completed: abstract theorem rediscovered
- [x] exact powered-period all-power and strict-successor source statements proved
- [x] all-power flat witness and strict-successor source statements formalized in Lean
- [x] equal-closure statement formalized in Lean
- [ ] dense-flat-intersection statement formalized in Lean
- [ ] second independent natural HT realization constructed

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceFlatIntersection.lean` proves:

- `exp_neg_inv_mul_inv_pow_le_factorial`;
- `poweredPeriodIncidenceMultiplier_flatPreimage`;
- `periodIncidenceFlatTarget_mem_all_poweredRanges`;
- `exists_mem_poweredPeriodRange_not_mem_succRange`;
- `periodIncidenceFlatTarget_ne_zero_of_not_discrete`;
- `closure_range_poweredPeriodIncidenceMultiplier_eq_atomic`;
- `poweredPeriodIncidence_strictBeforeClosure_equalAfterClosure`.

The exact leaf build and direct file elaboration pass.  The audited capstones use only `propext`,
`Classical.choice`, and `Quot.sound`.
