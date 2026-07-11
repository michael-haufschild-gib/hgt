# Static norm continuity of shifted Hardy leakage does not select RH

- **ID:** `shifted-hardy-leakage-static-continuity-no-go`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `euler-hardy-leakage-offline-zero-rank.md`;
  `euler-leakage-residue-mode-expansion.md`
- **Statement:** A rank-one off-line leakage channel can converge to zero in operator norm as the
  transverse shift tends to zero while its rank stays one.  Therefore norm continuity at the
  static boundary `omega=0` is compatible with an off-line zero.  The unit jump occurs at the
  *moving zero-crossing* `omega=a`, so using it to exclude entry requires an additional deformation
  of the zero displacement and is not a static RH mechanism.

## Goal

Test the proposed anti-causal entry barrier against the smallest nontrivial model.  The exact
question is whether source-side norm continuity down to `omega=0` can by itself force the leakage
to vanish.  It cannot.

## Rank-one model

For `y>0`, let

```text
b_y(z)=(z-i y)/(z+i y)
```

be the elementary upper-half-plane Blaschke factor.  Fix `a>0`.  For `0<omega<a`, put

```text
A_(a,omega)=b_(a+omega),
B_(a,omega)=b_(a-omega),
phi_(a,omega)=A_(a,omega) conjugate(B_(a,omega))
```

on the real boundary.  Let

```text
L_(a,omega)=P_- M_(phi_(a,omega)) | H^2_+
```

be the anti-causal Hankel compression.

This is the local shifted-quotient geometry of one off-line zero at transverse displacement `a`:
the denominator zero is `i(a-omega)` and its matched numerator zero is `i(a+omega)`.

## Theorem

For every `0<omega<a`,

```text
rank L_(a,omega)=1,
||L_(a,omega)||=omega/a.                                  (1)
```

Consequently

```text
L_(a,omega) -> 0 in operator norm as omega decreases to 0,
```

although the off-line channel persists and the rank remains one for every positive `omega`.
At the opposite endpoint,

```text
||L_(a,omega)|| -> 1 as omega increases to a.              (2)
```

Thus the unit singularity is a crossing singularity at `omega=a`, not a static singularity at
`omega=0`.

## Proof

Let `b=i(a-omega)`, the zero of `B_(a,omega)`.  Since `A_(a,omega)-A_(a,omega)(b)` vanishes at `b`
and `B_(a,omega)` is the simple inner factor with that zero, there is an `h in H^infinity` such
that

```text
A_(a,omega)=A_(a,omega)(b)+B_(a,omega) h.                 (3)
```

On the real boundary, `B conjugate(B)=1`.  Multiplying `(3)` by `conjugate(B)` gives

```text
A conjugate(B)=A(b) conjugate(B)+h.                        (4)
```

The analytic summand `h` has zero Hankel compression, hence

```text
L_(a,omega)=A_(a,omega)(b) H_(conjugate(B_(a,omega))).     (5)
```

The elementary Hankel operator `H_(conjugate(B))` is a rank-one partial isometry: its kernel is
`B H^2_+`, its initial space is the one-dimensional model space
`K_B=H^2_+ minus B H^2_+`, and its norm is one.  Therefore the rank in `(1)` is one and the norm is
`|A(b)|`.

Directly from the two Blaschke zeros,

```text
|A_(a,omega)(b)|
 = |(i(a-omega)-i(a+omega))
       /(i(a-omega)+i(a+omega))|
 = omega/a.                                               (6)
```

Equations `(5)`--`(6)` prove `(1)` and both endpoint limits.

## Route C consequence

The existing unit-channel theorem correctly says that an isolated transverse layer cannot cross
under joint operator-norm continuity through its corner.  The rank-one model shows what that claim
does **not** say:

```text
static continuity in omega at zero  -/->  no off-line zero.
```

To turn the unit corner into an RH proof one would need a deformation `t |-> F_t` beginning at a
source whose RH is known and ending at Xi, together with joint continuity in `(t,omega)` through
every possible crossing.  No such arithmetic deformation is supplied by the fixed Euler source.
Installing one as the proof mechanism would be a flow in disguise, contrary to the constraint-side
goal, unless an independent source constraint canonically fixes it and proves the joint norm law.

This does not refute the static horizontal-resultant route.  It refutes only the proposal that
continuity of the reduced leakage family at `omega=0` is itself an exclusion mechanism.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` Formula `(1)` is the standard rank-one model-space calculation for
two Blaschke factors.  Its application is important route control, but the parent theory proves it
immediately.  It should not be promoted as new operator theory or new number theory.

## Gates

- [x] 0 -> 1: the static-continuity claim reduced to the rank-one channel.
- [x] 1 -> 2: exact rank and norm formula proved on paper.
- [ ] 2 -> 3: no Lean formalization; a scalar Blaschke calculation without the Hardy/model-space
  theorem would be a misleading wrapper rather than a formal proof of `(1)`.
- [ ] 3 -> 4: not a publication target; it is a route-closing bridge.

