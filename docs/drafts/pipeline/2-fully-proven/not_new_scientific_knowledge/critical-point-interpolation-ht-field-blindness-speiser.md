# Critical-point interpolation and maximal-HT field blindness at the Speiser boundary

- **ID:** `critical-point-interpolation-ht-field-blindness-speiser`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; critical-point geometry; Speiser boundary
- **Statement:** Any finite packet of regular points can be made critical points by one polynomial
  gauge.  The gauge preserves exact order, maximal translation HT, the full differential-translation
  field, and every algebraic power level; it can also preserve sign/Schwarz symmetry and introduce
  no real zeros.  Critical-point localization is therefore not intrinsic to the unpointed HT power
  pro-field.

## Goal

Speiser's theorem turns RH into a global statement about zeros of `zeta'` left of the critical line.
This card tests whether derivative-zero geometry can be forced by hypertranscendence or reconstructed
from the same field/pro-field data used in the preceding route exclusions.

The exact answer is negative for every finite critical packet.  A second theorem identifies the
boundary where the gauge freedom disappears: fixed divisor, order one, and even functional-equation
normalization leave only a scalar multiplier.

## General finite critical-packet theorem `[PROVED HERE]`

Let `F` be holomorphic and nonzero at distinct points `a_1,...,a_m`.  Put

`ell_j=F'(a_j)/F(a_j)`.                                       (1)

There exists a polynomial `P` such that

`P(a_j)=1`, `P'(a_j)=-ell_j`, `1<=j<=m`.                     (2)

Consequently every `a_j` is a regular critical point of `G=PF`:

`G(a_j)=F(a_j)!=0`,

`G'(a_j)=P'(a_j)F(a_j)+P(a_j)F'(a_j)=0`.                     (3)

### Proof

The ideals `(z-a_j)^2` are pairwise coprime.  The polynomial Chinese remainder theorem, equivalently
finite Hermite interpolation, gives one polynomial satisfying the value and derivative conditions
(2).  Equation (3) is the product rule. `QED`

The same argument prescribes critical multiplicity at least `r_j`: recursively prescribe the jet of
`P` so that the first `r_j` jets of `P'F+PF'` vanish at `a_j`, starting from the nonzero value
`P(a_j)=1`, and apply higher Hermite interpolation.  Thus arbitrary finite critical divisors, not
only simple packets, can be inserted.

## Symmetry and real-axis-zero-free strengthening `[PROVED HERE]`

Assume now that `F` is entire, real even,

`F(-z)=F(z)`, `F(conj z)=conj(F(z))`,                         (4)

and let `S` be a finite set invariant under sign and conjugation, disjoint from the zero set of
`F`.  There is a real even polynomial `P` satisfying

`P(x)>=1` for every real `x`,                                 (5)

such that `(PF)'(a)=0` for every `a in S`.

The point `0`, if present, is already critical by evenness, so consider the nonzero sign orbits.
For one representative `a` from each squared orbit, put `x_a=a^2`.  Since `F'/F` is odd and
Schwarz-real, the Hermite data

`R(x_a)=1`,

`R'(x_a)=-(F'(a)/F(a))/(2a)`                                  (6)

are well defined on squared orbits and are compatible with conjugation.  Finite Hermite
interpolation therefore gives a real polynomial `R`.  Define

`Q(z)=R(z^2)`, `P(z)=1+Q(z)^2`.                               (7)

Then `P` is real even and satisfies (5).  At a packet point, `Q(a)=1` and (6) gives

`Q'(a)=2a R'(a^2)=-F'(a)/F(a)`.

Since `P'/P=2QQ'/(1+Q^2)=Q'` where `Q=1`, equation (3) again gives `(PF)'(a)=0`.  The multiplier is
nonzero at every selected point and has no real zeros. `QED`

Higher critical multiplicities follow similarly: at `Q(a)=1`, the `n`-th derivative of

`P'/P=(2Q/(1+Q^2))Q'`

depends on `Q^(n+1)(a)` with nonzero leading coefficient `1`.  Choose the jets recursively and use
equivariant Hermite interpolation.

## Maximal-HT and all-power realization `[PROVED HERE]`

Let `F` be any nonzero meromorphic function whose full translation family is differentially
algebraically independent over `C(z)`.  For the polynomial `P` above and every `N>=1`,

`T_h((PF)^N)=P(z+h)^N T_h(F^N)`.                              (8)

The polynomial factor and its inverse are elements of `C(z)`.  Hence

`C(z)<T_h((PF)^N):h in C>=C(z)<T_h(F^N):h in C>`             (9)

for every `N`, with identical divisibility transition maps.  In particular:

1. `PF` has the same maximal translation differential matroid as `F`;
2. `PF` has the same complete power-normalization pro-field;
3. polynomial multiplication preserves exact finite entire order;
4. in the real-even construction, scalar functional-equation and Schwarz symmetry are preserved;
5. the finite critical packet is arbitrary.

Apply this to the even order-one maximal-HT canonical products from
`herglotz-full-translation-ht-krein-index-orthogonality.md`.  One fixed unpointed maximal-HT power
pro-field therefore realizes arbitrary finite symmetry-compatible critical-point packets, including
packets strictly off the real symmetry axis. `QED`

## Zero-divisor-preserving variant and its cost `[PROVED HERE]`

Hermite interpolation also gives a real-even polynomial `Q` with

`Q'(a)=-F'(a)/F(a)`                                          (10)

at every point of a finite symmetry packet.  Then

`H=e^Q F`                                                     (11)

has exactly the same zero divisor as `F`, while every selected point is critical.  Moreover

`H'/H=F'/F+Q'`,                                               (12)

so the full differential-translation fields generated by the logarithmic derivatives are equal.
Hypertranscendence versus differential algebraicity is unchanged by the zero-free DA multiplier.

The cost is growth: in general `e^Q` has order `deg Q`.  Arbitrary interpolation therefore leaves
the order-one cage.  This cost is load-bearing, not cosmetic.

## Order-one fixed-divisor rigidity `[PROVED, CLASSICAL]`

Let `F` and `G` be nonzero entire functions of order at most one with the same zeros and
multiplicities.  Hadamard factorization gives

`G(z)/F(z)=exp(az+b)`                                        (13)

for constants `a,b`.  If both functions are even, (13) at `z` and `-z` forces `a=0`.  If both are
Schwarz-real, the remaining constant is real and nonzero.  With one common normalization value,
`F=G`.

Thus the simultaneous cage

`fixed divisor + order one + FE-evenness + one normalization` (14)

has no zero-free gauge freedom.  Critical-point plasticity survives exact order through polynomial
gauges only by changing the divisor; it preserves the divisor only by paying additional growth.
This is the precise boundary at which a canonical Speiser-type statement can become meaningful.

## Exact route consequence

Speiser proved that RH is equivalent to the absence of nonreal zeros of `zeta'` in the left half of
the critical strip.  The results above prove:

1. no finite Speiser packet can be derived from an unpointed HT field, differential matroid, or
   complete algebraic power hierarchy;
2. even exact order one and scalar FE/Schwarz symmetry do not repair this finite blindness when
   polynomial divisor gauges are allowed;
3. HT plus the complete zero divisor still does not determine critical points if the order-one
   normalization is dropped;
4. only the canonical order-one fixed-divisor representative removes both gauge freedoms.

This does **not** refute Speiser's theorem or exclude a proof using its full half-strip condition for
the canonical Riemann zeta function.  It excludes implementations that expect HT structure, finite
critical-point verification, or an unpointed field/pro-field to supply the missing localization.
The surviving route must use the exact Euler-normalized representative and global critical-point
geometry; those data are not recoverable from HT alone.

## Parent-theory and novelty verdict

- `[SEARCH]` Speiser's original paper is *Geometrisches zur Riemannschen Zetafunktion*, Mathematische
  Annalen 110, 514--521: `https://eudml.org/doc/159737`.
- `[SEARCH]` Levinson--Montgomery relate the left-half-plane zero counts of `zeta` and `zeta'`; the
  classical paper is *Zeros of the derivatives of the Riemann zeta-function*, Acta Math. 133
  (1974).
- `[SEARCH]` Finite Hermite interpolation is the polynomial Chinese remainder theorem for powers of
  distinct point ideals.
- `[SEARCH]` The order-one fixed-divisor statement is the direct uniqueness part of Hadamard
  factorization.
- `[BRIDGE]` Field and power-pro-field invariance under polynomial multiplication were proved in the
  rational-gauge cards and are elementary.

The exact HT/Speiser route map is useful, but every proof mechanism survives after project vocabulary
is erased.  It is a direct assembly of Hermite interpolation, rational gauge, and Hadamard
factorization.  It fails the parent-theory and anti-theatre novelty gates and is not new scientific
knowledge.

## Lean status

`formal/GaloisForLFunctions/RHTower/CriticalPointInterpolation.lean` formalizes unconditionally:

- `exists_polynomial_critical_packet`;
- `exists_polynomial_mul_hasDerivAt_zero`;
- `exists_real_even_polynomial_critical_packet`.

The exact module builds.  `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`, and the formal lint passes.  The module is not added to the currently dirty umbrella
import because another agent owns that file.

The full card additionally asserts the positive-real-axis multiplier, maximal HT realization,
equality of all differential power fields, entire-order preservation, the exponential-gauge growth
tradeoff, Hadamard rigidity, and the Speiser route boundary.  Those layers are not all formalized as
this single theorem.  Therefore the card remains at stage 2 and is not falsely promoted to
`3-formalized`.

## Gates

- [x] 0 -> 1: exact critical-point interpolation and Speiser boundary isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] exact generic and sign/Schwarz-equivariant interpolation formalized in Lean
- [x] parent-theory attack and bridge classification
- [ ] 2 -> 3: complete unconditional card formalized and safely integrated in Lean
- [ ] 3 -> 4: optional route-boundary integration

## Log

- 2026-07-11 -- Proved arbitrary finite critical-packet insertion by polynomial Hermite gauge and
  equality of every HT power level.
- 2026-07-11 -- Proved the real-even, real-axis-zero-free strengthening and the zero-divisor versus
  growth tradeoff.
- 2026-07-11 -- Formalized the generic analytic and equivariant finite interpolation theorems;
  exact build, axiom audit, and formal lint pass.
- 2026-07-11 -- Downgraded after the parent-theory attack: the complete mechanism is classical
  Hermite interpolation plus Hadamard/rational-gauge theory.
