# Primitive-work character transmutation and Wold signature-wall law

- **ID:** ULF-PCFG-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FOUR-ORGAN FUSION / PREDICTION
- **Statement:** Accumulated reflected work raises positive-response order by two and flips its
  square-root reflection character; locally it is exactly the missing energy channel in a canonical
  two-character polarization, while the Wold realization necessarily exits the Euclidean chamber
  and crosses a signed/Krein wall at finite displacement.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [NOVELTY UNVERIFIED] [LEAN PENDING] [NOT RH]`

## Goal

Construct one genuine fusion law across four structurally different organs:

1. positive/Fisher response;
2. primitive/current accumulation;
3. reflected proper work;
4. symmetry representation and signed inertia.

The target is an exact conservation identity that predicts something not inserted into any one
organ: which reflection character carries orientation, and when a positive polarization must become
indefinite.

## Gates

- [x] 0 -> 1 in-progress: response/work order gap and character flip isolated
- [x] 1 -> 2 fully-proven: dependency-closed general theorem and Wold wall proof below
- [ ] 2 -> 3 formalized: Lean theorem pending
- [ ] 3 -> 4 publication-ready

## 1. Accumulated work operator

Let `I` be a nonzero even real-analytic germ at zero with

```text
I(t)>=0,   I(0)=0,   nu(I)=2k.                         (PW.1)
```

Fix `c>0`. Define its current and reflected work by

```text
C_I(t)=integral_0^t I(s) ds,
W_I(t)=c t C_I(t).                                     (PW.2)
```

### Theorem 1.1 -- work contact and character transmutation

The current is odd and the work is even and nonnegative. More precisely,

```text
nu(C_I)=2k+1,
nu(W_I)=2k+2.                                          (PW.3)
```

There are unique normalized analytic germs

```text
w(t)/t^(k+1)>0 near 0,   w(t)^2=W_I(t),
q(t)/t^k>0 near 0,       q(t)^2=I(t)-W_I(t),            (PW.4)
```

where both inequalities mean that the quotient extends to a positive analytic unit. Their
reflection characters are opposite:

```text
q(-t)=(-1)^k q(t),
w(-t)=(-1)^(k+1) w(t).                                 (PW.5)
```

### Proof

Write

```text
I(t)=a t^(2k)+O(t^(2k+2)),   a>0,                      (PW.6)
```

using evenness. Integration and multiplication give

```text
C_I(t)=a/(2k+1)t^(2k+1)+O(t^(2k+3)),
W_I(t)=ca/(2k+1)t^(2k+2)+O(t^(2k+4)).                  (PW.7)
```

This proves parity, positivity, and `(PW.3)`. Since `W_I` has strictly larger order than `I`,

```text
I(t)-W_I(t)=a t^(2k)+O(t^(2k+2))                       (PW.8)
```

is positive on a sufficiently small punctured neighborhood. The analytic square-root normal form
from ULF-PCFG-2 produces `q` and `w`. Their orders are `k` and `k+1`, respectively, so their
characters are exactly `(PW.5)`. QED.

## 2. Exact two-character conservation

Put `V=R^2` and define

```text
v_I(t)=(q(t),w(t)),
Gamma_I(t)=integral_0^t v_I(s) ds,
R_k=diag((-1)^(k+1),(-1)^(k+2)).                       (PW.9)
```

### Theorem 2.1 -- primitive-work polarization identity

On a neighborhood of zero,

```text
||v_I(t)||^2=I(t),
w(t)^2=W_I(t),
q(t)^2=I(t)-W_I(t),                                   (PW.10)
```

and

```text
Gamma_I(-t)=R_k Gamma_I(t).                            (PW.11)
```

The curve separates the two reflection sides. If `k` is odd, its second coordinate is the sign
position channel and its squared velocity is **exactly the accumulated work** `W_I`. If `k` is
even, the first coordinate already supplies the minimal sign channel and work supplies the
complementary trivial channel.

### Proof

The three identities in `(PW.10)` are `(PW.4)` and their sum. If a velocity component has character
`epsilon`, its primitive has character `-epsilon`; `(PW.5)` therefore gives `(PW.11)`. One of `q,w`
has even character and positive leading unit times an even power. Its primitive is a nonzero odd
coordinate, so `Gamma_I(t)!=Gamma_I(-t)` for small nonzero `t`.

When `k` is odd, `w` is even and its primitive is the sign position channel. Equation `w^2=W_I`
identifies its energy with work. When `k` is even, the same reasoning applies to `q`. QED.

This is the fusion law:

```text
positive response = leading channel energy + accumulated-work channel energy.
```

It is not a fitted decomposition. `W_I` is fixed functorially by the primitive-work operator
`(PW.2)`, and parity fixes which representation channel it occupies.

## 3. Uniqueness and joint reconstruction

### Corollary 3.1

The marked pair `(I,W_I)`, together with the positive leading-root normalization, reconstructs
`(q,w)` uniquely. It therefore reconstructs the local equivariant velocity and curve up to one
global orthogonal sign on each representation channel. The scalar response `I` alone does not:
infinitely many analytic rotations of a square root have the same norm square.

### Proof

Equations `(PW.4)` determine the squares. Analytic square-root uniqueness determines each root up to
one germwise sign; the stated normalization fixes those signs. Integration fixes `Gamma_I(0)=0`.
The nonuniqueness from `I` alone is witnessed by

```text
sqrt(I(t))(cos alpha(t), sin alpha(t))
```

for arbitrary analytic angle germs `alpha` with compatible parity. QED.

Thus current/work data supply information absent from the positive metric even though work is
generated from that metric by a nonlocal primitive.

## 4. Wold realization

For the Wold source,

```text
I_W(u)=cosh(u)-sinh(u)/u,
C_W(u)=integral_0^u I_W(v)dv,
P(u)=(log 2)/2 u C_W(u).                               (PW.12)
```

This is `(PW.2)` with `c=(log 2)/2`. Since

```text
I_W(u)=u^2/3+O(u^4),
P(u)=(log 2)/18 u^4+O(u^6),                            (PW.13)
```

Theorem 2.1 gives canonical normalized local roots

```text
q_vis(u)^2=I_W(u)-P(u),
q_ori(u)^2=P(u),                                       (PW.14)
```

with `q_vis` odd and `q_ori` even. Their primitive has target reflection
`diag(1,-1)`. Consequently:

```text
I_W = q_vis^2 + q_ori^2,
P   = q_ori^2.                                         (PW.15)
```

The response, current/work, and functional-equation representation are now one exact local object.
At Wold half-order one, the work is not merely another quartic scalar: it is precisely the energy
of the first analytic channel capable of retaining reflection coorientation.

## 5. Predicted signed/Krein wall

The Euclidean decomposition `(PW.15)` cannot remain real-positive for every displacement.

### Theorem 5.1 -- Wold signature transition

Let

```text
Delta_W(u)=I_W(u)-P(u).                                (PW.16)
```

Then:

1. `Delta_W` is even and positive on a punctured neighborhood of zero;
2. `Delta_W(u)<0` for all sufficiently large positive `u`;
3. there exists `u_*>0` with `Delta_W(u_*)=0`.

Hence the canonical response/work polarization is Euclidean near the event, degenerates at a
finite wall, and is Lorentzian outside a sufficiently large compact set:

```text
I_W=P+(I_W-P)        near zero,
I_W=P-(P-I_W)        for large |u|.                    (PW.17)
```

It has at most one negative channel because only the complementary scalar changes sign.

### Proof

The local assertion follows from `(PW.13)`. For positive `u`, put

```text
C_W(u)=sinh(u)-Shi(u),
Shi(u)=integral_0^u sinh(v)/v dv.                       (PW.18)
```

The closed form for `I_W` gives

```text
I_W(u)/exp(u) -> 1/2.                                  (PW.19)
```

Also `Shi(u)/exp(u)->0`: both numerator and denominator tend to infinity, and l'Hopital reduces the
ratio to

```text
(sinh(u)/u)/exp(u) -> 0.
```

Thus `C_W(u)/exp(u)->1/2`, and consequently

```text
P(u)/I_W(u)
  = (log 2)/2 u C_W(u)/I_W(u) -> +infinity.            (PW.20)
```

Therefore `P>I_W` for all sufficiently large `u`, proving item 2. Continuity, local positivity,
and the intermediate value theorem give a positive zero. Equation `(PW.17)` is algebraic, and its
signature statement follows because `P>0` away from zero. QED.

No uniqueness of `u_*` is asserted.

## 6. Fourth-organ prediction

The signature transition was not used in constructing Wold response, polar work, or the packet
reflection. It predicts a signed/inertia shadow:

> Any global real polarization that insists the Wold polar work remain the orientation-channel
> energy must either pass through a degenerate frame, acquire one negative channel, or abandon
> coefficient-faithful work reconstruction.

This is a falsifiable theorem-level constraint on a future Stokes/Krein or operator realization. It
does not identify an existing route form with `(PW.17)` and does not assert that a physical system
must choose the indefinite continuation.

## 7. Hostile attacks

1. **The identity is arbitrary splitting.** Rejected locally: `W_I` is fixed by the primitive-work
   operator, has forced order, and occupies the unique opposite reflection character.
2. **Any higher-order positive term works equally well.** It produces a split, but only `(PW.2)` is
   the independently established work/current organ and gives joint reconstruction of that organ.
3. **The Euclidean lift proves global positivity.** False by Theorem 5.1.
4. **The signature wall is an RH selector.** False: it is a universal Wold-profile event and exists
   independently of Xi zeros.
5. **The wall is imported Stokes curvature.** False: no Stokes map is constructed. The theorem only
   predicts the possible inertia pattern of any faithful global receiver.

## 8. Parent theories and significance

Analytic square roots, equivariant representation blocks, sums of squares, Fisher/Hellinger
immersion, and signed quadratic forms are established. Parent references:

- https://arxiv.org/abs/math/0211450
- https://arxiv.org/abs/0808.0034
- https://arxiv.org/abs/1207.6736
- https://arxiv.org/abs/2604.12725

The theorem is an exact corpus fusion, not a priority claim. Its mathematical delta is the forced
character shift of the primitive-work operator, the exact local conservation `(PW.15)`, and the
independently predicted signature wall.

## 9. Scope

- The local theorem requires a finite-order positive analytic germ.
- The Wold wall proof uses the exact Wold growth, not only contact order.
- A signed continuation is not unique after the first wall.
- No source-to-Xi comparison, completed operator, or RH selection is proved.

## Lean status

Read-only corpus audit only. No Lean file was written or built. Exact formalization is pending.

## Log

- 2026-08-12 -- work-order shift recognized as complementary reflection-character generator.
- 2026-08-12 -- exact response/work polarization and Wold signature wall paper proofs completed.
