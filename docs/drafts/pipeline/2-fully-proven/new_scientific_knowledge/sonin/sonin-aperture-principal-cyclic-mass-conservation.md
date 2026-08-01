# Sonin aperture principal cyclic-mass conservation law

- **ID:** `sonin-aperture-principal-cyclic-mass-conservation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [SOURCE THEOREM] [NOT RH]`
- **Parent:** `sonin-aperture-area-rigidity-and-restriction-defect.md`
- **Statement:** Strict Sonin aperture restriction splits every crossing diagonal orbital shell
  into retained and lost noncompact principal shells, but their canonical cyclic logarithmic
  masses add exactly to the original orbital mass.  Lost mass is the additive aperture cocycle
  `log(b/a)`; all remaining aperture curvature is Schatten-1.

## Frontier changed

The prior result proved that no strict aperture step preserves every prime corner modulo the
trace-class relative ideal.  Its positive survivor asked for a cyclic reader on the necessarily
enlarged noncompact principal algebra.  That gate is now closed in the strict crossing chamber.
The lost layer is already a canonical scale-one live Sonin normal state, and the existing faithful
cyclic reader evaluates it exactly.

The remaining aperture problem is smaller: compute and weld the ordinary trace of the
Schatten-1 curvature counterterm.  Principal logarithmic mass needs no Burnol cancellation.

## Theorem

Let `0<a<b<r*a` and `r>1`.  Write

```text
S(s,t)=(A_t-A_s)+(R_t-R_s)
```

for the two-polarization shell.  At aperture `b`, define the three canonical scale-one live
windows

```text
W_keep  = W_b(b,r*a,1),
W_lost  = W_b(r*a,r*b,1),
W_total = W_b(b,r*b,1).                                  (1)
```

Their exact operators are

```text
Op(W_keep)  = S(b,r*a),
Op(W_lost)  = S(r*a,r*b),
Op(W_total) = S(b,r*b).                                  (2)
```

Therefore shell telescoping gives an equality of bounded operators, not a quotient identity:

```text
Op(W_total)=Op(W_keep)+Op(W_lost).                       (3)
```

For a scale-one live window, the faithful principal cyclic reader is logarithmic width:

```text
tau(W_b(s,t,1))=log t-log s.                             (4)
```

Consequently

```text
tau(W_lost)=log(r*b)-log(r*a)=log b-log a,               (5)

tau(W_keep)+tau(W_lost)
 =(log(r*a)-log b)+(log b-log a)
 =log r,                                                 (6)

tau(W_total)=log(r*b)-log b=log r.                       (7)
```

Thus aperture restriction transfers, but does not create or destroy, the prime orbital mass.
The transferred mass is independent of `r` and obeys the exact path law

```text
c(a,c)=c(a,b)+c(b,c),   c(a,b)=log b-log a.              (8)
```

## Operator cocycle and trace-class curvature

Let

```text
Delta(a,b;r)=G_b(r,r)-Q_b G_a(r,r) Q_b.                  (9)
```

For arbitrary nested `b<=c`, direct projection algebra gives the exact compressed cocycle

```text
Delta(a,c;r)=Delta(b,c;r)+Q_c Delta(a,b;r) Q_c.          (10)
```

In one strict crossing chamber `0<a<b<c<r*a`, each defect has its lost-shell representative.
Shell telescoping and `(8)` give

```text
Delta(a,c;r) =_r Delta(a,b;r)+Delta(b,c;r),              (11)
```

where `=_r` is congruence modulo the concrete Sonin principal-relative ideal.  Hence

```text
K(a,b,c;r)=Delta(a,c;r)-Delta(a,b;r)-Delta(b,c;r)        (12)
```

belongs to that ideal and is Schatten-1.  The noncompact principal quotient is flat; every
failure of literal path additivity is concentrated in one ordinary trace-class counterterm.

## Proof

For a general scale-one live window `W_a(s,t,1)` with `a<=s<t`, normalized dilation at scale one
is the identity.  Cutoff nesting gives

```text
(A_t-A_s)(1-A_a)=A_t-A_s,
(R_t-R_s)(1-R_a)=R_t-R_s,
```

which proves `(2)`.  Equation `(3)` follows by cancellation of the intermediate cutoffs at
`r*a`.  Equation `(4)` is the definition of the already-proved faithful normal-state trace, so
the positive logarithm product law proves `(5)`--`(7)`.  Equation `(8)` is additive cancellation.

For `(10)`, expand both defects and use `Q_cQ_b=Q_bQ_c=Q_c`.  In the crossing chamber, the exact
principal-relative lost-shell normal form identifies the three terms in `(11)` with
`S(r*a,r*c)`, `S(r*a,r*b)`, and `S(r*b,r*c)`.  Their sum telescopes exactly.  Membership and
Schatten-1 of `(12)` follow from closure of the concrete two-sided relative ideal.

No zero location, Weil sign, asymptotic estimate, numerical experiment, or RH premise is used.

## Terminal effect on Suzuki lane

This theorem rejects the previous candidate falsifier “no cyclic extension to aperture layers.”
The extension exists and conserves exact source mass.  It also rejects the idea that Burnol's
conductor must cancel a growing principal aperture anomaly: the principal anomaly is the exact
coboundary `(8)` and cancels internally between retained and lost shells.

Remaining source-complete terminal test is now:

```text
ordinary trace of K(a,b,c;r)
  + cutoff-dependent Burnol conductor counterterm
    -> canonical completed signed finite part
      -> uniform lower floor, or an explicit unbounded-below source sequence. (13)
```

A lower floor proves RH through the existing completed source endpoint.  An unconditional
unbounded-below sequence on that exact normalized source family kills the surviving Suzuki--Burnol
weld.  This theorem itself does neither.

## Gates

- [x] prior aperture and normal-state trace corpus audited
- [x] exact retained/lost/total operator decomposition
- [x] exact cyclic-mass conservation
- [x] additive aperture cocycle
- [x] exact compressed operator cocycle
- [x] principal-relative flatness and Schatten-1 curvature
- [x] dependency-closed Lean formalization
- [x] compute the ordinary trace of the curvature on actual finite source packets —
      `re_opTrace_soninAperturePacketCurvature` in `SoninAperturePacketCurvatureTrace.lean`: for a
      finite weighted family of prime scales the real curvature trace is minus the weighted total
      coupling energy, and `re_opTrace_soninAperturePacketCurvature_nonpos` shows no nonnegative
      reweighting can make it positive
- [x] **exact unbounded-below source sequence constructed** —
      `exists_soninAperturePacketCurvature_re_opTrace_lt` in `SoninUnboundedSourcePacket.lean`:
      for every level `M` there is a finite **unit-weight** source packet, over explicit scales of
      the crossing clock, whose aperture curvature trace lies below `-M`.  The chain is
      `norm_sq_apply_le_hsNormSq` (HS energy dominates the action on a unit vector) plus the
      cofinal nonannihilation, giving the uniform floor
      `eventually_le_hsNormSq_soninApertureCoupling` (energy eventually at least `1/4`), summed
      over enough scales.  Unit weights matter: rescaling a single weight would make unboundedness
      vacuous.
      This settles the first branch of the disjunction below; Burnol cancellation is now the
      remaining question, and it must contend with an unbounded-below channel.
- [ ] prove Burnol cancellation, against a channel now known to be unbounded below
- [ ] prove RH or terminally retire surviving Suzuki--Burnol weld

## Log

- 2026-07-31 — packet curvature trace computed.  The relative ideal is closed under finite sums, so
  the ordinary trace is additive over a weighted family of prime scales and the real trace is minus
  the weighted total coupling energy.  Nonnegative weights therefore cannot make the aperture
  curvature positive: the sign survives arbitrary finite source packets, not just single scales.
- 2026-07-22 — cyclic-extension falsifier failed; exact aperture mass conservation proved.
- 2026-07-22 — principal aperture quotient shown flat; remaining anomaly isolated in Schatten-1
  curvature.
