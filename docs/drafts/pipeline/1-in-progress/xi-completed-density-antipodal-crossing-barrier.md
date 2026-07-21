# Xi completed-density antipodal crossing barrier

- **ID:** `xi-completed-density-antipodal-crossing-barrier`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [RH-EQUIVALENT OPEN CORE] [SOURCE-PROJECTIVE] [NO RH CLAIM]`
- **Parent:**
  `../5-failed/xi-taylor-full-density-transfer-wronskian.md`

## Actual frontier

Let

```text
F(z)=integral_(0,infinity) rho(t)exp(i t z)dt,
q(z)=z^2+1/4,
E(z)=q(z)F(z)-1/4,
E#(z)=q(z)F(-z)-1/4.
```

Corpus proves

```text
E+E#=4z^2 XiC.                                        (1)
```

Therefore, away from `z=0`, an off-axis Xi zero is exactly an antipodal collision

```text
E#=-E.                                                (2)
```

The global norm barrier `|E|>|E#|` is false by the completed-density de Branges no-go theorem.
Consequently the unresolved source problem is narrower: allow ordinary unit-circle crossings of
`E#/E`, but exclude only the antipodal value `-1` in the open upper critical half-strip.

## Conjecture: negative-ray no-return

On the regular locus `E E# !=0`, put

```text
R(z)=E#(z)/E(z).
```

Every real critical-line zero is a boundary point with `R=-1`.  Conjecture:

> Each connected component of
> `R^(-1)((-infinity,0))` entering `0<Im z<1/2` from a real boundary zero carries a strict
> no-return radial coordinate: `log|R|` leaves `0` at the boundary and cannot return to `0`
> before the component exits the half-strip or reaches a projective pole.  Components not meeting
> a boundary zero have `-1` outside their real image interval.

At a simultaneous zero `E=E#=0`, replace `R` by the first nonzero projective jet pair.  The same
no-return statement is required at that jet order.

This conjecture is strictly weaker than a Hermite--Biehler gap: `|R|=1` may occur in the interior
at phases other than `pi`, exactly as forced by the corpus no-go.  It excludes only `(2)`.

## Source certificate sought

The conjecture will count as solved only through the exact theta source.  Required certificate is
a sign/nonvanishing law for the exterior connection

```text
C_F(z)
 =2z(F+F(-z))F
  -q(z)(F'(-z)F+F(-z)F')+(1/2)F'                    (3)
```

restricted to the negative-ray locus, together with its first nonzero projective jet at singular
points.  Corpus proves

```text
C_F=8z XiC F+4z^2(XiC'F-XiC F').                     (4)
```

Thus `(3)` is source-exact and division-free.  At a simple antipodal collision it equals
`4z^2 XiC'F` and is nonzero.  The missing theorem is global no-return of its induced projective
flow, not local transversality.

## Scientific-method protocol

### Predictions

1. Interior zeros of the completed-density norm gap exist or are permitted, but their ratio phase
   is not antipodal.
2. Near a simple real Xi zero, the negative-ray component enters transversely and `log|R|` has a
   definite one-sided sign determined by `(3)`.
3. The component cannot close in the half-strip without a zero of the exterior connection.
4. Any multiple collision is detected by a finite first nonzero projective jet; a first-order
   Wronskian alone is insufficient.
5. No scalar prime-log carrier appears: `F(-z)` retains the continuous archimedean coordinate.

### First experiment

1. Derive the boundary entry direction of `R` at an arbitrary simple real Xi zero, using only
   `(1)`, completed-density conjugation, and named derivatives.
2. Express the tangent derivative of `log|R|` on the negative-ray locus as a division-free real
   form in `F(z),F(-z),F'(z),F'(-z)`.
3. Reassemble that form as a signed double integral before taking absolute values.
4. Test whether source monotonicity fixes its sign only on this locus.  Do not seek a global gap.

### Kill criteria

Retire or strengthen immediately if:

- the completed-density no-go forces an actual interior antipodal crossing, not merely a norm-gap
  crossing;
- the negative-ray component can return to `|R|=1` while exterior connection stays nonzero;
- simultaneous `E=E#=0` collisions cannot be resolved by finite projective jets;
- proof needs global `|E|>|E#|`, divisor assumptions, computations, or separate absolute bounds on
  the two reflected channels;
- source integral reduces to the already conserved raw current.

## Status

Open.  This is the current exact corpus frontier.  No sign theorem or RH claim is asserted.

## Log

- 2026-07-21 — Created after exact source-exchange Wronskian falsified pure-transfer remainder
  interpretation and the existing completed-density no-go ruled out global Hermite--Biehler repair.
