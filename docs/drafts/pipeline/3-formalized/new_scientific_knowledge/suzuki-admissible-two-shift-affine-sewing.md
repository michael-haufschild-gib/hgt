# Suzuki admissible two-shift affine sewing and canonical nonreal pole germ

- **ID:** `suzuki-admissible-two-shift-affine-sewing`
- **Stage:** 3-formalized
- **Type:** THEOREM / CIRCULARITY CORRECTION / SOURCE-COMPATIBLE RH FRONTIER
- **Scientific status:** `[FORMALIZED] [FULLY PROVEN ON PAPER] [SOURCE-SPECIFIC] [NOVELTY SEARCH: NO MATCH] [NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096v1](https://arxiv.org/abs/2606.09096), Theorem 1.5, Corollary 1.6,
  and Sections 6--8.
- **Parents:** `suzuki-shifted-xi-target-flat-pencil`,
  `suzuki-opposite-shift-cross-sewn-exterior-product`.
- **Lean module:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiAdmissibleTwoShiftAffineSewing`

## Corpus frontier and falsified predecessor

> **Coordinate correction (2026-07-22).** Throughout algebra below, `I_alpha,I_beta` are Xi-real
> normalized right triangles `-iT_phys`, not physical triangles.  Exact one-sided source
> parameters are `eta(lambda)=-i lambda/2`.  Common factor `-i/2` cancels from affine sewing, so
> divisor, pair-independence, and RH criteria survive; source central phase uses corrected
> connector in `suzuki-one-sided-coordinate-phase-normalization.md`.

> **One-sided semantic correction (2026-07-21).**
> `suzuki-one-sided-carleman-exterior-seam.md` proves that every identity in this card must be read
> sheetwise.  The entire terms `I_alpha,I_beta` are the right convolution triangles, not full
> interval transforms, and `E_eta` is the continued right Carleman sheet.  The affine algebra,
> gauge descent, pair independence, pole order, and RH criterion remain valid under that reading.
> A bilateral exterior sum is automatically pole-free and is not the observable constructed here.

Suzuki constructs the finite-aperture Hilbert space at real form shift `lambda` only under

```text
lambda < lambda_a,                                      (1)
```

where `lambda_a=inf spec(A_a)` is the unknown restricted-Weil spectral floor. The previous
cross-sewn card proposed actual channels at opposite shifts `lambda,-lambda`. This source schedule
is circular:

```text
lambda<lambda_a and -lambda<lambda_a
  <=> |lambda|<lambda_a,                                (2)

exists nonzero lambda satisfying (2)
  <=> 0<lambda_a.                                       (3)
```

Cofinal positivity of these floors is the localized Weil/RH condition. Opposite cross-sewing is a
correct algebraic specialization, but unconditional source construction cannot assume its shifts.

The corpus's actual unsolved theorem is exterior continuation: construct an observable from
admissible finite-aperture source channels and prove that its continuation has no nonreal poles.
Exterior pole tomography proves this is RH-bearing. Before attacking it, source-shift selection
must be made unconditional and must not require controlling `lambda_a` or forcing `lambda->0`.

## Theorem A: unconditional two-shift availability `[PROVED HERE]`

Every half-line below a real floor contains two distinct shifts. Explicitly,

```text
alpha=lambda_a-1,
beta =lambda_a-2                                      (4)
```

satisfy `alpha<lambda_a`, `beta<lambda_a`, and `alpha!=beta`, whatever the sign of `lambda_a`.
Suzuki's centered parameter map

```text
eta(lambda)=-i lambda                                  (5)
```

is injective, so the two centered source parameters remain distinct.

This is more than existence bookkeeping. It supplies a source schedule where every input Hilbert
space is unconditionally positive while target shift zero need not be admissible.

## Theorem B: arbitrary-target affine sewing `[PROVED HERE]`

Write

```text
D_eta=XiC'-eta XiC,
R_eta=z^2 XiC/D_eta,
G_eta=R_eta^(-1),
E_eta(W,I)=G_eta W-I.                                  (6)
```

For two distinct source parameters `alpha,beta`, arbitrary target `gamma`, and unrelated source
channels `(W_alpha,I_alpha)`, `(W_beta,I_beta)`, define

```text
C_(alpha,beta->gamma)
 :=(beta-gamma) W_beta E_alpha(W_alpha,I_alpha)
   -(alpha-gamma) W_alpha E_beta(W_beta,I_beta),         (7)

P_(alpha,beta)
 :=(beta-alpha) W_alpha W_beta,                         (8)

J_(alpha,beta->gamma)
 :=(beta-gamma)W_beta I_alpha
   -(alpha-gamma)W_alpha I_beta.                        (9)
```

Then pointwise on all of `C`, including `z=0` and every Xi zero,

```text
C_(alpha,beta->gamma)
 =E_gamma(P_(alpha,beta),J_(alpha,beta->gamma)).       (10)
```

In particular, two same-side admissible sources reconstruct the distinguished zero-shift exterior
channel even when zero shift itself is inadmissible:

```text
C_(alpha,beta->0)
 =E_0((beta-alpha)W_alpha W_beta,
      beta W_beta I_alpha-alpha W_alpha I_beta).       (11)
```

### Proof

The already formalized totalized multiplier formula gives

```text
G_eta=(XiC'-eta XiC)/(z^2 XiC).                        (12)
```

Its affine numerator implies, without dividing by `XiC` or `z`,

```text
(beta-gamma)G_alpha-(alpha-gamma)G_beta
 =(beta-alpha)G_gamma.                                 (13)
```

Expand `(7)`, factor `W_alpha W_beta` from its multiplier terms, apply `(13)`, and collect
interval terms:

```text
C
 =W_alpha W_beta[(beta-gamma)G_alpha-(alpha-gamma)G_beta]-J
 =G_gamma[(beta-alpha)W_alpha W_beta]-J
 =E_gamma(P,J).
```

All operations are polynomial in totalized function values. No source admissibility of `gamma`,
nonvanishing, positivity, limit, or RH assumption enters `(10)`.

## Theorem C: projective descent and independent gauges `[PROVED HERE]`

Let unrelated gauges act on the two channels:

```text
(W_alpha,I_alpha)->g_alpha(W_alpha,I_alpha),
(W_beta,I_beta)  ->g_beta(W_beta,I_beta).               (14)
```

Direct expansion gives common covariance

```text
C->g_alpha g_beta C,
P->g_alpha g_beta P,
J->g_alpha g_beta J.                                   (15)
```

Hence

```text
N_(alpha,beta->gamma):=C/P                             (16)
```

is invariant under independent nonzero gauges. If `alpha!=beta` and both characteristic values
are nonzero, division of `(10)` yields

```text
N_(alpha,beta->gamma)
 =G_gamma-Q_(alpha,beta->gamma),                       (17)

Q_(alpha,beta->gamma)
 =[(beta-gamma)I_alpha/W_alpha
   -(alpha-gamma)I_beta/W_beta]/(beta-alpha).           (18)
```

Thus target multiplier is reconstructed by Lagrange extrapolation; all source normalization is
confined to gauge-invariant interval quotients.

## Theorem D: source-pair choice cannot alter nonreal singularities `[PROVED HERE]`

For another distinct pair `(delta,epsilon)`, formula `(17)` gives exact pair-change law

```text
N_(alpha,beta->gamma)-N_(delta,epsilon->gamma)
 =Q_(delta,epsilon->gamma)-Q_(alpha,beta->gamma).       (19)
```

Assume every `W` and `I` is entire and every `W` has only real zeros, as Suzuki's characteristic
theorem supplies. At a nonreal point every characteristic denominator in `(18)` is nonzero, so
both `Q` terms are analytic there. Consequently

```text
N_(alpha,beta->gamma) analytic at z
  <=> N_(delta,epsilon->gamma) analytic at z,
  whenever Im z != 0.                                  (20)
```

This is the principal new mechanism. Arbitrary admissible shift schedules—including schedules
forced far negative by an unknown floor—define one canonical nonreal meromorphic germ modulo
holomorphic corrections. Suzuki's unsolved control of `lambda_a`, shift convergence, and
shift-independent characteristic zeros is unnecessary for detecting the RH obstruction.

## Theorem E: exact RH criterion and universal pole invariant `[PROVED HERE]`

If `alpha!=beta`, `W_alpha,W_beta,I_alpha,I_beta` are entire, and both characteristic factors have
only real zeros, then `P` and `J` are entire and `P` has only real zeros. Existing generic exterior
tomography applied through `(10)` proves

```text
RH <=> C_(alpha,beta->gamma) is analytic at every nonreal point,
                                                               (21)
RH <=> N_(alpha,beta->gamma) is analytic at every nonreal point.
                                                               (22)
```

At any hypothetical nonreal Xi zero `z` of arbitrary multiplicity
`m=ord_z(XiC)`, product characteristic is nonzero and

```text
ord_z C=-1,
TC_z C=m P(z)/z^2,                                     (23)

ord_z N=-1,
TC_z N=m/z^2.                                          (24)
```

The normalized pole germ is independent of both source shifts, target shift, both characteristic
functions, interval terms, and independent gauges. Formula `(20)` says pair changes add only
off-real holomorphic functions; `(24)` identifies their shared singular principal part exactly.

## Theorem F: opposite sewing is a specialization `[PROVED HERE]`

Set `beta=-alpha=-eta` and `gamma=0`. Then

```text
C_(eta,-eta->0)=-eta C_opposite,
P_(eta,-eta)   =-eta P_opposite.                       (25)
```

For `eta!=0`, normalized channels agree. Thus the earlier opposite result is retained but no
longer used as an unconditional source schedule.

## Scientific-method falsification results

- [x] **T1 source-domain:** raw source and corpus require `lambda<lambda_a`; `(2)`--`(3)` prove
      opposite availability imports positive floor.
- [x] **T2 availability:** explicit pair `(4)` works below every real floor; centering is injective.
- [x] **T3 affine algebra:** `(13)` follows from exact shifted multiplier, and `(10)` follows by
      polynomial expansion.
- [x] **T4 totalization:** `(10)` was proved without clearing `z^2 XiC`; it survives `z=0` and Xi
      divisor values.
- [x] **T5 projective descent:** exact hypotheses of `(17)` are `alpha!=beta` and two nonzero
      characteristic values.
- [x] **T6 real-zero closure:** nonzero scalar times product of two real-zero entire functions has
      only real zeros.
- [x] **T7 pair-change:** target multiplier cancels exactly in `(19)`; analytic equivalence `(20)`
      uses only local nonvanishing of real-zero characteristics.
- [x] **T8 pole test:** arbitrary Xi multiplicity survives; normalization produces universal
      coefficient `(24)`.
- [x] **T9 specialization:** opposite normalized channel is recovered for `eta!=0`.
- [x] **T10 circularity:** target `gamma` is never assumed source-admissible.
- [x] **T11 no computation/RH:** no computation and no RH premise occurs in theorem proofs.

## Novelty boundary

- Repository research search found affine secants of shifted Xi denominators, opposite averaging,
  finite-shift projective holonomy, and opposite cross-sewing, but no arbitrary two-source
  Lagrange sewing, unconditional below-floor schedule, or off-real pair-choice descent.
- Suzuki's v1 paper states the one-shift admissibility condition and expects shift independence,
  while explicitly leaving shift control to arithmetic analysis. It does not form a two-shift
  exterior observable or prove `(10)`, `(19)`, or `(24)`.
- Current arXiv searches for Suzuki two-shift/affine/Lagrange exterior constructions found no
  collision. Lagrange interpolation and product-divisor closure are standard. Novelty claim is
  limited to source-specific synthesis: eliminating positive-floor circularity and proving the
  canonical nonreal singular germ of arbitrary admissible source pairs.

## Frontier after theorem

This does not prove RH. It removes shift-floor control from the RH route. Honest remaining theorem:

> For one pair of actual admissible Suzuki finite-aperture source channels, identify the sewn
> **right-sheet** observable `(16)` independently of the Xi quotient and continue it
> holomorphically through the upper half-plane.

By `(20)`, no special shift pair or convergence `lambda->0` is needed. By `(22)`--`(24)`, proving
that continuation proves RH and cannot be achieved by gauge selection, pair selection,
characteristic zeros, target shift, or multiplicity cancellation. Remaining difficulty is genuine
exterior continuation, not source-shift control.

## Lean status

Formalization contains unconditional source-admissibility certificates, totalized affine
multiplier and exterior identities, independent-gauge descent, analytic real-zero closure,
pair-choice analytic equivalence, raw and normalized RH criteria, universal pole order and
trailing coefficient, and exact opposite-shift specialization.

Verification:

- direct `lake env lean` check of new module passed;
- exact module build passed (`8995/8995`);
- direct checks of SOTA ledger and RHTower umbrella passed;
- formal lint passed with no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- axiom audit of every theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-21 — opposite-source schedule falsified by spectral-floor admissibility.
- 2026-07-21 — arbitrary two-shift affine sewing conjectured; source, totalization, gauge,
  pair-change, divisor, pole, specialization, and novelty tests passed.
- 2026-07-21 — dependency-closed paper proof completed; promoted to Stage 2.
- 2026-07-21 — complete theorem package formalized and audited; promoted to Stage 3.
