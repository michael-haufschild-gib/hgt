# Mass-shifted Padé contact parity law

- **ID:** `mass-shifted-pade-contact-parity-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-U POSITIVE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [NEW SCIENTIFIC KNOWLEDGE CANDIDATE] [NOVELTY NONCOLLISION] [NOT RH]`
- **Parent:** `../1-in-progress/universal-law-field/route-u-crossing-attack-typing.md`
- **Lean:** algebraic contact coefficients, exact moving-null energy, its full analytic germ,
  determinant first-contact coefficients, quadrature-shadow cancellation, right-cone orientation,
  shifted-Xi defects, and the genuine-crossing prime--archimedean normal form are formalized in
  `formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryPadeContactParity.lean` and
  `formal/GaloisForLFunctions/HTGeometry/FiniteHankelMassShiftDeterminantContact.lean` and
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryPadeContactParity.lean`
- **Statement:** A right-positive mass-shifted moment orbit can meet its canonical flat-quadrature
  orbit only with the alternating orientation fixed by the first nonzero Padé defect. At a genuine
  two-sided shifted-Xi loss the order is necessarily odd, so every such loss produces a strictly
  negative completed prime--Gamma moment `L_y(X R^2)` for an adaptively lifted null polynomial
  `R=P X^m`. More sharply, the last two lifted null reporters span a completed-source Gram plane
  of determinant exactly `-delta^2<0`. The ordinary Route-U flux law is the `m=0` case.

## 1. Setup

Let `L_0` be a real moment functional with moments

```text
s_k = L_0(X^k).
```

Assume its Hankel block of size `n+1` is positive semidefinite and singular, its leading block of
size `n` is positive definite, and `P` is the resulting monic null polynomial of degree `n`.
The flat-quadrature theorem gives distinct real roots `r_1,...,r_n`, positive weights
`w_1,...,w_n`, and the finite functional

```text
Q_0(f) = sum_i w_i f(r_i)
```

such that `L_0` and `Q_0` agree through degree `2n`. Put

```text
q_k     = Q_0(X^k),
delta_k = s_k-q_k.
```

The generating function

```text
G_0(z) = sum_k q_k z^k = sum_i w_i/(1-r_i z)
```

is the canonical positive rational Padé shadow of `F_0(z)=sum_k s_k z^k`. Their coefficients
agree through `z^(2n)`.

Suppose `K>=2n+1` is the first index for which `delta_K != 0`, and write

```text
d = K-2n > 0.
```

## 2. Exact mass-shift transport

For real `u` near zero, let

```text
phi_u(x) = x/(1+u*x).
```

Mass-shift transport acts on an atomic functional by

```text
L_u(f) = L_0(f(phi_u(X))/(1+u*X)).                       (1)
```

This is exactly the shifted-Xi law: a spectral atom `lambda` and its moment weight `lambda`
become `lambda/(1+u*lambda)`. Transport `Q_0` by the same formula to obtain `Q_u`.

Define

```text
kappa(u) = product_i (1+u*r_i),
P_u(x)   = kappa(u)^(-1) * (1-u*x)^n * P(x/(1-u*x)).     (2)
```

Then `P_u` is monic and its roots are `phi_u(r_i)`. Hence

```text
Q_u(P_u^2)=0.                                           (3)
```

Substitution of `phi_u` into `(2)` gives

```text
P_u(phi_u(x)) = kappa(u)^(-1) * P(x)/(1+u*x)^n.
```

Therefore the moving-null energy has the exact normal form

```text
E(u) := L_u(P_u^2)
      = kappa(u)^(-2)
        * (L_0-Q_0)(P^2/(1+u*X)^(2n+1)).                (4)
```

Equation `(4)` is the essential step. Keeping `P` fixed would retain a positive quadratic
tangential contribution from motion of the flat nodes and would not control higher contact.

## 3. Contact-parity theorem `[PAPER-PROVED]`

The negative-binomial expansion in `(4)` is

```text
(1+u*X)^(-(2n+1))
  = sum_(j>=0) (-1)^j * choose(2n+j,j) * u^j * X^j.     (5)
```

For `j<d`, the polynomial `P^2 X^j` has degree `2n+j<K`; hence
`(L_0-Q_0)(P^2 X^j)=0`. At `j=d`, monicity of `P` and minimality of `K` give

```text
(L_0-Q_0)(P^2 X^d)=delta_K.                             (6)
```

Since `kappa(0)=1`, equations `(4)`--`(6)` yield the sharp leading law

```text
E(u)
  = (-1)^d * choose(K,d) * delta_K * u^d + O(u^(d+1)). (7)
```

If the full Hankel block remains positive semidefinite for every sufficiently small `u>=0`, then
`E(u)>=0`. Because `delta_K!=0`, `(7)` forces

```text
(-1)^d * delta_K > 0.                                  (8)
```

This proves the contact-parity theorem. `QED`

## 4. Route-U specialization

For the shifted-Xi functional at a right-positive singular face,

```text
s_k = Re(xiShiftedReciprocalMoment y k).
```

Its mass-shift from `y` to `y+u` is exactly `(1)`. The canonical `Q_0` is the positive flat
quadrature already formalized in the Route-U tree. Thus every actual right-hand first crossing has
a first nonzero flat-shadow defect and that defect obeys `(8)`.

At ordinary contact, `K=2n+1` and `d=1`. The first defect is

```text
delta_(2n+1) = L_0(X P^2),
```

so `(8)` becomes `L_0(X P^2)<0`, the strict form of the existing first-crossing flux orientation.
The established derivative identity

```text
E'(0)=-(2n+1)L_0(X P^2)
```

is exactly the `d=1` instance of `(7)`.

If `L_0(X P^2)=0`, Route U does not become stationary or vacuous. The first later nonzero
quadrature defect controls the contact, with alternating sign:

```text
d even  -> delta_(2n+d)>0,
d odd   -> delta_(2n+d)<0.                              (9)
```

The first nonzero defect exists for the actual Xi orbit. Otherwise `F_0` would equal its finite
rational quadrature shadow as an analytic germ. Analytic continuation would make the shifted Xi
logarithmic derivative rational with finitely many poles, contradicting the infinite distinct Xi
divisor.

## 5. Determinant contact and genuine-crossing parity `[LEAN-PROVED]`

Let `H(u)` be the full `(n+1)`-block Hankel determinant along the shifted-Xi mass orbit. Its actual
analytic Taylor series is the determinant of the entrywise mass-shift power-series matrix. If `d`
is the first nonzero flat-shadow defect order, then all lower determinant coefficients vanish and

```text
[u^d] det H(u)
  = det(H_head(0)) * (-1)^d * choose(2n+d,d) * delta_(2n+d).       (10)
```

Positive definiteness of `H_head(0)` persists on a full neighborhood; this is derived recursively
from determinant analyticity and Schur complements, not assumed. At a genuine two-sided loss,
`H(u)` is positive semidefinite for small `u>0` and non-positive-semidefinite at `H(-u)` for small
`u>0`. Persistent positive definiteness of the head makes the latter equivalent to
`det H(-u)<0`, while the former gives `det H(u)>=0`. The first nonzero analytic order in `(10)` must
therefore be odd:

```text
d = 2m+1.                                                        (11)
```

Consequently the even/Hamburger alternative in `(9)` cannot occur at an actual two-sided first
loss. Source equality and the flat-defect identity sharpen every hypothetical loss to

```text
delta_(2n+2m+1) = L_y(X * (P X^m)^2) < 0,                        (12)
```

with all lower prime--Gamma flat defects zero. This is formalized by
`odd_first_contact_of_genuine_xiShiftedHankel_crossing` and
`exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing`.

### 5.1 Exact isotropic flag and hyperbolic-plane birth `[LEAN-PROVED]`

Put `P_j=P X^j`. Vanishing of every defect below `2n+2m+1` gives the full polarized law

```text
L_y(P_i P_j)=0                    if i+j<2m+1,
L_y(P_i P_j)=delta_(2n+2m+1)     if i+j=2m+1.             (13)
```

Thus higher contact creates a totally isotropic lifted flag, not merely the single zero square
`L_y((P X^m)^2)=0`. On its last two directions `A=P X^m` and `B=P X^(m+1)`,

```text
det [[L_y(A^2), L_y(AB)], [L_y(AB), L_y(B^2)]]
  = -delta_(2n+2m+1)^2.                                  (14)
```

Every genuine crossing has `delta_(2n+2m+1)<0`, so `(14)` is strictly negative in the exact
prime--Gamma source presentation. First failed extension is not only non-PSD: it creates a
nondegenerate hyperbolic two-plane at end of flat null flag. Contact delay, plateau length, and
first Krein-index birth are one invariant.

Formal declarations: `momentInner_liftedNullPair_eq_zero_of_odd_contact`,
`momentInner_liftedNullPair_eq_first_odd_defect`,
`liftedNullPair_gramDet_eq_neg_sq_of_odd_contact`,
`liftedNullPair_primeArch_gramDet_neg_of_first_odd_contact`, and
`exists_primeArch_liftedNull_hyperbolicPlane_of_genuine_crossing`.

## 6. Surviving admissible source conjecture

`[CONJECTURE]` At every hypothetical genuine shifted-Xi crossing in `0<y<41/2`, let `m` be selected
by its own first nonzero defect as in `(11)`. Then the completed prime--Gamma source satisfies

```text
L_y(X * (P X^m)^2) >= 0.                               (U-Source)
```

This remains admissibly crossing-dependent: `P`, `m`, and the lower-defect annihilation constraints
are selected by the same hypothetical singular face. It is not positivity on an unrestricted
polynomial class. Together with `(12)`, even non-strict `(U-Source)` excludes every genuine crossing,
including arbitrarily high stationary contacts. For `m=0`, strict positivity recovers the original
Route-U obligation `L_y(X P^2)>0`; the new normal form shows strictness is stronger than necessary.

## 7. Hostile audit and falsifiers

1. **Fixed-vector local minimum is insufficient.** The theorem needs right-hand positive
   semidefiniteness of the full block, or equivalently nonnegativity on the moving `P_u`. The weaker
   current interface `IsLocalMinOn (u mapsto L_(y+u)(P^2))` controls only `d=1`.
2. **Transport alone still has no orientation.** Existing same-face extension and signed-atomic
   Möbius countermodels assign either sign to `delta_(2n+1)`. The theorem constrains orientation only
   after one-sided full-cone positivity is imposed.
3. **Padé vocabulary alone is not progress.** Classical moment/Padé theory supplies rational
   quadrature shadows and defect blocks. New content here is exact mass-shift normal form `(4)`,
   parity coefficient `(7)`, and its Route-U stationary-crossing consequence.
4. **Source problem remains load-bearing.** `(U-Source)` is not proved. No generic Stieltjes,
   total-positivity, root-location, or Gamma-only theorem can prove it without becoming RH-equivalent
   or colliding with recorded countermodels.

## 8. Universal principle exposed

The previous obstruction list is one phenomenon: all fixed-face reporters see only the tangent
flat-quadrature stratum. The missing datum is the first nonzero **normal jet** of the actual source
orbit relative to that stratum. One-sided positivity fixes its parity orientation, while the
prime--Gamma source must force the opposite orientation. Route U is therefore an oriented
intersection problem between the actual infinite-divisor orbit and the finite-rank Padé stratum,
not a static moment inequality.

This principle compresses at least three failures:

- face data cannot determine the normal jet;
- first-order transport cannot determine its sign;
- fixed positive carriers reproduce the tangent stratum but not source-relative departure.

It also predicts the previously unrecorded higher-contact law `(9)`. Determinant analyticity adds a
second universal principle: a corank-one cone boundary with a stable positive head has scalar Schur
inertia. A genuine sign-changing loss is therefore an odd normal intersection. Higher stationary
contact can delay, but cannot change, its Stieltjes orientation.

## 9. Literature boundary

Classical Padé theory identifies Hankel degeneracy with rational approximation and allows defect
blocks; classical moment theory identifies positive finite atomic measures with terminating Hankel
towers. Simon's moment-problem treatment relates Padé approximants to finite Jacobi truncations,
and Berg--Szwarc characterize finite-support moment sequences by determinant termination. Targeted
searches found no statement of `(4)`--`(9)` for simultaneous mass-shift/Möbius transport, nor this
stationary first-crossing application. This is a novelty noncollision, not a priority claim.

## 10. Gates

- [x] exact flat-quadrature/Padé shadow identified
- [x] moving monic null polynomial under Möbius transport derived
- [x] exact normal-energy identity `(4)`
- [x] arbitrary-contact leading coefficient `(7)`
- [x] alternating right-positive orientation `(8)`
- [x] ordinary Route-U flux recovered as `d=1`
- [x] fixed-vector false strengthening rejected
- [x] exact stationary-crossing source conjecture `(U-Pade)` frozen
- [x] primary-literature noncollision audit
- [x] formalize defect-series coefficients and arbitrary first-contact parity in Lean
- [x] formalize one-sided analytic leading-sign theorem in Lean
- [x] formalize shifted-Xi/prime--archimedean defects and order-one Route-U coefficient
- [x] formalize exact normalized moving-null Xi energy identity and its analytic-series germ
- [x] formalize full shifted-Xi crossing consumer from actual right-cone positivity
- [x] formalize exact determinant first-contact coefficient and actual determinant analytic germ
- [x] derive head positive-definiteness persistence rather than assuming it
- [x] prove every genuine two-sided crossing has odd first contact
- [x] reduce every genuine crossing to a negative adaptive completed source moment `(12)`
- [x] prove full lifted isotropic-flag law and exact hyperbolic Gram determinant `(13)--(14)`
- [ ] prove `(U-Source)` from completed prime--Gamma source and adaptive crossing constraints

## Log

- 2026-08-09 — heavy loop 1: conjectured Padé interpretation; hostile audit found fixed-vector
  higher-contact claim false; pivoted to transported null polynomial and full right-cone positivity;
  proved exact normal form and alternating contact law; froze source-specific `(U-Pade)` conjecture.
- 2026-08-09 — Lean closure: proved the all-order shifted-Xi semigroup, exact transported-null
  energy identity, absolute double summability, exact Padé contact germ, all-order flat-quadrature
  cancellation, PSD-to-energy bridge, higher-contact alternating sign, and ordinary positive-
  remainder crossing exclusion. Only source orientation `(U-Pade)` remains open.
- 2026-08-10 — determinant/odd-crossing closure: formalized exact first determinant coefficient,
  convergence and evaluation of the determinant power series, analytic head persistence, and the
  genuine two-sided crossing parity theorem. Every actual loss now yields an adaptively selected
  `R=P X^m` with `L_y(XR^2)<0`; the even branch is impossible. Remaining target is the
  crossing-conditioned source exclusion `(U-Source)`.
- 2026-08-10 — polarized entire delayed-contact flag. Pairings below first odd anti-diagonal
  vanish, first anti-diagonal equals same defect, and final two lifted reporters have exact
  completed-source Gram determinant `-delta^2<0`. Every hypothetical loss is birth of one
  hyperbolic plane after a flat isotropic plateau; source exclusion remains open.
