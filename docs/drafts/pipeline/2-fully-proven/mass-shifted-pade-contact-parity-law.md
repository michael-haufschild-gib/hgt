# Mass-shifted Padé contact parity law

- **ID:** `mass-shifted-pade-contact-parity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE-U POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [NEW SCIENTIFIC KNOWLEDGE CANDIDATE] [NOVELTY NONCOLLISION] [NOT RH]`
- **Parent:** `../1-in-progress/universal-law-field/route-u-crossing-attack-typing.md`
- **Lean:** algebraic contact coefficients, one-sided analytic sign, shifted-Xi defects, and the
  zero-free prime--archimedean consumer are formalized in
  `formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryPadeContactParity.lean` and
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryPadeContactParity.lean`; the exact
  identification of the normalized moving-null Xi energy with that analytic series remains open
- **Statement:** A right-positive mass-shifted moment orbit can meet its canonical flat-quadrature
  orbit only with the alternating orientation fixed by the first nonzero Padé defect. The ordinary
  Route-U flux law is the contact-order-one case.

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

## 5. Stronger admissible source conjecture

`[CONJECTURE]` At every hypothetical right-positive shifted-Xi singular face in `0<y<41/2`, let
`K=2n+d` be the first nonzero defect from its own canonical flat quadrature. Then the completed
prime--Gamma source satisfies

```text
(-1)^d * delta_K < 0.                                  (U-Pade)
```

This is admissibly crossing-dependent: `P`, the flat quadrature, `K`, and `delta_K` are all selected
by the same hypothetical singular face. It is not positivity on an unrestricted polynomial class.
Together with `(8)`, `(U-Pade)` excludes every right-positive crossing, including arbitrarily high
stationary contacts. For `d=1`, it is exactly the current Route-U obligation
`L_y(X P^2)>0`.

## 6. Hostile audit and falsifiers

1. **Fixed-vector local minimum is insufficient.** The theorem needs right-hand positive
   semidefiniteness of the full block, or equivalently nonnegativity on the moving `P_u`. The weaker
   current interface `IsLocalMinOn (u mapsto L_(y+u)(P^2))` controls only `d=1`.
2. **Transport alone still has no orientation.** Existing same-face extension and signed-atomic
   Möbius countermodels assign either sign to `delta_(2n+1)`. The theorem constrains orientation only
   after one-sided full-cone positivity is imposed.
3. **Padé vocabulary alone is not progress.** Classical moment/Padé theory supplies rational
   quadrature shadows and defect blocks. New content here is exact mass-shift normal form `(4)`,
   parity coefficient `(7)`, and its Route-U stationary-crossing consequence.
4. **Source problem remains load-bearing.** `(U-Pade)` is not proved. No generic Stieltjes,
   total-positivity, root-location, or Gamma-only theorem can prove it without becoming RH-equivalent
   or colliding with recorded countermodels.

## 7. Universal principle exposed

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

It also predicts the previously unrecorded higher-contact law `(9)`.

## 8. Literature boundary

Classical Padé theory identifies Hankel degeneracy with rational approximation and allows defect
blocks; classical moment theory identifies positive finite atomic measures with terminating Hankel
towers. Simon's moment-problem treatment relates Padé approximants to finite Jacobi truncations,
and Berg--Szwarc characterize finite-support moment sequences by determinant termination. Targeted
searches found no statement of `(4)`--`(9)` for simultaneous mass-shift/Möbius transport, nor this
stationary first-crossing application. This is a novelty noncollision, not a priority claim.

## 9. Gates

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
- [ ] formalize exact normalized moving-null Xi energy identity and its analytic-series germ
- [ ] formalize full shifted-Xi crossing consumer from actual right-cone positivity
- [ ] prove `(U-Pade)` from completed prime--Gamma source

## Log

- 2026-08-09 — heavy loop 1: conjectured Padé interpretation; hostile audit found fixed-vector
  higher-contact claim false; pivoted to transported null polynomial and full right-cone positivity;
  proved exact normal form and alternating contact law; froze source-specific `(U-Pade)` conjecture.
