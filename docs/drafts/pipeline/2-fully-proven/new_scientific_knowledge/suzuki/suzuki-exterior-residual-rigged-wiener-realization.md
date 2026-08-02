# Completed Suzuki zero modes have an exact high-frequency rigged Wiener carrier

- **ID:** `suzuki-exterior-residual-rigged-wiener-realization`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-DOMAIN THEOREM / HIGH-FREQUENCY CARRIER REALIZATION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM completed Evans/logarithmic seam
- **Inputs:** `suzuki-completed-eigenmode-atomic-jump-boundedness.md`,
  `suzuki-support-pruned-evaluation-rigging-fracture.md`,
  `../../../1-in-progress/suzuki-two-root-valuation-wiener-lift.md`
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, formulas (2.6)--(2.8)

## 0. Scope correction: physical realization needs a uniform coefficient majorant

The first version stopped at \(L^2_\xi(\ell^1)\) and implicitly treated its inverse Fourier
transform as \(L^2_x(\ell^1)\). General \(\ell^1\)-valued Plancherel is false. The source-domain
theorem below is corrected by widening the high-frequency margin and using the fixed
coefficientwise Neumann majorant from
`suzuki-wiener-neumann-plancherel-order-repair.md`. The actual physical carrier lies in the
stronger space \(\ell^1_\nu(L^2_x)\).

## 1. Result

Let \(u\) be any completed eigenfunction of Suzuki's finite-aperture restricted-Weil operator
\(A_a\), extended by zero from \(I_a=(-a,a)\) to \(\mathbb R\).  Let \(P_a(D)\) be the exact
translation-invariant whole-line operator whose interval compression is \(A_a\), and put

```text
b=P_a(D)u.                                               (1)
```

Then:

1. \(b=0\) distributionally on \(I_a\), so \(b\) is an exterior two-port source;
2. \(b\in L^2(\mathbb R)\);
3. its two half-line pieces have ordinary \(L^2\) Hardy amplitudes \(B_-,B_+\);
4. above an explicit finite frequency threshold, the exact coefficient inverse has one
   frequency-independent coefficientwise `ell1` majorant;
5. the resulting two-root carrier belongs to

```text
ell1_valuation(L2_frequency)
  -> ell1_valuation(L2_position)
  -> L2_position(ell1)
  -> L2_position(ell2),                                  (2)
```

   and unit-phase evaluation reconstructs \(\widehat u\) exactly there.

Thus the high-frequency part of `SUZUKI-RIGGED-CARRIER-REALIZATION` is proved on Suzuki's
completed source domain.  No bounded `ell2 -> scalar` map is used.

## 2. Exterior residual is \(L^2\)

The completed-eigenmode theorem gives

```text
u in Linfinity(R),       supp u subset [-a,a].           (3)
```

Suzuki's whole-line operator consists of:

1. the one-dimensional logarithmic Laplacian;
2. finitely many translations by \(\pm\log n\), with
   \(n\le e^{2a}\);
3. bounded scalar terms;
4. convolution by the compactly truncated smooth polar kernel \(r_{0,a}''\).

The compressed eigen-equation says

```text
1_Ia P_a(D)u=lambda u.                                   (4)
```

Move \(\lambda u\) into the scalar part of \(P_a(D)\).  For a zero mode this is unnecessary.
Equation `(4)` then gives

```text
supp b subset (-infinity,-a] union [a,infinity).         (5)
```

Only the logarithmic kernel needs a boundary estimate.  For \(x=a+r\), \(0<r<1\), its unit-range
piece is bounded by

```text
||u||_infinity
 integral_0^min(1,2a) dt/(r+t)
 <=||u||_infinity log(1+1/r).                            (6)
```

The same estimate holds at the left endpoint.  Since

```text
integral_0^1 log(1+1/r)^2 dr < infinity,                 (7)
```

the two boundary collars are in \(L^2\).  The long-range logarithmic tail is
\(O((1+|x|)^{-1})\), hence square integrable.  Every translated copy of `(3)` is bounded and
compactly supported.  The polar convolution is bounded and compactly supported because
\(r_{0,a}''\) is bounded on its compact truncation.  Therefore every term in `(1)` is in
\(L^2\) off \(I_a\).  Together with `(4)` this proves

```text
b in L2(R).                                               (8)
```

No endpoint trace, \(H^1\) premise, or RH premise occurs in this argument.

## 3. Exact two-port Hardy amplitudes

Split

```text
b=b_-+b_+,
supp b_- subset (-infinity,-a],
supp b_+ subset [a,infinity).                            (9)
```

By `(8)`, both pieces lie in \(L^2\).  Translate their supports to the origin and take Fourier
transforms:

```text
bhat(xi)
 =exp(+i a xi)B_-(xi)+exp(-i a xi)B_+(xi),              (10)

B_-,B_+ in L2(R).                                        (11)
```

The support conditions put \(B_-\) and \(B_+\) in the opposite ordinary half-plane Hardy boundary
classes.  This closes the source-domain Hardy-amplitude qualification left open in the
two-root Wiener card.

## 4. Source normalization of the exact multiplier

Suzuki's formula (2.7) is

```text
p_a(xi)
 =Re psi(1/4+i xi/2)-log pi
  -2 sum_(n<=exp(2a)) Lambda(n)/sqrt(n) cos(xi log n)
  +Fourier(r_(0,a)'')(xi).                              (12)
```

Let

```text
L(xi)=log <xi>,

t_a=-sum_(p^j<=exp(2a)) (log p)/p^(j/2)
      [delta_(j e_p)+delta_(-j e_p)],                   (13)

q_a(xi)
 =Re psi(1/4+i xi/2)-L(xi)-log pi
  +Fourier(r_(0,a)'')(xi).                              (14)
```

Then, exactly,

```text
p_a(xi)=L(xi)+q_a(xi)+Ev_xi(t_a).                       (15)
```

This closes the normalization marked “source check pending” in the predecessor card:

```text
kappa=1.                                                 (16)
```

The digamma asymptotic

```text
Re psi(1/4+i xi/2)=log|xi|-log2+O(|xi|^-2)
```

and the bounded Fourier transform of the compact \(L^1\) kernel \(r_{0,a}''\) give

```text
||q_a||_infinity<=C_a<infinity.                          (17)
```

The exact Wiener mass is

```text
M_a=||t_a||_1
 =2 sum_(p^j<=exp(2a)) (log p)/p^(j/2)<infinity.         (18)
```

## 5. Rigged high-frequency inverse

Choose \(L_0>2(C_a+M_a)\) and \(\Xi_a\) so that

```text
L(xi)>=L_0>2(C_a+M_a)  for |xi|>=Xi_a.                  (19)
```

In the unitized valuation Wiener algebra define

```text
h_xi=L(xi)delta_0+q_a(xi)delta_0+t_a.                   (20)
```

The exact Neumann series gives

```text
h_xi^(-1)
 =1/L(xi) sum_(k>=0)
   [-(q_a(xi)delta_0+t_a)/L(xi)]^(*k),                  (21)

||h_xi^(-1)||_1
 <=1/[L(xi)-C_a-M_a].                                   (22)
```

Use two oriented root labels and set

```text
c(xi)
 =h_xi^(-1)*
   [exp(+iaxi)B_-(xi)e_-+exp(-iaxi)B_+(xi)e_+].         (23)
```

Equations `(11)` and `(22)` imply

```text
integral_(|xi|>=Xi_a)||c(xi)||_1^2 dxi
 <=C_a' [||B_-||_2^2+||B_+||_2^2]<infinity.             (24)
```

This estimate alone would not imply the physical \(\ell^1\) statement. Put

```text
r_*=(C_a delta_0+|t_a|)/L_0,
K=L_0^(-1) sum_(k>=0) r_*^(star k).
```

Then \(K\in\ell^1\) and every coefficient of \(h_\xi^{-1}\) is bounded in absolute value by
the corresponding coefficient of \(K\), uniformly in \(\xi\). Hence

```text
sum_nu ||c_nu||_(L2_xi)
 <=||K||_1 (||B_-||_2+||B_+||_2)<infinity.
```

Scalar Plancherel coordinatewise and Minkowski prove `(2)`. Absolute valuation evaluation is now
legal in physical as well as frequency space and, by `(15)` and `(20)`,

```text
Ev_xi(c(xi))
 =p_a(xi)^(-1)bhat(xi)
 =uhat(xi)                    for |xi|>=Xi_a.            (25)
```

The last equality is the global distributional identity
\(P_a(D)u=b\); `(19)` guarantees that division is only performed where \(p_a\ne0\).
This proves the theorem. `QED`

## 6. What remains

Low frequencies may contain zeros of \(p_a\).  They impose divisibility/matching conditions and
must not be divided out.  They do not affect ordinary \(H^1\) membership by themselves because
\(|\xi|\) is bounded there, but they retain the two-port kernel carrying raw Evans injectivity.

More importantly, `(23)` is the global Fourier/Wiener carrier.  To invoke the Gamma-wall and
weighted-tail theorems, one still has to identify its logarithmic boundary-scale transform with
the support-pruned self-adjoint seam equation, including:

```text
global two-root ell1 carrier
 -> support-pruned logarithmic ell1 subset ell2 carrier
 -> exact cutoff identity in ell2.                      (26)
```

This is now an intertwining theorem, not an existence or summability theorem.

## 7. Hostile audit

1. **No raw-domain assumption.**  Boundedness `(3)` is already proved for every completed
   eigenfunction.
2. **No illegal global inverse.**  Division occurs only on `(19)`; finite-frequency zeros remain
   in the two-port matching problem.
3. **No `ell2` evaluation.**  Reconstruction uses absolute `ell1` evaluation, respecting the
   rigging fracture theorem.
4. **No vector-valued Plancherel shortcut.** Uniform coefficient domination proves
   \(\ell^1_\nu(L^2)\) on both Fourier sides.
5. **No support-pruning confusion.**  `(23)` is the global exterior-source carrier.  The
   support-pruned local-log intertwiner is explicitly retained in `(26)`.
6. **No RH claim.**  The low-frequency return kernel and raw Evans positivity remain open.

## 8. Novelty boundary

Exterior \(L^2\) estimates for bounded compact sources and Wiener-algebra Neumann inversion are
standard separately.  The exact conjunction

```text
Suzuki completed eigenmode boundedness
 -> exterior residual in L2
 -> two ordinary Hardy amplitudes
 -> source-normalized valuation-Wiener inverse
 -> ell1-valuation(L2) physical rigged carrier reconstruction     (27)
```

was not found in the corpus or targeted literature search.  The claimed new content is the
source-domain theorem `(1)`--`(27)`; priority remains unverified.

## Gates

- [x] prove completed exterior residual lies in `L2`
- [x] construct opposite two-port `L2` Hardy amplitudes
- [x] source-check exact Suzuki multiplier and prove `kappa=1`
- [x] construct exact high-frequency `ell1(L2) subset L2(ell1) subset L2(ell2)` carrier
- [x] prove absolute evaluation reconstructs the completed mode at high frequency
- [ ] construct global-to-support-pruned logarithmic carrier intertwiner
- [ ] realize exact cutoff equation in the middle `ell2` space
- [ ] apply Gamma wall and weighted-tail coercivity
- [ ] prove raw Evans injectivity
- [ ] RH
