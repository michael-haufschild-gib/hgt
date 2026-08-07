# Suzuki low frequencies enter the Gamma seam through two boundary counterterms

- **ID:** `suzuki-low-frequency-boundary-counterterm-renormalization`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-ARCHITECTURE THEOREM / EXACT POSITIVE SURVIVOR
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `suzuki-physical-log-low-frequency-boundary-lock.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

The physical-log boundary lock does not require lifting the whole low-frequency band into
Suzuki's infinite valuation carrier.  At each endpoint it requires exactly one constant
counterterm.  Every remaining low-frequency boundary germ has physical rate \(e^{-L}\), matching
the first Gamma strip obstruction at \(\operatorname{Im}z=1\).

Let

```text
u=u_low+u_high,
u_low=Fourier^(-1)(chi uhat),    chi in C_c^infinity(R), (1)
```

and define the two boundary moments

```text
m_+=u_low(a),       m_-=u_low(-a).                       (2)
```

In the right and left physical coordinates put

```text
F_full,+(L)=u(a-exp(-L)),
F_low,+(L)=u_low(a-exp(-L)),
F_high,+(L)=u_high(a-exp(-L)),

F_full,-(L)=u(-a+exp(-L)),
F_low,-(L)=u_low(-a+exp(-L)),
F_high,-(L)=u_high(-a+exp(-L)).                         (3)
```

Define the matched high profiles

```text
F_match,+=F_high,++m_+,
F_match,-=F_high,-+m_-.                                 (4)
```

Then:

```text
F_match,+ =F_full,+ -(F_low,+-m_+),
F_match,- =F_full,- -(F_low,--m_-),                     (5)
```

and, for every integer \(j\ge0\),

```text
d^j/dL^j (F_low,+-m_+)=O_j((1+L)^j exp(-L)),
d^j/dL^j (F_low,--m_-)=O_j((1+L)^j exp(-L)).             (6)
```

In fact no polynomial factor is needed for fixed \(j\); `(6)` records a harmless form stable
under the physical \(2L\) coefficient.

Consequently, for every \(0<\sigma<1\),

```text
exp(sigma L)(F_low,+-m_+) in H^k(L_0,infinity),
exp(sigma L)(F_low,--m_-) in H^k(L_0,infinity)           (7)
```

for every finite \(k\).  The full profiles and matched high profiles therefore have:

1. the same half-log traces;
2. the same membership in unweighted \(L^2(dL)\), modulo an exponentially decaying vector;
3. the same homogeneous Gamma scattering constants;
4. forced differentiated Gamma equations whose difference belongs to every subcritical block
   Hardy strip \(0<\sigma<1\).

Thus correct completed carrier has finite-rank low-frequency augmentation

```text
high-frequency ell1 valuation carrier
  + two scalar boundary counterterms (m_-,m_+),          (8)
```

not an infinite low-frequency seam field.

The resulting singular boundary class is canonical.  If \(\chi_1,\chi_2\) are two admissible
low-frequency cutoffs and \(F_{{\rm match},1},F_{{\rm match},2}\) are their matched high profiles,
then

```text
F_(match,1)-F_(match,2)
 =(F_(low,2)-m_2)-(F_(low,1)-m_1).                      (8a)
```

Both terms on the right have rate \(e^{-L}\).  Hence every admissible cutoff defines the same
class modulo the Gamma-subcritical strip space.  Boundary counterterm renormalization is not a
cutoff-dependent choice of corona data.

## 2. Exact algebraic counterterm identity

Equation `(5)` is immediate:

```text
F_high,+ +m_+
 =(F_full,+-F_low,+)+m_+
 =F_full,+-(F_low,+-m_+).
```

The left identity is identical.  If \(u(\pm a)=0\), then evaluating `(5)` at the boundary gives

```text
F_match,+ (infinity)=F_match,-(infinity)=0              (9)
```

in the continuous \(r\)-coordinate sense, even when the unrenormalized high profiles tend to
\(-m_\pm\ne0\).

This is the exact cancellation missing from a high-frequency-only physical-log construction.

## 3. Bandlimited low germ has rate one

Because \(\chi\widehat u\) has compact frequency support and lies in \(L^1\) by
Cauchy--Schwarz, \(u_{\rm low}\) is \(C^\infty\), and

```text
u_low^(k)(x)
 =(1/(2pi)) integral (i xi)^k chi(xi) uhat(xi) exp(i x xi) dxi. (10)
```

Every derivative is bounded:

```text
||u_low^(k)||_infinity
 <=C_(chi,k)||uhat||_(L2(supp chi)).                     (11)
```

The mean-value theorem gives

```text
|u_low(a-r)-u_low(a)|<=||u_low'||_infinity r.            (12)
```

With \(r=e^{-L}\), `(12)` proves the \(j=0\) case of `(6)`.  Repeated chain rule writes every
positive \(L\)-derivative as a finite sum of

```text
exp(-kL) u_low^(k)(a-exp(-L)),     1<=k<=j,              (13)
```

with constant integer coefficients.  Bounds `(11)` prove `(6)` for all \(j\).

For \(0<\sigma<1\), multiplication by \(e^{\sigma L}\) changes each term into
\(O(e^{-(1-\sigma)L})\), with all finite derivatives obeying the same exponential bound.
This proves `(7)`. `QED`

## 4. Compatibility with the differentiated Gamma operator

Write

```text
D_T F=(2L I+R-T)F'+F,                                   (14)
```

where \(R\) is the literal Gamma jump remainder and \(T\) is the bounded self-adjoint
support-pruned prime adjacency with source sign \(T=T_a^\Gamma=-T_a\).

Let

```text
E_low=F_low-m.
```

Equations `(6)`--`(7)` give \(E_{\rm low},E_{\rm low}'\) subcritical exponential rate.  The
whole-line Gamma jump has kernel \((e^s-1)^{-1}\); splitting its integral at \(s=L/2\) and using
the finite exponential moments below the pole \(1\) gives, for every \(0<\sigma<1\),

```text
exp(sigma L) R(E_low') in L2.                            (15)
```

The terms \(2L E_{\rm low}'\), \(T E_{\rm low}'\), and \(E_{\rm low}\) obey the same conclusion
directly.  Hence

```text
exp(sigma L) D_T E_low in L2,       0<sigma<1.           (16)
```

By `(5)` and linearity,

```text
D_T F_match=D_T F_full-D_T E_low.                        (17)
```

Thus replacing the full physical profile by the matched high carrier changes the exact
differentiated equation only by a genuine subcritical Gamma-strip source.  No constant
non-\(L^2\) forcing remains; it was removed by \(m_\pm\).

This is precisely the source class already handled by the block-Hardy and weighted-tail
coercivity theorems.  The remaining work is not low-band regularity.  It is construction of the
two moments from the literal two-port return and exact identification of the matched high
valuation profile with the support-pruned/Feshbach carrier.

## 5. What this closes and what remains

Closed:

```text
low-frequency band
 -> two endpoint constants + Gamma-subcritical remainder. (18)
```

Still open:

```text
literal two-port return
 -> source-determined moments m_-,m_+
 -> matched high ell1 carrier in the exact support-pruned/Feshbach equation
 -> zero-trace Gamma no-return
 -> raw Evans injectivity.                               (19)
```

The low band has therefore been compressed without losing its load-bearing boundary data.  Any
future carrier theorem that adds more than the two constants must show why those additional
coordinates affect the singular Gamma boundary class; smooth low-band Taylor jets do not.

Equation `(8a)` also gives the exact invariant to transport:

```text
[F_match] in
  {physical boundary profiles}/
  {profiles of Gamma rate sigma for every sigma<1}.      (19a)
```

This quotient class is independent of Fourier cutoff.  The carrier intertwiner need only realize
`(19a)` and its two endpoint labels, not equality of arbitrary cutoff representatives.

## 6. Hostile audit

1. **No false high-tail \(dr/r\) claim.**  The high tail is renormalized before entering the
   physical chart.
2. **No discarded low spectrum.**  Its two singular boundary values remain explicit; its
   remainder is proved Gamma-subcritical.
3. **No claim that moments vanish.**  They are part of the open two-port return.
4. **No analyticity theatre.**  Compact frequency support gives derivative bounds `(10)`--`(11)`
   directly; only endpoint germ consequences are used.
5. **No pole crossing.**  Every weight satisfies \(\sigma<1\), the exact first Gamma pole.
6. **No RH claim.**  Return injectivity remains RH-bearing.

## 7. Lean certificate

`SuzukiPhysicalLogBoundaryMomentLock.lean` now formalizes:

```text
boundaryMatchedHigh;
boundaryMatchedHigh_eq_full_sub_lowRemainder;
boundaryMatchedHigh_zero;
lipschitz_boundaryLogRemainder_le;
boundaryMatchedHigh_sub_boundaryMatchedHigh.
```

The last theorem is the exact nonlinear chart estimate

```text
dist(g(a-exp(-L)),g(a)) <= Lip(g) exp(-L).               (20)
```

Together with the already formalized physical-log moment lock, this certifies the finite-rank
counterterm mechanism unconditionally.

## 8. Novelty boundary

Bandlimited smoothness, Fourier derivative bounds, and the mean-value theorem are classical.
Candidate-new source knowledge is the exact Route-O reduction:

```text
the low-frequency obstruction to Suzuki's Gamma carrier
is exhausted by two boundary constants;
after their counterterm renormalization the entire low band is
subcritical relative to the first Gamma pole.            (21)
```

No prior corpus theorem identified `(21)` or connected it to the corrected Feshbach/valuation
carrier.  Priority remains unverified.

A targeted primary-source search through 1 August 2026 found Suzuki's source paper
(arXiv:2606.09096), Chen--Weth's logarithmic Dirichlet theory (arXiv:1710.03416), and the 2026
numerical Suzuki realization (arXiv:2607.24830), but no boundary-counterterm/cutoff-quotient
theorem of the form `(21)`.  Suzuki leaves the relevant limiting and source-selection problems
open; the numerical paper explicitly makes no RH advance.  This supports, but does not certify,
the provisional novelty label.

## Gates

- [x] extract two low-frequency endpoint moments
- [x] prove exact matched-high counterterm identity
- [x] prove every low-band boundary remainder has rate \(e^{-L}\)
- [x] prove subcritical Gamma-strip regularity for every \(0<\sigma<1\)
- [x] show differentiated Gamma forcing remains subcritical
- [x] prove cutoff independence modulo Gamma-subcritical profiles
- [x] formalize exact counterterm and nonlinear chart bound in Lean
- [ ] construct literal two-port moment map
- [ ] attach counterterms to the exact valuation/Feshbach carrier
- [ ] prove zero-trace matched carrier has no nonzero return
- [ ] prove raw Evans injectivity
- [ ] RH
