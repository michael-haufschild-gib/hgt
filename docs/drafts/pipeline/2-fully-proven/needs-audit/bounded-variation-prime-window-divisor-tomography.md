# Bounded-variation prime-window divisor tomography

- **ID:** `bounded-variation-prime-window-divisor-tomography`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / unconditional CCM prime-source tomography / `[BRIDGE]`
- **Scientific status:** `[PROVED ON PAPER] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** bounded-variation quadrature, the Euler logarithmic derivative, and
  meromorphic divisor calculus
- **Statement:** Every compactly supported bounded-variation multiplicative prime window has a
  canonically polar-renormalized ordinary Dirichlet series.  Its poles are exactly the nontrivial
  zeta zeros not annihilated by the Mellin transform of the window.  One sharp window detects the
  complete off-critical divisor and gives an RH holomorphy criterion; two sharp windows of
  irrationally related logarithmic widths recover the complete nontrivial divisor, including the
  critical-line part, with exact multiplicities.

## 1. Window class and arithmetic carrier

Let `W : (0,infinity) -> C` be bounded, compactly supported in an interval `[a,b]` with
`0<a<b`, and of bounded variation after extension by zero to the real line.  Put

```text
I_W(s)=integral_0^infinity W(u)u^(-s)du.                  (1)
```

Compact support away from zero makes `I_W` entire.  For `N>=1`, define the finite moving-window
von Mangoldt statistic

```text
T_W(N)=sum_(k>=1) Lambda(k)/sqrt(k) W(N/k).               (2)
```

Only `N/b<=k<=N/a` contribute.  The unique scalar polar counterterm required below is

```text
R_W(N)=2 I_W(3/2) sqrt(N),
p_W(N)=R_W(N)-2T_W(N).                                   (3)
```

Thus the coefficient sequence is prime-defined and contains no zeta-zero data.

## 2. Bounded-variation quadrature

For `s in C`, set

```text
g_s(u)=W(u)u^(-s).                                       (4)
```

If `K` is compact in `C`, then

```text
sup_(s in K) Var_R(g_s)<infinity.                        (5)
```

Indeed, `u |-> u^(-s)` and its derivative are uniformly bounded on `[a,b]` for `s in K`, and
the product inequality for total variation gives `(5)` from the bounded variation of `W`.

For any compactly supported integrable bounded-variation function `g`, comparison on every cell
`((n-1)/k,n/k]` gives

```text
|g(n/k)/k-integral_((n-1)/k)^(n/k)g(u)du|
 <=Var_(cell)(g)/k.
```

Summing the cell variations proves the sharp uniform estimate

```text
|1/k sum_(n>=1)g_s(n/k)-integral_0^infinity g_s(u)du|
 <=C_(K,W)/k.                                            (6)
```

Define the entire finite-sum error

```text
E_(k,W)(s)
 =sum_(N>=1)W(N/k)N^(-s)-k^(1-s)I_W(s).                  (7)
```

Multiplication of `(6)` by `|k^(1-s)|` gives, uniformly on `K`,

```text
|E_(k,W)(s)|<=C_(K,W) k^(-Re s).                         (8)
```

Consequently

```text
H_W(s)=sum_(k>=1) Lambda(k)/sqrt(k) E_(k,W)(s)            (9)
```

converges locally uniformly and is holomorphic on `Re s>1/2`, because on every compact subset
of that half-plane it is dominated by a constant times
`sum Lambda(k)k^(-sigma-1/2)` with `sigma>1/2`.

## 3. Canonical continuation

For `Re s>3/2`, absolute convergence permits reversal of the two sums in `(2)`.  Inserting `(7)`
and using the Euler logarithmic derivative yields

```text
sum_(N>=1)T_W(N)N^(-s)
 =I_W(s)(-zeta'(s-1/2)/zeta(s-1/2))+H_W(s).              (10)
```

The polar sequence has ordinary Dirichlet series

```text
sum_(N>=1)R_W(N)N^(-s)=2I_W(3/2)zeta(s-1/2).             (11)
```

Hence the ordinary Dirichlet series of `p_W` has the canonical meromorphic continuation

```text
Scal_W(s)
 =2I_W(3/2)zeta(s-1/2)
  -2I_W(s)(-zeta'(s-1/2)/zeta(s-1/2))
  -2H_W(s)                                                (12)
```

to `Re s>1/2`.

At `s=3/2`, both `zeta(s-1/2)` and `-zeta'/zeta(s-1/2)` have residue `1`; the two residues in
`(12)` are `2I_W(3/2)` and `-2I_W(3/2)`.  They cancel.  Thus the zeta pole leaves no singularity.

Let `rho` be a nontrivial zeta zero of multiplicity `m(rho)`.  At `s=rho+1/2`, the logarithmic
derivative has residue `-m(rho)`, while the other two terms in `(12)` are holomorphic.  Therefore

```text
Res_(s=rho+1/2) Scal_W(s)=2m(rho)I_W(rho+1/2).            (13)
```

Since the logarithmic-derivative pole is simple, `(12)` is singular at `rho+1/2` if and only if

```text
I_W(rho+1/2)!=0.                                         (14)
```

This is the exact Mellin-censorship law: the window loses precisely those divisor points at which
its Mellin transform vanishes, and no others.

## 4. Main theorem: kernel-normalized prime-source class `[PROVED]`

Let `W` range over the compactly supported bounded-variation windows above.

1. The prime-defined ordinary Dirichlet series `sum p_W(N)N^(-s)` has the canonical continuation
   `(12)` to `Re s>1/2`.
2. Its nontrivial pole divisor obeys the exact censorship law `(13)`--`(14)`.
3. On any open set `U` on which `I_W` and `I_V` are both nonzero,

```text
Scal_W/I_W-Scal_V/I_V is holomorphic on U.               (15)
```

Indeed, both normalized functions have the same simple poles and the same residue `2m(rho)` at
every shifted nontrivial zero in `U`; their possible zeta-pole singularities at `3/2` have already
been removed.  Thus `(15)` identifies a kernel-independent prime-source divisor class modulo
holomorphic functions.

If `I_W` is zero-free on `Re s>1`, then `(13)` detects every right off-critical zero, and

```text
RH iff Scal_W is holomorphic on Re s>1.                   (16)
```

The theorem does not assert the holomorphy in `(16)`; it gives an exact source-side equivalent.

## 5. Sharp-window theorem `[PROVED]`

For `L>0`, take the unsmoothed multiplicative rectangle

```text
W_L(u)=1_[1,exp L](u).                                   (17)
```

Then

```text
T_L^sharp(N)
 =sum_(N exp(-L)<=k<=N) Lambda(k)/sqrt(k),                (18)
```

and

```text
J_L(s)=I_(W_L)(s)
      =(1-exp(-L(s-1)))/(s-1)
      =A_L(s-1),                                         (19)
```

with removable value `L` at `s=1`.  Also

```text
J_L(3/2)=2(1-exp(-L/2)).                                  (20)
```

Thus the completely explicit coefficient is

```text
p_L^sharp(N)
 =4(1-exp(-L/2))sqrt(N)
  -2 sum_(N exp(-L)<=k<=N) Lambda(k)/sqrt(k).             (21)
```

The zeros of `J_L` lie on `Re s=1`, so `J_L` is zero-free on `Re s>1`.  Equations
`(13)` and `(16)` therefore imply:

> One fixed sharp moving prime interval, with no smoothing and one elementary square-root
> counterterm, recovers every right off-critical zeta zero with its exact multiplicity.  RH is
> equivalent to holomorphy of its ordinary Dirichlet-series continuation on `Re s>1`.

For `L=log 2`, the prime sum in `(21)` is exactly over the dyadic interval

```text
N/2<=k<=N.                                                (22)
```

This strictly strengthens the moving-tent theorem: the tent, the squared Mellin multiplier, and
the three-term polar sequence are unnecessary for source-side divisor tomography.

## 6. Two-window full-divisor theorem `[PROVED]`

For `w!=0`, the rectangular amplitude satisfies

```text
A_L(w)=0 iff Lw is a nonzero integral multiple of 2pi i. (23)
```

Let `L_1,L_2>0` with `L_1/L_2` irrational.  If both `A_(L_1)(w)` and `A_(L_2)(w)` vanished,
`(23)` would make `L_1/L_2` a ratio of two nonzero integers, a contradiction.  At `w=0`, both
amplitudes equal their positive widths.  Hence

```text
for every w in C,
A_(L_1)(w)!=0 or A_(L_2)(w)!=0.                           (24)
```

Apply `(24)` to `w=rho-1/2`.  For every nontrivial zeta zero `rho`, at least one of the two
sharp-window continuations has a pole at `rho+1/2`, and its residue divided by the corresponding
`2A_(L_j)(rho-1/2)` is exactly `m(rho)`.  Therefore:

> Two sharp moving-prime windows whose logarithmic widths have irrational ratio recover the
> complete nontrivial zeta divisor, including all critical-line zeros, with exact analytic
> multiplicities.  No functional-equation reflection and no zero input occurs in either
> coefficient sequence.

The concrete pair `L_1=log 2`, `L_2=sqrt(2) log 2` works.

## 7. Positive CCM carrier law

The theorem identifies the positive architecture rather than merely excluding finite models:

```text
cofinal multiplicative prime window
  + scalar pole-charge cancellation
  + bounded-variation quadrature control
  + Mellin noncensorship
  = exact divisor incidence.                              (25)
```

The four resources have separate roles.  The moving window pays for new primes.  The square-root
counterterm removes the zeta-pole charge.  Bounded variation makes the discretization remainder
holomorphic beyond the critical shifted boundary.  The Mellin transform determines exactly which
divisor coordinates remain visible.  Two incommensurable sharp widths eliminate Mellin censorship
globally.

## 8. Parent-theory and significance verdict

1. Bounded-variation quadrature and the Euler logarithmic derivative are classical.
2. After the project vocabulary is erased, `(12)` is the standard transformation obtained by
   reversing the moving-window double sum, replacing its inner Riemann sum by the Mellin integral,
   and absorbing the bounded-variation discrepancy into a holomorphic remainder.  The pole and
   residue statements then follow immediately from the logarithmic derivative.  This is a routine
   parent-theory derivation, so the theorem fails the scientific-novelty gate even if the precise
   packaging is absent from a title or abstract.
3. The sharp-window and two-incommensurable-window statements are useful exact specializations,
   but their proofs add no mechanism beyond the same transform and the elementary zero lattice of
   `(1-exp(-Lw))/w`.  They are therefore bridge infrastructure, not candidate new scientific
   knowledge.
4. The theorem is not eligible to replace the paper's main theorem or to count toward the requested
   significance threshold.  Its legitimate role is to expose a concrete prime-source divisor
   coordinate for later CCM arguments.
5. This theorem still does not prove RH.  The RH-bearing theorem is the positive source
   regularity statement that the explicit sharp-window continuation `(12)` has no poles in
   `Re s>1`, equivalently a source-side condition strong enough to force that holomorphy.

## 9. Lean program

The publication paper must not be strengthened until all items below are concrete Lean theorems.

1. Formalize compactly supported bounded-variation windows and the cellwise quadrature inequality.
2. Prove locally uniform holomorphy of the error series `(9)` on `Re s>1/2`.
3. Prove the initial-half-plane identity `(10)` with `ArithmeticFunction.vonMangoldt`.
4. Define the concrete continuation `(12)` and formalize zeta-pole cancellation.
5. Prove the exact Mellin-censorship law `(13)`--`(14)` using analytic multiplicity.
6. Formalize the sharp rectangle `(17)`--`(22)` and its half-plane nonvanishing.
7. Prove the common-zero classification `(23)`--`(24)` and full two-window divisor recovery.
8. Prove the normalized holomorphic quotient `(15)` and connect it to the existing CCM
   observable divisor class.

No abstract meromorphic-continuation hypothesis, `Prop` interface, project axiom, `sorry`, `admit`,
`opaque`, `unsafe`, or target-defined source is permitted.

## Gates

- [x] complete paper proof of the bounded-variation continuation
- [x] exact Mellin-censorship classification
- [x] sharp unsmoothed one-window RH equivalence
- [x] two-window full nontrivial-divisor recovery
- [x] positive carrier formulation
- [ ] unconditional Lean formalization
- [x] parent-theory novelty gate failed; scientific-novelty promotion retired
- [ ] primary-literature placement audit for citation and historical attribution
- [ ] independent proof audit
- [ ] standalone paper integration
