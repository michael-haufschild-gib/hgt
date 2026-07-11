# The four-unit CCM target is a positive boundary relative-trace density

- **ID:** `ccm-hankel-boundary-relative-trace-four-unit-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT TARGET]`
- **Parent results:** Hilbert--Schmidt kernel calculus, half-line compression, and the off-line
  Cauchy-energy threshold
- **Statement:** Full trace class of the infinitesimal Xi Hankel operator is unnecessary. The
  squared Hilbert--Schmidt mass in the three boundary blocks removed by a two-sided gap cutoff is a
  positive relative trace with kernel `min(t,u)`. Its density at zero is exactly the transverse
  residue energy. The Euler pole has relative trace `4(1-e^(-u))`; an upper density of four for the
  completed source is equivalent to RH.

## 1. Boundary blocks of a Hankel kernel

Let

```text
(H_ell f)(x)=integral_0^infinity ell(x+y)f(y)dy          (1)
```

on `L2(0,infinity)`, where only

```text
ell in L2(0,infinity)                                    (2)
```

is assumed. The full operator need not be Hilbert--Schmidt, since that would additionally require
`integral t|ell(t)|^2dt<infinity`.

For `a>0`, let

```text
P_a=1_[a,infinity),       Q_a=I-P_a.                     (3)
```

The three boundary blocks

```text
Q_a H_ell Q_a,
Q_a H_ell P_a,
P_a H_ell Q_a                                             (4)
```

are Hilbert--Schmidt. Put `u=2a` and define their positive relative trace

```text
Delta_ell(u)
 =||Q_a H_ell Q_a||_(S_2)^2
  +||Q_a H_ell P_a||_(S_2)^2
  +||P_a H_ell Q_a||_(S_2)^2.                            (5)
```

Then

```text
Delta_ell(u)
 =integral_0^infinity min(t,u)|ell(t)|^2dt               (6)

 =integral_0^u t|ell(t)|^2dt
  +u integral_u^infinity |ell(t)|^2dt.                   (7)
```

### Proof

The squared Hilbert--Schmidt norm is the integral of `|ell(x+y)|^2` over the corresponding block
in the first quadrant. On the line segment `x+y=t`, the full first-quadrant length is `t`. The
corner retained by `P_a H_ell P_a` has length `t-2a` when `t>=2a` and length zero otherwise.
Therefore the union of the three removed blocks has line-segment length

```text
t,       0<t<u,
u,       t>=u.                                           (8)
```

Integrating over `t` proves `(6)`--`(7)`. Since `min(t,u)<=u`, assumption `(2)` makes `(5)` finite
without any full trace-class hypothesis.

The same carrier has an intrinsic commutator form. The off-diagonal blocks of `[P_a,H_ell]` are
`P_aH_ell Q_a` and `-Q_aH_ell P_a`, and they are orthogonal in Hilbert--Schmidt space. Hence

```text
Delta_ell(2a)
 =||Q_aH_ell Q_a||_(S_2)^2
  +||[P_a,H_ell]||_(S_2)^2.                              (8a)
```

Thus the relative trace is exactly a local corner plus a projection-commutator energy. This is the
form directly compatible with semilocal cutoff and relative-trace constructions.

## 2. Relative-trace density is residue energy

Equation `(6)` gives

```text
Delta_ell(u)/u
 =integral_0^infinity min(t/u,1)|ell(t)|^2dt.            (9)
```

Dominated convergence yields

```text
lim_(u->0+)Delta_ell(u)/u=||ell||_2^2.                   (10)
```

Equivalently, when the full shifted Hankel trace `F_ell` exists,

```text
Delta_ell(u)=F_ell(0)-F_ell(u),
lim_(u->0+)Delta_ell(u)/u=-F_ell'(0+).                   (11)
```

But `(5)`--`(10)` remain valid when both traces on the right side of `(11)` are unavailable
separately. This is the canonical relative formulation.

## 3. Incoming Euler pole

For

```text
ell_pole(t)=2 exp(-t/2),                                  (12)
```

equation `(7)` gives

```text
Delta_pole(u)=4(1-exp(-u)),                              (13)

lim_(u->0+)Delta_pole(u)/u=4.                            (14)
```

Thus the four-unit source budget is an initial boundary-layer density, not a global trace norm.

## 4. Completed divisor and exact RH criterion

For a finite right-half Xi divisor, let

```text
ell_E(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t),
0<a_j<1/2.                                               (15)
```

The Cauchy-energy theorem gives

```text
||ell_E||_2^2
 =4 sum_(j,k)m_jm_k
   (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2)
 >4                                                       (16)
```

whenever the divisor is nonempty. If the off-line divisor is infinite, its monotone finite-subset
energies diverge, and the extended value is `+infinity`.

Combining `(10)`, `(14)`, and `(16)` gives

```text
RH
 <-> limsup_(u->0+) Delta_E(u)/u<=4

 <-> limsup_(u->0+) Delta_E(u)/Delta_pole(u)<=1.         (17)
```

The second ratio uses `(13)` and has the direct meaning that completion does not increase the
infinitesimal boundary relative trace.

## 5. Positive CCM/Connes obligation

Let `D_Xi` be the closed anti-causal logarithmic-source Hankel operator. A successful semilocal
construction need not prove `D_Xi` or its full two-sided cut-down Hilbert--Schmidt. It must instead
construct, from the Euler--Gamma source, the three positive boundary-block traces in `(5)` and prove

```text
Delta_Xi(u)<=4(1-exp(-u))+o(u)       as u->0+.           (18)
```

Equivalently it may prove the quotient bound in `(17)`. This is a relative trace-ideal theorem:

```text
closed orbit-sensitive Xi graph
  + two-sided boundary cutoff
  + trace-class boundary blocks
  + nonexpansive relative-trace density
  -> RH.                                                   (19)
```

The carrier is strictly smaller than full Hankel trace class and strictly stronger than bounded
graph convergence. It is also native to the CCM semilocal framework, whose established trace
formulas are relative compression formulas.

## 6. Rational-orbit attack

For an inserted pole at horizontal depth `a`, the residue mode has energy proportional to `1/a`.
Equations `(10)` and `(17)` therefore show that no estimate `(18)` can hold uniformly over the
FE--Schwarz rational gauge family. The relative trace must remain pointed by the exact Xi source;
bounded graph isomorphism does not preserve its boundary density.

## 7. Scientific classification and Lean decision

The block decomposition `(6)` and dominated-convergence limit `(10)` are standard Hankel kernel
calculus. This is a route bridge, not new scientific knowledge. Its value is to remove the
unnecessary full trace-class hypothesis and identify the smallest positive trace object on which a
CCM proof can operate.

The Lean tree lacks half-line Hankel integral operators and Hilbert--Schmidt block traces. A finite
kernel shadow would not certify the source construction in `(18)`, so no Lean file is added.

## Gates

- [x] three positive boundary blocks isolated
- [x] exact `min(t,u)` relative-trace kernel
- [x] equivalent local-corner plus projection-commutator formula
- [x] relative-trace density equals residue energy
- [x] incoming pole relative trace computed exactly
- [x] RH-equivalent nonexpansive density criterion
- [ ] construct the boundary-block traces directly from the Xi source graph
- [ ] prove the relative-trace estimate `(18)`
- [ ] RH
