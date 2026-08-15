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

There is a simpler one-sided realization. Since `Q_u` projects the output variable onto `[0,u)`,

```text
Delta_ell(u)=||Q_uH_ell||_(S_2)^2.                       (5a)
```

Indeed, on the line `x+y=t`, the strip `0<=x<u` has length `min(t,u)`, exactly the weight in `(6)`.
Thus the three-block relative trace and the one-sided output-boundary trace are identical for every
Hankel kernel.

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

The local corner is lower order. Indeed, if `u=2a`, then

```text
||Q_aH_ell Q_a||_(S_2)^2
 =integral_0^u t|ell(t)|^2dt,                            (8b)
```

and therefore

```text
1/u ||Q_aH_ell Q_a||_(S_2)^2
 <=integral_0^u |ell(t)|^2dt ->0.                        (8c)
```

Combining `(8a)` and `(10)` below gives the pure commutator-density identity

```text
lim_(a->0+) 1/(2a)||[P_a,H_ell]||_(S_2)^2
 =||ell||_2^2.                                           (8d)
```

Thus no first-order residue charge lives in the shrinking local corner. The entire charge crosses
the cutoff interface.

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

This metric residue coordinate is the anti-causal half of the exact bilateral resolvent packet
seen by the infinitesimal Euler-ray kernel.  For `lambda=a+i gamma`, the Euler kernel's negative
coordinate is the antisymmetric causal/anti-causal combination whose Laplace density is
`exp(i gamma t)sinh(a t)`, up to the fixed Fourier conjugation convention, while `(15)` is its
decaying half.  Therefore
the negative index and the relative-trace slope are respectively the quantized and metric readings
of the same source-graph channel.  See
`ccm-quartet-resolvent-bilateral-polarization-law.md`.

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
construction need not prove `D_Xi` or its full two-sided cut-down Hilbert--Schmidt.

For a densely defined operator `T`, define its extended Hilbert--Schmidt norm to be the norm of the
unique Hilbert--Schmidt operator extending `T` when such an extension exists, and `+infinity`
otherwise. Density makes the extension unique. Equation `(5a)` therefore gives the unconditional
source-side definition

```text
Delta_Xi(u)=||Q_uD_Xi||_(S_2,ext)^2 in [0,+infinity].    (17a)
```

No zero list, residue expansion, or trace-class assumption enters `(17a)`. The closed Xi source
graph constructs the extended relative trace; finiteness is part of the desired estimate.

A successful semilocal construction must prove

```text
Delta_Xi(u)<=4(1-exp(-u))+o(u)       as u->0+.           (18)
```

Equivalently it may prove the quotient bound in `(17)`. This is a relative trace-ideal theorem:

```text
closed orbit-sensitive Xi graph
  + one-sided output boundary cutoff
  + extended Hilbert--Schmidt trace
  + nonexpansive relative-trace density
  -> RH.                                                   (19)
```

The carrier is strictly smaller than full Hankel trace class and strictly stronger than bounded
graph convergence. It is also native to the CCM semilocal framework, whose established trace
formulas are relative compression formulas.

By `(8d)`, the exact RH-bearing estimate can also be written

```text
limsup_(a->0+) 1/(2a)||[P_a,D_Xi]||_(S_2,ext)^2<=4.      (19a)
```

The extended value is `+infinity` if the commutator has no Hilbert--Schmidt extension. Equation
`(19a)` makes the required source theorem a cutoff-commutator density bound rather than an absolute
operator trace.

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
- [x] equivalent one-sided output-boundary Hilbert--Schmidt trace
- [x] exact `min(t,u)` relative-trace kernel
- [x] equivalent local-corner plus projection-commutator formula
- [x] local corner proved negligible at first order
- [x] residue energy identified with pure cutoff-commutator density
- [x] relative-trace density equals residue energy
- [x] incoming pole relative trace computed exactly
- [x] RH-equivalent nonexpansive density criterion
- [x] extended relative trace constructed directly from the closed Xi source graph
- [ ] prove the relative-trace estimate `(18)`
- [ ] RH

## Lean status

Section 7 above said "no Lean file is added" because the tree lacked half-line Hankel operators.
That reasoning was too pessimistic: the whole proved content of this card is a statement about the
*kernel* `ell`, not about the operator, and the geometric heart of the card — that the strip removed
by the one-sided output cutoff has antidiagonal length `min(t,u)` — is an honest Tonelli computation
that Lean can carry unconditionally.

Module: `GaloisForLFunctions.RHTower.CCMBoundaryRelativeTrace` (new), built on the pre-existing
`GaloisForLFunctions.RHTower.CCMHankelGapTraceSlope`.

- `boundaryBlockEnergy` — equation `(5a)`, the squared Hilbert--Schmidt mass of the output-boundary
  block of the Hankel kernel `k(x,y)=ell(x+y)`, as an `ENNReal`-valued quantity that is defined with
  no trace-class hypothesis whatsoever.
- **`boundaryBlockEnergy_eq_lintegral`** — equations `(5a)`--`(6)`: the block energy is
  `integral min(t,u)|ell(t)|^2 dt`. Proved by translating the inner half-line, swapping with Tonelli
  and evaluating `vol(Ioo 0 u inter Iio t) = min(t,u)`. This is exactly the card's line-segment
  length argument `(8)`.
- **`boundaryBlockEnergy_eq`** — the block energy is finite and equals `Delta_ell(u)` under the sole
  `L^2` hypothesis `(2)`.
- `boundaryRelativeTrace`, `cornerTrace`, `crossTrace` — equations `(6)`, `(8b)` and the
  projection-commutator block of `(8a)`.
- **`boundaryRelativeTrace_eq`** — equations `(7)` and `(8a)`: local corner plus cutoff interface.
- **`boundaryRelativeTrace_eq_gap_sub`** — equation `(11)`: `Delta_ell(u)=F_ell(0)-F_ell(u)`.
- **`boundaryRelativeTrace_div`** — equation `(9)`: the difference quotient is the
  `min(t/u,1)`-weighted residue integral.
- **`tendsto_boundaryRelativeTrace_div`** — equation `(10)`: the density at the origin is
  `||ell||_2^2`.
- **`cornerTrace_div_le`** — equation `(8c)`: the local corner is negligible at first order (proved
  in the sharper form `corner/u <= integral_0^u |ell|^2`).
- **`tendsto_crossTrace_div`** — equation `(8d)`: the entire first-order charge crosses the cutoff
  interface, i.e. the commutator density is the full residue energy.
- **`hankelGapProfile_polePacket`**, **`boundaryRelativeTrace_polePacket`** — equation `(13)`:
  `Delta_pole(u)=4(1-e^(-u))` exactly.
- **`tendsto_boundaryRelativeTrace_div_polePacket`** — equation `(14)`.
- **`tendsto_boundaryRelativeTrace_div_divisorPacket`**, **`tendsto_boundaryRelativeTrace_ratio`** —
  the divisor-packet density and the completed-to-pole ratio limit.
- **`boundaryRelativeTrace_ratio_le_one_iff`**, **`boundaryRelativeTrace_density_le_four_iff`** —
  equations `(16)`--`(17)`: for a finite right-half Xi divisor packet the nonexpansive
  boundary-relative-trace density holds if and only if the packet is empty.

All statements are unconditional: `#print axioms` returns exactly
`[propext, Classical.choice, Quot.sound]` on all nineteen theorems.

Deliberately imported rather than reproved: the operator-side reading of `(3)`--`(5)` (that the
three removed blocks are the Hilbert--Schmidt pieces of `Q_a H_ell Q_a`, `Q_a H_ell P_a`,
`P_a H_ell Q_a`, and that their total is the one-sided block `Q_u H_ell`) is Hilbert--Schmidt kernel
calculus; the Lean module works with the kernel-side energies these norms equal, which is where all
the card's mathematics lives. The extended-norm construction `(17a)`, the source estimate `(18)`,
`(19)`, `(19a)`, and the rational-gauge obstruction of section 6 are the card's own open gates.
