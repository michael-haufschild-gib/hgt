# Euler shift-pair incidence and the horizontal-charge resultant

- **ID:** `euler-shift-pair-incidence-resultant`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `../../1-in-progress/euler-horizontal-charge-separator.md`;
  `horizontal-entry-charge-transfer.md`; Suzuki's shifted Xi quotient
- **Statement:** The off-line horizontal cross-charge is exactly the positive-real-shift part of
  the local intersection/resultant cycle of the *uncancelled* pair
  `F(c-u), F(c+u)`.  The reduced shifted quotient cancels this incidence and retains only the
  minimum common multiplicity, whereas the resultant carries the product multiplicity required by
  horizontal charge.  Adding the reduced diagonal gives the conserved collision charge
  `O_I+M_I`.

## Goal

Decide whether the anti-causal shifted-Xi operator itself carries the integer measure requested by
Route C.  The result separates two objects that had been conflated:

```text
uncancelled shift pair / resultant  -> horizontal incidence,
reduced shift quotient / leakage    -> divisor after common-factor cancellation.
```

The theorem constructs the exact charge from the completed function, but supplies no source-side
bound on it.  It is therefore an exact encoding and route-control bridge, not an RH mechanism.

## Setup

Let `F` be a nonzero entire function with discrete zero multiset `Z(F)`.  Write `m_rho` for the
order of a zero `rho`.  On `C^2` with coordinates `(c,u)`, define

```text
F_-(c,u)=F(c-u),
F_+(c,u)=F(c+u).                                           (1)
```

Their zero divisors have a zero-dimensional local intersection cycle.  The linear map

```text
L(c,u)=(c-u,c+u)                                           (2)
```

is biholomorphic, with determinant `2`.  Hence an intersection point is the same datum as an
ordered pair `(rho,sigma)` of zeros of `F`, with

```text
c=(rho+sigma)/2,       u=(sigma-rho)/2.                    (3)
```

For the completed zeta function, restrict to zeros whose ordinates lie in a bounded interval `I`
avoiding zero ordinates at its endpoints.  There are finitely many such zeros.  A point of the
intersection cycle has `u>0` real exactly when `rho` and `sigma` are distinct zeros at the same
ordinate and `Re rho<Re sigma`.

## Theorem A: local product multiplicity

At the point `(c,u)` corresponding to zeros `rho` and `sigma`, the local intersection multiplicity
of `F_-` and `F_+` is

```text
i_(c,u)(F_-,F_+)=m_rho m_sigma.                            (4)
```

### Proof

Use the local coordinates

```text
x=c-u-rho,       y=c+u-sigma.
```

Their linear part is invertible by `(2)`.  In the two one-variable local rings,

```text
F(rho+x)=x^(m_rho) U(x),
F(sigma+y)=y^(m_sigma) V(y),                               (5)
```

where `U(0)` and `V(0)` are nonzero.  Units do not change intersection multiplicity, so the local
intersection algebra is

```text
C{x,y}/(x^(m_rho),y^(m_sigma)).                            (6)
```

The monomials `x^i y^j` with `0<=i<m_rho` and `0<=j<m_sigma` form a basis.  Its dimension is
`m_rho m_sigma`, proving `(4)`.

## Theorem B: the off-diagonal resultant is horizontal charge

For each ordinate `gamma`, let

```text
H_gamma=sum_(Im rho=gamma) m_rho.
```

Push twice the positive-real-`u` part of the intersection cycle through `(c,u) |-> Im c`.  Denote
the resulting positive integer measure by `Omega_F^off`.  Then

```text
Omega_F^off(I)
 = 2 sum_(gamma in I) sum_(Re rho<Re sigma, Im rho=Im sigma=gamma)
       m_rho m_sigma
 = sum_(gamma in I) H_gamma^2
     - sum_(Im rho in I) m_rho^2.                          (7)
```

For `F=xi`, the right side is exactly the Route C off-line horizontal cross-charge `O_I`.

### Proof

By `(3)`, positive real `u` parametrizes unordered pairs of distinct zero locations at the same
ordinate, with the left zero listed first.  Equation `(4)` assigns the product multiplicity to each
such pair.  Multiplication by two restores the two ordered orientations.  Expanding

```text
H_gamma^2
 = sum_(Im rho=gamma) m_rho^2
   + 2 sum_(Re rho<Re sigma, Im rho=Im sigma=gamma) m_rho m_sigma
```

proves `(7)`.

For a self-dual completed function, every off-line zero has a distinct reflected zero at the same
ordinate.  Therefore `Omega_F^off(I)=0` if and only if every zero in the window is fixed by the
reflection, i.e. lies on the critical line.

## Theorem C: the diagonal absorbs entry charge

At `u=0`, a zero `rho` of multiplicity `m_rho` contributes intersection multiplicity `m_rho^2`.
Subtracting the `m_rho` identity copies leaves

```text
m_rho^2-m_rho=m_rho(m_rho-1).                             (8)
```

Thus the reduced diagonal mass is the multiplicity charge `M_I`, and the total reduced real-shift
incidence mass is

```text
Omega_F^off(I)+Omega_F^diag(I)=O_I+M_I=C_I-N_I.            (9)
```

For a simple reflected pair colliding on the critical line, two units of positive-`u` intersection
mass reach `u=0`; after collision they are precisely the two reduced diagonal units of a double
zero.  The natural positive intersection cycle therefore conserves `O_I+M_I`, not `O_I` alone.

This gives the constraint-side geometry of the known charge transfer:

```text
off-line incidence  -> boundary at u=0 -> multiplicity incidence.
```

## Theorem D: reduced leakage deletes the charge carrier

Fix `u>0` and form the shifted quotient

```text
Theta_u(c)=F(c-u)/F(c+u).                                  (10)
```

At a common zero corresponding to `rho=c-u` and `sigma=c+u`, with orders `m_rho,m_sigma`, quotient
reduction cancels order

```text
min(m_rho,m_sigma).                                       (11)
```

The intersection/resultant multiplicity at the same point is instead

```text
m_rho m_sigma.                                            (12)
```

Consequently the rank of the Hardy leakage of the *reduced* quotient cannot recover horizontal
charge at exceptional shifts.  Even its rank deficit sees `(11)`, not `(12)`.  The charge belongs
to the uncancelled ordered pair—or equivalently its resultant/intersection cycle—not to the
quotient after common-divisor cancellation.

### Proof

In a local coordinate `z=c'-c`, the numerator and denominator of `(10)` are units times
`z^(m_rho)` and `z^(m_sigma)`.  Cancelling their greatest common power removes
`z^min(m_rho,m_sigma)`, proving `(11)`.  Equation `(12)` is theorem A.

## Theorem E: a divisor-free current construction of the measure

The infinite shift-pair intersection does not require an enumeration or canonical product of the
zeros.  In the global statement below, assume the relevant zero divisor lies in a fixed vertical
strip; this holds for `F=xi`.  For an arbitrary entire function the same construction is local on
compact subsets of `(c,u)`-space.  Normalize `dd^c` so that the Poincare--Lelong formula reads

```text
dd^c log|F|=[div F].                                      (13)
```

On `C^2`, define the positive intersection current

```text
J_F
 = dd^c log|F(c-u)| wedge dd^c log|F(c+u)|.               (14)
```

This wedge is well-defined.  The two polar divisors intersect properly: under the biholomorphism
`L` in `(2)`, they become `div(F) x C` and `C x div(F)`, whose intersection is the locally finite
zero-cycle `div(F) x div(F)`.  Consequently

```text
J_F=sum_(rho,sigma in Z(F))
      m_rho m_sigma delta_((rho+sigma)/2,(sigma-rho)/2).   (15)
```

Equation `(14)`, rather than `(15)`, is the construction: it uses only values of the completed
function and the canonical Poincare--Lelong operation.

Let `I` be a bounded interval avoiding zero ordinates at its endpoints.  Choose any continuous
compactly supported `kappa:R->R` with

```text
0<=kappa<=1,       kappa(0)=1,
supp(kappa) subset [-1,1].                                (16)
```

For `epsilon>0`, put

```text
Omega_(F,epsilon)^off(I)
 = 2 integral 1_(Im c in I) 1_(Re u>0)
       kappa(Im u/epsilon) dJ_F(c,u).                     (17)
```

Then the limit exists, is independent of `kappa`, and satisfies

```text
lim_(epsilon->0+) Omega_(F,epsilon)^off(I)
 = Omega_F^off(I).                                       (18)
```

### Proof

For `epsilon<=1`, every atom contributing to `(17)` has `Im c` in the bounded interval `I` and
`|Im u|<=1`.  Since

```text
rho=c-u,       sigma=c+u,
```

both zero ordinates then lie in one fixed bounded interval.  The vertical-strip hypothesis also
bounds both real parts.  The zero divisor of a nonzero entire function is locally finite, so only
finitely many ordered pairs occur in `(17)`.

For each of these finitely many atoms, `kappa(Im u/epsilon)` tends to one when `Im u=0` and is
eventually zero when `Im u!=0`.  The condition `Re u>0` selects the left-to-right orientation.
Taking the finite limit in `(15)` therefore gives exactly twice the product multiplicity of every
distinct same-ordinate pair, which is theorem B.  The argument uses only `(16)`, proving cutoff
independence and `(18)`.

For `F=xi`, equations `(14)`, `(17)`, and `(18)` give a canonical construction of `Omega_E` from
the completed Euler--Gamma function without first factoring Xi into zeros.  The construction is
nonlinear and discontinuous at horizontal incidence, as it must be; it supplies no estimate on the
resulting positive integer.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The result is a useful native formulation, but it fails the
parent-theory and anti-theatre gates.  After erasing the Xi notation, theorem A is the standard
local intersection multiplicity of two one-variable divisors after an invertible linear change of
coordinates; theorem B is the elementary off-diagonal expansion of a squared multiplicity; and
theorem D is ordinary common-factor cancellation.  Resultants have classically encoded common
roots with product multiplicity.

The Route C consequence is nevertheless decisive: the source object capable of carrying
horizontal charge is the *uncancelled shift-pair resultant*.  The reduced Hardy leakage is the
wrong carrier for that integer.  Poincare--Lelong gives the canonical infinite current directly,
so proving a `<2` bound for its positive-real-shift mass is now exactly the missing arithmetic
theorem.

## Open core

Prove directly from the Euler--Gamma source that the positive-real-shift mass of the canonical
current `(14)` is `<2` on a genuinely new window.  The current construction is closed; an
Euler-region formula, positivity, or boundary estimate capable of proving the absolute bound is
not.  Proving its vanishing by first expanding `(15)` is RH in resultant language.

## Gates

- [x] 0 -> 1: source pair, local cycle, and falsifier specified.
- [x] 1 -> 2: local intersection, charge identity, diagonal transfer, and quotient-cancellation
  theorems proved on paper; the Poincare--Lelong current and cutoff-independent source construction
  are complete.
- [x] 2 -> 3: formalized in Lean using the canonical entire-function Poincare--Lelong identity,
  literal locally finite zero-divisor product current, exact cutoff-independent thin-slice limit,
  local intersection algebra, diagonal conservation, and quotient-cancellation colength.
- [ ] 3 -> 4: requires the genuinely arithmetic `<2` theorem, not this exact encoding.

## 2026-08-23 (Codex) — formalization

Lean module `GaloisForLFunctions.RHTower.EulerShiftPairIncidenceCurrent` proves:

- canonical Poincare--Lelong identity for Xi from source values;
- inverse shift-pair coordinate and global locally finite product current expansion;
- reduction of every sufficiently thin source-current slice to a finite Xi zero set;
- cutoff-independent convergence to `xiHorizontalCollisionCharge`;
- ordered-pair quadratic census and zero-charge critical-line classification;
- reduced diagonal conservation `O_I+M_I=C_I-N_I`;
- local product multiplicity `m*n` versus quotient cancellation `min m n`, with a closed
  counterexample showing the two carriers differ.

No-argument capstone:
`RHTower.EulerShiftPairIncidenceCurrent.eulerShiftPairIncidenceResultant_unconditional`.
Direct Lean check and targeted leaf build passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Module is wired into `GaloisForLFunctions.RHTower`; umbrella
was not built.
