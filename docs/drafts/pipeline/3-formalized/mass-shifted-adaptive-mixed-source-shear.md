# Mass-shifted adaptive mixed-source shear

- **ID:** `mass-shifted-adaptive-mixed-source-shear`
- **Stage:** 3-formalized
- **Type:** SOURCE-FIRST BILINEAR CONNECTION / POSITIVE SURVIVOR
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, Conjecture 50
- **RH used:** no
- **Computation used:** no
- **Lean:** `XiShiftedHankelBoundaryAdaptiveMixedSourceShear.lean`

## Exact theorem

Let

```text
m_k(y) = Re xiShiftedReciprocalMoment(y,k),
L_y(f) = momentFunctional(m(y),f),
E_1 p = X p' + p,
B_y(p) = L_y(p Xp).
```

For every real polynomial `p` and every `y>0`,

```text
d/dy B_y(p) = -2 L_y((Xp)(X E_1p)).                    (1)
```

Let `c(p)` be the finite coefficient packet of `p^2`. Then

```text
B_y(p) = S_(1,c(p))(y),                                (2)
S_(2,M_1c(p))(y) = 2 L_y((Xp)(X E_1p)).                (3)
```

At `y=w^2`, `w>1/2`, the common landing in `(3)` has the exact pre-aggregation source split

```text
Arch_(w,2,M_1c(p)) + Disc_(w,2,M_1c(p))
  = 2 (ArchPair_w(Xp,X E_1p) + DiscPair_w(Xp,X E_1p)), (4)
```

and its factorial carrier is the mixed amplitude

```text
P_(2,M_1c(p))(T) = Q_(1,c(p))(T).                       (5)
```

In the endpoint window `0<y<41/2`, the landing also has the zero-free source presentation

```text
d/dy B_y(p)
  = -2 momentInner(Re primeArchShiftedReciprocalMoment(y,·), Xp, X E_1p). (6)
```

Every moment on this right-hand side is the absolutely convergent negative-binomial transform of
the normalized prime--Gamma moment tower.

Thus actual mass differentiation consumes marked odd crossing current and lands on even adaptive
null-flag shear before reflection aggregation. No fixed reporter or orientation map is chosen.

## Dependency-closed paper proof

Completed moment transport gives

```text
m_k'(y)=-(k+1)m_(k+1)(y).
```

Hence, for every polynomial `f`, coefficientwise differentiation gives

```text
d/dy L_y(f) = -L_y(X E_1 f).                            (7)
```

Apply `(7)` to `f=p Xp`. Polynomial differentiation and commutativity give the exact
Euler--Leibniz identity

```text
X E_1(p Xp) = 2 (Xp)(X E_1p),                           (8)
```

which proves `(1)`. Since `p Xp=X p^2`, expanding `p^2` in its finite coefficient packet gives
`(2)`. The general completed aggregate derivative is

```text
S_(1,c)'=-S_(2,M_1c).
```

Uniqueness of the derivative, `(1)`, and `(2)` imply `(3)`. The corpus completed-source identity
splits each aggregate before either arithmetic integral; the pairing-level source identity does
the same for both probes. Substitution into `(3)` proves `(4)`. Finally, one shifted Euler step on
squared-factorial coefficients gives

```text
(j+2)c_j / ((j+2)!)^2 = c_j / ((j+1)!(j+2)!),
```

which proves `(5)`. The corpus equality between shifted Xi moments and the source-only
negative-binomial prime--Gamma moments proves `(6)` termwise in the finite polynomial pairing.

Hostile audit: `(1)--(6)` are exact identities. They do not assume positivity, RH, terminal-flux
orientation, or any downstream cumulant cap. They do not prove strict sign. Remaining theorem is
strict arithmetic comparison of the two source channels in `(4)` on the adaptive packet.

## Lean closure

Target audit:

```text
lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveMixedSourceShear
```

passed. `#print axioms` for the source connection, odd-to-even shear, coefficient-packet bridge,
completed source split, and capstone reports only:

```text
propext, Classical.choice, Quot.sound
```

Module is umbrella-wired through `GaloisForLFunctions.RHTower`.

## Status

`[PAPER-PROVED] [LEAN-FORMALIZED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED] [NOT RH]`.

## Log

- 2026-08-10 — conjectured Euler--Leibniz lift after exact midpoint source law; proved odd current
  must land on even adaptive shear; formalized completed packet, mixed `Q`, pairing split, and
  capstone without computation.
