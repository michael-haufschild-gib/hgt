# Prime superspace is locally Wick-symmetric but globally decompactifies its clock

- **ID:** `prime-superspace-wick-anisotropy-decompactification`
- **Stage:** 2-fully-proven / Lean finite core verified
- **Type:** THEOREM / QUANTUM-GRAVITY AND PHASE-SPACE REFORMULATION
- **Scientific status:** `[PROVED; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the user's inner-scale-factor/external-clock conjecture; finite prime coherent states;
  `prime-clock-critical-window-scaling`; separate from RHTower Routes A--D
- **Statement:** Radial scale separation and vertical clock separation have the same infinitesimal
  Fisher metric and Wick-related `1/log N` profiles, but opposite global behavior. Radial separation
  is coercive; finite-prime clock separation is recurrent. In the all-prime limit every fixed
  nonzero clock displacement becomes orthogonal at the sharp rate `1/log N`, while recurrence times
  escape to infinity. External time therefore emerges by thermodynamic decompactification, not as a
  finite-prime Hamiltonian flow forced by the scale factor.

## 1. Finite prime superspace

For `N>=2`, let

```text
a_(N,t)(p)=p^(-1/2-it),  p<=N.
```

These are the finite-prime coherent displacements at the critical scale. Use the coordinate

```text
r=2(Re(s)-1/2)
```

for reflected radial separation and `h` for clock separation.

The radial and vertical squared distances are

```text
R_N(r)
  = sum_(p<=N) |p^(-1/2-r/2)-p^(-1/2+r/2)|^2
  = 4 sum_(p<=N) sinh(r log p/2)^2/p
  = 2 sum_(p<=N) (cosh(r log p)-1)/p,                 (1)

V_N(h)
  = ||a_(N,t+h)-a_(N,t)||^2
  = 4 sum_(p<=N) sin(h log p/2)^2/p
  = 2 sum_(p<=N) (1-cos(h log p))/p.                 (2)
```

Both are independent of the base height `t`. Let

```text
chi_N=sum_(p<=N)(log p)^2/p.                          (3)
```

## 2. Exact Wick anisotropy

`[PROVED ON PAPER; PROVED IN LEAN]` For every real `r`,

```text
V_N(r) <= r^2 chi_N <= R_N(r).                        (4)
```

### Proof

The elementary inequalities

```text
sin(x)^2 <= x^2 <= sinh(x)^2
```

applied prime by prime to `(1)`--`(2)` give `(4)`. QED.

Thus both directions have the same Hessian `2 chi_N` at the origin, after the coordinate
normalization `r=2 epsilon`, but immediately bend in opposite directions:

- the radial hyperbolic distance lies above its tangent quadratic form;
- the clock trigonometric distance lies below it.

This is an exact obstruction to treating the finite-prime superspace as globally Lorentzian after
a formal Wick rotation. Wick rotation is valid for the analytic germ, not for the global positive
metric.

## 3. The common logarithmic tangent window

Mertens' first theorem gives

```text
chi_N/(log N)^2 -> 1/2.                               (5)
```

Inside the first non-wrapping clock window `|h| log N<=pi`, the sine chord inequality gives

```text
(4/pi^2) h^2 chi_N <= V_N(h) <= h^2 chi_N.            (6)
```

This is proved in Lean. In particular, for `h=c/log N` and `|c|<=pi`,

```text
(4/pi^2)c^2 chi_N/(log N)^2
  <= V_N(c/log N)
  <= c^2 chi_N/(log N)^2.                             (7)
```

Hence the vertical clock has the same nondegenerate `1/log N` tangent window as the radial scale
factor.

The exact profiles follow from the same Mertens probability measures

```text
nu_N=(1/log N) sum_(p<=N) ((log p)/p) delta_(log p/log N)
     -> Lebesgue_[0,1].                               (8)
```

For fixed real `c`, `(8)` and the continuous removable integrands give

```text
R_N(c/log N) -> Phi_R(c)
  = 2 integral_0^1 (cosh(cu)-1)/u du,                 (9)

V_N(c/log N) -> Phi_T(c)
  = 2 integral_0^1 (1-cos(cu))/u du.                  (10)
```

Define the entire even germ

```text
Phi(z)=2 integral_0^1 (cosh(zu)-1)/u du
      = sum_(k>=1) z^(2k)/(k(2k)!).                   (11)
```

Then

```text
Phi_R(c)=Phi(c),
Phi_T(c)=-Phi(i c).                                   (12)
```

Both profiles begin with `c^2/2`. Equation `(12)` is the exact local Wick relation; inequality
`(4)` is its positive-metric anisotropy.

### Proof of `(9)`--`(10)`

For `u=log p/log N`, equations `(1)`--`(2)` become integrals against `nu_N` with test functions

```text
f_R(c,u)=2(cosh(cu)-1)/u,
f_T(c,u)=2(1-cos(cu))/u,
```

extended by zero at `u=0`. Both extensions are continuous on `[0,1]`. Weak convergence `(8)` gives
the two limits. The power series follows by termwise integration on compact `z`-sets, and
`cosh(i x)=cos x` proves `(12)`. QED.

## 4. Finite clock recurrence

`[PROVED ON PAPER]` For every fixed finite `N` and every `eta>0`, there are arbitrarily large
`|h|` such that

```text
V_N(h)<eta.                                            (13)
```

### Proof

The clock map

```text
h |-> (exp(-i h log p))_(p<=N)
```

is a continuous one-parameter subgroup of the finite torus. Its orbit closure is compact. Every
translation on a compact group is uniformly recurrent: the return set to every neighborhood of the
identity is relatively dense, hence unbounded. When the phase vector returns sufficiently close to
the identity, every summand in `(2)` is arbitrarily small, proving `(13)`. QED.

Unique factorization makes the frequencies `log p` rationally independent, so the orbit closure is
in fact the full finite prime torus. Density is stronger than the recurrence needed here.

By contrast,

```text
R_N(r) -> infinity as |r|->infinity                  (14)
```

for every `N>=2`, already because the `p=2` summand tends to infinity. Therefore radial scale and
clock time are globally inequivalent:

```text
radial coordinate: noncompact and coercive,
clock coordinate:  compact-group recurrent at every finite cutoff.       (15)
```

## 5. Thermodynamic decompactification

Fix `h!=0`. The prime-number theorem with the classical de la Vallee Poussin remainder gives
conditional convergence of the naturally ordered boundary prime sum

```text
C(h)=lim_(N->infinity) sum_(p<=N) p^(-1-i h).          (16)
```

Euler--Mertens gives

```text
sum_(p<=N)1/p=log log N+B_1+o(1).                     (17)
```

Taking real parts in `(16)` and using `(2)` yields the sharp law

```text
V_N(h)
  =2 log log N+2B_1-2 Re C(h)+o(1).                   (18)
```

Let `e(a_(N,t))` denote the normalized bosonic coherent vector. Its overlap satisfies

```text
|<e(a_(N,t+h)),e(a_(N,t))>|
  = exp(-V_N(h)/2)
  ~ exp(Re C(h)-B_1)/log N.                            (19)
```

Thus every fixed nonzero time translation becomes orthogonal in the all-prime limit, at the exact
logarithmic rate `1/log N`. This refines the previously proved qualitative disjointness of distinct
critical height sectors.

Equations `(13)` and `(18)` form a noncommuting-limits theorem:

```text
for each finite N:  liminf_(|h|->infinity) V_N(h)=0,
for each fixed h!=0: lim_(N->infinity) V_N(h)=infinity.        (20)
```

The finite recurrence times necessarily escape as `N` grows. The infinite-prime limit therefore
decompactifies the clock: height translations cease to be recurrent motions inside one Hilbert
sector and become outer motions between mutually disjoint sectors.

## 6. Quantum-gravity reading

The internal radial metric does not create an ordinary external Hamiltonian time. What it creates
is a thermodynamic distinction between two limits:

```text
finite prime universe:
  scale is noncompact; time is a recurrent angle on a compact phase torus,

all-prime constraint:
  fixed time translations become infinitely separated sectors;
  recurrence is pushed to infinite clock time.                         (21)
```

This is a precise mechanism for emergent time in the prime superspace. The `1/log N` boundary layer
is the local Wick-symmetric tangent region where radial scale and clock are measured by one Fisher
susceptibility. The global all-prime constraint breaks that symmetry and externalizes time.

## 7. RH verdict

`[PROVED KINEMATICS; RH-BLIND]` The decompactification occurs for every nonzero height difference,
not only at zeta-zero heights. It therefore does not prove RH or identify the divisor.

It does sharpen the boundary-transfer requirement. A finite-prime RH construction cannot use a
global finite clock flow: that flow always recurs. It must instead prove that its defect parameters
survive the cofinal limit in which recurrence times escape, and it must transfer its zero divisor
locally uniformly through the `1/log N` tangent layer.

The joint open core is now

```text
source-defined finite defects
  -> locally uniform zero preservation to Xi
  -> sub-log-square radial pinning
  -> compatibility with clock decompactification.                    (22)
```

The last condition cannot be replaced by finite spectral agreement or a finite Hamiltonian.

## 8. Parent-theory boundary

After erasing the project vocabulary, the proof is a direct composition of:

- elementary sine/sinh inequalities;
- Mertens' first theorem and weak convergence of weighted prime measures;
- recurrence of one-parameter subgroups on compact tori;
- Euler--Mertens and conditional convergence of `sum_p p^(-1-i h)`.

The exact assembled superspace statement was not audited for literature novelty in this pass, but
its mechanism is routine in the parent theories. It is therefore classified as a proved bridge,
not new scientific knowledge.

## 9. Lean surface

`formal/GaloisForLFunctions/PrimeSuperspaceWickAnisotropy.lean` proves:

- `primeClockVerticalEnergy_eq_cos`;
- `primeClockVerticalEnergy_quadratic_upper`;
- `primeClock_wick_anisotropy`;
- `primeClockVerticalEnergy_quadratic_lower`;
- `primeClockVerticalEnergy_critical_scaled_sandwich`.

The exact finite anisotropy and the nondegenerate vertical critical window are axiom-clean. The
compact-torus recurrence and PNT boundary asymptotic remain paper theorems; formalizing them would
require substantial general topological-dynamics and boundary-prime-series infrastructure and is
not needed by a current downstream construction.

## Gates

- [x] exact radial and vertical energies identified
- [x] finite Wick anisotropy proved on paper and in Lean
- [x] common `1/log N` tangent window proved
- [x] exact Wick-related limiting profiles proved on paper
- [x] finite recurrence and radial coercivity proved
- [x] thermodynamic `1/log N` overlap law proved
- [x] RH implication attacked and shown absent
- [ ] formalize recurrence/asymptotic only if required by a source-built zero-transfer construction

