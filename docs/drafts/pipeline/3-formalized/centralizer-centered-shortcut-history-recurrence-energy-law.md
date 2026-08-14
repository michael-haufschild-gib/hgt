# Centralizer-centered shortcut-history recurrence-energy law

- **ID:** `centralizer-centered-shortcut-history-recurrence-energy-law`
- **Stage:** 3-formalized
- **Formalized companion:** `centralizer-centered-shortcut-history-recurrence-energy-law-formalized.md`
- **Type:** theorem / exact static-history reduction / literature-frontier boundary
- **Parents:** `static-circuit-two-memory-orthogonality-law.md`,
  `centralizer-centered-circuit-collision-and-design-barrier-law.md`
- **Status:** `[LEAN-PROVED] [BRIDGE] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-14

## Public sentence

Every adaptive shortcut history obeys one observer--spectral product law: after permanent memory
is removed, its squared mass is bounded by centralizer-conditioned target frame energy times the
system's centralizer-centered recurrence energy.

## Exact theorem

Let `F` be a real Hilbert space, let `U(t)` be a unitary one-parameter group, and let `z,q in F`.
For a finite sample set `J`, times `t_j`, and real weights `w_j`, define

```text
A_w(q) = sum_j w_j <U(t_j)z,q>,
R_w(z) = sum_(i,j) w_i w_j <z,U(t_j-t_i)z>.
```

Then

```text
R_w(z) = ||sum_j w_j U(t_j)z||^2 >= 0                    (1)
```

and

```text
                         A_w(q)^2 <= ||q||^2 R_w(z).       (2)
```

The bound is sharp for every history: choosing

```text
q = sum_j w_j U(t_j)z                                      (2a)
```

makes `(2)` an equality.  Therefore no universally stronger inequality can remove the quadratic
loss without using structure beyond unitary recurrence geometry.

If `w_j>=0`, `eta>=0`, and

```text
<U(t_j)z,q> >= eta                 for every j,           (3)
```

then

```text
             (eta sum_j w_j)^2 <= ||q||^2 R_w(z).          (4)
```

Now take nested orthogonal projections `Pi<=P`, a seed `x`, and a unitary flow fixing `range P`.
Put

```text
z = x-Px,
q = y-Pi x,
r(t) = U(t)x-Px = U(t)z,
B = <Pi x,Pi x> + <(P-Pi)x,q>.
```

For a uniform finite target family `Y={y_k}`, define its frame energy and conditioned frame energy
by

```text
F(Y)    = || |Y|^(-1) sum_k y_k ||^2
        = |Y|^(-2) sum_(k,l) <y_k,y_l>,
F_Pi(Y) = F(Y)-||Pi x||^2.
```

If `Pi y=Pi x`, orthogonal projection gives the exact identity

```text
F_Pi(Y)=||y-Pi x||^2=||q||^2 >= 0.                       (4a)
```

When `Y` indexes each occupied endpoint once in replica-projector Hilbert space, `F(Y)` is the
normalized average replica fidelity of all endpoint pairs.  The theorem itself permits any finite
family; duplicate labels retain their chosen multiplicity.

This quantum identification is formal, not interpretive shorthand.  For every finite pure state
`psi`, vectorize the rank-one projector of its `r`-fold tensor power in real Hilbert--Schmidt
coordinates.  Lean proves

```text
<Proj(psi^tensor r),Proj(phi^tensor r)>_R
  = Fidelity(psi,phi)^r >= 0,
F(Y_r)=|Y|^(-2) sum_(k,l) Fidelity(y_k,y_l)^r.             (4b)
```

Thus the nonnegative-collision premise below is automatic for physical pure-state projector
targets; it is not a sign assumption on raw quantum amplitudes.

Let `Y={y_k}` be any finite nonnegative target dictionary whose uniform preparation moment is `y`
and has the same universal projection as `x`.  At each time `t_j`, the witnessing target `k(j)` may
be chosen adaptively.  If

```text
<U(t_j)x,y_k> >= a,
<U(t_j)x,y_l> >= 0 for every target l,
eta = |Y|^(-1) a-B >= 0,                                  (5)
```

then the same `q` satisfies `(3)`.  Consequently

```text
(eta sum_j w_j)^2
 <= F_Pi(Y) sum_(i,j) w_i w_j
       <x-Px,U(t_j-t_i)(x-Px)>.                            (6)
```

Thus target adaptation disappears before the temporal estimate.  Equation `(6)` is an exact
observer--spectral reciprocity law: observer geometry enters only through conditioned average
target overlap, while static dynamics enters only through one stationary positive-definite
recurrence kernel.  It contains no time-dependent circuit selector, minimum endpoint separation,
minimum spectral gap, or Haar-mixing premise.

## Dependency-closed proof

Let `v=sum_j w_j U(t_j)z`.  Bilinearity gives

```text
A_w(q)=<v,q>.
```

Cauchy--Schwarz gives `(2)`.  Unitarity and the group law give

```text
<U(t_i)z,U(t_j)z>
 = <z,U(-t_i)U(t_j)z>
 = <z,U(t_j-t_i)z>.
```

Expanding `||v||^2` proves `(1)`.  Under `(3)` and nonnegative weights,
`A_w(q)>=eta sum_j w_j>=0`; squaring this inequality and applying `(2)` proves `(4)`.
For `q=v`, both sides of `(2)` equal `||v||^4`, proving sharpness `(2a)`.

Self-adjoint idempotence makes `Pi x` orthogonal to `q`.  Since `y=Pi x+q`, Pythagoras gives
`||y||^2=||Pi x||^2+||q||^2`, proving `(4a)`.  Bilinearity expands `||y||^2` into the displayed
normalized target Gram sum.  Substituting `(4a)` into the temporal Cauchy bound proves the product
form `(6)`.

For the projected statement, invariance of `range P` gives

```text
U(t)x-Px=U(t)(x-Px).
```

The parent two-memory collision theorem and uniform target averaging imply, independently at each
sample time,

```text
<r(t_j),q> >= |Y|^(-1)a-B=eta.
```

The preparation moment `y`, hence `q`, is fixed even though the witnessing target varies with
`j`.  Apply `(4)` and the stationary-kernel identity to obtain `(6)`.

## Conjecture--failure--survivor audit

### C0 -- monotone memory flux

`[FALSIFIED]`.  A two-dimensional rotation already makes every nonconstant alignment oscillatory;
finite static spectra recur, so no nontrivial pointwise monotone memory functional can cover the
full cycle.

### C1 -- one-time recurrence controls one-time shortcut alignment

`[BRIDGE] [INSIGNIFICANT]`.  Cauchy at one time is only
`<U(t)z,q>^2<=||z||^2||q||^2`; it contains no recurrence information beyond the diagonal.

### C2 -- many adaptive shortcuts force recurrence Gram energy

`[LEAN-PROVED]`.  Equations `(1)--(6)` survive recurrence, centralizer nonmixing, changing target
selectors, and arbitrary signed quadrature weights.  The precise positive survivor is the
stationary Gram kernel, not a monotone flux.

### C3 -- improve the quadratic loss by pure Hilbert geometry

`[FALSIFIED SHARPLY]`.  Equation `(2a)` saturates Cauchy for every weighted history.  A one-heap-
capacity Brown bound cannot come from a better universal Gram inequality.  It must exploit the
fact that physical preparation memory is generated by a bounded-dependence gate heap, rather than
an arbitrary Hilbert vector.

### C4 -- use minimum endpoint separation to recover one capacity factor

`[RETIRED AS WRONG INVARIANT]`.  A worst-pair separation bound is unnecessary and unstable under
one exceptionally close endpoint pair.  The proof exposes the exact aggregate replacement:
`F_Pi(Y)`, the centralizer-conditioned average of every target pair overlap.  Growing replicas must
control this frame energy directly.  No minimum endpoint gap is present in `(6)`.

## Scale audit and exact remaining core

The theorem is not by itself a Brown-onset estimate.  With uniform dictionary size `N`, the forced
alignment may be only `Theta(N^(-1))`; Cauchy squares that scale.  Equation `(4a)` now shows exactly
when one factor is recovered: if the return/carrier-excised occupied replica image satisfies
`F_Pi(Y)=O(N^(-1))`, then `(6)` loses only one capacity factor.  No pointwise pair-separation
estimate is needed.  Without such an aggregate frame-energy bound, claiming first onset from `(6)`
would be theatre.

Its real advance is exact: it factorizes the complete adaptive problem into two average invariants.
To obtain Brown growth one must prove, at a growing replica order and after the common
return/carrier cut, both (i) an occupied heap-image frame-energy estimate at inverse intrinsic
capacity and (ii) a quenched upper bound for the centralizer-centered recurrence energy of an
ordinary one-draw local Hamiltonian.  Minimum endpoint separation and minimum spectral-gap
anti-concentration are both retired.

## External frontier audit

- `[LITERATURE]` Positive-definiteness of unitary matrix-coefficient kernels and Gram/Cauchy energy
  inequalities are classical; no novelty is claimed for `(1)--(4)` in isolation.
- `[LITERATURE]` Haferkamp et al. prove linear growth for random circuits through accessible
  dimension, not for powers of one fixed Hamiltonian:
  <https://arxiv.org/abs/2106.05305>.
- `[LITERATURE]` Oszmaniec et al. prove saturation and recurrence for random circuits and
  stochastic local Hamiltonian evolution, not ordinary one-draw static dynamics:
  <https://arxiv.org/abs/2205.09734>.
- `[LITERATURE]` Balasubramanian et al. obtain exponential-time local minimality only under the
  Eigenstate Complexity Hypothesis: <https://arxiv.org/abs/1905.05765>.
- `[LITERATURE]` Ippoliti proves a connected spectral ramp for an engineered static geometrically
  local Hamiltonian inside a symmetry sector, but no complete circuit-shortcut law:
  <https://arxiv.org/abs/2606.30635>.
- `[LOCAL-RESEARCH]` `StaticOrbitNetBellmanLaw.lean` already formalizes why fixed-time source
  covering entropy cannot transfer random-circuit accessible-dimension proofs and identifies the
  exact Bellman survivor.  This card does not duplicate that boundary.

External priority for the adaptive centralizer-centered composition `(5)--(6)` is unverified.
Until a focused citation audit or expert review establishes otherwise, it is a candidate bridge,
not new scientific knowledge and not a manuscript headline.

## Pipeline

- [x] Stage 1 -> 2: exact proof closes.
- [x] Stage 2 -> 3: `(1)--(6)`, sharpness, frame-energy identity, and conditioned-energy
  factorization formalized and axiom-audited; replica-projector fidelity realization and automatic
  collision nonnegativity formalized separately.
- [ ] Publication use: establish application priority and close both growing-replica factors for
  ordinary static local Hamiltonians.
