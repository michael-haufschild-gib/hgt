# The CCM diagonal Fock coordinate is an exact polar--prime Mellin colligation

- **ID:** `ccm-diagonal-fock-polar-prime-mellin-incidence-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT TARGET]`
- **Parents:** `ccm-safe-kernel-diagonal-fock-lift-rh-law.md` and
  `ccm-polar-prime-critical-mellin-defect-law.md`

## Statement

For `x,y>1/2`, put `s=x+y` and define

```text
C(x,y)=1/s,                                                (1)
E(x,y)=-zeta'(1+s)/zeta(1+s)
      =sum_(n>=2) Lambda(n)n^(-1-s),                       (2)
B(x,y)=1/(s+1).                                           (3)
```

Let

```text
A_0(h)=sum_(n<=exp(h)) Lambda(n)n^(-1/2),
R(h)=4sinh(h/2)-A_0(h),                                   (4)
M(x,y)=integral_0^infinity exp(-(s+1/2)h)dR(h).            (5)
```

Then

```text
C=E-B+M.                                                  (6)
```

The kernels `C`, `E`, and `B` are positive semidefinite.  The kernel `M` is the exact signed
critical Mellin-defect channel.  Thus the universal Cauchy/Laplace coordinate in the canonical CCM
diagonal Fock lift is not external to the arithmetic source: it is the signed colligation of the
positive prime-power channel, a positive shifted polar channel, and the finite-aperture critical
Mellin defect.

## Proof of the incidence identity

The polar--prime defect card proves, for `Re z>1/2`,

```text
integral_0^infinity exp(-zh)dR(h)
 =1/(z-1/2)+1/(z+1/2)+zeta'(z+1/2)/zeta(z+1/2).           (7)
```

Set `z=s+1/2`.  Since `s>1`, all terms converge absolutely, and `(7)` becomes

```text
M(x,y)
 =1/s+1/(s+1)+zeta'(1+s)/zeta(1+s)
 =C(x,y)+B(x,y)-E(x,y).                                  (8)
```

Rearranging gives `(6)`.

Positivity has source-explicit feature realizations:

```text
C(x,y)=integral_0^infinity exp(-xh)exp(-yh)dh,             (9)

E(x,y)=sum_(n>=2)
  [sqrt(Lambda(n)/n)n^(-x)]
  [sqrt(Lambda(n)/n)n^(-y)],                              (10)

B(x,y)=integral_0^infinity
  exp(-(x+1/2)h)exp(-(y+1/2)h)dh.                         (11)
```

The signed measure `dR` has exponentially finite total variation on this domain.  With
`dR=sigma_R d|R|`, `(5)` is the Krein Gram

```text
M(x,y)=integral_0^infinity
  exp(-(x+1/4)h) sigma_R(h) exp(-(y+1/4)h)d|R|(h).         (12)
```

This proves the complete channel decomposition. `QED`

## Tensoring with the safe completed source

Let

```text
A(x,y)=[Q(x)+Q(y)]/(x+y-1)                                (13)
```

be the unconditional safe completed kernel, and let `H_A` have kernel vectors `k_x`.  Define the
free algebraic kernel core `F_0` to consist of finite coefficient packets on the symbols `k_x`,
equipped with the semidefinite input form having Gram kernel `A`.  On `F_0`, define the three
source-resolved diagonal graph relations by

```text
T_E k_x=k_x tensor (sqrt(Lambda(n)/n)n^(-x))_(n>=2),       (14)
T_B k_x=k_x tensor (h |-> exp(-(x+1/2)h)),                 (15)
T_R k_x=k_x tensor (h |-> exp(-(x+1/4)h)).                 (16)
```

The last target carries the fundamental symmetry `sigma_R`.  The word "relation" is essential:
an individual channel need not descend through every zero-norm relation of `A`.  If

```text
T_0 k_x=k_x tensor (h |-> exp(-xh)),                       (17)
```

then the Schur-product identity `(6)` gives, for every finite coefficient packet `v in F_0`,

```text
||T_0 v||^2
 =||T_E v||^2-||T_B v||^2+[T_R v,T_R v]_R.                (18)
```

Consequently the canonical contraction criterion is exactly

```text
RH
iff ||v||_A^2+||T_B v||^2
      >=||T_E v||^2+[T_R v,T_R v]_R
    for every finite packet v in F_0.                     (19)
```

Indeed the difference of the two sides of `(19)` is

```text
||v||_A^2-||T_0v||^2,
```

whose Gram kernel is `J_RH` by the diagonal Fock theorem.

## Positive CCM carrier law

Equation `(19)` identifies the exact source-built passivity theorem that a successful CCM proof is
forced to establish.  Under `(19)`, the combined diagonal relation respects the nullspace of `A`
and descends to the contractive operator `T_0` on `H_A`; no separate descent of the three signed
source channels is asserted.  The four channels are

```text
input:        safe completed RKHS H_A;
positive in: shifted polar Laplace channel T_B;
positive out: resolved von-Mangoldt prime-power channel T_E;
signed out:   critical Mellin-defect channel T_R.          (20)
```

The signed channel is not optional bookkeeping.  Its cumulative measure is the same
finite-aperture invariant whose endpoint value is the polar--prime critical Mellin error and whose
Laplace transform contains the zeta logarithmic derivative.  Hence `(19)` keeps the required
source--divisor incidence that is lost by replacing the primes with their main term.

The line-211 positive-transport theorem and its finite-packet strengthening determine the domain
of this colligation.  No uniformly finite rational cancellation realizes `(14)`--`(18)` in the
uncoupled prime Hilbert space.  The formal Gamma-damped carrier transition supplies the required
inverse-prime order and shows that the source channels can be placed in a common finite-Cauchy
domain before the relative/Krein completion is taken.

## Relation to the closed completed-source graph

The feature in `(17)` is source-selected independently of the present algebra.  In the canonical
closed completed-logarithmic-source graph, an upper-half-plane pole `w` contributes the anti-causal
Cauchy residue vector `(u-w)^(-1)`.  Under reflected Paley--Wiener transformation, the imaginary
family `w=i x` becomes `exp(-xt)`, up to the fixed unitary normalization.  Hence `T_0` is the
normalized diagonal bundle of the graph's
orbit-sensitive residue coordinates.

The missing incidence map is therefore narrower than constructing a new source graph: one must
show that its distinguished Sonin compression sends this residue bundle to the polar, prime, and
critical-defect relations `(14)`--`(16)` with the signs in `(18)` and with cofinal index preserved.

## Route consequence

The open analytic problem is no longer to guess the missing `L2(R_+)` feature.  It is to derive the
colligation `(14)`--`(16)` from the actual Gauss-paired Hardy--Titchmarsh/Sonin operator and prove
its passivity `(19)` cofinally.  Equivalently, one must construct a source-selected relative trace
in which the polar, prime, Gamma, and critical-error channels retain the exact signs in `(18)`.

This is still RH-equivalent.  The identity does not prove the inequality.

## Scope and classification

The theorem is a direct substitution into the already proved polar--prime Laplace identity,
followed by standard Hilbert/Krein feature calculus.  It is a route bridge, not new scientific
knowledge.  The infinite Laplace identity `(7)` is paper-proved but not yet formalized; formalizing
only the algebraic rearrangement would be wrapper work, so no new Lean file is added.

## Gates

- [x] universal diagonal Fock coordinate decomposed into exact source channels
- [x] positive prime and shifted-polar features constructed
- [x] critical Mellin defect isolated as the unique signed channel
- [x] RH rewritten as source-resolved four-channel passivity
- [x] formal line-211 topology obligation attached
- [x] diagonal Fock leg identified with the closed source graph's residue bundle
- [ ] derive the colligation from the genuine Gauss-paired/Sonin source operator
- [ ] prove cofinal passivity `(19)`
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "no new Lean file is added" decision recorded above.  The infinite
Laplace identity `(7)` remains a cited parent, but the card's own channel constructions and the
passivity rewriting are reachable and are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCMDiagonalFockColligation.lean`
(7 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `cauchy_channel_eq` — **equation (9)**: `C(x,y) = ∫_0^∞ e^{-xh}e^{-yh}dh = 1/(x+y)`.
- `polar_channel_eq` — **equation (11)**: `B(x,y) = ∫_0^∞ e^{-(x+1/2)h}e^{-(y+1/2)h}dh = 1/(s+1)`.
  Both reuse the corpus ray integral `RHTower.integral_exp_ray`
  (`CCMHalfUnitCauchySeam.lean`, card `ccm-half-unit-cauchy-seam`), not rebuilt here.
- `prime_feature_mul` — **equation (10), termwise**: the von Mangoldt feature multiplies to
  `(Λ(n)/n) n^{-(x+y)}`, exhibiting `E` as an explicit positive Gram.
- `colligation_rearrange`, `colligation_rearrange'` — **equations (8) → (6)**: the exact incidence
  rearrangement `M = C + B − E ⟺ C = E − B + M`.
- `quadratic_colligation` — **equation (18)**: the kernel colligation passes to every finite
  quadratic form, so the four channel energies satisfy the same signed identity.
- `passivity_iff` — **equation (19)**: under that identity, the contraction criterion
  `‖v‖²_A − ‖T₀v‖² ≥ 0` is exactly the four-channel passivity inequality
  `‖T_E v‖² + [T_R v, T_R v]_R ≤ ‖v‖²_A + ‖T_B v‖²`.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the Laplace–Stieltjes identity `(7)` of `ccm-polar-prime-critical-mellin-defect-law`;
- the Krein Gram representation `(12)` of the signed defect channel;
- the safe completed RKHS `H_A` and the diagonal Fock theorem identifying the difference kernel
  with `J_RH`;
- the reflected Paley–Wiener identification of `T₀` with the residue bundle of the closed source
  graph.
