# A finite-prime autonomous Hilbert--Pólya carrier has order above half the prime count

- **ID:** `finite-prime-autonomous-hp-order-floor`
- **Stage:** 2-fully-proven
- **Type:** POSITIVE COMPLEXITY LOWER BOUND / HILBERT--PÓLYA BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Let a vertically Bohr-almost-periodic cutoff carrier retain every independent
  phase `log p` for `p<=N`. If it is governed by a regular autonomous complex ADE of order `n`,
  with unique evolution on its compact jet hull, then

  ```text
  pi(N)<2n,
  n>pi(N)/2.                                                 (1)
  ```

  The same floor holds when the full prime phase module is retained by a continuous
  translation-equivariant divisor observable. A fixed-order autonomous BBM, Berry--Keating,
  Connes, de Branges, or other Hilbert--Pólya flow therefore cannot survive a cofinal prime
  exhaustion. Its differential/state order must grow at least linearly in `pi(N)`, or the
  arithmetic carrier must live in an infinite-dimensional domain, a singular constraint, or a
  nonautonomous coefficient system.

## 1. Exact hypotheses

Fix `N>=2`. Let

```text
P_N={p prime:p<=N}.                                         (2)
```

Let `f` be a nonzero holomorphic uniformly almost-periodic function on a horizontal or vertical
strip, after the harmless rotation exchanging real and imaginary translation. Assume that its
Bohr frequency group contains

```text
Gamma_N=span_Z{log p:p in P_N}.                             (3)
```

Assume also that `f` satisfies a regular autonomous complex ADE

```text
f^(n)=R(f,f',...,f^(n-1)),                                  (4)
```

where `R` is holomorphic and locally Lipschitz on a neighborhood of the compact jet hull, so the
associated first-order system has unique solutions there.

The divisor version replaces the containment `(3)` for `f` by the same containment for any
continuous translation-equivariant observable of `Div(f)`.

## 2. Proof

Unique factorization gives rational linear independence of the prime logarithms. Indeed,

```text
sum_(p in P_N) q_p log p=0, q_p in Q                       (5)
```

can be cleared of denominators and exponentiated to an equality between two positive integers
with disjoint prime valuations. Hence every coefficient is zero and

```text
rank_Q Gamma_N=#P_N=pi(N).                                  (6)
```

The autonomous ADE frequency-rank law applies to `(4)` and gives

```text
rank_Q Gamma(f)<2n.                                         (7)
```

Containment `(3)` and `(6)` imply

```text
pi(N)<=rank_Q Gamma(f)<2n,                                  (8)
```

which is `(1)`. For the divisor version, the divisor hull is a compact abelian factor of the
function hull, so its character group embeds in the function frequency group. If its observable
contains `Gamma_N`, the same chain `(8)` follows. QED.

Since `n` is integral, one may write the exact floor as

```text
n>=floor(pi(N)/2)+1.                                        (9)
```

## 3. Archimedean completion cannot pay the rank cost

The theorem `finite-archimedean-gamma-product-boundary-law.md` proves that every commensurable
finite Gamma product

```text
G(s)=exp(alpha s) product_j Gamma(lambda_j s+mu_j)          (10)
```

has a one-point upper projective boundary in `C(s)<G>`. A recurrent function DA over this field
acquires an autonomous constant-coefficient differential relation in a vertical return limit and
has finite rational phase rank.

Consequently the finite completion in `(10)` cannot supply or hide the rank in `(6)`. If a
Gamma-coefficient ADE of maximal derivative order `n` has a projective boundary relation that is
regular and uniquely solvable on the recurrent hull, then the limiting autonomous relation has
order at most `n`, so `(1)` still applies. The prime phase dimension must be transported separately
through completion.

The regularity qualification is essential. A singular implicit limit relation with nonunique
initial-value evolution lies outside Cartwright--O'Brien and is a genuine escape category.

## 4. Hilbert--Pólya interpretation

At cutoff `N`, a scalar finite-order differential operator can encode the smooth archimedean clock,
but it cannot generate all marked prime phases unless its state order obeys `(9)`. Thus a viable
cofinal operator architecture must choose one of the following positive forms.

1. **Growing differential order:** `n_N>=floor(pi(N)/2)+1`.
2. **Growing matrix/domain rank:** an equivalent first-order state system has real dimension at
   least `pi(N)+1`; the prime modes remain explicitly marked under the inclusions.
3. **Infinite-dimensional arithmetic domain:** the operator is already defined on a Hilbert or
   Krein module carrying the full prime-log character group.
4. **Constraint rather than flow:** an exact global determinant, trace formula, or boundary
   incidence transports the phase module without claiming to generate it by a finite autonomous
   evolution.
5. **Singular/nonunique category:** the limiting differential relation is implicit and singular;
   then the architecture must prove its own zero-preserving cofinal theorem.

For the Bender--Brody--Muller construction, the formal differential equation is fixed order while
the arithmetic selector sits in the boundary value `psi_z(0)=-zeta(z)`. Equation `(1)` explains
positively what a repair must do: the closed boundary/domain system, not the fixed-order dilation
flow, must carry the growing prime module.

## 5. Boundary with the logarithmic finite-prime layer

The order floor is independent of the `1/log N` horizontal boundary layer. The two obligations are
complementary:

```text
phase obligation:      carrier rank >=pi(N),
divisor obligation:    locally uniform zero-preserving convergence to Xi,
horizontal obligation: sub-log-square reflected energy on zero fibres.       (11)
```

Increasing autonomous order satisfies only the first clause. It does not by itself create finite
zeros, preserve divisor winding, or cross the reflected-energy layer. Conversely, a finite
determinant with real zeros but phase rank below `(6)` has not transported the complete finite-prime
source.

## 6. Scope and novelty

- The theorem applies only to regular autonomous ADEs, or Gamma-coefficient relations whose
  projective boundary is a regular autonomous relation of no greater order.
- It does not exclude exact global self-adjoint operators, infinite-dimensional flows, singular
  constraints, locally uniform determinant limits, or cofinal Weil positivity.
- `pi(N)` counts retained independent prime directions. A model that intentionally compresses the
  source must prove a faithful intertwining theorem before a smaller number can be called the full
  finite-prime carrier.

The proof is a direct composition of prime-log independence with the Cartwright--O'Brien frequency
rank theorem already recorded in `autonomous-ade-almost-periodic-frequency-rank.md`. The Gamma-field
interpretation uses the separate finite-product boundary law. The quantitative Hilbert--Pólya
form is operationally useful but does not clear the novelty gate.

## Gates

- [x] prime cutoff frequency rank identified exactly as `pi(N)`.
- [x] autonomous order floor proved.
- [x] divisor-observable form proved.
- [x] finite-Gamma projective boundary integrated with explicit regularity boundary.
- [x] separated from zero-preserving and logarithmic-boundary obligations.
- [ ] construct a cofinal Hilbert--Pólya domain satisfying all three obligations in `(11)`.
