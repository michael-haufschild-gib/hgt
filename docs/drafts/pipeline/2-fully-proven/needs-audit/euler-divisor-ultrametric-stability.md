# Non-Archimedean stability of the Euler-to-divisor map

- **ID:** euler-divisor-ultrametric-stability
- **Stage:** 2-fully-proven/needs-audit
- **Type:** THEOREM (paper) -- novelty audit open
- **Source:** `euler-support-transverse-divisor-rigidity.md`; user question on the global constraint
  preventing off-line zeros from entering the critical line
- **Statement:** `[PROVED HERE; CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]` The
  absolute-convergence abscissa of the logarithmic Euler discrepancy and the outer horizontal
  exponent of the nontrivial divisor difference are extended ultrapseudometrics, and the
  Euler-to-divisor map is non-expanding. The critical Euler ball of exponent `1/2` has constant
  off-line divisor; below `1/2` the entire nontrivial divisor is constant.

## Goal

Turn the relative-strip inequality into a global geometry on infinite Euler data, with no height,
zero labels, local Taylor data, or chosen deformation. The result should identify critical-line
entry as a topological event: it cannot occur along a path continuous in the natural
absolute-convergence filtration of the Euler data.

## Gates

- [x] 0 -> 1: objects, triangle laws, and source theorem identified.
- [x] 1 -> 2: complete paper proof below.
- [ ] 2 -> 3: formalize the max-triangle and non-expansion skeleton in Lean.
- [ ] 3 -> 4: primary-literature novelty audit and standalone note.

## Setup

Use the completed Euler-product class of `euler-support-transverse-divisor-rigidity.md`. For two
members `F,G`, write their logarithmic Euler discrepancy coefficients as

```text
c_(F,G)(p,k)=c_F(p,k)-c_G(p,k),
```

and define

```text
sigma_E(F,G)=inf {u:
  sum_p sum_(k>=1) |c_(F,G)(p,k)| p^(-kv)/k < infinity
  for every v>u}.
```

Let

```text
D_nt(F,G)=(div F-div G) restricted to 0<Re s<1.
```

Define the divisor exponent

```text
sigma_D(F,G) = -infinity                         if D_nt(F,G)=0,
sigma_D(F,G) = sup_(rho in supp D_nt(F,G))
                 max(Re rho,1-Re rho)            otherwise.
```

Thus, when the divisor difference is nonempty,

```text
sigma_D(F,G)=1/2+r_perp(D_nt(F,G)).
```

## Theorem

1. Both `sigma_E` and `sigma_D` are symmetric extended ultrapseudometrics in exponent form:

   ```text
   sigma_X(F,F)=-infinity,
   sigma_X(F,G)=sigma_X(G,F),
   sigma_X(F,G)<=max(sigma_X(F,H),sigma_X(H,G)),  X in {E,D}.
   ```

2. The Euler-to-divisor map is filtration-non-expanding:

   ```text
   sigma_D(F,G)<=sigma_E(F,G).                                  (NE)
   ```

3. After exponentiation, with `exp(-infinity)=0`,

   ```text
   d_E(F,G)=exp(sigma_E(F,G)),
   d_D(F,G)=exp(sigma_D(F,G))
   ```

   are extended ultrapseudometrics and `d_D<=d_E`.

4. Every `sigma_E<=1/2` equivalence class has one fixed off-critical divisor. Every
   `sigma_E<1/2` class has one fixed complete nontrivial divisor; with fixed archimedean data it
   contains only one L-function.

5. Every continuous map from a connected topological space into the separated quotient of the
   `d_E` space is constant. Hence critical-line entry is impossible along a `d_E`-continuous family.

## Paper proof

`[PROVED HERE; NOVELTY UNVERIFIED]`

Symmetry and the diagonal value of `sigma_E` are immediate. For the triangle law, coefficientwise

```text
c_(F,G)=c_(F,H)+c_(H,G).
```

If the two series on the right converge absolutely in every half-plane to the right of `u` and
`v`, their sum converges absolutely to the right of `max(u,v)`. Taking infima proves

```text
sigma_E(F,G)<=max(sigma_E(F,H),sigma_E(H,G)).                  (1)
```

For divisors,

```text
D_nt(F,G)=D_nt(F,H)+D_nt(H,G).
```

Cancellation can remove support but cannot create a point outside the union of the two supports.
Taking the supremum of `max(Re rho,1-Re rho)` proves the same max-triangle law for `sigma_D`.

The relative-strip theorem in `euler-support-transverse-divisor-rigidity.md` says that every point
`rho` of `D_nt(F,G)` obeys

```text
max(Re rho,1-Re rho)<=sigma_E(F,G).
```

Taking the supremum gives `(NE)`; the empty-divisor case is automatic. Exponentiation is monotone
and converts `max` into `max`, proving the ordinary strong triangle laws and `d_D<=d_E`.

If `sigma_E(F,G)<=1/2`, `(NE)` rules out any point of `D_nt(F,G)` with
`Re rho!=1/2`; hence the off-line divisors agree. If the inequality is strict, even a critical-line
point would have divisor exponent `1/2`, so `D_nt(F,G)=0`. The relative-strip theorem's Hadamard
clause then gives `F=G` when the conductor and gamma data are fixed.

Finally, the separated quotient of an ultrapseudometric space is an ultrametric space. Every open
ball in an ultrametric space is also closed, so its connected subsets are singletons. The continuous
image of a connected space is connected; therefore every continuous path is constant. Any family
whose divisor genuinely moves -- in particular, one in which an off-line zero enters the critical
line -- must be discontinuous in the `d_E` topology.

## Scientific meaning

The constraint is not a force acting on a zero. It is a non-Archimedean separation law between two
infinite data sets:

```text
Euler discrepancy exponent  >=  outer divisor-change exponent.
```

The critical value `1/2` is the first Euler radius at which the divisor is allowed to change at all;
above it, the excess radius is exactly the largest permitted horizontal displacement. This packages
the phase trichotomy

```text
sigma_E<1/2  : no nontrivial divisor change,
sigma_E=1/2  : line-only divisor change,
sigma_E>1/2  : |Re rho-1/2|<=sigma_E-1/2
```

as a stability theorem for the infinite Euler-to-divisor map.

## Novelty and significance audit

### Calibrations

- A finite Euler discrepancy has `sigma_E=-infinity`, so the ambient construction is only a
  pseudometric. On the fixed-archimedean completed L-function class it becomes separated: the
  subcritical rigidity theorem forces `F=G` whenever `sigma_E<1/2`, hence in particular whenever
  `d_E=0`.
- A nonzero vertical shift changes Euler coefficients at all primes. The theorem makes no claim that
  such a shift is continuous in `d_E`; continuity would require a separate absolute-convergence
  estimate and, if it held on a connected parameter interval, would force the shift to be trivial in
  the separated quotient.
- Functional-equation-preserving perturbations of Gauthier--Xarles lie outside the Euler space and
  therefore do not contradict the path-rigidity statement.

- The max-triangle for convergence abscissae is elementary Dirichlet-series theory.
- Michael Farmer's 2021 thin-prime theorem gives the qualitative `sigma_E<1/2` off-line rigidity in
  a different coefficient regime.
- The candidate new content is the combined ultrametric filtration, the non-expansion theorem
  `sigma_D<=sigma_E`, and the path-disconnectedness interpretation of zero entry.
- This remains in `needs-audit`: if the construction is already standard under another name, it must
  be downgraded to structural packaging rather than new scientific knowledge.

## Log

- 2026-07-10 -- theorem extracted and proved from the quantitative relative-strip result.
