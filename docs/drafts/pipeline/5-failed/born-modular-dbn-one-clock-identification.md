# Born, modular, and de Bruijn--Newman one-clock identification

- **ID:** `born-modular-dbn-one-clock-identification`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED]`, `[LARGE OUTLANDISH DETOUR]`, `[POSITIVE RIGIDITY]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/HeatFlowModularNoGo.lean`
- **Origin:** `../0-backlog/dewitt-gr-lens-conjectures.md`, Seed C

## Proposed chain

```text
completed theta source
  -> de Bruijn--Newman heat clock t
  = Tomita modular clock tau
  = Born/KMS inverse temperature beta
  -> factor-type transition at beta=1
  -> Newman threshold at t=0
  -> RH.
```

The literal identification is false.

## Three different parameter types

The corpus proves that `beta=2 Re(s)` is the inverse-temperature **label of a state** built from the
Born weights of the Dirichlet wavefunction. Tomita time `tau` is the parameter of an
**automorphism group of a fixed operator algebra and state**. De Bruijn--Newman time `t` is the
parameter of a **heat deformation of the function** whose zeros move and collide. Equality of the
three real numbers has no typed mathematical meaning by itself.

There is also a decisive algebraic obstruction. Every modular flow map is multiplicative. On the
quadratic polynomial sector, the heat flow is exactly

```text
H_t(P)=P+t P'',
H_t(X)=X,
H_t(X^2)=X^2+2t.
```

Hence `H_t(X^2)=H_t(X)^2` if and only if `t=0`. Lean formalizes this exact rigidity. Nonzero heat
time cannot be modular time even in the smallest nontrivial polynomial test algebra.

## Positive statement

The no-go does not exclude an operator-algebraic model of the de Bruijn family. It determines the
minimum shape of one:

```text
t |-> (M_t, phi_t, Xi_t)
```

must be a **covariant family of algebras or states**, with heat transport implemented by a
nonmultiplicative completely positive correspondence or cocycle between different fibers. It
cannot be the Tomita automorphism group inside one fixed fiber, and the state label `beta` cannot
be substituted for either flow parameter. A live successor must construct this family from the
theta source and prove that its factor-type wall tracks hyperbolicity of `Xi_t`; merely assigning
the same numerical coordinate restates the desired threshold.

## Two-ended verdict

The chain reaches RH at its right end only after the invalid equality of clocks. The Born/KMS
factor-type theorem already shows that reflected label matching at the zeros is equivalent to the
reflection fixing those zeros, hence is itself RH rather than a provider. The literal one-clock
detour is closed. The covariant-family replacement is a new construction problem and currently has
no source-defined bridge to the Newman constant.
