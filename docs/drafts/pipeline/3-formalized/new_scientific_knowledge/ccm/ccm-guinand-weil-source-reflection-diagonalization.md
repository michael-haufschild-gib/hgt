# CCM Guinand--Weil source-reflection diagonalization

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / finite Guinand--Weil source dictionary
- **Novelty scope:** corpus-new structural decomposition and obstruction; trigonometric identities
  and divided differences are classical
- **External priority:** targeted primary-source and corpus search found no statement of the matrix
  decomposition or its CCM four-unit consequence; priority remains unverified
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilSourceReflection.lean`

## Exact theorem

For horizon `omega`, integral Fourier mode `n`, event source

```text
b_omega(n) = sin(2*pi*omega*n)/pi
```

and diagonal derivative

```text
d_omega(n) = 2*omega*cos(2*pi*omega*n),
```

let `Q_omega` be the finite divided-difference matrix with off-diagonal entry

```text
(b_omega(m)-b_omega(n))/(m-n).
```

Source reflection `omega |-> 1-omega` obeys

```text
b_(1-omega)(n) = -b_omega(n),
cos(2*pi*(1-omega)*n) = cos(2*pi*omega*n).
```

Therefore, entrywise and without any assumption on `omega`,

```text
Q_omega + Q_(1-omega)
  = 2*Diag_n(cos(2*pi*omega*n)).                         (1)
```

Equation (1) says that the source-reflection-even sector is exactly diagonal. Every off-diagonal
source incidence is reflection-odd.

For arbitrary finite signed event weights `alpha_r` and horizons `omega_r`, Lean also proves

```text
sum_r alpha_r*(Q_(omega_r)+Q_(1-omega_r))
  = 2*Diag_n(sum_r alpha_r*cos(2*pi*omega_r*n)).          (2)
```

At mode zero, (2) is `2*sum_r alpha_r`. In particular, total event weight `2` produces the central
value `4`, independently of all event horizons.

## Sharp obstruction

Central four-unit mass is not positive orientation. At half horizon and mode one,

```text
(Q_(1/2)+Q_(1-1/2))(1,1) = 2*cos(pi) = -2.              (3)
```

Lean derives from (3) that every finite mode carrier containing mode one makes this reflected event
matrix non-positive-semidefinite. Thus positive central value `2` and negative first-mode value `-2`
coexist in one exact event pair; doubling gives `4` and `-4`.

This closes these CCM-FU subclasses:

- eventwise positive reflected Gamma/pole blocks;
- diagonal repair inferred from source reflection alone;
- any orientation argument using only central four-unit saturation;
- scalarization of the event packet before controlling its reflection-odd sector.

## Higher principle and surviving frontier

The exact decomposition

```text
Q_omega
  = (Q_omega+Q_(1-omega))/2
    +(Q_omega-Q_(1-omega))/2
```

separates central normalization from source orientation. Scalar, radial, source-blind, and
fixed-compact failures all discard or average the second summand before it has been oriented.

The surviving producer must be non-atomwise: assemble distinct prime, pole, and archimedean events,
transport their reflection-odd sector through the source-defined all-jet physical horizon, and prove
a cofinal Schur-complement or equivalent positivity law against the completed diagonal sector. Any
proposal decomposing into positive single-event reflected blocks is falsified by (3) before a limit.

This theorem does not prove that the completed arithmetic packet has the required cross-event law,
does not construct canonical `Pi(lambda,k)`, and does not prove RH.

## Lean declarations

- `ccmGuinandWeilEventSource_one_sub`
- `ccmGuinandWeilEventCos_one_sub`
- `ccmGuinandWeilEventDiagonal_add_one_sub`
- `ccmGuinandWeilEventMatrix_add_reflected`
- `ccmGuinandWeilEventMatrix_reflection_even_part`
- `ccmGuinandWeilReflectedEventPacketMatrix_eq_diagonal`
- `ccmGuinandWeilReflectedEventPacketMatrix_zero_mode`
- `ccmGuinandWeilReflectedEventPacketMatrix_central_four`
- `ccmGuinandWeilEventMatrix_half_diagonal_at_one`
- `ccmGuinandWeilEventMatrix_half_not_posSemidef`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilSourceReflection` both pass. `#print axioms` reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`,
`opaque`, or `unsafe` declaration is used.
