# Theta-cusp supersymmetric Morse Born bootstrap

- **ID:** `theta-cusp-susy-morse-born-bootstrap`
- **Stage:** 3-formalized
- **Type:** `[PROVEN] [PHYSICS VALUE BRIDGE] [LEAN] [DIRECT CONSUMER]`
- **Physics source:** supersymmetric quantum-mechanical factorization, Morse-type exponential
  potentials, Witten-Laplacian boundary coercivity, and quantum-mechanical moment bootstraps.
- **Lean consumers:** `PrimeArchThetaLiouvilleWard.lean`, the all-order first-atom enclosure, and
  `forall_primeArchSourceTraceHankel_linear_nonneg_of_liouvilleWard`.

## Claim

For a real parameter `A`, positive integer atom `n`, and `x >= 0`, put

```text
t_n(x) = pi (n exp x)^2,
psi_(A,n)(x) = n exp(A x) exp(-t_n(x)/2),
W_(A,n)(x) = t_n(x) - A.
```

Then the theta-cusp Gibbs atom is the Born density of the `A=5/4` state,

```text
thetaCuspLiouvilleGibbsAtom n x = psi_(5/4,n)(x)^2,       (B)
```

and the first-order supercharge annihilates it:

```text
(d/dx + W_(A,n)) psi_(A,n) = 0.                          (S)
```

Consequently `psi_(A,n)` is a zero mode of the Morse-type supersymmetric Hamiltonian

```text
H_- = -d^2/dx^2 + V_-(A,n),
V_-(A,n) = W_(A,n)^2 - 2 t_n.
```

The partner potential is `V_+(A,n)=W_(A,n)^2+2t_n` and obeys the exact shape-invariance value

```text
V_+(A,n) = V_-(A-2,n) + 4(A-1).                         (I)
```

For `A=5/4`, the theta source atom is a positive Born observable:

```text
thetaCuspSourceTerm x n
  = 4 pi (W_(5/4,n)(x)-1/4) psi_(5/4,n)(x)^2.            (O)
```

For `n>=1` and `x>=0`, the multiplier is positive because
`W_(5/4,n)-1/4 = pi (n exp x)^2-3/2 > 0`.

On the half-line, the partner potential also has the explicit pointwise floor

```text
pi^2 - pi/2 + 25/16 <= V_+(5/4,n)(x),                  (P)
```

for `n>=1` and `x>=0`. This is a coercive potential input for a later Witten-Laplacian or mixed
quantum bootstrap argument; it is not claimed to be a spectral-gap theorem.

## Moment consequence

Define the quantum Born observable moments

```text
M_j(n) = 4 integral_(0,infinity)
  x^(2j) (W_(5/4,n)(x)-1/4) psi_(5/4,n)(x)^2 dx.
```

Equation `(O)` gives the exact value relation

```text
thetaCuspAtomRawEvenMoment j n = 2 pi M_j(n).            (M)
```

For the first atom, the already-formalized Ward normalization therefore satisfies

```text
thetaCuspFirstAtomWardMoment j = M_j(1).                 (U)
```

Thus the two remaining first-atom hypotheses become moment inequalities for one explicit positive
observable in one exact zero-energy Morse state. This is the correct input form for the
coordinate/momentum Gram matrices and commutator recurrences of the quantum-mechanical bootstrap.

## Direct corpus application

The target consumer takes only

```text
14 ((3005/2997) M_2(1))^2 <= 9 M_1(1) M_3(1),
16 ((3005/2997) M_0(1)) ((3005/2997) M_2(1)) <= 45 M_1(1)^2
```

and returns every linear-polynomial prime--Gamma source Hankel inequality. No source comparison,
KMS realization, Xi zero data, or separate transition-weight positivity is introduced.

The existing all-order first-atom enclosure also transports without new assumptions:

```text
2 pi M_j(1) <= thetaCuspRawEvenMoment j
thetaCuspRawEvenMoment j <= (3005/2997) (2 pi M_j(1)).
```

Thus all current consumers of the raw theta moments can use the Morse Born variables, not only the
final linear Hankel criterion.

## Formalization

Implemented in `formal/GaloisForLFunctions/RHTower/PrimeArchThetaMorseGroundState.lean`.
Principal declarations:

- `hasDerivAt_thetaCuspMorseZeroMode`
- `thetaCuspMorseZeroMode_schrodinger_zero`
- `thetaCuspMorse_shapeInvariant`
- `thetaCuspMorsePotentialPlus_floor`
- `thetaCuspMorseGroundState_sq`
- `thetaCuspSourceTerm_eq_morseBornObservable`
- `thetaCuspMorseBornMoment_nonneg`
- `thetaCuspAtomRawEvenMoment_eq_morseBornMoment`
- `thetaCuspFirstAtomWardMoment_eq_morseBornMoment`
- `thetaCuspRawEvenMoment_between_morseBornMoment`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_morseBorn`

## Physics references

- Socorro--Reyes--Villaseñor Mora, *Supersymmetric Quantum Mechanics: two factorization schemes,
  and quasi-exactly solvable potentials*, <https://arxiv.org/abs/1902.01782>.
- Han--Hartnoll--Kruthoff, *Bootstrapping Matrix Quantum Mechanics*,
  <https://arxiv.org/abs/2004.10212>.
- Hu, *Different Bootstrap Matrices in Many QM Systems*,
  <https://arxiv.org/abs/2206.00767>.
- Le Peutrec, *On Witten Laplacians and Brascamp--Lieb's inequality on manifolds with boundary*,
  <https://arxiv.org/abs/1607.08714>.

The physics literature supplies the factorization and bootstrap mechanisms. The Lean module proves
every project-specific value relation `(B)`--`(U)` and the potential floor `(P)` directly.

## Attack

- Generic position-moment positivity gives only `M_2^2 <= M_1 M_3`, short of the buffered
  coefficient in the first open inequality.
- Generic KMS or reflection positivity therefore does not close the certificate.
- The useful residue is the exact supercharge and partner potential: mixed position--momentum
  bootstrap matrices and boundary Witten-Laplacian estimates can use more than ordinary moment
  positivity.
- The formalized `(B)`--`(U)` identities and direct Hankel consumer clear the utility gate; no
  spectral-gap or Brascamp--Lieb hypothesis has been introduced.

## Gates

- [x] live-corpus duplicate and failed-route check
- [x] primary physics mechanism identified
- [x] direct existing Lean consumer identified
- [x] formalize the supercharge annihilation and zero-mode Schrödinger equation
- [x] formalize the partner potential and shape-invariance identity
- [x] formalize the half-line partner-potential floor
- [x] formalize the Born-density and positive-observable source identities
- [x] formalize the Born-moment equality and first-atom Ward identification
- [x] transport the all-order first-atom enclosure to Born moments
- [x] connect the Born inequalities directly to the existing Hankel consumer
- [ ] derive a non-target-fed mixed quantum-bootstrap inequality stronger than ordinary Hankel PSD
- [ ] prove the two buffered Born-moment inequalities
- [ ] RH
