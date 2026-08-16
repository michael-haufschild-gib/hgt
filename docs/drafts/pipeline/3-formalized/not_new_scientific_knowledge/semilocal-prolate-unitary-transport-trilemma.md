# Semilocal prolate unitary-transport trilemma

- **ID:** semilocal-prolate-unitary-transport-trilemma
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source input:** normalized semilocal cyclic pairs and
  `semilocal-all-even-jacobi-prolate-residue-tower.md`

## Statement

Let `P` be any finite nonempty prime set. There is no unitary

`U:H_infinity->H_P`

which simultaneously intertwines the scaling operators and the number operators:

`UD_infinity=D_PU`, `UN_infinity=N_PU`.                    (1)

There is also no unitary `U` which intertwines the source formal prolate families at two distinct
positive parameters `lambda!=mu`:

`UW_(lambda,infinity)=W_(lambda,P)U`,

`UW_(mu,infinity)=W_(mu,P)U`.                              (2)

Thus the genuine semilocal prolate family cannot be obtained by any unitary transport of the
archimedean family.

The three canonical transport choices have mutually incompatible strengths:

1. `theta_P` intertwines scaling and carries every Sonin space exactly, but is not unitary;
2. its polar unitarization is unitary, but its exact-Sonin crossing is noncompact;
3. a unitary mapping the Jacobi eigenbases intertwines the number operators, but cannot intertwine
   scaling.

## Proof

The eigenvalue-zero space of each number operator is one dimensional and spanned by the normalized
cyclic ground state `p_0=1`. If `U` intertwines the number operators, then

`Up_0^infinity=c p_0^P`

for a scalar `c` of modulus one. If it also intertwines scaling, unitarity gives

`||D_infinity p_0^infinity||^2
 =||D_Pp_0^P||^2`.

For an even cyclic pair the first Jacobi recurrence is

`Dp_0=a_0p_1`,

so this equality says

`a_0(empty)^2=a_0(P)^2`.

But the normalized semilocal contraction theorem proves

`a_0(P)^2<1/2=a_0(empty)^2`

for every finite nonempty `P`. This contradiction proves the first assertion.

For (2), subtract the two intertwining identities. Since

`W_(lambda,S)=-D_S^2+lambda^2N_S`,

and `lambda^2!=mu^2`, subtraction gives `UN_infinity=N_PU`. Inserting this back into either identity
gives `UD_infinity^2=D_P^2U`. The number-operator relation again maps the ground states, and

`<p_0,D^2p_0>=||Dp_0||^2=a_0^2`.

Unitarity therefore forces equality of the first Jacobi coefficients, contradicting strict
contraction. Hence (2) is impossible.

The three transport claims are now immediate. The source proves the scaling/Sonin properties of
`theta_P`; its Gram operator is the nontrivial Euler metric, so it is not unitary. The polar-corner
theorem proves failure modulo compacts of its unitary correction. Mapping the two number eigenbases
defines a unitary intertwining `N`, and the first part proves that it cannot also intertwine `D`.

## Route consequence

- `[CLOSED]` No unitary change of coordinates turns the archimedean prolate family into the genuine
  semilocal cyclic family.
- `[CLOSED]` The transported control cannot be promoted merely by changing its unitary gauge.
- `[PROVED]` The strict first-Jacobi contraction is an obstruction to simultaneous scaling--grading
  naturality, not just a low-mode numerical difference.
- `[OPEN CORE]` A genuine semilocal prolate realization must be constructed as a new self-adjoint
  extension of the deformed formal sum. It cannot inherit self-adjointness, Sonin reduction, and
  spectrum wholesale from the archimedean operator.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/SemilocalProlateUnitaryTransport.lean`

| Card claim | Lean declaration |
|---|---|
| a number-operator intertwiner sends the ground state to a unimodular multiple of the ground state | `exists_unimodular_of_ground_transport` |
| **(1)** a simultaneous scaling/grading unitary forces `‖D_∞ p₀‖ = ‖D_P p₀‖` | `norm_scaling_ground_eq_of_unitary_transport` |
| hence a strict first-Jacobi contraction forbids every such unitary | `not_exists_unitary_transport` |
| `W_{λ,S} = -D_S² + λ² N_S` | `prolateOp` |
| **(2)** two distinct parameters recover `U N_∞ = N_P U` and `U D_∞² = D_P² U` | `number_transport_of_two_prolate` |
| and hence the same first-Jacobi equality via `⟪p₀, D² p₀⟫ = ‖D p₀‖²` | `norm_scaling_ground_eq_of_unitary_prolate_transport` |
| the strict contraction `a_0(P)² < 1/2 = a_0(∅)²` | `semilocal_normalizedSecondMoment_lt_archimedean`, built on the corpus's `semilocalFinitePrimeNormalizedSecondMoment_lt_half` and `semilocalArchimedeanJacobiCoefficient_sq` |

The three transport alternatives listed in the card are exactly this dichotomy: `θ_P` intertwines
scaling but is not unitary (its Gram operator is the Euler metric), the Jacobi-basis unitary
intertwines `N` but then `not_exists_unitary_transport` forbids it from intertwining `D`, and the
polar unitarization is treated in the separate polar-corner card.

The `[OPEN CORE]` item (constructing a genuine semilocal prolate self-adjoint extension) is
explicitly open research.

All declarations audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

## Novelty audit

The no-go is a direct invariant consequence of unitary equivalence of cyclic pairs and the proved
first-Jacobi contraction. It sharply closes a transport shortcut but is classified as BRIDGE.
