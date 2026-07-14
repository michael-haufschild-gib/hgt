# Theta-cusp anomalous Darboux value law

- **ID:** `theta-cusp-anomalous-darboux-value-law`
- **Stage:** 3-formalized
- **Type:** `[PROVEN] [PHYSICS VALUE BRIDGE] [LEAN] [DIRECT CONSUMER]`
- **Physics source:** supersymmetric factorization, ground-state/Doob transforms, and the anomalous
  half-line quantum-mechanical bootstrap.
- **Lean source:** `PrimeArchThetaMorseAnomalousDarboux.lean`.

## Claim

For the Morse zero mode `psi = thetaCuspMorseZeroMode A n`, superpotential `W`, and lower
Hamiltonian

```text
H_- f = -f'' + (W^2 - 2 t_n) f,
```

the polynomial-dressed state `P psi` obeys the exact Darboux/Doob value law

```text
H_-(P psi) = (-P'' + 2 W P') psi.                       (D)
```

At the half-line boundary, the undressed state has Robin value

```text
psi'(0) + W(0) psi(0) = 0,
```

whereas the dressed state has the exact domain defect

```text
(P psi)'(0) + W(0) (P psi)(0) = P'(0) psi(0).           (A)
```

Thus the dressing preserves the Morse Robin domain exactly when `P'(0)=0`.  For the monomial
`P=X^k`, the boundary anomaly vanishes except at `k=1`; this is the Kronecker contact term in the
half-line hypervirial recursion.

## Direct theta-source application

At `A=5/4`, write `q=W-1/4`, `psi=thetaCuspMorseGroundState`, and `k=2j+1`.  The already-proved
Born identity and `(D)` imply the pointwise Hamiltonian decomposition

```text
x^(2j) thetaCuspSourceTerm x n
  = pi * ((2/k) psi H_-(x^k psi)
      + 4j x^(2j-1) psi^2 - x^(2j) psi^2),              (B_j)
```

with the middle term interpreted separately at `j=0`.  After half-line integration, `(A)` supplies
the zeroth boundary charge and all positive orders are anomaly-free.  This recovers the existing
Ward moments as Hamiltonian matrix values and makes mixed position--Hamiltonian Gram constraints
available without inventing a self-adjoint momentum operator on the half-line.

## Why this is useful

- It replaces informal commutator equations by the correct boundary-sensitive identity.
- It classifies exactly which polynomial test vectors remain in the Robin Hamiltonian domain.
- It gives an all-order source-to-Hamiltonian value relation for the existing Born moments.
- It supplies the operator ordering needed for a mixed quantum bootstrap aimed at the two buffered
  Born-moment inequalities.

This is a physics bridge and corpus strengthening.  It does not by itself prove the buffered moment
inequalities or RH.

## Formalization

The Lean module proves the full polynomial law, not only the displayed monomial cases:

- `thetaCuspMorse_supercharge_dressedPolynomial` proves `Q(P psi)=P' psi` pointwise;
- `thetaCuspMorse_robinDefect_eq_zero_iff` proves the exact Robin-domain classification for
  positive atom number;
- `thetaCuspMorseHamiltonianMinus_dressedPolynomial` proves `(D)`;
- `thetaCuspMorseMomentTestPolynomial_robinDefect` isolates the unique `j=0` contact anomaly in the
  normalized odd-monomial moment family;
- `pow_mul_thetaCuspSourceTerm_eq_morseHamiltonianWard` proves `(B_j)` pointwise;
- `thetaCuspAtomRawEvenMoment_eq_morseHamiltonianWard` and
  `thetaCuspMorseBornMoment_eq_morseHamiltonianWard` identify the existing atom and Born moments
  with the integrated Hamiltonian Ward density;
- `thetaCuspRawEvenMoment_eq_tsum_morseHamiltonianWard` transports the relation through the
  existing atom decomposition to every full theta-cusp raw even moment;
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_morseHamiltonianWard` rewrites the two open
  first-atom inequalities directly into the existing linear prime-archimedean Hankel consumer.

The principal declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Physics references

- Berenstein--Hulsey, *Anomalous Bootstrap on the half line*,
  <https://arxiv.org/abs/2206.01765>.
- Berenstein--Hulsey, *One-dimensional reflection in the quantum mechanical bootstrap*,
  <https://arxiv.org/abs/2307.11724>.
- Cooper--Khare--Sukhatme, *Supersymmetry and Quantum Mechanics*,
  <https://arxiv.org/abs/hep-th/9405029>.

The literature supplies the anomaly and factorization mechanisms.  Every theta-specific value
identity above must be proved directly in Lean.

## Gates

- [x] current formal and failed-route corpus checked
- [x] primary half-line quantum-bootstrap source identified
- [x] exact existing theta-source consumer identified
- [x] formalize polynomial dressing and the supercharge derivative law
- [x] formalize the Robin-domain defect `(A)`
- [x] formalize the second-order Darboux/Doob law `(D)`
- [x] specialize `(D)` to monomials and isolate the `k=1` boundary anomaly
- [x] formalize the source Hamiltonian decomposition `(B_j)`
- [x] connect the decomposition to the existing Born-moment/Hankel surface
- [ ] derive a non-target-fed mixed Gram inequality closing either buffered Born inequality
- [ ] RH
