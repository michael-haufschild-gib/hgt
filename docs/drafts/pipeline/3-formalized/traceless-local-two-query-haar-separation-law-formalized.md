# Traceless local two-query Haar separation — formalized closure

- **ID:** `traceless-local-two-query-haar-separation-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./traceless-local-two-query-haar-separation-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean modules

Pre-existing corpus layer:

- `HTGeometry/ConservedLocalCompressionWitness`, `HTGeometry/ConservedLocalTwoQuerySignalLaw` —
  the conserved-coordinate Frobenius bound and the dimension-linear signal bound.
- `HTGeometry/ProductStabilizerPauliTwirlLaw` — the exact six-state single-qubit twirl and the
  coefficient diagonalization.
- `HTGeometry/FiniteQubitPauliBasisLaw`, `HTGeometry/TracelessLocalPauliTransferConservationLaw` —
  the literal Pauli basis of the Hermitian matrix space, the principal transfer block on the
  **nonidentity** weight-at-most-`q` dictionary, exact conservation and nonvanishing.
- `HTGeometry/FiniteUnitaryHaarMeasureLaw`, `HTGeometry/PermanentLocalityHaarSeparationLaw` —
  normalized Haar on a finite unitary group and the exact `1/(D+1)` mean square of a prepared
  coordinate state against a traceless Hermitian involution.

New in this closure:

- `HTGeometry/TracelessPauliIdentityCoordinate` (new)
- `HTGeometry/ProductStabilizerPhysicalScore` (new)
- `HTGeometry/FiniteUnitaryHaarReindex` (new)
- `HTGeometry/RankOneProjectionConjugation` (new)
- `HTGeometry/LiteralTwoQueryHaarBenchmark` (new)

All are imported by the umbrella `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

The card's own Lean plan had five steps.

### 1–2. Traceless dictionary, transfer block, conservation

`IsFiniteQTracelessPauliLabel`, `FiniteQTracelessPauliLabel`,
`finiteQTracelessPauliTransferMatrix`, `finiteQTracelessEnergyCoordinates`,
`finiteQTracelessPauliTransferMatrix_fixes_energyCoordinates` and
`finiteQTracelessEnergyCoordinates_ne_zero`.  The identity is excluded from the dictionary, as the
card's hostile audit demands.

The card's *identity-coordinate gap* is closed by
`trace_eq_pauliIdentityCoordinate_mul` — expanding a self-adjoint matrix in the Pauli basis and
tracing kills every nonidentity string, so `Tr H` is the identity Pauli coordinate times `2^n` —
and hence `hasZeroPauliIdentityCoordinate_of_trace_eq_zero`: literal tracelessness replaces the
abstract coordinate hypothesis.  `instNonemptyFiniteQTracelessPauliLabel` inhabits the dictionary
for `n ≥ 1`, `q ≥ 1`.

### 3. The boxed lower bound `(2)`

`twoQueryProductStabilizerSignal_ge` gives `3^{-q}/M` from one nonzero conserved coordinate, at
every time; `productStabilizerTwoQueryProtocolSignal_ge` states it for the operational twirl;
`finiteQTracelessAutonomousTransferSignal_ge_of_trace_eq_zero` states it for a nonzero traceless
`q`-local Hamiltonian; and `literalTwoQueryScore_ge_of_trace_eq_zero` states it for the **literal**
score.

### 4. The physical score and its transfer expansion `(5)`

- `qubitLocalTensor` with sitewise product, trace and adjoint laws.
- `stabilizerDensity u = (I + s σ_p)/2`, proved Hermitian, idempotent and of unit trace — hence a
  rank-one orthogonal projection — with the exact six-state evaluation
  `trace_stabilizerDensity_mul_boolPauliOption`.  The density-matrix route keeps `√2` out of all
  twenty-four evaluations.
- `productStabilizerDensity` and `trace_productStabilizerDensity_mul_finitePauliMatrix`: the
  product-state expectation of a Pauli string factorizes over sites.
- `conjugation_finitePauliMatrix_expansion`: `U† P U = ∑_Q T_{QP} • Q` with
  `T = pauliConjugationTransfer U`.
- `literalTwoQueryScore` — the actual experiment — and `average_sq_trace_eq_sum_twirl`, which turns
  its sample average into `∑_Q 3^{-wt Q} T_{QP}²` over the whole Pauli basis.  This is `(5)`.
- `productStabilizerTwoQueryProtocolSignal_le_literalTwoQueryScore` is the card's step `(6)`: the
  transfer signal retains only dictionary outputs and every dropped term is nonnegative.

### 5. The exact Haar value `(3)` and the capstone `(4)`

- `exists_unitary_trace_mul_eq_conj_entry` — a Hermitian idempotent of unit trace pairs with every
  observable as one diagonal entry of the observable conjugated by a fixed unitary.  Proof:
  eigenvalues of a Hermitian idempotent lie in `{0,1}`
  (`hermitianEigenvalues_sq_eq_self_of_mul_self_eq_self`) and unit trace forces exactly one of them
  to be `1` (`exists_unique_eigenvalue_one_of_isIdempotent_trace_one`).  This makes a product
  stabilizer state an admissible *preparation* for the corpus benchmark.
- `unitaryGroupReindex`, `measurePreserving_unitaryGroupReindex`,
  `integral_finiteUnitaryHaar_reindex` — normalized Haar transfers along a change of matrix index
  type.  The pushforward along a continuous surjective group hom of compact groups is a Haar
  probability measure and `Measure.haarMeasure_unique` pins it down.  mathlib has Haar invariance
  under translations but nothing that moves Haar across a reindexing.
- `haar_sq_trace_pure_state_conjugation` — on **any** finite register, the normalized Haar mean
  square of a pure-state expectation of a traceless Hermitian involution is `1/(D+1)`.
- `haar_literalTwoQueryScore_eq` — **the boxed `(3)` on the literal score**:
  `𝔼_{V∼Haar} 𝒮(V) = 1/(2^n+1)` for every nonidentity Pauli dictionary, via
  `FiniteQubitConfiguration (Fin n) ≃ Fin 2 ⊕ Fin (2^n - 2)`.
- `haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero` — **the boxed `(4)`**: whenever
  `M_q 3^q < 2^n + 1`, every nonzero traceless `q`-local autonomous evolution scores strictly above
  the Haar benchmark on the same experiment, at every real time.

## Verification

- `lake env lean` clean, no warnings, on all five new modules.
- `lake build` green on all five.
- `#print axioms` on `trace_eq_pauliIdentityCoordinate_mul`,
  `hasZeroPauliIdentityCoordinate_of_trace_eq_zero`,
  `trace_stabilizerDensity_mul_boolPauliOption`, `productStabilizerDensity_mul_self`,
  `trace_productStabilizerDensity_mul_finitePauliMatrix`,
  `conjugation_finitePauliMatrix_expansion`, `average_sq_trace_eq_sum_twirl`,
  `productStabilizerTwoQueryProtocolSignal_le_literalTwoQueryScore`,
  `literalTwoQueryScore_ge_of_trace_eq_zero`,
  `haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero`,
  `hermitianEigenvalues_sq_eq_self_of_mul_self_eq_self`,
  `exists_unique_eigenvalue_one_of_isIdempotent_trace_one`,
  `exists_unitary_trace_mul_eq_conj_entry`, `measurePreserving_unitaryGroupReindex`,
  `integral_finiteUnitaryHaar_reindex`, `haar_sq_trace_pure_state_conjugation`,
  `haar_literalTwoQueryScore_eq`: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present in `GaloisForLFunctions/HTGeometry.lean`.

## What is *not* claimed

Exactly what the card's own audit says: this is the permanent non-Haar clause only.  It proves no
complexity growth and no plateau hitting time.  The efficient-decision-rule paragraph (Chebyshev
trial count and the `M_q ≤ (4n)^q` dictionary bound) is arithmetic commentary on the boxed results,
not part of them.  No priority claim: the protocol and no-go are due to Cui–Schuster–Mao–Huang–
Brandão; this is an unconditional internal certificate.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
