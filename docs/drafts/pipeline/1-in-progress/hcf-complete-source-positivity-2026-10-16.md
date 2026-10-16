# HCF complete source positivity

Status: investigation. Requested target remains open.

## Exact target

Prove nonnegativity of the complete actual heat Hankel form for every polynomial
at positive heat time, equivalently positivity of every actual leading heat
Hankel determinant. The existing `XiGaussianHeatRouteCapstone` proves that
this is RH-strength. No new equivalence, receiver, conditional theorem or
estimate will count as completion.

## Starting evidence

The new regular-head kernels reproduce the exact signed moment form and split
into mutually orthogonal block projections. This retains every negative
direction; idempotence alone supplies no sign. The existing source endpoint
rigidity preserves the preceding positive head at a first contact but leaves
the new pivot's sign unresolved.

## Attack ledger

1. **Signed projections select the positive branch.** Not established.
   `XiGaussianHeatRegularKernelProjections` reproduces the signed form; its
   idempotence identities do not assert positive block couplings. On the
   completed arithmetic source, `CHMDContinuousOrbitProjection` gives the exact
   nonreal-orbit energy `4 * cardinalPositiveMass a * (re(sample)^2 - im(sample)^2)`.
   A positive Hilbert-space projection argument cannot be applied to these
   signed projections.
2. **Heat flow and positive initial windows prevent first contact.** Not
   established. `XiGaussianHeatEndpointRigidity.heatMoment_head_posDef_at_endpoint`
   preserves rank `n` from positivity at rank `n+1`. It does not preserve the
   terminal rank. `XiGaussianHeatFirstContact` retains the contact branch and
   gives earlier contacts at successor ranks; decreasing contact times can
   approach zero, where these positive-time analytic statements do not apply.
3. **The prime-chain factorization pays the negative mass.** Not established.
   `CHMDPrimeChainSourceFactorization.doob_source_eq_chain_variances_sub_cosh`
   retains the complete cosh subtraction. Nonnegativity, and even trivial
   nullspace, of the crossing energy do not compare its size with that mass.
4. **The new self-adjoint arithmetic generator proves the required sign.** The
   actual conclusion in `CHMDStationaryGenerators.arithmeticGenerator_nonneg`
   concerns jump energy only. `CHMDPolarTransfer.weilForm_eq_edge_sub_polar`
   still subtracts polar energy. Its comparison theorem explicitly assumes RH.
5. **Theta null functions exhaust the troublesome source directions.** The
   exact nullspace description in `CHMDFullSpectralNullspace` leaves the
   zero-sample quotient. `CHMDContinuousOrbitProjection` retains the individual
   signed zero-orbit blocks in that quotient. No exhaustion argument removing
   their negative directions was obtained.
6. **A scalar ground-state change makes the folded odd source positive.** This
   particular mechanism is ruled out by
   `CHMDReflectedPrimeSingularPart.negative_component_survives_positive_gauge`.
   The positive survivor is already formalized: retaining the collar
   compensation gives the exact positive crossing source and the complete
   prime-chain variance decomposition. The cosh mass remains unpaid. This does
   not rule out a nonlocal factorization of the complete form.
7. **Heat-slice positivity transfers to the undeformed source.** No such
   transfer was obtained. `XiSliceHeatLargeHeightPositivity` gives all-order
   positivity only at sufficiently large heights for positive deformation.
   `XiSliceHeatTransferPositivity.kernelSliceMoment_heat_nonneg` at arbitrary
   heights has a zero-strip premise. Neither statement supplies the missing
   zero-deformation, all-height conclusion.
8. **Even-sector purification supplies a sign.** `EvenSectorWindowPurification`
   preserves the complete source profile and energy. It does not improve the
   sign. `WeilCutEvenMeanZeroDeficit` assumes odd Weil positivity and leaves a
   negative cut contribution; its cut-elimination conclusion also needs
   even mean-zero positivity. Those premises were not discharged.

## Remaining source statement

The exact completed-source identity is

`weilForm p = ‖p.val.snd‖ ^ 2 - polarEnergy p.val.fst`.

The missing inequality is

`∀ p : SourceGraph, polarEnergy p.val.fst ≤ ‖p.val.snd‖ ^ 2`.

The available theorem
`CHMDPolar.polarEnergy_le_edge_of_riemannHypothesis` has an explicit RH premise.
Replacing that premise with an unconditional proof remains unfinished. The
equivalent HCF target in the first section has not been proved either.

## Validation status

Corpus searches used the documented research command, including whole-RHTower
and HTGeometry deep searches and a CHMD lexical search. Candidate statements
were checked against Lean source. No web search or numerical experiment was
used. No new Lean theorem or umbrella import has been added in this attempt.
Direct Lean declaration and axiom audit is pending.

No claim of complete positivity is made. Only a dependency-closed unconditional
proof, checked directly in Lean with standard axioms, can close this card.
