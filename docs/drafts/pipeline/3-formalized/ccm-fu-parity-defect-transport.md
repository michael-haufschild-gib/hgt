# CCM-FU: quantitative parity-defect transport

- **Stage:** 3-formalized
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Type:** exact source energy control after sign reversal
- **Boundary:** a uniform accumulated-defect budget is not assumed or proved.

## Exact source bounds

Write the oriented retained coordinate as `A_P(R)=(-1)^card(R) F_P(R)`. Split its complete squared energy into `G_P=sum max(A_P(R),0)^2` and `D_P=sum max(-A_P(R),0)^2`, so `Q_P=G_P+D_P`. The original source has D_empty=0.

Every available prime pairs two oriented coordinates a,b and replaces them by a-b. The energy gain is -2ab. Its positive part is bounded by twice the sum of the positive-negative cross products. Cauchy-Schwarz on the complete paired label set therefore gives the general ceiling

`Q_(P union {q})-Q_P <= 2 sqrt(G_P) sqrt(D_P)`.

When the input retains the original orientation, `max(b-a,0)^2<=b^2`. Thus the defect created by its next prime is at most the removed prime-containing packet energy. The exact all-cutoff copied-packet bound transfers this to the two adjacent smaller retained sources. For the original source those smaller energies are already bounded by their unconditional quadratic diagonals. This supplies a quantitative cost for the next merger without requiring parity to persist.

For every first prime q<M, put `N=floor(M/q)` and `w=divisorPrimeClipWeight M q`. The unconditional source bound is

`D_{q}(M) <= 722 q ((1-w)N^2+w(N+1)^2)`.

For distinct primes p,q<M, first-prime contraction and the exact good/defect split give the unconditional second-step estimate

`Q_{p,q}(M) <= Q_{p}(M)+2 sqrt(Q_empty(M)) sqrt(D_{p}(M))`.

This quantifies a cost after parity has changed. A sufficient continuation through these estimates would compare that cost, and later accumulated costs, with previously released energy along a growing interleaving. The geometric bound is an upper estimate, not an identity for the actual gain; failure of this sufficient comparison need not refute an adaptive path. No such uniform comparison, two-prime original-diagonal ceiling or SD1 theorem is proved here.

## Lean certificate and verification

`RHTower.MobiusDivisorParityDefectTransport` contains three definitions and eleven public theorems. Key declarations are `mobiusDivisorParityGoodEnergy_add_defect`, `mobiusDivisorSelectionEnergy_insert_le_parity_geometric`, `mobiusDivisorParityDefectEnergy_insert_le_packet`, `mobiusDivisorParityDefectEnergy_insert_le_adjacent`, `mobiusDivisorParityDefectEnergy_singleton_le_quadratic`, and `mobiusDivisorSelectionEnergy_second_prime_le_defect`. The oriented-coordinate recurrence and original zero-defect theorem retain the exact arithmetic field.

The complete scratch proof and exact leaf check passed with `lake env lean`. The leaf is wired once in `RHTower.lean`; no full, dependency or umbrella build was run. All fourteen new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. No numerical premise or proof placeholder is used.

Global formal lint reports twelve unrelated concurrent umbrella-wiring errors: RHTower's `ThetaCuspSecondAtomAllMoments`, `ThetaCuspTwoAtomExponentialAdmission`, `ThetaCuspTwoAtomOddProfiles`, `ThetaCuspTwoAtomOddReserves`; and HTGeometry's `LogarithmicLaplaceMiddleAbsoluteBounds`, `MiddleHankelPerturbation`, `TwoAtomMiddleEntryBounds`, `TwoAtomMiddleHighEntries`, `TwoAtomMiddleLowEntries`, `TwoAtomOddAlgebra`, `TwoAtomOddHighReserve`, `TwoAtomOddLowerReserve`. It reports no error for this new CCM-FU leaf. This invocation does not establish a passing global lint gate.
