# HB positive FE--Schwarz orbit symmetrization cancellation no-go

Status: failed route with positive survivor
Route: HB
Completed: 2026-08-28

## Failed conjecture

Passing from two source-faithful branches to the minimal four-sector FE--Schwarz real closure might
make the Peierls obstruction cancel automatically after orbit symmetrization.

## Exact obstruction

False. With canonical unit-carrier source normalization, all four exact global Peierls cuts add
with one sign:

`orbitTrace = -4 * normSq(mixing(q)) * (8n+5)`.

It is strictly negative off the critical wall. More generally, reflection-invariant real pair
weights `a,b` give zero exactly when `a+b=0` or the Xi copy is critical. Any positive-total-weight
average therefore retains the obstruction. The only unconditional cancellation uses opposite
pair weights and is identically blind to RH.

## Positive survivor

The four-sector orbit landing itself is now exact, automatically FE--Schwarz covariant, and an RH
receiver: universal vanishing is equivalent to RH. The complete weight classification separates
physical positive averaging from vacuous signed cancellation.

Formalized in
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFESchwarzOrbitPeierlsTrace.lean`.

## Consequence

Retire covariance-by-positive-orbit-symmetrization as a cancellation mechanism. Continue HB only
by deriving a nonzero-total-weight Ward/stationarity law from the literal action or by proving a
new physical signed character whose cancellation is not the zero-total-weight identity already
classified here.
