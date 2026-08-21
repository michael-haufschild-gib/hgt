# CCM wall-Gram light-cone jet pairing

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeJetPairing`.
This transports differential wall-light occurrence through literal actual-head spectral pairing.
Completed Gamma/Robin transport and the final Schur residual remain open.

## New knowledge

For a prime-power wall, write `J_n(f)` for actual chord-energy derivative paired against the
literal density `|fourierUnitary f|²`, `R_n = 4π log(n) w_n` for center-reserve rate, and
`E_n⁺(f), E_n⁻(f)` for the positive and negative Suzuki light energies with rate `8π log(n)`.
For every actual head `f`, Lean proves the complementary exact decompositions

\[
E_n^-(f)+J_n(f)=R_n\|f\|_2^2,
\qquad
E_n^+(f)-J_n(f)=R_n\|f\|_2^2.
\]

Both light energies are nonnegative. Consequently the differentiated scalar wall channel is a
sharp light-cone contraction:

\[
|J_n(f)|\le R_n\|f\|_2^2.
\]

No spectral moment or smoothness of `f` is required. The proof works for arbitrary `SoninL2`
because chord differentiation produces a bounded sine multiplier rather than a frequency factor.
For every finite labeled prime-power packet `S`, Lean also proves

\[
\left|\sum_{(p,e)\in S}J_{p,e}(f)\right|
\le
\left(\sum_{(p,e)\in S}R_{p,e}\right)\|f\|_2^2.
\]

The packet theorem retains prime and valuation-depth labels; no common-clock collapse occurs.

## Frontier consequence

The earlier center-reserve obstruction was not a missing positivity estimate. It was the shadow of
a two-sided conservation law: positive and negative Suzuki light are the two exact positive slacks
around the spectral connection on the actual chord Gram. This identifies a bounded self-adjoint
jet channel already normalized by actual-head mass. Next test is coefficient-faithful insertion of
this channel into the completed Gamma/Robin producer, where the reserve must cancel or dominate the
remaining signed Schur residual rather than be estimated separately.

## Lean audit

- scratch check: passed;
- direct leaf check: passed;
- exact leaf-module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
