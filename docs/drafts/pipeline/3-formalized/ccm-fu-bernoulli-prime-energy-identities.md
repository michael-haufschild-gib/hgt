# CCM-FU: exact half-probability prime energy and source mean

- **Stage:** 3-formalized
- **Type:** unconditional finite source identities and lower bound
- **Source:** [PE5 arithmetic investigation](../5-failed/ccm-fu-bernoulli-prime-energy.md)
- **Boundary:** the all-scale analytic obstruction, adaptive PE4, SD1 and RH are not proved by these identities.

## Exact positive survivor

For every finite source with labels `a(i)` inside a fixed finite coordinate packet U, group source coefficients by `a(i)\P`, the coordinates remaining after processing P. Every grouping preserves the complete signed sum. Inserting a coordinate p gives exactly the signed two-fibre merger: a fibre containing p disappears, while a p-free fibre receives itself plus the fibre with p inserted.

Two source indices meet in one retained fibre precisely when P contains their symmetric difference. Uniform averaging over all subsets P therefore gives

`mean_P energy(P)=sum_(i,j) c(i)c(j)/2^|a(i) triangle a(j)|`.

The mean empty-cofactor source is exactly `sum_i c(i)/2^|a(i)|`. Its square is bounded by the averaged energy. The proof retains the exact variance gap `mean(f²)-mean(f)²=mean((f-mean(f))²)>=0`. Injective labels at empty selection give the original diagonal; full selection gives the complete signed square.

`UniformPrimeSubsetEnergy.lean` proves all these assertions for arbitrary finite labelled real sources. `MobiusDivisorBernoulliPrimeEnergy.lean` supplies the actual Möbius–divisor channels, squarefree source indices and prime-factor labels. It proves that nonsquarefree and terminal source channels vanish, so both endpoint identities use exactly the original sums over `1<=d<=M`. Its merger and conservation laws hold at every processed subset.

The actual mean has the exact arithmetic form

`H_(1/2)(M)=sum_(d<=M) mu(d)K_d(M)/2^omega(d)`
`=sum_(k<M)(sqrt(k+1)-sqrt(k)) sum_(d<=k) [mu(d)/2^omega(d)] D(floor(k/d))`.

This is a changed arithmetic coefficient before the divisor convolution, rather than an extra positivity premise. The source inequality `H_(1/2)(M)^2<=E_(1/2)(M)` is unconditional for every M. It is the lower bound used by PE5's separate obstruction investigation.

## Lean audit

Both new leaves passed `lake env lean <file> -o <exact corresponding olean>` after scratch checking. Twelve generic and eight actual-source public theorems were axiom-audited once from a temporary import: only `propext`, `Classical.choice`, and `Quot.sound`. No numerical result, added axiom or unproved analytic premise enters these proofs. Both modules are wired once into `RHTower.lean`; no umbrella or dependency build was run. The declaration index was refreshed. Global formal lint was run once: its ten errors concern concurrently added, unwired `HTGeometry.PolynomialODEOddCompact*` modules; neither new CCM-FU module is flagged.

Principal actual-source declarations: `mobiusDivisorSelectionFibre_insert`, `mobiusDivisorSelectionFibre_sum`, `mobiusDivisorSelectionEnergy_empty`, `mobiusDivisorSelectionEnergy_full`, `mobiusDivisorHalfSelectionHead_eq_mean`, `mobiusDivisorHalfSelectionHead_sq_le_energy`, `mobiusDivisorHalfSelectionEnergy_eq_kernel`, and `mobiusDivisorHalfSelectionHead_eq_divisor_abel`.

The numerical cutoff1024 excess and the pole-based paper no-go have their own statuses on the linked PE5 card. They are not included in this formal certificate.
