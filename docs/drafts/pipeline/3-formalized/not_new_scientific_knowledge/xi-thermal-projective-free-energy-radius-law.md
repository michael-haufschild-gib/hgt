# Xi thermal projective free-energy radius law

- **ID:** `xi-thermal-projective-free-energy-radius-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); source--temperature bridge; exact cofinal asymptotic
- **Source:** faithful Xi projective cold partition

## Theorem

Let

\[
Z_N(k)=\sum_{j<N}w_j e^{k\delta_j},
\qquad
w_j=\Re\!\left(-\frac1{(\rho_j-1/2)^2}\right)>0,
\qquad
\delta_j=\left|\Re\rho_j-\frac12\right|,
\]

with multiplicity-exact enumeration of the Xi divisor.  For every cofinal size and cooling
schedule `N(m), k(m) -> infinity`, one has

\[
\frac{\log Z_{N(m)}(k(m))}{k(m)}
\longrightarrow
\delta_*:=\sup_{\xi(\rho)=0}\left|\Re\rho-\frac12\right|.
\]

Consequently

\[
\mathrm{RH}
\iff
\frac{\log Z_{N(m)}(k(m))}{k(m)}\longrightarrow0
\]

for every, equivalently one, cofinal schedule.  More strongly, uniform boundedness is unnecessary:

\[
\mathrm{RH}
\iff
\forall\varepsilon>0,\quad
Z_{N(m)}(k(m))\le e^{\varepsilon k(m)}
\quad\text{eventually}.
\]

Thus the exact positive obligation is subexponential growth along one source-derived cofinal
thermal section.

## Proof architecture

1. Upper bound every displacement by `delta_*` and use summability of the faithful weights:
   `Z_N(k) <= Z(k) <= M exp(k delta_*)`.
2. For every `a < delta_*`, choose one multiplicity copy with `a < delta_j`.  Cofinality of `N`
   eventually includes that atom, giving `w_j exp(k delta_j) <= Z_N(k)`.
3. Divide logarithms by `k`; the fixed terms `log M / k` and `log w_j / k` vanish along every
   cooling schedule.
4. Apply the order characterization of convergence.

## Source--temperature master consequence

At the endpoint, the following form one exact equivalence chain:

1. the fixed-window prime--polar negative-source abscissa is at most one;
2. the fixed Eisenstein-at-two source-Hankel chamber is nonnegative on any infinite degree set;
3. the calibrated Hausdorff differences are nonnegative in one common cofinal quadrant;
4. one cofinal finite thermal section has zero free-energy density;
5. that section grows subexponentially;
6. one fixed upper bound recurs cofinally often;
7. the source moments have local finite KMS/Wightman closure;
8. the Connes reflection-positive Gram condition;
9. RH.

This chain is formalized in
`formal/GaloisForLFunctions/RHTower/PrimeArchCofinalSourceTemperatureMaster.lean`.

## Circularity firewall

This is an unconditional Laplace-principle theorem for the actual Xi divisor and does not estimate
`delta_*`.  It becomes an RH proof only after an independently source-derived subexponential bound
for one cofinal partition section is proved.

## Gates

- [x] exact statement and proof architecture
- [x] Xi support-radius approximation lemma
- [x] cofinal finite-partition asymptotic
- [x] RH equivalence
- [x] subexponential cofinal criterion
- [x] prime-source/Hausdorff/KMS/Connes master chain
- [x] named module and aggregate import compile
- [x] formal lint passes
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] integrate the strengthened theorem into the master paper

## Formal declarations

- `tendsto_xiThermalProjectiveColdTruncation_log_div_cold`
- `riemannHypothesis_iff_tendsto_thermalProjectiveCofinalFreeEnergy_zero`
- `riemannHypothesis_iff_thermalProjectiveCofinalSubexponential`
- `primeArchCofinalSourceTemperatureMaster`
- `primeArchCofinalSourceTemperatureSpectrum`
