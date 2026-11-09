# Odd-relation cycle spectrum controls annihilator mass

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Obstacles:** B13, B112; simultaneous positive annihilation.
- **Statement:** For odd `q>=3`, ordinates with `sum gamma_j=0`, and joint evaluation accuracy `epsilon`, `cos(pi/q) H >= 1-epsilon`. This is sharp over all such ordinate lists, at every real abscissa and every `epsilon` in `[0,1]`.
- **Novelty:** The cycle spectral certificate gives the optimal obstruction for arbitrary odd additive relations. It improves the telescoping mass bound and extends the sharp first/fourth-harmonic law to every odd relation length.

- **Extremizers:** Write `q=2r+1`, use `q-1` copies of `gamma` and one copy of `-(q-1)gamma`, with `gamma=2pi/(q log 2)`. The polynomial is `1+a(X_beta^r+X_beta^(r+1))`, where `a=(1-epsilon)/(2cos(pi/q))` and `X_beta` is the scaled two-monomial.

## Proof

Put `c=cos(pi/q)`. For every residue `k`, oddness gives
`cos(2pi k/q)>=-c`: fold `k` to `min(k,q-k)`, whose doubled value is at most `q-1`, then use cosine monotonicity on `[0,pi]`.
The discrete Fourier transform sends `f(j+1)+f(j)` to
`(1+exp(2pi i k/q)) F(k)`. Parseval therefore gives
`sum abs(f(j+1)+f(j))^2 >= 2(1-c) sum abs(f(j))^2`.

For unit phases `u_j` with product one, let `f(j)` be their successive partial products. The product constraint closes the cycle, all `abs(f(j))=1`, and each edge energy is `abs(1+u_j)^2`. Thus `sum Re u_j>=-q c`.
Apply this to each supported monomial at the zero-sum ordinate list and integrate its positive coefficient weight. Since `Re P_j=1+sum_d w_d Re u_jd`, the result is `sum_j Re P_j>=q(1-cH)`. Joint accuracy gives `sum_j Re P_j<=q epsilon`; division by positive `q` proves the bound.

For the proposed extremizer, `q=2r+1` with `r>=1` and `c>0`. Set `u=exp(-2pi i/q)`. Then `u^q=1` and `u^r+u^(r+1)=-2c`. At the repeated ordinate `gamma` and the last ordinate `-(q-1)gamma`, the scaled two-monomial has value `u`. The polynomial therefore evaluates to `epsilon` at every target, has constant coefficient one, nonnegative coefficients, and tail mass `(1-epsilon)/c`. This attains the lower bound.

The spectral certificate, arbitrary-relation bound, and sharp positive witnesses count together. No spectral premise is introduced.

## Lean certificate

Modules in `GaloisForLFunctions/ArithmeticPositiveDuality/`:

- `OddCyclePhaseEnergy.lean`: `odd_cycle_edge_energy`, `odd_unit_product_phase_energy`.
- `SharpOddOrdinateRelationMass.lean`: `odd_ordinate_relation_sharp_mass_bound`.
- `SharpOddRelationAnnihilators.lean`: `oddRelationAnnihilator_at_harmonic`, `exists_sharp_odd_relation_accuracy`, `odd_relation_accuracy_frontier`.

Each module passed direct `lake --old env lean` audit without warnings. Every listed capstone has exactly `[propext, Classical.choice, Quot.sound]` as axioms. All three modules are wired into `ArithmeticPositiveDuality.lean`; umbrella not compiled. The existing finite cyclic Parseval and exact positive phase-energy identities supply the analytic dependencies.
