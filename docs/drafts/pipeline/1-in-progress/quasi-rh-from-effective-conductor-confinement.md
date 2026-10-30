# Quasi-RH from effective conductor confinement

- **ID:** quasi-rh-effective-conductor-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The literal complete Weil form admits a lower bound on fixed-width difference-bump tests of separation `v` by `-C exp(σv)`, for some fixed `0≤σ<1/2`.

## Required conclusion

Prove `Re ρ≤1/2+σ<1` for every nontrivial zeta zero, or prove an obstruction to the specified conductor-confinement route. Failure of a coarse estimate alone does not retire the route. Any obstruction requires its strongest positive survivor and a Lean proof.

## Mathematical route

Write `W=W_(N,c)`, `v_m` for normalized Ramanujan vectors, `E_m(c)` for completed conductor energies, and `R_m=Wv_m-E_m(c)v_m`.

1. Retain the coprime-tail floor `E_m(c)≥δ(m/φ(m)) min(1,(m/c)^7)`, with one explicit `δ>0`.
2. Quantify conductor-coordinate mass of every negative unit eigenvector at growing overlap. Existing bounded-overlap confinement gives mass `≥1/18` on a finite family, but its conductor range and horizon depend on overlap.
3. Bound the actual weighted residual sum `Σ_(m∈S) ||R_m||²/(E_m(c)+B)²`. A value below `1/18` excludes eigenvalues below `-B`, provided the actual negative eigenvectors have the stated coordinate mass.
4. Include coefficient normalization, separated-bump synthesis error, poles, prime powers, and horizon boundaries. The resulting physical Weil loss must be `O(exp(σv))` with fixed `σ<1/2`.

## Established inputs and open estimates

- Fixed-conductor actual squared residual: `||R_m||²≤K_m(c^5/log N+c^10(log N/N)^2)`, for `N≥4(exp(1)+3)^2c²` beyond a fixed horizon; [Lean proof](../3-formalized/complete-conductor-residuals-retain-their-horizon-decay.md). All eight source terms are included.
- Actual reciprocal affine-shell source: uniform unnormalized square budget `K_m c^5`, hence normalized error `K_m c^5/log N`; [Lean proof](../3-formalized/affine-shell-errors-have-a-uniform-harmonic-budget.md). Its conductor constant includes a residue-Mertens threshold.
- Fixed finite conductor packets are positive for `c≤(log N)^α`, `α<1/48`.
- Growing Gamma reserve: `κ c^-7 log N-bc`, with explicit constants, for `1≤c≤N`.
- Conductor-sensitive floor: formalized in [conductor-scale-controls-completed-energy.md](../3-formalized/conductor-scale-controls-completed-energy.md), with standard-only axioms.
- Complete reserve `W_(N,c)≥a c^-7 D_N-C c^9‖x‖²` for `N≥Hc^8`: formalized in [growing-overlap-has-an-effective-complete-defect-reserve.md](../3-formalized/growing-overlap-has-an-effective-complete-defect-reserve.md). Every negative unit vector has `D_N≤C'c^16`.
- Whole-family harmonic Gram lower bound: `Σ_(n≤N)(Σ_(m≤Q)a_m r_m(n))²≥(log(N+1)-2 log Q)Σa_m²`, for `Q≥2`; `GrowingRamanujanFamiliesHaveASquareRootHorizon.ramanujanPoleProfile_family_squareRoot_lower`. The earlier pairwise `Q³/log N` budget is not a necessary horizon restriction.
- **Open:** effective negative-eigenvector confinement, growing-conductor weighted source estimate, and physical loss with exponent below `1/2`.

The current finite approximation selects a prime threshold exponential in its defect bound, then all divisors of a valuation-box modulus. Neither this qualitative construction nor fixed-modulus prime asymptotics supply the needed growing-conductor estimate.

The complete reserve uses the exact horizon-uniform counterterm `P_N+D_N≤(log N+log 4+4)‖x‖²`, avoiding a shrinking-error convergence horizon. The polynomial defect bound alone still gives an enormous conductor family under existing generic compactness. Useful confinement must exploit additional structure of the complete signed form.
