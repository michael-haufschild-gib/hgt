# Route N C19 projective parity/leakage bridge (2026-08-10)

Formal module: `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnProjectiveParityLeakageBridge.lean` (umbrella-wired).

Exact results:
- Gamma-sewn grade selects projective weight `z_t(p)=-|t| log p`.
- `exp(2 z_t(p))=p^(-2|t|)`, the Route N transverse modular cocycle.
- Projective marked-to-bulk odds on `P^1(F_p)` equal `p^(-1-2|t|)`, literally the twisted squarefree parity odds.
- At `t=0`, selected natural-cone state is uniform and fixed by residue Weyl inversion.
- Projective foreign-polarization leakage satisfies
  `L_t(p)=H_t(p)(p-1)/(p+p^(-2|t|))`.
- Uniform comparison: `(1/3)H_t(p) <= L_t(p) <= H_t(p)`.
- `Summable L_t iff t=0`; pointwise `L_t(p)=0 iff t=0`.

Verification:
- direct `lake env lean` passed;
- explicit olean generation passed;
- headline axiom audit uses only `propext`, `Classical.choice`, `Quot.sound`.

Research consequence:
Finite projective realization and all-prime sector classifier are closed. Naive same-scalar-sector normality is invalid: off-neutral grades undergo orthogonality catastrophe, so assuming scalar survival restates desired grade. Live Route N theorem is construction of source-derived continuation-record correspondence plus a source Fourier-Mellin theorem forcing Xi principal conormals to have zero complementary record while conserving parity modular marginal.

Paper/map updated with (N.37)-(N.39).