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
- Actual reciprocal affine-shell source: uniform unnormalized square budget `K_m c²(1+log c)`; [Lean proof](../3-formalized/reciprocal-shell-variation-controls-the-actual-source.md). Its conductor constant still includes a residue-Mertens threshold.
- Fixed finite conductor packets are positive for `c≤(log N)^α`, `α<1/48`.
- Growing Gamma reserve: `κ c^-7 log N-bc`, with explicit constants, for `1≤c≤N`.
- Conductor-sensitive floor: formalized in [conductor-scale-controls-completed-energy.md](../3-formalized/conductor-scale-controls-completed-energy.md), with standard-only axioms.
- Complete reserve `W_(N,c)≥a c^-7 D_N-C c^9‖x‖²` for `N≥Hc^8`: formalized in [growing-overlap-has-an-effective-complete-defect-reserve.md](../3-formalized/growing-overlap-has-an-effective-complete-defect-reserve.md). Every negative unit vector has `D_N≤C'c^16`.
- Whole-family harmonic Gram lower bound: `Σ_(n≤N)(Σ_(m≤Q)a_m r_m(n))²≥(log(N+1)-2 log Q)Σa_m²`, for `Q≥2`; `GrowingRamanujanFamiliesHaveASquareRootHorizon.ramanujanPoleProfile_family_squareRoot_lower`. The earlier pairwise `Q³/log N` budget is not a necessary horizon restriction.
- **Open:** effective negative-eigenvector confinement, growing-conductor weighted source estimate, and physical loss with exponent below `1/2`.

The proved second-order synthesis condition is `(κ_N/N)^4 log κ_N→0`; for widths `(log N)^α/N`, it holds when `α>1/4`. The present finite-packet positivity estimate only covers `α<1/48`. These ranges do not overlap. Moreover, synthesis of a test supported in `[-R,R]` uses `blockSize R=⌈1+exp(2R)⌉`, so its separation dependence must be retained. Uniform arithmetic source horizons alone do not close either gap.

The finite-sieve spectral tail costs `2(log A+L_Q)/log R` for a class vector supported at `a≤A`; [Lean proof](../3-formalized/finite-sieve-profiles-have-logarithmic-conductor-tails.md). Density-preserving harmonic comparison now transfers this to relative squared error `16(log A+L_Q)/log R` in the actual class weights; [Lean proof](../3-formalized/finite-sieve-profiles-have-effective-ramanujan-approximations.md). The [exponential defect-only cutoff](../3-formalized/logarithmic-conductor-moments-sharpen-defect-confinement.md) is formalized: squared error at most `η` using `m≤exp(Cη(K+1))`, uniformly over every horizon. The signed negative-eigenvector bound remains open.

The exponential cutoff replaces the valuation-box modulus. With the present negative-vector defect bound it still gives `exp(O(c^16))` conductors. The existing fixed-conductor residual estimates do not control this growing family.

The complete reserve uses the exact horizon-uniform counterterm `P_N+D_N≤(log N+log 4+4)‖x‖²`, avoiding a shrinking-error convergence horizon. The polynomial defect bound alone still gives an exponential conductor family. Useful confinement must exploit additional structure of the complete signed form.

This limitation is intrinsic to defect-only capture: actual unit conductor-`2^k` vectors have defect at most `γ+(k+1)log 2+log 4+5` eventually, while their total coordinate mass below every fixed cutoff `Q<2^k` tends to zero. [Lean proof](../3-formalized/prime-defect-confinement-must-retain-low-energy-conductors.md). Thus a polynomial cutoff in the defect budget cannot work. These witnesses are not negative complete-Weil eigenvectors; the signed eigenvalue equation remains the unresolved additional input.

## Candidate signed reserve — unproved

An estimate `W_(N,c)(x)≥a c^-7(D_N(x)-C log(2c)‖x‖²)` would give logarithmic defect on negative vectors. Its starting horizon must also be controlled; a fixed-`c` eventual statement would leave the synthesis obstruction intact. The current proof does not establish this cancellation between prime, Gamma and pole terms. Together with the formalized exponential cutoff, this reserve would give a polynomial conductor range. The weighted residual and physical synthesis estimates would remain to prove. Direct confinement of negative eigenvectors remains an alternative.

Separate payment of the actual non-ratio shell cannot produce this reserve. For `q=(∫φ)²/∫φ²`, any eventual bound `NR≤(∫g²)(εD+C‖x‖²)` forces `C≥max(cq/(4 log 2)-1/2,0)²/(2ε)`; `TheShellsAloneCostTheSquareOfTheOverlap.le_of_nonRatioForm_payment`. Direct Lean audit uses only standard axioms. This forces the existing order `c^9` mass cost when `ε` is a fixed fraction of `c^-7`; it does not obstruct an estimate retaining the complete signed form.

The alternative reserve `D(x,Gx)` is also not positive for the literal mass Gram. For every fixed `c>1`, eventually, `D(x,Gx)+τD(x-Gx)` is nonnegative for all vectors exactly when `τ≥1/4`. At equality its kernel is `(I+G)^(-1)span(b)`, whose nonzero vectors have positive unsmoothed defect. This [sharp correction and transformed kernel](../3-formalized/overlap-gram-needs-a-prime-defect-corrector.md) are formalized with standard axioms. A comparison with the complete signed Weil form remains unproved.

The literal physical prime kernel has a different, positive ground-state transform: `D_g=M D_N+D_NR`, with `D_NR≥0`, exactly the original pole nullspace, and the original uniform spectral gap after normalization by `M`. Its [Lean proof](../3-formalized/the-physical-prime-kernel-retains-the-pole-defect.md) also gives `W_g=D_g+Gamma_g+Pole_g−Σ_n[(K_g b)_n/b_n]x_n²`. The signed remainder must still be controlled together with `D_NR`; this identity does not establish the candidate logarithmic reserve.
