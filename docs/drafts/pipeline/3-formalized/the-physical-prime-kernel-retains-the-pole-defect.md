# The physical prime kernel retains the pole defect

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The ground-state transform of the literal prime-pairing kernel equals the original prime defect plus a nonnegative non-ratio energy, with the original arithmetic pole as its exact nullspace.

For `b_n=1/√n`, `M=∫g²` and `K_g(n,j)=primePair(atom g n,atom g j)`, set

`D_g(x)=½Σ_(n,j≤N) K_g(n,j)b_n b_j(x_n/b_n-x_j/b_j)²`.

The exact non-ratio identity gives `K_g=M P+K_NR`, with `K_NR≥0` for a nonnegative profile. The identity is `D_g=M D_N+D_NR`. Unlike the mass-Gram pairing `D(x,Gx)`, this expression retains nonnegative prime-power edges and the original pole vector.

The corresponding exact signed Weil decomposition is

`W_g(x)=D_g(x)+Gamma_g(x)+Pole_g(x)-Σ_n [(K_g b)_n/b_n]x_n²`.

**Open analytic comparison:** control the signed Gamma, pole and row-potential remainder together with `D_NR`. Dropping `D_NR` need not give a useful remainder bound. Neither this identity nor entrywise kernel positivity alone proves the logarithmic defect reserve or quasi-RH.

## Proof

[PROVED HERE] Write `y_n=x_n/b_n`. Symmetry of any finite kernel `K` gives

`½Σ K_nj b_n b_j(y_n-y_j)² + Σ K_nj x_n x_j = Σ_n (x_n²/b_n)Σ_j K_nj b_j`.

Expand the square and exchange the two indices in its second diagonal term. For the exact-ratio prime kernel `P`, its row identity is `(P b)_n=(A(⌊N/n⌋)+log n)b_n`. Comparing with the existing identity `P_N(x)+D_N(x)=Σ_n(A(⌊N/n⌋)+log n)x_n²` identifies its transformed energy with `D_N`.

For the literal physical prime kernel, the exact lag decomposition gives `K_g=M P+K_NR`. Each entry of `K_NR` is a sum of nonnegative von Mangoldt weights times nonnegative autocorrelations, with exact ratios removed. Linearity in the kernel proves `D_g=M D_N+D_NR`, hence `D_g≥M D_N`. If `M>0`, zero physical energy implies zero original defect; the existing prime-defect gap identifies this nullspace with `span(b)`. Conversely every difference `y_n-y_j` vanishes on that line. The existing uniform prime gap therefore gives `D_g(x)/M≥δ‖x-proj_b x‖²`, with the same `δ>0` for every horizon and overlap of the tilted spline.

Finite prime-pairing linearity identifies `Σ K_g(n,j)x_nx_j` with the literal synthesized prime sum. Substitution into the complete Weil identity gives the stated signed decomposition, retaining Gamma and both pole moments. The tilted unit spline is nonnegative because it is a positive exponential times a convolution of nonnegative interval indicators; its proved positive square mass supplies `M>0` at every positive width.

**Scope:** exact physical kernel and every overlap; no prime-distribution approximation or missing analytic premise. The signed remainder estimate remains open.

## Lean

`GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePhysicalPrimeKernelRetainsThePoleDefect.lean`:

- `physicalPrimeKernel_defect_eq`: exact ratio and non-ratio energy decomposition.
- `physicalPrimeKernel_defect_eq_zero_iff`: unchanged arithmetic ground line.
- `weilQuad_eq_physicalPrimeDefect_add_remainder`: actual signed Weil decomposition.
- `tiltedSpline_physicalPrimeDefect`: unconditional fixed-profile specialization.
- `exists_tiltedSpline_physicalPrimeDefect_gap`: one positive gap for every horizon and overlap.

Direct `lake --old env lean` audit passed without warnings. All five axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.
