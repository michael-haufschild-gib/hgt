# Countable dissipative finite-KMS cluster values imply RH

- **ID:** `prime-arch-countable-passive-cluster-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / RH PROOF-BURDEN REDUCTION
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT AN RH PROOF]`
- **Lean files:**
  - `formal/GaloisForLFunctions/HTGeometry/FiniteKMSPassivePalette.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeArchCountablePassiveResponseRH.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeArchCountablePassiveResponseEquivalence.lean`

## Statement

Fix one sequence of finite KMS/Wightman systems, with dimensions, inverse temperatures,
Hamiltonian eigenvalues, and transition amplitudes allowed to vary with the cutoff `N`.  For a
Gaussian-rational source point

\[
s_q\in \mathbb Q+i\mathbb Q,
\qquad
z_q=(s_q-\tfrac12)(-i),
\]

assume

\[
0<\Re s_q<\frac12,
\qquad
\Im s_q>\frac{218}{25},
\qquad
\zeta(s_q)\ne0.
\]

Let `R_N(z)` be the finite KMS transition response.  If, at every such countable probe,

\[
\Im\mathcal S(z_q)
\in
\overline{\{\Im R_N(z_q):N\in\mathbb N\}},
\]

where `S` is the analytically continued prime--archimedean source trace, then RH holds.

This hypothesis is weaker than pointwise thermodynamic convergence.  It asks only for one real
cluster value at countably many positive high-frequency probes.  It does not ask for convergence
of real parts, convergence at other points, locally uniform convergence, or a single finite system
representing all source values.

The carrier is now exact.  Let (r_N) enumerate (mathbb Q), and take the one-state system with
zero Hamiltonian, inverse temperature zero, and real observable amplitude (r_N).  Its response is

\[
R_N(z)=\frac{r_N^2}{z},
\qquad
\Im R_N(z)=-\frac{r_N^2\Im z}{|z|^2}.
\]

For every (z) in the open upper half-plane,

\[
\overline{\{\Im R_N(z):N\ge0\}}=(-\infty,0].
\]

Consequently, at every exact quartet-admissible radius (R), countable Gaussian-rational source
membership in this single universal palette is equivalent to the positive-frequency response
condition above (R), and hence to RH.

## Proof

Every finite KMS/Wightman transition intensity is nonnegative, so finite passivity gives

\[
\Im R_N(z_q)\le0.
\]

The half-line `(-infinity,0]` is closed.  Hence every cluster value of the finite imaginary
responses also lies in that half-line:

\[
\Im\mathcal S(z_q)\le0.
\]

The exact coordinate identity

\[
\mathcal S((s-\tfrac12)(-i))
=-i\,\mathcal F(s)
\]

identifies this inequality with

\[
\Re\mathcal F(s_q)\ge0,
\]

where `F` is the completed prime--Gamma flux.  The exact off-line-quartet central-band theorem
handles frequencies of absolute value at most `218/25`, reflection handles negative high frequencies,
and Gaussian-rational density plus continuity upgrades the countable positive high-frequency sign
to the full anti-Herglotz source sign.  The existing source criterion then proves RH.

## Lean certificate

The module proves:

- `gaussianRatPassiveResponsePoint`;
- `gaussianRatPassiveResponsePoint_im`;
- `continuedPrimeArchSourceRelativeTrace_gaussianRatPassiveResponsePoint`;
- `CompletedPrimeGammaPositiveFrequencyAbove`;
- `CompletedPrimeGammaGaussianRatPositiveFrequencyAbove`;
- `completedPrimeGammaPositiveFrequencyAbove_of_gaussianRat`;
- `continuedPrimeArchPositiveFrequencyAbove_of_completedPrimeGamma`;
- `riemannHypothesis_of_gaussianRat_positiveHigh_finiteKMSWightmanResponse_im_mem_closure`.
- `closure_range_universalOneStateKMSPassiveResponse_im`;
- `primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_positiveFrequency`;
- `primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_riemannHypothesis`.

The result compiles with no `sorry`, `admit`, custom axiom, `opaque`, or `unsafe` declaration.

## Exact remaining obligation

Prove that the continued arithmetic source belongs to the universal dissipative chamber at every
regular Gaussian-rational point with

\[
0<\Re s<\frac12,
\qquad
\Im s>\frac{218}{25}.
\]

The universal finite-system palette is already explicit and exhausts the chamber.  Full
thermodynamic-limit convergence is sufficient but unnecessary; the remaining content is the
source-side sign itself.

## Gates

- [x] 0 -> 1: countable scalar cluster condition isolated
- [x] 1 -> 2: paper proof complete
- [x] 2 -> 3: axiom-clean Lean proof compiled, including the exact universal palette and the
  variable-radius equivalence
- [ ] 3 -> 4: not a standalone publication claim
