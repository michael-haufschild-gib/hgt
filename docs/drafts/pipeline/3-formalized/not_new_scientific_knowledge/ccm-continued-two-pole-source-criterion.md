# CCM continued two-pole source criterion

- **ID:** `ccm-continued-two-pole-source-criterion`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMTwoPoleSourceCriterion.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Statement

Let `T(z)` be the meromorphically continued prime--archimedean relative trace already formalized
in the CCM source stack, and define

\[
K(z,w)=\frac{T(\overline w)-T(z)}{z-\overline w}.
\]

For two poles and two coefficients define the explicit source energy

\[
\mathcal E(z,w;a,b)
=a\overline aK(z,z)+a\overline bK(z,w)
 +b\overline aK(w,z)+b\overline bK(w,w).
\]

On the natural continued source domain, with the two poles distinct and separated from both
reflected poles, Lean proves the exact identity

\[
\mathcal E(z,w;a,b)
=\left\langle
  \frac{a}{\lambda-z}+\frac{b}{\lambda-w},
  \frac{a}{\lambda-z}+\frac{b}{\lambda-w}
 \right\rangle_{\Xi,\mathrm{Weil}}.
\]

Define `CCMContinuedTwoPoleSourcePassivity` to require

\[
\Re\mathcal E(z,w;a,b)\ge0
\]

for every admissible separated pair and every `a,b`. Then Lean proves

\[
\mathrm{RH}
\quad\Longleftrightarrow\quad
\texttt{CCMContinuedTwoPoleSourcePassivity}.
\]

## Positive carrier law

The RH-bearing CCM carrier is the moving rank-two continued source form. It must remain positive
for poles approaching every functional-equation conjugate divisor pair. No full Cauchy-span density
or arbitrary Weil test-space completion is required.

The converse proof uses two real pole approaches with unequal speeds. They remain inside the open
critical-strip source domain, avoid every reflected collision, and converge in the multiplicity-exact
divisor `ell^2` carrier to the negative off-line sign direction. Thus any off-line Xi zero forces a
negative value of the explicit source energy along an admissible two-pole sequence.

## Remaining construction theorem

The non-q62 formal corpus already supplies:

- the exact Sonin intersection projection and resolvent correction;
- the finite-support semilocal Sonin relative trace;
- self-adjointness and Hilbert--Schmidt trace pairing;
- the one-mode geometric normalization gate
  `SoninSemilocalFluxNormalization`;
- the exact continued prime-plus-archimedean source identity above.

The remaining RH-bearing construction theorem is therefore positive and precise:

```text
the distinguished semilocal Sonin principal/residual graph supplies
CCMContinuedTwoPoleSourcePassivity on the normalized moving pole family.
```

This statement contains the unresolved sign. The present card proves every transfer and
admissibility step around it, but does not prove that sign for zeta.

## Formal declarations

```text
RHTower.ccmContinuedCauchyKernel
RHTower.ccmTwoPoleSourceEnergy
RHTower.CCMContinuedCauchyDomain
RHTower.XiC_conj
RHTower.ccmContinuedCauchyDomain_of_regular_same_spectral_im
RHTower.xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
RHTower.CCMContinuedTwoPoleSourcePassivity
RHTower.riemannHypothesis_iff_ccmContinuedTwoPoleSourcePassivity
RHTower.ccmContinuedTwoPoleSourcePassivity_iff_riemannHypothesis
```

## Verification

- [x] prior non-q62 source and Sonin declarations searched before implementation
- [x] exact two-pole source expansion compiled
- [x] centered Schwarz law compiled
- [x] open-strip continued-domain preservation compiled
- [x] collision-free unequal-speed pole approach compiled
- [x] source-passivity equivalence with RH compiled
- [x] narrow module and CCM umbrella builds
- [ ] distinguished semilocal Sonin source passivity
- [ ] RH
