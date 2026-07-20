# 2026 arXiv electrical/optical frontier harvest

- **ID:** `arxiv-2026-electrical-optical-frontier-harvest`
- **Stage:** 2-fully-proven/needs-audit
- **Type:** `[LITERATURE HARVEST] [FRONTIER MAP] [NO-GO CLOSURE] [NO RH CLAIM]`
- **Parent:** `electrical-optical-law-application-census.md`
- **Area:** `HTGeometry`, `RHTower`, `HilbertMetric`
- **Cutoff:** arXiv submissions through 2026-07-20
- **Formal output:** none; no preprint statement below is treated as a new axiom or interface

## Reproducible search boundary

The harvest queried arXiv's dated metadata for submissions from 2026-01-01 through 2026-07-20
in `physics.optics`, `eess.SP`, `eess.SY`, `math.OC`, `math-ph`, and relevant `quant-ph` results.
The query families were:

```text
Wigner--Smith / complex delay / scattering reciprocity
passive or positive-real scattering / realization / network synthesis
finite aperture / inverse source / passive cloaking
Hankel rank / minimal or sparse state-space realization
Riemann zeta / prime spectrum with optical or electrical scattering
```

Every returned paper with a theorem or formula capable of touching the live source, passivity,
realization, observation, or cofinal-limit interfaces was read in full.  Papers merely deposited
on arXiv in 2026 but carrying older journal references were screened but not counted as 2026
scientific novelty.  No 2026 paper directly connecting optical/electrical scattering to zeta or
hypertranscendence was returned; the direct zeta-light results found by the same searches predate
2026 and remain computational or realization analogies.

## Exact theorem and formula harvest

### 1. Finite stationary passive broadband matching is impossible

[arXiv:2607.10704](https://arxiv.org/abs/2607.10704) models a finite passive one-port by

\[
\Sigma_N(s)=\sum_{n=1}^N\frac{w_n}{s+\Gamma_n+i\nu_n},\qquad
r(s)=\frac{s-\kappa/2+\Sigma_N(s)}{s+\kappa/2+\Sigma_N(s)},
\]

with positive weights and damping.  Its Theorem 2 proves that if `Sigma_N` is finite rational,
positive-real, and vanishes at infinity, then `r(i omega)` cannot vanish on any nonempty open
frequency interval.  Otherwise rational analytic continuation would force `r` to vanish
identically and hence `Sigma_N(s)=kappa/2-s`, contradicting both high-frequency decay and
positive-realness.

Under the paper's additional rational-Schur, no-axis-pole/zero, asymptotic, and stationary
assumptions, its Poisson--Jensen formula gives

\[
\int_{-\infty}^{\infty}\log\frac1{|r(i\omega)|}\,d\omega\le \pi\kappa,
\qquad
\|r\|_{L^\infty([-B,B])}\ge \exp\!\left(-\frac{\pi\kappa}{2B}\right).
\]

**Verdict: `[NO-GO]` with a sharp survivor.**  An exact open-band match to the continued source
cannot be supplied by one finite stationary passive rational aperture.  Any exact route must use a
genuine cofinal/infinite limit or explicitly spend an active, nonstationary, or single-mode-prior
resource.  The paper's write-probability identity additionally requires an isometric capture of all
controlled outputs; absorption or small reflection alone is not storage.  Its numerical designs and
computer-assisted certificates are not used here.

### 2. Stable minimal realization equals finite Hankel rank plus uniform decay

[arXiv:2607.03849](https://arxiv.org/abs/2607.03849) defines the Hankel space of an input-output
family `Psi` by

\[
W_\Psi=\operatorname{span}\{v\circ H_j:j\in J,\ v\in U^*\},
\qquad \operatorname{HankelRank}(\Psi)=\dim W_\Psi.
\]

Its Theorem 3.1 proves for state-linear systems:

```text
stable finite-dimensional realization
  iff finite Hankel rank and uniform decay;
uniform exponential decay at rate beta
  -> every minimal realization is stable at rate beta;
finite Hankel rank and uniform decay
  -> uniform exponential decay.
```

The paper extends the equivalence to state-affine, LPV, and switched systems through explicit
input-forgetting conditions.

**Verdict: `[BRIDGE] [INTERFACE]`.**  The live Lean corpus already proves the finite Hankel-rank,
minimal-dimension, controllability, and observability laws, but not this normed input-word decay
theory.  The exact missing premise for a stable realization is therefore **uniform decay**, not
another rank determinant.  Stability still does not create positive-realness, anti-Herglotz sign,
or source equality, so this theorem cannot close the RH-bearing source wall by itself.

### 3. Passive quasistatic cloaking cannot be exact on an interval

[arXiv:2601.02169](https://arxiv.org/abs/2601.02169) constructs from the Dirichlet-to-Neumann map
the Herglotz function

\[
H_{V_0}(z)=z\,\langle(\Lambda_{\varepsilon(\cdot,\sqrt z)}-
\Lambda_{\varepsilon_0})V_0,V_0\rangle.
\]

Under its material, passivity, regularity, and boundary hypotheses, Theorem 52 proves that a
dielectric obstacle cannot be perfectly cloaked on a positive finite frequency interval.  The proof
uses open-interval vanishing, Schwarz reflection, analytic continuation, and the positive
high-frequency coefficient.  Its Herglotz sum rule is

\[
\lim_{\eta\to0^+}\lim_{y\to0^+}\frac1\pi
\int_{\eta<|x|<\eta^{-1}}\operatorname{Im}h(x+iy)\,dx=a_{-1}-b_{-1}.
\]

**Verdict: `[NO-GO] [PARENT]`.**  This independently confirms that passivity plus analyticity
forbids exact finite-band invisibility.  It is a geometry-specific parent theorem, not a source
realization and not evidence for RH.  Its transferable content is the analytic-continuation
obstruction, already present abstractly in the project.

### 4. Multidimensional passive synthesis has a sum-of-squares obstruction

[arXiv:2607.02557](https://arxiv.org/abs/2607.02557) records a necessary condition for a
`k`-variable scalar lossless scattering function `s=sigma*g*/g`, with
`g=g_0+g_1 p_1`, to have a finite lossless synthesis.  With
`a_0=g_0-g_1` and `a_1=g_0+g_1`, Theorem 4.1 requires a polynomial vector `P` satisfying

\[
P^*P=a_1a_1^*-a_0a_0^*.
\]

This is a polynomial sum-of-squares requirement.  Every bivariate lossless function is covered by
the classical construction, and a low-degree trivariate class survives, but generic higher-order
or higher-dimensional functions fail the condition.

**Verdict: `[NO-GO]` with a constructive subclass.**  A multivariable positive-real or bounded-real
source cannot be declared network-realizable merely from its sign.  The live route must construct
its colligation explicitly or prove that its exact source polynomial belongs to a synthesizable
sum-of-squares subclass.  Generic Cauer/Foster language cannot discharge this interface.

### 5. Sparse state-space support reduces to polynomial equations

[arXiv:2603.28754](https://arxiv.org/abs/2603.28754) proves that a rational proper transfer
function with simple poles has a realization on a prescribed support exactly when a similarity
transform of a modal realization has the required zero pattern.  Factoring the similarity into
permutation, row-addition, and diagonal factors reduces the zero pattern to multivariate
polynomial equations in the row-addition parameters; a reduced Groebner basis detects complex
feasibility and the paper gives a separate real-algebraic procedure.

**Verdict: `[COMPOSER]`.**  This can discharge a future **sparsity** interface after the arithmetic
transfer function is known.  It does not supply the transfer function, passivity, convergence, or
source identity, and therefore does not advance the current source-facing core.

### 6. Complex Wigner--Smith delay controls narrowband chirped-pulse shifts

[arXiv:2602.22034](https://arxiv.org/abs/2602.22034) uses

\[
\tau=-\frac{i}{2\pi}\frac{\partial}{\partial f}\log\rho(f),
\qquad
D_f=-\widetilde\Delta^2\operatorname{Im}\tau,
\qquad
D_t=\operatorname{Re}\tau-\Omega'\delta_t^2\operatorname{Im}\tau.
\]

Here `rho` is a scalar transmission/reflection coefficient (or the normalized scattering
determinant), and the last two formulas follow after a first-order expansion across a pulse whose
bandwidth is much narrower than the resonance linewidth.

**Verdict: `[CONSUMER]`.**  This supplies a physical readout for the existing logarithmic-delay
surface, including the imaginary delay that intensity measurements lose.  Because the shift law is
a narrowband approximation and scalarization, it is neither an unconditional universal theorem
for the matrix Wigner--Smith object nor a source/passivity producer.  No Lean interface is
discharged.

### 7. Boundary-admittance/continued-fraction formulas are conditional composers

[arXiv:2601.04407](https://arxiv.org/abs/2601.04407) harvests the useful spectral boundary
condition

\[
sY_{\mathrm{in}}(s)+\frac1{L_J}=0,
\]

and connects a lossless positive-real one-port, a Cauer continued fraction, and a Jacobi resolvent.
These are downstream realization and spectral-compression formulas.

**Verdict: `[COMPOSER] [AUDIT REQUIRED]`.**  The paper's Proposition IV.1 says positive-realness
alone makes the eliminated internal block invertible and preserves positive-realness under its
Schur complement.  As stated, positive semidefinite real part does not imply invertibility; a
strictness or regularity hypothesis is missing.  The formula can be used only after the required
block invertibility and passive network realization are proved independently.  It is not admitted
as an unconditional project theorem.

### 8. A claimed positive-real Mori kernel fails the standard definition

[arXiv:2606.15505](https://arxiv.org/abs/2606.15505) derives for harmonic hidden modes

\[
\widehat K(s)=\sum_i\frac{R_i}{s^2+\omega_i^2},\qquad R_i\succeq0,
\]

and calls this matrix function lossless positive-real.  Already in the scalar one-mode case,

\[
\operatorname{Re}\frac1{(\sigma+i\tau)^2+\omega^2}
=\frac{\sigma^2-\tau^2+\omega^2}
{(\sigma^2-\tau^2+\omega^2)^2+4\sigma^2\tau^2},
\]

which is negative whenever `tau^2 > sigma^2+omega^2`, despite `sigma>0`.  The standard
positive-real oscillator term is instead `s/(s^2+omega^2)`; the missing factor changes the sign.
The supplemental identifiability argument also asserts an invertibility equivalence from a trace
condition that does not establish full matrix rank.

**Verdict: `[REJECTED]`.**  The pole/residue decomposition remains a harmonic-memory formula, but
its advertised positive-real and unconditional identifiability conclusions cannot discharge any
project interface.  No theorem or definition is imported from this claim.

### 9. Screened 2026 deposits that are not 2026 frontier results

- [arXiv:2607.08301](https://arxiv.org/abs/2607.08301) preserves incremental scattering
  passivity under projection to a closed convex state set, but arXiv records a 2025 journal
  reference.  It is a conditional passivity-preserving composer, not a source producer.
- [arXiv:2607.08637](https://arxiv.org/abs/2607.08637) adds a maximal-monotone nonlinear damping
  operator to a scattering-passive linear generator, but arXiv records a 2022 journal reference.
  It preserves an assumed passive generator and supplies no arithmetic realization.
- [arXiv:2606.13897](https://arxiv.org/abs/2606.13897) gives storage-function and
  Wirtinger-inequality conditions for delayed port-Hamiltonian passivity/stability.  These are
  conditional certificates for a supplied plant and delay, not a source theorem.

## Frontier delta

The 2026 literature sharpens the open core without closing it:

```text
source-defined finite KMS/passive apertures
  -> exact safe-half-plane prime-power coefficient identity        [OPEN]
  -> locally uniform, path-independent cofinal convergence to
     continuedPrimeArchSourceRelativeTrace                         [OPEN]
  -> anti-Herglotz transfer and RH consumer                         [LEAN-PROVED]
```

The new consequences are exact:

1. **Cofinality is forced.**  A finite stationary rational passive network cannot match exactly
   on an open frequency band.
2. **Generic synthesis is unavailable.**  Multidimensional sign data do not imply a finite network;
   the source must satisfy a concrete sum-of-squares/synthesis criterion or be built directly.
3. **Uniform decay is the stability gate.**  Existing Hankel rank and minimality laws do not alone
   yield a stable realization.
4. **Reporter improvements stay downstream.**  Complex Wigner--Smith pulse shifts, sparse support,
   boundary admittance, and passive projection preserve or expose a supplied response; none
   produces its arithmetic coefficients.
5. **No new local scientific theorem survived.**  The genuine progress is a literature-backed
   narrowing of the producer obligation and two explicit rejected interfaces, not a renamed
   electrical/optical analogy.

## Lean decision

No Lean file was added for this harvest.  The strongest correct results require analytic rational
continuation, normed input-word realization theory, or multidimensional sum-of-squares machinery
not currently present as source-facing interfaces.  Formalizing a weakened wrapper would add no
scientific content.  The two audited preprint gaps are explicitly barred from use as hypotheses.

## Gates

- [x] live source, generated API, formalized KMS/Hankel/Wigner--Smith surfaces searched first
- [x] dated arXiv metadata queried through 2026-07-20
- [x] relevant full PDFs read; theorem pages visually checked against extraction
- [x] exact formulas, hypotheses, and limitations harvested
- [x] older journal work newly deposited in 2026 separated from 2026 novelty
- [x] producer, bridge, consumer, no-go, and rejected claims separated
- [x] no numerical or computer-assisted result used
- [x] exact frontier and remaining source-value proposition stated
- [x] no conditional preprint claim imported into Lean
