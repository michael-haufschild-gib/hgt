# Parity-free simple-ground Fourier real-zero law

- **ID:** `parity-free-simple-ground-fourier-real-zero-law`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, full restricted-Weil ground selection
- **Type:** THEOREM + FAILED CLOSURE AUDIT (paper)
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [SECTIONS 1--3 LEAN-PROVED FOR EVERY PACKET] [SECTION 4 ANALYTIC LIMIT LEAN-PROVED] [COMPRESSION MATRIX IDENTIFICATION LEAN-PROVED] [VARIATIONAL ASSEMBLY OPEN]`
- **External parent:** Connes--van Suijlekom,
  [Quadratic Forms, Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257)
- **Statement:** For the reflection-invariant truncated-convolution operators of
  Connes--van Suijlekom, a simple isolated lowest eigenfunction has a Fourier transform with only
  real zeros without assuming that the eigenfunction is even.  The missing odd case follows from
  a nonnegative rank-one correction of the squared frequency operator.

## Goal and Route-U verdict

The Route-U finite-impedance branch suggested the following attack.

> **[CONJECTURE, FALSIFIED AS A CLOSURE]** A simple negative hard root
> $r=-\kappa^2$ with positive terminal mass makes $i\kappa$ a common nonreal zero of the
> ground, so a degenerate or odd extension of the Connes--van Suijlekom theorem should contradict
> it.

The exact killing mechanism is parity.  Positive terminal mass proves

\[
 \langle \cosh(\kappa t),k\rangle=0
 \qquad(k\in\ker A_\sigma^+),
\]

so $i\kappa$ is common only to the **even** ground space.  It says nothing about an odd vector at
the bottom of the full operator.  The common-zero formulation for a degenerate ground therefore
does not apply at $i\kappa$ unless one first supplies the missing cross-parity admission theorem.

The strongest positive survivor is the theorem proved below: the evenness hypothesis in the
simple-ground real-zero theorem is unnecessary.  This is useful but does not close Route U.  It
proves that an earlier simple odd ground also has a real-rooted Fourier transform, so odd descent
is compatible with the external theorem rather than contradictory to it.  The missing datum is
full-ground parity selection (or an equivalent literal odd-sector lower bound), not another
real-zero theorem.

## 1. Finite odd theorem

Use the finite matrix setting of the external parent.  On

\[
 H=\mathbb R^{\{-N,\ldots,N\}},
 \qquad De_j=j e_j,
 \qquad \Gamma e_j=e_{-j},
\]

let $Q\ge0$ be real symmetric, commute with $\Gamma$, and have entries

\[
 q_{ij}=\frac{b_i-b_j}{i-j}\quad(i\ne j),
 \qquad b_{-j}=-b_j,
\]

with arbitrary reflection-even diagonal.  Put

\[
 \eta=\sum_{j=-N}^N e_j,
 \qquad
 \beta=\sum_{j=-N}^N b_j e_j.
\]

Then $\eta$ is even, $\beta$ is odd, and the exact commutator is

\[
 [D,Q]=DQ-QD=|\beta\rangle\langle\eta|-|\eta\rangle\langle\beta|.
 \tag{PF.1}
\]

Assume

\[
 \ker Q=\mathbb R\xi,
 \qquad \Gamma\xi=-\xi.
 \tag{PF.2}
\]

Let $\widehat\xi$ be the Fourier transform of the trigonometric polynomial with coefficient
vector $\xi$, restricted to one period and extended by zero.  Then every zero of
$\widehat\xi$ is real.

## 2. Squared-frequency correction `[PAPER-PROVED]`

Set

\[
 \delta=D\eta=\sum_{j=-N}^N j e_j.
\]

Both $\delta$ and $\xi$ are odd.  Write temporarily

\[
 a=\langle\delta,\xi\rangle,
 \qquad b=\langle\beta,\xi\rangle.
\]

Applying `(PF.1)` to $\xi$ gives

\[
 QD\xi=b\eta.                                             \tag{PF.3}
\]

The vector $D\xi$ is nonzero and even, hence it cannot lie in the one-dimensional odd kernel of
(Q).  Therefore

\[
 0<\langle QD\xi,D\xi\rangle=ab.                         \tag{PF.4}
\]

In particular $a\ne0$.  Rescale $\xi$ so that

\[
 \langle\delta,\xi\rangle=1.
 \tag{PF.5}
\]

After this rescaling, `(PF.4)` says (b>0).

Restrict to the odd subspace (H^-), and put (T=D^2|_{H^-}).  Its spectrum is the simple set
$\{1^2,\ldots,N^2\}$.  Squaring the commutator and using parity gives

\[
 [T,Q]|_{H^-}=|\beta\rangle\langle\delta|
              -|\delta\rangle\langle\beta|.              \tag{PF.6}
\]

Equations `(PF.2)`, `(PF.5)`, and `(PF.6)` imply

\[
 QT\xi=b\delta-\beta.                                    \tag{PF.7}
\]

Define the rank-one correction

\[
 T'=T-|T\xi\rangle\langle\delta|.                        \tag{PF.8}
\]

First, $T'\xi=0$.  Second, `(PF.6)` and `(PF.7)` give

\[
 QT'=T'^*Q.                                               \tag{PF.9}
\]

Indeed,

\[
 QT-TQ=-|\beta\rangle\langle\delta|
        +|\delta\rangle\langle\beta|,
\]

while the two correction terms are

\[
 -|b\delta-\beta\rangle\langle\delta|,
 \qquad
 -|\delta\rangle\langle b\delta-\beta|,
\]

and their skew difference cancels the commutator exactly.  Thus (T') induces a self-adjoint
operator on the separated Euclidean quotient $H^-/\ker Q$.

The new point is that this induced operator is not merely self-adjoint; it is nonnegative.  For
every odd (f), `(PF.1)` gives

\[
 \langle QD^2f,f\rangle
 =\langle QDf,Df\rangle
  -\langle\beta,f\rangle\langle\delta,f\rangle.
 \tag{PF.10}
\]

Using `(PF.7)` in `(PF.8)`, the mixed terms cancel and yield

\[
 \langle QT'f,f\rangle
 =\langle QDf,Df\rangle-b\langle\delta,f\rangle^2.
 \tag{PF.11}
\]

But `(PF.3)` and `(PF.5)` say

\[
 \langle D\xi,Df\rangle_Q=b\langle\delta,f\rangle,
 \qquad
 \|D\xi\|_Q^2=b.
\]

Cauchy--Schwarz for the semidefinite (Q)-inner product therefore gives

\[
 b^2\langle\delta,f\rangle^2
 \le b\langle QDf,Df\rangle.
\]

Since (b>0), `(PF.11)` is nonnegative.  Hence every eigenvalue of the operator induced by (T')
on $H^-/\ker Q$ lies in $[0,\infty)$.

## 3. Determinant and Fourier zeros `[PAPER-PROVED]`

For $s\notin\{1^2,\ldots,N^2\}$, the rank-one determinant identity and `(PF.5)` give

\[
\begin{aligned}
 \det(T'-s)
 &=\det(T-s)
   \left(1-\langle\delta,(T-s)^{-1}T\xi\rangle\right)\\
 &=-s\det(T-s)\langle\delta,(T-s)^{-1}\xi\rangle.
                                                               \tag{PF.12}
\end{aligned}
\]

The left side has one zero from $\xi$, and every remaining zero is a nonnegative eigenvalue of
the quotient operator.  Consequently every zero of

\[
 \det(T-s)\langle\delta,(T-s)^{-1}\xi\rangle              \tag{PF.13}
\]

is nonnegative.

Oddness of $\xi$ supplies the exact bridge back to the first-order Fourier resolvent:

\[
 \sum_{j=-N}^N\frac{\xi_j}{z-j}
 =\left\langle\delta,(z^2-T)^{-1}\xi\right\rangle.       \tag{PF.14}
\]

Indeed, the (j,-j) pair on both sides is

\[
 \frac{2j\xi_j}{z^2-j^2}.
\]

By `(PF.13)`, every non-pole zero of `(PF.14)` has $z^2\ge0$, hence $z\in\mathbb R$.
The Shannon formula used in the external parent writes the actual Fourier transform as a real-zero
sine factor times this rational function.  Pole cancellations occur only at the real sampling
lattice, and oddness contributes the zero at (z=0).  Therefore every zero of
$\widehat\xi$ is real.

This proves the finite odd theorem.

## 4. Infinite-dimensional theorem `[PAPER-PROVED]`

Let (A) be the lower-bounded self-adjoint operator associated with a real truncated-convolution
form on (L^2([-L/2,L/2])), under the precise core and isolation hypotheses of the external
parent.  Assume its minimum $\lambda$ is simple and isolated, with odd eigenfunction $\xi$.

The external approximation proof applies after projecting every approximant to the odd subspace.
More explicitly, choose odd trigonometric polynomials $\eta_\varepsilon$ converging to $\xi$ in
norm with Rayleigh value below $\lambda+\varepsilon$, and let $E_N$ be a symmetric Fourier
space containing $\eta_\varepsilon$.  The minimum $\lambda_N$ of the compressed form satisfies

\[
 \lambda\le\lambda_N\le\lambda+\varepsilon.
\]

If the rest of the spectrum of $A$ lies above $\lambda+\Delta$, min--max on
$E_N\cap\xi^\perp$ puts the second compressed eigenvalue above $\lambda+\Delta$.  Hence, for
small $\varepsilon$, the compressed minimum is simple.  The compression commutes with reflection,
so its minimum vector has definite parity; its nonzero overlap with the odd vector $\xi$ forces
that parity to be odd.  Subtracting $\lambda_N I$ gives a positive matrix of the finite form above
with one-dimensional odd kernel.  Its minimum vector therefore has real-rooted Fourier transform.

The compressed vectors converge to $\xi$ in $L^2$.  Since all functions have support in the
fixed interval,

\[
 |\widehat f(z)|
 \le \sqrt L\,e^{L|\operatorname{Im}z|/2}\|f\|_2,
\]

so their Fourier transforms converge locally uniformly on $\mathbb C$.  Hurwitz's theorem then
excludes a nonreal zero of $\widehat\xi$.

Finally, a simple eigenfunction of a reflection-commuting operator is automatically either even or
odd.  The even case is the external theorem; the odd case is proved above.  Therefore:

\[
 \boxed{
 \text{Every simple isolated lowest eigenfunction has only real Fourier zeros.}
 }
 \tag{PF.15}
\]

No parity hypothesis is needed.

## 5. Hostile audit and significance

- **Internal audit.** Route U already used the even theorem and the finite-source common-zero
  remark.  Corpus searches found no general odd proof or the (D^2) correction `(PF.8)`--`(PF.11)`.
  This is not a Lean claim.
- **External audit.** The cited primary source proves the even theorem, comments that degenerate
  eigenspaces require common zeros, and checks the odd phenomenon only in its explicit
  five-dimensional appendix.  Targeted arXiv searches found no exact general odd statement.
  Search absence is not a priority proof; status remains `[NOVELTY UNVERIFIED]`.
- **Circularity audit.** `(PF.15)` uses only the divided-difference commutator, positivity,
  simplicity, parity, min--max, and Hurwitz.  It does not assume zero reality or RH.
- **Route-U delta.** The theorem removes parity from the external real-zero mechanism but kills the
  proposed closure: an odd spectral descent produces another real-rooted ground rather than a
  contradiction.  Any successful successor must prove from the literal completed-Xi source that
  the selected even critical state is the full bottom, or must couple its nonreal zero to every odd
  lower-ground vector.  Even-ground common zeros alone cannot do this.
- **Lean status.** Finite odd core is proved in
  `formal/GaloisForLFunctions/RHTower/CCMParityFreeOddGroundFourier.lean`: positive semimetric
  completion, nonnegative full characteristic roots, and real non-pole Fourier-resolvent zeros.
  `CCMCompactFourierMeanSquareZeroTransfer.lean` proves the exact fixed-support `L²` Fourier bound,
  locally uniform convergence, and nonzero-limit real-zero transfer.
  `CCMPublishedRestrictedWeilParityBlocks.lean` now constructs the literal centered parity packet,
  derives its PSD blocks and cross commutator, selects an unconditional PSD singular floor, and
  proves that a simple full odd ground automatically supplies source visibility, normalization,
  and all finite odd-ground data. Simple-floor selection and compressed-ground mean-square
  convergence remain open. This formalization closes the finite literal-adapter and
  analytic-transfer parts of the literature parity debt but does not receive Route-O
  whole-ground-comparison credit.

## No-go closure

- **Exact killing theorem/mechanism:** $i\kappa$ is common only to the even kernel; odd ground
  evaluation is unconstrained.
- **Strongest positive survivor:** parity-free simple-ground Fourier real-zero law `(PF.15)`.
- **New insight:** parity is not the obstruction.  Full-ground selection is.
- **Status:** dependency-closed paper proof; external novelty unverified; finite odd core
  and fixed-support analytic transfer Lean-closed; no Route-O ground-selection credit.

## Log

- 2026-08-16 — the compressed truncated convolution is identified with a centered
  divided-difference packet: exact commutator law `(i-j)Q_{ij} = b_j - b_i` with odd source, proved
  by two integrations by parts, in `HTGeometry/TruncatedConvolutionCommutator.lean` and
  `RHTower/TruncatedConvolutionParityPacket.lean`; the compressed quadratic form, its positive
  semidefiniteness criterion, and its kernel are identified with the truncated-convolution form on
  trigonometric polynomials; the symmetry of the form, Parseval on the unit interval, the Lipschitz
  bound of the form, the mode-window bridge to the parity index, and the existence of the compressed
  ground with its spectral-floor and kernel properties are formalized.
- 2026-08-11 — odd (D^2) correction derived; common-zero closure falsified; paper proof closed.
- 2026-08-14 — finite odd squared-frequency correction and non-pole Fourier-resolvent reality
  formalized in `CCMParityFreeOddGroundFourier.lean`.
- 2026-08-14 — exact fixed-support mean-square-to-locally-uniform Fourier estimate and Hurwitz
  zero-locus transfer formalized in `CCMCompactFourierMeanSquareZeroTransfer.lean`; literal
  compressed-ground approximation remains.
- 2026-08-14 — literal centered restricted-Weil parity frames, block positivity, cross commutator,
  unconditional finite ground shift, and simple-full-odd-ground adapter formalized in
  `CCMPublishedRestrictedWeilParityBlocks.lean`; no source visibility or normalization premise
  remains in the odd branch.
- 2026-08-16 — Shannon factorization of the band-limited transform, the literal identification of
  the packet cross-frequency block with the centered modes, (PF.14), the finite odd theorem, and
  the analytic limit step formalized in `CCMShannonFourierFactorization.lean` and
  `CCMPublishedOddGroundRealZeros.lean`.

### The variational engine of section 4 is now formal

`HTGeometry/GroundGapCompression.lean` (axiom-clean, wired, built) supplies both of the steps that
were listed as open, in the exact generality section 4 uses — a symmetric operator on a real inner
product space, with no spectral theorem:

    norm_sub_ground_proj_sq_le      a unit vector of Rayleigh quotient at most `lam + eps` is
                                    within `eps/Delta` in squared norm of the ground line
    tendsto_norm_sub_ground_proj    hence a minimizing sequence converges to the ground line
    tendsto_norm_sub_ground         with nonnegative ground overlap it converges to `xi` itself,
                                    which is exactly the mean-square convergence consumed by
                                    `CCMCompactFourierMeanSquareZeroTransfer`
    eq_zero_of_rayleigh_lt_of_inner_eq_zero,
      finrank_le_one_of_rayleigh_lt a subspace whose Rayleigh quotient stays strictly below
                                    `lam + Delta` meets the orthogonal complement of the ground only
                                    in zero, hence is at most a line — the simple-floor selection

What is still missing for the card is not an estimate but an object: the literal
truncated-convolution operator on `L^2([-L/2, L/2])` together with its compressions to the
symmetric Fourier spaces `E_N`, so that these two lemmas can be applied to it and the compressed
matrices identified with the finite packet of `CCMPublishedRestrictedWeilParityBlocks.lean`.

Added: `HTGeometry/SymmetricCompressionGround.lean` (`compress`, `inner_compress`,
`compress_isSymmetric`, `exists_compressed_ground`, `finrank_le_one_of_compressed_rayleigh_lt`) —
the compression of a symmetric operator to a subspace, the existence of its ground state on a
finite-dimensional subspace, and the transfer of the gap statements to it; and
`reflection_ground_eq_or_neg` in `GroundGapCompression.lean` — a simple eigenvector of an operator
commuting with an involution is either even or odd, which is the last sentence of section 4.

The literal infinite-dimensional operator these are to be applied to already exists in the corpus:
`RHTower/CCMRestrictedWeilFriedrichsOperator.lean` builds `ccmRestrictedWeilOperator` with a
compact resolvent and a ground eigenstate, and `RHTower/CCMRestrictedWeilGroundParity.lean` builds
its reflection and the even/odd splitting of the source quadratic form.  What remains is the
wiring: choose the symmetric Fourier compressions `E_N`, identify the compressed matrices with the
published parity packet, and feed the two convergence lemmas into
`compactFourier_limit_zero_im_eq_zero_of_meanSquare`.

### The Shannon bridge and the finite odd theorem are now formal

Two new axiom-clean modules close the gap between the finite resolvent numerator and the actual
Fourier transform, and identify the abstract packet data with the literal centered modes.

    RHTower/CCMShannonFourierFactorization.lean
      ccmModeWindow, ccmTrigPoly, continuous_ccmTrigPoly
      ccmModeWindow_succ, sum_ccmModeWindow_eq      the symmetric window splits into the zero mode
                                                    and the `±(k+1)` pairs
      ccmPeriodFactor, ccmPeriodFactor_ne_zero      `(e^{2πiz} − 1)/i` vanishes only on `ℝ`
      compactFourier_ccmTrigPoly                    **Shannon factorization**: the transform of a
                                                    trigonometric polynomial over one period is the
                                                    period factor times `∑_j ξ_j/(z + j)`
      sum_ccmModeWindow_odd_neg                     for an odd vector, `∑ ξ_j/(z+j) = -∑ ξ_j/(z-j)`
      sum_eq_zero_of_compactFourier_ccmTrigPoly_eq_zero,
        compactFourier_ccmTrigPoly_zero_im_eq_zero  off the real axis the zeros of the transform are
                                                    exactly the zeros of the first-order resolvent

    RHTower/CCMPublishedOddGroundRealZeros.lean
      ccmPublishedParityCrossFrequency_none/_some   the cross-frequency block is inclusion times mode
      ccmPublishedParity_squaredFrequency('),
        ccmPublishedParityEta_none/_some,
        ccmPublishedParity_delta(')                 `B^H B = diag((k+1)^2)`, `η = (1, √2, …)`,
                                                    `δ_k = √2 (k+1)`
      ccmOddGroundCoeff, _odd, _pos_aux, _neg_aux   the centered coefficient vector of an odd ground
      ccmMode_sq_sub_ne_zero, ccmModeShift_det_ne_zero,
        ccmModeShift_inv                            the shifted mode matrix is invertible off `ℝ`
      sum_ccmOddGroundCoeff_eq                      **(PF.14)** the first-order Fourier resolvent
                                                    equals the diagonal squared-frequency resolvent
      ccmPublishedParity_squaredResolventNumerator_eq
      ccmPublishedParityOddGround_compactFourier_zero_im_eq_zero,
        ccmParityFreeOddGroundData_compactFourier_zero_im_eq_zero,
        exists_ccmPublishedParityGroundShift_oddGroundRealFourierZeros
                                                    **the finite odd theorem**: the band-limited
                                                    Fourier transform of a simple odd ground of the
                                                    published packet has only real zeros
      ccmOddGroundLimit_compactFourier_zero_im_eq_zero
                                                    **(PF.15) analytic half**: a mean-square limit of
                                                    such grounds with nonvanishing transform again has
                                                    only real Fourier zeros

What remains for the card is exactly one object, unchanged in kind: the symmetric Fourier
compressions `E_N` of `ccmRestrictedWeilOperator`, together with the identification of the
compressed matrices with `ccmPublishedParityShift`, so that `GroundGapCompression` /
`SymmetricCompressionGround` supply the mean-square hypothesis of
`ccmOddGroundLimit_compactFourier_zero_im_eq_zero`.

### Sections 1--3 are now formal for an arbitrary packet, and so is the analytic limit

The finite theorem was previously formal only for the published restricted-Weil packet.  The new
module removes that restriction: it proves the parity-block construction from three structural facts
alone, and then instantiates them for an arbitrary centered divided-difference matrix, which is
exactly the matrix class of section 1.

    RHTower/CCMGeneralParityOddGroundAdapter.lean
      exists_ccmParityFreeOddGroundData_of_blocks
                                                only positive semidefiniteness of the two parity
                                                blocks, the rank-one cross commutator `(PF.1)`, and a
                                                simple visible odd kernel are used; the normalization
                                                `(PF.5)` is produced internally
      ccmParityEvenBlockOf, ccmParityOddBlockOf,
        ccmParityEvenBlockOf_posSemidef,
        ccmParityOddBlockOf_posSemidef          the parity blocks of an arbitrary centered packet
      ccmParity_mul_evenFrame_of_commutes,
        ccmParity_mul_oddFrame_of_commutes      reflection commutation alone splits the packet along
                                                the two parity frames
      ccmParityCross_commutator_of_displacement **(PF.1)** the rank-two clock commutator
                                                `|β⟩⟨η| − |η⟩⟨β|` compresses to the rank-one cross
                                                commutator required by the parity-free data
      exists_ccmParityFreeOddGroundData_of_simple_odd_ground
                                                the full finite adapter for an arbitrary
                                                reflection-symmetric displacement packet
      ccmOddGroundCoeff_smul, ccmTrigPoly_smul,
        compactFourier_ccmTrigPoly_smul          rescaling the kernel vector does not move the
                                                Fourier zeros
      ccmGeneralParityOddGround_compactFourier_zero_im_eq_zero
                                                the finite odd theorem for any such packet
      ccmCenteredParityPacket, ccmCenteredParitySourceFull,
        ccmCenteredParityPacket_commutes_reflection,
        ccmCenteredParitySourceFull_odd,
        ccmCenteredParityPacket_displacement    an arbitrary centered divided-difference matrix with
                                                odd source and reflection-even diagonal, after any
                                                spectral-floor shift, satisfies the three structural
                                                hypotheses
      ccmCenteredDividedDifferenceOddGround_compactFourier_zero_im_eq_zero
                                                **section 1 verbatim**: `Q ≥ 0` real symmetric with
                                                `q_{ij} = (b_i − b_j)/(i − j)`, `b_{-j} = −b_j`,
                                                arbitrary reflection-even diagonal, and
                                                `ker Q = ℝξ` with `Γξ = −ξ`, forces every zero of
                                                `ξ̂` to be real
      ccmCenteredDividedDifferenceOddGroundLimit_compactFourier_zero_im_eq_zero
                                                **section 4's analytic half verbatim**: a
                                                mean-square limit of such odd kernel vectors with a
                                                nonvanishing transform again has only real Fourier
                                                zeros

What remains is now a single analytic construction, unchanged in kind but now stated against the
general packet: for a real truncated-convolution form on `L²` with a simple isolated odd ground,
produce the symmetric Fourier compressions, show their matrices are centered divided-difference
matrices with odd source and reflection-even diagonal, and show their odd grounds converge in mean
square to the ground.  The variational half of that construction (`compress`,
`exists_compressed_ground`, `finrank_le_one_of_compressed_rayleigh_lt` in
`HTGeometry/SymmetricCompressionGround.lean`) is already formal.

### The matrix identification of the compressed form is now formal

Normalize the interval to `[0,1]` (a translation and a dilation, both of which conjugate the
truncated convolution into a truncated convolution and carry the exponential basis to the
exponential basis).  For an even `C¹` kernel `k` write

    (A f)(x) = ∫_0^1 k(x-y) f(y) dy,   e_j(x) = e^{2πijx},   Q_{ij} = ⟨e_i, A e_j⟩.

Two integrations by parts — one in the outer variable against `e_{-i}`, one in the inner variable
against `e_j` — produce the *same* interior double integral, so it cancels in the difference and
only the two endpoint terms survive:

    (i - j) Q_{ij} = b_j - b_i,   b_j = -(2πi)^{-1} ∫_0^1 (k(1-y) - k(y)) e_j(y) dy.

The substitution `y ↦ 1-y` sends `b_{-j}` to `-b_j`, and reflecting both the interval and the
frequency leaves `Q` invariant, so the diagonal is reflection even.  No Fubini and no
differentiation under the outer integral are used.

    HTGeometry/TruncatedConvolutionCommutator.lean
      fourierChar, hasDerivAt_fourierChar,
        fourierChar_neg_one_sub                 the exponential basis and the reflection
                                                `e_{-j}(1-u) = e_j(u)`
      truncConv, continuous_truncConv,
        hasDerivAt_truncConv                    the truncated convolution and the fact that
                                                differentiation falls on the kernel, by dominated
                                                differentiation under the integral
      truncConv_char_freq                       the inner integration by parts: multiplying the
                                                exponential by its frequency is differentiating
                                                the kernel, up to the two endpoint values
      convMatrix, convSource,
        convMatrix_commutator                   **the exact divided-difference law**
                                                `(i-j)Q_{ij} = b_j - b_i`
      convSource_neg, convSource_re_neg          the source is odd
      truncConv_reflect, convMatrix_reflect      the matrix is reflection invariant
      convMatrix_re_commutator                   the real form of the law

    RHTower/TruncatedConvolutionParityPacket.lean
      truncConvParitySource,
        truncConvParityDiagonal                  the centered source and diagonal of the packet
      truncConvParitySource_odd,
        truncConvParityDiagonal_even             the two structural parities
      ccmDividedDifferenceMatrix_truncConv       **the matrix identification**: every entry of the
                                                 compressed truncated convolution is the
                                                 corresponding entry of the centered
                                                 divided-difference matrix built from its own
                                                 boundary source and diagonal
      truncConvParityPacket,
        truncConvParityPacket_compactFourier_zero_im_eq_zero
                                                 a simple odd kernel vector of the shifted
                                                 compressed packet has a real-rooted band-limited
                                                 Fourier transform

The compressed quadratic form has also been identified, so the two spectral hypotheses of section 4
are now literal statements about the truncated-convolution form on trigonometric polynomials.

    HTGeometry/TruncatedConvolutionCommutator.lean (continued)
      fourierChar_conj, fourierChar_add,
        integral_fourierChar,
        integral_fourierChar_orthonormal        the exponentials are orthonormal on `[0,1]`
      intervalIntegral_conj, truncConv_conj,
        convMatrix_conj, convMatrix_im_eq_zero,
        convMatrix_ofReal_re                    the matrix is real
      convMatrix_symm                           the matrix is symmetric — off the diagonal this is
                                                forced by the divided-difference law alone, so no
                                                Fubini is needed
      indexTrigPoly, truncConv_indexTrigPoly,
        integral_indexTrigPoly_normSq            the `L²` norm of a trigonometric polynomial is the
                                                `ℓ²` norm of its coefficients
      integral_indexTrigPoly_truncConv          **the quadratic form is the matrix form**

    RHTower/TruncatedConvolutionParityPacket.lean (continued)
      truncConvModePoly,
        truncConvParityPacket_apply             the packet entries in terms of the matrix
      truncConvParityPacket_form                the compressed sesquilinear form is the
                                                truncated-convolution pairing minus `mu` times the
                                                `L²` pairing
      truncConvParityPacket_isHermitian,
        truncConvParityPacket_posSemidef        the packet is positive semidefinite exactly when the
                                                form dominates `mu` times the `L²` norm on the
                                                compression
      truncConvParityPacket_mulVec_eq_zero_iff  the kernel of the packet is exactly the set of
                                                minimizers of the form

### The analytic scaffolding of the variational assembly is formal

    HTGeometry/TruncatedConvolutionSelfAdjoint.lean
      intervalIntegral_swap_unitSquare          iterated interval integrals of a continuous
                                                function on the unit square commute
      l2Pair, l2Pair_conj, l2Pair_add_right,
        l2Pair_smul_left, l2Pair_smul_right     the `L²` pairing on the unit interval
      truncConv_selfAdjoint                     **the truncated convolution is symmetric** — the
                                                only place Fubini is used
      l2Pair_truncConv_self_im                  its quadratic form is real

    HTGeometry/UnitIntervalFourierProjection.lean
      l2NormSq, l2Pair_self,
        l2Pair_sub_left, l2Pair_sub_right,
        l2Pair_sum_right                        the squared `L²` norm and the sesquilinear algebra
      fourierCoeffOn_eq_l2Pair                  the interval Fourier coefficient is the pairing
                                                against the exponential
      fourierPartialSum,
        l2NormSq_sub_fourierPartialSum          **the mean-square error is the Parseval tail**
      tendsto_l2NormSq_sub_fourierPartialSum    **mean-square convergence of the Fourier partial
                                                sums** — the density statement behind the
                                                compressed approximation

    HTGeometry/TruncatedConvolutionFormBound.lean
      l1Norm, l1Norm_sq_le_l2NormSq,
        l1Norm_le_sqrt_l2NormSq                 Cauchy--Schwarz against the constant one
      norm_l2Pair_truncConv_le, truncConv_sub,
        norm_form_sub_le                        **the form is Lipschitz on `L²` balls**, so an
                                                `L²` approximation of a ground transports to an
                                                approximation of its Rayleigh quotient

    RHTower/TruncatedConvolutionModeBridge.lean
      ccmParityCenteredMode_injective,
        image_ccmParityCenteredMode,
        sum_ccmParityCenteredMode               the centered parity index is the symmetric mode
                                                window
      ccmOddGroundCoeff_mode                    the odd frame is the odd coefficient sequence in
                                                mode coordinates
      indexTrigPoly_eq_ccmTrigPoly,
        integral_ccmTrigPoly_sub_sq             rescaling `[0,1]` to `[0,2π]` identifies the two
                                                trigonometric polynomials and multiplies the
                                                mean-square error by `2π`

    RHTower/TruncatedConvolutionCompressedGround.lean
      truncConvSphere, truncConvRayleigh,
        l2NormSq_truncConvModePoly              the compressed Rayleigh quotient and the fact that
                                                the `L²` norm is the `ℓ²` norm of the coefficients
      isCompact_truncConvSphere,
        exists_truncConv_compressed_ground      **the compressed ground exists**
      truncConvRayleigh_const_mul,
        truncConvRayleigh_min_le                the compressed minimum is a spectral floor
      truncConvParityPacket_posSemidef_of_min   the packet shifted by the compressed minimum is
                                                positive semidefinite
      truncConvParityPacket_ground_mulVec       the compressed ground lies in its kernel

What remains is the selection step: below an isolated spectral gap the compressed kernel is a line,
its generator is odd, the compressed minima converge to the bottom of the form, and the compressed
grounds converge to the ground in mean square.  Every ingredient those four steps consume — the
spectral floor, the kernel characterization, Parseval, and the Lipschitz form bound — is now
formal.
