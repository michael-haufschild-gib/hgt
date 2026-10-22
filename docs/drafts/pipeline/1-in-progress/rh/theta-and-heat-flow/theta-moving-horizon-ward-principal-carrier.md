# Theta moving-horizon / Ward principal carrier

Status: in progress — paper identity proved; Lean formalization active

## Mission

Identify Route P's physical Möbius/Ward half-density with a literal theta-source carrier before
Hilbert completion, preserving every prime label and both reflection orientations.  Then test
whether CCM trace-class crossblocks annihilate the resulting principal class.

## Heavy conjecture loop

1. **Conjecture: Euler--Green polar work is a fixed CCM trace-class displacement under aperture
   dilation.** **FAILED.**  `sourceHorizontalWoldPrimeClockPolarRateWork_eq_eulerGreenDefect`
   identifies the scalar exactly, but the CCM trace-class theorem is pointwise in a Schwartz
   symbol.  Aperture dilation moves that symbol and its controlling Schwartz seminorms.  No
   source-uniform trace budget follows.

2. **Conjecture: Borel Hilbert integrability makes the prime-normal Ward amplitude square
   summable.** **FAILED.**  Fixed-horizon Borel density decays superexponentially at geometric
   prime samples, while moving the horizon restores the physical reciprocal-prime principal
   mass.  The required sampling estimate would divide out precisely that source decay and is
   equivalent to the missing Ward bound.

3. **Conjecture: the missing weak-Hilbert principal carrier is already present in the physical
   theta moving horizon.** **PROVED ON PAPER.**  At prime aperture `L=log p`, Hadamard addition of
   the literal even and odd endpoint channels gives

   ```text
   (E_p + O_p) / (2 k(0)) = exp(-L/2) = p^(-1/2).
   ```

   This is exactly Route N's universal critical amplitude, with no fitted weight.  For centered
   grade `a`, the oriented Möbius/Ward half-density is

   ```text
   sgn(a) (p^(-1/2) - p^(-1/2-|a|)).
   ```

   Hence, away from the wall, it differs from the oriented physical theta endpoint carrier by the
   square-summable twisted amplitude.  At the wall the Ward amplitude is zero and the difference
   is the non-square-summable universal carrier.  Reflection reverses the orientation while
   retaining the same prime labels.

4. **Conjecture: CCM trace class annihilates this carrier without another source law.**
   **FAILED WITH AN EXACT BLOCK SEPARATION.**  Hadamard difference of the same endpoint doublet is
   `p^(-1/2) k(log p)/k(0)`.  It is square summable, and `k(log p)` is literally the diagonal
   kernel value in CCM's explicit Hilbert--Schmidt factorization.  Hadamard sum is the nonsummable
   `p^(-1/2)` principal channel.  A square-summable CCM crossblock correction cannot absorb it.
   Required novelty is therefore a source-derived, non-equivariant block rotation taking the
   Hadamard **sum** into the CCM crossblock before completion.

5. **Conjecture: source reflection identifies the same CCM-visible orientation.** **FAILED WITH
   STRICT SEPARATION.**  Reflection fixes the even aperture endpoint and negates the odd endpoint.
   It therefore swaps Hadamard sum and difference rather than identifying them.  Strict theta-tail
   decay gives `k(log p) < k(0)` at every prime, so the reflected tail channel is strictly smaller
   than the universal channel label by label; no accidental primewise equality is available.

6. **Conjecture: physical aperture transport rotates the universal channel into the CCM
   crossblock.** **FAILED WITH AN EXACT CONNECTION CLASSIFICATION.**  For the left moving-horizon
   window

   ```text
   W(L) = exp(-L/2) (k(0) + k(L)),
   ```

   the half-density covariant derivative `(d/dL + 1/2) W(L)` is exactly
   `exp(-L/2) k'(L)`, the CCM/Hankel tail derivative.  In contrast, the universal boundary mode
   `exp(-L/2) k(0)` lies in the exact kernel of this connection.  At prime apertures its normalized
   samples remain `p^(-1/2)`.  Thus every local differential/curvature receiver erases precisely
   the missing nonsquare-summable class.  The missing law must be an **anchored boundary
   transgression**, not another local curvature identity.

7. **Conjecture: direct sums of the flat boundary mode give moment-neutral hyperbolic index
   amplification.** **FAILED.**  The already formal source rank--trace theorem charges raw positive
   index per faithful block independently of amplitude.  Scaling flat copies keeps prime moments
   small but does not make their index free.

8. **Conjecture: the multiplicative theta translation coboundary selects the flat mode.**
   **FAILED AS AN RH SELECTOR.**  The exact positive-projection translation coboundary produces the
   same `m^(-1/2)` coefficient for every horizontal grade.  Its curvature vanishes identically, so
   passing to the coboundary again discards the grade detector.  Positive survivor: the universal
   prime carrier is simultaneously a physical half-density connection kernel and a translation
   boundary coboundary.  Any successful producer must retain an anchor that distinguishes the two
   reflected source orientations before taking either quotient.

9. **Conjecture: C1's rank-two Green boundary supplies the coefficient-faithful simultaneous
   shared-reservoir landing.** **FAILED BY DIMENSION BEFORE ANY INERTIA ARGUMENT.**  Every nonzero
   theta-source eigenspace is geometrically one-dimensional; the full generalized eigenspace has
   dimension exactly the analytic Xi multiplicity.  The two fixed metric probes observe every
   divisor mode but cannot embed arbitrarily many independently prime-labelled reservoir
   coefficients.  Prime translation creates conormal log-prime jets, not new vectors in a fixed
   compact-source eigenspace.

10. **Conjecture: P-G25's corrected completed response telescopes the flat boundary mode.**
    **FAILED.**  Its identity `E=Q+D/2` is an exact pointed polarization identity, not an upper
    bound, and the completed endpoint kernel has a strictly positive zero-frequency stiffness.
    Moving-horizon differentiation therefore cannot make the signed Dirichlet term disappear.

11. **Conjecture: normalized prime translations act as contractions on the actual theta divisor
    vector, so an off-line Dirichlet character violates the operator norm.** **FAILED AT THE
    CARRIER TYPE.**  Translation diagonalizes the Fourier--Laplace conormal evaluation.  It does
    not act as a bounded contraction on the quantile root vector: the theta source weight is not
    translation invariant, and quantile transport converts translation into an unbounded weighted
    graph in one orientation.  Treating the character as a Hilbert eigenvector repeats the known
    domain error.

12. **Conjecture: constitutive theta--Hasse--KMS balance supplies equality of the reflected
    executions.** **FAILED AS A PRODUCER.**  The universal-law theorem proves strict recovery:
    equality of reflected execution losses selects zero tilt.  It does not prove that the two
    actual Xi executions are equal.  Specializing that equality would restate the missing
    same-fibre law.

13. **Conjecture: the physical moving-horizon carrier and P-G25 completed response live on one
    literal coefficient carrier.** **PROVED IN LEAN.**  The forced P-G25 normalization is exactly

    ```text
    sqrt(p/log p) * (oriented universal theta boundary atom + twisted residual).
    ```

    Functional-equation reflection negates this complete vector prime by prime.  Nevertheless the
    corrected completed-response pairing and its signed prime-ratio Dirichlet energy are each
    reflection-even.  Their mixed forward/reflected bilinear terms are the corresponding
    negatives, while the two separately scalarized Ward budgets add to exactly twice Route P
    packet energy.  This extends the signed-current/positive-polarization split to the actual
    non-diagonal completed source.

14. **Conjecture: clustered exponential moment annihilators make the hyperbolic amplification
    index-free.** **FAILED.**  They cancel signed conormal Taylor moments, but positive block
    formation squares the coefficients; every surviving block still contributes one positive
    index unit.  This is the existing rank--trace price exposed by
    `SourceHorizontalMomentNeutralAmplification`, now seen to persist after arbitrary finite jet
    annihilation.

15. **Conjecture: the Gamma-six shell base-change anomaly and the physical theta boundary atom
    form one coefficient-faithful nonlinear source carrier.** **PROVED IN LEAN.**  At every finite
    shell cutoff, multiply the actual reflected Gamma-six response defect by the literal theta
    moving-horizon Hadamard-sum atom at the same prime label.  These carriers preserve the Xi
    multiplicity copy and negate labelwise under functional-equation reflection.  Their cofinal
    limit is

    ```text
    2 p^(-1/2) F(a(q)),
    ```

    where `F` is the complete Wold prime-clock profile.  Its square is exactly
    `4 F(a(q))^2 / p`; Euler divergence makes the prime-labelled limit square summable exactly
    when `a(q)=0`, equivalently when the theta Green boundary flux vanishes.  This is a literal
    pre-scalarization L/T/P carrier, not an analogy between three RH receivers.  The remaining
    producer has also become stricter: derive admission of this finite-shell limit from a
    source comparison preserving the Gamma-six trace-class remainder.  Assuming its global
    prime-domain admission would already assume an RH-equivalent conclusion.

16. **Conjecture: every finite Gamma-six shell cutoff is already a strict horizontal selector.**
    **FAILED SHARPLY AT THE FIRST CUTOFF; PROVED FOR EVERY LATER CUTOFF IN LEAN.**  At `N=1` the
    only shell clock is one, every normalized moment is one, and the complete odd response is
    identically zero at every grade.  For every `N>=2`, the interior clock `k=1` makes the
    quadratic normalized moment strictly smaller than one.  All Taylor deficits are nonnegative
    and the cubic deficit is strict, so the full finite response is negative for positive grade,
    positive for negative grade, and zero exactly at grade zero.  Thus every fixed nonblind
    finite carrier already has prime-`ell2` admission iff the retained Xi copy is central; no
    cofinal limit is needed for strict selection.

17. **Conjecture: the finite L/T/P carrier is only a post hoc scalar splice.** **FAILED BY AN
    EXACT SOURCE IDENTITY.**  Existing Route-L transgression identifies twice the finite shell
    profile with nonlinear exponent-character evaluation of the literal Gamma-six harmonic
    boundary class, which is unconditionally killed by the linear Kummer exponent regulator
    before any Xi divisor is selected.  The finite theta carrier is exactly this source readout
    times the physical prime half-density.  At the first nonblind cutoff,

    ```text
    D_2(u) = -(sinh(u)-2 sinh(u/2))
           = -2 sinh(u/2)(cosh(u/2)-1).
    ```

    Hence the Route-L source anomaly is precisely the negative Route-N/P dyadic Hellinger sewing
    atom: its odd factor retains reflection orientation while its even factor is the positive
    polarization loss.  Linear regulator nullity therefore cannot be promoted to nonlinear
    physical nullity without the missing strict comparison.

18. **Conjecture: the Gamma-six weak-trace principal class and theta moving-horizon boundary are
    different carriers.** **FAILED BY AN EXACT TWO-CLOCK IDENTIFICATION IN LEAN.**  The normalized
    flat theta boundary mode at doubled shell aperture is

    ```text
    B_theta(2m log 6)/k(0) = 6^(-m),
    ```

    exactly the Gamma-six Green principal eigenvalue.  Shell translation multiplies both by
    `1/6`, and replication over the literal integer shell of size `5*6^m` gives exact trace mass
    five at every depth.  Prime sampling of the same mode gives `p^(-1/2)`.  Prime harmonic
    divergence and Gamma weak-`S1` anomaly are therefore two clock samplings of one
    connection-flat physical source mode.  A successful Frankenstein producer must make the
    regulator-null harmonic boundary undergo an ideal drop from this flat principal mode into the
    CCM/theta tail while preserving its nonlinear coefficient.  Because the first nonblind
    coefficient is `D_2(u)`, such an ideal-preserving chain comparison forces `D_2(u)=0`, hence
    `u=0`.  Construction of that global strict lift on the corrected trace-class remainder remains
    open; it is not supplied by these receiver identities.

19. **Conjecture: ideal drop is only a qualitative reformulation of prime-domain admission.**
    **FAILED; AN ACTUAL OPERATOR-IDEAL CLASSIFICATION IS PROVED IN LEAN.**  Multiply the formalized
    Gamma-six shell principal operator by the finite regulator-null source coefficient `D_N(a)`.
    This operator stays in weak Schatten `S_(1,infinity)` for every Xi copy.  A nonzero scalar
    multiple of the principal operator cannot enter ordinary `S_1`; therefore, for every
    `N>=2`,

    ```text
    D_N(a(q)) G_6 in S_1  iff  a(q)=0.
    ```

    Global trace-class admission of these literal operators is equivalent to RH.  This is the
    precise codomain forced on a completed strict lift: proving its image trace class while
    preserving the source coefficient would finish the argument.  The theorem does not assert
    that the still-missing full corrected-source lift has this image.

## Novelty and hostile audit

- Hedenmalm's 2026 theta spectral paper supplies the source eigenproblem but not this prime-labelled
  moving-horizon principal-class identification.
- Suzuki's screw-function work and CCM quantized calculus supply global receivers/trace-class
  crossblocks, but not the Hadamard endpoint extraction above.
- Internal Route P principal-class results identify an abstract `p^(-1/2)` channel.  New content is
  its exact non-equivariant realization as the normalized sum of the two literal theta aperture
  endpoints on the same source carrier.
- This does **not** prove RH.  It turns the remaining producer into a precise block question:
  derive, from source incidence, a non-equivariant transport sending the Hadamard-sum principal
  channel into the CCM trace-class crossblock.  Ordinary CCM crossblocks see the Hadamard
  difference/theta tail, not the universal endpoint atom.

## Formal targets

- exact moving-horizon universal amplitude equals `routeNGammaSewnUniversalCriticalChannelAmplitude`;
- exact oriented residual equals the signed twisted amplitude;
- residual square summability iff centered grade is nonzero;
- reflection reverses orientation and annihilates the two principal classes labelwise;
- CCM-visible Hadamard difference is square summable and its kernel value is exact;
- Hadamard sum minus CCM-visible difference remains non-square-summable;
- right-horizon reflection swaps Hadamard sum and difference, with strict labelwise separation;
- physical moving-horizon covariant derivative is exactly the CCM/Hankel tail derivative;
- universal boundary mode lies in the exact connection kernel while its prime samples equal the
  Route N critical channel;
- P-G25 normalized profile equals the complete moving-horizon carrier coefficientwise;
- complete profile is reflection-odd, while completed pairing and Dirichlet energy are
  reflection-even and separate reflected budgets double exactly;
- umbrella wiring, direct Lean verification, targeted build, forbidden-declaration and axiom audit.
- finite Gamma-six shell defect times literal theta boundary atom, its cofinal Wold limit,
  reflection law, exact reciprocal-prime square, and strict prime-domain wall.
- sharp finite-cutoff classification (`N=1` blind, every `N>=2` strict), regulator-null harmonic
  source-readout identity, first-cutoff dyadic Hellinger factorization, and finite RH receiver;
- exact doubled-shell identification of theta flat boundary with Gamma-six Green eigenvalue,
  Wold `1/6` translation, and constant shell trace mass five.
- actual weak-`S1` source operator weighted by the finite nonlinear defect, with ordinary
  trace-class membership iff neutral grade and global membership iff RH.

## Current open core

Linear source involution and quadratic Ward completion are now separated on the same literal
carrier.  More sharply, the first nonblind finite source boundary has an exact odd-times-even
dyadic factor and the Gamma weak-trace principal eigenvalue is the same connection-flat theta mode
whose prime samples form the harmonic obstruction.  Folding divisor copies still annihilates every
reflection pair, including off-line pairs, while separate completion doubles escape.  Remaining
producer is a same-fibre, pre-reflection **ideal-drop chain law**: transport the regulator-null
Gamma harmonic boundary through the complete corrected shell source into the CCM/theta tail,
preserve the nonlinear coefficient and both marked orientations, and make the fixed target reader
cyclic on that transported boundary.  Since flat principal and tail ideals are strictly separated,
this forces the finite dyadic coefficient to vanish.  Existing local exceptional incidence does
not preserve the amplified trace-class remainder, so it does not yet supply this law.
