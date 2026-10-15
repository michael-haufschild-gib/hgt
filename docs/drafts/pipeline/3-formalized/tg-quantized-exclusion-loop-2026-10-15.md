# TG: native arithmetic source bound to quantized zero exclusion

Status: FORMALIZED BRIDGE; NATIVE ARITHMETIC PRODUCER IN PROGRESS.
Parent objective: unconditional Lean RH via TG.
User target: convert quantitative arithmetic source control into actual zero
exclusion, not another identification of a spectral index.

## Exact statement

For a>0, any finite C satisfying

    for every M, some N>=M has ||soninPrimePolarGridSource a N||²<=C

forces RiemannHypothesis. Equivalently, it suffices to prove finiteness of

    E = sum_n A_n²/((n+2)(n+3)),
    A_n = sum_{k<=n} (primeIndicator(k+2)-soninPolarGroundCellMass(k)).

All coefficients and polar cell masses are the original ones. No native
arithmetic bound is proved here. The separate safe-Euler cubic budget <1
has not been compared to this physical norm and cannot be substituted for E.

The same implication holds when the bound is imposed directly on the literal
continuous-cell source. Paper transfer: its difference from the grid is a
convergent correction e_N. Eventually ||e_N||<=||e||+1, so at bounded returns
the grid norm squared is at most 2*C+2*(||e||+1)^2. Taking returns beyond both
the requested cutoff and this eventual threshold supplies the grid criterion.

## Dependency-closed paper proof

1. SoninPrimePolarCofinalGroundEnergy turns E finite into ONE cofinal strong
   limit f of the literal continuous-cell source at aperture 1. Its admitted
   discretization correction retains the original polar integrals.
2. For u>=0 the entering ground interval has head Mellin transform
   exp(-s*u)/s. The continuous head Mellin functional therefore takes every
   finite prime-polar cell assembly to its exact scalar arithmetic assembly.
3. F(s)=s*soninHeadMellin(f,s) is holomorphic on Re s>1/2 and is the cofinal
   scalar limit there. Its value is bounded by
   |s|*||soninHeadMellinCLM s||*||f||. The same f supplies every frequency.
4. On Re s>1, absolute convergence of the prime series and of the original
   polar integral gives F=P-I, where P is prime zeta and

       I(s)=integral_{log 2}^infinity (exp u+1)/u * exp(-s*u) du.

   Finite polar cells telescope exactly. No ordinary Dirichlet convergence
   assertion on the larger half-plane is made.
5. Dominated differentiation gives, with b=log 2,

       -I'(s)=C_b(s)=exp(-(s-1)*b)/(s-1)+exp(-s*b)/s.

   Hence A(s)=-F'(s)+C_b(s) equals the valuation-one prime current on Re s>1.
   This identity is derived from admission, not assumed separately.
6. A and the existing higher-valuation correction H are analytic on
   U={Re s>1/2} minus {1}. U is preconnected by the existing convex-minus-
   countable theorem. The division-free identity

       zeta'(s)+(A(s)+H(s))*zeta(s)=0

   holds on the Euler chamber, hence throughout U. Zeta is not identically
   zero, since zeta(2) is nonzero.
7. At a hypothetical strict-right zero rho, zeta has an isolated zero and
   rho!=1. The identity gives A=xiPrimeLogDirichletContinuation on a punctured
   neighborhood. Continuity of A forces (s-rho)*A(s) to tend to zero.
   The existing exact residue theorem instead gives limit -m, where m is a
   natural number with m>=1. Contradiction. Existing zeta symmetry then gives
   RH, hence every strict-right formation count is zero.

Any finite C suffices. Quantization enters through m>=1, and the native bound
prevents a nonzero residue from forming. No global logarithm, lower bound on
|Xi|, frequency-dependent source limit, or zero-free endpoint is assumed.

## Corpus and novelty audit

FormationAnchoredCubicEndpoint already proves the subunit trace-norm zero
gate. RestrictedProjectionIndexOperatorNormCriterion already gives its
oriented seam criterion. RestrictedUnitaryCubicRelativeIndexSubunit proves a
safe-Euler source budget <1 but no comparison to the literal completed seam.
The new argument connects native source admission directly to the certified
first-prime residue, bypassing that unproved operator comparison.

Classification: BRIDGE. Standard complex analysis and certified multiplicity
are reused; no claim of a new field or literature novelty. External literature
and numerical experiments omitted under user instructions. This is not an
unconditional RH proof. Native source-energy control remains the hard
arithmetic obligation; a conditional conversion must not be counted as it.

## Lean implementation and verification

- SoninPrimePolarHeadMellin.lean: exact finite-cell identity, analyticity,
  physical norm bound, and cofinal scalar limit. Direct Lean check and targeted
  build passed without own diagnostics.
- SoninPrimePolarEulerHead.lean: exact Euler limit, original polar derivative,
  and first-prime current identity from admission. Direct Lean check and
  targeted build passed without own diagnostics.
- SoninPrimePolarResidueExclusion.lean: division-free continuation and integer
  residue contradiction; final native-energy and cofinal-bound implications.
  Direct Lean check passed without diagnostics for all three forms: energy,
  grid returns, and literal continuous-cell returns. Targeted build passed
  (13201 jobs); final direct Lean check passed without diagnostics.
- SoninDampedPrimePolarCurrent.lean: expose existing private head_dilated_band
  as public soninHeadMellin_dilated_bandIndicator; update both uses. Targeted
  build and final direct Lean check passed without diagnostics. No mathematical
  change to the existing proof.
- Scratch axiom audits passed for the finite-cell identity, source current
  identity, finite-energy implication, grid-return implication, and original
  continuous-cell return implication. Each uses only propext, Classical.choice,
  Quot.sound. No new axioms, placeholders, heartbeat increases, or numerical
  experiments. Whitespace check passed.
- All three new leaves imported in RHTower.lean. Current repository lint has
  one unrelated error: EvenSectorNegPartAbelRigidity is unreachable from the
  umbrella. No change to that concurrent module was made.

Closed-selector work stays deferred: its verified closedness theorem does not
supply the missing arithmetic cancellation. Do not expand that side problem.
With this conversion verified, continue attacking native E itself and the
missing comparison with available arithmetic source estimates. RH goal remains
active.

Producer audit for the next cycle: the exact grid norm is
2*a*(sum_{n<=N} E_n + A_N^2/(N+3)). A sign change or small endpoint A_N only
controls the terminal square; it does not control the accumulated nonnegative
energy. Littlewood crossings therefore do not supply bounded source returns.
The needed arithmetic mechanism must control the complete signed prime-polar
coherence, including its cumulative history. Do not replace it with diagonal
prime weights or an assumed holomorphic continuation.
