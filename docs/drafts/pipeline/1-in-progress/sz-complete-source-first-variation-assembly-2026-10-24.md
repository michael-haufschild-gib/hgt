# Suzuki: complete critical source first variation

- **Stage:** 1-in-progress (formalization of a dependency-closed paper proof)
- **Parent:** `../2-fully-proven/sz-critical-source-first-variation-2026-10-18.md`
- **Scope:** Finish the literal `suzukiSourceHFinite` first variation, then test
  connections to the broader Lean corpus for an actual source estimate.

## Exact endpoint

For every real compactly supported C² source `f`, let `C = autocorr f` and
`A_w(t) = exp(t/2) * Re(suzukiSourceHFinite w (exp t))`. Prove

`lim_(w→0+) [C(0) - integral_(0,infinity) C(t) A_w(t)] / w
 = Re(weilFullFunctional Λ (weilTest f f))`.

Keep the forming Gamma atom, both polar exponentials, and every prime-power
cusp. All integrability and limiting premises must follow from the stated
source domain. No sign hypothesis, innerness, or RH premise is allowed.

## Work split and verification gates

- [x] Read complete parent paper proof and primary Beta implementation.
- [ ] Use the translated-cusp leaf once its independent ongoing check finishes;
  preserve that worker's edits and avoid duplicate concurrent compilation.
- [ ] Prove the exact logarithmic primary/pole convolution identity.
- [ ] Prove compactly tested pole convergence, keeping the growing exponential
  inside the compact aperture throughout Fubini and dominated convergence.
- [ ] Assemble the locally finite arithmetic source using the common support
  cutoff and `hasDerivAt_suzukiShiftedCoefficient`.
- [ ] Identify Gamma/Lévy/pole/prime normalization with the complete Weil form.
- [ ] Check canonical leaves, audit every public declaration's transitive
  axioms, wire imports without compiling umbrellas.
- [ ] Search the broader corpus for estimates applying to this exact source;
  formalize any substantive premise discharge found.

## Remaining mathematical frontier

The fixed-source first variation supplies an unconditional analytic input. It
does not establish nonnegative first variation, a growing-aperture estimate, or
JAS power-budget positivity. These remain the source-level research targets
after the complete identity is formalized.

## Pole-limit proof refinement

The finite logarithmic identity is being formalized in
`SuzukiCriticalSourceKernel.lean`:

`G_w(t) = B_w(t) - 2w Q_w(t)`,
`Q_w(t) = integral_(0,t) B_w(r) exp((1/2-w)(t-r)) dr`.

To justify the pole limit without a global convolution interchange, use the
primary first moment `L_w = integral_0^infinity r B_w(r) dr`. The existing
compensated-primary convergence theorem gives `L_w → 0`: its required
dominator is integrable because

`r * 2 exp(-r/2)/(1-exp(-2r)) <= (1+2r) exp(-r/2)`.

For `0<w<=1/2`, the truncated exponential weight differs from one by at most
`(1+1/t)r`. Hence its pairing with `B_w` differs from the total mass by at most
`(1+1/t)L_w`. It follows that `Q_w(t)→exp(t/2)` for every `t>0`, while
`0<=Q_w(t)<=M_w exp(t/2)`. Compact support then justifies the tested pole
limit by dominated convergence. This retains the complete growing polar branch.

## Shared-workspace integration

The concurrent `SuzukiCriticalLogKernel` and `SuzukiCriticalPolePairing` leaves
provide the exact log identity and the compact Fubini argument. This assembly
uses those leaves, rather than keeping duplicate declarations. The alternative
first-moment derivation above remains a paper argument; its scratch Lean files
are not part of the certified dependency chain.

Assembly work now owns `SuzukiCriticalWeilNormalization`,
`SuzukiCriticalArithmeticVariation`, and the complete source capstone.

## Broader-corpus checks during assembly

- `SuzukiFiniteShiftGeneratorLimit`: the divided-difference theorem is for the
  exact artificial family `F + delta J`, with nonzero endpoint assumptions.
  It does not supply a literal-source sign estimate or growing-aperture limit.
- `SuzukiWeilFriedrichsOperator`: `suzukiWeilIntervalCovariance_isPositive`
  concerns `boundedPerturbedFormCovariance`, a shifted covariance. The exact
  interval form itself equals `ccmRestrictedWeilForm`. Positivity of that
  unshifted form is not proved by the covariance theorem.
- `CompactFiniteJumpWeilFormula` identifies the full signed spectral form with
  the prime–Gamma–polar physical expression on the finite-jump domain. This is
  being used directly in the complete first-variation capstone, with jump
  integrability discharged from compact C² regularity.
- `CCMRealGramComplexEnergy` splits complex phase-source energies into two real
  energies after reality of the mixed matrix is established. It does not
  remove the need to establish the sign of those real energies.

Draft assembly leaves: `SuzukiCriticalWeilNormalization`,
`SuzukiCriticalArithmeticVariation`, `SuzukiCriticalCuspEstimate`,
`SuzukiCriticalFirstVariation`. No draft theorem is certified until its
canonical Lean check and transitive-axiom audit pass.
