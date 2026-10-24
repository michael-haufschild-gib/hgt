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
