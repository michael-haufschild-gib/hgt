# Finite spectral-trace no-go for the Riemann xi function

- **ID:** `finite-spectral-trace-xi-nogo`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[FORMALIZED] [UNCONDITIONAL] [BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/FiniteSpectralTraceNoGo.lean`
- **Statement:** No finite atomic resolvent trace with arbitrary complex weights is globally
  equal to the actual completed-zeta logarithmic derivative `xi'/xi`.

## Exact theorem

For a finite support `S subset C` and arbitrary weights `w : C -> C`, define

`finiteSpectralTrace(S,w;s) = sum_(rho in S) w(rho)/(s-rho)`.

Lean proves

`not (forall s, logDeriv xi s = finiteSpectralTrace(S,w;s))`.

The capstone is `RHTower.xi_logDeriv_ne_finiteSpectralTrace`.

The proof uses the unconditional infinite xi divisor from `XiZerosInfinite` and the exact
simple-pole theorem for `xi'/xi`.  Every finite support misses a chosen actual xi zero.  The
finite trace is analytic there, so its meromorphic order is nonnegative, whereas `xi'/xi` has
order `-1`.  Global equality is impossible.

## Route consequences

This theorem excludes the following precise finite implementations:

1. **Hilbert--Polya:** a finite-dimensional operator whose characteristic determinant is
   claimed to be `xi` or whose resolvent trace is claimed to be `xi'/xi`;
2. **Connes trace formulas:** a finite atomic/finitely ranked spectral carrier claimed to
   reproduce the completed logarithmic derivative exactly;
3. **de Branges/canonical systems:** a finite spectral support or finite characteristic
   determinant claimed to carry the full xi divisor;
4. **finite Fredholm or transfer determinants:** any reduction whose exact logarithmic
   determinant derivative is a finite weighted sum of simple resolvent poles.

Repeated eigenvalues are allowed: their algebraic multiplicities are absorbed into the complex
weights.  Non-diagonal finite matrices are also covered at the trace-of-resolvent level because
the logarithmic derivative of the characteristic polynomial has one weighted simple pole per
distinct eigenvalue.

The theorem does **not** exclude infinite-dimensional Hilbert--Polya, Connes, de Branges,
Fredholm-determinant, or canonical-system routes.  Such infinite objects are exactly what the
infinite divisor requires.

## Scientific status

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The route boundary is useful and completely formal,
but it is the direct finite-versus-infinite pole obstruction, not a new scientific law.

## Verification

- `lake build GaloisForLFunctions.RHTower.FiniteSpectralTraceNoGo` passed.
- Scratch `#print axioms` for all declarations reports only
  `[propext, Classical.choice, Quot.sound]`.
- The project formal lint passes.

## Gates

- [x] 0 -> 1: exact finite spectral model and no-go statement
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete claim formalized in Lean; narrow build and axiom audit pass
- [ ] 3 -> 4: not a standalone publication target

## Log

- 2026-07-11 -- Formalized the finite atomic trace, existence of an actual xi zero outside
  every finite support, analyticity off the support, and the global no-go theorem.  Route
  consequences restricted explicitly to finite implementations.
