# Completed prime--Gamma moment far-right asymptotic

- **ID:** `completed-prime-gamma-moment-far-right-asymptotic`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED IN LEAN] [PROOF-CONTRIBUTING]`
- **Statement:** Every normalized odd completed logarithmic-derivative moment has its exact
  unconditional far-right limit, so even factorization is the only remaining input in the moving
  polynomial RH chain.

## Theorem

For every `k`, Lean proves

\[
x^{2k+1}\operatorname{Re}\left(
\frac{(-1)^k}{(2k+1)!}
\left(\frac{\xi'}{\xi}\right)^{(2k+1)}(x)
\right)
\longrightarrow \frac{(-1)^k}{2(2k+1)}.
\]

The rational polar channel is one inverse power smaller, the Euler channel is exponentially
small after first-prime normalization, and the half-argument Gamma channel supplies the full
leading constant through the formalized Hurwitz--polygamma asymptotic.

## Top-down consequence

`riemannHypothesis_of_completedPolynomial_evenFactorization` proves

\[
\text{completed moving polynomial right-even factorization}\Longrightarrow RH.
\]

Thus no far-right sign or limiting-measure hypothesis remains.

## Lean

`formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMomentFarRightAsymptotic.lean`, imported by
the `RHTower` umbrella.

## Gates

- [x] rational channel limit
- [x] Gamma channel limit
- [x] Euler channel limit
- [x] full completed-moment limit
- [x] scalar limit converted to every finite polynomial far-right anchor
- [x] RH capstone wired
- [ ] source proof of even real-root factorization
