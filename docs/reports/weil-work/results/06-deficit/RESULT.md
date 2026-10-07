# WP06 result register

**Overall verdict: OPEN.** The required zero lower deficit density has not been proved. No application yielding `λ = Λ` or RH has been added.

## Audited Lean results

`WeilWorkDeficitRecovery.lean` proves exact regularized-deficit decomposition and uniform atom recovery over every prefix of a fixed bounded height window. All eight theorem axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Targeted build and final `lake --old env lean` both passed. Umbrella import wired.

Classification: **BRIDGE**. No effective recovery rate as height grows, no upper bound on the actual deficit, no scientific novelty claim.

`WeilWorkDeficitSharedMass.lean` constructs the actual common critical submeasure `χ≤μ,ν` and proves:

- `χ((0,T])=N(T)−D(T)`, with every multiplicity copy retained;
- `‖∫_(0,T] e^(ikr)dμ−∫_(0,T] e^(ikr)dν‖≤M(T)−N(T)+2D(T)` for every real `k,T`.

Here `ν` is the projected actual Xi divisor and `M(T)=μ((0,T])`. Diffuse spectral mass and off-line copies are included. All twelve public theorem axiom audits report only standard Lean foundations. Targeted build and final direct `lake --old env lean` passed without target diagnostics. Umbrella wired. Full audit output is in `lean-audit.log`.

Classification: **EXACT COMPARISON / BRIDGE**. This completes the shared-submeasure comparison step; it does not yet improve the compiled coefficient bound or produce small deficit.

## Active quantitative research

The paper argument in `PROOF.md` improves the existing coefficient factor from `4πn` to `4π√n`, using actual shared critical mass, Poisson endpoint control, and the unconditional Ford–Zaharescu fixed-character theorem. It remains unformalized and is not counted as a Lean result.

The shared-mass Fourier comparison, linear-scale Poisson leakage estimate, and canonical complex Fourier transport are now formalized. The sharper coefficient comparison still needs the actual zero-side transport and horizontal square-moment limit. The full-line transform itself already exists as `HTGeometry.integral_cexp_mul_inv_sq_add_sq`; it was reused.

## Validation limits

Latest completed repository-wide formal lint status is recorded in `EVIDENCE.md`. All seven WP06 modules are umbrella-wired. No full or umbrella build was run. No numerical experiments, heartbeat increases, commits, or added mathematical axioms.

## Verified linear-scale Poisson leakage

Three additional modules extend the logarithmic unit-window mass estimate to arbitrary bounded intervals and prove the full canonical leakage limit:

`(1/T) ∫ |countKernel T r − π 1_(0,T](r)| dμλ(r) → 0`.

The proof retains endpoint atoms and diffuse mass. Endpoint intervals of width `√T` and the remaining bounded interval contribute `O(log T/√T)` after normalization. The distant contribution is bounded by `12∫_(|r|>2T)(1+r²)⁻¹dμλ(r)`, which tends to zero by the corpus's Cauchy-weight integrability. No new scientific hypothesis is used.

Sources: `WeilWorkDeficitMassBounds.lean`, `WeilWorkDeficitPoissonLeakage.lean`, `WeilWorkDeficitLeakageIntegral.lean`. All three unchanged final sources passed direct `lake --old env lean`; targeted builds passed and umbrella imports are wired. All eleven public theorem axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. Repository lint still reports six unrelated unreachable modules; no error in the owned modules.

Classification: **BRIDGE**, not a small-deficit theorem or a claim of scientific novelty. Candidate A's sharper coefficient bound remains paper-only.

Frontier correction: `WeilFibreBochnerLaw` already excludes both signs of the nonzero Cramér-restored profile. The prime-deficit profile escapes the rough-sign test alone, but does not survive the full corpus's fibre constraints.

## Verified canonical Fourier transport

`WeilWorkDeficitFourierTransport.lean` proves, for every full-positive λ and `T≥1`,

`‖∫_0^T e^(ikt) Re Φλ(2+it)dt − π e^(−3|k|/2) ∫_(0,T]e^(ikr)dμλ‖ ≤ ∫ deficitPoissonLeakage T dμλ`.

Consequently its error divided by T tends to zero, even for an arbitrary frequency function `k(T)`. Product integrability and the Fubini exchange are proved for the actual canonical measure. All four public theorem axiom audits report only standard Lean foundations. Targeted build and final direct `lake --old env lean` passed; umbrella wired.

Classification: **BRIDGE**. Forward uniformity in frequency does not justify uniform inversion of the exponentially decaying multiplier and does not recover small atom deficit.

Next cycle: subtract `Φλ−ξ'/ξ` before taking means, then transport the actual zero copies. The corpus already gives a uniform first-displacement tail estimate; a fixed-cutoff square-moment argument suffices, so the stronger exponential estimate need not be rebuilt. Exact arithmetic mean and zero-side proof status are recorded below. The main target stays active throughout.

## Verified arithmetic difference means

`WeilWorkDeficitArithmeticMean.lean` proves, for every σ>1 and n≥2,

`T⁻¹∫_0^T (Re Φλ(σ+it)−Re ξ'/ξ(σ+it)) cos(t log n)dt → (Λ(n)−λ(n))n^(−σ)/2`,

and the zero-frequency difference mean tends to zero. It reuses the exact Dirichlet cosine-series identity and Bohr means, then removes the fixed initial interval. No separate asymptotic assertion about the archimedean term is assumed. Both public theorem axiom audits contain only standard Lean foundations. Targeted build and final direct source audit passed with no target diagnostics; umbrella wired.

Classification: **BRIDGE / CORPUS CONSEQUENCE**. These two means simplify Candidate A's proof dependencies; they do not prove the sharper coefficient inequality or the main deficit target. All seven owned modules are finished, with 37 public theorems audited; no significant new rigidity law is claimed from this infrastructure.
