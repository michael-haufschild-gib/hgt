# Route-P two-step wild saddle gives trace-class Xi relocation

- **ID:** IRH-P-TWO-STEP-WILD-SADDLE-TRACE-RELOCATION
- **Stage:** 3-formalized
- **Type:** CONSTRUCTIVE BRIDGE
- **Source:** prime-labelled Route-P second wild jet; enhanced Fourier–Laplace stationary phase;
  two logarithmic fixed-point steps for the RVM wild saddle
- **Statement:** A target-free two-step logarithmic saddle counterterm differs in `ℓ¹` from the
  exact smooth RVM reciprocal carrier and therefore differs by Schatten-1 from the actual ordered
  reciprocal-Xi operator.

## Goal

Upgrade principal-density matching to determinant-grade trace-class relocation without reading Xi
zeros into source operator.

## Gates

- [x] 0 → 1 in-progress: exact candidate fixed; corpus and primary-literature audits complete
- [x] 1 → 2 fully-proven: dependency-closed scalar remainder and summability proof
- [x] 2 → 3 formalized: Lean theorem, direct check, umbrella wiring, new-axiom audit
- [ ] 3 → 4 publication-ready: standalone note and external novelty review pending

## Audit

- `[CORPUS]` Actual ordered reciprocal-Xi operator already differs by Schatten-1 from exact smooth
  RVM quantile operator, but smooth quantile remains defined implicitly.
- `[CORPUS]` Source-pure second wild jet matches only principal `log n/n` density. Its unrenormalized
  next correction has wrong `log log n/n` sign and cannot support a trace-class comparison.
- `[CORPUS]` No two-step fixed-point, Lambert-W, or explicit logarithmic RVM counterterm theorem was
  found.
- `[LITERATURE]` Enhanced irregular Riemann–Hilbert/Fourier–Sato theory transports exponential
  factors by stationary-phase geometry; Stokes data retain resulting exponential components.
- `[LITERATURE]` Corless–Gonnet–Hare–Jeffrey–Knuth give the large-argument Lambert-W expansion
  `W(x)=L₁-L₂+L₂/L₁+O(L₂²/L₁²)`. Two fixed-point steps encode enough of this
  expansion for a summable reciprocal defect.
- `[NOVELTY STATUS]` `[BRIDGE]`: no source found connecting this explicit wild-saddle counterterm to
  trace-class reciprocal-Xi relocation; no external-priority claim.

## Exact theorem `[PAPER PROOF COMPLETE]`

For `N_n=n+1/8`, cap only finitely many low modes so `N_n≥exp 3`, and put

```text
L_n  = log(N_n/e),
u₁,n = L_n - log L_n,
u₂,n = L_n - log u₁,n,
r_n  = u₂,n/(2πN_n).
```

Use `+r_{π(p)}` and `-r_{π(p)}` on two signed prime sectors, producing `R₂`. Then

```text
∑_p |r_{π(p)} - routeKPrimeRVMReciprocal(p)| < ∞,
R₂ - routeKSignedPrimeRVMOperator ∈ S₁,
xiOrderedSignedPrimeOperator - R₂ ∈ S₁.
```

## Proof route under audit

Writing `q_n` for smooth RVM quantile and `u_n=log(q_n/(2πe))`, exact RVM equation gives

```text
u_n + log u_n = L_n,
q_n⁻¹ = u_n/(2πN_n).
```

For large `L`, `u₁≤u≤L`, `u₁≥L/2`, and two applications of logarithm's local Lipschitz
bound give

```text
0 ≤ u₂-u ≤ 4 log(L)/L².
```

Thus reciprocal defect is `O(log L/(N L²))`, hence `O(1/(N L^(3/2)))`. PNT comparison with
`p_n ~ n log n` reduces summability to the proven prime tail
`∑_p 1/(p (log p)^(1/2)) < ∞`.

## Dependency-closed proof

1. Smooth RVM quantile `q_n` satisfies
   `q_n/(2π) log(q_n/(2πe)) = n+1/8`. Thus for
   `u_n=log(q_n/(2πe))`, `N_n=n+1/8`, and `L_n=log(N_n/e)`,
   `u_n+log u_n=L_n` and `q_n⁻¹=u_n/(2πN_n)` exactly.
2. On `L≥2`, positivity and fixed-point equation give `1<u`,
   `L-log L≤u≤L`, and `L-log L≥L/2`.
3. Applying `log x≤x-1` first to `L/u`, then to `u/(L-log L)`, proves
   `0≤u₂-u≤4 log L/L²` for `u₂=L-log(L-log L)`.
4. Finite cap is eventually inactive. Hence explicit reciprocal defect is nonnegative and bounded
   by `(4 log L/L²)/(2πN)`. The elementary bound `log L≤2√L` reduces this to
   `O(1/(N L^(3/2)))`.
5. PNT gives eventually `p_n≤2n log n` and `log p_n≤2 log n`; also
   `L_n≥(log n)/2`. Therefore defect is bounded by
   `128/[p_n√(log p_n)]`. Proven prime reciprocal-log summability closes `ℓ¹`.
6. Signed duplication preserves absolute summability. The explicit diagonal minus smooth RVM
   diagonal is Schatten-1. Subtracting this from existing Xi-minus-RVM Schatten-1 relocation gives
   `xiOrderedSignedPrimeOperator-R₂∈S₁` by ideal closure.

## Hostile-audit result

- Cap `max(exp 3,n+1/8)` affects finitely many modes and is absent from every cofinal identity.
- Source multiplier uses only prime rank, `π`, `e`, and two real logarithmic iterations. No Xi
  ordinate, Xi zero count, or fitted spectral datum occurs.
- Signed correction is proved by exact diagonal equality; singular-value comparison is not used to
  infer operator difference.
- Two iterations are quantitatively essential for this proof: one leaves an
  `O(log L/(N L))`-scale defect, while second supplies summable `L^(-3/2)` gain.
- Result gives trace-class relocation and determinant-grade perturbation class, not equality of
  determinants, equality of spectra, or RH.

## Lean formalization

- Module: `GaloisForLFunctions.RHTower.RoutePTwoStepWildSaddleTraceClassRelocation`.
- Capstone: `routeP_twoStepWildSaddle_traceClassXiRelocation`.
- Source-to-Xi theorem:
  `xiOrderedSignedPrimeOperator_sub_routePTwoStepWildSaddleSignedOperator_memSchattenClass_one`.
- Direct module check: passed with `lake env lean`.
- Umbrella import: wired into `GaloisForLFunctions.RHTower`.
- New-declaration axiom audit: all 35 new theorems depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom introduced.
- Deliberately skipped `lake build`: previous exact-target checks replayed 13,283 dependencies;
  direct source check is targeted verification.

## Hostile audit targets

- Low-mode cap must be finite and absent from cofinal estimates.
- Counterterm may use prime rank and universal RVM constants only; no Xi ordinate or zero count.
- Need exact signed diagonal identity, not approximation-number inference.
- Trace-class relocation transfers regularized determinant availability, not determinant equality.
- If scalar remainder cannot be closed without a new analytic assumption, retire route and record
  strongest non-trivial asymptotic survivor.

## References

- Andrea D'Agnolo, Marco Hien, Giovanni Morando, Claude Sabbah, *Topological computation of some
  Stokes phenomena on the affine line*, Ann. Inst. Fourier 70 (2020), 739–808.
- Andrea D'Agnolo and Masaki Kashiwara, *Riemann–Hilbert correspondence for holonomic D-modules*,
  Publ. Math. IHÉS 123 (2016), 69–197.
- Robert M. Corless, Gaston H. Gonnet, D. E. G. Hare, David J. Jeffrey, Donald E. Knuth,
  *On the Lambert W Function*, Adv. Comput. Math. 5 (1996), 329–359.

## Log

- 2026-08-25 — exact two-step wild-saddle counterterm fixed after corpus and literature audits;
  moved to `1-in-progress`.
- 2026-08-25 — exact fixed-point identity, two-step remainder, PNT/prime-tail summability, and
  hostile audit complete; moved to `2-fully-proven`.
- 2026-08-25 — source operator, trace-class Xi relocation, direct module check, umbrella wiring,
  and new-declaration axiom audit complete; moved to `3-formalized`.
