# Completed prime--Gamma left-half accretivity to RH

- **ID:** `completed-prime-gamma-left-half-accretivity-to-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[RH-SUFFICIENT SOURCE ROUTE]`
- **Source:** `PrimeArchAntiHerglotzGate.lean`, `XiWeilOneCauchyGate.lean`,
  `CCMCompletedPrimeGammaAccretivityCriterion.lean`, `XiRelativeResolventFlux.lean`,
  `CompletedPrimeFluxFittingAttachment.lean`, and the corpus-wide carrier Pick machinery
- **Statement:** A source-only proof that the completed continued prime--Gamma flux is accretive on
  the left half of the critical strip proves RH.

## Goal

Prove, without using the Xi divisor, Weil positivity, or an RH-equivalent moment form, that

```text
0 <= Re(infinitePrimeFlux(s) - logDeriv(archFactor)(s))
```

whenever

```text
0 < Re(s) < 1/2  and  riemannZeta(s) != 0.                 (A)
```

Lean now proves the exact equivalence chain

```text
RH
  iff (A)
  iff the centered continued prime--archimedean trace is anti-Herglotz
  iff every upper-half-strip one-Cauchy source diagonal is nonnegative.
```

The open problem is not to assume `(A)` under another name. It is to produce its sign from an
independent positive source construction.

## Gates

- [x] 0 -> 1 in-progress: source-pure inequality and pole-exclusion mechanism isolated
- [ ] 1 -> 2 fully-proven: derive `(A)` from a positive prime--Gamma or theta representation
- [ ] 2 -> 3 formalized: formalize that source producer and compose it with the existing Lean gate
- [ ] 3 -> 4 publication-ready: standalone source proof, non-circularity audit, and Lean certificate

## Lean endpoint already proved

`formal/GaloisForLFunctions/RHTower/PrimeArchAntiHerglotzGate.lean` and
`formal/GaloisForLFunctions/RHTower/CCMCompletedPrimeGammaAccretivityCriterion.lean` define

```text
CompletedPrimeGammaLeftHalfAccretive
ContinuedPrimeArchUpperAntiHerglotz
```

and prove

```text
CompletedPrimeGammaLeftHalfAccretive
  iff ContinuedPrimeArchUpperAntiHerglotz
  iff RiemannHypothesis.
```

The second implication is a local pole argument with full zero multiplicity. If a right-half Xi
zero exists, reflect it into `0 < Re(s) < 1/2` and approach it from the right by
`s_n = s_0 + 1/(n+1)`. The normalized logarithmic derivative satisfies

```text
(s_n-s_0) logDeriv(xi)(s_n) -> ord_(s_0)(xi) > 0.
```

Hence `Re logDeriv(xi)(s_n) > 0`. Under the centered change of variables this makes the continued
source trace have strictly positive imaginary part, contradicting anti-Herglotzness.

## Positive source producers to investigate

1. **Prime--Gamma Loewner representation.** Construct, before reading the Xi divisor, a positive
   kernel or positive measure whose Cauchy transform is
   `-(continuedPrimeArchSourceRelativeTrace)`. Positivity immediately supplies `(A)`.
2. **Theta total positivity.** Use the exact theta-cusp Fourier representation of `XiC` to prove a
   translation-determinant or variation-diminishing property strong enough to make its negative
   logarithmic derivative Herglotz. Plain log-concavity is insufficient.
3. **Semilocal coherent Gram limit.** Produce the one-point Pick diagonal as a limit of genuine
   prime--archimedean Gram energies. The construction must retain the principal Euler shell, the
   unsquared `m log p` response, and the Gamma channel.

## Non-circularity gate

The bare assertion `(A)` is a criterion, not an RH proof. A successful producer must establish its
sign from source geometry before invoking any identity with `XiC`, and may not use:

- the Xi zero divisor or a measure supported on it;
- trace-Hankel or Weil positivity already equivalent to RH;
- a factorization whose existence is itself equivalent to real-rootedness;
- a polynomial-dependent Gram norm chosen after evaluating the target sign.

The criterion becomes a live proof route only when one of the three positive producers is closed.

## Log

- 2026-07-12 -- Full-corpus top-down sweep joined the continued prime--Gamma trace to the scalar
  Pick pole-witness mechanism and formalized the local multiplicity-exact implication to RH.

## Producer audit against the full formal corpus

The unconditional carrier in `HTGeometry/PrimeLogHerglotz.lean` does not discharge the premise.
Its dyadic weights were chosen for global absolute convergence and facet-sewn HT geometry; they are
not the arithmetic von-Mangoldt weights.

The exact Euler-log prime-power Herglotz measure is arithmetically correct in the Euler region, but
the formal theorem

```text
not_summable_primeLogHerglotzTransportMassOrder_of_pos
```

shows that every positive exponential transport toward the critical line diverges even after every
fixed finite order of logarithmic cancellation. The Gamma diagonal repairs the finite-Cauchy domain,
but the paper-proved Radon--Nikodym audit shows that the critical von-Mangoldt correction is
cofinally unbounded and that the required divided difference is an exponential Loewner kernel, not
the Euler Cauchy product.

The positive surviving producer is therefore sharper:

```text
canonical closed causal/anti-causal prime--Gamma graph
  -> distinguished Sonin compression with a source-selected relative trace
  -> nonnegative exponential Loewner diagonal on the left half-strip
  -> CompletedPrimeGammaLeftHalfAccretive
  -> RH.
```

The first new theorem to seek is a relative trace-slope domination bound for that distinguished
compression. It must control the unbounded critical recession while retaining the archimedean
boundary channel. The existing positive-transport wall proves that no bounded diagonal transport or
finite logarithmic renormalization can substitute for this theorem.

## Countable Gaussian-rational reduction

`[PROVED IN LEAN]` The global source inequality need only be checked at Gaussian-rational points.
Define

```text
s_(a,b)=a+i b,  (a,b) in Q^2.
```

If the completed prime--Gamma flux has nonnegative real part at every regular `s_(a,b)` with
`0<a<1/2`, then it is accretive throughout the regular left half-strip. Gaussian rationals are
dense, and the completed flux is continuous wherever `zeta` is nonzero, so any strict negative
value would persist on an open ball containing a Gaussian-rational witness.

The strengthened formal equivalence is

```text
CompletedPrimeGammaGaussianRatLeftHalfAccretive
  iff CompletedPrimeGammaLeftHalfAccretive
  iff ContinuedPrimeArchUpperAntiHerglotz
  iff RiemannHypothesis.
```

The still weaker exact criterion in `PrimeArchSourceUpperBoundGate.lean` requires only

```text
exists L, every regular Gaussian-rational left-half-strip value satisfies
  L <= Re(completedPrimeGammaFlux(s)).
```

Lean proves this countable finite-lower-floor condition equivalent to RH. Thus the open source
theorem is not necessarily a countable family of nonnegative values: any independently produced
uniform finite floor suffices.

## Corpus-wide producer boundary

The search surface is the whole `formal/GaloisForLFunctions/` tree, not only `RHTower/`. Several
non-RHTower modules sharpen the open source theorem without discharging it:

- `FredholmDeterminantZeta.lean` and `FredholmDeterminantEuler.lean` realize the Euler source on
  `Re(s)>1` as the logarithmic derivative of a genuine diagonal Fredholm determinant. They supply
  the canonical prime-side operator before continuation, but their trace-class disk does not reach
  the critical strip.
- `RHTower/XiShiftPrimeExposure.lean` now proves an exact strict source sign for the actual
  von-Mangoldt carrier: on every real `sigma > 1`, the rationally renormalized `+2` shift defect of
  `xi'/xi` is positive.  This removes source positivity at the Euler anchor as a hypothesis.  The
  remaining theorem is a continuation-domination statement carrying that marked sign from the
  real Euler ray to the required left-half-strip accretivity; real-axis positivity alone does not
  supply such propagation.
- `HTGeometry/PrimeLogCauchyJetControllability.lean` proves that finitely supported real variations
  of positive prime-log masses realize every finite complex Cauchy-jet packet at upper-half-plane
  nodes. Consequently no condition depending only on finitely many local prime-mass jets can force
  the required sign. Positively, an RH-capable producer must use an infinite tail coupling or a
  distinguished global compression.
- `HTGeometry/PrimeLogCauchySeamRank.lean` proves that every nonzero finite packet of transported
  Cauchy sections has nonsummable positive exponential energy. Positively, the source construction
  must retain infinite renormalization rank; no finite packet of counterterms can continue the
  Euler Cauchy carrier to the strip.
- `ReflectedDigammaAnomaly.lean` gives a faithful archimedean selector: at nonzero height its
  reflected anomaly is real exactly on the critical line. This identifies the correct Gamma
  channel, but a source theorem must still force the combined prime--Gamma relative trace to have
  the required sign or reality.
- `../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/finite-euler-connection-cauchy-phase-chambers.md`
  identifies the finite-place orientation exactly: the literal one-sided prime contribution is
  one half of an FE-paired radial difference of disk Poisson kernels, with a closed phase threshold,
  and every finite nonempty packet visits both signs.  Hence the missing completion theorem is a
  phase-locked Gamma/cofinal compensation inequality, not positivity of the finite Euler
  connection.
- `FinitePrimeBoundaryTransfer.lean` proves the cofinal implication from sub-log-square reflected
  prime energy to horizontal pinning. It remains a second compatible endpoint: a source-side
  construction producing that energy bound would feed the same critical-line conclusion without
  first naming the continued logarithmic derivative.
- `SchwartzSpectralMeasureForm.lean` constructs positive translation-invariant Schwartz forms from
  positive tempered spectral measures. This supplies the positive-form direction of the
  theta/Hedenmalm lane, but divisor-complete nullity or an exact prime--Gamma source identification
  is still required before it can imply RH.

Together these theorems select the surviving positive architecture more tightly:

```text
Euler Fredholm determinant on Re(s)>1
  + full coherent Gamma covariance
  + infinite-rank, source-selected Sonin/relative compression
  + continuation preserving the exponential Loewner diagonal
  -> countable Gaussian-rational prime--Gamma accretivity
  -> RH.
```

This is not a finite-dimensional Gram problem. The new theorem to prove must control the joint
prime--Gamma tail while preserving the exact source marking through continuation.
