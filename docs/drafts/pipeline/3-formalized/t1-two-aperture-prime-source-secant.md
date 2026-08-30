# T1 two-aperture prime-source secant

- **ID:** T1-PRIME-SECANT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` Route T1 (read-only)
- **Statement:** Two distinct reciprocal Levinson apertures recover, by an exact coefficient secant, the cofinite true-prime Dirichlet source whose fixed Xi-mass cone bound is equivalent to RH.

## Goal and RH proof chain

Route T1 chain attacked:

`smooth AFE / reciprocal Levinson detector family`
`-> two-aperture coefficient secant`
`-> cofinite true-prime Dirichlet cone plus one fixed finite prime packet`
`-> XiMassCriticalTruePrimeDirichletConePairingLineBound`
`-> RiemannHypothesis`.

This attacks the coefficient-faithful source-to-detector landing gate, not another detector-energy
constant.  Exact target is an unconditional RH equivalence in which the receiver polynomial is
written with literal Levinson detector coefficients at two fixed apertures.  The remaining burden
after this landing must be only uniform control of that actual detector-secant pairing.

## Corpus provenance

- `[CORPUS]` `levinsonLinearMollifiedCriticalDetectorCoeff_eq` gives the exact differentiated
  Barban--Vehov coefficient.
- `[CORPUS]` `levinsonLinearMollifiedCriticalDetectorCoeff_eq_vonMangoldt` shows that reciprocal
  tuning annihilates ordinary primes inside the mollifier range because `(Lambda*Lambda)(p)=0`.
- `[CORPUS]` `xiMassCriticalTruePrimeCone_eq_integral_dirichlet` identifies the moving true-prime
  cone with its literal finite Dirichlet polynomial pairing.
- `[CORPUS]`
  `riemannHypothesis_iff_xiMassCriticalTruePrimeDirichletConePairingLineBound` proves that uniform
  boundedness of that pairing is equivalent to RH.
- `[CORPUS]` `norm_xiMassCenteredPrimeAtom_le_verticalBound` supplies a uniform-in-height bound for
  every fixed prime atom, hence fixed finite prime packets are harmless.
- `[LOCAL-RESEARCH]` Required searches found no theorem evaluating a reciprocal detector
  coefficient at a prime outside its aperture, no aperture-secant theorem, and no detector-level
  landing into the true-prime Xi-mass cone.

## Literature audit

Checked primary literature on Levinson mollifiers, multi-piece/unequal-length mollifiers,
Barban--Vehov weights, and modern short mollifiers.  These sources optimize moments or mollifier
shape.  No checked source states the reciprocal-aperture prime coefficient, its two-aperture
secant, the cofinite von-Mangoldt recovery, or the resulting fixed Xi-mass/RH landing.  Exact-title
and formula searches for two mollifier lengths, reciprocal logarithms, scale derivatives, and
von-Mangoldt recovery returned no matching result. Final adversarial search after theorem freeze
found no matching result as of 2026-08-30.

## Conjecture loop

1. `[FALSIFIED C1]` One reciprocal-tuned aperture lands coefficient-faithfully on the true-prime
   source.
   Killing mechanism: for every prime `p <= M`, the exact short-range formula is proportional to
   `(Lambda*Lambda)(p)=0`, whereas the true-prime source coefficient is `Lambda(p)/sqrt(p) != 0`.
2. `[LEAN-PROVED C2]` If `1 < M1 < M2 < p` and `p` is prime, then
   `c(M2,p)-c(M1,p) = (1/log M1-1/log M2) * Lambda(p)/sqrt(p)`, where
   `c(M,p)` is the detector coefficient at tuning `1/log M`.
3. `[LEAN-PROVED C3]` Summing C2 over the moving prime cone gives an exact carrier identity:
   the detector secant is the nonzero aperture slope times the full true-prime polynomial minus
   one fixed finite prime prefix.
4. `[LEAN-PROVED C4]` The fixed prefix is uniformly bounded in vertical time, so the
   detector-secant pairing line bound is equivalent to the existing true-prime pairing line bound,
   and therefore to RH.

## Attack and hostile checks

For prime `p > M`, only divisor `1` survives the Barban--Vehov aperture.  Thus

`c(M,p) = (1-log(p)/log(M))/sqrt(p)`.

Taking the secant in reciprocal log-aperture cancels the constant term and leaves the exact
von-Mangoldt prime weight.  Distinct apertures above `1` make the slope nonzero.  Primes at or below
the larger aperture form a fixed finite packet; corpus vertical atom bounds pay it uniformly.

Hostile conditions:

- prove the outside-aperture divisor evaluation from literal definitions; do not infer it from the
  short-range formula;
- retain strict endpoint inequalities, since a prime exactly at the aperture contributes a second
  divisor;
- prove the reciprocal-log slope is nonzero from strict aperture order;
- do not divide by the slope until nonvanishing is established;
- keep the polynomial identity coefficient-by-coefficient and prime-labelled;
- the final theorem may transfer an RH-equivalent line bound, but may not assume RH or a hidden
  prime/Xi estimate;
- no computation or numerical experiment may enter the proof.

## Paper proof

1. If `p` is prime and `M < p`, then `p.divisors = {1,p}`. The aperture kills the `p` divisor,
   while the unit divisor gives `barbanVehovCoeff M p = log M` and
   `barbanVehovLogMomentCoeff M p = 0`. Substitution into the exact detector coefficient gives
   `c(M,p)=(1-log(p)/log(M))/sqrt(p)`.
2. Subtract the evaluations at `M2` and `M1`. Constant terms cancel and
   `c(M2,p)-c(M1,p)=(1/log(M1)-1/log(M2))*log(p)/sqrt(p)`. At a prime,
   `Lambda(p)=log(p)`. Strict monotonicity of `log` makes this slope positive and nonzero.
3. Multiply C2 by the literal Xi-mass Fourier profile and sum over moving-cone primes above
   `M2`. Splitting the full prime index set at `M2` proves
   `detectorSecant = slope * (truePrimeCone - fixedPrefixCone)` exactly.
4. Every term in the moving prefix is a prime atom with label at most `M2`. The corpus atom bound,
   monotonicity of `log`, and the fact that at most `M2` labels occur give the uniform bound
   `norm(prefixCone) <= M2*log(M2)*xiMassVerticalBound(sigma)`.
5. Nonzero scalar multiplication and a uniformly bounded additive prefix preserve and reflect
   line boundedness. Combining this equivalence with
   `riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound` proves C4 and the RH capstone.

Every step is unconditional. No RH consequence, zero-density estimate, prime-distribution
hypothesis, numerical experiment, or new axiom is used.

## Novel result and changed frontier

The formal result is not an optimized detector constant. It changes the carrier ontology:
one reciprocal detector vector provably loses the primitive-prime source, while the scale secant
of two detector vectors recovers the complete cofinite RH-equivalent source exactly. Thus T1's
smooth-AFE-to-fixed-Weil landing needs coherent aperture variation, not a single tuned aperture.

The exact surviving T1 premise is now uniform boundedness of
`xiMassLevinsonReciprocalPrimeSecantCone` for any fixed legal aperture pair. Proving that explicit
detector-family bound closes the existing true-prime Xi-mass RH chain.

## Formal status

`[LEAN-PROVED]` Module `XiMassLevinsonPrimeSecantLanding` proves:

- single-aperture prime erasure;
- exterior-prime coefficient evaluation;
- exact two-aperture von-Mangoldt secant;
- exact moving-cone landing modulo fixed prefix;
- uniform fixed-prefix bound;
- detector-secant/true-prime line-bound equivalence;
- `riemannHypothesis_iff_xiMassLevinsonReciprocalPrimeSecantConeLineBound`.

Targeted `lake env lean` and module-only `lake build` pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Repository lint still exits red solely on unrelated
pre-existing unwired modules; it reports no forbidden declaration or wiring defect for this module.
Frontier map remained read-only by this work.

## No-go closure for C1

- **Exact killing mechanism:** reciprocal tuning cancels the primitive-prime channel throughout
  one aperture.
- **Strongest positive survivor:** the detector family is affine in reciprocal log-aperture on
  every fixed exterior prime, and its two-aperture secant is exactly the prime source coefficient.
- **New insight:** the source is encoded in scale variation of the detector family, not in one
  detector vector.  T1 landing therefore needs two coherent apertures.
- **Status:** C1 killed in Lean; strongest survivor C2--C4 dependency-closed and formalized in
  `XiMassLevinsonPrimeSecantLanding`.

## Log

- 2026-08-30 — created in 1-in-progress after corpus and literature hostile audit; C1 falsified,
  C2--C4 frozen.
- 2026-08-30 — C1 killed and C2--C4 proved unconditionally in Lean; moved to 3-formalized.
