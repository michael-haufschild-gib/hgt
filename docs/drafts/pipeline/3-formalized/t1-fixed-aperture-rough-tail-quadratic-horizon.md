# T1 Fixed-Aperture Rough-Tail Quadratic Horizon

- **ID:** T1-ROUGH-HORIZON
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` route T1; `XiMassLevinsonPrimeSecantLanding.lean`
- **Statement:** Fixed finite reciprocal Levinson apertures have a rank-two affine rough tail and cannot isolate the true-prime half-density beyond the quadratic aperture horizon.

## Goal

Close or kill the hidden selection step in the route-T1 chain

`literal detector coefficients → true-prime Xi-mass cone → uniform cone bound → RH`.

The existing two-aperture landing first filters to true primes. This card tests whether that filter
can arise from the detector family itself. Success would discharge `LAND`; failure must classify
the strongest detector-native source and the exact scale law a surviving co-moving route requires.

## Gates

- [x] 0 → 1 in-progress: exact coefficient question; source-pure detector family; corpus and SOTA audit
- [x] 1 → 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, targeted build green, axiom audit green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, independent priority audit

## Internal frontier

- `[CORPUS]` `levinsonLinearMollifiedCriticalDetectorCoeff_eq` gives the exact Barban--Vehov
  coefficient and divisor-log moment.
- `[CORPUS]` `rough_window_coeff_eq_lam_one` proves every divisor-window carrier is constant on its
  rough support.
- `[CORPUS]` `rough_eq_one_or_prime` proves an `M`-rough integer at most `M²` is `1` or prime.
- `[CORPUS]` `levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_secant` recovers the prime
  half-density outside two apertures, but only after primality is supplied.
- `[LOCAL-RESEARCH]` `riemannHypothesis_iff_xiMassLevinsonReciprocalPrimeSecantConeLineBound` lands
  the explicitly prime-filtered secant cone and makes its uniform bound equivalent to RH.

## External frontier

- `[LITERATURE]` Friedlander--Iwaniec's asymptotic-sieve paper records the classical parity barrier:
  ordinary sieve information cannot generally distinguish primes from almost primes
  ([Annals 148 (1998)](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/Annals/148_3/fried1.pdf)).
- `[LITERATURE]` Current Levinson-mollifier work optimizes derivative combinations and mollified
  moments ([Short mollifiers of the Riemann zeta-function](https://arxiv.org/abs/2508.11108));
  current Barban--Vehov work estimates their aggregate weights
  ([Ramaré](https://ramare-olivier.github.io/Maths/SelbergIdentity-KVOR-21-withbib.pdf)). The checked
  sources do not state the exact reciprocal-aperture rough-tail rank, prime-square no-go, or sharp
  quadratic source horizon.
- The exact priority claim remains provisional pending independent expert audit.

## Frozen conjecture and hostile attack

### C1 — affine rough-tail law

`[PAPER-PROVED]` Let `S` be any finite family of legal apertures, all at most `M`, and let `α_S` be
arbitrary complex weights. On every `M`-rough nonzero index `n`,

`Σ_{L∈S} α_L c_L(n) = (A - B log n) / sqrt n`,

where `A = Σ α_L` and `B = Σ α_L / log L`.

The exact finite-sum identity is paper-proved below.

### C2 — fixed-aperture no-go

`[PAPER-PROVED]` No fixed finite reciprocal-aperture linear combination agrees with the true-prime
half-density on all sufficiently rough indices. Two exterior primes force the affine tail to be
`log n / sqrt n`; an exterior prime square then gives a nonzero detector coefficient at a nonprime
index.

The counterexample is uniform in the finite aperture and weights.

### C3 — positive survivor

`[PAPER-PROVED]` The obstruction is sharp: on the `M`-rough sector below `M²`, every nonunit is prime,
so any prime-correct affine detector is coefficient-faithful there. Above `M²`, exterior prime
squares force contamination. Therefore a detector-native co-moving landing must maintain
`source cutoff ≤ aperture²` or subtract prime powers through an independent source law.

The quadratic-horizon classification is paper-proved below.

## Complete paper proof

Let `c_L(n)` denote the reciprocal-tuned detector coefficient with aperture `L`, and say `n` is
`M`-rough when every prime divisor of `n` is greater than `M`.

1. Fix `L ≤ M`, `1 < L`, and a positive `M`-rough integer `n`. Any divisor `d | n` with `d ≤ L`
   must equal `1`: otherwise `minFac(d)` is a prime divisor of `n`, is at most `d ≤ L ≤ M`, and
   contradicts roughness. Therefore the Barban--Vehov divisor sum has only its unit term,
   `b_L(n)=log L`, while its divisor-log moment is zero.
2. Substitute these identities into the exact detector-coefficient formula. Since `log L ≠ 0`,
   `c_L(n)=(1-log n/log L)/sqrt n`.
3. For a finite family `S` and complex weights `α_L`, sum the preceding equality. With
   `A=Σ_{L∈S} α_L` and `B=Σ_{L∈S} α_L/log L`,
   `F(n)=Σ α_L c_L(n)=(A-B log n)/sqrt n`. This proves C1.
4. Suppose `F` agrees with `log p/sqrt p` on every `M`-rough prime. Choose distinct primes
   `p,q>M`. Multiplying the two equalities by their positive square roots gives
   `A-B log p=log p` and `A-B log q=log q`. Subtraction yields
   `(B+1)(log q-log p)=0`. Distinct positive primes have distinct logarithms, hence `B=-1`, and
   either equation gives `A=0`. Thus `F(n)=log n/sqrt n` on every positive `M`-rough integer.
5. Choose a prime `r>M`. Then `r²` is `M`-rough and composite, but
   `F(r²)=log(r²)/sqrt(r²) ≠ 0`; the true-prime half-density is zero there. Contradiction. This
   proves C2 and kills every fixed finite linear-aperture prime extractor.
6. If instead `0<n≤M²` is `M`-rough, `rough_eq_one_or_prime` gives `n=1` or `n` prime. Hence the
   universal logarithmic rough-tail profile agrees with true-prime support throughout this region.
   Every rough composite lies strictly above `M²`, while the squares of primes above `M` supply
   counterexamples beyond it. This proves C3 and sharpness of the quadratic horizon.

No analytic estimate, RH instance, zero data, or unproved number-theoretic premise enters the
argument.

## No-go closure

- **Exact killing theorem/mechanism:** Fixed finite linear aperture data have rank-two affine tail
  on rough indices. Prime agreement forces the universal logarithmic profile, which is nonzero on
  every exterior prime square.
- **Strongest positive survivor:** The same profile is prime-faithful on the entire rough sector
  through `M²`; this boundary is sharp.
- **New insight:** Aperture must be a co-moving resolution variable satisfying
  `source cutoff ≤ aperture²`, or the route must independently subtract prime powers. Fixed
  detector scales cannot supply T1's true-prime projector.
- **Status:** `[LEAN-PROVED]` in
  `GaloisForLFunctions.RHTower.XiMassLevinsonRoughTailHorizon`; exact priority remains provisional
  pending independent expert audit.

## Lean certificate

- `levinsonReciprocalDetectorCombinationCoeff_eq_affine_of_rough` — arbitrary finite complex
  aperture combination has rank-two affine rough tail.
- `intercept_eq_zero_and_logSlope_eq_neg_one_of_primeCorrectOnRoughTail` — two exterior prime
  values rigidly force the universal logarithmic profile.
- `not_forall_levinsonReciprocalDetectorCombinationCoeff_eq_truePrime_of_rough` — general fixed
  finite linear-aperture no-go.
- `levinsonReciprocalMollifiedCriticalDetectorCoeff_secant_eq_truePrime_of_rough_le_sq` — exact
  quadratic-horizon survivor for the literal two-aperture secant.
- `exists_primeSquare_rough_levinsonReciprocalSecant_ne_truePrime` — explicit uniform exterior
  prime-square obstruction.
- `lake env lean GaloisForLFunctions/RHTower/XiMassLevinsonRoughTailHorizon.lean` — PASS.
- `lake build GaloisForLFunctions.RHTower.XiMassLevinsonRoughTailHorizon` — PASS, target only.
- Axiom audit for rank, no-go, survivor, and counterexample theorems: only `propext`,
  `Classical.choice`, `Quot.sound`.
- Global lint remains red only on pre-existing unreachable modules outside this card; it reports no
  forbidden declaration or wiring error for this module.

## Log

- 2026-08-30 — Created after the two-aperture landing exposed an unproved true-prime projection.
- 2026-08-30 — C1--C3 dependency-closed on paper; fixed finite linear landing branch killed.
- 2026-08-30 — Exact no-go and sharp survivor formalized, wired, target-built, and axiom-audited.
