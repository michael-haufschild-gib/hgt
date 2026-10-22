# Xi restricted-Weil floor growth universality law

- **ID:** xi-restricted-weil-floor-growth-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-33 theorem-first scan of `CCMInwardRegularizationFloor.lean`,
  `CCMRestrictedWeilFloorAbscissaTransfer.lean`, and
  `CCMRestrictedWeilFloorGrowthSpectrum.lean`
- **Statement:** Any nonnegative continuous aperture floor whose logarithmic samples envelope the
  restricted Weil negative floor and vanish under RH has one exact two-phase growth law. Under RH,
  its sampled Dirichlet abscissa is bottom, both sampled and aperture logarithmic exponents vanish,
  and its sampled/continuous growth is subpower/subexponential. Under failure of RH, the Xi
  transverse supremum lower-bounds both exponents and the sampled abscissa, while subpower,
  subexponential, and eventual vanishing all fail; monotonicity additionally gives the exact
  abscissa/log-power identity.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and direct consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Three `scripts/formal_tools.py research` searches covered restricted-Weil floors, sampled and
continuous growth exponents, subpower/subexponential criteria, and abscissa transfer. They found
the individual terminal theorems but no theorem joining all presentations into a common phase
law. In particular, no existing declaration states the sampled upper logarithmic exponent's exact
zero criterion.

## Paper proof

Under RH, the supplied vanishing hypothesis makes every sampled coefficient zero. The zero
Dirichlet series has bottom absolute-convergence abscissa; its sampled logarithmic limsup is zero;
and zero functions satisfy every positive-power and positive-exponential bound. The existing
aperture theorem gives the continuous exponent criterion.

If RH fails, the restricted-floor envelope transfers the right-transverse Xi zero spectrum into
the floor. Existing cofinal lower bounds give abscissa at least `1 + xiRightTransverseSup`, both
sampled and aperture exponent at least `xiRightTransverseSup`, failure of subpower and
subexponential growth, and failure of eventual zero. For monotone samples, the generic
nonnegative-coefficient identity sharpens the abscissa to one plus the coefficient log-power
exponent. Since false RH makes `xiRightTransverseSup` positive, a zero sampled exponent is
impossible; this proves the missing sampled zero criterion and makes the two certificates exact
complements.

## Lean formalization

`RHTower/XiRestrictedWeilFloorGrowthUniversalityLaw.lean` defines five- and seven-coordinate
phase certificates, proves the new sampled-exponent zero criterion, identifies each certificate
with RH or its failure, and proves exact complementarity. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiRestrictedWeilFloorGrowthUniversalityLaw.lean
```

passed on the first run.

## Hostile literature noncollision audit

Searches covered Weil positivity, restricted compactly supported test functions, inward/screw
regularizations, RH growth criteria, Dirichlet abscissae, and sampled/continuous logarithmic
types. Connes--Consani explain the compact-support Weil criterion and semilocal trace carrier
([arXiv:2006.13771](https://arxiv.org/abs/2006.13771)). Suzuki's continuous screw-function
framework studies finite-aperture Weil quadratic forms
([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)). Classical Riesz/Hardy--Littlewood
criteria provide different smoothed Möbius growth equivalences
([arXiv:2202.00637](https://arxiv.org/abs/2202.00637)). None defines this restricted negative
floor, transfers its right-transverse Xi supremum simultaneously to sampled and continuous
exponents, or states the resulting exact two-phase certificate. No exact collision was found;
this is not a priority claim.

## Log

- 2026-07-21 — Found bottom-up from terminal restricted-floor theorems. Paper proof closed and
  internal duplicate search passed; Lean implementation started.
- 2026-07-21 — Five-field RH certificate, seven-field failure certificate, and sampled-exponent
  zero connector passed exact direct Lean check on first run. Hostile literature audit found no
  matching common growth-phase law. Exhaustion restarted from augmented corpus.
