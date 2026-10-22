# Hedenmalm theta anomaly--Burnol/Gaussian relative splitting

## Metadata

- **Label:** `P-G115`
- **Type:** `[THEOREM (LEAN)] [SOURCE-CANONICAL RELATIVE SPLITTING] [EXACT OBSTRUCTION]`
- **Parents:** `P-G111`, `P-G112`, `P-G113`, `P-G114`, `RiemannSourceForcedHorizontalVanishingFrontier`
- **Status:** source theorem proved and formalized; direct, exact module, axiom, and full umbrella audits passed; repository lint blocked by unrelated pre-existing reachability debt
- **Route:** P (Hedenmalm theta anomaly / Burnol co-Poisson / Gaussian source geometry)

## Frozen conjecture

The prime-tail Gamma/co-Poisson horizontal parameter, equivalently the normalized reflected-Gaussian
line Wronskian, should be the unique affine gauge selecting a source-canonical splitting of the
two-prime completed Burnol singular synthesis. Its critical-line reflection defect should vanish
exactly at critical-line placement.

## Why this is a hard delta

P-G114 classified every two-prime Burnol right inverse as a one-complex-dimensional affine torsor,
but did not canonically select its transverse coordinate. Independently, Gaussian source geometry
already supplied an unsquared, reflection-odd horizontal parameter whose zero set is the critical
line. The missing step was to prove these objects inhabit one exact construction rather than merely
share a zero set.

This card inserts the Gaussian/Gamma source parameter into the Burnol affine torsor and computes the
full relative splitting defect. No fitted coefficient, sign assumption, zero-location premise, or
RH hypothesis is used.

## Theorem package

For each `q : XiZeroCopy`, let

```text
c(q) = riemannSourceGammaCoPoissonHorizontalParameter(q)
b_G(q) = b_*(q) + c(q) (a_3(q), -a_2(q)),
```

where `a_2,a_3` are completed centered Burnol multipliers and `b_*` is the canonical
Moore--Penrose synthesis row.

Lean proves unconditionally:

1. `b_G(q)` reconstructs `1` against the Burnol frame exactly.
2. The unique P-G114 affine gauge extracted from `b_G(q)` is exactly `c(q)`.
3. `c(q)` is the reflected-Gaussian Wronskian divided by the strictly positive Gaussian line-pair
   scale.
4. `c` is real and odd under `xiZeroCopyLineConjEquiv`.
5. Reflection defects of the two synthesis coordinates are exactly
   `-2 c(q) conj(a_3(q))` and `2 c(q) conj(a_2(q))`.
6. Their total squared energy is
   `4 normSq(c(q)) burnolTwoPrimeFrameEnergy(xiSpectralPoint q)`.
7. `c(q) = 0`, zero reflection-defect energy, descent of `b_G`, and
   `Re(q) = 1/2` are equivalent.
8. Global descent of this constructed splitting is equivalent to `RiemannHypothesis`.

## Proof sketch

P-G114's affine synthesis identity gives reconstruction and its gauge inverse gives exact recovery of
`c`. The Gaussian/source frontier identifies the Wronskian as `c` times a nowhere-zero positive
line-pair scale. Burnol completed multipliers are reflection-real while `c` is reflection-odd, so
expanding the affine row produces the two signed coordinate defects. Multiplicativity and conjugation
invariance of `Complex.normSq` reduce their sum to four times `normSq(c)` times frame energy.
P-G112 makes that energy strictly positive, giving faithful vanishing. The existing Gaussian
Wronskian characterization then closes the global equivalence with RH.

## Falsifiers checked

- The Gaussian parameter might fail to define a Burnol synthesis: falsified by exact reconstruction.
- Its affine gauge might differ by an arbitrary unit or scale: falsified by the gauge inverse.
- Reflection could lose the sign after completion: falsified by the explicit two-coordinate defect.
- Defect energy could vanish through a Burnol-frame degeneracy: falsified by strict frame positivity.
- The construction might only report an already-assumed zero location: falsified; all local formulas
  are unconditional and quantified over `XiZeroCopy`.

## Scientific delta

Two previously independent source geometries now construct two explicit splittings of one singular
quotient. Their relative extension class is not an analogy: it is exactly the Gamma/co-Poisson
horizontal parameter, equivalently normalized Gaussian Wronskian. Critical-line placement is exact
equality/descent of these splittings, with a positive faithful defect norm.

This supplies the missing asymmetric singular connector. It does **not** prove its global descent and
therefore does not prove RH. Remaining open core is a source principle forcing this constructed
relative extension class to vanish, not another detector of horizontal displacement.

## Novelty audit

Burnol's co-Poisson and conductor-operator papers establish the Mellin/co-Poisson framework and
critical-line spectral structures. Targeted primary-source searches found no published construction
identifying the finite-prime completed Burnol Bezout torsor with the normalized Gaussian line
Wronskian, nor the exact affine splitting-defect energy above. General affine right-inverse algebra is
standard; claimed novelty is the exact source weld and faithful relative-extension formula.

Primary comparisons:

- J.-F. Burnol, *Entrelacement de co-Poisson* (2003).
- J.-F. Burnol, *On Fourier and Zeta(s)* (2007).
- J.-F. Burnol, *The Explicit Formula and a Propagator* (2002).
- J.-F. Burnol, *The Conductor Operator and the Riemann Hypothesis* (2004).

## Formal artifact

`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaAnomalyBurnolGaussianRelativeSplitting.lean`

Imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Verification log

- 2026-08-13 — Frozen after P-G114 exposed affine gauge as sole reflection-odd coordinate.
- 2026-08-13 — Direct `lake env lean` check passed.
- 2026-08-13 — Exact `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolGaussianRelativeSplitting` passed (`12937` jobs).
- 2026-08-13 — Axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`; full RHTower umbrella build passed (`19790` jobs).
- 2026-08-13 — Repository lint failed on 41 pre-existing unrelated unreachable modules; no P-G115--P-G117 module appeared in failures.
