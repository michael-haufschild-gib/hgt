# Route P exponential-wall/Xi tau projective-jet no-go

Status: `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Exact claim

Let

```text
D(z) = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z,
L_Xi(z) = canonicalXiSeamLog z.
```

There is no `c : ℂ` for which the analytic germs at zero satisfy

```text
L_Xi(z) = log(D(c z)).
```

Equivalently, no scalar change of the irregular time identifies the normalized exponential-wall
Fredholm tau germ with the canonical Xi seam tau germ.

## Internal frontier

- `[CORPUS]` `routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_one` gives `D_1 = 1`.
- `[CORPUS]` `routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two` gives
  `D_2 = 19/70`.
- `[CORPUS]` `routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_exp` gives the first
  logarithmic curvature `2 D_2 - D_1^2 = -16/35`.
- `[CORPUS]` `canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment` identifies the first two
  Xi logarithmic jets with `m_0 = normalizedPrimeArchMoment 0` and
  `m_1 = normalizedPrimeArchMoment 1`.
- `[CORPUS]` `one_div_twentyFive_lt_normalizedPrimeArchMoment_zero` gives `1/25 < m_0`.
- `[CORPUS]` `normalizedPrimeArchMoment_ratio_lt_nine_div_twoThousand` gives
  `m_1/m_0 < 9/2000`.
- Corpus search found exact wall coefficients but no wall/Xi rescaling no-go or equivalent
  projective tau-jet comparison.

## External frontier

- `[LITERATURE]` Bertola, *The dependence on the monodromy data of the isomonodromic tau
  function*, arXiv:0902.4716 (with corrigendum arXiv:1601.04790), constructs tau variation over
  generalized monodromy/Stokes data. This makes a logarithmic tau jet a genuine Stokes-data
  invariant, not a parity consequence.
- `[LITERATURE]` Its--Lisovyy--Prokhorov, *Monodromy dependence and connection formulae for
  isomonodromic tau functions*, arXiv:1604.03082, treats non-Fuchsian systems and extended
  monodromy data.
- `[LITERATURE]` Yafaev, *Spectral and scattering theory for differential and Hankel operators*,
  arXiv:1511.04683, covers generalized Carleman/Hankel reductions but not this compact
  unit-exponential cubic wall kernel or its Xi comparison.
- Exact-kernel searches for `8 (xy)^(3/2)/(x+y)^3` and its Fredholm determinant returned no
  matching paper. Scientific priority remains subject to independent expert audit.

## Hostile attack

Normalization of tau itself is irrelevant because both logarithms vanish at zero. A scalar
irregular-time change `z -> c z` remains possible, so one ordinary derivative cannot obstruct
matching. The scale-free two-jet ratio is the first legitimate test.

Write `m_n = normalizedPrimeArchMoment n`. From

```text
completedSeamMomentGerm(z) = 2 L_Xi'(-z)
```

and its Taylor coefficients,

```text
L_Xi'(0)  = m_0 / 2,
L_Xi''(0) = -m_1 / 2.
```

For `D(z) = 1 + z + (19/70) z^2 + O(z^3)`,

```text
(log D)'(0)  = 1,
(log D)''(0) = 2(19/70) - 1 = -16/35.
```

If `L_Xi(z) = log D(cz)` as germs, first derivatives force `c = m_0/2`; second derivatives then
force

```text
m_1 = (8/35) m_0^2.                         (forced wall law)
```

But `m_1/m_0 < 9/2000` and `m_0 > 1/25` imply

```text
m_1 < (9/2000)m_0 < (8/35)m_0^2,
```

because `9/2000 < 8/(35*25)`. Contradiction.

## Paper-proof status

Dependency-closed. Both logarithmic jet identities follow from the displayed Taylor expansions;
both strict inequalities are existing unconditional source theorems. No RH statement, divisor
selection, numerical computation, or extra premise enters the proof.

## Failure-driven replacement

The scalar-rescaling conjecture is expected to be `[FALSIFIED]`. Strongest positive survivor:
the projective logarithmic two-jet

```text
J(L) = -L''(0) / (2 L'(0)^2)
```

is invariant under `z -> c z`; the exponential wall has `J = 8/35`, while the canonical Xi seam
has `J = m_1/m_0^2 < 9/80 < 8/35`. Any viable irregular-RH realization must therefore change
even Stokes/monodromy data, not only normalize tau or rescale irregular time.

## Lean status

Formalized in
`GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesExpWallXiTauProjectiveJetNoGo.lean`.
Main declarations:

- `routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_projectiveTwoJet`
- `routePPrimitiveGammaJuliaStokes_canonicalXiSeamLog_projectiveTwoJet`
- `normalizedPrimeArchMoment_projectiveTauJet_lt_expWall`
- `not_routePPrimitiveGammaJuliaStokesExpWallXiTauScalarRescaling`
- `routePPrimitive_GammaJulia_Stokes_expWallXiTau_projectiveJetNoGo`

Targeted `lake env lean` passed. `#print axioms` on every new theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`. Repository lint reports no issue in this module;
its nonzero exit is caused by two pre-existing unreachable `HTGeometry` modules.
