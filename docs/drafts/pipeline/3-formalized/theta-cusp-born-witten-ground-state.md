# Theta-cusp Born/Witten ground-state value law

- **ID:** `theta-cusp-born-witten-ground-state`
- **Stage:** 3-formalized
- **Type:** `[PROVEN] [PHYSICS VALUE BRIDGE] [LEAN] [DIRECT CONSUMER]`
- **Physics source:** supersymmetric quantum mechanics, Witten-Laplacian factorization, and
  boundary Brascamp--Lieb coercivity.
- **Lean source:** `PrimeArchThetaBornWittenGroundState.lean`,
  `PrimeArchThetaBornWittenBootstrap.lean`, and `PrimeArchThetaBornWittenSourceMoment.lean`.

## Claim

For one positive theta atom, write

```text
t_n(x) = pi (n exp x)^2,
q_n(x) = W_(5/4),n(x) - 1/4 = t_n(x) - 3/2,
psi_n(x) = thetaCuspMorseGroundState n x.
```

On the theta half-line, `q_n` is strictly positive.  Define the Born amplitude and its Witten
superpotential by

```text
chi_n(x) = 2 sqrt(q_n(x)) psi_n(x),
B_n(x) = W_(5/4),n(x) - t_n(x) / q_n(x).
```

Then the observable-weighted Morse state is itself an exact supersymmetric zero mode:

```text
(d/dx + B_n) chi_n = 0.                                  (Z)
```

Its square is exactly the theta source value rather than merely a comparable density:

```text
thetaCuspSourceTerm x n = pi * chi_n(x)^2.                (S)
```

The new superpotential has the exact curvature

```text
B_n'(x) = 2 t_n(x) + 3 t_n(x) / q_n(x)^2.                (C)
```

Consequently `B_n' >= 2 pi n^2` on `x>=0`; the logarithmic Born-density curvature is
`2 B_n' >= 4 pi n^2`, and the supersymmetric partner potential `B_n^2+B_n'` has the same
`2 pi n^2` pointwise floor.

## Direct corpus application

Equation `(S)` turns every existing Born moment into an ordinary position moment of one exact
Witten ground state:

```text
thetaCuspMorseBornMoment j n
  = integral_(0,infinity) x^(2j) * chi_n(x)^2 dx.
```

It also rewrites every atom and full theta-cusp raw moment as a sum of pure-state position moments.
Thus quantum moment matrices, supercharge constraints, and boundary Witten/Brascamp--Lieb estimates
can act on the exact current values without an extra positive observable insertion.

This is a static value relation.  It does not posit a spectral realization of Xi or use a hidden
evolution parameter.  It does not by itself prove either buffered first-atom inequality.

## Physics references

- Laliberte--McPeak, *Bootstrapping supersymmetric (matrix) quantum mechanics*,
  <https://arxiv.org/abs/2510.01356>.
- Le Peutrec, *On Witten Laplacians and Brascamp--Lieb's inequality on manifolds with boundary*,
  <https://arxiv.org/abs/1607.08714>.
- Berenstein--Hulsey, *Anomalous Bootstrap on the half line*,
  <https://arxiv.org/abs/2206.01765>.

The literature supplies the supersymmetric factorization, moment-matrix, and boundary-coercivity
mechanisms.  The theta-specific amplitude, source identity, curvature, and moment transport must be
proved directly in Lean.

## Formalization

The three Lean modules prove:

- `thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq`, the atomwise source identity `(S)`;
- `thetaCuspFullSource_eq_pi_mul_tsum_bornWittenAmplitude_sq`, its full-source pure-state sum;
- `thetaCuspBornWitten_supercharge_zero` and
  `thetaCuspBornWitten_factorized_schrodinger_zero`, the exact zero-mode equations;
- `hasDerivAt_thetaCuspBornWittenSuperpotential` and
  `thetaCuspBornWittenCurvature_floor`, the curvature formula `(C)` and its floor;
- `hasDerivAt_thetaCuspBornWittenLogDensityPotential` and
  `thetaCuspBornWittenLogCurvature_floor`, the literal negative-log-density derivative chain and
  the `4 pi n^2` logarithmic-curvature floor;
- `thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq`,
  `thetaCuspAtomRawEvenMoment_eq_integral_bornWittenAmplitude_sq`, and
  `thetaCuspRawEvenMoment_eq_tsum_integral_bornWittenAmplitude_sq`, the existing moment transports;
- `iteratedDeriv_XiC_zero_eq_tsum_bornWittenAmplitude_sq`, the direct all-order even-jet interface
  to the existing central Taylor and cumulant corpus;
- `thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment` and
  `normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource`, the compact full-family moment
  interface and its first exact normalized prime--archimedean source-value consumer;
- `thetaCuspBornWitten_robinDefect_eq_zero_iff` and
  `thetaCuspBornWittenMomentTestPolynomial_robinDefect`, the polynomial bootstrap-domain
  classification and unique zeroth-order contact anomaly;
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenAmplitude`, the direct pure-state
  formulation of the two remaining inequalities and their existing linear Hankel conclusion.

The principal declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] current formal and failed-route corpus checked
- [x] primary supersymmetric-bootstrap and boundary-Witten sources identified
- [x] exact current Born-moment and Hankel consumers identified
- [x] formalize `q_n`, `chi_n`, and `B_n`
- [x] prove positivity of `q_n` on the half-line
- [x] prove the square/source identity `(S)`
- [x] prove the zero-mode relation `(Z)`
- [x] prove the curvature identity and floor `(C)`
- [x] prove the Born, atom, and full raw-moment transports
- [x] connect the pure-state moment form to the two existing Hankel hypotheses
- [x] connect the full pure-state moment family to the even central jets and first normalized
      prime--archimedean source value
- [ ] prove either buffered first-atom inequality
- [ ] RH
