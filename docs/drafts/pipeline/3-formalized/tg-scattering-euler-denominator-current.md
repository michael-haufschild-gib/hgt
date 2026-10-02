# TG C9.11g — clear Euler denominators in the actual joint current

- **Stage:** 3-formalized
- **Type:** PROVED in Lean; finite comparison and exact fixed-carrier boundary
- **Route:** TG, source-to-relative-projection comparison.

## Corpus inputs

- `FieldOneFiniteStageConnesMarcolliLocalRatio.primeRatio_eq_localLFactor_ratio`:
  the prime phase is the Euler-factor ratio at t and -t.
- `HardyTitchmarshSourceTransport.evenPrimeLocalFactor`: the physical polynomial
  `A_p=1-p^(-1/2)D_p*`, with exact positive Euler Gram.
- `HardyTitchmarshEulerConcrete.evenPrimeLocalFactor_isUnit`: A_p is boundedly invertible.
- C9.11f's finite spherical construction retains all Euler ratios in V_S and
  targets `D_S=V_S*R₁V_S+A₁-1` on the actual physical carrier.

## New conjecture

For one prime, prove the literal physical ratio relation `V_p A_p=A_p*`.
With `Δ_p=V_p* R₁ V_p-R₁`, clear denominators without a scalar normalization:

`A_p* Δ_p A_p = A_p R₁ A_p* - A_p* R₁ A_p`.

Then extend to the complete finite Euler polynomial A_S, retaining every mixed
prime term. The resulting difference of two actual source Grams is a concrete
four-leg current representative for the twisted Fourier projection pair.

The clearing identity needs only `V_p A_p=A_p*`: adjointing gives `A_p* V_p*=A_p`.
Thus its proof uses no operator inverse and no separate normality assumption.
This matters at a cofinal stage: the four source legs can remain meaningful even
when a uniformly bounded inverse of the Euler polynomial is unavailable. Actual
cofinal admission and cubic-index compatibility still require proof.

## Why this is the next hard comparison

The mixed unitary representation alone gives a generic compression sign, not the
TG cyclic transgression. This identity should compare the literal scattering
projection pair with the existing physical Euler/Burnol source currents. Whether
the nonunitary denominator congruence admits a provenance-retaining cofinal
relative class and preserves the required cubic index is not assumed. Those are
the hard analytic/geometric questions after the exact finite identity.

## Log

- 2026-10-02: direct lexical corpus search for `evenPrimeLocalFactor` and `primeRatio`
  located the exact factor, invertibility and scalar-ratio theorems. Orientation
  checked from source: phase numerator is A_p(-t), denominator A_p(t), hence A_p*/A_p.
  Deep search for periodic Hardy compactness was partial and did not establish an
  applicable theorem; no noncompactness claim is made.
- 2026-10-02 continuation: constructing A_S as the product of actual
  `ccmPlaceEulerDenominator` factors over `S.toList`, with exact Mellin symbol
  `∏v∈S semilocalPrimeSymbol p_v`. Symbol commutativity removes enumeration dependence
  at the operator level; no noncommutative product is silently treated as commutative.
  Both the polynomial and its adjoint Mellin formulas are under Lean audit.

## New boundary issue exposed by the source

The forward-dilation adjoint of each Euler denominator preserves the complement
of the unit Fourier cutoff. The existing exact cutoff covariance therefore suggests
`R₁ A_S* Q_b=0` for b≥1. If established, the cleared current compressed on Q_b is
`-(R₁ A_S Q_b)*(R₁ A_S Q_b)`, whereas the original projection difference compressed
there is the positive Gram of `R₁ V_S Q_b`. Denominator congruence consequently
cannot be silently treated as preserving the fixed Sonin compression. Its source
carrier must be transported too. This is a conjectured exact carrier distinction,
not yet a proved nonvanishing statement or a retirement of TG.

## Verified outcome — 2026-10-02

All claims above are now formalized in `CCMFiniteEulerDenominator` and
`CCMScatteringEulerCurrent`. The full finite physical polynomial and its adjoint
have their literal Mellin symbols; `V_S A_S=A_S*` is proved for every finite S.
The relative current is exactly `δ_S=V_S*R₁V_S−R₁`, and its inverse-free congruence
is `A_S*δ_S A_S=J_S=A_S R₁ A_S*−A_S*R₁ A_S`.

On Q_b, b≥1, the exact signs are
`Q_b δ_S Q_b=(R₁V_SQ_b)*(R₁V_SQ_b)` and
`Q_b J_S Q_b=−(R₁A_SQ_b)*(R₁A_SQ_b)`.
Their equality is equivalent to **both boundary maps being zero**. This is the
sharp positive classification exposed by the apparent sign obstruction; no
nonvanishing premise was inserted. Nonunitary congruence must transport the
carrier, and cannot be identified with an unchanged Sonin compression.

Fourteen public theorems and five definitions pass foreground leaf audits with
`lake --old env lean ... -o ...`; all nineteen public axiom queries return only
`propext`, `Classical.choice`, `Quot.sound`. Both modules are umbrella-wired;
default heartbeats, no full build, no added axioms or numerical experiment.

Next hard attack: `tg-euler-denominator-cofinal-carrier` seeks the exact finite
anisotropic carrier and decides whether its common core across all primes is
zero. Cofinal relative-ideal admission, cubic-index compatibility, and the
sub-unit law remain unproved. This is not an RH proof or a retirement of TG.
