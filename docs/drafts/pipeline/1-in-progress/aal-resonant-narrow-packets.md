# Resonant narrow packets against a finite top layer

- **ID:** aal-resonant-narrow-packets
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Test whether higher-order cardinal-spline alias notches permit two narrow resonant packets to detect a finite top layer within the proved arithmetic positivity range.

## Candidate mechanism

For a top depth `δ=β*−1/2>0`, separate two packets by `log B` and normalize each packet to fixed integral. Their width is `ε`. Place their centers at integer effective overlap, where the complete alias density vanishes. A cardinal spline of order `m` has candidate alias-notch order `q=2m−1`.

The scales to prove or reject are: negative top-layer pairing of order `B^δ`, archimedean self-cost of order `ε^(-1) log(1/ε)`, and alias cost of order `(log N) ε^(q−1)`. If the arithmetic positivity range permits `B≈(log N)^α` and `ε=(log N)^(-d)`, separation requires

`d<αδ`, and `1−d(q−1)<αδ`.

Such a `d` exists exactly when `αδq>1`. None of these packet estimates or the requisite profile-dependent positivity range is asserted proved here.

## Existing constraint

The checked fourth-denominator spline families have `q=7`, even after arbitrarily many extra individual harmonic zeros. The current whole-matrix bound has `α=1/8`. Thus these families do not satisfy the candidate scale inequality for `0<δ<1/2`.

## Open input

Determine the actual dependence of the certified arithmetic positivity exponent `α` on the profile's complete alias-notch order. A positivity range obtained from a lower Gamma reserve must be checked for the same profile; transferring the cubic-spline exponent without proof is invalid. The finite bulk and all packet cross-terms also require estimates before any AAL conclusion.

## Exact obstruction to universal profile transfer

For `φ(u)=ψ(2u)+ψ(2u−1)`, alternating translates at overlap two satisfy

`Σ_(j<m) (−1)^j φ((v−j)/2)=ψ(v)−(−1)^m ψ(v−m)`.

The checked local Gamma Gram law transfers the constant endpoint energy to the literal integer horizon. With `ψ=tiltedUnitSpline`, `resonantTiltedSpline_certificate` excludes every uniform positive logarithmic Gamma reserve by coefficient mass at this fixed overlap. The surviving Gram is tridiagonal: diagonal `2∫ψ²`, adjacent entries `∫ψ²`, all others zero.

See `../3-formalized/local-gamma-grams-detect-spline-resonances.md`. This settles the universal reserve-transfer claim, not full Weil positivity or the higher-order resonant-packet candidate. A replacement argument must control the synthesized source or its local Gram rather than assume a coefficient-mass floor.
