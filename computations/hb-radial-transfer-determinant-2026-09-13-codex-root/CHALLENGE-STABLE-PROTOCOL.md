# Stable direct finite-part retry: frozen protocol

The first direct-integral challenge failed numerically: subtracting `F(z)-F(0)` naively near `z=0` lost precision, and multiplication by `z^w` amplified roundoff into values of order `1e69`–`1e218`. Its root failures and winding two are rejected as implementation artifacts, not candidate evidence.

This single retry changes only evaluation of the same literal subtraction. Write `d=2s-w`, `C=c0+c1`, `L=log(sqrt(1-z))+d log((1+sqrt(1-z))/2)`, then evaluate

`F(z)-F(0) = 2^d [C expm1(L) - c1 z exp(L)]`.

This is algebraically identical and cancellation-stable. Object, frozen root, precision levels, local contour, gates, physical exclusions and 570-second budget remain those of `CHALLENGE-PROTOCOL.md`. Added controls: compare stable and naive formulas at moderate `z`, record the small-`z` scaled limit, and reject the retry if either fails. No further quadrature tuning is allowed after this run.

Scientific-method mechanics: preserve failed result, identify concrete numerical mechanism, change representation without changing object, and precommit stopping after one stable retry.
