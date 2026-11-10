# Growing moments and polynomial cofactor localization

- **ID:** b13-growing-moment-polynomial-cofactors
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B13; independent centred arithmetic upper bound.

## Target

At `σ=1/2`, `X=exp(at)`, `a>0`, use an order comparable to
`at/log t`, with `U` comparable to `X/t^A`, and polynomial-height
`V,W`. Seek an exponentially small difference between the normalized
pole-subtracted prime moment and the actual centred current restricted
to cofactors `b≤W`. Unlike the fixed-order reduction, this would leave
a cofactor count polynomial in height.

No growing-order result is yet proved. The selected-mode response and
filter constants must also be controlled uniformly; fixed-order big-O
notation cannot justify this limit.

## Quantitative route

The proved derivative recursion is
`C_0(a)=Γ((a+1)/2)/2`,
`C_(k+1)(a)=(|a|+1)C_k(a−1)+8C_k(a+1)`.
For `p≥1`, `k+j≤p`, its quarter-line branch admits the envelope

`C_k(k+2j−1/2) ≤ Γ(1/4) p^p (2p+9)^k / 2`.

The terminal Gamma values satisfy `Γ(j+1/4)≤Γ(1/4) j!≤Γ(1/4)p^p`.
At each preceding branch, the derivative coefficient is at most `2p+1`;
adding the second branch gives the multiplier `2p+9`.
The factorial bound for the even Bernoulli coefficient gives
`K_r,1/2≤C(C₁r^4)^r` for the physical first type-I constant.
The three logarithmic Gamma moments also satisfy
`L_r,1/2≤C(C₂r^3)^r`.

For example, orders comparable to `at/(32 log t)`, `U` comparable to
`X/t^34`, and `V` comparable to `t` leave exponential room in both
errors, provided these constant estimates are proved. Higher-moment
tails require their own uniform factorial estimate before choosing `W`.
These powers are sufficient candidates, not asserted sharp thresholds.

## Arithmetic scope

The corpus's fixed-conductor signed estimates do not control the full
complement: `CriticalWindowsSurviveLowConductorRemoval` preserves every
critical window under removal of a growing low-conductor packet.
The proposed localization therefore does not itself establish the
independent centred-current bound. Any subsequent conductor transfer
must identify and estimate the actual remaining arithmetic component.
B13 remains the objective and is unresolved.

## Uniform constant calculation

For `0<q≤1` and integers `j≤p`, Gamma recurrence gives
`Γ(j+q)≤Γ(q)p^j`; if `p≥1`, this is at most `Γ(q)p^p`.
At depth `k`, the shifted argument is `k+2j−1/2`, with `k+j≤p`.
The two descendants have indices `(k−1,j)` and `(k−1,j+1)`;
their combined multiplier is bounded by `2p+9`.

The corpus supplies
`|B_(2r)|≤[2(2r)!/(2π)^(2r)](1−2/2^(2r))^(-1)`.
For `r≥1`, its factorial-normalized value is at most one. Taking `p=2r`
in the recursion therefore yields the sufficient physical bound

`K_r,1/2≤Γ(1/4)(8192r^4)^r`.

All Gamma values in the logarithmic constant lie at `j+1/4` or `j+3/4`,
with `j≤r+1`. Writing `G=Γ(1/4)+Γ(3/4)` gives the bound

`L_r,1/2≤58G(16r^3)^r`.

Consequently, if `r≤t` and `t≥8192`, the uniform height bounds
are `K_r,1/2≤Γ(1/4)t^(5r)` and `L_r,1/2≤58G t^(4r)`.
These explicit inequalities, rather than fixed-order asymptotics, are the
inputs needed for the growing-order reduction.

## Selected-mode check

For a fixed mode `ρ=β+iγ`, `β>1/2`, write
`z=(ρ−(1/2+it))/2`. Gamma recurrence gives
`Γ(z+r)/Γ(z)=∏_(j<r)(z+j)`. If `t≥2|γ|`, each factor has modulus
at least `t/4`, so the normalization `t^(−r)` loses at most `4^(−r)`.
Orders `r=O(t/log t)` therefore lose only `exp(−o(t))`, while the
mode has the exponential scale factor `exp(a(β−1/2)t)`.
This makes the growing-order detection compatible with the proposed
arithmetic reduction. The exact current/filter transfer remains to be
formalized; no selected-mode estimate is assumed by the constant bounds.


## Proved constant input

`GaussianHigherMomentConstants.lean` proves the quarter-line recursion
bound, the physical lattice envelope, the logarithmic envelope, and both
uniform height bounds. Its five transitive axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`; the direct source check
passes without warnings. The growing-order arithmetic reduction and
cofactor localization are still unproved.

The selected-mode product bound alone does not control the infinite
contour remainder. Its order growth must be paid from the exceptional
abscissa gap. The general target therefore allows `r≈κt/log t` with
arbitrarily small fixed `κ>0`, and cutoff powers depending on `a/κ`.
For `J≥4`, the uniform arithmetic bound should have the form

`C [X^(1/2)/t^((2J−7)r)+t^(4r+2)X^(−1/2)](1+log X)`

whenever `UV t^J≤X`, `V≤t`, and `r≤t`. Conditions
`κ≤a/32` and `(2J−7)κ≥2a` leave exponential room in both terms.
