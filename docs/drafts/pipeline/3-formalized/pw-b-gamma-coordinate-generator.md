# PW-B actual Möbius coordinate generator

- **ID:** PW-B-GAMMA-COORDINATE-GENERATOR-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The complete Möbius coefficient family has coordinate derivative `M_b/(2*x)-M_(b-1)` and log-coordinate derivative `M_b/2-x*M_(b-1)`. The weight `x` exactly compensates the parameter shift in the global atom-norm admission boundary. For `Re(b)>0`, the full weighted shift and weighted coordinate derivative are integrable, with exact masses `3/2*integral M_b` and `-integral M_b`.

## Actual source and derivative proof

Retain `Q(x)=sqrt(x)*exp(-x)` on the positive ray and the original family

`A_b(n,x)=mu(n)*exp(-b*log(n))*Q(n*x)`,
`M_b(x)=sum_n A_b(n,x)`.

The zero-index atom vanishes. For positive indices the exponential identity
and `exp(log(n))=n` give exactly `A_(b-1)(n,x)=n*A_b(n,x)`.
The already-admitted original Gamma derivative, composed with `log(n*x)`,
then gives `partial_x A_b=A_b/(2*x)-A_(b-1)`.

For `0<a<=y<=c` and `n>0`, monotonicity of the square root and exponential gives

`norm Q(n*y) <= sqrt(c)/sqrt(a)*norm Q(n*a)`.

Choose an integer `N` bounding both `norm b` and `norm(b-1)`. The actual
coefficient norms are at most `n^N`; consequently the derivative atoms
are bounded on this interval by

`(1/(2*a)+1)*sqrt(c)/sqrt(a)*n^N*norm Q(n*a)`.

The existing polynomial Gamma-moment theorem makes this majorant summable.
The corpus's derivative-of-series theorem on an open connected interval
therefore applies to the full series at every `x>0`, for every complex `b`.
No finite truncation replaces the source. Summability of both complete
families justifies splitting their derivative sum. Thus

`partial_x M_b(x)=M_b(x)/(2*x)-M_(b-1)(x)`,
`partial_t M_b(exp(t))=M_b(exp(t))/2-exp(t)*M_(b-1)(exp(t))`.

Together with the [coefficient-generator theorem](pw-b-gamma-parameter-generator.md),
this retains both actual identities: `partial_b M_b=E_b` and the coordinate
shift equation. At zero the log-coordinate identity holds pointwise for
the original preimage `M`, retaining `M_(-1)`. No unproved global endpoint
admission is used in this identity.

## Sharp weighted global admission and complete mass

The actual shifted atom is

`F_b(n,x)=x*A_(b-1)(n,x)=mu(n)*exp(-b*log(n))*(n*x)*Q(n*x)`.

Every such atom is integrable in Lebesgue `dx` on `x>0`, for every `b`.
A positive dilation and the admitted moment `integral x*Q(x)=Gamma(5/2)`
give both exact atom identities

`integral norm F_b(n,x) dx=3/2*integral norm A_b(n,x) dx`,
`integral F_b(n,x) dx=3/2*integral A_b(n,x) dx`.

Here the recurrence is `Gamma(5/2)=3/2*Gamma(3/2)`. Therefore

`sum_n integral norm F_b(n,x) dx < infinity iff Re(b)>0`.

This is the original absolute boundary, not the smaller region obtained
by dropping the weight and applying admission to `M_(b-1)` alone.
For `Re(b)>0`, summability of all atom norm integrals justifies admission
of the complete weighted shift and exchanging its series with the integral:

`integral x*M_(b-1)(x) dx=3/2*integral M_b(x) dx`.

The weighted coordinate derivative is the admitted complete difference
`x*partial_x M_b=M_b/2-x*M_(b-1)`. Its integral is therefore

`integral x*partial_x M_b(x) dx=-integral M_b(x) dx`.

All measures, weights and shifted coefficients are retained. Failure of
atom-norm summability at zero does not exclude an integrable signed sum.
This leaf makes no claim that the signed weighted shift at zero has yet
been globally admitted.

## Route scope and next conjecture

The chain remains literal PW response -> FE imbalance -> positive Deninger
Ward transmutation -> independently source-forced fixed-grade balance -> RH.
These are actual source dynamics and exact admission laws. They do not
identify the coefficient parameter with the spectral label, realize the
Xi divisor, or force a Ward response to vanish. RH remains unproved.

The next signed-endpoint candidate is `x*M_(-1) in L1(dx)` with zero mass.
Set `R(x)=x*Q(x)` and retain the complete Abel atoms
`S(n)*(R(n*x)-R((n+1)*x))`, with `S` the actual Möbius partial sums.
The existing adjacent-source bound suggests an integrated difference cost
at most `(2*Gamma(5/2)+Gamma(7/2))/n^2`. The needed second moment, finite
identity, pointwise terminal and integrated terminal must all be proved
before using the candidate. If closed, the weighted coordinate derivative
would have zero mass at zero, whereas the actual coefficient derivative
has mass `Gamma(3/2)`. That would obstruct their identification even after
both complete signed sources are admitted; the exact mass difference is
the positive survivor to retain, not a proof of RH.

## Search and method audit

All four deep method searches are retained in the
[search artifact](../1-in-progress/pw-b-gamma-coordinate-searches.json),
including candidates, source arguments and ingredient groups. All report
partial coverage of 723219 declarations, with source/compiler freshness
metadata preserved. The decisive available method is differentiation of a
full series under common summable derivative bounds; the actual Gamma
comparison supplies its missing source-specific premise. Mertens decay
methods are relevant to the next signed endpoint but do not themselves
prove admission of the weighted shifted source.

Broad dilation and bifurcation searches led to primary abstracts:
[nonexpansive wavelet dilations](https://arxiv.org/abs/2609.08746),
[sparse Mellin recovery](https://arxiv.org/abs/2609.06661), and
[Shilnikov-Hopf bifurcation](https://arxiv.org/abs/2608.13021).
The first constructs wavelet bases without the usual expansive-dilation
setting; the second treats finite sparse recovery through dilation samples;
the third uses a specific dynamical return-map mechanism. None supplies an
admitted identification with this full arithmetic source or its spectral
parameter. Only abstracts were inspected; no transfer theorem or external
paper is a Lean premise.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusCoordinateGenerator.lean`.
The leaf contains 338 lines, 21 public theorems and one definition.
Its capstone is `pwGammaMobiusCoordinateGenerator_closed`.
Scratch and direct `lake env lean` checks passed without warnings. The
targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusCoordinateGenerator`
passed. Scratch `#print axioms` audited all 22 public declarations: only
`propext`, `Classical.choice`, and `Quot.sound` occur. Formal lint, index
regeneration, all-name uniqueness, generated API coverage and task-scoped
file checks passed. Umbrella wired; no full or umbrella build or numerical
experiment ran. All owned Lean and research processes finished. RH remains
unproved and the goal remains active.
