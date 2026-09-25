# Critical-line Euler deletion has an infinite, two-sign port defect

Paper-level structural fact; Lean and literature novelty audits open. This is
not an RH criterion or a source-specific orientation theorem.

Fix a prime `p`, put `a=p^(-1/2)∈(0,1)`, `ell=log p`, and let the literal
deletion factor act by multiplication on critical-line frequency space
`H=L²(ℝ,W(t)dt)`, where `W` is positive almost everywhere:

`m_p(t)=1-a exp(-i ell t)`, `M_p f=m_p f`.

Its exact Hilbert defect is

`I-M_p* M_p = M_(2a cos(ell t)-a²)`.

The multiplier on the right is positive on an open interval around `t=0`
and negative on an open interval around `t=π/ell`. Both sign subspaces are
infinite-dimensional. In particular `M_p` is neither a contraction nor an
expansion, and its defect has infinite rank.

Suppose a block-diagonal Krein extension of the literal bulk action has a
finite-dimensional boundary port `K`, with boundary metric `J_K` and first
column `(M_p,B):H→H⊕K`. Metric conservation would require

`I-M_p* M_p = B* J_K B`.

The right side has finite rank; the left side has infinite rank. Thus **no
finite-dimensional port**, positive or indefinite, can conservatively
realize even one literal prime-deletion step in this frequency-space model.
An ordinary positive Hilbert reservoir of any dimension is also impossible,
because the defect has a negative region.

There is a sharp positive replacement. With `d=1-|m_p|²`, let
`H_+=L²({d>0},Wdt)` and `H_-=L²({d<0},Wdt)`. Define

`B_+f=√(d_+)f`, `B_-f=√(d_-)f` on their respective regions. Then

`‖M_p f‖²+‖B_+f‖²-‖B_-f‖²=‖f‖²`.

Both channels are genuinely infinite-dimensional and their signs are
forced, not choices. This is only an isometric first-column law, not a
constructed full Krein-unitary prime dynamics. It applies to arbitrary
input functions and therefore cannot, by itself, distinguish theta from a
source engineered to have off-axis zeros.

## Whole-route meaning

The theta quotient's **one scalar port** selects the divisor of the fixed
completed source. It cannot also serve as a conservative port for literal
finite Euler deletion on critical-line `L²`; those are different operators.
Any proposed identification of a finite-index Stokes receiver with this
bounded conservative `L²` lift inherits the same obstruction; no general
Stokes no-go is claimed here. The natural replacement arena is
an infinite-dimensional, signed frequency reservoir coupled to the
source-selected two-ended domain. Constructing that coupling with exact
Gamma/polar cancellation remains the hard source-to-spectrum problem.

This observation is generic Euler-factor geometry. Treating it as an RH
producer would be theatre; an actual producer must add a theta-specific
arithmetic law not shared by perturbed off-line sources.
