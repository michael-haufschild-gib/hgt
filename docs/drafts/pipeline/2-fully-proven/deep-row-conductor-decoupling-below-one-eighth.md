# Deep-row conductor decoupling below the eighth root

- **Stage:** 2-fully-proven.
- **Type:** THEOREM (paper); Lean assembly pending.
- **Wall:** Σ1b; completion of the all-vector range `α<1/8`.
- **Parent:** [eighth-root positivity](../1-in-progress/off-pole-nonratio-cross-and-one-eighth-weil-positivity.md).

## Target

Write `L=log N`, `Q=floor(L^q)`, `R=floor(N^θ)`,
`y=Σ_(m≤Q) a_m v_m`, and `E(a)=Σ_(m≤Q) E_m(c)a_m²`.
For `0<α<1/8`, choose `3α<q<(1−α)/2` and sufficiently small fixed `θ>0`.
For every `ε>0`, eventually uniformly in `1≤c≤L^α`,

`2|⟨W y,u⟩| ≤ ε E(a)+ε‖u‖²`

for every `u∈V_R∩V_Q^⊥`. Together with the existing block reserves this gives
all-vector complete Weil positivity below `1/8`, with the retained floor
`κ₀/(2c⁷)`. The paper proof below is not yet a Lean certificate.

## Inputs

Split the residual `r_m=Wv_m−E_m(c)v_m` at
`M=floor(N exp(−sqrt L))`. Orthogonality removes its eigenvector term.
The conductor large-sieve estimate bounds the terminal mass of every
`u∈V_R` by `O(L^(−1/2))‖u‖²`. Combining this with the existing global
inverse-energy residual bound gains half a logarithmic power in the
terminal pairing.

The deep rows have `N/n≥exp(sqrt L)`. The existing
`exists_deepMass_conductorResidual_le` retains the completed-shell
cancellation: its prime term is `O(m(1+log m)²/L)`, independent of `c`;
near channels vanish; other channels carry inverse powers of `X` or `N`,
apart from the uniform shifted-shell error. Its inverse-energy prime sum
is `O((c⁷+Q²(1+log Q)²)/L)`, which tends to zero.

The terminal packet estimate is already available as
`harmonicConductorPacket_terminal_le`. The complement assembly is also
available as `exists_complement_block_reserves_below_one_eighth`.
The new conclusion combines these estimates with the low-packet Schur
estimate; it does not assert a new deep-row or terminal-frame theorem.

## Paper proof

Fix `0<α<1/8`, put `q=α+1/4`, and use `θ,b>0` supplied by
`exists_complement_block_reserves_below_one_eighth`. Write
`Q=floor(L^q)`, `R₀=floor(exp(sqrt L))`, `R₁=floor(N^θ)`,
`X=exp(sqrt L)`, and `M=floor(N/X)`.

Let `S=Σ_(m≤Q) ‖r_m‖²/E_m` and `D=Σ_(m≤Q) deepMass_X(r_m)/E_m`.
The existing global estimate gives, for arbitrarily small fixed `η>0`,

`S ≪ (c⁷+Q²(1+log Q)²)[c²(1+log c)³L^(η−1)+c¹⁰(L/N)²]`.

For the deep estimate choose `Y=exp(sqrt L/2)`. Eventually
`2cY≤X` and `Q≤(log Y)²`, uniformly in the allowed overlaps.
The uniform shifted-shell theorem with exponent twelve gives both shifted
errors at every deep row at most `ρ/sqrt n`, where
`ρ=Cc/(log Y)^12 ≤ 4096C/L⁵`. This uses `c≤L`; the conductor range is
absorbed by the theorem with exponent two.

In the existing deep budget, replace `φ(m)≤m`, `m²≤Qm`,
`H_N≤2L`, and `linearPrimeStrip(c)+1≤C₁L`. The nonprime part is at most

`C₂ m [L¹²/N²+L⁴/X+L^(−10)]`.

The two existing inverse-energy sums therefore give

`D ≪ (c⁷+Q²(1+log Q)²)/L`
`     +(c⁷+Q²)[L¹²/N²+L⁴/X+L^(−10)] = o(1)`.

Indeed `7α<1`, `2q<1`, and the exponential factors beat every fixed
power of `L`. All constants and convergence are uniform in `c` and the
packet coefficients.

Since `R₁²≤M` and `18(1+log R₁)≤L` eventually, the existing terminal
mass theorem gives, for every `u∈V_(R₁)`,

`Σ_(M<n≤N) u(n)² ≤ C₃L^(−1/2)‖u‖²`.

Here `N/M≤2X` eventually. Put `T=C₃L^(−1/2)`. The global residual
estimate implies `TS=o(1)`: the leading exponents are `9α−3/2` and
`2α+2q−3/2`, both strictly negative. It also implies

`c⁷S/L=o(1)`,

whose leading exponents are `16α−2` and `9α+2q−2`. Choose `η` small
enough to preserve these strict inequalities; fixed logarithmic powers
are absorbed by another arbitrarily small power of `L`.

For `u∈V_(R₁)∩V_Q^⊥`, orthogonality gives
`⟨Wy,u⟩=Σ a_m⟨r_m,u⟩`. Weighted Cauchy–Schwarz on deep and terminal
rows gives

`|⟨Wy,u⟩|² ≤ 2(D+TS)E(a)‖u‖²`.

Consequently, eventually,
`2|⟨Wy,u⟩|≤E(a)/16+‖u‖²`.
For `w∈V_(R₁)^⊥`, the global residual gives instead
`2|⟨Wy,w⟩|≤E(a)/16+16S‖w‖²`.
The last coefficient is eventually at most the retained far reserve
`3bk/(16c⁷)`, where `k=θL/(2D₀)` and `D₀` is the fixed conductor
cutoff constant.

Decompose an arbitrary vector orthogonally as `x=y+u₀+u₁+w` along
`V_Q⊆V_(R₀)⊆V_(R₁)`. The existing low-packet theorem bounds the
spectrally shifted form `W−κ₀/(2c⁷)I` on `y` below by `E(a)/4`.
The three-band complement theorem retains floors
`κ₀+3`, `κ₀+2+sqrt L/32`, and `κ₀+2+3bk/(16c⁷)` on the other
three blocks. Subtracting the scalar shift costs at most `κ₀/2`
per unit mass. The three low-packet cross payments consume `3E(a)/16`,
one unit on each band, and the displayed far reserve. All remaining
coefficients are strictly positive. Also `E(a)>0` whenever `y≠0`,
by the positive conductor floors. Thus the shifted form is positive
definite, proving the asserted all-vector floor and positivity.

## Remaining proof obligations

1. Specialize the existing deep-row estimate and shifted-shell rates to
   an inverse-energy sum tending uniformly to zero.
2. Transfer the terminal packet bound to horizon vectors and prove the
   displayed cross estimate.
3. Pay the low-packet/far interaction from the retained far-block reserve.
4. Assemble all blocks, formalize the all-vector theorem, and audit its
   transitive axioms. No wall-status change before this conclusion is proved.
