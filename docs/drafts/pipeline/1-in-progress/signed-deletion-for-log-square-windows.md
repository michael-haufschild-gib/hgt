# Signed deletion on logarithmic-square windows

**Target.** Derive the two-sided local width criterion without positive
averaging or negative-excursion arguments. The existing one-sided theorem
does not provide this proof.

**Exact theorem.** For every `α ≥ 0`, all zeta zeros in the critical strip
have real part at most `1/2+α` if and only if some `K` bounds
`|2 Re lagStructure(log p)| ≤ K p^α` for every prime in arbitrarily late
windows `|log p−T| ≤ primeLogSquareRadius T`. The radius is the existing
explicit constant times `log²(T+2)`. At `α=0`, this is equivalent to RH.

## Complex deletion kernel

For a deleted exponent `λ=a+iγ`, put `h=2π/(3γ)` and

`b = cosh(ha)/2 − i√3 sinh(ha)/2`,

`Qλ(w) = (cosh(hw)+b)/(1+b)`.

Then `Qλ(λ)=0`, `Qλ(0)=1`, and `Re b≥1/2`. Its three translation
coefficients are `1/(2(1+b)), b/(1+b), 1/(2(1+b))`; they need not be
real. Conjugate-pair multiplication must not replace this kernel by a
positive one.

Writing `x=ha`, the variation mass is
`m=(1+|b|)/|1+b|`. Since `|b|²=(Re b)²+(Im b)²`,

`m ≤ 1 + (Im b)²/(2 Re b (1+Re b))
   ≤ 1 + (3/2)tanh² x ≤ exp((3/2)x²)`.

The absolute exponential moment is at most
`m exp(min(|hs|,s²h²/2))`. Thus bounded real parts and square-summable
shifts give finite total variation; the existing ordinate head/tail
estimates yield logarithmic-square leakage. For retained `w`,
`|Qλ(w)−1| ≤ (2/3)h²|w|²` when `|hw|≤1`, so a sufficiently late
infinite product is nonzero at `w` and deletes a cofinite spectrum.

## Finite-spectrum endpoint

For a finite set `S` of distinct exponents choose `δ>0` with the values
`exp(δz)`, `z∈S`, distinct. The polynomial
`P(X)=∏_{z∈S\{z₀}}(X−exp(δz))` gives the exact translation identity

`Σ_j P_j F(T+jδ) = c(z₀)exp(z₀T)P(exp(δz₀))`.

Its triangle inequality forces a large absolute value within a fixed
distance of every `T` when `Re z₀>0`. No conjugation symmetry, absence
of real exponents, or sign of the trace is needed.

## Local criterion

Normalize the spline trace by `exp(−αu)` and retain any zero exponent
with `Re z₀>α`. Its coefficient stays nonzero after sufficiently late
signed deletion. All but finitely many other coefficients vanish. Let
`A` be the original coefficient mass, `D=1/2+|α|`, and `V` the total
variation exponent of the chosen tail. Dominated convergence passes the
finite-convolution norm bound to the infinite deletion. On a log-square
window centered at `T`, every observation point `t∈[T,T+B]` satisfies

`|filtered trace(t)| ≤ exp(V) (|K| + 2A exp(DB−T))`.

The finite-spectrum endpoint instead forces growth with exponent
`Re z₀−α>0`, a contradiction at arbitrarily large centers. Hence the
continuous window bound gives width at most `α`.

Prime gaps transfer an absolute bound of exponent `α`, starting with
width `a`, to continuous exponent `max(α,a−1/3)`. Starting at `a=1/2`,
the first signed deletion gives width `max(α,1/6)`; the second gives
width `α`. Conversely, width `α` bounds every prime trace by the
summable coefficient mass times `p^α`.

**Lean status:** all eight modules compile. Direct check of
`SignedPrimeLogSquareWindows.lean` passed; both final criteria depend only
on `propext`, `Classical.choice`, `Quot.sound`. Direct helper-module audits
remain. The infinite norm bound uses total variation and dominated
convergence, not order preservation. All modules are wired into the owning
umbrella.
